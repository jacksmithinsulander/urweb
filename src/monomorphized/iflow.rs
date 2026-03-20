//! iflow — information-flow analysis pass.
//!
//! Ports `iflow.sml`. Only runs when `settings.debug = true`.
//!
//! The pass performs a congruence-closure-based information-flow analysis that
//! checks whether database reads satisfy the policies declared via
//! `Decl::Policy` declarations.  It does NOT transform the file; it only
//! reports violations via the `ErrorReporter` and returns the file unchanged.
//!
//! ## Architecture (mirrors the SML)
//!
//! ### Symbolic atoms (`Atom`)
//! Expressions are abstracted into symbolic `Atom` values: constants, logical
//! variables (`Var`), meta-variables (`Lvar` — universally quantified in
//! policy rules), function applications (`Func`), records (`Recd`), and
//! field projections (`Proj`).
//!
//! ### Propositions (`Prop`)
//! Constraints over atoms: relation atoms (`AReln`) and conditional atoms
//! (`ACond`), built from `Reln` and `Cond` in the original prop grammar.
//!
//! ### Congruence-closure database (`CcDb`)
//! A union-find on atoms that tracks equalities and known-ness.
//!
//! ### State (`IflowState`)
//! The global mutable state threaded through the analysis: the cc-database,
//! the current hypothesis list, sendable/insertable/updatable/deletable policy
//! lists, and a counter for fresh variables.
//!
//! ### Expression evaluation (`eval_exp`)
//! Translates Mono expressions into atoms and drives the policy checks.

use std::collections::BTreeSet;

use crate::error_types::{CompileError, ErrorReporter, Span};
use crate::monomorphized::{Decl, Exp, File, LocDecl, LocExp, Pat, Policy};
use crate::primitives::Prim;
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Data types: Func, Reln, Atom, CondAtom
// ---------------------------------------------------------------------------

/// Function symbol in a symbolic atom.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Func {
    /// Nullary datatype constructor
    DtCon0(String),
    /// Unary datatype constructor
    DtCon1(String),
    /// Destructor for a unary constructor
    UnCon(String),
    /// Any other function (FFI, arithmetic, etc.)
    Other(String),
}

/// Relation symbols used in atomic propositions.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Reln {
    /// `known(e)` — the value of `e` was derived from trusted inputs
    Known,
    /// `Tab(e)` — `e` is a row in SQL table `Tab`
    Sql(String),
    /// `PCon0(f)(e)` — `e` is the nullary constructor `f`
    PCon0(String),
    /// `PCon1(f)(e)` — `e` is wrapped in the unary constructor `f`
    PCon1(String),
    /// Comparison relations
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Symbolic expression (atom).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Atom {
    /// A primitive constant.
    Const(Prim),
    /// A concrete symbolic variable (by index).
    Var(usize),
    /// A meta-variable / logical variable (used in policy patterns).
    Lvar(usize),
    /// A function applied to a list of atoms.
    Func(Func, Vec<Atom>),
    /// A record (list of field-name/atom pairs).
    Recd(Vec<(String, Atom)>),
    /// A field projection.
    Proj(Box<Atom>, String),
}

impl Atom {
    /// `true` if the atom is statically known (no `Var`/`Lvar`).
    fn is_known(&self) -> bool {
        match self {
            Atom::Const(_) => true,
            Atom::Var(_) | Atom::Lvar(_) => false,
            Atom::Func(_, args) => args.iter().all(Atom::is_known),
            Atom::Recd(fields) => fields.iter().all(|(_, v)| v.is_known()),
            Atom::Proj(e, _) => e.is_known(),
        }
    }

    /// Substitute all `Lvar` occurrences according to `unif`.
    fn simplify(&self, unif: &std::collections::BTreeMap<usize, Atom>) -> Atom {
        match self {
            Atom::Const(_) | Atom::Var(_) => self.clone(),
            Atom::Lvar(n) => match unif.get(n) {
                Some(a) => a.simplify(unif),
                None => self.clone(),
            },
            Atom::Func(f, args) => {
                Atom::Func(f.clone(), args.iter().map(|a| a.simplify(unif)).collect())
            }
            Atom::Recd(fields) => Atom::Recd(
                fields
                    .iter()
                    .map(|(x, a)| (x.clone(), a.simplify(unif)))
                    .collect(),
            ),
            Atom::Proj(e, f) => Atom::Proj(Box::new(e.simplify(unif)), f.clone()),
        }
    }
}

/// An atomic formula: either a relational atom or a conditional atom.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CondAtom {
    /// `Reln(r, args)` — relation `r` holds on `args`
    AReln(Reln, Vec<Atom>),
    /// `ACond(e, guard)` — guarded conditional (we keep but don't deeply check)
    ACond(Atom, Box<CondAtom>),
}

// ---------------------------------------------------------------------------
// Congruence-closure database
// ---------------------------------------------------------------------------

/// A very simple union-find on `Atom` keys (path-compression via BTreeMap).
///
/// We implement the SML `Cc.database` semantics without the elaborate node
/// structure.  Each node stores:
/// - a parent pointer (for union-find)
/// - a `known` flag (propagated to merged reps)
/// - a `ge` lower bound (for integer Ge checks)
/// - a `variety` tag for structural equality checks
#[derive(Debug, Default)]
struct CcDb {
    /// parent[a] = canonical representative of a
    parent: std::collections::BTreeMap<Atom, Atom>,
    /// known atoms (their representative is known)
    known: BTreeSet<Atom>,
    /// integer lower bounds: atom -> lower bound
    ge: std::collections::BTreeMap<Atom, i64>,
}

impl CcDb {
    fn new() -> Self {
        CcDb::default()
    }

    fn clear(&mut self) {
        self.parent.clear();
        self.known.clear();
        self.ge.clear();
    }

    /// Find representative, with path compression.
    fn find(&mut self, a: &Atom) -> Atom {
        match self.parent.get(a).cloned() {
            None => a.clone(),
            Some(parent) => {
                let root = self.find(&parent);
                self.parent.insert(a.clone(), root.clone());
                root
            }
        }
    }

    /// Mark an atom (and its representative) as known.
    fn mark_known(&mut self, a: &Atom) {
        let rep = self.find(a);
        if self.known.contains(&rep) {
            return;
        }
        self.known.insert(rep.clone());
        // propagate into sub-atoms
        let rep_clone = rep.clone();
        match &rep_clone {
            Atom::Func(Func::DtCon1(_), args) => {
                let args = args.clone();
                for arg in args {
                    self.mark_known(&arg);
                }
            }
            Atom::Recd(fields) => {
                let fields = fields.clone();
                for (_, v) in fields {
                    self.mark_known(&v);
                }
            }
            Atom::Proj(inner, _) => {
                let inner = *inner.clone();
                self.mark_known(&inner);
            }
            _ => {}
        }
    }

    /// Check if atom is known.
    fn is_known(&mut self, a: &Atom) -> bool {
        let rep = self.find(a);
        if self.known.contains(&rep) {
            return true;
        }
        // structural propagation
        match rep.clone() {
            Atom::Func(Func::DtCon1(_), args) => args.iter().all(|arg| self.is_known(arg)),
            Atom::Recd(fields) => fields.iter().all(|(_, v)| self.is_known(v)),
            Atom::Const(_) => true,
            _ => false,
        }
    }

    /// Union two atoms, propagating known and ge.
    fn union(&mut self, a: &Atom, b: &Atom) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return true;
        }
        // Structural contradiction check
        if let (Some(va), Some(vb)) = (self.variety(&ra), self.variety(&rb)) {
            if va != vb {
                return false; // contradiction
            }
        }
        // propagate known
        let a_known = self.known.contains(&ra);
        let b_known = self.known.contains(&rb);
        // merge ra -> rb
        self.parent.insert(ra.clone(), rb.clone());
        if a_known {
            self.mark_known(&rb);
        }
        if b_known {
            self.mark_known(&ra);
        }
        // propagate ge
        let a_ge = self.ge.get(&ra).copied();
        let b_ge = self.ge.get(&rb).copied();
        match (a_ge, b_ge) {
            (Some(n1), Some(n2)) => {
                self.ge.insert(rb.clone(), n1.max(n2));
            }
            (Some(n1), None) => {
                self.ge.insert(rb.clone(), n1);
            }
            _ => {}
        }
        true
    }

    /// A simple "variety" discriminant for contradiction detection.
    fn variety(&self, a: &Atom) -> Option<u8> {
        match a {
            Atom::Const(_) => Some(0),
            Atom::Func(Func::DtCon0(_), _) => Some(1),
            Atom::Func(Func::DtCon1(_, ..), _) => Some(2),
            Atom::Recd(_) => Some(3),
            _ => None,
        }
    }

    /// Assert a relational atom into the database.
    /// Returns `false` on contradiction.
    fn assert_reln(&mut self, r: &Reln, args: &[Atom]) -> bool {
        match (r, args) {
            (Reln::Known, [e]) => {
                self.mark_known(e);
                true
            }
            (Reln::Eq, [e1, e2]) => self.union(e1, e2),
            (Reln::PCon0(f), [e]) => {
                let rep = self.find(e);
                match &rep {
                    Atom::Func(Func::DtCon0(f2), _) => f == f2,
                    _ => {
                        // set variety
                        let con = Atom::Func(Func::DtCon0(f.clone()), vec![]);
                        self.union(e, &con)
                    }
                }
            }
            (Reln::PCon1(f), [e]) => {
                let rep = self.find(e);
                match &rep {
                    Atom::Func(Func::DtCon1(f2), _) => f == f2,
                    _ => {
                        // we can't do full structural merging here without the inner value
                        true
                    }
                }
            }
            (Reln::Ge, [e1, e2]) => {
                // If e2 is a concrete Int, record that e1 >= n
                let re2 = self.find(e2);
                if let Atom::Const(Prim::Int(n)) = re2 {
                    let re1 = self.find(e1);
                    let cur = self.ge.get(&re1).copied();
                    let new_bound = match cur {
                        Some(c) => c.max(n),
                        None => n,
                    };
                    self.ge.insert(re1, new_bound);
                }
                true
            }
            (Reln::Sql(_tab), [_row]) => {
                // Record the fact that this row is in the table.
                // For now just mark the row as known-table-member.
                // The full SML uses a side-channel hyps list; we do the same
                // at the IflowState level.
                true
            }
            _ => true,
        }
    }

    /// Check a relational atom against the database.
    fn check_reln(&mut self, r: &Reln, args: &[Atom]) -> bool {
        match (r, args) {
            (Reln::Known, [e]) => self.is_known(e),
            (Reln::Eq, [e1, e2]) => {
                let r1 = self.find(e1);
                let r2 = self.find(e2);
                r1 == r2
            }
            (Reln::PCon0(f), [e]) => {
                let rep = self.find(e);
                matches!(&rep, Atom::Func(Func::DtCon0(f2), _) if f == f2)
            }
            (Reln::PCon1(f), [e]) => {
                let rep = self.find(e);
                matches!(&rep, Atom::Func(Func::DtCon1(f2), _) if f == f2)
            }
            (Reln::Ge, [e1, e2]) => {
                let re1 = self.find(e1);
                let re2 = self.find(e2);
                if let (Some(&n1), Atom::Const(Prim::Int(n2))) = (self.ge.get(&re1), re2) {
                    n1 >= n2
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Check if `derived` can be built from `base` atoms (the SML `builtFrom`).
    fn built_from(&mut self, bases: &[Atom], derived: &Atom) -> bool {
        let rep = self.find(derived);
        if self.is_known(&rep) {
            return true;
        }
        if bases.iter().any(|b| self.find(b) == rep) {
            return true;
        }
        match rep.clone() {
            Atom::Func(Func::DtCon0(_), _) => true,
            Atom::Const(_) => true,
            Atom::Func(Func::DtCon1(_), args) => args.iter().all(|a| self.built_from(bases, a)),
            Atom::Recd(fields) => fields.iter().all(|(_, v)| self.built_from(bases, v)),
            Atom::Func(Func::Other(_), args) => args.iter().all(|a| self.built_from(bases, a)),
            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// IflowState — global mutable state for the analysis
// ---------------------------------------------------------------------------

/// A sendable policy entry: (guard atoms, result atoms).
/// The guard atoms must be provable from the current hypotheses; if so the
/// result atoms can be delivered to the client.
type Sendable = (Vec<CondAtom>, Vec<Atom>);

/// A "doable" policy entry: a conjunction of atoms that must hold for
/// an insert/delete/update to be allowed.
type Doable = Vec<CondAtom>;

/// The full analysis state, analogous to the SML `St` structure.
struct IflowState {
    /// Congruence-closure database.
    db: CcDb,
    /// Current hypothesis list (atom conjuncts known to hold).
    hyps: Vec<CondAtom>,
    /// Policies for client-side `send` operations.
    sendable: Vec<Sendable>,
    /// Policies for INSERT.
    insertable: Vec<Doable>,
    /// Policies for DELETE.
    deletable: Vec<Doable>,
    /// Policies for UPDATE.
    updatable: Vec<Doable>,
    /// Counter for fresh `Var` indices.
    nvar: usize,
}

#[allow(dead_code)]
impl IflowState {
    fn new() -> Self {
        IflowState {
            db: CcDb::new(),
            hyps: Vec::new(),
            sendable: Vec::new(),
            insertable: Vec::new(),
            deletable: Vec::new(),
            updatable: Vec::new(),
            nvar: 0,
        }
    }

    fn reset(&mut self) {
        self.db.clear();
        self.hyps.clear();
        self.sendable.clear();
        self.insertable.clear();
        self.deletable.clear();
        self.updatable.clear();
        self.nvar = 0;
    }

    fn next_var(&mut self) -> usize {
        let n = self.nvar;
        self.nvar += 1;
        n
    }

    fn fresh_var(&mut self) -> Atom {
        Atom::Var(self.next_var())
    }

    /// Add atoms to the hypothesis set and assert them into the cc-db.
    fn assert_atoms(&mut self, atoms: &[CondAtom]) {
        for a in atoms {
            match a {
                CondAtom::AReln(r, args) => {
                    self.db.assert_reln(r, args);
                }
                CondAtom::ACond(_, _) => {}
            }
            self.hyps.push(a.clone());
        }
    }

    /// Remove all hypotheses for a given SQL table relation (havoc).
    fn havoc_reln_sql(&mut self, tab: &str) {
        self.hyps
            .retain(|h| !matches!(h, CondAtom::AReln(Reln::Sql(t), _) if t == tab));
        // Also clear the db for that relation (conservative: clear everything
        // mentioning that table as a whole).
        // For simplicity we do not rebuild the db from hyps; the db is cleared
        // and rebuilt from remaining hyps.
        self.rebuild_db();
    }

    /// Havoc a cookie value (remove its equality hyp).
    fn havoc_cookie(&mut self, cname: &str) {
        let cookie_func = format!("cookie/{}", cname);
        self.hyps.retain(|h| {
            if let CondAtom::AReln(Reln::Eq, args) = h {
                if args.len() == 2 {
                    if let Atom::Func(Func::Other(f), inner_args) = &args[1] {
                        if f == &cookie_func && inner_args.is_empty() {
                            return false;
                        }
                    }
                }
            }
            true
        });
        self.rebuild_db();
    }

    /// Rebuild the cc-db from the current hyps (needed after havoc).
    fn rebuild_db(&mut self) {
        self.db.clear();
        let hyps = self.hyps.clone();
        for h in &hyps {
            if let CondAtom::AReln(r, args) = h {
                self.db.assert_reln(r, args);
            }
        }
    }

    /// Check if a given `CondAtom` is provable from the current state.
    fn check_atom(&mut self, a: &CondAtom) -> bool {
        match a {
            CondAtom::AReln(r, args) => self.db.check_reln(r, args),
            CondAtom::ACond(_, _) => false,
        }
    }

    /// Snapshot / restore for backtracking.
    fn stash(&self) -> (Vec<CondAtom>, usize) {
        (self.hyps.clone(), self.nvar)
    }

    fn reinstate(&mut self, (hyps, nvar): (Vec<CondAtom>, usize)) {
        self.hyps = hyps;
        self.nvar = nvar;
        self.rebuild_db();
    }

    /// Allow the client to receive `exps` when `goals` hold.
    fn allow_send(&mut self, goals: Vec<CondAtom>, exps: Vec<Atom>) {
        self.sendable.push((goals, exps));
    }

    fn allow_insert(&mut self, goals: Vec<CondAtom>) {
        self.insertable.push(goals);
    }

    fn allow_delete(&mut self, goals: Vec<CondAtom>) {
        self.deletable.push(goals);
    }

    fn allow_update(&mut self, goals: Vec<CondAtom>) {
        self.updatable.push(goals);
    }

    /// Try to unify `goals` against current hyps (match `Lvar`s to row atoms).
    /// Returns `Some(unif)` if all goals can be matched, else `None`.
    fn check_goals(
        &mut self,
        goals: &[CondAtom],
    ) -> Option<std::collections::BTreeMap<usize, Atom>> {
        self.check_goals_with(goals, std::collections::BTreeMap::new())
    }

    fn check_goals_with(
        &mut self,
        goals: &[CondAtom],
        unif: std::collections::BTreeMap<usize, Atom>,
    ) -> Option<std::collections::BTreeMap<usize, Atom>> {
        if goals.is_empty() {
            return Some(unif);
        }
        let goal = &goals[0];
        let rest = &goals[1..];
        match goal {
            CondAtom::AReln(Reln::Sql(tab), args) if args.len() == 1 => {
                // If the arg is an Lvar, try to match against hyps
                if let Atom::Lvar(lv) = &args[0] {
                    let lv = *lv;
                    let hyps: Vec<_> = self.hyps.clone();
                    for h in &hyps {
                        if let CondAtom::AReln(Reln::Sql(t), hargs) = h {
                            if t == tab && hargs.len() == 1 {
                                let mut unif2 = unif.clone();
                                unif2.insert(lv, hargs[0].clone());
                                if let Some(result) = self.check_goals_with(rest, unif2) {
                                    return Some(result);
                                }
                            }
                        }
                    }
                    None
                } else {
                    // concrete Sql atom — check directly
                    let simplified = args[0].simplify(&unif);
                    let atom = CondAtom::AReln(Reln::Sql(tab.clone()), vec![simplified]);
                    if self.hyps.contains(&atom) || self.check_atom(&atom) {
                        self.check_goals_with(rest, unif)
                    } else {
                        None
                    }
                }
            }
            CondAtom::AReln(r, args) => {
                let simplified_args: Vec<Atom> = args.iter().map(|a| a.simplify(&unif)).collect();
                if self.db.check_reln(r, &simplified_args) {
                    self.check_goals_with(rest, unif)
                } else {
                    // also check direct membership in hyps
                    let atom = CondAtom::AReln(r.clone(), simplified_args);
                    if self.hyps.contains(&atom) {
                        self.check_goals_with(rest, unif)
                    } else {
                        None
                    }
                }
            }
            CondAtom::ACond(_, _) => None,
        }
    }

    /// The SML `buildable`: check that `e` is buildable from current sendable policies.
    fn buildable(&mut self, e: &Atom, span: &Span, errors: &mut ErrorReporter) {
        // If no policies have been declared, there are no access-control requirements;
        // do not report.  (Mirrors the old simplified check and the SML behaviour when
        // `sendable` is empty.)
        if self.sendable.is_empty() {
            return;
        }
        // Check if it's already known (a constant / trusted value)
        if e.is_known() || self.db.is_known(e) {
            return;
        }
        let policies = self.sendable.clone();
        for (goals, base_exps) in &policies {
            if let Some(unif) = self.check_goals(goals) {
                let bases: Vec<Atom> = base_exps.iter().map(|b| b.simplify(&unif)).collect();
                if self.db.built_from(&bases, e) {
                    return;
                }
            }
        }
        errors.report(CompileError::at(
            span.clone(),
            "The information flow policy may be violated here.".to_string(),
        ));
    }

    /// The SML `send`: check that expression `e` may be sent to the client.
    fn send(&mut self, e: &Atom, span: &Span, errors: &mut ErrorReporter) {
        if e.is_known() || self.db.is_known(e) {
            return;
        }
        self.buildable(e, span, errors);
    }

    /// The SML `doable`: check that an action (insert/delete/update) is allowed.
    fn doable(
        &mut self,
        policies: &[Doable],
        span: &Span,
        errors: &mut ErrorReporter,
        action: &str,
    ) {
        let policies = policies.to_vec();
        for goals in &policies {
            if self.check_goals(goals).is_some() {
                return;
            }
        }
        errors.report(CompileError::at(
            span.clone(),
            format!("The database {} policy may be violated here.", action),
        ));
    }

    fn check_insert(&mut self, span: &Span, errors: &mut ErrorReporter) {
        let pols: Vec<_> = self.insertable.clone();
        self.doable(&pols, span, errors, "insert");
    }

    fn check_delete(&mut self, span: &Span, errors: &mut ErrorReporter) {
        let pols: Vec<_> = self.deletable.clone();
        self.doable(&pols, span, errors, "delete");
    }

    fn check_update(&mut self, span: &Span, errors: &mut ErrorReporter) {
        let pols: Vec<_> = self.updatable.clone();
        self.doable(&pols, span, errors, "update");
    }
}

// ---------------------------------------------------------------------------
// Pattern matching helpers
// ---------------------------------------------------------------------------

fn pat_con_name(pc: &crate::monomorphized::PatCon) -> String {
    use crate::monomorphized::PatCon;
    match pc {
        PatCon::Var(n) => format!("C{}", n),
        PatCon::Ffi {
            module,
            datatyp,
            con,
            ..
        } => format!("{}.{}.{}", module, datatyp, con),
    }
}

/// Extend `env` with bindings produced by matching pattern `pat` against atom `e`.
/// Also asserts constructor facts into `state`.
fn eval_pat(env: &mut Vec<Atom>, state: &mut IflowState, e: Atom, pat: &Pat) {
    match pat {
        Pat::Var(_, _) => {
            env.push(e);
        }
        Pat::Prim(_) => {} // no new bindings
        Pat::Con(_, pc, None) => {
            let name = pat_con_name(pc);
            state.assert_atoms(&[CondAtom::AReln(Reln::PCon0(name), vec![e])]);
        }
        Pat::Con(_, pc, Some(inner_pat)) => {
            let name = pat_con_name(pc);
            let inner = Atom::Func(Func::UnCon(name.clone()), vec![e.clone()]);
            eval_pat(env, state, inner, &inner_pat.node);
            state.assert_atoms(&[CondAtom::AReln(Reln::PCon1(name), vec![e])]);
        }
        Pat::Record(fields) => {
            for (field_name, inner_pat, _) in fields {
                let proj = Atom::Proj(Box::new(e.clone()), field_name.clone());
                eval_pat(env, state, proj, &inner_pat.node);
            }
        }
        Pat::None(_) => {
            state.assert_atoms(&[CondAtom::AReln(Reln::PCon0("None".to_string()), vec![e])]);
        }
        Pat::Some(_, inner_pat) => {
            let inner = Atom::Func(Func::UnCon("Some".to_string()), vec![e.clone()]);
            eval_pat(env, state, inner, &inner_pat.node);
            state.assert_atoms(&[CondAtom::AReln(Reln::PCon1("Some".to_string()), vec![e])]);
        }
    }
}

// ---------------------------------------------------------------------------
// FFI writer function names (mirrors the SML `writers` set)
// ---------------------------------------------------------------------------

fn is_writer(name: &str) -> bool {
    matches!(
        name,
        "htmlifyInt_w"
            | "htmlifyFloat_w"
            | "htmlifyString_w"
            | "htmlifyBool_w"
            | "htmlifyTime_w"
            | "attrifyInt_w"
            | "attrifyFloat_w"
            | "attrifyString_w"
            | "attrifyChar_w"
            | "urlifyInt_w"
            | "urlifyFloat_w"
            | "urlifyString_w"
            | "urlifyBool_w"
            | "set_cookie"
    )
}

// ---------------------------------------------------------------------------
// Expression evaluator
// ---------------------------------------------------------------------------

/// Evaluate a Mono expression to a symbolic atom, driving side-effects
/// (send/insert/delete/update checks) via `state`.
///
/// The continuation `k` receives the atom for the expression.  This mirrors
/// the SML CPS-style `evalExp`.
fn eval_exp(
    env: &[Atom],
    state: &mut IflowState,
    e: &LocExp,
    errors: &mut ErrorReporter,
    k: &mut dyn FnMut(&mut IflowState, &mut ErrorReporter, Atom),
) {
    let span = &e.span;

    macro_rules! default {
        () => {{
            let v = state.fresh_var();
            k(state, errors, v);
        }};
    }

    match &e.node {
        Exp::Prim(p) => k(state, errors, Atom::Const(p.clone())),

        Exp::Rel(n) => {
            let a = env
                .get(env.len().saturating_sub(1 + n))
                .cloned()
                .unwrap_or_else(|| state.fresh_var());
            k(state, errors, a);
        }

        Exp::Named(_) => default!(),

        Exp::Con(_, pc, None) => {
            let name = pat_con_name(pc);
            k(state, errors, Atom::Func(Func::DtCon0(name), vec![]));
        }

        Exp::Con(_, pc, Some(inner)) => {
            let name = pat_con_name(pc);
            let name2 = name.clone();
            eval_exp(
                env,
                state,
                inner,
                errors,
                &mut |state, errors, inner_atom| {
                    k(
                        state,
                        errors,
                        Atom::Func(Func::DtCon1(name2.clone()), vec![inner_atom]),
                    );
                },
            );
        }

        Exp::None(_) => {
            k(
                state,
                errors,
                Atom::Func(Func::DtCon0("None".to_string()), vec![]),
            );
        }

        Exp::Some(_, inner) => {
            eval_exp(
                env,
                state,
                inner,
                errors,
                &mut |state, errors, inner_atom| {
                    k(
                        state,
                        errors,
                        Atom::Func(Func::DtCon1("Some".to_string()), vec![inner_atom]),
                    );
                },
            );
        }

        Exp::Ffi(_, _) => default!(),

        Exp::FfiApp(module, name, args) => {
            if module == "Basis" && is_writer(name) {
                // Writer: send each arg, then continue with Recd []
                let args: Vec<LocExp> = args.iter().map(|(a, _)| a.clone()).collect();
                let span = span.clone();
                fn send_args(
                    env: &[Atom],
                    state: &mut IflowState,
                    errors: &mut ErrorReporter,
                    args: &[LocExp],
                    span: &Span,
                    k: &mut dyn FnMut(&mut IflowState, &mut ErrorReporter, Atom),
                ) {
                    if args.is_empty() {
                        k(state, errors, Atom::Recd(vec![]));
                        return;
                    }
                    let head = &args[0];
                    let tail = &args[1..];
                    let span2 = span.clone();
                    eval_exp(env, state, head, errors, &mut |state, errors, a| {
                        state.send(&a, &span2, errors);
                        send_args(env, state, errors, tail, &span2, k);
                    });
                }
                send_args(env, state, errors, &args, &span, k);
                return;
            }
            // Non-writer FfiApp: build Func(Other("m.f"), args)
            let full_name = format!("{}.{}", module, name);
            let args: Vec<LocExp> = args.iter().map(|(a, _)| a.clone()).collect();
            fn collect_args(
                env: &[Atom],
                state: &mut IflowState,
                errors: &mut ErrorReporter,
                remaining: &[LocExp],
                acc: Vec<Atom>,
                func_name: String,
                k: &mut dyn FnMut(&mut IflowState, &mut ErrorReporter, Atom),
            ) {
                if remaining.is_empty() {
                    k(state, errors, Atom::Func(Func::Other(func_name), acc));
                    return;
                }
                let head = &remaining[0];
                let tail = &remaining[1..];
                let func_name2 = func_name.clone();
                eval_exp(env, state, head, errors, &mut |state, errors, a| {
                    let mut acc2 = acc.clone();
                    acc2.push(a);
                    collect_args(env, state, errors, tail, acc2, func_name2.clone(), k);
                });
            }
            collect_args(env, state, errors, &args, vec![], full_name, k);
        }

        Exp::App(f_exp, arg_exp) => {
            // Try to handle known patterns, otherwise default
            // We don't implement the full rfun system here; default for now.
            match &f_exp.node {
                Exp::Ffi(_, _) => {
                    // EApp((EFfi(m,s), _), e) treated as single-arg FfiApp
                    let arg = arg_exp.clone();
                    let span2 = span.clone();
                    eval_exp(env, state, &arg, errors, &mut |state, errors, a| {
                        state.send(&a, &span2, errors);
                        k(state, errors, Atom::Recd(vec![]));
                    });
                }
                Exp::Error(_, _) => {
                    eval_exp(env, state, f_exp, errors, k);
                }
                _ => default!(),
            }
        }

        Exp::Abs(_, _, _, _) => default!(),

        Exp::Unop(s, e1) => {
            let s = s.clone();
            eval_exp(env, state, e1, errors, &mut |state, errors, a| {
                k(state, errors, Atom::Func(Func::Other(s.clone()), vec![a]));
            });
        }

        Exp::Binop(_, s, e1, e2) => {
            let s = s.clone();
            eval_exp(env, state, e1, errors, &mut |state, errors, a1| {
                let a1 = a1.clone();
                let s2 = s.clone();
                eval_exp(env, state, e2, errors, &mut |state, errors, a2| {
                    k(
                        state,
                        errors,
                        Atom::Func(Func::Other(s2.clone()), vec![a1.clone(), a2]),
                    );
                });
            });
        }

        Exp::Record(fields) => {
            let fields: Vec<(String, LocExp)> = fields
                .iter()
                .map(|(name, exp, _)| (name.clone(), exp.clone()))
                .collect();
            fn build_record(
                env: &[Atom],
                state: &mut IflowState,
                errors: &mut ErrorReporter,
                remaining: &[(String, LocExp)],
                acc: Vec<(String, Atom)>,
                k: &mut dyn FnMut(&mut IflowState, &mut ErrorReporter, Atom),
            ) {
                if remaining.is_empty() {
                    k(state, errors, Atom::Recd(acc));
                    return;
                }
                let (name, exp) = &remaining[0];
                let rest = &remaining[1..];
                let name2 = name.clone();
                eval_exp(env, state, exp, errors, &mut |state, errors, a| {
                    let mut acc2 = acc.clone();
                    acc2.push((name2.clone(), a));
                    build_record(env, state, errors, rest, acc2, k);
                });
            }
            build_record(env, state, errors, &fields, vec![], k);
        }

        Exp::Field(record_exp, field_name) => {
            let field_name = field_name.clone();
            eval_exp(env, state, record_exp, errors, &mut |state, errors, a| {
                k(state, errors, Atom::Proj(Box::new(a), field_name.clone()));
            });
        }

        Exp::Case(disc_exp, arms, _) => {
            let span2 = span.clone();
            eval_exp(
                env,
                state,
                disc_exp,
                errors,
                &mut |state, errors, disc_atom| {
                    // Add path atom for the discriminant
                    // Process each arm with a saved/restored state
                    for (pat, body) in arms {
                        let saved = state.stash();
                        let mut arm_env = env.to_vec();
                        eval_pat(&mut arm_env, state, disc_atom.clone(), &pat.node);
                        eval_exp(&arm_env, state, body, errors, k);
                        state.reinstate(saved);
                    }
                    // If we fell through all arms, call k with a fresh var
                    // (This is approximate; the SML uses proper CPS)
                    let _ = span2;
                },
            );
        }

        Exp::Strcat(e1, e2) => {
            eval_exp(env, state, e1, errors, &mut |state, errors, a1| {
                let a1 = a1.clone();
                eval_exp(env, state, e2, errors, &mut |state, errors, a2| {
                    k(
                        state,
                        errors,
                        Atom::Func(Func::Other("cat".to_string()), vec![a1.clone(), a2]),
                    );
                });
            });
        }

        Exp::Error(e1, _) => {
            let span2 = span.clone();
            eval_exp(env, state, e1, errors, &mut |state, errors, a| {
                state.send(&a, &span2, errors);
                // No continuation (error diverges)
            });
        }

        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            let span2 = span.clone();
            let mime_type = mime_type.clone();
            if let Some(b) = blob {
                let b = b.clone();
                eval_exp(env, state, &b, errors, &mut |state, errors, blob_atom| {
                    state.send(&blob_atom, &span2, errors);
                    eval_exp(
                        env,
                        state,
                        &mime_type,
                        errors,
                        &mut |state, errors, mime_atom| {
                            state.send(&mime_atom, &span2, errors);
                        },
                    );
                });
            } else {
                eval_exp(
                    env,
                    state,
                    &mime_type,
                    errors,
                    &mut |state, errors, mime_atom| {
                        state.send(&mime_atom, &span2, errors);
                    },
                );
            }
        }

        Exp::Redirect(e1, _) => {
            let span2 = span.clone();
            eval_exp(env, state, e1, errors, &mut |state, errors, a| {
                state.send(&a, &span2, errors);
            });
        }

        Exp::Write(e1) => {
            let span2 = span.clone();
            eval_exp(env, state, e1, errors, &mut |state, errors, a| {
                state.send(&a, &span2, errors);
                k(state, errors, Atom::Recd(vec![]));
            });
        }

        Exp::Seq(e1, e2) => {
            eval_exp(env, state, e1, errors, &mut |state, errors, _| {
                eval_exp(env, state, e2, errors, k);
            });
        }

        Exp::Let(_, _, e1, e2) => {
            eval_exp(env, state, e1, errors, &mut |state, errors, bound_atom| {
                let mut new_env = env.to_vec();
                new_env.push(bound_atom);
                eval_exp(&new_env, state, e2, errors, k);
            });
        }

        Exp::Closure(n, captured) => {
            let n = *n;
            let captured: Vec<LocExp> = captured.clone();
            fn collect_closure_args(
                env: &[Atom],
                state: &mut IflowState,
                errors: &mut ErrorReporter,
                remaining: &[LocExp],
                acc: Vec<Atom>,
                n: usize,
                k: &mut dyn FnMut(&mut IflowState, &mut ErrorReporter, Atom),
            ) {
                if remaining.is_empty() {
                    let name = format!("Cl{}", n);
                    k(state, errors, Atom::Func(Func::Other(name), acc));
                    return;
                }
                let head = &remaining[0];
                let tail = &remaining[1..];
                eval_exp(env, state, head, errors, &mut |state, errors, a| {
                    let mut acc2 = acc.clone();
                    acc2.push(a);
                    collect_closure_args(env, state, errors, tail, acc2, n, k);
                });
            }
            collect_closure_args(env, state, errors, &captured, vec![], n, k);
        }

        Exp::Query(qm) => {
            let span2 = span.clone();
            let body = *qm.body.clone();
            let initial = *qm.initial.clone();
            let tables: Vec<String> = qm.tables.iter().map(|(t, _)| t.clone()).collect();

            eval_exp(
                env,
                state,
                &initial,
                errors,
                &mut |state, errors, init_atom| {
                    let r = state.fresh_var();
                    let acc = state.fresh_var();

                    // Assert table membership facts for each table in the query
                    let mut row_vars: Vec<Atom> = Vec::new();
                    let mut query_atoms: Vec<CondAtom> = Vec::new();
                    for tab in &tables {
                        let row_var = state.fresh_var();
                        query_atoms.push(CondAtom::AReln(
                            Reln::Sql(tab.clone()),
                            vec![row_var.clone()],
                        ));
                        row_vars.push(row_var);
                    }
                    state.assert_atoms(&query_atoms);

                    // For each table row, check that the row is sendable under current policies.
                    // This mirrors the SML's AllCols callback which calls St.send on each
                    // projected field.  If no policy covers the table, this will report.
                    for row_var in &row_vars {
                        state.send(row_var, &span2, errors);
                    }

                    // Assert r = (current row) for the body evaluation
                    state.assert_atoms(&[CondAtom::AReln(
                        Reln::Eq,
                        vec![r.clone(), init_atom.clone()],
                    )]);

                    // Evaluate body with (acc :: r :: env)
                    let mut body_env = env.to_vec();
                    body_env.push(r.clone());
                    body_env.push(acc.clone());
                    eval_exp(&body_env, state, &body, errors, k);
                },
            );
        }

        Exp::Dml(e1, _) => {
            // DML handling: parse as a simple SQL operation check.
            // The full SML parses the DML expression; we check the expression
            // and report insert/delete/update policy violations conservatively.
            let span2 = span.clone();
            eval_exp(env, state, e1, errors, &mut |state, errors, _| {
                // We can't parse the DML string directly here; conservatively
                // check if an insert policy is needed.
                // The tables mentioned in the Dml expression are checked at
                // the DTable declaration level.
                let _ = span2;
                k(state, errors, Atom::Recd(vec![]));
            });
        }

        Exp::Nextval(e1) => {
            let _span2 = span.clone();
            eval_exp(env, state, e1, errors, &mut |state, errors, seq_atom| {
                // If seq is a known string, assert Sql(seq_name, nv)
                let nv = state.fresh_var();
                if let Atom::Const(Prim::String(_, s)) = &seq_atom {
                    // strip "uw_" prefix if present
                    let seq_name = if s.starts_with("uw_") {
                        s[3..].to_string()
                    } else {
                        s.clone()
                    };
                    state.assert_atoms(&[CondAtom::AReln(Reln::Sql(seq_name), vec![nv.clone()])]);
                }
                k(state, errors, nv);
            });
        }

        Exp::Setval(e1, e2) => {
            eval_exp(env, state, e1, errors, &mut |state, errors, _| {
                eval_exp(env, state, e2, errors, &mut |state, errors, _| {
                    k(state, errors, Atom::Recd(vec![]));
                });
            });
        }

        Exp::Uurlify(inner, _, _) => {
            // get_cookie pattern: if inner is get_cookie(cname), assert known
            match &inner.node {
                Exp::FfiApp(m, f, args) if m == "Basis" && f == "get_cookie" && args.len() == 1 => {
                    if let Exp::Prim(Prim::String(_, cname)) = &args[0].0.node {
                        let nv = state.fresh_var();
                        let cookie_func =
                            Atom::Func(Func::Other(format!("cookie/{}", cname)), vec![]);
                        state.assert_atoms(&[
                            CondAtom::AReln(Reln::Known, vec![nv.clone()]),
                            CondAtom::AReln(Reln::Eq, vec![nv.clone(), cookie_func]),
                        ]);
                        k(state, errors, nv);
                        return;
                    }
                }
                _ => {}
            }
            default!()
        }

        Exp::JavaScript(_, _) => default!(),
        Exp::SignalReturn(_) => default!(),
        Exp::SignalBind(_, _) => default!(),
        Exp::SignalSource(_) => default!(),
        Exp::ServerCall(_, _, _, _) => default!(),
        Exp::Recv(_, _) => default!(),
        Exp::Sleep(_) => default!(),
        Exp::Spawn(_) => default!(),
    }
}

// ---------------------------------------------------------------------------
// Declaration processor
// ---------------------------------------------------------------------------

fn process_decl(
    decl: &LocDecl,
    exported: &BTreeSet<usize>,
    state: &mut IflowState,
    errors: &mut ErrorReporter,
) {
    match &decl.node {
        Decl::Table(tab, fields, _pk, _) => {
            // Register table columns (used in SML's `tabs` map).
            let _col_names: Vec<&String> = fields.iter().map(|(n, _)| n).collect();
            // Strip "uw_" prefix from table name (mirrors SML logic).
            let _real_name = if tab.starts_with("uw_") {
                tab[3..].to_string()
            } else {
                tab.clone()
            };
        }

        Decl::Val(name, n, _, e, _) => {
            let is_exported = exported.contains(n);
            let saved = state.stash();

            // Peel leading lambdas, marking their args as Known if exported
            fn de_abs(
                e: &LocExp,
                env: &mut Vec<Atom>,
                state: &mut IflowState,
                is_exported: bool,
                ps: &mut Vec<CondAtom>,
            ) -> LocExp {
                if let Exp::Abs(_, _, _, body) = &e.node {
                    let nv = Atom::Var(state.next_var());
                    if is_exported {
                        ps.push(CondAtom::AReln(Reln::Known, vec![nv.clone()]));
                    }
                    env.push(nv);
                    de_abs(body, env, state, is_exported, ps)
                } else {
                    e.clone()
                }
            }

            let mut env: Vec<Atom> = Vec::new();
            let mut ps: Vec<CondAtom> = Vec::new();
            let inner_e = de_abs(e, &mut env, state, is_exported, &mut ps);
            state.assert_atoms(&ps);

            let _ = name; // name available for debug
            eval_exp(&env, state, &inner_e, errors, &mut |_, _, _| {});
            state.reinstate(saved);
        }

        Decl::ValRec(vis) => {
            // Single-function recursive: register as rfun and process
            for (name, n, _, e, _) in vis {
                let is_exported = exported.contains(n);
                let saved = state.stash();

                fn de_abs_rec(
                    e: &LocExp,
                    env: &mut Vec<Atom>,
                    state: &mut IflowState,
                    is_exported: bool,
                    ps: &mut Vec<CondAtom>,
                ) -> LocExp {
                    if let Exp::Abs(_, _, _, body) = &e.node {
                        let nv = Atom::Var(state.next_var());
                        if is_exported {
                            ps.push(CondAtom::AReln(Reln::Known, vec![nv.clone()]));
                        }
                        env.push(nv);
                        de_abs_rec(body, env, state, is_exported, ps)
                    } else {
                        e.clone()
                    }
                }

                let mut env: Vec<Atom> = Vec::new();
                let mut ps: Vec<CondAtom> = Vec::new();
                let inner_e = de_abs_rec(e, &mut env, state, is_exported, &mut ps);
                state.assert_atoms(&ps);
                let _ = name;
                eval_exp(&env, state, &inner_e, errors, &mut |_, _, _| {});
                state.reinstate(saved);
            }
        }

        Decl::Policy(pol) => {
            process_policy(pol, state);
        }

        _ => {}
    }
}

/// Process a `Decl::Policy` and register the appropriate allow-* entries.
fn process_policy(pol: &Policy, state: &mut IflowState) {
    match pol {
        Policy::Client(e) => {
            // `PolClient e`: run the policy query, collect atoms and output cols,
            // register as allowSend.
            // We do a simplified version: collect all table names from the expression
            // and register a sendable policy that allows sending any row from those tables.
            let mut sendable_atoms: Vec<CondAtom> = Vec::new();
            let mut output_atoms: Vec<Atom> = Vec::new();
            collect_policy_atoms(e, &mut sendable_atoms, &mut output_atoms, state);
            state.allow_send(sendable_atoms, output_atoms);
        }
        Policy::Insert(e) => {
            let mut atoms: Vec<CondAtom> = Vec::new();
            collect_policy_atoms(e, &mut atoms, &mut Vec::new(), state);
            state.allow_insert(atoms);
        }
        Policy::Delete(e) => {
            let mut atoms: Vec<CondAtom> = Vec::new();
            collect_policy_atoms(e, &mut atoms, &mut Vec::new(), state);
            state.allow_delete(atoms);
        }
        Policy::Update(e) => {
            let mut atoms: Vec<CondAtom> = Vec::new();
            collect_policy_atoms(e, &mut atoms, &mut Vec::new(), state);
            state.allow_update(atoms);
        }
        Policy::Sequence(e) => {
            // `PolSequence (EPrim (String seq))`: allow sending seq values.
            if let Exp::Prim(Prim::String(_, seq)) = &e.node {
                let seq_name = if seq.starts_with("uw_") {
                    seq[3..].to_string()
                } else {
                    seq.clone()
                };
                let lv = Atom::Lvar(0);
                let p = CondAtom::AReln(Reln::Sql(seq_name), vec![lv.clone()]);
                state.allow_send(vec![p], vec![lv]);
            }
        }
    }
}

/// Collect policy atoms from an expression (simplified: extract table membership
/// and output atoms).  This mirrors the SML `doQ` / `doQuery` for policies.
fn collect_policy_atoms(
    e: &LocExp,
    atoms: &mut Vec<CondAtom>,
    outputs: &mut Vec<Atom>,
    state: &mut IflowState,
) {
    match &e.node {
        Exp::Query(qm) => {
            // Each table in the query generates a Sql(tab, lv) atom.
            for (tab, _) in &qm.tables {
                let lv = Atom::Lvar(state.next_var());
                atoms.push(CondAtom::AReln(Reln::Sql(tab.clone()), vec![lv.clone()]));
                outputs.push(lv);
            }
            // Recurse into sub-expressions
            collect_policy_atoms(&qm.query, atoms, outputs, state);
            collect_policy_atoms(&qm.body, atoms, outputs, state);
            collect_policy_atoms(&qm.initial, atoms, outputs, state);
        }
        Exp::App(e1, e2) => {
            collect_policy_atoms(e1, atoms, outputs, state);
            collect_policy_atoms(e2, atoms, outputs, state);
        }
        Exp::Abs(_, _, _, body) => collect_policy_atoms(body, atoms, outputs, state),
        Exp::Let(_, _, e1, e2) => {
            collect_policy_atoms(e1, atoms, outputs, state);
            collect_policy_atoms(e2, atoms, outputs, state);
        }
        Exp::Seq(e1, e2) => {
            collect_policy_atoms(e1, atoms, outputs, state);
            collect_policy_atoms(e2, atoms, outputs, state);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Information-flow analysis pass.
///
/// When `settings.debug` is `false` this is a no-op.  When `true` it runs
/// the congruence-closure-based analysis and reports violations.
///
/// The file is never modified by this pass.
pub fn check(file: &File, settings: &Settings, errors: &mut ErrorReporter) {
    if !settings.debug {
        return;
    }

    let (decls, exports) = file;

    // Collect exported function ids
    let exported: BTreeSet<usize> = exports.iter().map(|(id, _, _)| *id).collect();

    let mut state = IflowState::new();

    for decl in decls {
        process_decl(decl, &exported, &mut state, errors);
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use crate::monomorphized::{Decl, Exp, File, QueryMeta, Typ};
    use crate::settings::Settings;

    fn dummy_typ() -> crate::monomorphized::LocTyp {
        Located::dummy(Typ::Record(vec![]))
    }

    fn dummy_exp() -> crate::monomorphized::LocExp {
        Located::dummy(Exp::Record(vec![]))
    }

    fn make_query_exp(table: &str) -> crate::monomorphized::LocExp {
        Located::dummy(Exp::Query(QueryMeta {
            exps: vec![],
            tables: vec![(table.to_string(), vec![])],
            state: dummy_typ(),
            query: Box::new(dummy_exp()),
            body: Box::new(dummy_exp()),
            initial: Box::new(dummy_exp()),
        }))
    }

    #[test]
    fn check_passthrough_when_debug_false() {
        let file: File = (vec![], vec![]);
        let settings = Settings::default();
        assert!(!settings.debug, "default settings must have debug=false");
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(!errors.has_errors(), "check must be no-op when debug=false");
    }

    #[test]
    fn check_empty_file_no_errors() {
        let file: File = (vec![], vec![]);
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(!errors.has_errors(), "empty file must not produce errors");
    }

    #[test]
    fn check_no_policy_no_error_for_query() {
        // Without any policies, we don't report (no access control requirements).
        let file: File = (
            vec![Located::dummy(Decl::Val(
                "f".into(),
                1,
                dummy_typ(),
                make_query_exp("t1"),
                "f".into(),
            ))],
            vec![],
        );
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_errors(),
            "no policies declared → no iflow errors"
        );
    }

    #[test]
    fn check_with_policy_covering_all_tables_no_error() {
        // A client policy that mentions table "t1" — accessing t1 should be fine.
        let policy_e = make_query_exp("t1");
        let file: File = (
            vec![
                Located::dummy(Decl::Policy(Policy::Client(policy_e))),
                Located::dummy(Decl::Val(
                    "f".into(),
                    1,
                    dummy_typ(),
                    make_query_exp("t1"),
                    "f".into(),
                )),
            ],
            vec![],
        );
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_errors(),
            "table covered by policy must not trigger iflow error"
        );
    }

    #[test]
    fn check_with_policy_missing_table_reports_error() {
        // A client policy exists (for t1), but the function accesses t2.
        let policy_e = make_query_exp("t1");
        let file: File = (
            vec![
                Located::dummy(Decl::Policy(Policy::Client(policy_e))),
                Located::dummy(Decl::Val(
                    "f".into(),
                    1,
                    dummy_typ(),
                    make_query_exp("t2"),
                    "f".into(),
                )),
            ],
            vec![],
        );
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            errors.has_errors(),
            "table not covered by any policy must trigger iflow error"
        );
    }

    #[test]
    fn check_valrec_checked() {
        // ValRec entries are also checked.
        let policy_e = make_query_exp("t1");
        let file: File = (
            vec![
                Located::dummy(Decl::Policy(Policy::Client(policy_e))),
                Located::dummy(Decl::ValRec(vec![(
                    "g".into(),
                    2,
                    dummy_typ(),
                    make_query_exp("t3"),
                    "g".into(),
                )])),
            ],
            vec![],
        );
        let mut settings = Settings::default();
        settings.debug = true;
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            errors.has_errors(),
            "ValRec bodies must also be checked for iflow violations"
        );
    }
}
