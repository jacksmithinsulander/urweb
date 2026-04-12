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

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
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
            Atom::Func(Func::DtCon1(..), _) => Some(2),
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

    /// Rebuild the cc-db from the current hyps (used after [`IflowState::reinstate`]).
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
        errors.report(CompileError::type_at_with_hint(
            span.clone(),
            DiagnosticPayload::new(DiagnosticId::InformationFlowPolicyViolation, vec![]),
            DiagnosticId::HintInformationFlowPolicyViolation,
            vec![],
        ));
    }

    /// The SML `send`: check that expression `e` may be sent to the client.
    fn send(&mut self, e: &Atom, span: &Span, errors: &mut ErrorReporter) {
        if e.is_known() || self.db.is_known(e) {
            return;
        }
        self.buildable(e, span, errors);
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

/// Continuation after a subexpression evaluates to an [`Atom`]: explicit enum
/// (no `dyn` trait objects) so the pass stays statically dispatched.
#[derive(Clone)]
enum Kont {
    /// Top-level or diverging subexpression: drop the atom.
    End,
    /// After `Con` inner: wrap with unary constructor `name`.
    Con1 {
        name: String,
        rest: Box<Kont>,
    },
    /// After `Some` inner.
    Some1 {
        rest: Box<Kont>,
    },
    /// After each Basis writer argument: send atom, then evaluate the next arg or finish with `Recd []`.
    WriterRest {
        args: Vec<LocExp>,
        just_finished_index: usize,
        span: Span,
        rest: Box<Kont>,
    },
    /// Collect evaluated FFI (`Other`) arguments left-to-right.
    CollectFfi {
        args: Vec<LocExp>,
        acc: Vec<Atom>,
        func_name: String,
        rest: Box<Kont>,
    },
    /// After `App` onto `Ffi`: send the argument, then continue with `Recd []`.
    AppFfiSendArg {
        outer_span: Span,
        rest: Box<Kont>,
    },
    /// Unary primitive / `Other` wrapper.
    UnopWrap {
        op: String,
        rest: Box<Kont>,
    },
    /// Binary: after left subexpression.
    BinopLeft {
        op: String,
        e2: LocExp,
        env: Vec<Atom>,
        rest: Box<Kont>,
    },
    /// Binary: after right subexpression.
    BinopRight {
        op: String,
        a1: Atom,
        rest: Box<Kont>,
    },
    /// Record fields left-to-right.
    RecordRest {
        fields: Vec<(String, LocExp)>,
        field_index: usize,
        acc: Vec<(String, Atom)>,
        rest: Box<Kont>,
    },
    /// After record subexpression: project field.
    FieldProj {
        field: String,
        rest: Box<Kont>,
    },
    /// String concat: after first operand.
    StrcatLeft {
        e2: LocExp,
        env: Vec<Atom>,
        rest: Box<Kont>,
    },
    StrcatRight {
        a1: Atom,
        rest: Box<Kont>,
    },
    /// After `Write` subexpression: send then continue.
    WriteThen {
        span: Span,
        rest: Box<Kont>,
    },
    /// After `Seq` first expression.
    SeqSecond {
        e2: LocExp,
        env: Vec<Atom>,
        rest: Box<Kont>,
    },
    /// After `Let` binding expression.
    LetBody {
        e2: LocExp,
        base_env: Vec<Atom>,
        rest: Box<Kont>,
    },
    /// Closure environment atoms.
    ClosureRest {
        captured: Vec<LocExp>,
        acc: Vec<Atom>,
        closure_id: usize,
        rest: Box<Kont>,
    },
    /// After SQL `query` initial expression.
    QueryAfterInit {
        outer_span: Span,
        tables: Vec<String>,
        body: LocExp,
        base_env: Vec<Atom>,
        rest: Box<Kont>,
    },
    /// After `Case` discriminant: run each arm (mirrors the former CPS structure).
    CaseDisc {
        arms: Vec<(super::LocPat, LocExp)>,
        outer_span: Span,
        rest: Box<Kont>,
    },
    /// After `Dml` subexpression.
    DmlThen {
        rest: Box<Kont>,
    },
    /// After `Nextval` subexpression.
    NextvalThen {
        rest: Box<Kont>,
    },
    /// After `Setval` first subexpression.
    SetvalFirst {
        e2: LocExp,
        env: Vec<Atom>,
        rest: Box<Kont>,
    },
    SetvalSecond {
        rest: Box<Kont>,
    },
    /// `Error e`: send only.
    ErrorSendOnly {
        span: Span,
    },
    /// After blob half of `ReturnBlob`: send blob, then evaluate mime type.
    ReturnBlobThenMime {
        mime_type: LocExp,
        span: Span,
    },
    /// Send mime atom, then continue `rest`.
    MimeSendOnly {
        span: Span,
        rest: Box<Kont>,
    },
    /// `Redirect`: send only.
    RedirectSendOnly {
        span: Span,
    },
}

/// Resume evaluation with the atom yielded from the most recently finished subexpression.
fn resume_with_atom(
    env: &[Atom],
    state: &mut IflowState,
    errors: &mut ErrorReporter,
    atom: Atom,
    kont: Kont,
) {
    match kont {
        Kont::End => {}
        Kont::Con1 { name, rest } => {
            resume_with_atom(
                env,
                state,
                errors,
                Atom::Func(Func::DtCon1(name), vec![atom]),
                *rest,
            );
        }
        Kont::Some1 { rest } => {
            resume_with_atom(
                env,
                state,
                errors,
                Atom::Func(Func::DtCon1("Some".to_string()), vec![atom]),
                *rest,
            );
        }
        Kont::WriterRest {
            args,
            just_finished_index,
            span,
            rest,
        } => {
            state.send(&atom, &span, errors);
            let next_i = just_finished_index + 1;
            if next_i >= args.len() {
                resume_with_atom(env, state, errors, Atom::Recd(vec![]), *rest);
            } else {
                let next_writer_arg = args[next_i].clone();
                eval_exp(
                    env,
                    state,
                    &next_writer_arg,
                    errors,
                    Kont::WriterRest {
                        args,
                        just_finished_index: next_i,
                        span,
                        rest,
                    },
                );
            }
        }
        Kont::CollectFfi {
            mut acc,
            args,
            func_name,
            rest,
        } => {
            acc.push(atom);
            if acc.len() >= args.len() {
                resume_with_atom(
                    env,
                    state,
                    errors,
                    Atom::Func(Func::Other(func_name), acc),
                    *rest,
                );
            } else {
                let next_i = acc.len();
                let next_ffi_arg = args[next_i].clone();
                eval_exp(
                    env,
                    state,
                    &next_ffi_arg,
                    errors,
                    Kont::CollectFfi {
                        args,
                        acc,
                        func_name,
                        rest,
                    },
                );
            }
        }
        Kont::AppFfiSendArg { outer_span, rest } => {
            state.send(&atom, &outer_span, errors);
            resume_with_atom(env, state, errors, Atom::Recd(vec![]), *rest);
        }
        Kont::UnopWrap { op, rest } => {
            resume_with_atom(
                env,
                state,
                errors,
                Atom::Func(Func::Other(op), vec![atom]),
                *rest,
            );
        }
        Kont::BinopLeft {
            op,
            e2,
            env: saved_env,
            rest,
        } => {
            eval_exp(
                &saved_env,
                state,
                &e2,
                errors,
                Kont::BinopRight { op, a1: atom, rest },
            );
        }
        Kont::BinopRight { op, a1, rest } => {
            resume_with_atom(
                env,
                state,
                errors,
                Atom::Func(Func::Other(op), vec![a1, atom]),
                *rest,
            );
        }
        Kont::RecordRest {
            fields,
            field_index,
            mut acc,
            rest,
        } => {
            let (field_name, _) = &fields[field_index];
            acc.push((field_name.clone(), atom));
            let next_i = field_index + 1;
            if next_i >= fields.len() {
                resume_with_atom(env, state, errors, Atom::Recd(acc), *rest);
            } else {
                let next_record_exp = fields[next_i].1.clone();
                eval_exp(
                    env,
                    state,
                    &next_record_exp,
                    errors,
                    Kont::RecordRest {
                        fields,
                        field_index: next_i,
                        acc,
                        rest,
                    },
                );
            }
        }
        Kont::FieldProj { field, rest } => {
            resume_with_atom(env, state, errors, Atom::Proj(Box::new(atom), field), *rest);
        }
        Kont::StrcatLeft {
            e2,
            env: saved_env,
            rest,
        } => {
            eval_exp(
                &saved_env,
                state,
                &e2,
                errors,
                Kont::StrcatRight { a1: atom, rest },
            );
        }
        Kont::StrcatRight { a1, rest } => {
            resume_with_atom(
                env,
                state,
                errors,
                Atom::Func(Func::Other("cat".to_string()), vec![a1, atom]),
                *rest,
            );
        }
        Kont::WriteThen { span, rest } => {
            state.send(&atom, &span, errors);
            resume_with_atom(env, state, errors, Atom::Recd(vec![]), *rest);
        }
        Kont::SeqSecond {
            e2,
            env: saved_env,
            rest,
        } => {
            eval_exp(&saved_env, state, &e2, errors, *rest);
        }
        Kont::LetBody {
            e2,
            mut base_env,
            rest,
        } => {
            base_env.push(atom);
            eval_exp(&base_env, state, &e2, errors, *rest);
        }
        Kont::ClosureRest {
            captured,
            mut acc,
            closure_id,
            rest,
        } => {
            acc.push(atom);
            if acc.len() >= captured.len() {
                let name = format!("Cl{}", closure_id);
                resume_with_atom(
                    env,
                    state,
                    errors,
                    Atom::Func(Func::Other(name), acc),
                    *rest,
                );
            } else {
                let idx = acc.len();
                let next_captured_exp = captured[idx].clone();
                eval_exp(
                    env,
                    state,
                    &next_captured_exp,
                    errors,
                    Kont::ClosureRest {
                        captured,
                        acc,
                        closure_id,
                        rest,
                    },
                );
            }
        }
        Kont::QueryAfterInit {
            outer_span,
            tables,
            body,
            base_env,
            rest,
        } => {
            let init_atom = atom;
            let r = state.fresh_var();
            let acc = state.fresh_var();
            let mut query_atoms: Vec<CondAtom> = Vec::new();
            let mut row_vars: Vec<Atom> = Vec::new();
            for tab in &tables {
                let row_var = state.fresh_var();
                query_atoms.push(CondAtom::AReln(
                    Reln::Sql(tab.clone()),
                    vec![row_var.clone()],
                ));
                row_vars.push(row_var);
            }
            state.assert_atoms(&query_atoms);
            for row_var in &row_vars {
                state.send(row_var, &outer_span, errors);
            }
            state.assert_atoms(&[CondAtom::AReln(Reln::Eq, vec![r.clone(), init_atom])]);
            let mut body_env = base_env;
            body_env.push(r);
            body_env.push(acc);
            eval_exp(&body_env, state, &body, errors, *rest);
        }
        Kont::CaseDisc {
            arms,
            outer_span,
            rest,
        } => {
            let discriminant_atom = atom;
            for (arm_pat, arm_body) in arms {
                let saved = state.stash();
                let mut arm_env = env.to_vec();
                eval_pat(
                    &mut arm_env,
                    state,
                    discriminant_atom.clone(),
                    &arm_pat.node,
                );
                eval_exp(&arm_env, state, &arm_body, errors, (*rest).clone());
                state.reinstate(saved);
            }
            let _ = outer_span;
        }
        Kont::DmlThen { rest } => {
            resume_with_atom(env, state, errors, Atom::Recd(vec![]), *rest);
        }
        Kont::NextvalThen { rest } => {
            let nv = state.fresh_var();
            if let Atom::Const(Prim::String(_, s)) = &atom {
                let seq_name = s
                    .strip_prefix("uw_")
                    .map(|t| t.to_string())
                    .unwrap_or_else(|| s.clone());
                state.assert_atoms(&[CondAtom::AReln(Reln::Sql(seq_name), vec![nv.clone()])]);
            }
            resume_with_atom(env, state, errors, nv, *rest);
        }
        Kont::SetvalFirst {
            e2,
            env: saved_env,
            rest,
        } => {
            eval_exp(&saved_env, state, &e2, errors, Kont::SetvalSecond { rest });
        }
        Kont::SetvalSecond { rest } => {
            resume_with_atom(env, state, errors, Atom::Recd(vec![]), *rest);
        }
        Kont::ErrorSendOnly { span } => {
            state.send(&atom, &span, errors);
        }
        Kont::ReturnBlobThenMime { mime_type, span } => {
            state.send(&atom, &span, errors);
            eval_exp(
                env,
                state,
                &mime_type,
                errors,
                Kont::MimeSendOnly {
                    span,
                    rest: Box::new(Kont::End),
                },
            );
        }
        Kont::MimeSendOnly { span, rest } => {
            state.send(&atom, &span, errors);
            resume_with_atom(env, state, errors, Atom::Recd(vec![]), *rest);
        }
        Kont::RedirectSendOnly { span } => {
            state.send(&atom, &span, errors);
        }
    }
}

/// Evaluate a Mono expression to completion under continuation `kont`.
fn eval_exp(
    env: &[Atom],
    state: &mut IflowState,
    e: &LocExp,
    errors: &mut ErrorReporter,
    kont: Kont,
) {
    let span = &e.span;

    macro_rules! eval_default {
        () => {{
            let placeholder_var = state.fresh_var();
            resume_with_atom(env, state, errors, placeholder_var, kont);
        }};
    }

    match &e.node {
        Exp::Prim(p) => resume_with_atom(env, state, errors, Atom::Const(p.clone()), kont),

        Exp::Rel(n) => {
            let rel_atom = env
                .get(env.len().saturating_sub(1 + n))
                .cloned()
                .unwrap_or_else(|| state.fresh_var());
            resume_with_atom(env, state, errors, rel_atom, kont);
        }

        Exp::Named(_) => eval_default!(),

        Exp::Con(_, pc, None) => {
            let con_name = pat_con_name(pc);
            resume_with_atom(
                env,
                state,
                errors,
                Atom::Func(Func::DtCon0(con_name), vec![]),
                kont,
            );
        }

        Exp::Con(_, pc, Some(inner)) => {
            let con_name = pat_con_name(pc);
            eval_exp(
                env,
                state,
                inner,
                errors,
                Kont::Con1 {
                    name: con_name,
                    rest: Box::new(kont),
                },
            );
        }

        Exp::None(_) => {
            resume_with_atom(
                env,
                state,
                errors,
                Atom::Func(Func::DtCon0("None".to_string()), vec![]),
                kont,
            );
        }

        Exp::Some(_, inner) => {
            eval_exp(
                env,
                state,
                inner,
                errors,
                Kont::Some1 {
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Ffi(_, _) => eval_default!(),

        Exp::FfiApp(module, name, args) => {
            if module == "Basis" && is_writer(name) {
                let writer_args: Vec<LocExp> = args.iter().map(|(a, _)| a.clone()).collect();
                let outer_span = span.clone();
                if writer_args.is_empty() {
                    resume_with_atom(env, state, errors, Atom::Recd(vec![]), kont);
                } else {
                    let head_writer_arg = writer_args[0].clone();
                    eval_exp(
                        env,
                        state,
                        &head_writer_arg,
                        errors,
                        Kont::WriterRest {
                            args: writer_args,
                            just_finished_index: 0,
                            span: outer_span,
                            rest: Box::new(kont),
                        },
                    );
                }
                return;
            }
            let full_name = format!("{}.{}", module, name);
            let ffi_args: Vec<LocExp> = args.iter().map(|(a, _)| a.clone()).collect();
            if ffi_args.is_empty() {
                resume_with_atom(
                    env,
                    state,
                    errors,
                    Atom::Func(Func::Other(full_name), vec![]),
                    kont,
                );
            } else {
                let head_ffi_arg = ffi_args[0].clone();
                eval_exp(
                    env,
                    state,
                    &head_ffi_arg,
                    errors,
                    Kont::CollectFfi {
                        args: ffi_args,
                        acc: vec![],
                        func_name: full_name,
                        rest: Box::new(kont),
                    },
                );
            }
        }

        Exp::App(f_exp, arg_exp) => match &f_exp.node {
            Exp::Ffi(_, _) => {
                let arg = arg_exp.clone();
                let outer_span = span.clone();
                eval_exp(
                    env,
                    state,
                    &arg,
                    errors,
                    Kont::AppFfiSendArg {
                        outer_span,
                        rest: Box::new(kont),
                    },
                );
            }
            Exp::Error(_, _) => {
                eval_exp(env, state, f_exp, errors, kont);
            }
            _ => eval_default!(),
        },

        Exp::Abs(_, _, _, _) => eval_default!(),

        Exp::Unop(s, e1) => {
            let op_label = s.clone();
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::UnopWrap {
                    op: op_label,
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Binop(_, s, e1, e2) => {
            let op_label = s.clone();
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::BinopLeft {
                    op: op_label,
                    e2: (**e2).clone(),
                    env: env.to_vec(),
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Record(record_fields) => {
            let fields: Vec<(String, LocExp)> = record_fields
                .iter()
                .map(|(field_name, exp, _)| (field_name.clone(), exp.clone()))
                .collect();
            if fields.is_empty() {
                resume_with_atom(env, state, errors, Atom::Recd(vec![]), kont);
            } else {
                let first_record_exp = fields[0].1.clone();
                eval_exp(
                    env,
                    state,
                    &first_record_exp,
                    errors,
                    Kont::RecordRest {
                        fields,
                        field_index: 0,
                        acc: vec![],
                        rest: Box::new(kont),
                    },
                );
            }
        }

        Exp::Field(record_exp, field_name) => {
            let field_name_clone = field_name.clone();
            eval_exp(
                env,
                state,
                record_exp,
                errors,
                Kont::FieldProj {
                    field: field_name_clone,
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Case(disc_exp, arms, _) => {
            let outer_span = span.clone();
            eval_exp(
                env,
                state,
                disc_exp,
                errors,
                Kont::CaseDisc {
                    arms: arms.clone(),
                    outer_span,
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Strcat(e1, e2) => {
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::StrcatLeft {
                    e2: (**e2).clone(),
                    env: env.to_vec(),
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Error(e1, _) => {
            let outer_span = span.clone();
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::ErrorSendOnly { span: outer_span },
            );
        }

        Exp::ReturnBlob {
            blob, mime_type, ..
        } => {
            let outer_span = span.clone();
            let mime_loc = (**mime_type).clone();
            if let Some(b) = blob {
                let blob_exp = (**b).clone();
                eval_exp(
                    env,
                    state,
                    &blob_exp,
                    errors,
                    Kont::ReturnBlobThenMime {
                        mime_type: mime_loc,
                        span: outer_span,
                    },
                );
            } else {
                eval_exp(
                    env,
                    state,
                    &mime_loc,
                    errors,
                    Kont::MimeSendOnly {
                        span: outer_span,
                        rest: Box::new(Kont::End),
                    },
                );
            }
        }

        Exp::Redirect(e1, _) => {
            let outer_span = span.clone();
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::RedirectSendOnly { span: outer_span },
            );
        }

        Exp::Write(e1) => {
            let outer_span = span.clone();
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::WriteThen {
                    span: outer_span,
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Seq(e1, e2) => {
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::SeqSecond {
                    e2: (**e2).clone(),
                    env: env.to_vec(),
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Let(_, _, e1, e2) => {
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::LetBody {
                    e2: (**e2).clone(),
                    base_env: env.to_vec(),
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Closure(n, captured) => {
            let closure_n = *n;
            let captured_exprs: Vec<LocExp> = captured.clone();
            if captured_exprs.is_empty() {
                let name = format!("Cl{}", closure_n);
                resume_with_atom(
                    env,
                    state,
                    errors,
                    Atom::Func(Func::Other(name), vec![]),
                    kont,
                );
            } else {
                let head_captured_exp = captured_exprs[0].clone();
                eval_exp(
                    env,
                    state,
                    &head_captured_exp,
                    errors,
                    Kont::ClosureRest {
                        captured: captured_exprs,
                        acc: vec![],
                        closure_id: closure_n,
                        rest: Box::new(kont),
                    },
                );
            }
        }

        Exp::Query(qm) => {
            let outer_span = span.clone();
            let body = (*qm.body).clone();
            let initial = (*qm.initial).clone();
            let tables: Vec<String> = qm.tables.iter().map(|(t, _)| t.clone()).collect();
            eval_exp(
                env,
                state,
                &initial,
                errors,
                Kont::QueryAfterInit {
                    outer_span,
                    tables,
                    body,
                    base_env: env.to_vec(),
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Dml(e1, _) => {
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::DmlThen {
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Nextval(e1) => {
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::NextvalThen {
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Setval(e1, e2) => {
            eval_exp(
                env,
                state,
                e1,
                errors,
                Kont::SetvalFirst {
                    e2: (**e2).clone(),
                    env: env.to_vec(),
                    rest: Box::new(kont),
                },
            );
        }

        Exp::Uurlify(inner, _, _) => {
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
                        resume_with_atom(env, state, errors, nv, kont);
                        return;
                    }
                }
                _ => {}
            }
            eval_default!()
        }

        Exp::JavaScript(_, _) => eval_default!(),
        Exp::SignalReturn(_) => eval_default!(),
        Exp::SignalBind(_, _) => eval_default!(),
        Exp::SignalSource(_) => eval_default!(),
        Exp::ServerCall(_, _, _, _) => eval_default!(),
        Exp::Recv(_, _) => eval_default!(),
        Exp::Sleep(_) => eval_default!(),
        Exp::Spawn(_) => eval_default!(),
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
            let _real_name = tab
                .strip_prefix("uw_")
                .map(|t| t.to_string())
                .unwrap_or_else(|| tab.clone());
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
            eval_exp(&env, state, &inner_e, errors, Kont::End);
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
                eval_exp(&env, state, &inner_e, errors, Kont::End);
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
                let seq_name = seq
                    .strip_prefix("uw_")
                    .map(|t| t.to_string())
                    .unwrap_or_else(|| seq.clone());
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
        assert!(
            !errors.has_hard_errors(),
            "check must be no-op when debug=false"
        );
    }

    #[test]
    fn check_empty_file_no_errors() {
        let file: File = (vec![], vec![]);
        let settings = Settings {
            debug: true,
            ..Default::default()
        };
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_hard_errors(),
            "empty file must not produce hard errors"
        );
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
        let settings = Settings {
            debug: true,
            ..Default::default()
        };
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_hard_errors(),
            "no policies declared → no iflow hard errors"
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
        let settings = Settings {
            debug: true,
            ..Default::default()
        };
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            !errors.has_hard_errors(),
            "table covered by policy must not trigger iflow hard error"
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
        let settings = Settings {
            debug: true,
            ..Default::default()
        };
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            errors.has_hard_errors(),
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
        let settings = Settings {
            debug: true,
            ..Default::default()
        };
        let mut errors = ErrorReporter::new();
        check(&file, &settings, &mut errors);
        assert!(
            errors.has_hard_errors(),
            "ValRec bodies must also be checked for iflow violations"
        );
    }
}
