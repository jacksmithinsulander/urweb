#![allow(dead_code, unused_variables, unused_imports)]

//! Cache of module code with dependency information.
//!
//! Translated from `mod_db.sml`.

use std::collections::{HashMap, HashSet};
use std::sync::Mutex;
use std::time::SystemTime;

use crate::elaborated::{
    Constructor, Declaration, Expression, LocatedDeclaration, Signature, Structure,
};

// ---------------------------------------------------------------------------
// One cached module entry
// ---------------------------------------------------------------------------

/// A single cached module.
#[derive(Debug, Clone)]
pub struct OneMod {
    /// The elaborated top-level declaration for this module.
    pub decl: LocatedDeclaration,
    /// The timestamp of the source file when this was compiled.
    pub when: SystemTime,
    /// Transitive set of module names this module depends on.
    pub deps: HashSet<String>,
    /// Whether the module was compiled with errors.
    /// Modules with errors are kept so tooling can still find them.
    pub has_errors: bool,
}

// ---------------------------------------------------------------------------
// Global module database
// ---------------------------------------------------------------------------

/// The module database, keyed by module name.
pub struct ModDb {
    /// Primary index: name -> module record
    by_name: HashMap<String, OneMod>,
    /// Secondary index: numeric module id -> name (for dependency tracking)
    by_id: HashMap<usize, String>,
    /// Snapshot for rollback
    by_name_backup: HashMap<String, OneMod>,
    by_id_backup: HashMap<usize, String>,
}

impl ModDb {
    pub fn new() -> Self {
        ModDb {
            by_name: HashMap::new(),
            by_id: HashMap::new(),
            by_name_backup: HashMap::new(),
            by_id_backup: HashMap::new(),
        }
    }

    /// Clear all entries (mirrors SML `reset`).
    pub fn reset(&mut self) {
        self.by_name.clear();
        self.by_id.clear();
    }

    // -----------------------------------------------------------------------
    // Debug printing
    // -----------------------------------------------------------------------

    pub fn print_by_name(&self) {
        eprintln!("Contents of ModDb.by_name:");
        let mut names: Vec<&String> = self.by_name.keys().collect();
        names.sort();
        for name in names {
            let m = &self.by_name[name];
            let deps: Vec<&str> = {
                let mut v: Vec<&str> = m.deps.iter().map(|s| s.as_str()).collect();
                v.sort();
                v
            };
            let when = m
                .when
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs().to_string())
                .unwrap_or_else(|_| "?".to_string());
            eprintln!(
                "  {}. Stored at: {}. HasErrors: {}. Deps: {}",
                name,
                when,
                m.has_errors,
                deps.join(", ")
            );
        }
    }

    // -----------------------------------------------------------------------
    // Undetermined unification variable check
    // -----------------------------------------------------------------------

    /// Returns `true` if the declaration contains any unsolved expression
    /// unification variables (`EUnif` with `None`).
    ///
    /// Mirrors `dContainsUndeterminedUnif`.
    fn contains_undetermined_unif(d: &LocatedDeclaration) -> bool {
        contains_unif_decl(d)
    }

    // -----------------------------------------------------------------------
    // insert
    // -----------------------------------------------------------------------

    /// Insert a newly elaborated module declaration into the database.
    ///
    /// Mirrors `ModDb.insert`.
    pub fn insert(&mut self, d: LocatedDeclaration, tm: SystemTime, has_errors: bool) {
        // Extract module name and numeric id from the decl
        let xn: Option<(String, usize)> = match &d.node {
            Declaration::Structure(x, n, _, _) => Some((x.clone(), *n)),
            Declaration::FfiStr(x, n, _) => Some((x.clone(), *n)),
            _ => None,
        };

        let (x, n) = match xn {
            None => return,
            Some(pair) => pair,
        };

        // Skip re-insertion if the timestamp matches and the old entry was clean
        let skip_it = if let Some(r) = self.by_name.get(&x) {
            r.when == tm && !r.has_errors && !Self::contains_undetermined_unif(&r.decl)
        } else {
            false
        };

        if skip_it {
            return;
        }

        // Compute transitive dependency set by walking the AST
        let deps = compute_deps(&d, &self.by_id, &self.by_name);

        // Remove entries whose dependency set includes x (they depended on the
        // old version of this module and must be invalidated)
        let to_remove: Vec<String> = self
            .by_name
            .iter()
            .filter(|(_, r)| r.deps.contains(&x))
            .map(|(name, _)| name.clone())
            .collect();

        for name in &to_remove {
            if let Some(r) = self.by_name.remove(name) {
                // Also remove from by_id
                let id_to_remove: Option<usize> = match &r.decl.node {
                    Declaration::Structure(_, n2, _, _) => Some(*n2),
                    Declaration::FfiStr(_, n2, _) => Some(*n2),
                    _ => None,
                };
                if let Some(id) = id_to_remove {
                    self.by_id.remove(&id);
                }
            }
        }

        // Insert the new entry
        self.by_name.insert(
            x.clone(),
            OneMod {
                decl: d,
                when: tm,
                deps,
                has_errors,
            },
        );
        self.by_id.insert(n, x);
    }

    // -----------------------------------------------------------------------
    // lookup (from a Source decl)
    // -----------------------------------------------------------------------

    /// Look up a cached elaborated module corresponding to a source declaration.
    ///
    /// Returns `Some(decl)` when there is a clean, up-to-date cached entry.
    ///
    /// Mirrors `ModDb.lookup`.
    pub fn lookup(&self, name: &str, tm: SystemTime) -> Option<&LocatedDeclaration> {
        if let Some(r) = self.by_name.get(name) {
            if r.when == tm && !r.has_errors && !Self::contains_undetermined_unif(&r.decl) {
                return Some(&r.decl);
            }
        }
        None
    }

    // -----------------------------------------------------------------------
    // lookupModAndDepsIncludingErrored
    // -----------------------------------------------------------------------

    /// Look up a module and all its dependencies (including errored ones).
    ///
    /// Returns `(main_decl, dep_decls)` or `None` if the module is not found.
    ///
    /// Mirrors `ModDb.lookupModAndDepsIncludingErrored`.
    pub fn lookup_mod_and_deps_including_errored(
        &self,
        name: &str,
    ) -> Option<(&LocatedDeclaration, Vec<&LocatedDeclaration>)> {
        let m = self.by_name.get(name)?;

        // Collect deps, ensuring "Basis" and "Top" come first without duplicates
        let mut deps: Vec<&str> = m
            .deps
            .iter()
            .map(|s| s.as_str())
            .filter(|&s| s != "Basis" && s != "Top")
            .collect();
        deps.sort();
        let mut ordered_deps = vec!["Basis", "Top"];
        ordered_deps.extend(deps);

        let dep_decls: Vec<&LocatedDeclaration> = ordered_deps
            .into_iter()
            .filter_map(|d| self.by_name.get(d).map(|r| &r.decl))
            .collect();

        Some((&m.decl, dep_decls))
    }

    // -----------------------------------------------------------------------
    // snapshot / revert
    // -----------------------------------------------------------------------

    /// Save the current database state (mirrors `ModDb.snapshot`).
    pub fn snapshot(&mut self) {
        self.by_name_backup = self.by_name.clone();
        self.by_id_backup = self.by_id.clone();
    }

    /// Restore the database to the last snapshot (mirrors `ModDb.revert`).
    pub fn revert(&mut self) {
        self.by_name = self.by_name_backup.clone();
        self.by_id = self.by_id_backup.clone();
    }
}

impl Default for ModDb {
    fn default() -> Self {
        ModDb::new()
    }
}

// ---------------------------------------------------------------------------
// Dependency computation (AST walk)
// ---------------------------------------------------------------------------

/// Walk a declaration and collect the transitive dependency set.
fn compute_deps(
    d: &LocatedDeclaration,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
) -> HashSet<String> {
    let mut deps: HashSet<String> = HashSet::new();
    collect_deps_decl(d, by_id, by_name, &mut deps);
    deps
}

fn do_mod(
    n: usize,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    if let Some(name) = by_id.get(&n) {
        // Add the module's own transitive deps
        if let Some(r) = by_name.get(name) {
            for dep in &r.deps {
                deps.insert(dep.clone());
            }
        }
        deps.insert(name.clone());
    }
    // If not found in by_id, we silently skip (mirrors SML behaviour of not raising)
}

// ---------------------------------------------------------------------------
// Recursive AST walkers
// ---------------------------------------------------------------------------

fn collect_deps_decl(
    d: &LocatedDeclaration,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    match &d.node {
        Declaration::Constructor(_, _, _, c) => collect_deps_con(c, by_id, by_name, deps),
        Declaration::Datatype(dts) => {
            for dt in dts {
                for (_, _, co) in &dt.constrs {
                    if let Some(c) = co {
                        collect_deps_con(c, by_id, by_name, deps);
                    }
                }
            }
        }
        Declaration::DatatypeImp { orig_mod, .. } => do_mod(*orig_mod, by_id, by_name, deps),
        Declaration::Val(_, _, c, e) => {
            collect_deps_con(c, by_id, by_name, deps);
            collect_deps_exp(e, by_id, by_name, deps);
        }
        Declaration::ValRec(vs) => {
            for (_, _, c, e) in vs {
                collect_deps_con(c, by_id, by_name, deps);
                collect_deps_exp(e, by_id, by_name, deps);
            }
        }
        Declaration::Signature(_, _, s) => collect_deps_sgn(s, by_id, by_name, deps),
        Declaration::Structure(_, _, s, st) => {
            collect_deps_sgn(s, by_id, by_name, deps);
            collect_deps_str(st, by_id, by_name, deps);
        }
        Declaration::FfiStr(_, _, s) => collect_deps_sgn(s, by_id, by_name, deps),
        Declaration::Constraint(c1, c2) => {
            collect_deps_con(c1, by_id, by_name, deps);
            collect_deps_con(c2, by_id, by_name, deps);
        }
        Declaration::Export(_, s, st) => {
            collect_deps_sgn(s, by_id, by_name, deps);
            collect_deps_str(st, by_id, by_name, deps);
        }
        Declaration::Table {
            con,
            exp,
            pk_con,
            pk_exp,
            unique_con,
            ..
        } => {
            collect_deps_con(con, by_id, by_name, deps);
            collect_deps_exp(exp, by_id, by_name, deps);
            collect_deps_con(pk_con, by_id, by_name, deps);
            collect_deps_exp(pk_exp, by_id, by_name, deps);
            collect_deps_con(unique_con, by_id, by_name, deps);
        }
        Declaration::View(_, _, _, e, c) => {
            collect_deps_exp(e, by_id, by_name, deps);
            collect_deps_con(c, by_id, by_name, deps);
        }
        Declaration::Index(e1, e2) => {
            collect_deps_exp(e1, by_id, by_name, deps);
            collect_deps_exp(e2, by_id, by_name, deps);
        }
        Declaration::Cookie(_, _, _, c) => collect_deps_con(c, by_id, by_name, deps),
        Declaration::Task(e1, e2) => {
            collect_deps_exp(e1, by_id, by_name, deps);
            collect_deps_exp(e2, by_id, by_name, deps);
        }
        Declaration::Policy(e) => collect_deps_exp(e, by_id, by_name, deps),
        Declaration::OnError(n, _, _) => do_mod(*n, by_id, by_name, deps),
        Declaration::Ffi(_, _, _, c) => collect_deps_con(c, by_id, by_name, deps),
        // Sequence, Style, Database have no sub-terms with module refs
        Declaration::Sequence(_, _, _) | Declaration::Style(_, _, _) | Declaration::Database(_) => {
        }
    }
}

fn collect_deps_con(
    c: &crate::elaborated::LocatedConstructor,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    match &c.node {
        Constructor::ModProj(n, _, _) => do_mod(*n, by_id, by_name, deps),
        Constructor::TFun(a, b) => {
            collect_deps_con(a, by_id, by_name, deps);
            collect_deps_con(b, by_id, by_name, deps);
        }
        Constructor::TCFun(_, _, _, body) => collect_deps_con(body, by_id, by_name, deps),
        Constructor::TRecord(r) => collect_deps_con(r, by_id, by_name, deps),
        Constructor::TDisjoint(a, b, c2) => {
            collect_deps_con(a, by_id, by_name, deps);
            collect_deps_con(b, by_id, by_name, deps);
            collect_deps_con(c2, by_id, by_name, deps);
        }
        Constructor::App(f, x) => {
            collect_deps_con(f, by_id, by_name, deps);
            collect_deps_con(x, by_id, by_name, deps);
        }
        Constructor::Abs(_, _, body) => collect_deps_con(body, by_id, by_name, deps),
        Constructor::KAbs(_, body) => collect_deps_con(body, by_id, by_name, deps),
        Constructor::KApp(c2, _) => collect_deps_con(c2, by_id, by_name, deps),
        Constructor::TKFun(_, body) => collect_deps_con(body, by_id, by_name, deps),
        Constructor::Record(_, xcs) => {
            for (x, v) in xcs {
                collect_deps_con(x, by_id, by_name, deps);
                collect_deps_con(v, by_id, by_name, deps);
            }
        }
        Constructor::Concat(a, b) => {
            collect_deps_con(a, by_id, by_name, deps);
            collect_deps_con(b, by_id, by_name, deps);
        }
        Constructor::Tuple(cs) => {
            for ci in cs {
                collect_deps_con(ci, by_id, by_name, deps);
            }
        }
        Constructor::Proj(c2, _) => collect_deps_con(c2, by_id, by_name, deps),
        _ => {}
    }
}

fn collect_deps_exp(
    e: &crate::elaborated::LocatedExpression,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    use crate::elaborated::Expression;
    match &e.node {
        Expression::ModProj(n, _, _) => do_mod(*n, by_id, by_name, deps),
        Expression::App(f, x) => {
            collect_deps_exp(f, by_id, by_name, deps);
            collect_deps_exp(x, by_id, by_name, deps);
        }
        Expression::Abs(_, c1, c2, body) => {
            collect_deps_con(c1, by_id, by_name, deps);
            collect_deps_con(c2, by_id, by_name, deps);
            collect_deps_exp(body, by_id, by_name, deps);
        }
        Expression::CApp(f, c) => {
            collect_deps_exp(f, by_id, by_name, deps);
            collect_deps_con(c, by_id, by_name, deps);
        }
        Expression::CAbs(_, _, _, body) => collect_deps_exp(body, by_id, by_name, deps),
        Expression::KAbs(_, body) => collect_deps_exp(body, by_id, by_name, deps),
        Expression::KApp(f, _) => collect_deps_exp(f, by_id, by_name, deps),
        Expression::Record(fields) => {
            for (n, v, t) in fields {
                collect_deps_con(n, by_id, by_name, deps);
                collect_deps_exp(v, by_id, by_name, deps);
                collect_deps_con(t, by_id, by_name, deps);
            }
        }
        Expression::Field(body, c, meta) => {
            collect_deps_exp(body, by_id, by_name, deps);
            collect_deps_con(c, by_id, by_name, deps);
            collect_deps_con(&meta.field, by_id, by_name, deps);
            collect_deps_con(&meta.rest, by_id, by_name, deps);
        }
        Expression::Concat(e1, c1, e2, c2) => {
            collect_deps_exp(e1, by_id, by_name, deps);
            collect_deps_con(c1, by_id, by_name, deps);
            collect_deps_exp(e2, by_id, by_name, deps);
            collect_deps_con(c2, by_id, by_name, deps);
        }
        Expression::Cut(body, c, meta) => {
            collect_deps_exp(body, by_id, by_name, deps);
            collect_deps_con(c, by_id, by_name, deps);
            collect_deps_con(&meta.field, by_id, by_name, deps);
            collect_deps_con(&meta.rest, by_id, by_name, deps);
        }
        Expression::CutMulti(body, c, meta) => {
            collect_deps_exp(body, by_id, by_name, deps);
            collect_deps_con(c, by_id, by_name, deps);
            collect_deps_con(&meta.rest, by_id, by_name, deps);
        }
        Expression::Case(disc, arms, meta) => {
            collect_deps_exp(disc, by_id, by_name, deps);
            for (_, arm_e) in arms {
                collect_deps_exp(arm_e, by_id, by_name, deps);
            }
            collect_deps_con(&meta.disc, by_id, by_name, deps);
            collect_deps_con(&meta.result, by_id, by_name, deps);
        }
        Expression::Let(decls, body, c) => {
            for edecl in decls {
                collect_deps_edecl(edecl, by_id, by_name, deps);
            }
            collect_deps_exp(body, by_id, by_name, deps);
            collect_deps_con(c, by_id, by_name, deps);
        }
        _ => {}
    }
}

fn collect_deps_edecl(
    ed: &crate::elaborated::LocatedElaboratedDeclaration,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    use crate::elaborated::ElaboratedDeclaration;
    match &ed.node {
        ElaboratedDeclaration::Val(_, c, e) => {
            collect_deps_con(c, by_id, by_name, deps);
            collect_deps_exp(e, by_id, by_name, deps);
        }
        ElaboratedDeclaration::ValRec(vs) => {
            for (_, c, e) in vs {
                collect_deps_con(c, by_id, by_name, deps);
                collect_deps_exp(e, by_id, by_name, deps);
            }
        }
    }
}

fn collect_deps_sgn(
    s: &crate::elaborated::LocatedSignature,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    use crate::elaborated::Signature;
    match &s.node {
        Signature::Const(items) => {
            for item in items {
                collect_deps_sgn_item(item, by_id, by_name, deps);
            }
        }
        Signature::Fun(_, _, dom, cod) => {
            collect_deps_sgn(dom, by_id, by_name, deps);
            collect_deps_sgn(cod, by_id, by_name, deps);
        }
        Signature::Where(s2, _, _, c) => {
            collect_deps_sgn(s2, by_id, by_name, deps);
            collect_deps_con(c, by_id, by_name, deps);
        }
        Signature::Proj(n, _, _) => do_mod(*n, by_id, by_name, deps),
        _ => {}
    }
}

fn collect_deps_sgn_item(
    item: &crate::elaborated::LocatedSignatureItem,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    use crate::elaborated::SignatureItem;
    match &item.node {
        SignatureItem::Constructor(_, _, _, c) => collect_deps_con(c, by_id, by_name, deps),
        SignatureItem::Datatype(dts) => {
            for dt in dts {
                for (_, _, co) in &dt.constrs {
                    if let Some(c) = co {
                        collect_deps_con(c, by_id, by_name, deps);
                    }
                }
            }
        }
        SignatureItem::DatatypeImp { orig_mod, .. } => do_mod(*orig_mod, by_id, by_name, deps),
        SignatureItem::Val(_, _, c) => collect_deps_con(c, by_id, by_name, deps),
        SignatureItem::Structure(_, _, _, s) => collect_deps_sgn(s, by_id, by_name, deps),
        SignatureItem::Signature(_, _, s) => collect_deps_sgn(s, by_id, by_name, deps),
        SignatureItem::Constraint(c1, c2) => {
            collect_deps_con(c1, by_id, by_name, deps);
            collect_deps_con(c2, by_id, by_name, deps);
        }
        SignatureItem::Class(_, _, _, c) => collect_deps_con(c, by_id, by_name, deps),
        _ => {}
    }
}

fn collect_deps_str(
    st: &crate::elaborated::LocatedStructure,
    by_id: &HashMap<usize, String>,
    by_name: &HashMap<String, OneMod>,
    deps: &mut HashSet<String>,
) {
    use crate::elaborated::Structure;
    match &st.node {
        Structure::Const(decls) => {
            for d in decls {
                collect_deps_decl(d, by_id, by_name, deps);
            }
        }
        Structure::Var(n) => do_mod(*n, by_id, by_name, deps),
        Structure::Proj(s2, _) => collect_deps_str(s2, by_id, by_name, deps),
        Structure::Fun(_, _, dom, cod, body) => {
            collect_deps_sgn(dom, by_id, by_name, deps);
            collect_deps_sgn(cod, by_id, by_name, deps);
            collect_deps_str(body, by_id, by_name, deps);
        }
        Structure::App(s1, s2) => {
            collect_deps_str(s1, by_id, by_name, deps);
            collect_deps_str(s2, by_id, by_name, deps);
        }
        Structure::Error => {}
    }
}

// ---------------------------------------------------------------------------
// Undetermined unification variable check (AST walk)
// ---------------------------------------------------------------------------

fn contains_unif_decl(d: &LocatedDeclaration) -> bool {
    match &d.node {
        Declaration::Val(_, _, _, e) => contains_unif_exp(e),
        Declaration::ValRec(vs) => vs.iter().any(|(_, _, _, e)| contains_unif_exp(e)),
        Declaration::Structure(_, _, _, st) => contains_unif_str(st),
        _ => false,
    }
}

fn contains_unif_exp(e: &crate::elaborated::LocatedExpression) -> bool {
    use crate::elaborated::Expression;
    match &e.node {
        Expression::Unif(r) => r.lock().unwrap().is_none(),
        Expression::App(f, x) => contains_unif_exp(f) || contains_unif_exp(x),
        Expression::Abs(_, _, _, body) => contains_unif_exp(body),
        Expression::CApp(f, _) => contains_unif_exp(f),
        Expression::CAbs(_, _, _, body) => contains_unif_exp(body),
        Expression::KAbs(_, body) => contains_unif_exp(body),
        Expression::KApp(f, _) => contains_unif_exp(f),
        Expression::Record(fields) => fields.iter().any(|(_, v, _)| contains_unif_exp(v)),
        Expression::Field(body, _, _) => contains_unif_exp(body),
        Expression::Concat(e1, _, e2, _) => contains_unif_exp(e1) || contains_unif_exp(e2),
        Expression::Cut(body, _, _) => contains_unif_exp(body),
        Expression::CutMulti(body, _, _) => contains_unif_exp(body),
        Expression::Case(disc, arms, _) => {
            contains_unif_exp(disc) || arms.iter().any(|(_, arm_e)| contains_unif_exp(arm_e))
        }
        Expression::Let(decls, body, _) => {
            decls.iter().any(|ed| contains_unif_edecl(ed)) || contains_unif_exp(body)
        }
        _ => false,
    }
}

fn contains_unif_edecl(ed: &crate::elaborated::LocatedElaboratedDeclaration) -> bool {
    use crate::elaborated::ElaboratedDeclaration;
    match &ed.node {
        ElaboratedDeclaration::Val(_, _, e) => contains_unif_exp(e),
        ElaboratedDeclaration::ValRec(vs) => vs.iter().any(|(_, _, e)| contains_unif_exp(e)),
    }
}

fn contains_unif_str(st: &crate::elaborated::LocatedStructure) -> bool {
    use crate::elaborated::Structure;
    match &st.node {
        Structure::Const(decls) => decls.iter().any(contains_unif_decl),
        Structure::Fun(_, _, _, _, body) => contains_unif_str(body),
        Structure::App(s1, s2) => contains_unif_str(s1) || contains_unif_str(s2),
        _ => false,
    }
}
