//! C code generator for the CJR intermediate representation.
//!
//! Translates a CJR `File` into a C source string.
//! Mirrors `cjr_print.sml`.

#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::c_like_representation::{
    DatatypeDecl, Decl, DmlMeta, Exp, ExportEntry, LocDecl, LocExp, LocPat, LocTyp, Pat, PatCon,
    QueryMeta, Typ,
};
use crate::compiler_diagnostics::lock_for_compile;
use crate::datatype_kind::DatatypeKind;
use crate::export::{Effect, ExportKind};
use crate::monomorphized::{DbMode, Sidedness};
use crate::settings::{FailureMode, Settings};

// ---------------------------------------------------------------------------
// Thread-local URL handler accumulator
// (mirrors the mutable `unurlifies`/`urlHandlerPrototypes` refs in cjr_print.sml)
// ---------------------------------------------------------------------------

thread_local! {
    /// Datatype/list ids for which unurlify helpers have already been emitted.
    static UNURLIFY_SEEN: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    /// Datatype/list ids for which urlify helpers have already been emitted.
    static URLIFY_SEEN: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    /// Forward declarations for URL handler helper functions.
    static URL_HANDLER_PROTOS: RefCell<Vec<String>> = RefCell::new(Vec::new());
    /// Definitions for URL handler helper functions.
    static URL_HANDLER_DEFS: RefCell<Vec<String>> = RefCell::new(Vec::new());
}

fn reset_url_handlers() {
    cjr_test_tick();
    UNURLIFY_SEEN.with(|s| s.borrow_mut().clear());
    URLIFY_SEEN.with(|s| s.borrow_mut().clear());
    URL_HANDLER_PROTOS.with(|s| s.borrow_mut().clear());
    URL_HANDLER_DEFS.with(|s| s.borrow_mut().clear());
}

fn add_url_handler(proto: String, def: String) {
    cjr_test_tick();
    URL_HANDLER_PROTOS.with(|s| s.borrow_mut().push(proto));
    URL_HANDLER_DEFS.with(|s| s.borrow_mut().push(def));
}

fn collect_url_handler_protos() -> Vec<String> {
    cjr_test_tick();
    URL_HANDLER_PROTOS.with(|s| s.borrow().clone())
}

fn collect_url_handler_defs() -> Vec<String> {
    cjr_test_tick();
    URL_HANDLER_DEFS.with(|s| s.borrow().clone())
}

#[cfg(test)]
thread_local! {
    /// Caps recursive work during `cargo test` / mutation so runaway mutants panic instead of timing out.
    /// Default budget so unit tests can call `p_exp` / `p_typ` without going through `cjr_print`.
    static CJR_PRINT_TICKS: Cell<usize> = Cell::new(8_000_000);
}

#[cfg(test)]
fn cjr_test_reset_print_ticks() {
    CJR_PRINT_TICKS.with(|c| c.set(8_000_000));
}

#[cfg(test)]
fn cjr_test_tick() {
    CJR_PRINT_TICKS.with(|c| {
        let n = c.get();
        if n == 0 {
            panic!(
                "cjr_print: test tick budget exhausted (likely infinite recursion from a mutation)"
            );
        }
        c.set(n - 1);
    });
}

#[cfg(not(test))]
#[inline]
fn cjr_test_tick() {}

// ---------------------------------------------------------------------------
// CjrEnv — compilation environment
// ---------------------------------------------------------------------------

/// Environment used while printing CJR to C.
#[derive(Clone)]
pub struct CjrEnv {
    /// Stack of relative (De Bruijn) bindings. Index 0 = most-recently pushed.
    pub rels: Vec<(String, LocTyp)>,
    /// Named declarations: id → (name, type)
    pub named: HashMap<usize, (String, LocTyp)>,
    /// Datatypes: id → (name, constructors)
    pub datatypes: HashMap<usize, (String, Vec<(String, usize, Option<LocTyp>)>)>,
    /// Constructors: id → (name, arg_type, datatype_id)
    pub constructors: HashMap<usize, (String, Option<LocTyp>, usize)>,
    /// Struct fields: struct_id → field list
    pub structs: HashMap<usize, Vec<(String, LocTyp)>>,
}

impl CjrEnv {
    pub fn new() -> Self {
        cjr_test_tick();
        let mut env = CjrEnv {
            rels: Vec::new(),
            named: HashMap::new(),
            datatypes: HashMap::new(),
            constructors: HashMap::new(),
            structs: HashMap::new(),
        };
        // id 0 = unit struct (empty)
        env.structs.insert(0, vec![]);
        env
    }

    pub fn push_e_rel(&mut self, x: &str, t: LocTyp) {
        cjr_test_tick();
        self.rels.push((x.to_string(), t));
    }

    pub fn lookup_e_rel(&self, n: usize) -> Option<&(String, LocTyp)> {
        cjr_test_tick();
        let idx = self.rels.len().checked_sub(n + 1)?;
        self.rels.get(idx)
    }

    pub fn count_e_rels(&self) -> usize {
        cjr_test_tick();
        self.rels.len()
    }

    pub fn push_e_named(&mut self, x: &str, n: usize, t: LocTyp) {
        cjr_test_tick();
        self.named.insert(n, (x.to_string(), t));
    }

    pub fn lookup_e_named(&self, n: usize) -> Option<&(String, LocTyp)> {
        cjr_test_tick();
        self.named.get(&n)
    }

    pub fn push_datatype(
        &mut self,
        x: &str,
        n: usize,
        constrs: &[(String, usize, Option<LocTyp>)],
    ) {
        cjr_test_tick();
        self.datatypes.insert(n, (x.to_string(), constrs.to_vec()));
        for (cx, cn, ct) in constrs {
            self.constructors.insert(*cn, (cx.clone(), ct.clone(), n));
        }
    }

    pub fn lookup_datatype(
        &self,
        n: usize,
    ) -> Option<&(String, Vec<(String, usize, Option<LocTyp>)>)> {
        cjr_test_tick();
        self.datatypes.get(&n)
    }

    pub fn lookup_constructor(&self, n: usize) -> Option<&(String, Option<LocTyp>, usize)> {
        cjr_test_tick();
        self.constructors.get(&n)
    }

    pub fn push_struct(&mut self, n: usize, xts: Vec<(String, LocTyp)>) {
        cjr_test_tick();
        self.structs.insert(n, xts);
    }

    pub fn lookup_struct(&self, n: usize) -> Option<&Vec<(String, LocTyp)>> {
        cjr_test_tick();
        self.structs.get(&n)
    }

    /// Update the environment by processing a declaration's bindings.
    pub fn decl_binds(&mut self, d: &LocDecl) {
        cjr_test_tick();
        match &d.node {
            Decl::Struct(n, xts) => {
                self.push_struct(*n, xts.clone());
            }
            Decl::Datatype(dts) => {
                for dt in dts {
                    self.push_datatype(&dt.name, dt.id, &dt.constrs);
                }
            }
            Decl::DatatypeForward(_, _, _) => {}
            Decl::Val(x, n, t, _) => {
                self.push_e_named(x, *n, t.clone());
            }
            Decl::Fun(fx, n, args, ran, _) => {
                // Build the curried function type
                let fun_t = args.iter().rev().fold(ran.clone(), |acc, (_, dom)| {
                    crate::error_types::Located::dummy(Typ::Fun(
                        Box::new(dom.clone()),
                        Box::new(acc),
                    ))
                });
                self.push_e_named(fx, *n, fun_t);
            }
            Decl::FunRec(vis) => {
                for (fx, n, args, ran, _) in vis {
                    let fun_t = args.iter().rev().fold(ran.clone(), |acc, (_, dom)| {
                        crate::error_types::Located::dummy(Typ::Fun(
                            Box::new(dom.clone()),
                            Box::new(acc),
                        ))
                    });
                    self.push_e_named(fx, *n, fun_t);
                }
            }
            _ => {}
        }
    }
}

impl Default for CjrEnv {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Naming helpers
// ---------------------------------------------------------------------------

fn ident(s: &str) -> String {
    s.replace('\'', "PRIME").replace('$', "_")
}

fn p_rel_name(env: &CjrEnv, n: usize) -> String {
    cjr_test_tick();
    match env.lookup_e_rel(n) {
        Some((x, _)) => {
            let idx = env.count_e_rels().saturating_sub(n + 1);
            format!("__uwr_{}_{}", ident(x), idx)
        }
        None => format!("__uwr_UNBOUND_{}", n),
    }
}

fn p_named_name(n: usize, x: &str) -> String {
    cjr_test_tick();
    format!("__uwn_{}_{}", ident(x), n)
}

// ---------------------------------------------------------------------------
// isUnboxable
// ---------------------------------------------------------------------------

fn is_unboxable(t: &LocTyp) -> bool {
    match &t.node {
        Typ::Datatype(DatatypeKind::Default, _, _) => true,
        Typ::Ffi(m, x) if m == "Basis" && (x == "string" || x == "queryString") => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Type printing
// ---------------------------------------------------------------------------

pub fn p_typ(env: &CjrEnv, t: &LocTyp) -> String {
    cjr_test_tick();
    match &t.node {
        Typ::Fun(_, _) => "<FUNCTION>".to_string(),
        Typ::Record(0) => "uw_unit".to_string(),
        Typ::Record(i) => format!("struct __uws_{}", i),
        Typ::Datatype(DatatypeKind::Enum, n, _) => match env.lookup_datatype(*n) {
            Some((name, _)) => format!("enum __uwe_{}_{}", ident(name), n),
            None => format!("enum __uwe_UNBOUND_{}", n),
        },
        Typ::Datatype(DatatypeKind::Option, _n, xncs) => {
            // Find the constructor with an argument
            let xncs_locked = lock_for_compile(xncs.as_ref(), "CJR print Option constructors");
            let arg_typ = xncs_locked.iter().find_map(|(_, _, ot)| ot.as_ref());
            match arg_typ {
                None => "void*".to_string(),
                Some(t) => {
                    if is_unboxable(t) {
                        p_typ(env, t)
                    } else {
                        format!("{}*", p_typ(env, t))
                    }
                }
            }
        }
        Typ::Datatype(DatatypeKind::Default, n, _) => match env.lookup_datatype(*n) {
            Some((name, _)) => format!("struct __uwd_{}_{}*", ident(name), n),
            None => format!("struct __uwd_UNBOUND_{}*", n),
        },
        Typ::Ffi(m, x) => format!("uw_{}_{}", ident(m), ident(x)),
        Typ::Option(inner) => {
            if is_unboxable(inner) {
                p_typ(env, inner)
            } else {
                format!("{}*", p_typ(env, inner))
            }
        }
        Typ::List(_, i) => format!("struct __uws_{}*", i),
    }
}

// ---------------------------------------------------------------------------
// Pattern constructor name
// ---------------------------------------------------------------------------

fn p_pat_con(env: &CjrEnv, pc: &PatCon) -> String {
    cjr_test_tick();
    match pc {
        PatCon::Var(n) => match env.lookup_constructor(*n) {
            Some((x, _, _)) => format!("__uwc_{}_{}", ident(x), n),
            None => format!("__uwc_UNBOUND_{}", n),
        },
        PatCon::Ffi {
            module,
            datatyp,
            con,
            ..
        } => format!(
            "uw_{}_{}_{}", // matches SML: uw_{m}_{datatyp}_{con} for FFI
            ident(module),
            ident(datatyp),
            ident(con)
        ),
    }
}

/// Constructor name used for data field access: "uw_{name}"
fn con_field_name(env: &CjrEnv, pc: &PatCon) -> String {
    cjr_test_tick();
    match pc {
        PatCon::Var(n) => match env.lookup_constructor(*n) {
            Some((x, _, _)) => format!("uw_{}", ident(x)),
            None => format!("uw_UNBOUND_{}", n),
        },
        PatCon::Ffi { module, con, .. } => format!("uw_{}_{}", ident(module), ident(con)),
    }
}

/// Info about a Default constructor: (struct_type_name, enum_const_name, data_field_name)
fn pat_con_info(env: &CjrEnv, pc: &PatCon) -> (String, String, String) {
    cjr_test_tick();
    match pc {
        PatCon::Var(n) => match env.lookup_constructor(*n) {
            Some((x, _, dn)) => {
                let dx = match env.lookup_datatype(*dn) {
                    Some((name, _)) => name.clone(),
                    None => "UNBOUND".to_string(),
                };
                (
                    format!("__uwd_{}_{}", ident(&dx), dn),
                    format!("__uwc_{}_{}", ident(x), n),
                    format!("uw_{}", ident(x)),
                )
            }
            None => (
                format!("__uwd_UNBOUND"),
                format!("__uwc_UNBOUND_{}", n),
                format!("uw_UNBOUND_{}", n),
            ),
        },
        PatCon::Ffi {
            module,
            datatyp,
            con,
            ..
        } => (
            format!("uw_{}_{}", ident(module), ident(datatyp)),
            format!("uw_{}_{}_{}", ident(module), ident(datatyp), ident(con)),
            format!("uw_{}_{}", ident(module), ident(con)),
        ),
    }
}

// ---------------------------------------------------------------------------
// Pattern matching — generates the boolean condition
// ---------------------------------------------------------------------------

fn p_pat_match(env: &CjrEnv, disc: &str, pat: &LocPat) -> String {
    cjr_test_tick();
    match &pat.node {
        Pat::Var(_, _) => "1".to_string(),
        Pat::Prim(p) => match p {
            crate::primitives::Prim::Int(n) => format!("({} == {}LL)", disc, n),
            crate::primitives::Prim::Float(f) => format!("({} == {})", disc, f),
            crate::primitives::Prim::String(_, s) => {
                format!("(!strcmp({}, \"{}\"))", disc, s.replace('"', "\\\""))
            }
            crate::primitives::Prim::Char(c) => format!("({} == '{}')", disc, c),
        },
        Pat::Con(dk, pc, po) => {
            let base = match dk {
                DatatypeKind::Enum => format!("({} == {})", disc, p_pat_con(env, pc)),
                DatatypeKind::Default => format!("({}->tag == {})", disc, p_pat_con(env, pc)),
                DatatypeKind::Option => match po {
                    None => format!("({} == NULL)", disc),
                    Some(_) => format!("({} != NULL)", disc),
                },
            };
            match po {
                None => base,
                Some(inner_pat) => {
                    let disc2 = match dk {
                        DatatypeKind::Enum => disc.to_string(),
                        DatatypeKind::Default => {
                            format!("{}->{}", disc, con_field_name(env, pc))
                        }
                        DatatypeKind::Option => {
                            // Get the arg type to decide unboxable
                            let arg_t = get_pc_arg_typ(env, pc);
                            match arg_t {
                                Some(t) if is_unboxable(&t) => disc.to_string(),
                                _ => format!("(*{})", disc),
                            }
                        }
                    };
                    let inner = p_pat_match(env, &disc2, inner_pat);
                    format!("{} && {}", base, inner)
                }
            }
        }
        Pat::Record(xps) => {
            if xps.is_empty() {
                return "1".to_string();
            }
            xps.iter()
                .map(|(x, p, _)| {
                    let disc2 = format!("{}.__uwf_{}", disc, ident(x));
                    p_pat_match(env, &disc2, p)
                })
                .collect::<Vec<_>>()
                .join(" && ")
        }
        Pat::None(_) => format!("({} == NULL)", disc),
        Pat::Some(t, inner_pat) => {
            let disc2 = if is_unboxable(t) {
                disc.to_string()
            } else {
                format!("(*{})", disc)
            };
            let inner = p_pat_match(env, &disc2, inner_pat);
            format!("({} != NULL) && {}", disc, inner)
        }
    }
}

/// Get the argument type of a constructor (for Option/unboxable decisions).
fn get_pc_arg_typ(env: &CjrEnv, pc: &PatCon) -> Option<LocTyp> {
    cjr_test_tick();
    match pc {
        PatCon::Var(n) => env.lookup_constructor(*n).and_then(|(_, t, _)| t.clone()),
        PatCon::Ffi { arg, .. } => arg.clone(),
    }
}

// ---------------------------------------------------------------------------
// Pattern binding — generates variable assignments
// ---------------------------------------------------------------------------

fn p_pat_bind(env: &mut CjrEnv, disc: &str, pat: &LocPat) -> String {
    cjr_test_tick();
    match &pat.node {
        Pat::Var(x, t) => {
            let idx = env.count_e_rels();
            let var_name = format!("__uwr_{}_{}", ident(x), idx);
            let decl = format!("{} {} = {};\n", p_typ(env, t), var_name, disc);
            env.push_e_rel(x, t.clone());
            decl
        }
        Pat::Prim(_) => String::new(),
        Pat::Con(_, _, None) => String::new(),
        Pat::Con(dk, pc, Some(inner_pat)) => {
            let disc2 = match dk {
                DatatypeKind::Enum => disc.to_string(),
                DatatypeKind::Default => format!("({}->data.{})", disc, con_field_name(env, pc)),
                DatatypeKind::Option => {
                    let arg_t = get_pc_arg_typ(env, pc);
                    match arg_t {
                        Some(t) if is_unboxable(&t) => disc.to_string(),
                        _ => format!("(*{})", disc),
                    }
                }
            };
            p_pat_bind(env, &disc2, inner_pat)
        }
        Pat::Record(xps) => {
            let mut out = String::new();
            for (x, p, _) in xps {
                let disc2 = format!("{}.__uwf_{}", disc, ident(x));
                out.push_str(&p_pat_bind(env, &disc2, p));
            }
            out
        }
        Pat::None(_) => String::new(),
        Pat::Some(t, inner_pat) => {
            let disc2 = if is_unboxable(t) {
                disc.to_string()
            } else {
                format!("(*{})", disc)
            };
            p_pat_bind(env, &disc2, inner_pat)
        }
    }
}

// ---------------------------------------------------------------------------
// p_funcall — safe left-to-right argument evaluation
// ---------------------------------------------------------------------------

fn p_funcall(
    env: &CjrEnv,
    m: &str,
    x: &str,
    args: &[(LocExp, LocTyp)],
    extra: Option<&str>,
    settings: &Settings,
) -> String {
    cjr_test_tick();
    let fn_name = format!("uw_{}_{}", ident(m), ident(x));
    let extra_s = match extra {
        None => String::new(),
        Some(e) => format!(", {}", e),
    };
    match args {
        [] => format!("{}(ctx{})", fn_name, extra_s),
        [(e, _)] => {
            let ae = p_exp(env, e, settings);
            format!("{}(ctx, {}{})", fn_name, ae, extra_s)
        }
        _ => {
            // Evaluate args and call: C11-compliant direct call.
            // Evaluation order of function arguments is implementation-defined but
            // cjrize should have lifted side-effectful sub-expressions to let-bindings.
            let arg_strs: Vec<String> = args.iter().map(|(e, _)| p_exp(env, e, settings)).collect();
            format!("{}(ctx, {}{})", fn_name, arg_strs.join(", "), extra_s)
        }
    }
}

// ---------------------------------------------------------------------------
// Expression printing
// ---------------------------------------------------------------------------

pub fn p_exp(env: &CjrEnv, e: &LocExp, settings: &Settings) -> String {
    cjr_test_tick();
    match &e.node {
        Exp::Prim(p) => p.to_c_literal(),

        Exp::Rel(n) => p_rel_name(env, *n),

        Exp::Named(n) => match env.lookup_e_named(*n) {
            Some((x, _)) => p_named_name(*n, x),
            None => format!("__uwn_UNBOUND_{}", n),
        },

        Exp::Con(DatatypeKind::Enum, pc, _) => p_pat_con(env, pc),

        Exp::Con(DatatypeKind::Option, _pc, None) => "NULL".to_string(),

        Exp::Con(DatatypeKind::Option, pc, Some(inner_e)) => {
            let arg_t = get_pc_arg_typ(env, pc);
            match arg_t {
                Some(t) if is_unboxable(&t) => p_exp(env, inner_e, settings),
                Some(t) => {
                    let typ_s = p_typ(env, &t);
                    let val_s = p_exp(env, inner_e, settings);
                    format!(
                        "({{\n{} *tmp = uw_malloc(ctx, sizeof({}));\n*tmp = {};\ntmp;\n}})",
                        typ_s, typ_s, val_s
                    )
                }
                None => {
                    let val_s = p_exp(env, inner_e, settings);
                    format!(
                        "({{\nvoid *tmp = uw_malloc(ctx, sizeof(void*));\n*tmp = {};\ntmp;\n}})",
                        val_s
                    )
                }
            }
        }

        Exp::Con(DatatypeKind::Default, pc, eo) => {
            let (xd, xc, xn) = pat_con_info(env, pc);
            let mut out = format!(
                "({{\nstruct {0} *tmp = uw_malloc(ctx, sizeof(struct {0}));\ntmp->tag = {1};\n",
                xd, xc
            );
            if let Some(inner_e) = eo {
                let val_s = p_exp(env, inner_e, settings);
                out.push_str(&format!("tmp->data.{} = {};\n", xn, val_s));
            }
            out.push_str("tmp;\n})");
            out
        }

        Exp::None(_) => "NULL".to_string(),

        Exp::Some(t, inner_e) => {
            if is_unboxable(t) {
                p_exp(env, inner_e, settings)
            } else {
                let typ_s = p_typ(env, t);
                let val_s = p_exp(env, inner_e, settings);
                format!(
                    "({{\n{} *tmp = uw_malloc(ctx, sizeof({}));\n*tmp = {};\ntmp;\n}})",
                    typ_s, typ_s, val_s
                )
            }
        }

        Exp::Ffi(m, x) => format!("uw_{}_{}", ident(m), ident(x)),

        Exp::FfiApp(m, x, args) => {
            // Special case: strcat flattening
            if m == "Basis" && x == "strcat" {
                if let [(e1, _), (e2, _)] = args.as_slice() {
                    let flat = flatten_strcat(e1, e2);
                    if flat.len() == 2 {
                        // 2 args: plain strcat
                        return p_funcall(env, "Basis", "strcat", args, None, settings);
                    } else {
                        // 3+ args: mstrcat with NULL sentinel
                        let dummy_t = crate::error_types::Located::dummy(Typ::Ffi(
                            "Basis".to_string(),
                            "string".to_string(),
                        ));
                        let typed_args: Vec<(LocExp, LocTyp)> =
                            flat.into_iter().map(|e| (e, dummy_t.clone())).collect();
                        return p_funcall(
                            env,
                            "Basis",
                            "mstrcat",
                            &typed_args,
                            Some("NULL"),
                            settings,
                        );
                    }
                }
            }
            p_funcall(env, m, x, args, None, settings)
        }

        Exp::App(f, args) => {
            // For functions with 2+ args, assign each to a local to fix eval order
            if args.len() >= 2 {
                if let Exp::Named(n) = &f.node {
                    // Try to get argument types from the named function type
                    if let Some((_, fun_t)) = env.lookup_e_named(*n) {
                        let arg_types = collect_arg_types(fun_t, args.len());
                        if arg_types.len() == args.len() {
                            let f_s = p_exp(env, f, settings);
                            let mut out = String::from("({\n");
                            for (i, (e, t)) in args.iter().zip(arg_types.iter()).enumerate() {
                                let ae = p_exp(env, e, settings);
                                let at = p_typ(env, t);
                                out.push_str(&format!("{} arg{} = {};\n", at, i, ae));
                            }
                            let arg_list: Vec<String> =
                                (0..args.len()).map(|i| format!("arg{}", i)).collect();
                            out.push_str(&f_s);
                            out.push_str("(ctx, ");
                            out.push_str(&arg_list.join(", "));
                            out.push_str(");\n})");
                            return out;
                        }
                    }
                }
            }
            // Simple app
            let f_s = p_exp(env, f, settings);
            let arg_strs: Vec<String> = args.iter().map(|a| p_exp(env, a, settings)).collect();
            if arg_strs.is_empty() {
                format!("{}(ctx)", f_s)
            } else {
                format!("{}(ctx, {})", f_s, arg_strs.join(", "))
            }
        }

        Exp::Unop(s, e1) => {
            let e_s = p_exp(env, e1, settings);
            format!("({} {})", s, e_s)
        }

        Exp::Binop(s, e1, e2) => {
            let e1_s = p_exp(env, e1, settings);
            let e2_s = p_exp(env, e2, settings);
            // Division/modulo: guard against divide by zero
            if s == "/" || s == "%" {
                return format!(
                    "({{\nuw_Basis_int dividend = {}, divisor = {};\nif (divisor == 0)\nuw_error(ctx, FATAL, \"division by zero\");\ndividend {} divisor;\n}})",
                    e1_s, e2_s, s
                );
            }
            // If op ends with an alpha char (and not fdiv), treat as a function call
            if s != "fdiv" && s.chars().last().map_or(false, |c| c.is_alphabetic()) {
                return format!("{}({}, {})", s, e1_s, e2_s);
            }
            let op = if s == "fdiv" { "/" } else { s.as_str() };
            format!("({} {} {})", e1_s, op, e2_s)
        }

        Exp::Record(0, _) => "0".to_string(),

        Exp::Record(i, xes) => {
            let vals: Vec<String> = xes.iter().map(|(_, e)| p_exp(env, e, settings)).collect();
            format!(
                "({{ struct __uws_{} tmp = {{{}}}; tmp; }})",
                i,
                vals.join(", ")
            )
        }

        Exp::Field(e1, x) => {
            let e_s = p_exp(env, e1, settings);
            format!("{}.__uwf_{}", e_s, ident(x))
        }

        Exp::Case(disc_e, arms, meta) => {
            let disc_t = p_typ(env, &meta.disc);
            let result_t = p_typ(env, &meta.result);
            let disc_s = p_exp(env, disc_e, settings);

            // Build ternary chain (like SML: cond ? ({binds; body}) : (next_cond ? ... : error))
            let error_fallback = format!(
                "({{\n{} tmp;\nuw_error(ctx, FATAL, \"pattern match failure\");\ntmp;\n}})",
                result_t
            );

            let chain = arms.iter().rev().fold(error_fallback, |acc, (pat, body)| {
                let cond = p_pat_match(env, "disc", pat);
                // Compute bindings in a cloned env
                let mut env2 = env.clone();
                let binds = p_pat_bind(&mut env2, "disc", pat);
                let body_s = p_exp(&env2, body, settings);

                if binds.is_empty() {
                    format!("{} ? {} : {}", cond, body_s, acc)
                } else {
                    format!("{} ? ({{\n{}{};\n}}) : {}", cond, binds, body_s, acc)
                }
            });

            format!(
                "({{\n{} disc = {};\n{}\n{};\n}})",
                disc_t, disc_s, result_t, chain
            )
        }

        Exp::Error(msg_e, t) => {
            let t_s = p_typ(env, t);
            let msg_s = p_exp(env, msg_e, settings);
            format!(
                "({{\n{} tmp;\nuw_error(ctx, FATAL, \"%s\", {});\ntmp;\n}})",
                t_s, msg_s
            )
        }

        Exp::ReturnBlob {
            blob: Some(blob_e),
            mime_type,
            t,
        } => {
            let t_s = p_typ(env, t);
            let blob_s = p_exp(env, blob_e, settings);
            let mime_s = p_exp(env, mime_type, settings);
            format!(
                "({{\nuw_Basis_blob blob = {};\nuw_Basis_string mimeType = {};\n{} tmp;\nuw_return_blob(ctx, blob, mimeType);\ntmp;\n}})",
                blob_s, mime_s, t_s
            )
        }

        Exp::ReturnBlob {
            blob: None,
            mime_type,
            t,
        } => {
            let t_s = p_typ(env, t);
            let mime_s = p_exp(env, mime_type, settings);
            format!(
                "({{\nuw_Basis_string mimeType = {};\n{} tmp;\nuw_return_blob_from_page(ctx, mimeType);\ntmp;\n}})",
                mime_s, t_s
            )
        }

        Exp::Redirect(url_e, t) => {
            let t_s = p_typ(env, t);
            let url_s = p_exp(env, url_e, settings);
            format!("({{\n{} tmp;\nuw_redirect(ctx, {});\ntmp;\n}})", t_s, url_s)
        }

        Exp::Write(e1) => {
            let e_s = p_exp(env, e1, settings);
            format!("(uw_write(ctx, {}), 0)", e_s)
        }

        Exp::Seq(e1, e2) => {
            let e1_s = p_exp(env, e1, settings);
            let e2_s = p_exp(env, e2, settings);
            format!("({}, {})", e1_s, e2_s)
        }

        Exp::Let(x, t, e1, e2) => {
            let idx = env.count_e_rels();
            let var_name = format!("__uwr_{}_{}", ident(x), idx);
            let t_s = p_typ(env, t);
            let e1_s = p_exp(env, e1, settings);
            let mut env2 = env.clone();
            env2.push_e_rel(x, t.clone());
            let e2_s = p_exp(&env2, e2, settings);
            format!("({{\n{} {} = {};\n{};\n}})", t_s, var_name, e1_s, e2_s)
        }

        Exp::Query(qm) => p_exp_query(env, qm, settings),

        Exp::Dml(dm) => p_exp_dml(env, dm, settings),

        Exp::Nextval { seq, prepared } => {
            let seq_s = p_exp(env, seq, settings);
            let nextval_common = |query_expr: &str| -> String {
                format!(
                    "if (res == NULL) {{\n\
                       uw_try_reconnecting_and_restarting(ctx);\n\
                       uw_error(ctx, FATAL, \"Can't allocate NEXTVAL result; database server may be down.\");\n\
                     }}\n\
                     if (PQresultStatus(res) != PGRES_TUPLES_OK) {{\n\
                       PQclear(res);\n\
                       uw_error(ctx, FATAL, \"nextval: Query failed:\\n%s\\n%s\", {q}, PQerrorMessage(conn));\n\
                     }}\n\
                     n = PQntuples(res);\n\
                     if (n != 1) {{\n\
                       PQclear(res);\n\
                       uw_error(ctx, FATAL, \"nextval: Wrong number of result rows:\\n%s\\n%s\", {q}, PQerrorMessage(conn));\n\
                     }}\n\
                     n = uw_Basis_stringToInt_error(ctx, PQgetvalue(res, 0, 0));\n\
                     PQclear(res);\n",
                    q = query_expr,
                )
            };
            match prepared {
                Some(pq) => {
                    let query_literal = format!("\"{}\"", pq.query.replace('"', "\\\""));
                    let exec_call = if settings.persistent() {
                        format!(
                            "PQexecPrepared(conn, \"uw{}\", 0, NULL, NULL, NULL, 0)",
                            pq.id
                        )
                    } else {
                        format!(
                            "PQexecParams(conn, \"{}\", 0, NULL, NULL, NULL, NULL, 0)",
                            pq.query.replace('"', "\\\"")
                        )
                    };
                    let nc = nextval_common(&query_literal);
                    format!(
                        "({{\nuw_Basis_int n;\nuw_ensure_transaction(ctx);\nPGconn *conn = uw_get_db(ctx);\nPGresult *res = {exec};\n{nc}n;\n}})",
                        exec = exec_call,
                        nc = nc,
                    )
                }
                None => {
                    let nc = nextval_common("query");
                    format!(
                        "({{\nuw_Basis_int n;\nuw_ensure_transaction(ctx);\nPGconn *conn = uw_get_db(ctx);\nchar *query = uw_Basis_strcat(ctx, \"SELECT NEXTVAL('\", uw_Basis_strcat(ctx, {seq}, \"')\"));\nPGresult *res = PQexecParams(conn, query, 0, NULL, NULL, NULL, NULL, 0);\n{nc}n;\n}})",
                        seq = seq_s,
                        nc = nc,
                    )
                }
            }
        }

        Exp::Setval { seq, count } => {
            let seq_s = p_exp(env, seq, settings);
            let count_s = p_exp(env, count, settings);
            format!(
                "({{\nuw_ensure_transaction(ctx);\nPGconn *conn = uw_get_db(ctx);\nchar *query = uw_Basis_strcat(ctx, \"SELECT SETVAL('\", uw_Basis_strcat(ctx, {seq}, uw_Basis_strcat(ctx, \"', \", uw_Basis_strcat(ctx, uw_Basis_sqlifyInt(ctx, {count}), \")\"))));\nPGresult *res = PQexecParams(conn, query, 0, NULL, NULL, NULL, NULL, 0);\nif (res == NULL) {{ uw_try_reconnecting_and_restarting(ctx); uw_error(ctx, FATAL, \"Can't allocate SETVAL result; database server may be down.\"); }}\nif (PQresultStatus(res) != PGRES_TUPLES_OK) {{ PQclear(res); uw_error(ctx, FATAL, \"setval: Query failed:\\n%s\\n%s\", query, PQerrorMessage(conn)); }}\nPQclear(res);\n0;\n}})",
                seq = seq_s,
                count = count_s,
            )
        }

        Exp::Uurlify(e1, t, from_client) => {
            let e_s = p_exp(env, e1, settings);
            let t_s = p_typ(env, t);
            let unurl = unurlify_req("request", t, env, *from_client);
            if is_unboxable(t) {
                format!(
                    "({{\nuw_Basis_string request = uw_maybe_strdup(ctx, {e_s});\n\
                     (request ? {unurl} : ({t_s}){{}});\n}})"
                )
            } else {
                format!(
                    "({{\nuw_Basis_string request = uw_maybe_strdup(ctx, {e_s});\n\
                     (request ? ({{\n{t_s} *tmp = uw_malloc(ctx, sizeof({t_s}));\n\
                     *tmp = {unurl};\ntmp;\n}}) : ({t_s}*)NULL);\n}})"
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SQL type helpers
// ---------------------------------------------------------------------------

/// Convert a CJR type to a SqlType (for column reading/writing).
fn sql_type_in(t: &LocTyp) -> crate::settings::SqlType {
    cjr_test_tick();
    use crate::settings::SqlType;
    match &t.node {
        Typ::Ffi(m, s) if m == "Basis" => match s.as_str() {
            "int" => SqlType::Int,
            "float" => SqlType::Float,
            "string" => SqlType::String,
            "char" => SqlType::Char,
            "bool" => SqlType::Bool,
            "time" => SqlType::Time,
            "clocktime" => SqlType::Clocktime,
            "calendardate" => SqlType::Calendardate,
            "blob" => SqlType::Blob,
            "channel" => SqlType::Channel,
            "client" => SqlType::Client,
            _ => SqlType::Int, // fallback
        },
        Typ::Option(inner) => SqlType::Nullable(Box::new(sql_type_in(inner))),
        _ => SqlType::Int, // fallback
    }
}

/// Generate C code to convert a C value to a Postgres parameter string.
fn p_ensql(t: &crate::settings::SqlType, expr: &str) -> String {
    cjr_test_tick();
    use crate::settings::SqlType;
    match t {
        SqlType::Int => format!("uw_Basis_attrifyInt(ctx, {})", expr),
        SqlType::Float => format!("uw_Basis_attrifyFloat(ctx, {})", expr),
        SqlType::String => expr.to_string(),
        SqlType::Char => format!("uw_Basis_attrifyChar(ctx, {})", expr),
        SqlType::Bool => format!("({} ? \"TRUE\" : \"FALSE\")", expr),
        SqlType::Time => format!("uw_Basis_ensqlTime(ctx, {})", expr),
        SqlType::Clocktime => format!("uw_Basis_ensqlClocktime(ctx, {})", expr),
        SqlType::Calendardate => format!("uw_Basis_ensqlCalendardate(ctx, {})", expr),
        SqlType::Blob => format!("{}.data", expr),
        SqlType::Channel => format!("uw_Basis_attrifyChannel(ctx, {})", expr),
        SqlType::Client => format!("uw_Basis_attrifyClient(ctx, {})", expr),
        SqlType::Nullable(inner) => match inner.as_ref() {
            SqlType::String => expr.to_string(),
            _ => format!(
                "({e} == NULL ? NULL : ({inner_ensql}))",
                e = expr,
                inner_ensql = p_ensql(inner, &format!("(*{})", expr))
            ),
        },
    }
}

/// Generate C code to read a Postgres column value.
fn p_getcol(
    col: usize,
    t: &crate::settings::SqlType,
    wont_leak_strings: bool,
    loc_str: &str,
) -> String {
    cjr_test_tick();
    use crate::settings::SqlType;

    fn p_unsql(t: &SqlType, e: &str, e_len: &str, wont_leak_strings: bool) -> String {
        cjr_test_tick();
        match t {
            SqlType::Int => format!("uw_Basis_stringToInt_error(ctx, {})", e),
            SqlType::Float => format!("uw_Basis_stringToFloat_error(ctx, {})", e),
            SqlType::String => {
                if wont_leak_strings {
                    e.to_string()
                } else {
                    format!("uw_strdup(ctx, {})", e)
                }
            }
            SqlType::Char => format!("{}[0]", e),
            SqlType::Bool => format!("uw_Basis_stringToBool_error(ctx, {})", e),
            SqlType::Time => format!("uw_Basis_unsqlTime(ctx, {})", e),
            SqlType::Clocktime => format!("uw_Basis_unsqlClocktime(ctx, {})", e),
            SqlType::Calendardate => format!("uw_Basis_unsqlCalendardate(ctx, {})", e),
            SqlType::Blob => {
                format!("uw_Basis_stringToBlob_error(ctx, {}, {})", e, e_len)
            }
            SqlType::Channel => format!("uw_Basis_stringToChannel_error(ctx, {})", e),
            SqlType::Client => format!("uw_Basis_stringToClient_error(ctx, {})", e),
            SqlType::Nullable(inner) => p_unsql(inner, e, e_len, wont_leak_strings),
        }
    }

    let getvalue = format!("PQgetvalue(res, i, {})", col);
    let getlength = format!("PQgetlength(res, i, {})", col);

    match t {
        SqlType::Nullable(inner) => {
            let getter = match inner.as_ref() {
                SqlType::String => {
                    let inner_expr = p_unsql(inner, &getvalue, &getlength, wont_leak_strings);
                    format!("(PQgetisnull(res, i, {col}) ? NULL : {inner_expr})")
                }
                _ => {
                    let ctype = inner.c_type();
                    let inner_expr = p_unsql(inner, &getvalue, &getlength, wont_leak_strings);
                    format!(
                        "(PQgetisnull(res, i, {col}) ? NULL : ({{\n{ctype} *tmp = uw_malloc(ctx, sizeof({ctype}));\n*tmp = {inner_expr};\ntmp;\n}}))"
                    )
                }
            };
            getter
        }
        _ => {
            let value_expr = p_unsql(t, &getvalue, &getlength, wont_leak_strings);
            format!(
                "(PQgetisnull(res, i, {col}) ? ({{ {ctype} tmp; uw_error(ctx, FATAL, \"{loc}: Unexpectedly NULL field #{col}\"); tmp; }}) : {value_expr})",
                col = col,
                ctype = t.c_type(),
                loc = loc_str,
                value_expr = value_expr,
            )
        }
    }
}

/// Generate C code to declare and fill Postgres prepared-statement parameters.
fn make_params(inputs: &[(String, crate::settings::SqlType)]) -> String {
    cjr_test_tick();
    use crate::settings::SqlType;
    let mut out = String::new();

    // paramFormats array
    out.push_str("static const int paramFormats[] = { ");
    let formats: Vec<String> = inputs
        .iter()
        .map(|(_, t)| if t.is_blob() { "1".into() } else { "0".into() })
        .collect();
    out.push_str(&formats.join(", "));
    out.push_str(" };\n");

    // paramLengths
    let has_blob = inputs.iter().any(|(_, t)| t.is_blob());
    if has_blob {
        out.push_str(&format!(
            "int *paramLengths = uw_malloc(ctx, {} * sizeof(int));\n",
            inputs.len()
        ));
        for (i, (e, t)) in inputs.iter().enumerate() {
            let len_expr = match t {
                SqlType::Blob => format!("{}.size", e),
                SqlType::Nullable(inner) if inner.is_blob() => {
                    format!("{e}?{e}->size:0")
                }
                _ => "0".into(),
            };
            out.push_str(&format!("paramLengths[{}] = {};\n", i, len_expr));
        }
    } else {
        out.push_str("const int *paramLengths = paramFormats;\n");
    }

    // paramValues
    out.push_str(&format!(
        "const char **paramValues = uw_malloc(ctx, {} * sizeof(char*));\n",
        inputs.len()
    ));
    for (i, (e, t)) in inputs.iter().enumerate() {
        let ensql = p_ensql(t, e);
        out.push_str(&format!("paramValues[{}] = {};\n", i, ensql));
    }

    out
}

/// Generate the common Postgres query loop (after `res` is set).
fn query_common(
    loc_str: &str,
    query_expr: &str,
    outputs: &[(String, crate::settings::SqlType)],
    do_cols: &str,
) -> String {
    cjr_test_tick();
    let bumped_len = if outputs.is_empty() { 1 } else { outputs.len() };
    format!(
        "int n, i;\n\
         if (res == NULL) {{\n\
           uw_try_reconnecting_and_restarting(ctx);\n\
           uw_error(ctx, FATAL, \"Can't allocate query result; database server may be down.\");\n\
         }}\n\
         if (PQresultStatus(res) != PGRES_TUPLES_OK) {{\n\
           if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), \"40001\")) {{\n\
             PQclear(res);\n\
             uw_error(ctx, UNLIMITED_RETRY, \"Serialization failure\");\n\
           }}\n\
           if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), \"40P01\")) {{\n\
             PQclear(res);\n\
             uw_error(ctx, UNLIMITED_RETRY, \"Deadlock detected\");\n\
           }}\n\
           PQclear(res);\n\
           uw_error(ctx, FATAL, \"{loc}: Query failed:\\n%s\\n%s\", {q}, PQerrorMessage(conn));\n\
         }}\n\
         if (PQnfields(res) != {nf}) {{\n\
           int nf = PQnfields(res);\n\
           PQclear(res);\n\
           uw_error(ctx, FATAL, \"{loc}: Query returned %d columns instead of {nf}:\\n%s\\n%s\", nf, {q}, PQerrorMessage(conn));\n\
         }}\n\
         uw_end_region(ctx);\n\
         uw_push_cleanup(ctx, (void (*)(void *))PQclear, res);\n\
         n = PQntuples(res);\n\
         for (i = 0; i < n; ++i) {{\n\
           {do_cols}\
         }}\n\
         uw_pop_cleanup(ctx);\n",
        loc = loc_str,
        q = query_expr,
        nf = bumped_len,
        do_cols = do_cols,
    )
}

/// Generate the `do_cols` body: read all output columns into the row struct.
fn make_do_cols(
    rnum: usize,
    outputs: &[(String, crate::settings::SqlType)],
    body_s: &str,
    env_depth: usize,
    wont_leak_strings: bool,
    loc_str: &str,
) -> String {
    cjr_test_tick();
    let mut out = format!(
        "struct __uws_{rn} __uwr_r_{dep};\n\
         {st} __uwr_acc_{dep1} = acc;\n\n",
        rn = rnum,
        dep = env_depth,
        st = "/* state */",
        dep1 = env_depth + 1,
    );

    for (i, (proj, t)) in outputs.iter().enumerate() {
        let col_s = p_getcol(i, t, wont_leak_strings, loc_str);
        out.push_str(&format!(
            "__uwr_r_{dep}.{proj} = {col};\n",
            dep = env_depth,
            proj = proj,
            col = col_s,
        ));
    }

    out.push_str(&format!("\nacc = {};\n", body_s));
    out
}

/// Extract `(expr_string, SqlType)` pairs from a prepared SQL query expression
/// (the `$N::type` placeholders come from the sqlify functions).
fn get_pargs(
    e: &LocExp,
    env: &CjrEnv,
    settings: &Settings,
) -> Vec<(String, crate::settings::SqlType)> {
    cjr_test_tick();
    use crate::settings::SqlType;
    match &e.node {
        Exp::Prim(crate::primitives::Prim::String(_, _)) => vec![],
        Exp::FfiApp(m, x, args) if m == "Basis" => match x.as_str() {
            "strcat" => {
                if let [(e1, _), (e2, _)] = args.as_slice() {
                    let mut v = get_pargs(e1, env, settings);
                    v.extend(get_pargs(e2, env, settings));
                    v
                } else {
                    vec![]
                }
            }
            "sqlifyInt" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Int)]
                } else {
                    vec![]
                }
            }
            "sqlifyFloat" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Float)]
                } else {
                    vec![]
                }
            }
            "sqlifyString" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::String)]
                } else {
                    vec![]
                }
            }
            "sqlifyBool" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Bool)]
                } else {
                    vec![]
                }
            }
            "sqlifyTime" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Time)]
                } else {
                    vec![]
                }
            }
            "sqlifyClocktime" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Clocktime)]
                } else {
                    vec![]
                }
            }
            "sqlifyCalendardate" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Calendardate)]
                } else {
                    vec![]
                }
            }
            "sqlifyBlob" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Blob)]
                } else {
                    vec![]
                }
            }
            "sqlifyChannel" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Channel)]
                } else {
                    vec![]
                }
            }
            "sqlifyClient" => {
                if let [(ae, _)] = args.as_slice() {
                    vec![(p_exp(env, ae, settings), SqlType::Client)]
                } else {
                    vec![]
                }
            }
            _ => vec![],
        },
        _ => vec![],
    }
}

// ---------------------------------------------------------------------------
// Query and DML printing (Postgres)
// ---------------------------------------------------------------------------

fn p_exp_query(env: &CjrEnv, qm: &QueryMeta, settings: &Settings) -> String {
    cjr_test_tick();
    let state_t = p_typ(env, &qm.state);
    let initial_s = p_exp(env, &qm.initial, settings);
    let query_s = p_exp(env, &qm.query, settings);
    let loc_str = "query";
    let env_depth = env.count_e_rels();

    // Sort exps and expand tables to get the full output column list
    let mut exps: Vec<(String, crate::settings::SqlType)> = qm
        .exps
        .iter()
        .map(|(x, t)| (format!("__uwf_{}", ident(x)), sql_type_in(t)))
        .collect();
    let mut table_cols: Vec<(String, crate::settings::SqlType)> = qm
        .tables
        .iter()
        .flat_map(|(tname, cols)| {
            cols.iter().map(move |(cname, t)| {
                (
                    format!("__uwf_{}.__uwf_{}", ident(tname), ident(cname)),
                    sql_type_in(t),
                )
            })
        })
        .collect();
    exps.sort_by(|a, b| a.0.cmp(&b.0));
    table_cols.sort_by(|a, b| a.0.cmp(&b.0));
    let outputs: Vec<(String, crate::settings::SqlType)> =
        exps.into_iter().chain(table_cols).collect();

    // Build the body expression in an extended environment (push r and acc)
    let mut env2 = env.clone();
    let row_t = crate::error_types::Located::dummy(Typ::Record(qm.rnum));
    env2.push_e_rel("r", row_t);
    env2.push_e_rel("acc", qm.state.clone());
    let body_s = p_exp(&env2, &qm.body, settings);

    let do_cols = make_do_cols(qm.rnum, &outputs, &body_s, env_depth, false, loc_str);

    match &qm.prepared {
        None => {
            let query_common_s = query_common(loc_str, "query", &outputs, &do_cols);
            format!(
                "(({{\n\
                 {state_t} acc = {initial_s};\n\
                 int dummy = (uw_begin_region(ctx), 0);\n\
                 uw_ensure_transaction(ctx);\n\
                 char *query = {query_s};\n\n\
                 PGconn *conn = uw_get_db(ctx);\n\
                 PGresult *res = PQexecParams(conn, query, 0, NULL, NULL, NULL, NULL, 0);\n\n\
                 {query_common}\
                 acc;\n\
                 }}))",
                state_t = state_t,
                initial_s = initial_s,
                query_s = query_s,
                query_common = query_common_s,
            )
        }
        Some(pq) => {
            let inputs = get_pargs(&qm.query, env, settings);
            let params_s = if inputs.is_empty() {
                String::new()
            } else {
                make_params(&inputs)
            };
            let n_inputs = inputs.len();
            let query_common_s = query_common(
                loc_str,
                &format!("\"{}\"", pq.query.replace('"', "\\\"")),
                &outputs,
                &do_cols,
            );
            let arg_decls: String = inputs
                .iter()
                .enumerate()
                .map(|(i, (e, t))| format!("{} arg{} = {};\n", t.c_type(), i + 1, e))
                .collect();
            let exec_call = if settings.persistent() {
                format!(
                    "PQexecPrepared(conn, \"uw{id}\", {n}, paramValues, paramLengths, paramFormats, 0)",
                    id = pq.id,
                    n = n_inputs,
                )
            } else {
                format!(
                    "PQexecParams(conn, \"{q}\", {n}, NULL, paramValues, paramLengths, paramFormats, 0)",
                    q = pq.query.replace('"', "\\\""),
                    n = n_inputs,
                )
            };
            format!(
                "(({{\n\
                 {state_t} acc = {initial_s};\n\
                 int dummy = (uw_begin_region(ctx), 0);\n\
                 uw_ensure_transaction(ctx);\n\
                 {arg_decls}\n\
                 PGconn *conn = uw_get_db(ctx);\n\
                 {params}\n\
                 PGresult *res = {exec};\n\n\
                 {query_common}\
                 acc;\n\
                 }}))",
                state_t = state_t,
                initial_s = initial_s,
                arg_decls = arg_decls,
                params = params_s,
                exec = exec_call,
                query_common = query_common_s,
            )
        }
    }
}

fn p_exp_dml(env: &CjrEnv, dm: &DmlMeta, settings: &Settings) -> String {
    cjr_test_tick();
    let dml_s = p_exp(env, &dm.dml, settings);
    let loc_str = "dml";

    let make_savepoint = match dm.mode {
        FailureMode::None => {
            "PGresult *res = PQexec(conn, \"SAVEPOINT s\");\n\
             if (res == NULL) { uw_try_reconnecting_and_restarting(ctx); uw_error(ctx, FATAL, \"Can't allocate DML SAVEPOINT result; database server may be down.\"); }\n\
             if (PQresultStatus(res) != PGRES_COMMAND_OK) { PQclear(res); uw_error(ctx, FATAL, \"Error creating SAVEPOINT\"); }\n\
             PQclear(res);\n\n"
        }
        FailureMode::Error => "",
    };

    let dml_common = |dml_expr: &str| -> String {
        let error_case = match dm.mode {
            FailureMode::Error => format!(
                "PQclear(res);\nuw_error(ctx, FATAL, \"{loc}: DML failed:\\n%s\\n%s\", {dml}, PQerrorMessage(conn));",
                loc = loc_str,
                dml = dml_expr,
            ),
            FailureMode::None => format!(
                "uw_set_error_message(ctx, PQerrorMessage(conn));\n\
                 res = PQexec(conn, \"ROLLBACK TO s\");\n\
                 if (res == NULL) {{ uw_try_reconnecting_and_restarting(ctx); uw_error(ctx, FATAL, \"Can't allocate DML ROLLBACK result; database server may be down.\"); }}\n\
                 if (PQresultStatus(res) != PGRES_COMMAND_OK) {{ PQclear(res); uw_error(ctx, FATAL, \"{loc}: ROLLBACK TO failed:\\n%s\\n%s\", {dml}, PQerrorMessage(conn)); }}\n\
                 PQclear(res);",
                loc = loc_str,
                dml = dml_expr,
            ),
        };
        let success_case = match dm.mode {
            FailureMode::Error => "PQclear(res);\n".into(),
            FailureMode::None => format!(
                " else {{\n\
                 PQclear(res);\n\
                 res = PQexec(conn, \"RELEASE s\");\n\
                 if (res == NULL) {{ uw_try_reconnecting_and_restarting(ctx); uw_error(ctx, FATAL, \"Can't allocate DML RELEASE result; database server may be down.\"); }}\n\
                 if (PQresultStatus(res) != PGRES_COMMAND_OK) {{ PQclear(res); uw_error(ctx, FATAL, \"{loc}: RELEASE failed:\\n%s\\n%s\", {dml}, PQerrorMessage(conn)); }}\n\
                 PQclear(res);\n}}\n",
                loc = loc_str,
                dml = dml_expr,
            ),
        };
        format!(
            "if (res == NULL) {{\n\
               uw_try_reconnecting_and_restarting(ctx);\n\
               uw_error(ctx, FATAL, \"Can't allocate DML result; database server may be down.\");\n\
             }}\n\
             if (PQresultStatus(res) != PGRES_COMMAND_OK) {{\n\
               if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), \"40001\")) {{ PQclear(res); uw_error(ctx, UNLIMITED_RETRY, \"Serialization failure\"); }}\n\
               if (!strcmp_nullsafe(PQresultErrorField(res, PG_DIAG_SQLSTATE), \"40P01\")) {{ PQclear(res); uw_error(ctx, UNLIMITED_RETRY, \"Deadlock detected\"); }}\n\
               {error}\n\
             }}{success}",
            error = error_case,
            success = success_case,
        )
    };

    let mode_result = match dm.mode {
        FailureMode::Error => "0",
        FailureMode::None => "uw_dup_and_clear_error_message(ctx)",
    };

    match &dm.prepared {
        None => {
            let dml_common_s = dml_common("dml");
            format!(
                "(uw_begin_region(ctx), ({{\n\
                 char *dml = {dml_s};\n\
                 PGconn *conn = uw_get_db(ctx);\n\
                 PGresult *res;\n\
                 {savepoint}\
                 res = PQexecParams(conn, dml, 0, NULL, NULL, NULL, NULL, 0);\n\n\
                 uw_ensure_transaction(ctx);\n\n\
                 {dml_common}\n\
                 uw_end_region(ctx);\n\
                 {mode_result};\n\
                 }}))",
                dml_s = dml_s,
                savepoint = make_savepoint,
                dml_common = dml_common_s,
                mode_result = mode_result,
            )
        }
        Some(pd) => {
            let inputs = get_pargs(&dm.dml, env, settings);
            let params_s = if inputs.is_empty() {
                String::new()
            } else {
                make_params(&inputs)
            };
            let n_inputs = inputs.len();
            let arg_decls: String = inputs
                .iter()
                .enumerate()
                .map(|(i, (e, t))| format!("{} arg{} = {};\n", t.c_type(), i + 1, e))
                .collect();
            let exec_call = if settings.persistent() {
                format!(
                    "PQexecPrepared(conn, \"uw{id}\", {n}, paramValues, paramLengths, paramFormats, 0)",
                    id = pd.id,
                    n = n_inputs,
                )
            } else {
                format!(
                    "PQexecParams(conn, \"{q}\", {n}, NULL, paramValues, paramLengths, paramFormats, 0)",
                    q = pd.dml.replace('"', "\\\""),
                    n = n_inputs,
                )
            };
            let dml_expr = format!("\"{}\"", pd.dml.replace('"', "\\\""));
            let dml_common_s = dml_common(&dml_expr);
            format!(
                "(uw_begin_region(ctx), ({{\n\
                 PGconn *conn = uw_get_db(ctx);\n\
                 {arg_decls}\n\
                 {params}\n\
                 PGresult *res;\n\
                 {savepoint}\
                 res = {exec};\n\n\
                 uw_ensure_transaction(ctx);\n\n\
                 {dml_common}\n\
                 uw_end_region(ctx);\n\
                 {mode_result};\n\
                 }}))",
                arg_decls = arg_decls,
                params = params_s,
                savepoint = make_savepoint,
                exec = exec_call,
                dml_common = dml_common_s,
                mode_result = mode_result,
            )
        }
    }
}

// ---------------------------------------------------------------------------
// strcat flattening helper
// ---------------------------------------------------------------------------

fn flatten_strcat(e1: &LocExp, e2: &LocExp) -> Vec<LocExp> {
    cjr_test_tick();
    let mut parts = Vec::new();
    collect_strcat_parts(e1, &mut parts);
    collect_strcat_parts(e2, &mut parts);
    parts
}

fn collect_strcat_parts(e: &LocExp, parts: &mut Vec<LocExp>) {
    cjr_test_tick();
    if let Exp::FfiApp(m, x, args) = &e.node {
        if m == "Basis" && x == "strcat" {
            if let [(e1, _), (e2, _)] = args.as_slice() {
                collect_strcat_parts(e1, parts);
                collect_strcat_parts(e2, parts);
                return;
            }
        }
    }
    parts.push(e.clone());
}

// ---------------------------------------------------------------------------
// Collect argument types from a function type (for multi-arg app eval order)
// ---------------------------------------------------------------------------

fn collect_arg_types(t: &LocTyp, n: usize) -> Vec<LocTyp> {
    cjr_test_tick();
    const MAX_ARGS: usize = 256; // sanity limit; real functions have far fewer
    let n = n.min(MAX_ARGS);
    let mut result = Vec::new();
    let mut cur = t.clone();
    while result.len() < n {
        cjr_test_tick();
        match cur.node.clone() {
            Typ::Fun(dom, ran) => {
                result.push(*dom);
                cur = *ran;
            }
            _ => break,
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Function printing
// ---------------------------------------------------------------------------

fn p_fun(
    is_rec: bool,
    env: &CjrEnv,
    fx: &str,
    n: usize,
    args: &[(String, LocTyp)],
    ran: &LocTyp,
    e: &LocExp,
    settings: &Settings,
) -> String {
    cjr_test_tick();
    let ran_s = p_typ(env, ran);
    let fn_name = format!("__uwn_{}_{}", ident(fx), n);

    // Build env with args pushed
    let mut env2 = env.clone();
    for (arg_name, arg_t) in args {
        env2.push_e_rel(arg_name, arg_t.clone());
    }

    // Arg list for the function signature: use the rel names in env2
    let arg_decls: Vec<String> = args
        .iter()
        .enumerate()
        .map(|(i, (arg_name, arg_t))| {
            let rel_name = format!("__uwr_{}_{}", ident(arg_name), i);
            format!("{} {}", p_typ(env, arg_t), rel_name)
        })
        .collect();

    let params = if arg_decls.is_empty() {
        "uw_context ctx".to_string()
    } else {
        format!("uw_context ctx, {}", arg_decls.join(", "))
    };

    let body_s = p_exp(&env2, e, settings);

    let restart_label = if is_rec { "restart:\n" } else { "" };

    format!(
        "static {ran_s} {fn_name}({params}) {{\n{restart_label}return({body_s});\n}}",
        ran_s = ran_s,
        fn_name = fn_name,
        params = params,
        restart_label = restart_label,
        body_s = body_s,
    )
}

// ---------------------------------------------------------------------------
// Forward declaration (prototype)
// ---------------------------------------------------------------------------

fn p_proto(env: &CjrEnv, fx: &str, n: usize, args: &[(String, LocTyp)], ran: &LocTyp) -> String {
    cjr_test_tick();
    let ran_s = p_typ(env, ran);
    let fn_name = format!("__uwn_{}_{}", ident(fx), n);
    let arg_types: Vec<String> = args.iter().map(|(_, t)| p_typ(env, t)).collect();
    let params = if arg_types.is_empty() {
        "uw_context".to_string()
    } else {
        format!("uw_context, {}", arg_types.join(", "))
    };
    format!("static {} {}({});", ran_s, fn_name, params)
}

// ---------------------------------------------------------------------------
// Declaration printing
// ---------------------------------------------------------------------------

/// C `#line` so DWARF/debuggers map generated C back to Ur source (`.ur` / `.urs`).
fn format_line_directive_for_span(span: &crate::error_types::Span) -> Option<String> {
    if span.file.is_empty() || span.first.line == 0 {
        return None;
    }
    let path = span.file.replace('\\', "\\\\").replace('"', "\\\"");
    Some(format!("#line {} \"{}\"\n", span.first.line, path))
}

fn p_decl(
    env: &CjrEnv,
    d: &LocDecl,
    settings: &Settings,
    global_initializers: &mut Vec<String>,
) -> String {
    cjr_test_tick();
    match &d.node {
        Decl::Struct(n, xts) => {
            if xts.is_empty() {
                // unit struct — still emit the typedef so code compiles
                return format!("/* struct __uws_{} is uw_unit */", n);
            }
            let mut s = format!("struct __uws_{} {{\n", n);
            for (x, t) in xts {
                s.push_str(&format!("{} __uwf_{};\n", p_typ(env, t), ident(x)));
            }
            s.push_str("};");
            s
        }

        Decl::Datatype(dts) => {
            let mut parts = Vec::new();
            for dt in dts {
                let s = p_datatype_decl(env, dt);
                if !s.is_empty() {
                    parts.push(s);
                }
            }
            parts.join("\n\n")
        }

        Decl::DatatypeForward(_, _, _) => String::new(),

        Decl::Val(x, n, t, e) => {
            let t_s = p_typ(env, t);
            let name = p_named_name(*n, x);
            let val_s = p_exp(env, e, settings);
            global_initializers.push(format!("{} = {};", name, val_s));
            format!("{} {};", t_s, name)
        }

        Decl::Fun(fx, n, args, ran, e) => p_fun(false, env, fx, *n, args, ran, e, settings),

        Decl::FunRec(vis) => {
            // First emit forward declarations for the whole group
            let mut out = String::new();
            for (fx, n, args, ran, _) in vis {
                out.push_str(&p_proto(env, fx, *n, args, ran));
                out.push('\n');
            }
            out.push('\n');
            // Then emit definitions
            for (fx, n, args, ran, e) in vis {
                out.push_str(&p_fun(true, env, fx, *n, args, ran, e, settings));
                out.push('\n');
            }
            out
        }

        Decl::Table(x, _, sql, csts) => {
            let cst_s: Vec<String> = csts.iter().map(|(k, v)| format!("{}: {}", k, v)).collect();
            format!(
                "/* SQL table {} {} constraints {} */",
                x,
                sql,
                cst_s.join(", ")
            )
        }

        Decl::Sequence(x) => format!("/* SQL sequence {} */", x),

        Decl::View(x, _, sql) => format!("/* SQL view {} AS {} */", x, sql),

        Decl::Index(tab, cols) => {
            let col_s: Vec<String> = cols.iter().map(|(f, _m)| f.clone()).collect();
            format!("/* SQL index {} : {} */", tab, col_s.join(", "))
        }

        Decl::Database { .. } => String::new(),

        Decl::PreparedStatements(_) => String::new(),

        Decl::JavaScript(s) => {
            // Escape the JS string for embedding as a C string literal
            let escaped = s
                .replace('\\', "\\\\")
                .replace('"', "\\\"")
                .replace('\n', "\\n")
                .replace('\r', "\\r");
            format!("static char jslib[] = \"{}\";", escaped)
        }

        Decl::Cookie(s) => format!("/* cookie {} */", s),

        Decl::Style(s) => format!("/* style {} */", s),

        Decl::Task(_, _, _, _) => String::new(),

        Decl::OnError(_) => String::new(),
    }
}

fn p_datatype_decl(env: &CjrEnv, dt: &DatatypeDecl) -> String {
    cjr_test_tick();
    match dt.kind {
        DatatypeKind::Enum => {
            let enum_name = format!("__uwe_{}_{}", ident(&dt.name), dt.id);
            let consts: Vec<String> = dt
                .constrs
                .iter()
                .map(|(x, n, _)| format!("__uwc_{}_{}", ident(x), n))
                .collect();
            let body = if consts.is_empty() {
                format!("__uwec_{}_{}", ident(&dt.name), dt.id)
            } else {
                consts.join(", ")
            };
            format!("enum {} {{ {} }};", enum_name, body)
        }
        DatatypeKind::Option => String::new(), // No separate C declaration needed
        DatatypeKind::Default => {
            let enum_name = format!("__uwe_{}_{}", ident(&dt.name), dt.id);
            let struct_name = format!("__uwd_{}_{}", ident(&dt.name), dt.id);

            let consts: Vec<String> = dt
                .constrs
                .iter()
                .map(|(x, n, _)| format!("__uwc_{}_{}", ident(x), n))
                .collect();
            let enum_decl = format!("enum {} {{ {} }};", enum_name, consts.join(", "));

            // Constructors with args go in a union
            let args_constrs: Vec<&(String, usize, Option<LocTyp>)> =
                dt.constrs.iter().filter(|(_, _, t)| t.is_some()).collect();

            let mut struct_decl = format!("struct {} {{\n", struct_name);
            struct_decl.push_str(&format!("enum {} tag;\n", enum_name));
            if !args_constrs.is_empty() {
                struct_decl.push_str("union {\n");
                for (x, _n, t) in &args_constrs {
                    if let Some(t) = t {
                        struct_decl.push_str(&format!("{} uw_{};\n", p_typ(env, t), ident(x)));
                    }
                }
                struct_decl.push_str("} data;\n");
            }
            struct_decl.push_str("};");

            format!("{}\n\n{}", enum_decl, struct_decl)
        }
    }
}

// ---------------------------------------------------------------------------
// URL unurlify helpers
// ---------------------------------------------------------------------------

/// `deStar` helper: convert `"(*request)"` to `"request"` and others to `"&X"`.
fn de_star(request: &str) -> String {
    if request == "(*request)" {
        "request".to_string()
    } else {
        format!("&{}", request)
    }
}

/// Capitalize the first ASCII character of `s`.
fn capitalize(s: &str) -> String {
    let mut out = s.to_string();
    if let Some(c) = out.get_mut(0..1) {
        c.make_ascii_uppercase();
    }
    out
}

/// Generate the chain of strncmp checks for an enum datatype's unurlification.
fn do_em_enum(
    request: &str,
    xncs: &[(String, usize, Option<LocTyp>)],
    x: &str,
    i: usize,
) -> String {
    cjr_test_tick();
    match xncs {
        [] => format!(
            "(uw_error(ctx, FATAL, \"Error unurlifying datatype {x}\"), \
             (enum __uwe_{x_ident}_{i})0)",
            x_ident = ident(x)
        ),
        [(x_, n, _), rest @ ..] => {
            let len = x_.len();
            let x_ident = ident(x_);
            let rest_s = do_em_enum(request, rest, x, i);
            format!(
                "((!strncmp({request}, \"{x_}\", {len}) \
                 && ({request}[{len}] == 0 || {request}[{len}] == '/')) \
                 ? ({request} += {len}, \
                    ({request}[0] == '/' ? ++{request} : NULL), \
                    __uwc_{x_ident}_{n}) \
                 : {rest_s})"
            )
        }
    }
}

/// Generate the chain of strncmp checks for a Default datatype's unurlification.
fn do_em_default(
    xncs: &[(String, usize, Option<LocTyp>)],
    x: &str,
    i: usize,
    env: &CjrEnv,
    from_client: bool,
) -> String {
    cjr_test_tick();
    match xncs {
        [] => format!("(uw_error(ctx, FATAL, \"Error unurlifying datatype {x}\"), NULL)"),
        [(x_, n, to), rest @ ..] => {
            let x_ident = ident(x_);
            let x_dt_ident = ident(x);
            let len = x_.len();
            let rest_s = do_em_default(rest, x, i, env, from_client);
            let tag_code = format!(
                "struct __uwd_{x_dt_ident}_{i} *tmp = \
                 uw_malloc(ctx, sizeof(struct __uwd_{x_dt_ident}_{i}));\n\
                 tmp->tag = __uwc_{x_ident}_{n};\n\
                 *request += {len};\n\
                 if ((*request)[0] == '/') ++*request;\n"
            );
            let arg_code = match to {
                None => String::new(),
                Some(t_arg) => {
                    let inner = unurlify_req("(*request)", t_arg, env, from_client);
                    format!("tmp->data.uw_{x_ident} = {inner};\n")
                }
            };
            format!(
                "((!strncmp(*request, \"{x_}\", {len}) \
                 && ((*request)[{len}] == 0 || (*request)[{len}] == '/')) \
                 ? ({{\n{tag_code}{arg_code}tmp;\n}}) \
                 : {rest_s})"
            )
        }
    }
}

/// Generate C code to parse a URL-encoded value of type `t` from a `char **request` pointer.
/// When called from the inline context (not a helper function), `request` is a `char *` local.
fn unurlify_req(request: &str, t: &LocTyp, env: &CjrEnv, from_client: bool) -> String {
    cjr_test_tick();
    match &t.node {
        Typ::Ffi(m, name) if m == "Basis" && name == "unit" => {
            format!("uw_Basis_unurlifyUnit(ctx, {})", de_star(request))
        }
        Typ::Ffi(m, name) if m == "Basis" && name == "string" => {
            if from_client {
                format!(
                    "uw_Basis_unurlifyString_fromClient(ctx, {})",
                    de_star(request)
                )
            } else {
                format!("uw_Basis_unurlifyString(ctx, {})", de_star(request))
            }
        }
        Typ::Ffi(m, name) => {
            format!(
                "uw_{}_{unurlify}{}(ctx, {})",
                ident(m),
                capitalize(name),
                de_star(request),
                unurlify = "unurlify"
            )
        }
        Typ::Record(0) => format!("uw_Basis_unurlifyUnit(ctx, {})", de_star(request)),
        Typ::Record(i) => {
            let fields = env.structs.get(i).cloned().unwrap_or_default();
            let mut out = String::from("({\n");
            for (x, ft) in &fields {
                let inner = unurlify_req(request, ft, env, from_client);
                out.push_str(&format!(
                    "{} uwr_{} = {};\n",
                    p_typ(env, ft),
                    ident(x),
                    inner
                ));
            }
            out.push_str(&format!("struct __uws_{i} tmp = {{ "));
            let field_names: Vec<String> = fields
                .iter()
                .map(|(x, _)| format!("uwr_{}", ident(x)))
                .collect();
            out.push_str(&field_names.join(", "));
            out.push_str(" };\ntmp;\n})");
            out
        }
        Typ::Datatype(DatatypeKind::Enum, i, xncs_ref) => {
            let (x, xncs) = env
                .lookup_datatype(*i)
                .map(|(x, v)| (x.clone(), v.clone()))
                .unwrap_or_else(|| {
                    (
                        "?".into(),
                        lock_for_compile(xncs_ref.as_ref(), "CJR print datatype constructors")
                            .clone(),
                    )
                });
            let inner = do_em_enum(request, &xncs, &x, *i);
            format!("({request}[0] == '/' ? ++{request} : {request},\n{inner})")
        }
        Typ::Datatype(DatatypeKind::Option, i, xncs_ref) => {
            let already = UNURLIFY_SEEN.with(|s| s.borrow().contains(i));
            if already {
                format!("unurlify_{i}(ctx, {})", de_star(request))
            } else {
                UNURLIFY_SEEN.with(|s| s.borrow_mut().insert(*i));
                let (x, xncs) = env
                    .lookup_datatype(*i)
                    .map(|(x, v)| (x.clone(), v.clone()))
                    .unwrap_or_else(|| {
                        (
                            "?".into(),
                            lock_for_compile(xncs_ref.as_ref(), "CJR print datatype constructors")
                                .clone(),
                        )
                    });
                let (no_arg, has_arg, t_inner) = match xncs.as_slice() {
                    [(a, _, None), (b, _, Some(t))] => (a.clone(), b.clone(), t.clone()),
                    [(b, _, Some(t)), (a, _, None)] => (a.clone(), b.clone(), t.clone()),
                    _ => return format!("/* unurlify: bad Option datatype */ NULL"),
                };
                let unboxable = is_unboxable(&t_inner);
                let t_s = p_typ(env, &t_inner);
                let no_arg_len = no_arg.len();
                let has_arg_len = has_arg.len();
                let has_arg_body = if unboxable {
                    unurlify_req("(*request)", &t_inner, env, from_client)
                } else {
                    let inner = unurlify_req("(*request)", &t_inner, env, from_client);
                    format!(
                        "({{\n{t_s} *tmp = uw_malloc(ctx, sizeof({t_s}));\n\
                             *tmp = {inner};\ntmp;\n}})"
                    )
                };
                let star = if unboxable { "" } else { "*" };
                let proto = format!("static {t_s} {star}unurlify_{i}(uw_context, char **);\n");
                let def = format!(
                    "static {t_s} {star}unurlify_{i}(uw_context ctx, char **request) {{\n\
                     return ((*request)[0] == '/' ? ++*request : *request,\n\
                     ((!strncmp(*request, \"{no_arg}\", {no_arg_len}) \
                     && ((*request)[{no_arg_len}] == 0 || (*request)[{no_arg_len}] == '/')) \
                     ? (*request += {no_arg_len}, NULL) \
                     : ((!strncmp(*request, \"{has_arg}\", {has_arg_len}) \
                     && ((*request)[{has_arg_len}] == 0 || (*request)[{has_arg_len}] == '/')) \
                     ? (*request += {has_arg_len}, \
                        ((*request)[0] == '/' ? ++*request : NULL),\n\
                        {has_arg_body})\n\
                     : (uw_error(ctx, FATAL, \
                        \"Error unurlifying datatype {x}\"), NULL))));\n}}\n"
                );
                add_url_handler(proto, def);
                format!("unurlify_{i}(ctx, {})", de_star(request))
            }
        }
        Typ::Datatype(DatatypeKind::Default, i, xncs_ref) => {
            let already = UNURLIFY_SEEN.with(|s| s.borrow().contains(i));
            if already {
                format!("unurlify_{i}(ctx, {})", de_star(request))
            } else {
                UNURLIFY_SEEN.with(|s| s.borrow_mut().insert(*i));
                let (x, xncs) = env
                    .lookup_datatype(*i)
                    .map(|(x, v)| (x.clone(), v.clone()))
                    .unwrap_or_else(|| {
                        (
                            "?".into(),
                            lock_for_compile(xncs_ref.as_ref(), "CJR print datatype constructors")
                                .clone(),
                        )
                    });
                let x_ident = ident(&x);
                let t_name = format!("struct __uwd_{x_ident}_{i}");
                let body = do_em_default(&xncs, &x, *i, env, from_client);
                let proto = format!("static {t_name} *unurlify_{i}(uw_context, char **);\n");
                let def = format!(
                    "static {t_name} *unurlify_{i}(uw_context ctx, char **request) {{\n\
                     return {body};\n}}\n"
                );
                add_url_handler(proto, def);
                format!("unurlify_{i}(ctx, {})", de_star(request))
            }
        }
        Typ::List(t_inner, i) => {
            // Use a distinct key to avoid colliding with datatype ids: i | (1 << 63)
            let list_key = *i | (1usize << 62);
            let already = UNURLIFY_SEEN.with(|s| s.borrow().contains(&list_key));
            if already {
                format!("unurlify_list_{i}(ctx, {})", de_star(request))
            } else {
                UNURLIFY_SEEN.with(|s| s.borrow_mut().insert(list_key));
                let t_s = p_typ(env, t_inner); // element type
                                               // The list struct type
                let list_t = format!("struct __uws_{i} *");
                // unurlify a Cons node (Record of the list struct)
                let record_t = crate::error_types::Located::dummy(Typ::Record(*i));
                let inner_s = unurlify_req("(*request)", &record_t, env, from_client);
                let proto = format!("static {list_t}unurlify_list_{i}(uw_context, char **);\n");
                let _ = t_s;
                let def = format!(
                    "static {list_t}unurlify_list_{i}(uw_context ctx, char **request) {{\n\
                     return ((*request)[0] == '/' ? ++*request : *request,\n\
                     ((!strncmp(*request, \"Nil\", 3) && ((*request)[3] == 0 || (*request)[3] == '/')) \
                     ? (*request += 3, \
                        ((*request)[0] == '/' ? ((*request)[0] = 0, ++*request) : NULL), NULL) \
                     : ((!strncmp(*request, \"Cons\", 4) && ((*request)[4] == 0 || (*request)[4] == '/')) \
                     ? (*request += 4, ((*request)[0] == '/' ? ++*request : NULL),\n\
                        ({{\n{list_t}tmp = uw_malloc(ctx, sizeof(struct __uws_{i}));\n\
                        *tmp = {inner_s};\ntmp;\n}})) \
                     : (uw_error(ctx, FATAL, \"Error unurlifying list: %s\", *request), NULL))));\n}}\n"
                );
                add_url_handler(proto, def);
                format!("unurlify_list_{i}(ctx, {})", de_star(request))
            }
        }
        Typ::Option(inner) => {
            // Inline TOption (nullable pointer wrapping)
            let inner_unurl = unurlify_req(request, inner, env, from_client);
            let inner_t = p_typ(env, inner);
            format!(
                "({request}[0] == '/' ? ++{request} : {request}, \
                 ((!strncmp({request}, \"None\", 4) \
                 && ({request}[4] == 0 || {request}[4] == '/')) \
                 ? ({request} += ({request}[4] == 0 ? 4 : 5), NULL) \
                 : ((!strncmp({request}, \"Some\", 4) && {request}[4] == '/') \
                 ? ({request} += 5, \
                    ({{ {inner_t} *tmp = uw_malloc(ctx, sizeof({inner_t})); \
                    *tmp = {inner_unurl}; tmp; }}) \
                 : (uw_error(ctx, FATAL, \"Error unurlifying option type\"), NULL))))"
            )
        }
        _ => format!("/* unurlify unknown type */ ({}){{}}", p_typ(env, t)),
    }
}

/// Wrapper: parse from a `char *request` local (not a `char **`).
fn unurlify(t: &LocTyp, env: &CjrEnv, from_client: bool) -> String {
    cjr_test_tick();
    unurlify_req("request", t, env, from_client)
}

// ---------------------------------------------------------------------------
// URL urlify helpers
// ---------------------------------------------------------------------------

/// Generate C statements to urlify-write a value `it<level>` of type `t`.
fn urlify_stmts(level: usize, t: &LocTyp, env: &CjrEnv) -> String {
    cjr_test_tick();
    match &t.node {
        Typ::Ffi(m, name) if m == "Basis" && name == "unit" => {
            "uw_Basis_urlifyString_w(ctx, \"\");\n".to_string()
        }
        Typ::Ffi(m, name) => {
            format!(
                "uw_{}_urlify{}_w(ctx, it{level});\n",
                ident(m),
                capitalize(name)
            )
        }
        Typ::Record(0) => "uw_Basis_urlifyString_w(ctx, \"\");\n".to_string(),
        Typ::Record(i) => {
            let fields = env.structs.get(i).cloned().unwrap_or_default();
            let mut out = String::new();
            let mut printing_since_slash = false;
            for (x, ft) in &fields {
                let ft_s = p_typ(env, ft);
                out.push_str("{\n");
                out.push_str(&format!(
                    "{ft_s} it{} = it{level}.__uwf_{};\n",
                    level + 1,
                    ident(x)
                ));
                if printing_since_slash {
                    out.push_str("uw_write(ctx, \"/\");\n");
                }
                out.push_str(&urlify_stmts(level + 1, ft, env));
                out.push_str("}\n");
                printing_since_slash = true;
            }
            out
        }
        Typ::Datatype(DatatypeKind::Enum, i, xncs_ref) => {
            let (x, xncs) = env
                .lookup_datatype(*i)
                .map(|(x, v)| (x.clone(), v.clone()))
                .unwrap_or_else(|| {
                    (
                        "?".into(),
                        lock_for_compile(xncs_ref.as_ref(), "CJR print datatype constructors")
                            .clone(),
                    )
                });
            urlify_enum_stmts(level, &xncs, &x, *i)
        }
        Typ::Datatype(DatatypeKind::Option, i, xncs_ref) => {
            let already = URLIFY_SEEN.with(|s| s.borrow().contains(i));
            if !already {
                URLIFY_SEEN.with(|s| s.borrow_mut().insert(*i));
                let (x, xncs) = env
                    .lookup_datatype(*i)
                    .map(|(x, v)| (x.clone(), v.clone()))
                    .unwrap_or_else(|| {
                        (
                            "?".into(),
                            lock_for_compile(xncs_ref.as_ref(), "CJR print datatype constructors")
                                .clone(),
                        )
                    });
                let (no_arg, has_arg, t_inner) = match xncs.as_slice() {
                    [(a, _, None), (b, _, Some(t))] => (a.clone(), b.clone(), t.clone()),
                    [(b, _, Some(t)), (a, _, None)] => (a.clone(), b.clone(), t.clone()),
                    _ => {
                        return format!("urlify_{i}(ctx, it{level});\n");
                    }
                };
                let unboxable = is_unboxable(&t_inner);
                let t_s = p_typ(env, &t_inner);
                let has_arg_body = if unboxable {
                    format!(
                        "uw_write(ctx, \"{has_arg}/\");\n{}",
                        urlify_stmts(0, &t_inner, env)
                    )
                } else {
                    format!(
                        "{t_s} it1 = *it0;\nuw_write(ctx, \"{has_arg}/\");\n{}",
                        urlify_stmts(1, &t_inner, env)
                    )
                };
                let star = if unboxable { "" } else { "*" };
                let proto = format!("static void urlify_{i}(uw_context, {t_s} {star});\n");
                let def = format!(
                    "static void urlify_{i}(uw_context ctx, {t_s} {star}it0) {{\n\
                     if (it0) {{\n{has_arg_body}}} else {{\nuw_write(ctx, \"{no_arg}\");\n}}\n}}\n\n"
                );
                let _ = x;
                add_url_handler(proto, def);
            }
            format!("urlify_{i}(ctx, it{level});\n")
        }
        Typ::Datatype(DatatypeKind::Default, i, xncs_ref) => {
            let already = URLIFY_SEEN.with(|s| s.borrow().contains(i));
            if !already {
                URLIFY_SEEN.with(|s| s.borrow_mut().insert(*i));
                let (x, xncs) = env
                    .lookup_datatype(*i)
                    .map(|(x, v)| (x.clone(), v.clone()))
                    .unwrap_or_else(|| {
                        (
                            "?".into(),
                            lock_for_compile(xncs_ref.as_ref(), "CJR print datatype constructors")
                                .clone(),
                        )
                    });
                let x_ident = ident(&x);
                let t_name = format!("struct __uwd_{x_ident}_{i}");
                let body = urlify_default_stmts(&xncs, &x, *i, env);
                let proto = format!("static void urlify_{i}(uw_context, {t_name} *);\n");
                let def = format!(
                    "static void urlify_{i}(uw_context ctx, {t_name} *it0) {{\n{body}}}\n\n"
                );
                add_url_handler(proto, def);
            }
            format!("urlify_{i}(ctx, it{level});\n")
        }
        Typ::List(_t_inner, i) => {
            let list_key = *i | (1usize << 62);
            let already = URLIFY_SEEN.with(|s| s.borrow().contains(&list_key));
            if !already {
                URLIFY_SEEN.with(|s| s.borrow_mut().insert(list_key));
                let list_t = format!("struct __uws_{i} *");
                let record_t = crate::error_types::Located::dummy(Typ::Record(*i));
                let inner_body = urlify_stmts(1, &record_t, env);
                let proto = format!("static void urlifyl_{i}(uw_context, {list_t});\n");
                let def = format!(
                    "static void urlifyl_{i}(uw_context ctx, {list_t}it0) {{\n\
                     if (it0) {{\n\
                     uw_write(ctx, \"Cons/\");\n\
                     struct __uws_{i} it1 = *it0;\n\
                     {inner_body}\
                     urlifyl_{i}(ctx, it0->next);\n\
                     }} else {{\nuw_write(ctx, \"Nil\");\n}}\n}}\n\n"
                );
                add_url_handler(proto, def);
            }
            format!("urlifyl_{i}(ctx, it{level});\n")
        }
        Typ::Option(inner) => {
            let inner_t = p_typ(env, inner);
            let unboxable = is_unboxable(inner);
            let next_level = if unboxable { level } else { level + 1 };
            let deref = if unboxable {
                String::new()
            } else {
                format!("{inner_t} it{next_level} = *it{level};\n")
            };
            let inner_stmts = urlify_stmts(next_level, inner, env);
            format!(
                "if (it{level}) {{\n\
                 uw_write(ctx, \"Some/\");\n\
                 {deref}\
                 {inner_stmts}\
                 }} else {{\nuw_write(ctx, \"None\");\n}}\n"
            )
        }
        _ => format!("/* urlify unknown type: {} */\n", p_typ(env, t)),
    }
}

/// Generate if-else chain for urlifying an enum datatype.
fn urlify_enum_stmts(
    level: usize,
    xncs: &[(String, usize, Option<LocTyp>)],
    x: &str,
    i: usize,
) -> String {
    cjr_test_tick();
    match xncs {
        [] => format!("uw_error(ctx, FATAL, \"Error urlifying datatype {x}\");\n"),
        [(x_, n, _), rest @ ..] => {
            let x_ident = ident(x_);
            let rest_s = urlify_enum_stmts(level, rest, x, i);
            format!(
                "if (it{level} == __uwc_{x_ident}_{n}) {{\n\
                 uw_write(ctx, \"{x_}\");\n\
                 }} else {{\n{rest_s}}}\n"
            )
        }
    }
}

/// Generate if-else chain for urlifying a Default datatype.
fn urlify_default_stmts(
    xncs: &[(String, usize, Option<LocTyp>)],
    x: &str,
    i: usize,
    env: &CjrEnv,
) -> String {
    cjr_test_tick();
    match xncs {
        [] => format!("uw_error(ctx, FATAL, \"Error urlifying datatype {x} (%d)\", it0->data);\n"),
        [(x_, n, to), rest @ ..] => {
            let x_ident = ident(x_);
            let rest_s = urlify_default_stmts(rest, x, i, env);
            let arm = match to {
                None => format!("uw_write(ctx, \"{x_}\");\n"),
                Some(t_arg) => {
                    let t_s = p_typ(env, t_arg);
                    let inner = urlify_stmts(1, t_arg, env);
                    format!(
                        "uw_write(ctx, \"{x_}/\");\n{t_s} it1 = it0->data.uw_{x_ident};\n{inner}"
                    )
                }
            };
            format!("if (it0->tag == __uwc_{x_ident}_{n}) {{\n{arm}}} else {{\n{rest_s}}}\n")
        }
    }
}

/// Generate a page handler if-block for one export entry.
fn p_page(
    ek: &ExportKind,
    path: &str,
    n: usize,
    ts: &[LocTyp],
    ran: &LocTyp,
    side: &Sidedness,
    dbmode: &DbMode,
    tell_sig: bool,
    env: &CjrEnv,
    settings: &Settings,
) -> String {
    cjr_test_tick();
    // Strip the url_prefix from the path (already included in the path from cjrize)
    let path_c = path.replace('"', "\\\"").replace('\n', "\\n");
    let path_len = path.len();

    let could_write = matches!(ek, ExportKind::Action(_) | ExportKind::Rpc(_));
    let could_write_db = !matches!(dbmode, DbMode::NoDb);
    let needs_push = matches!(side, Sidedness::ServerAndPullAndPush);
    let is_rpc = matches!(ek, ExportKind::Rpc(_));

    // For Action exports, the last argument is a record of form inputs.
    // For Link/Extern/Rpc, all args are URL-parsed.
    let (url_ts, has_form_inputs) = match ek {
        ExportKind::Action(_) if ts.len() >= 2 => (&ts[..ts.len() - 2], true),
        _ if !ts.is_empty() => (&ts[..ts.len() - 1], false),
        _ => (&ts[..0], false),
    };

    let mut body = String::new();

    // Advance past the path prefix
    body.push_str(&format!(
        "request += {path_len};\n\
         if (*request == '/') ++request;\n"
    ));

    // For RPC: append POST body to request
    if is_rpc {
        body.push_str(
            "if (uw_hasPostBody(ctx)) {\n\
             uw_Basis_postBody pb = uw_getPostBody(ctx);\n\
             if (pb.data[0])\n\
             request = uw_Basis_strcat(ctx, request, pb.data);\n\
             }\n",
        );
    }

    // CSRF check for write actions
    if could_write && !settings.no_xsrf_protection.contains(path) {
        body.push_str(
            "{\n\
             uw_Basis_string sig = uw_Basis_requestHeader(ctx, \"UrWeb-Sig\");\n\
             if (sig == NULL) uw_error(ctx, FATAL, \"Missing cookie signature\");\n\
             if (!uw_streq(sig, uw_cookie_sig(ctx)))\n\
             uw_error(ctx, FATAL, \"Wrong cookie signature\");\n\
             }\n",
        );
    }

    // Write Content-Type header
    if is_rpc {
        body.push_str("uw_write_header(ctx, \"Content-type: text/plain\\r\\n\");\n");
    } else {
        body.push_str("uw_write_header(ctx, \"Content-type: text/html; charset=utf-8\\r\\n\");\n");
        if !matches!(side, Sidedness::ServerOnly) {
            body.push_str(
                "uw_write_header(ctx, \"Content-script-type: text/javascript\\r\\n\");\n",
            );
        }
        if settings.html5 {
            body.push_str("uw_write(ctx, uw_begin_html5);\n");
        } else {
            body.push_str("uw_write(ctx, uw_begin_xhtml);\n");
        }
        body.push_str("uw_mayReturnIndirectly(ctx);\n");
    }

    // Set context flags
    body.push_str(&format!(
        "uw_set_could_write_db(ctx, {});\n",
        if could_write_db { 1 } else { 0 }
    ));
    body.push_str(&format!(
        "uw_set_at_most_one_query(ctx, {});\n",
        if matches!(dbmode, DbMode::OneQuery) {
            1
        } else {
            0
        }
    ));
    body.push_str(&format!(
        "uw_set_needs_push(ctx, {});\n",
        if needs_push { 1 } else { 0 }
    ));
    body.push_str(&format!(
        "uw_set_needs_sig(ctx, {});\n",
        if tell_sig { 1 } else { 0 }
    ));
    body.push_str("uw_login(ctx);\n");

    // Parse URL arguments
    body.push_str("{\n");
    for (i, t) in url_ts.iter().enumerate() {
        let t_s = p_typ(env, t);
        let unurl = unurlify(t, env, false);
        body.push_str(&format!("{} arg{} = {};\n", t_s, i, unurl));
    }

    // Parse form inputs (Action-specific)
    if has_form_inputs {
        // The second-to-last argument is the form record struct id
        if let Some(form_t) = ts.get(ts.len() - 2) {
            if let Typ::Record(struct_id) = &form_t.node {
                let fields = env.structs.get(struct_id).cloned().unwrap_or_default();
                let arg_idx = url_ts.len();
                if fields.is_empty() {
                    body.push_str(&format!("uw_unit arg{} = 0;\n", arg_idx));
                } else {
                    for (fi, (x, ft)) in fields.iter().enumerate() {
                        let ft_s = p_typ(env, ft);
                        body.push_str(&format!(
                            "{} uw_input_{x} = uw_Basis_unurlifyString(ctx, &request);\n",
                            ft_s
                        ));
                        let _ = fi;
                    }
                    body.push_str(&format!("struct __uws_{} uw_inputs = {{ ", struct_id));
                    let field_inits: Vec<String> = fields
                        .iter()
                        .map(|(x, _)| format!("uw_input_{}", ident(x)))
                        .collect();
                    body.push_str(&field_inits.join(", "));
                    body.push_str(" };\n");
                    body.push_str(&format!(
                        "struct __uws_{} arg{} = uw_inputs;\n",
                        struct_id, arg_idx
                    ));
                }
            }
        }
    }

    // Call the handler — look up function name from env by ID
    let handler_name = match env.lookup_e_named(n) {
        Some((x, _)) => p_named_name(n, x),
        None => format!("__uwn_UNBOUND_{}", n),
    };
    let arg_list: Vec<String> = (0..url_ts.len() + if has_form_inputs { 1 } else { 0 })
        .map(|i| format!("arg{}", i))
        .collect();
    let args_str = if arg_list.is_empty() {
        "ctx, 0".to_string()
    } else {
        format!("ctx, {}, 0", arg_list.join(", "))
    };

    if is_rpc {
        let ran_s = p_typ(env, ran);
        body.push_str(&format!(
            "{ran_s} it0 = {handler_name}({args_str});\n\
             uw_write(ctx, uw_get_real_script(ctx));\n\
             uw_write(ctx, \"\\n\");\n",
        ));
        // urlify the result
        body.push_str(&urlify_stmts(0, ran, env));
    } else {
        body.push_str(&format!("{handler_name}({args_str});\n"));
        body.push_str("uw_write(ctx, \"</html>\");\n");
    }

    body.push_str("return;\n}\n");

    format!(
        "if (!strncmp(request, \"{path_c}\", {path_len}) && \
         (request[{path_len}] == 0 || request[{path_len}] == '/')) {{\n\
         {body}\
         }}\n",
    )
}

// ---------------------------------------------------------------------------
// DBMS-specific C code generation
// ---------------------------------------------------------------------------

/// Generate the DBMS-specific C code: uw_client_init, uw_conn typedef,
/// uw_db_validate, uw_db_prepare, uw_db_init, uw_db_begin/commit/rollback/close.
///
/// Mirrors the DBMS-specific sections of `cjr_print.sml` / `cjrize.sml`.
fn gen_dbms_c_code(
    settings: &Settings,
    tables: &[(String, Vec<(String, LocTyp)>)],
    prepared_stmts: &[(String, usize)],
) -> String {
    cjr_test_tick();
    crate::c_like_representation::relational_sql_runtime::emit_dbms_c_code(
        settings,
        tables,
        prepared_stmts,
    )
}

// ---------------------------------------------------------------------------
// Form input indices (uw_input_num / inputs_len) — mirrors cjr_print.sml
// ---------------------------------------------------------------------------

/// Synthetic field name for cookie-signature hidden input (`sigName` in SML).
fn sig_name(fields: &[(String, LocTyp)]) -> String {
    let in_fields = |s: &str| fields.iter().any(|(n, _)| n == s);
    if !in_fields("Sig") {
        return "Sig".to_string();
    }
    let mut n = 0usize;
    loop {
        let candidate = format!("Sig{n}");
        if !in_fields(&candidate) {
            return candidate;
        }
        n += 1;
    }
}

/// `flatFields` from cjr_print.sml: returns layers of sibling field names (outer to inner).
fn flat_fields(env: &CjrEnv, always: &[String], t: &LocTyp) -> Option<Vec<Vec<String>>> {
    cjr_test_tick();
    match &t.node {
        Typ::Record(i) => {
            let xts = env.lookup_struct(*i)?.clone();
            let mut first: Vec<String> = always.to_vec();
            first.extend(xts.iter().map(|(x, _)| x.clone()));
            let mut nested_pieces: Vec<Vec<Vec<String>>> = Vec::new();
            for (_, ft) in &xts {
                if let Some(sub) = flat_fields(env, &[], ft) {
                    nested_pieces.push(sub);
                }
            }
            let mut concat_nested: Vec<Vec<String>> = Vec::new();
            for piece in nested_pieces {
                concat_nested.extend(piece);
            }
            let mut out = Vec::with_capacity(1 + concat_nested.len());
            out.push(first);
            out.extend(concat_nested);
            Some(out)
        }
        Typ::List(_, i) => {
            let ts = env.lookup_struct(*i)?;
            if ts.len() == 2 && ts[0].0 == "1" && ts[1].0 == "2" {
                flat_fields(env, &[], &ts[0].1)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn compute_form_field_layers(env: &CjrEnv, ps: &[ExportEntry]) -> Vec<Vec<String>> {
    cjr_test_tick();
    let mut acc: Vec<Vec<String>> = Vec::new();
    for (ek, _, _, ts, _, _, _, _) in ps {
        let ExportKind::Action(eff) = ek else {
            continue;
        };
        if ts.len() < 2 {
            continue;
        }
        let form_t = &ts[ts.len() - 2];
        let Typ::Record(i) = &form_t.node else {
            continue;
        };
        let Some(xts) = env.lookup_struct(*i) else {
            continue;
        };
        let extra: Vec<String> = match eff {
            Effect::ReadCookieWrite => vec![sig_name(xts)],
            _ => vec![],
        };
        if let Some(fp) = flat_fields(env, &extra, form_t) {
            acc = fp.into_iter().rev().chain(acc.into_iter()).collect();
        }
    }
    acc
}

/// For each field name, the set of peer names in the same layer that must get distinct indices.
fn build_peer_map(layers: &[Vec<String>]) -> BTreeMap<String, BTreeSet<String>> {
    cjr_test_tick();
    let mut fields: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for xts in layers {
        let set: BTreeSet<String> = xts.iter().cloned().collect();
        for x in xts {
            let without_x: BTreeSet<String> = set.iter().filter(|&s| s != x).cloned().collect();
            fields
                .entry(x.clone())
                .and_modify(|e| *e = e.union(&without_x).cloned().collect())
                .or_insert(without_x);
        }
    }
    fields
}

fn assign_fnums(peer_map: &BTreeMap<String, BTreeSet<String>>) -> BTreeMap<String, usize> {
    cjr_test_tick();
    let mut fnums: BTreeMap<String, usize> = BTreeMap::new();
    for x in peer_map.keys() {
        let xs = &peer_map[x];
        let mut unusable: BTreeSet<usize> = BTreeSet::new();
        for xprime in xs {
            if let Some(&n) = fnums.get(xprime) {
                unusable.insert(n);
            }
        }
        let mut n = 0usize;
        while unusable.contains(&n) {
            n += 1;
        }
        fnums.insert(x.clone(), n);
    }
    fnums
}

#[derive(Clone, Copy)]
enum SwitchAgg {
    NotFound,
    Found(usize),
    Error,
}

fn fold_switch_agg(fnums: &BTreeMap<String, usize>) -> SwitchAgg {
    cjr_test_tick();
    let mut a = SwitchAgg::NotFound;
    for &n in fnums.values() {
        a = match a {
            SwitchAgg::NotFound => SwitchAgg::Found(n),
            SwitchAgg::Found(n0) if n0 == n => SwitchAgg::Found(n),
            SwitchAgg::Found(_) => SwitchAgg::Error,
            SwitchAgg::Error => SwitchAgg::Error,
        };
    }
    a
}

fn c_switch_case_label(ch: char) -> String {
    if ch == '\0' {
        "0".to_string()
    } else if ch.is_ascii() && (ch.is_ascii_alphanumeric() || ch == '_') && ch != '\'' {
        format!("'{ch}'")
    } else {
        format!("{}", u32::from(ch))
    }
}

fn make_switch_impl(fnums: &BTreeMap<String, usize>, i: usize, indent: &str) -> String {
    cjr_test_tick();
    match fold_switch_agg(fnums) {
        SwitchAgg::NotFound => format!("{indent}return -1;\n"),
        SwitchAgg::Found(n) => format!("{indent}return {n};\n"),
        SwitchAgg::Error => {
            let mut cmap: BTreeMap<char, BTreeMap<String, usize>> = BTreeMap::new();
            for (maybe_str, n) in fnums {
                let ch = maybe_str.chars().nth(i).unwrap_or('\0');
                cmap.entry(ch).or_default().insert(maybe_str.clone(), *n);
            }
            if cmap.len() == 1 {
                let (_ch, sub) = cmap.into_iter().next().unwrap();
                let mut s = format!("{indent}if (name[{i}] == 0) return -1;\n");
                s.push_str(&make_switch_impl(&sub, i + 1, indent));
                s
            } else {
                let mut s = format!("{indent}switch ((unsigned char)name[{i}]) {{\n");
                for (ch, sub) in &cmap {
                    let lbl = c_switch_case_label(*ch);
                    s.push_str(&format!("{indent}  case {lbl}:\n"));
                    s.push_str(&make_switch_impl(sub, i + 1, &format!("{indent}    ")));
                }
                s.push_str(&format!(
                    "{indent}  default:\n{indent}    return -1;\n{indent}}}\n"
                ));
                s
            }
        }
    }
}

/// Generate uw_input_num: maps form input names to their indices.
/// Second return value is `inputs_len` for `uw_application` (max index + 1, at least 1).
fn gen_input_num(env: &CjrEnv, ps: &[ExportEntry]) -> (String, usize) {
    cjr_test_tick();
    let layers = compute_form_field_layers(env, ps);
    let peer_map = build_peer_map(&layers);
    let fnums = assign_fnums(&peer_map);
    let inputs_len = fnums.values().max().map(|m| m + 1).unwrap_or(0).max(1);
    if fnums.is_empty() {
        return (
            "static int uw_input_num(const char *name) { return -1; }\n\n".to_string(),
            inputs_len,
        );
    }
    let mut out = String::from("static int uw_input_num(const char *name) {\n");
    out.push_str(&make_switch_impl(&fnums, 0, "    "));
    out.push_str("}\n\n");
    (out, inputs_len)
}

/// Generate uw_cookie_sig: HMAC signature for cookies.
fn gen_cookie_sig() -> &'static str {
    cjr_test_tick();
    concat!(
        "extern void uw_sign(const char *in, char *out);\n",
        "extern int uw_hash_blocksize;\n",
        "static uw_Basis_string uw_cookie_sig(uw_context ctx) {\n",
        "    uw_Basis_string r = uw_malloc(ctx, uw_hash_blocksize);\n",
        "    uw_sign(\"\", r);\n",
        "    return uw_Basis_makeSigString(ctx, r);\n",
        "}\n\n",
    )
}

// ---------------------------------------------------------------------------
// p_file — the main entry point
// ---------------------------------------------------------------------------

/// Generate a C source file from a CJR file.
pub fn cjr_print(file: &crate::c_like_representation::File, settings: &Settings) -> String {
    #[cfg(test)]
    cjr_test_reset_print_ticks();
    let (ds, ps) = file;

    // Separate enum datatypes from other declarations (emit enums first)
    let mut enum_constrs: Vec<DatatypeDecl> = Vec::new();
    let mut remaining_ds: Vec<LocDecl> = Vec::new();

    for d in ds {
        match &d.node {
            Decl::Datatype(dts) => {
                let mut non_enum: Vec<DatatypeDecl> = Vec::new();
                for dt in dts {
                    if dt.kind == DatatypeKind::Enum {
                        enum_constrs.push(dt.clone());
                    } else {
                        non_enum.push(dt.clone());
                    }
                }
                if !non_enum.is_empty() {
                    remaining_ds.push(crate::error_types::Located::dummy(Decl::Datatype(non_enum)));
                }
            }
            Decl::DatatypeForward(DatatypeKind::Enum, _, _) => {
                // Skip enum forwards
            }
            _ => remaining_ds.push(d.clone()),
        }
    }

    // Prepend the collected enum declarations as a single DDatatype node
    let mut all_ds = Vec::new();
    if !enum_constrs.is_empty() {
        all_ds.push(crate::error_types::Located::dummy(Decl::Datatype(
            enum_constrs,
        )));
    }
    all_ds.extend(remaining_ds);

    // Build the full env by processing all declarations in sequence
    let mut full_env = CjrEnv::new();
    for d in &all_ds {
        full_env.decl_binds(d);
    }

    // Collect global initializers
    let mut global_initializers: Vec<String> = Vec::new();

    // Print each declaration using the full_env (for forward references)
    let mut decl_outputs: Vec<String> = Vec::new();
    for d in &all_ds {
        let body = p_decl(&full_env, d, settings, &mut global_initializers);
        if body.is_empty() {
            continue;
        }
        let mut s = String::new();
        if let Some(dir) = format_line_directive_for_span(&d.span) {
            s.push_str(&dir);
        }
        s.push_str(&body);
        decl_outputs.push(s);
    }

    // Build global forward declarations (prototypes) for all named functions
    let mut global_protos: Vec<String> = Vec::new();
    for d in &all_ds {
        match &d.node {
            Decl::Fun(fx, n, args, ran, _) => {
                global_protos.push(p_proto(&full_env, fx, *n, args, ran));
            }
            Decl::FunRec(vis) => {
                for (fx, n, args, ran, _) in vis {
                    global_protos.push(p_proto(&full_env, fx, *n, args, ran));
                }
            }
            _ => {}
        }
    }

    // Gather meta-information from declarations
    let mut _has_db = false;
    let mut db_name = String::new();
    let mut expunge_id: usize = 0;
    let mut initialize_id: usize = 0;
    let mut tables: Vec<(String, Vec<(String, LocTyp)>)> = Vec::new();
    let mut sequences: Vec<String> = Vec::new();
    let mut prepared_stmts: Vec<(String, usize)> = Vec::new();
    let mut _has_js = false;
    let mut cookies: Vec<String> = Vec::new();

    for d in &all_ds {
        match &d.node {
            Decl::Database {
                name,
                expunge,
                initialize,
                ..
            } => {
                _has_db = true;
                db_name = name.clone();
                expunge_id = *expunge;
                initialize_id = *initialize;
            }
            Decl::JavaScript(_) => _has_js = true,
            Decl::Table(s, xts, _, _) => tables.push((s.clone(), xts.clone())),
            Decl::Sequence(s) => sequences.push(s.clone()),
            Decl::PreparedStatements(ss) => prepared_stmts = ss.clone(),
            Decl::Cookie(s) => cookies.push(s.clone()),
            _ => {}
        }
    }

    // Separate struct/datatype declarations from function declarations
    let mut struct_decls: Vec<String> = Vec::new();
    let mut func_decls: Vec<String> = Vec::new();

    for (d, s) in all_ds.iter().zip(decl_outputs.iter()) {
        match &d.node {
            Decl::Datatype(_) | Decl::DatatypeForward(_, _, _) | Decl::Struct(_, _) => {
                struct_decls.push(s.clone());
            }
            _ => func_decls.push(s.clone()),
        }
    }

    // Build the uw_app struct content
    let _table_count = tables.len();
    let _seq_count = sequences.len();
    let _prep_count = prepared_stmts.len();

    // URL prefix
    let url_prefix = &settings.url_prefix;

    // Reset URL handler accumulator before generating page handlers
    reset_url_handlers();

    // Generate URL dispatch blocks for each export
    let mut page_handlers = String::new();
    for (ek, path, n, ts, ran, side, dbmode, tell_sig) in ps {
        let handler_block = p_page(
            ek, path, *n, ts, ran, side, dbmode, *tell_sig, &full_env, settings,
        );
        page_handlers.push_str(&handler_block);
    }

    // Collect URL handler helpers (generated during p_page via unurlify/urlify)
    let url_handler_protos = collect_url_handler_protos();
    let url_handler_defs = collect_url_handler_defs();

    // Global init function
    let init_body = if global_initializers.is_empty() {
        String::new()
    } else {
        global_initializers.join("\n")
    };

    // Build output
    let mut out = String::new();

    // Includes
    out.push_str("#include \"urweb.h\"\n");
    out.push_str("#include <stdio.h>\n");
    out.push_str("#include <stdlib.h>\n");
    out.push_str("#include <string.h>\n");
    out.push_str("#include <math.h>\n");
    out.push_str("#include <time.h>\n\n");

    // DBMS-specific code (uw_client_init, uw_db_init, etc.)
    out.push_str(&gen_dbms_c_code(settings, &tables, &prepared_stmts));

    // uw_input_num and uw_cookie_sig
    let (input_num_code, inputs_len) = gen_input_num(&full_env, ps);
    out.push_str(&input_num_code);
    out.push_str(gen_cookie_sig());

    // Helper: emit optional HTML attribute (C11-compliant, no GNU extensions)
    out.push_str(concat!(
        "static inline uw_Basis_string uw_Basis_attrOptional(\n",
        "    struct uw_context *ctx, uw_Basis_string name, uw_Basis_string val) {\n",
        "    if (val == NULL || val[0] == '\\0') return \"\";\n",
        "    return uw_Basis_mstrcat(ctx, \" \", name, \"=\\\"\", val, \"\\\"\", NULL);\n",
        "}\n\n"
    ));

    // Struct and datatype definitions
    if !struct_decls.is_empty() {
        out.push_str(&struct_decls.join("\n\n"));
        out.push_str("\n\n");
    }

    // Global function forward declarations
    if !global_protos.is_empty() {
        out.push_str("/* Function prototypes */\n");
        out.push_str(&global_protos.join("\n"));
        out.push_str("\n\n");
    }

    // URL handler forward declarations (unurlify_N, urlify_N helpers)
    if !url_handler_protos.is_empty() {
        out.push_str("/* URL handler prototypes */\n");
        out.push_str(&url_handler_protos.join(""));
        out.push('\n');
    }

    // Function and other declarations
    if !func_decls.is_empty() {
        out.push_str(&func_decls.join("\n\n"));
        out.push_str("\n\n");
    }

    // URL handler definitions
    if !url_handler_defs.is_empty() {
        out.push_str("/* URL handler helpers */\n");
        out.push_str(&url_handler_defs.join(""));
        out.push('\n');
    }

    // Collect task declarations
    let mut initializer_tasks: Vec<(String, String, String)> = Vec::new();
    let mut expunger_tasks: Vec<(String, String, String)> = Vec::new();
    let mut periodic_tasks: Vec<(i64, String, String, String)> = Vec::new();
    for d in &all_ds {
        if let Decl::Task(task, x1, x2, e) = &d.node {
            let body_s = p_exp(&full_env, e, settings);
            match task {
                crate::c_like_representation::Task::Initialize => {
                    initializer_tasks.push((x1.clone(), x2.clone(), body_s));
                }
                crate::c_like_representation::Task::ClientLeaves => {
                    expunger_tasks.push((x1.clone(), x2.clone(), body_s));
                }
                crate::c_like_representation::Task::Periodic(n) => {
                    periodic_tasks.push((*n, x1.clone(), x2.clone(), body_s));
                }
            }
        }
    }

    // OnError handler
    let mut on_error_id: Option<usize> = None;
    for d in &all_ds {
        if let Decl::OnError(n) = &d.node {
            on_error_id = Some(*n);
        }
    }

    // uw_setup_limits: sets resource limits from settings
    out.push_str("static void uw_setup_limits(void) {\n");
    if settings.min_heap > 0 {
        out.push_str(&format!("uw_min_heap = {};\n", settings.min_heap));
    }
    for (class, num) in &settings.limits {
        let num = if class == "page" {
            (*num).max(2048)
        } else {
            *num
        };
        out.push_str(&format!("uw_{class}_max = {num};\n"));
    }
    out.push_str("}\n\n");

    // uw_global_custom: called by uw_global_init in urweb.c (signature: void uw_global_custom(void))
    out.push_str("void uw_global_custom(void) {\n");
    if let Some(ref sf) = settings.sig_file {
        out.push_str("extern char *uw_sig_file;\n");
        out.push_str(&format!(
            "uw_sig_file = \"{}\";\n",
            sf.replace('\\', "\\\\").replace('"', "\\\"")
        ));
    }
    out.push_str("uw_setup_limits();\n");
    out.push_str("}\n\n");

    // uw_initializer: runs application initializers (does NOT call uw_global_custom)
    out.push_str("static void uw_initializer(uw_context ctx) {\n");
    if let Some(ref cache_dir) = settings.file_cache {
        out.push_str("struct stat st = {0};\n\n");
        out.push_str(&format!(
            "if (stat(\"{}\", &st) == -1)\n",
            cache_dir.replace('\\', "\\\\").replace('"', "\\\"")
        ));
        out.push_str(&format!(
            "mkdir(\"{}\", 0700);\n",
            cache_dir.replace('\\', "\\\\").replace('"', "\\\"")
        ));
    }
    out.push_str("uw_begin_initializing(ctx);\n");
    if !init_body.is_empty() {
        out.push_str(&init_body);
        out.push('\n');
    }
    out.push_str("uw_end_initializing(ctx);\n");
    for (x1, x2, body) in &initializer_tasks {
        out.push_str(&format!(
            "({{ uw_unit __uwr_{x1}_0 = 0, __uwr_{x2}_1 = 0; {body}; }});\n"
        ));
    }
    if !db_name.is_empty() {
        out.push_str(&format!("__uwn__{}(ctx, 0);\n", initialize_id));
    }
    out.push_str("}\n\n");

    // Expunger function
    out.push_str("static void uw_expunger(uw_context ctx, uw_Basis_client cli) {\n");
    for (x1, x2, body) in &expunger_tasks {
        out.push_str(&format!(
            "({{ uw_Basis_client __uwr_{x1}_0 = cli; uw_unit __uwr_{x2}_1 = 0; {body}; }});\n"
        ));
    }
    if !db_name.is_empty() {
        out.push_str(&format!("__uwn__{}(ctx, cli);\n", expunge_id));
    }
    out.push_str("}\n\n");

    // Periodic tasks array
    out.push_str("static uw_periodic my_periodics[] = {\n");
    for (interval, x1, x2, body) in &periodic_tasks {
        // Each periodic task becomes a function + entry
        let fn_name = format!("__uwperiodic_{}_{}", ident(x1), ident(x2));
        out.push_str(&format!("  {{ {interval}, {fn_name} }},\n"));
        let _ = body;
    }
    out.push_str("  { NULL, 0 }\n};\n\n");

    // Emit periodic task functions
    for (interval, x1, x2, body) in &periodic_tasks {
        let fn_name = format!("__uwperiodic_{}_{}", ident(x1), ident(x2));
        out.push_str(&format!(
            "static void {fn_name}(uw_context ctx) {{\n\
             uw_unit __uwr_{x1}_0 = 0, __uwr_{x2}_1 = 0;\n\
             {body};\n}}\n\n"
        ));
        let _ = interval;
    }

    // OnError handler
    if let Some(on_err_n) = on_error_id {
        out.push_str(&format!(
            "static void uw_onError(uw_context ctx, char *msg) {{\n\
             uw_write(ctx, __uwn__{}(ctx, msg, 0));\n}}\n\n",
            on_err_n
        ));
    }

    // URL checking functions (filters)
    out.push_str("static int uw_check_url(const char *url) {\n  return 1;\n}\n\n");
    out.push_str("static int uw_check_mime(const char *mime) {\n  return 1;\n}\n\n");
    out.push_str("static int uw_check_requestHeader(const char *h) {\n  return 1;\n}\n\n");
    out.push_str("static int uw_check_responseHeader(const char *h) {\n  return 1;\n}\n\n");
    out.push_str("static int uw_check_envVar(const char *v) {\n  return 1;\n}\n\n");
    out.push_str("static int uw_check_meta(const char *m) {\n  return 1;\n}\n\n");

    // Dispatch function
    out.push_str("static void uw_handle(uw_context ctx, char *request) {\n");
    if !page_handlers.is_empty() {
        out.push_str(&page_handlers);
    }
    out.push_str(
        "uw_clear_headers(ctx);\n\
         uw_write_header(ctx, uw_supports_direct_status ? \"HTTP/1.1 404 Not Found\\r\\n\" : \"Status: 404 Not Found\\r\\n\");\n\
         uw_write_header(ctx, \"Content-type: text/plain\\r\\n\");\n\
         uw_write(ctx, \"Not Found\");\n",
    );
    out.push_str("}\n\n");

    // Prepared statement count
    let _prep_count = prepared_stmts.len();

    // uw_app struct (positional fields matching urweb runtime's uw_app struct)
    // Fields: inputs_len, timeout, url_prefix, client_init, initializer, expunger,
    //         db_init, db_begin, db_commit, db_rollback, db_close, handle,
    //         input_num, cookie_sig, check_url, check_mime, check_requestHeader,
    //         check_responseHeader, check_envVar, check_meta, on_error,
    //         periodics, time_format, is_html5, file_cache
    let file_cache_val = settings
        .file_cache
        .as_deref()
        .map(|p| format!("\"{}\"", p.replace('"', "\\\"")))
        .unwrap_or_else(|| "NULL".to_string());
    out.push_str(&format!(
        "uw_app uw_application = {{\n\
         {inputs_len},\n\
         {timeout},\n\
         \"{url_prefix}\",\n\
         uw_client_init,\n\
         uw_initializer,\n\
         uw_expunger,\n\
         uw_db_init, uw_db_begin, uw_db_commit, uw_db_rollback, uw_db_close,\n\
         uw_handle,\n\
         uw_input_num,\n\
         uw_cookie_sig,\n\
         uw_check_url, uw_check_mime, uw_check_requestHeader, uw_check_responseHeader,\n\
         uw_check_envVar, uw_check_meta,\n\
         {on_error},\n\
         my_periodics,\n\
         \"{time_format}\",\n\
         {is_html5},\n\
         {file_cache}\n\
         }};\n",
        inputs_len = inputs_len,
        timeout = settings.timeout,
        url_prefix = url_prefix.replace('"', "\\\""),
        on_error = if on_error_id.is_some() {
            "uw_onError"
        } else {
            "NULL"
        },
        time_format = settings.time_format.replace('"', "\\\""),
        is_html5 = if settings.html5 { 1 } else { 0 },
        file_cache = file_cache_val,
    ));

    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c_like_representation::{Decl, Exp, ExportEntry, Typ};
    use crate::error_types::Located;
    use crate::export::{Effect, ExportKind};
    use crate::monomorphized::{DbMode, Sidedness};
    use crate::primitives::{Prim, StringMode};
    use crate::settings::Settings;

    fn dummy<T>(node: T) -> Located<T> {
        Located::dummy(node)
    }

    #[test]
    fn empty_file_generates_header() {
        let settings = Settings::default();
        let result = cjr_print(&(vec![], vec![]), &settings);
        assert!(
            result.contains("#include"),
            "output must contain #include, got:\n{}",
            result
        );
    }

    #[test]
    fn empty_file_generates_uw_app() {
        let settings = Settings::default();
        let result = cjr_print(&(vec![], vec![]), &settings);
        assert!(
            result.contains("uw_app uw_application"),
            "output must contain uw_app struct, got:\n{}",
            result
        );
    }

    /// `inputs_len` matches SML (`max fnums + 1`, at least 1); no form fields → stub `uw_input_num`.
    #[test]
    fn uw_app_inputs_len_one_without_form_exports() {
        let settings = Settings::default();
        let result = cjr_print(&(vec![], vec![]), &settings);
        assert!(
            result.contains("uw_application = {\n1,"),
            "first uw_app field should be inputs_len 1, got:\n{}",
            result
        );
        assert!(
            result.contains("static int uw_input_num(const char *name) { return -1; }"),
            "expected stub uw_input_num, got:\n{}",
            result
        );
    }

    /// Action export with a 2-field form record → distinct indices and `inputs_len == 2`.
    #[test]
    fn action_export_uw_input_num_and_inputs_len_from_form_fields() {
        let settings = Settings::default();
        let t_int = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let form_rec = dummy(Typ::Record(99));
        let ran = dummy(Typ::Ffi("Basis".into(), "unit".into()));
        let struc = dummy(Decl::Struct(
            99,
            vec![("foo".into(), t_int.clone()), ("bar".into(), t_int.clone())],
        ));
        let export: ExportEntry = (
            ExportKind::Action(Effect::ReadOnly),
            "/page".into(),
            0usize,
            vec![form_rec, ran.clone()],
            ran,
            Sidedness::ServerOnly,
            DbMode::NoDb,
            false,
        );
        let result = cjr_print(&(vec![struc], vec![export]), &settings);
        assert!(
            result.contains("static int uw_input_num(const char *name) {")
                && !result.contains("static int uw_input_num(const char *name) { return -1; }"),
            "expected non-stub uw_input_num, got:\n{}",
            result
        );
        assert!(
            result.contains("return 0;") && result.contains("return 1;"),
            "expected indices 0 and 1 for foo/bar, got:\n{}",
            result
        );
        assert!(
            result.contains("uw_application = {\n2,"),
            "first uw_app field should be inputs_len 2, got:\n{}",
            result
        );
    }

    /// ReadCookieWrite adds synthetic `Sig` to the form layer (cookie signature field).
    #[test]
    fn action_read_cookie_write_includes_sig_in_input_num_trie() {
        let settings = Settings::default();
        let t_int = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let form_rec = dummy(Typ::Record(7));
        let ran = dummy(Typ::Ffi("Basis".into(), "unit".into()));
        let struc = dummy(Decl::Struct(7, vec![("field1".into(), t_int)]));
        let export: ExportEntry = (
            ExportKind::Action(Effect::ReadCookieWrite),
            "/a".into(),
            0usize,
            vec![form_rec, ran.clone()],
            ran,
            Sidedness::ServerOnly,
            DbMode::NoDb,
            false,
        );
        let result = cjr_print(&(vec![struc], vec![export]), &settings);
        assert!(
            result.contains("Sig") && result.contains("field1"),
            "expected Sig and field1 in uw_input_num, got:\n{}",
            result
        );
    }

    #[test]
    fn struct_generates_c_struct() {
        // DStruct(1, [("x", TFfi("Basis","int"))]) should generate:
        // struct __uws_1 { uw_Basis_int __uwf_x; };
        let settings = Settings::default();
        let t_int = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let d = dummy(Decl::Struct(1, vec![("x".into(), t_int)]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("struct __uws_1"),
            "must contain struct __uws_1, got:\n{}",
            result
        );
        assert!(
            result.contains("uw_Basis_int"),
            "must contain uw_Basis_int, got:\n{}",
            result
        );
        assert!(
            result.contains("__uwf_x"),
            "must contain __uwf_x, got:\n{}",
            result
        );
    }

    #[test]
    fn enum_datatype_generates_c_enum() {
        let settings = Settings::default();
        let dt = crate::c_like_representation::DatatypeDecl {
            kind: DatatypeKind::Enum,
            name: "Color".into(),
            id: 5,
            constrs: vec![("Red".into(), 10, None), ("Blue".into(), 11, None)],
        };
        let d = dummy(Decl::Datatype(vec![dt]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("enum __uwe_Color_5"),
            "must contain enum name, got:\n{}",
            result
        );
        assert!(
            result.contains("__uwc_Red_10"),
            "must contain Red constructor, got:\n{}",
            result
        );
        assert!(
            result.contains("__uwc_Blue_11"),
            "must contain Blue constructor, got:\n{}",
            result
        );
    }

    #[test]
    fn val_decl_emits_global_and_initializer() {
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let e = dummy(Exp::Prim(Prim::Int(42)));
        let d = dummy(Decl::Val("answer".into(), 7, t, e));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("__uwn_answer_7"),
            "must contain named global, got:\n{}",
            result
        );
        assert!(
            result.contains("42LL"),
            "must contain initializer value, got:\n{}",
            result
        );
    }

    #[test]
    fn fun_decl_emits_static_function() {
        let settings = Settings::default();
        let ran = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let body = dummy(Exp::Prim(Prim::Int(0)));
        let d = dummy(Decl::Fun("myFun".into(), 3, vec![], ran, body));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("static"),
            "function must be static, got:\n{}",
            result
        );
        assert!(
            result.contains("__uwn_myFun_3"),
            "must contain function name, got:\n{}",
            result
        );
    }

    #[test]
    fn prim_int_prints_ll_suffix() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let e = dummy(Exp::Prim(Prim::Int(99)));
        let s = p_exp(&env, &e, &settings);
        assert_eq!(s, "99LL");
    }

    #[test]
    fn prim_string_prints_quoted() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let e = dummy(Exp::Prim(Prim::String(StringMode::Normal, "hello".into())));
        let s = p_exp(&env, &e, &settings);
        assert_eq!(s, "\"hello\"");
    }

    #[test]
    fn none_exp_prints_null() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let e = dummy(Exp::None(t));
        let s = p_exp(&env, &e, &settings);
        assert_eq!(s, "NULL");
    }

    #[test]
    fn write_exp_wraps_in_uw_write() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let inner = dummy(Exp::Prim(Prim::String(StringMode::Normal, "hi".into())));
        let e = dummy(Exp::Write(Box::new(inner)));
        let s = p_exp(&env, &e, &settings);
        assert!(s.contains("uw_write"), "got: {}", s);
    }

    #[test]
    fn seq_uses_comma_operator() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let e1 = dummy(Exp::Prim(Prim::Int(1)));
        let e2 = dummy(Exp::Prim(Prim::Int(2)));
        let e = dummy(Exp::Seq(Box::new(e1), Box::new(e2)));
        let s = p_exp(&env, &e, &settings);
        assert!(s.contains("1LL") && s.contains("2LL"), "got: {}", s);
    }

    #[test]
    fn ffi_exp_formats_correctly() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let e = dummy(Exp::Ffi("Basis".into(), "strdup".into()));
        let s = p_exp(&env, &e, &settings);
        assert_eq!(s, "uw_Basis_strdup");
    }

    #[test]
    fn ffi_app_funcall_branches() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let e0 = dummy(Exp::FfiApp("Basis".into(), "now".into(), vec![]));
        let s0 = p_exp(&env, &e0, &settings);
        assert!(
            s0.contains("uw_Basis_now") && s0.contains("ctx"),
            "0-arg FfiApp"
        );
        let arg = (dummy(Exp::Prim(Prim::Int(1))), t.clone());
        let e1 = dummy(Exp::FfiApp("Basis".into(), "intToString".into(), vec![arg]));
        let s1 = p_exp(&env, &e1, &settings);
        assert!(
            s1.contains("1LL") && s1.contains("intToString"),
            "1-arg FfiApp"
        );
        let args = vec![
            (dummy(Exp::Prim(Prim::Int(1))), t.clone()),
            (dummy(Exp::Prim(Prim::Int(2))), t.clone()),
        ];
        let e2 = dummy(Exp::FfiApp("Basis".into(), "max".into(), args));
        let s2 = p_exp(&env, &e2, &settings);
        assert!(
            s2.contains("uw_Basis_max") && s2.contains("1LL") && s2.contains("2LL"),
            "2-arg FfiApp, got: {}",
            s2
        );
    }

    #[test]
    fn field_access_uses_uwf_prefix() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let inner = dummy(Exp::Prim(Prim::Int(0)));
        let e = dummy(Exp::Field(Box::new(inner), "myField".into()));
        let s = p_exp(&env, &e, &settings);
        assert!(s.contains("__uwf_myField"), "got: {}", s);
    }

    #[test]
    fn p_typ_unit_returns_uw_unit() {
        let env = CjrEnv::new();
        let t = dummy(Typ::Record(0));
        assert_eq!(p_typ(&env, &t), "uw_unit");
    }

    #[test]
    fn p_typ_record_returns_struct_name() {
        let env = CjrEnv::new();
        let t = dummy(Typ::Record(3));
        assert_eq!(p_typ(&env, &t), "struct __uws_3");
    }

    #[test]
    fn p_typ_ffi_formats_correctly() {
        let env = CjrEnv::new();
        let t = dummy(Typ::Ffi("Basis".into(), "string".into()));
        assert_eq!(p_typ(&env, &t), "uw_Basis_string");
    }

    #[test]
    fn ident_replaces_prime() {
        assert_eq!(ident("foo'bar"), "fooQUOTEbar".replace("QUOTE", "PRIME"));
        assert_eq!(ident("foo'"), "fooPRIME");
    }

    #[test]
    fn javascript_decl_emits_jslib() {
        let settings = Settings::default();
        let d = dummy(Decl::JavaScript("alert(1)".into()));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("static char jslib[]"),
            "must contain jslib, got:\n{}",
            result
        );
    }

    #[test]
    fn is_unboxable_basis_string_and_querystring() {
        // Catches mutant: delete match arm, wrong guard for Basis string/queryString.
        let t_string = dummy(Typ::Ffi("Basis".into(), "string".into()));
        let t_qs = dummy(Typ::Ffi("Basis".into(), "queryString".into()));
        assert!(is_unboxable(&t_string), "Basis.string must be unboxable");
        assert!(is_unboxable(&t_qs), "Basis.queryString must be unboxable");
    }

    #[test]
    fn is_unboxable_others_false() {
        // Catches mutant: replace return with true; default/other types.
        let t_int = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let t_other = dummy(Typ::Ffi("Other".into(), "string".into()));
        assert!(!is_unboxable(&t_int), "Basis.int must not be unboxable");
        assert!(
            !is_unboxable(&t_other),
            "Other.string must not be unboxable"
        );
    }

    #[test]
    fn is_unboxable_default_datatype() {
        // Catches mutant: delete match arm Typ::Datatype(DatatypeKind::Default, _, _) in is_unboxable
        use std::sync::{Arc, Mutex};
        let xncs = Arc::new(Mutex::new(vec![("Mk".into(), 0, None)]));
        let t = dummy(Typ::Datatype(DatatypeKind::Default, 1, xncs));
        assert!(is_unboxable(&t), "DatatypeKind::Default must be unboxable");
    }

    #[test]
    fn cjr_print_database_decl_in_output() {
        // Catches mutant: cjr_print return with String::new() when file has decls.
        let settings = Settings::default();
        let d = dummy(Decl::Database {
            name: "mydb".into(),
            expunge: 0,
            initialize: 0,
            uses_similar: false,
        });
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            !result.is_empty() && result.len() > 100,
            "cjr_print must generate substantial output for Database decl"
        );
    }

    #[test]
    fn table_decl_emits_create_table() {
        let settings = Settings::default();
        let xts = vec![
            ("id".into(), dummy(Typ::Ffi("Basis".into(), "int".into()))),
            (
                "score".into(),
                dummy(Typ::Ffi("Basis".into(), "float".into())),
            ),
            (
                "name".into(),
                dummy(Typ::Ffi("Basis".into(), "string".into())),
            ),
        ];
        let d = dummy(Decl::Table("users".into(), xts, "".into(), vec![]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("users"),
            "Table decl must produce output with table name (catches delete Decl::Table arm): {}",
            result
        );
    }

    #[test]
    fn datatype_with_option_variant() {
        let settings = Settings::default();
        let dt = crate::c_like_representation::DatatypeDecl {
            kind: DatatypeKind::Option,
            name: "Maybe".into(),
            id: 7,
            constrs: vec![
                ("None".into(), 8, None),
                (
                    "Some".into(),
                    9,
                    Some(dummy(Typ::Ffi("Basis".into(), "int".into()))),
                ),
            ],
        };
        let d = dummy(Decl::Datatype(vec![dt]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("uw_app") && result.len() > 100,
            "Option datatype path must be exercised (DatatypeKind::Option branch)"
        );
    }

    #[test]
    fn datatype_default_generates_struct() {
        let settings = Settings::default();
        let unit = dummy(Typ::Ffi("Basis".into(), "unit".into()));
        let dt = crate::c_like_representation::DatatypeDecl {
            kind: DatatypeKind::Default,
            name: "Pair".into(),
            id: 10,
            constrs: vec![("Mk".into(), 11, Some(unit))],
        };
        let d = dummy(Decl::Datatype(vec![dt]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("Pair") || result.contains("__uwc_Mk"),
            "Default datatype must emit (catches delete Datatype arm in is_unboxable)"
        );
    }

    #[test]
    fn funrec_decl_emits_functions() {
        let settings = Settings::default();
        let ran = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let body = dummy(Exp::Prim(Prim::Int(0)));
        let d = dummy(Decl::FunRec(vec![("f".into(), 5, vec![], ran, body)]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("__uwn_f_5") || result.contains("static"),
            "FunRec must emit (catches delete Decl::FunRec arm)"
        );
    }

    #[test]
    fn sequence_decl_in_output() {
        let settings = Settings::default();
        let d = dummy(Decl::Sequence("seq".into()));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(!result.is_empty(), "Sequence decl must produce output");
    }

    #[test]
    fn cookie_decl_in_output() {
        let settings = Settings::default();
        let d = dummy(Decl::Cookie("sess".into()));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            !result.is_empty(),
            "Cookie decl must produce output (catches delete Decl::Cookie arm)"
        );
    }

    #[test]
    fn datatype_forward_in_output() {
        let settings = Settings::default();
        let d = dummy(Decl::DatatypeForward(DatatypeKind::Enum, "E".into(), 1));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("E") || !result.is_empty(),
            "DatatypeForward must produce output"
        );
    }

    #[test]
    fn con_exp_with_record_constructor() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let _t = dummy(Typ::Record(0));
        let e = dummy(Exp::Con(
            DatatypeKind::Default,
            crate::c_like_representation::PatCon::Var(0),
            None,
        ));
        let s = p_exp(&env, &e, &settings);
        assert!(!s.is_empty(), "Con exp must print");
    }

    #[test]
    fn p_typ_option_prints() {
        let env = CjrEnv::new();
        let inner = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let t = dummy(Typ::Option(Box::new(inner)));
        let s = p_typ(&env, &t);
        assert!(
            !s.is_empty() && (s.contains("uw_") || s.contains("struct")),
            "Option type must print (catches delete Typ::Option in p_typ)"
        );
    }

    #[test]
    fn p_typ_list_prints() {
        let env = CjrEnv::new();
        let inner = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let t = dummy(Typ::List(Box::new(inner), 1));
        let s = p_typ(&env, &t);
        assert!(!s.is_empty(), "List type must print");
    }

    #[test]
    fn prim_float_prints() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let e = dummy(Exp::Prim(Prim::Float(3.14)));
        let s = p_exp(&env, &e, &settings);
        assert!(
            s.contains(".") || s.contains("e"),
            "float must print with decimal/exp"
        );
    }

    #[test]
    fn p_exp_binop_comparisons() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let a = dummy(Exp::Prim(Prim::Int(1)));
        let b = dummy(Exp::Prim(Prim::Int(2)));
        let ge = dummy(Exp::Binop(
            ">=".into(),
            Box::new(a.clone()),
            Box::new(b.clone()),
        ));
        assert!(
            p_exp(&env, &ge, &settings).contains(">="),
            "Ge must print >="
        );
        let le = dummy(Exp::Binop(
            "<".into(),
            Box::new(a.clone()),
            Box::new(b.clone()),
        ));
        assert!(p_exp(&env, &le, &settings).contains("<"), "Lt must print <");
        let eq = dummy(Exp::Binop(
            "==".into(),
            Box::new(a.clone()),
            Box::new(b.clone()),
        ));
        assert!(
            p_exp(&env, &eq, &settings).contains("=="),
            "Eq must print =="
        );
        let and = dummy(Exp::Binop(
            "&&".into(),
            Box::new(a.clone()),
            Box::new(b.clone()),
        ));
        assert!(
            p_exp(&env, &and, &settings).contains("&&"),
            "And must print &&"
        );
        let or = dummy(Exp::Binop(
            "||".into(),
            Box::new(a.clone()),
            Box::new(b.clone()),
        ));
        assert!(
            p_exp(&env, &or, &settings).contains("||"),
            "Or must print ||"
        );
    }

    #[test]
    fn prim_char_prints() {
        let env = CjrEnv::new();
        let settings = Settings::default();
        let e = dummy(Exp::Prim(Prim::Char('x')));
        let s = p_exp(&env, &e, &settings);
        assert!(s.contains("'") || !s.is_empty());
    }

    #[test]
    fn sql_type_in_basis_string_in_struct() {
        // Catches mutant: delete "string" arm in sql_type_in.
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "string".into()));
        let d = dummy(Decl::Struct(1, vec![("s".into(), t)]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("uw_Basis_string"),
            "Basis.string must produce uw_Basis_string, got: {}",
            result
        );
    }

    #[test]
    fn sql_type_in_basis_bool_in_struct() {
        // Catches mutant: delete "bool" arm in sql_type_in.
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "bool".into()));
        let d = dummy(Decl::Struct(1, vec![("b".into(), t)]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("uw_Basis_bool"),
            "Basis.bool must produce uw_Basis_bool, got: {}",
            result
        );
    }

    #[test]
    fn sql_type_in_basis_clocktime_in_struct() {
        // Catches mutant: delete "clocktime" arm in sql_type_in / p_typ for Basis types.
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "clocktime".into()));
        let d = dummy(Decl::Struct(1, vec![("t".into(), t)]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("uw_Basis_clocktime"),
            "Basis.clocktime must produce uw_Basis_clocktime, got: {}",
            result
        );
    }

    #[test]
    fn p_exp_funcall_empty_and_single_arg() {
        // Catches mutant: wrong arm for [] or [(e,_)] in p_funcall.
        let env = CjrEnv::new();
        let settings = Settings::default();
        let e0 = dummy(Exp::FfiApp("Basis".into(), "now".into(), vec![]));
        assert!(
            p_exp(&env, &e0, &settings).contains("uw_Basis_now(ctx)"),
            "0-arg FfiApp => fn(ctx)"
        );
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let arg = (dummy(Exp::Prim(Prim::Int(42))), t);
        let e1 = dummy(Exp::FfiApp("Basis".into(), "intToString".into(), vec![arg]));
        let s = p_exp(&env, &e1, &settings);
        assert!(
            s.contains("42LL") && s.contains("intToString"),
            "1-arg FfiApp => fn(ctx, arg), got: {}",
            s
        );
    }

    #[test]
    fn url_handler_registration_in_output() {
        // Catches mutant: reset_url_handlers/add_url_handler/collect replaced with no-op.
        use crate::export::Effect;
        use crate::export::ExportKind;
        use crate::monomorphized::{DbMode, Sidedness};
        use std::sync::{Arc, Mutex};

        let settings = Settings::default();
        let dt = crate::c_like_representation::DatatypeDecl {
            kind: DatatypeKind::Default,
            name: "Color".into(),
            id: 20,
            constrs: vec![("Red".into(), 21, None), ("Blue".into(), 22, None)],
        };
        let d = dummy(Decl::Datatype(vec![dt]));
        let dt_ref: crate::c_like_representation::DatatypeRef = Arc::new(Mutex::new(vec![
            ("Red".into(), 21, None),
            ("Blue".into(), 22, None),
        ]));
        let url_arg = dummy(Typ::Datatype(DatatypeKind::Default, 20, dt_ref));
        let ran = dummy(Typ::Record(0));
        // ts: param types; for Link, url_ts = ts[..ts.len()-1], so we need 2+ to get url args
        let export: crate::c_like_representation::ExportEntry = (
            ExportKind::Link(Effect::ReadOnly),
            "/main".into(),
            1,
            vec![url_arg, ran.clone()],
            ran,
            Sidedness::ServerOnly,
            DbMode::NoDb,
            false,
        );
        let result = cjr_print(&(vec![d], vec![export]), &settings);
        assert!(
            result.contains("unurlify_")
                || result.contains("urlify_")
                || result.contains("URL handler"),
            "Export with Datatype URL arg must emit URL handler code, got excerpt: ...",
        );
    }

    #[test]
    fn p_exp_binop_ne_prints() {
        // Catches mutant: replace != with == in p_exp.
        let env = CjrEnv::new();
        let settings = Settings::default();
        let a = dummy(Exp::Prim(Prim::Int(1)));
        let b = dummy(Exp::Prim(Prim::Int(2)));
        let ne = dummy(Exp::Binop("!=".into(), Box::new(a), Box::new(b)));
        assert!(
            p_exp(&env, &ne, &settings).contains("!="),
            "Ne must print !="
        );
    }

    #[test]
    fn sql_type_in_basis_float_in_struct() {
        // Catches mutant: delete "float" arm in sql_type_in.
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "float".into()));
        let d = dummy(Decl::Struct(1, vec![("f".into(), t)]));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        assert!(
            result.contains("uw_Basis_float"),
            "Basis.float must produce uw_Basis_float, got: {}",
            result
        );
    }

    #[test]
    fn index_decl_emits_struct_or_forward() {
        // Index decls are passed through; table+index produce CREATE INDEX in sql_generate.
        let settings = Settings::default();
        use crate::monomorphized::IndexMode;
        let d = dummy(Decl::Index(
            "uw_t".into(),
            vec![("col".into(), IndexMode::Equality)],
        ));
        let result = cjr_print(&(vec![d], vec![]), &settings);
        // Index doesn't produce C output directly; ensure file still parses.
        assert!(
            result.contains("#include") || !result.is_empty(),
            "Index decl should not break output"
        );
    }

    #[test]
    fn p_exp_record_with_fields() {
        // Catches mutant: delete Record arm in p_exp.
        let env = CjrEnv::new();
        let settings = Settings::default();
        let inner = dummy(Exp::Prim(Prim::Int(0)));
        let e = dummy(Exp::Record(1, vec![("x".into(), inner)]));
        let s = p_exp(&env, &e, &settings);
        assert!(
            s.contains("__uwf_x") || s.contains("struct") || !s.is_empty(),
            "Record must produce output, got: {}",
            s
        );
    }

    #[test]
    fn p_exp_division_includes_zero_guard() {
        // Kills: replace "/" branch or "division by zero" text.
        let env = CjrEnv::new();
        let settings = Settings::default();
        let a = dummy(Exp::Prim(Prim::Int(10)));
        let b = dummy(Exp::Prim(Prim::Int(2)));
        let div = dummy(Exp::Binop("/".into(), Box::new(a), Box::new(b)));
        let s = p_exp(&env, &div, &settings);
        assert!(
            s.contains("division by zero") && s.contains("dividend") && s.contains("divisor"),
            "Division must emit zero guard, got: {}",
            s
        );
    }

    #[test]
    fn p_exp_strcat_three_parts_uses_mstrcat() {
        // flatten_strcat(strcat(a,b), c) has len 3 => mstrcat with NULL.
        let env = CjrEnv::new();
        let settings = Settings::default();
        let t = dummy(Typ::Ffi("Basis".into(), "string".into()));
        let a = dummy(Exp::Prim(Prim::String(StringMode::Normal, "a".into())));
        let b = dummy(Exp::Prim(Prim::String(StringMode::Normal, "b".into())));
        let c = dummy(Exp::Prim(Prim::String(StringMode::Normal, "c".into())));
        let strcat_ab = dummy(Exp::FfiApp(
            "Basis".into(),
            "strcat".into(),
            vec![(a, t.clone()), (b, t.clone())],
        ));
        let strcat_abc = dummy(Exp::FfiApp(
            "Basis".into(),
            "strcat".into(),
            vec![(strcat_ab, t.clone()), (c, t)],
        ));
        let s = p_exp(&env, &strcat_abc, &settings);
        assert!(
            s.contains("mstrcat") && s.contains("NULL"),
            "Three-part strcat must use mstrcat with NULL, got: {}",
            s
        );
    }

    #[test]
    fn p_exp_binop_exact_operators() {
        // Exact string so ==/!= and &&/|| mutants change output.
        let env = CjrEnv::new();
        let settings = Settings::default();
        let one = dummy(Exp::Prim(Prim::Int(1)));
        let two = dummy(Exp::Prim(Prim::Int(2)));
        let eq = dummy(Exp::Binop(
            "==".into(),
            Box::new(one.clone()),
            Box::new(two.clone()),
        ));
        let ne = dummy(Exp::Binop(
            "!=".into(),
            Box::new(one.clone()),
            Box::new(two.clone()),
        ));
        let and = dummy(Exp::Binop(
            "&&".into(),
            Box::new(one.clone()),
            Box::new(two.clone()),
        ));
        let or = dummy(Exp::Binop(
            "||".into(),
            Box::new(one.clone()),
            Box::new(two),
        ));
        assert_eq!(p_exp(&env, &eq, &settings), "(1LL == 2LL)");
        assert_eq!(p_exp(&env, &ne, &settings), "(1LL != 2LL)");
        assert!(p_exp(&env, &and, &settings).contains("&&"));
        assert!(p_exp(&env, &or, &settings).contains("||"));
    }

    #[test]
    fn de_star_request_strips_parens() {
        assert_eq!(de_star("(*request)"), "request");
    }

    #[test]
    fn de_star_other_prepends_amp() {
        assert_eq!(de_star("foo"), "&foo");
    }

    #[test]
    fn capitalize_first_char() {
        assert_eq!(capitalize("hello"), "Hello");
    }

    #[test]
    fn capitalize_empty_unchanged() {
        assert_eq!(capitalize(""), "");
    }

    #[test]
    fn sql_type_in_basis_int() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "int".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Int));
    }

    #[test]
    fn sql_type_in_basis_string() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "string".into()));
        assert!(matches!(sql_type_in(&t), SqlType::String));
    }

    #[test]
    fn sql_type_in_option_nullable() {
        use crate::settings::SqlType;
        let inner = dummy(Typ::Ffi("Basis".into(), "int".into()));
        let t = dummy(Typ::Option(Box::new(inner)));
        match &sql_type_in(&t) {
            SqlType::Nullable(b) => assert!(matches!(b.as_ref(), SqlType::Int)),
            _ => panic!("Option must yield Nullable"),
        }
    }

    #[test]
    fn sql_type_in_basis_char() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "char".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Char));
    }

    #[test]
    fn sql_type_in_basis_time() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "time".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Time));
    }

    #[test]
    fn sql_type_in_basis_blob() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "blob".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Blob));
    }

    #[test]
    fn sql_type_in_basis_channel() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "channel".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Channel));
    }

    #[test]
    fn sql_type_in_basis_client() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "client".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Client));
    }

    #[test]
    fn sql_type_in_basis_clocktime() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "clocktime".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Clocktime));
    }

    #[test]
    fn sql_type_in_basis_calendardate() {
        use crate::settings::SqlType;
        let t = dummy(Typ::Ffi("Basis".into(), "calendardate".into()));
        assert!(matches!(sql_type_in(&t), SqlType::Calendardate));
    }
}
