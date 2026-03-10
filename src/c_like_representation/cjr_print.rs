//! C code generator for the CJR intermediate representation.
//!
//! Translates a CJR `File` into a C source string.
//! Mirrors `cjr_print.sml`.

use std::collections::HashMap;

use crate::c_like_representation::{
    DatatypeDecl, Decl, DmlMeta, Exp, LocDecl, LocExp, LocPat, LocTyp, Pat, PatCon, QueryMeta, Typ,
};
use crate::datatype_kind::DatatypeKind;
use crate::settings::{FailureMode, Settings};

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
        self.rels.push((x.to_string(), t));
    }

    pub fn lookup_e_rel(&self, n: usize) -> Option<&(String, LocTyp)> {
        let idx = self.rels.len().checked_sub(n + 1)?;
        self.rels.get(idx)
    }

    pub fn count_e_rels(&self) -> usize {
        self.rels.len()
    }

    pub fn push_e_named(&mut self, x: &str, n: usize, t: LocTyp) {
        self.named.insert(n, (x.to_string(), t));
    }

    pub fn lookup_e_named(&self, n: usize) -> Option<&(String, LocTyp)> {
        self.named.get(&n)
    }

    pub fn push_datatype(
        &mut self,
        x: &str,
        n: usize,
        constrs: &[(String, usize, Option<LocTyp>)],
    ) {
        self.datatypes.insert(n, (x.to_string(), constrs.to_vec()));
        for (cx, cn, ct) in constrs {
            self.constructors.insert(*cn, (cx.clone(), ct.clone(), n));
        }
    }

    pub fn lookup_datatype(
        &self,
        n: usize,
    ) -> Option<&(String, Vec<(String, usize, Option<LocTyp>)>)> {
        self.datatypes.get(&n)
    }

    pub fn lookup_constructor(&self, n: usize) -> Option<&(String, Option<LocTyp>, usize)> {
        self.constructors.get(&n)
    }

    pub fn push_struct(&mut self, n: usize, xts: Vec<(String, LocTyp)>) {
        self.structs.insert(n, xts);
    }

    pub fn lookup_struct(&self, n: usize) -> Option<&Vec<(String, LocTyp)>> {
        self.structs.get(&n)
    }

    /// Update the environment by processing a declaration's bindings.
    pub fn decl_binds(&mut self, d: &LocDecl) {
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
    s.replace('\'', "PRIME")
}

fn p_rel_name(env: &CjrEnv, n: usize) -> String {
    match env.lookup_e_rel(n) {
        Some((x, _)) => {
            let idx = env.count_e_rels().saturating_sub(n + 1);
            format!("__uwr_{}_{}", ident(x), idx)
        }
        None => format!("__uwr_UNBOUND_{}", n),
    }
}

fn p_named_name(n: usize, x: &str) -> String {
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
            let xncs_locked = xncs.lock().unwrap();
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
                        DatatypeKind::Enum => panic!("Enum con has argument"),
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
    match pc {
        PatCon::Var(n) => env.lookup_constructor(*n).and_then(|(_, t, _)| t.clone()),
        PatCon::Ffi { arg, .. } => arg.clone(),
    }
}

// ---------------------------------------------------------------------------
// Pattern binding — generates variable assignments
// ---------------------------------------------------------------------------

fn p_pat_bind(env: &mut CjrEnv, disc: &str, pat: &LocPat) -> String {
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
                DatatypeKind::Enum => panic!("Enum con has argument"),
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
            let mut out = String::from("({\n");
            for (i, (e, t)) in args.iter().enumerate() {
                let ae = p_exp(env, e, settings);
                let at = p_typ(env, t);
                out.push_str(&format!("{} arg{} = {};\n", at, i, ae));
            }
            let arg_list: Vec<String> = (0..args.len()).map(|i| format!("arg{}", i)).collect();
            out.push_str(&fn_name);
            out.push_str("(ctx, ");
            out.push_str(&arg_list.join(", "));
            out.push_str(&extra_s);
            out.push_str(");\n})");
            out
        }
    }
}

// ---------------------------------------------------------------------------
// Expression printing
// ---------------------------------------------------------------------------

pub fn p_exp(env: &CjrEnv, e: &LocExp, settings: &Settings) -> String {
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
            match prepared {
                Some(pq) => format!(
                    "({{\nuw_Basis_int n;\nuw_ensure_transaction(ctx);\n/* nextval prepared id={} query={} */\nn;\n}})",
                    pq.id, pq.query
                ),
                None => format!(
                    "({{\nuw_Basis_int n;\nuw_ensure_transaction(ctx);\n/* nextval {} */\nn;\n}})",
                    seq_s
                ),
            }
        }

        Exp::Setval { seq, count } => {
            let seq_s = p_exp(env, seq, settings);
            let count_s = p_exp(env, count, settings);
            format!(
                "({{\nuw_ensure_transaction(ctx);\n/* setval {} {} */\n0;\n}})",
                seq_s, count_s
            )
        }

        Exp::Uurlify(e1, t, _from_client) => {
            let e_s = p_exp(env, e1, settings);
            let t_s = p_typ(env, t);
            format!(
                "({{\nuw_Basis_string request = uw_maybe_strdup(ctx, {});\n/* TODO: unurlify {} */\n(request ? ({} ){{}} : ({}){{}});\n}})",
                e_s, t_s, t_s, t_s
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Query and DML printing (simplified / TODO stubs)
// ---------------------------------------------------------------------------

fn p_exp_query(env: &CjrEnv, qm: &QueryMeta, settings: &Settings) -> String {
    let state_t = p_typ(env, &qm.state);
    let initial_s = p_exp(env, &qm.initial, settings);
    let query_s = p_exp(env, &qm.query, settings);

    // Build the row struct type name
    let row_struct = format!("struct __uws_{}", qm.rnum);

    // Build the body expression in an extended environment (push r and acc)
    let mut env2 = env.clone();
    let row_t = crate::error_types::Located::dummy(Typ::Record(qm.rnum));
    env2.push_e_rel("r", row_t);
    env2.push_e_rel("acc", qm.state.clone());
    let body_s = p_exp(&env2, &qm.body, settings);

    match &qm.prepared {
        None => format!(
            "(({{\n{state_t} acc = {initial_s};\nuw_ensure_transaction(ctx);\nchar *query = {query_s};\n/* TODO: execute query and iterate rows:\n   for each row: {row_struct} __uwr_r_N; ... acc = {body_s}; */\nacc;\n}}))",
            state_t = state_t,
            initial_s = initial_s,
            query_s = query_s,
            row_struct = row_struct,
            body_s = body_s,
        ),
        Some(pq) => format!(
            "(({{\n{state_t} acc = {initial_s};\nuw_ensure_transaction(ctx);\n/* TODO: execute prepared query id={id} and iterate rows:\n   for each row: {row_struct} __uwr_r_N; ... acc = {body_s}; */\nacc;\n}}))",
            state_t = state_t,
            initial_s = initial_s,
            id = pq.id,
            row_struct = row_struct,
            body_s = body_s,
        ),
    }
}

fn p_exp_dml(env: &CjrEnv, dm: &DmlMeta, settings: &Settings) -> String {
    let dml_s = p_exp(env, &dm.dml, settings);
    let mode_s = match dm.mode {
        FailureMode::Error => "0",
        FailureMode::None => "uw_dup_and_clear_error_message(ctx)",
    };
    match &dm.prepared {
        None => format!(
            "(uw_begin_region(ctx), ({{\nchar *dml = {};\nuw_ensure_transaction(ctx);\n/* TODO: execute DML */\nuw_end_region(ctx);\n{};\n}}))",
            dml_s, mode_s
        ),
        Some(pd) => format!(
            "(uw_begin_region(ctx), ({{\n/* TODO: execute prepared DML id={} */\nuw_ensure_transaction(ctx);\nuw_end_region(ctx);\n{};\n}}))",
            pd.id, mode_s
        ),
    }
}

// ---------------------------------------------------------------------------
// strcat flattening helper
// ---------------------------------------------------------------------------

fn flatten_strcat(e1: &LocExp, e2: &LocExp) -> Vec<LocExp> {
    let mut parts = Vec::new();
    collect_strcat_parts(e1, &mut parts);
    collect_strcat_parts(e2, &mut parts);
    parts
}

fn collect_strcat_parts(e: &LocExp, parts: &mut Vec<LocExp>) {
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
    let mut result = Vec::new();
    let mut cur = t.clone();
    while result.len() < n {
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

fn p_decl(
    env: &CjrEnv,
    d: &LocDecl,
    settings: &Settings,
    global_initializers: &mut Vec<String>,
) -> String {
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
// p_file — the main entry point
// ---------------------------------------------------------------------------

/// Generate a C source file from a CJR file.
pub fn cjr_print(file: &crate::c_like_representation::File, settings: &Settings) -> String {
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
        let s = p_decl(&full_env, d, settings, &mut global_initializers);
        if !s.is_empty() {
            decl_outputs.push(s);
        }
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

    // Export handlers (page/RPC) — emit TODO stubs
    let mut page_handlers = String::new();
    for (_ek, path, n, _ts, _ran, _side, _dbmode, _tell_sig) in ps {
        let handler_name = format!("__uwn_HANDLER_{}", n);
        page_handlers.push_str(&format!(
            "/* TODO: page handler for {} at {} */\n",
            handler_name, path
        ));
    }

    // Global init function
    let init_body = if global_initializers.is_empty() {
        String::new()
    } else {
        global_initializers.join("\n")
    };

    // Build output
    let mut out = String::new();

    // Includes
    out.push_str("#include \"urweb.h\"\n\n");

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

    // Function and other declarations
    if !func_decls.is_empty() {
        out.push_str(&func_decls.join("\n\n"));
        out.push_str("\n\n");
    }

    // Page handlers
    if !page_handlers.is_empty() {
        out.push_str(&page_handlers);
        out.push('\n');
    }

    // Global initializer function
    out.push_str("static void uw_global_custom(uw_context ctx) {\n");
    if !init_body.is_empty() {
        out.push_str(&init_body);
        out.push('\n');
    }
    out.push_str("}\n\n");

    // Dispatch function (simplified)
    out.push_str("static void uw_handle(uw_context ctx, char *request) {\n");
    out.push_str("  /* TODO: URL dispatch */\n");
    out.push_str("  uw_error(ctx, FATAL, \"Unknown page\");\n");
    out.push_str("}\n\n");

    // uw_app struct
    out.push_str("uw_app uw_application = {\n");
    out.push_str(&format!("  .url_prefix = \"{}\",\n", url_prefix));
    out.push_str(&format!(
        "  .db_name = \"{}\",\n",
        db_name.replace('"', "\\\"")
    ));
    out.push_str("  .handle = uw_handle,\n");
    out.push_str("  .global_custom = uw_global_custom,\n");
    out.push_str(&format!("  .expunge = {},\n", expunge_id));
    out.push_str(&format!("  .initialize = {},\n", initialize_id));
    out.push_str("};\n");

    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c_like_representation::{Decl, Exp, Typ};
    use crate::error_types::Located;
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
}
