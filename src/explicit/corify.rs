//! Corify pass: converts the Explicit AST to the Core AST.
//!
//! Flattens module structure, resolves all module projections to globally-unique
//! integer identifiers, and converts FFI references to `(module, name)` pairs.
//!
//! Mirrors `corify.sml`.

#![allow(dead_code)]

use std::collections::HashMap;

use crate::datatype_kind::DatatypeKind;
use crate::error_types::{ErrorReporter, Located, Span};
use crate::export::{Effect, ExportKind};
use crate::settings::{PathKind, Settings};
use crate::{core as core_ir, explicit as expl};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn loc_dummy() -> Span {
    Span::dummy()
}

fn do_restify(settings: &Settings, kind: &PathKind, mods: &[String], s: &str) -> String {
    // Strip "wrap_" prefix if present
    let s = if s.starts_with("wrap_") { &s[5..] } else { s };
    // Build "mod1/mod2/.../s" with mods in reverse (mods is already in reverse order)
    let mut parts: Vec<&str> = mods.iter().map(|m| m.as_str()).collect();
    parts.insert(0, s);
    parts.reverse();
    let joined = parts.join("/");
    // Remove '$' characters
    let cleaned: String = joined.chars().filter(|&c| c != '$').collect();
    settings.rewrite(kind, &cleaned)
}

fn relify(s: &str) -> String {
    s.chars().map(|c| if c == '/' { '_' } else { c }).collect()
}

fn alloc(counter: &mut usize) -> usize {
    let r = *counter;
    *counter += 1;
    r
}

// ---------------------------------------------------------------------------
// Flattening / St data structures
// ---------------------------------------------------------------------------

/// The Core PatternConstructor type alias.
type CorePatCon = core_ir::PatternConstructor;

#[derive(Debug, Clone)]
enum Flattening {
    Normal {
        name: Vec<String>,
        cons: HashMap<String, usize>,
        constructors: HashMap<String, CorePatCon>,
        vals: HashMap<String, usize>,
        strs: HashMap<String, Flattening>,
        funs: HashMap<String, (String, usize, expl::LocatedStructure)>,
    },
    Ffi {
        module: String,
        vals: HashMap<String, core_ir::LocatedConstructor>,
        constructors: HashMap<
            String,
            (
                String,
                Vec<String>,
                Option<core_ir::LocatedConstructor>,
                DatatypeKind,
            ),
        >,
    },
}

impl Flattening {
    fn new_normal(name: Vec<String>) -> Self {
        Flattening::Normal {
            name,
            cons: HashMap::new(),
            constructors: HashMap::new(),
            vals: HashMap::new(),
            strs: HashMap::new(),
            funs: HashMap::new(),
        }
    }

    fn name(&self) -> Vec<String> {
        match self {
            Flattening::Normal { name, .. } => name.clone(),
            Flattening::Ffi { module, .. } => vec![module.clone()],
        }
    }
}

#[derive(Debug, Clone)]
enum CoreCon {
    Normal(usize),
    Ffi(String),
}

#[derive(Debug, Clone)]
enum CoreVal {
    Normal(usize),
    Ffi(String, core_ir::LocatedConstructor),
}

struct St {
    basis: Option<usize>,
    cons: HashMap<usize, usize>,
    /// Maps explicit constructor ID → (ffi_module_name, con_name) for FFI types.
    /// Populated when processing DFfiStr to allow reverse lookup by explicit ID.
    con_ffi_map: HashMap<usize, (String, String)>,
    constructors: HashMap<usize, CorePatCon>,
    vals: HashMap<usize, usize>,
    strs: HashMap<usize, Flattening>,
    funs: HashMap<usize, (String, usize, expl::LocatedStructure)>,
    current: Flattening,
    nested: Vec<Flattening>,
}

impl St {
    fn empty() -> Self {
        St {
            basis: None,
            cons: HashMap::new(),
            con_ffi_map: HashMap::new(),
            constructors: HashMap::new(),
            vals: HashMap::new(),
            strs: HashMap::new(),
            funs: HashMap::new(),
            current: Flattening::new_normal(vec![]),
            nested: vec![],
        }
    }

    fn dummy(basis: Option<usize>, current: Flattening) -> Self {
        St {
            basis,
            cons: HashMap::new(),
            con_ffi_map: HashMap::new(),
            constructors: HashMap::new(),
            vals: HashMap::new(),
            strs: HashMap::new(),
            funs: HashMap::new(),
            current,
            nested: vec![],
        }
    }

    fn lookup_con_ffi(&self, explicit_id: usize) -> Option<&(String, String)> {
        self.con_ffi_map.get(&explicit_id)
    }

    fn basis_is(mut self, n: usize) -> Self {
        self.basis = Some(n);
        self
    }

    fn lookup_basis(&self) -> Option<usize> {
        self.basis
    }

    fn name(&self) -> Vec<String> {
        self.current.name()
    }

    // --- Con bindings ---

    fn bind_con(&mut self, x: &str, n: usize, counter: &mut usize) -> usize {
        let n_new = alloc(counter);
        match &mut self.current {
            Flattening::Normal { cons, .. } => {
                cons.insert(x.to_string(), n_new);
            }
            Flattening::Ffi { .. } => panic!("bind_con inside FFi flattening"),
        }
        self.cons.insert(n, n_new);
        n_new
    }

    fn lookup_con_by_id(&self, n: usize) -> Option<usize> {
        self.cons.get(&n).copied()
    }

    fn lookup_con_by_name(&self, x: &str) -> CoreCon {
        match &self.current {
            Flattening::Ffi { module, .. } => CoreCon::Ffi(module.clone()),
            Flattening::Normal { cons, .. } => match cons.get(x) {
                None => panic!("Corify.St.lookupConByName {}", x),
                Some(&n) => CoreCon::Normal(n),
            },
        }
    }

    // --- Val bindings ---

    fn bind_val(&mut self, x: &str, n: usize, counter: &mut usize) -> usize {
        let n_new = alloc(counter);
        match &mut self.current {
            Flattening::Normal { vals, .. } => {
                vals.insert(x.to_string(), n_new);
            }
            Flattening::Ffi { .. } => panic!("bind_val inside FFi flattening"),
        }
        self.vals.insert(n, n_new);
        n_new
    }

    fn bind_constructor_val(&mut self, x: &str, n: usize, n_new: usize) {
        match &mut self.current {
            Flattening::Normal { vals, .. } => {
                vals.insert(x.to_string(), n_new);
            }
            Flattening::Ffi { .. } => panic!("bind_constructor_val inside FFi flattening"),
        }
        self.vals.insert(n, n_new);
    }

    fn lookup_val_by_id(&self, n: usize) -> Option<usize> {
        self.vals.get(&n).copied()
    }

    fn lookup_val_by_name(&self, x: &str) -> CoreVal {
        match &self.current {
            Flattening::Ffi { module, vals, .. } => match vals.get(x) {
                None => panic!("Corify.St.lookupValByName: no type for FFI val {}", x),
                Some(t) => CoreVal::Ffi(module.clone(), t.clone()),
            },
            Flattening::Normal { name, vals, .. } => match vals.get(x) {
                None => {
                    let path: Vec<_> = name.iter().rev().cloned().collect();
                    panic!("Corify.St.lookupValByName {}.{}", path.join("."), x)
                }
                Some(&n) => CoreVal::Normal(n),
            },
        }
    }

    // --- Constructor (pattern) bindings ---

    fn bind_constructor_as(&mut self, x: &str, n: usize, c: CorePatCon) {
        match &mut self.current {
            Flattening::Normal { constructors, .. } => {
                constructors.insert(x.to_string(), c.clone());
            }
            Flattening::Ffi { .. } => panic!("bind_constructor_as inside FFi flattening"),
        }
        self.constructors.insert(n, c);
    }

    fn bind_constructor(&mut self, x: &str, n: usize, counter: &mut usize) -> (CorePatCon, usize) {
        let n_new = alloc(counter);
        let c = CorePatCon::Var(n_new);
        self.bind_constructor_as(x, n, c.clone());
        (c, n_new)
    }

    fn lookup_constructor_by_id(&self, n: usize) -> CorePatCon {
        match self.constructors.get(&n) {
            None => panic!("Corify.St.lookupConstructorById"),
            Some(c) => c.clone(),
        }
    }

    fn lookup_constructor_by_id_opt(&self, n: usize) -> Option<CorePatCon> {
        self.constructors.get(&n).cloned()
    }

    fn lookup_constructor_by_name_opt(&self, x: &str) -> Option<CorePatCon> {
        match &self.current {
            Flattening::Ffi {
                module,
                constructors,
                ..
            } => constructors.get(x).map(|(n, xs, to, dk)| CorePatCon::Ffi {
                module: module.clone(),
                datatyp: n.clone(),
                params: xs.clone(),
                con: x.to_string(),
                arg: to.clone(),
                kind: *dk,
            }),
            Flattening::Normal { constructors, .. } => constructors.get(x).cloned(),
        }
    }

    fn lookup_constructor_by_name(&self, x: &str) -> CorePatCon {
        match self.lookup_constructor_by_name_opt(x) {
            None => panic!("Corify.St.lookupConstructorByName {}", x),
            Some(c) => c,
        }
    }

    // --- Enter/leave ---

    fn enter(&mut self, name: Vec<String>) {
        let old = std::mem::replace(&mut self.current, Flattening::new_normal(name));
        self.nested.push(old);
    }

    fn leave(&mut self) -> Flattening {
        let inner = std::mem::replace(
            &mut self.current,
            self.nested
                .pop()
                .expect("Corify.St.leave: empty nested stack"),
        );
        inner
    }

    // --- Str bindings ---

    fn bind_str(&mut self, x: &str, n: usize, inner: &St) {
        let f = inner.current.clone();
        match &mut self.current {
            Flattening::Normal { strs, .. } => {
                strs.insert(x.to_string(), f.clone());
            }
            Flattening::Ffi { .. } => panic!("bind_str inside FFi flattening"),
        }
        self.strs.insert(n, f);
    }

    fn lookup_str_by_id(&self, n: usize) -> St {
        match self.strs.get(&n) {
            None => panic!("Corify.St.lookupStrById({})", n),
            Some(f) => St::dummy(self.basis, f.clone()),
        }
    }

    fn lookup_str_by_id_opt(&self, n: usize) -> Option<St> {
        self.strs.get(&n).map(|f| St::dummy(self.basis, f.clone()))
    }

    fn lookup_str_by_name(&self, x: &str) -> St {
        match &self.current {
            Flattening::Normal { strs, .. } => match strs.get(x) {
                None => panic!("Corify.St.lookupStrByName [1] {}", x),
                Some(f) => St::dummy(self.basis, f.clone()),
            },
            Flattening::Ffi { .. } => panic!("Corify.St.lookupStrByName [2]"),
        }
    }

    fn lookup_str_by_name_opt(&self, x: &str) -> Option<St> {
        match &self.current {
            Flattening::Normal { strs, .. } => {
                strs.get(x).map(|f| St::dummy(self.basis, f.clone()))
            }
            Flattening::Ffi { .. } => None,
        }
    }

    // --- Functor bindings ---

    fn bind_functor(
        &mut self,
        x: &str,
        n: usize,
        xa: String,
        na: usize,
        str: expl::LocatedStructure,
    ) {
        let v = (xa, na, str);
        match &mut self.current {
            Flattening::Normal { funs, .. } => {
                funs.insert(x.to_string(), v.clone());
            }
            Flattening::Ffi { .. } => panic!("bind_functor inside FFi flattening"),
        }
        self.funs.insert(n, v);
    }

    fn lookup_functor_by_id(&self, n: usize) -> (String, usize, expl::LocatedStructure) {
        match self.funs.get(&n) {
            None => panic!("Corify.St.lookupFunctorById"),
            Some(v) => v.clone(),
        }
    }

    fn lookup_functor_by_id_opt(
        &self,
        n: usize,
    ) -> Option<(String, usize, expl::LocatedStructure)> {
        self.funs.get(&n).cloned()
    }

    fn lookup_functor_by_name(&self, x: &str) -> (String, usize, expl::LocatedStructure) {
        match &self.current {
            Flattening::Normal { funs, .. } => match funs.get(x) {
                None => panic!("Corify.St.lookupFunctorByName {} [1]", x),
                Some(v) => v.clone(),
            },
            Flattening::Ffi { .. } => panic!("Corify.St.lookupFunctorByName [2]"),
        }
    }

    fn ffi(
        module: String,
        vals: HashMap<String, core_ir::LocatedConstructor>,
        constructors: HashMap<
            String,
            (
                String,
                Vec<String>,
                Option<core_ir::LocatedConstructor>,
                DatatypeKind,
            ),
        >,
    ) -> Self {
        St::dummy(
            None,
            Flattening::Ffi {
                module,
                vals,
                constructors,
            },
        )
    }
}

// ---------------------------------------------------------------------------
// Kind / Con / Pat / Exp corification (pure translations)
// ---------------------------------------------------------------------------

fn corify_kind(k: expl::LocatedKind) -> core_ir::LocatedKind {
    let span = k.span.clone();
    let node = match k.node {
        expl::Kind::Type => core_ir::Kind::Type,
        expl::Kind::Arrow(k1, k2) => {
            core_ir::Kind::Arrow(Box::new(corify_kind(*k1)), Box::new(corify_kind(*k2)))
        }
        expl::Kind::Name => core_ir::Kind::Name,
        expl::Kind::Record(k1) => core_ir::Kind::Record(Box::new(corify_kind(*k1))),
        expl::Kind::Unit => core_ir::Kind::Unit,
        expl::Kind::Tuple(ks) => core_ir::Kind::Tuple(ks.into_iter().map(corify_kind).collect()),
        expl::Kind::Rel(n) => core_ir::Kind::Rel(n),
        expl::Kind::Fun(x, k1) => core_ir::Kind::Fun(x, Box::new(corify_kind(*k1))),
    };
    Located { node, span }
}

fn corify_con(st: &St, c: expl::LocatedConstructor) -> core_ir::LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        expl::Constructor::TFun(t1, t2) => {
            core_ir::Constructor::TFun(Box::new(corify_con(st, *t1)), Box::new(corify_con(st, *t2)))
        }
        expl::Constructor::TCFun(x, k, t) => {
            core_ir::Constructor::TCFun(x, Box::new(corify_kind(*k)), Box::new(corify_con(st, *t)))
        }
        expl::Constructor::TKFun(x, t) => {
            core_ir::Constructor::TKFun(x, Box::new(corify_con(st, *t)))
        }
        expl::Constructor::TRecord(c1) => {
            core_ir::Constructor::TRecord(Box::new(corify_con(st, *c1)))
        }
        expl::Constructor::Rel(n) => core_ir::Constructor::Rel(n),
        expl::Constructor::Named(n) => {
            let n = match st.lookup_con_by_id(n) {
                None => n,
                Some(n2) => n2,
            };
            core_ir::Constructor::Named(n)
        }
        expl::Constructor::ModProj(m, ms, x) => {
            let mut sub_st = st.lookup_str_by_id(m);
            for seg in &ms {
                sub_st = sub_st.lookup_str_by_name(seg);
            }
            match sub_st.lookup_con_by_name(&x) {
                CoreCon::Normal(n) => core_ir::Constructor::Named(n),
                CoreCon::Ffi(m_name) => {
                    if m_name == "Basis" && x == "unit" {
                        // Basis.unit => TRecord (CRecord (KType, []))
                        core_ir::Constructor::TRecord(Box::new(Located {
                            node: core_ir::Constructor::Record(
                                Box::new(Located {
                                    node: core_ir::Kind::Type,
                                    span: span.clone(),
                                }),
                                vec![],
                            ),
                            span: span.clone(),
                        }))
                    } else {
                        core_ir::Constructor::Ffi(m_name, x)
                    }
                }
            }
        }
        expl::Constructor::App(c1, c2) => {
            core_ir::Constructor::App(Box::new(corify_con(st, *c1)), Box::new(corify_con(st, *c2)))
        }
        expl::Constructor::Abs(x, k, c1) => {
            core_ir::Constructor::Abs(x, Box::new(corify_kind(*k)), Box::new(corify_con(st, *c1)))
        }
        expl::Constructor::KAbs(x, c1) => {
            core_ir::Constructor::KAbs(x, Box::new(corify_con(st, *c1)))
        }
        expl::Constructor::KApp(c1, k) => {
            core_ir::Constructor::KApp(Box::new(corify_con(st, *c1)), Box::new(corify_kind(*k)))
        }
        expl::Constructor::Name(s) => core_ir::Constructor::Name(s),
        expl::Constructor::Record(k, xcs) => core_ir::Constructor::Record(
            Box::new(corify_kind(*k)),
            xcs.into_iter()
                .map(|(c1, c2)| (corify_con(st, c1), corify_con(st, c2)))
                .collect(),
        ),
        expl::Constructor::Concat(c1, c2) => core_ir::Constructor::Concat(
            Box::new(corify_con(st, *c1)),
            Box::new(corify_con(st, *c2)),
        ),
        expl::Constructor::Map(k1, k2) => {
            core_ir::Constructor::Map(Box::new(corify_kind(*k1)), Box::new(corify_kind(*k2)))
        }
        expl::Constructor::Unit => core_ir::Constructor::Unit,
        expl::Constructor::Tuple(cs) => {
            core_ir::Constructor::Tuple(cs.into_iter().map(|c| corify_con(st, c)).collect())
        }
        expl::Constructor::Proj(c1, n) => {
            core_ir::Constructor::Proj(Box::new(corify_con(st, *c1)), n)
        }
    };
    Located { node, span }
}

fn corify_pat_con(st: &St, pc: expl::PatternConstructor) -> CorePatCon {
    match pc {
        expl::PatternConstructor::Var(n) => st.lookup_constructor_by_id(n),
        expl::PatternConstructor::Proj(m1, ms, x) => {
            let mut sub_st = st.lookup_str_by_id(m1);
            for seg in &ms {
                sub_st = sub_st.lookup_str_by_name(seg);
            }
            sub_st.lookup_constructor_by_name(&x)
        }
    }
}

fn corify_pat(st: &St, p: expl::LocatedPattern) -> core_ir::LocatedPattern {
    let span = p.span.clone();
    let node = match p.node {
        expl::Pattern::Var(x, t) => core_ir::Pattern::Var(x, corify_con(st, t)),
        expl::Pattern::Prim(p) => core_ir::Pattern::Prim(p),
        expl::Pattern::Constructor(dk, pc, ts, po) => core_ir::Pattern::Constructor(
            dk,
            corify_pat_con(st, pc),
            ts.into_iter().map(|t| corify_con(st, t)).collect(),
            po.map(|p| Box::new(corify_pat(st, *p))),
        ),
        expl::Pattern::Record(xps) => core_ir::Pattern::Record(
            xps.into_iter()
                .map(|(x, p, t)| (x, corify_pat(st, p), corify_con(st, t)))
                .collect(),
        ),
    };
    Located { node, span }
}

fn is_transactional(c: &core_ir::LocatedConstructor) -> bool {
    match &c.node {
        core_ir::Constructor::TFun(_, ran) => is_transactional(ran),
        core_ir::Constructor::App(f, _) => {
            matches!(&f.node, core_ir::Constructor::Ffi(m, x) if m == "Basis" && x == "transaction")
        }
        _ => false,
    }
}

fn corify_exp(st: &St, e: expl::LocatedExpression) -> core_ir::LocatedExpression {
    let span = e.span.clone();
    let node = match e.node {
        expl::Expression::Prim(p) => core_ir::Expression::Prim(p),
        expl::Expression::Rel(n) => core_ir::Expression::Rel(n),
        expl::Expression::Named(n) => {
            let n = match st.lookup_val_by_id(n) {
                None => n,
                Some(n2) => n2,
            };
            core_ir::Expression::Named(n)
        }
        expl::Expression::ModProj(m, ms, x) => {
            let mut sub_st = st.lookup_str_by_id(m);
            for seg in &ms {
                sub_st = sub_st.lookup_str_by_name(seg);
            }

            // First check if it's a constructor
            if let Some(pc) = sub_st.lookup_constructor_by_name_opt(&x) {
                if let CorePatCon::Ffi {
                    module: m_name,
                    datatyp,
                    params,
                    arg,
                    kind,
                    ..
                } = &pc
                {
                    let params_clone = params.clone();
                    let arg_clone = arg.clone();
                    let m_name = m_name.clone();
                    let datatyp = datatyp.clone();
                    let kind = *kind;
                    let k_type = Located {
                        node: core_ir::Kind::Type,
                        span: span.clone(),
                    };
                    let args: Vec<core_ir::LocatedConstructor> = params_clone
                        .iter()
                        .enumerate()
                        .map(|(i, _)| Located {
                            node: core_ir::Constructor::Rel(i),
                            span: span.clone(),
                        })
                        .collect();
                    let inner_e: core_ir::LocatedExpression = match &arg_clone {
                        None => Located {
                            node: core_ir::Expression::Constructor(kind, pc.clone(), args, None),
                            span: span.clone(),
                        },
                        Some(dom) => {
                            let dt_con = Located {
                                node: core_ir::Constructor::Ffi(m_name.clone(), datatyp.clone()),
                                span: span.clone(),
                            };
                            Located {
                                node: core_ir::Expression::Abs(
                                    "x".to_string(),
                                    dom.clone(),
                                    dt_con,
                                    Box::new(Located {
                                        node: core_ir::Expression::Constructor(
                                            kind,
                                            pc.clone(),
                                            args,
                                            Some(Box::new(Located {
                                                node: core_ir::Expression::Rel(0),
                                                span: span.clone(),
                                            })),
                                        ),
                                        span: span.clone(),
                                    }),
                                ),
                                span: span.clone(),
                            }
                        }
                    };
                    // Wrap in ECAbs for each type param
                    let result = params_clone
                        .iter()
                        .rev()
                        .fold(inner_e, |acc_e, param_name| Located {
                            node: core_ir::Expression::CAbs(
                                param_name.clone(),
                                Box::new(k_type.clone()),
                                Box::new(acc_e),
                            ),
                            span: span.clone(),
                        });
                    return result;
                }
            }

            // Otherwise look up as val
            match sub_st.lookup_val_by_name(&x) {
                CoreVal::Normal(n) => core_ir::Expression::Named(n),
                CoreVal::Ffi(m_name, t) => {
                    // Check if it's a transaction wrapper
                    match &t.node {
                        core_ir::Constructor::App(f, dom) if matches!(&f.node, core_ir::Constructor::Ffi(bm, bt) if bm == "Basis" && bt == "transaction") =>
                        {
                            let dom = dom.clone();
                            let unit_t = Located {
                                node: core_ir::Constructor::TRecord(Box::new(Located {
                                    node: core_ir::Constructor::Record(
                                        Box::new(Located {
                                            node: core_ir::Kind::Type,
                                            span: span.clone(),
                                        }),
                                        vec![],
                                    ),
                                    span: span.clone(),
                                })),
                                span: span.clone(),
                            };
                            return Located {
                                node: core_ir::Expression::Abs(
                                    "arg".to_string(),
                                    *dom,
                                    unit_t,
                                    Box::new(Located {
                                        node: core_ir::Expression::FfiApp(m_name, x, vec![]),
                                        span: span.clone(),
                                    }),
                                ),
                                span,
                            };
                        }
                        _ => {}
                    }

                    // Check if it's a TFun — wrap in lambda
                    if let core_ir::Constructor::TFun(_, _) = &t.node {
                        // Collect argument types
                        fn get_args(
                            t: &core_ir::LocatedConstructor,
                        ) -> (
                            core_ir::LocatedConstructor,
                            Vec<core_ir::LocatedConstructor>,
                        ) {
                            match &t.node {
                                core_ir::Constructor::TFun(dom, ran) => {
                                    let (result, mut args) = get_args(ran);
                                    args.insert(0, *dom.clone());
                                    (result, args)
                                }
                                _ => (t.clone(), vec![]),
                            }
                        }

                        let (result_t, args) = get_args(&t);
                        let (is_transaction, result_t) = match &result_t.node {
                            core_ir::Constructor::App(f, inner_result) if matches!(&f.node, core_ir::Constructor::Ffi(bm, bt) if bm == "Basis" && bt == "transaction") => {
                                (true, *inner_result.clone())
                            }
                            _ => (false, result_t),
                        };

                        let unit_t = Located {
                            node: core_ir::Constructor::TRecord(Box::new(Located {
                                node: core_ir::Constructor::Record(
                                    Box::new(Located {
                                        node: core_ir::Kind::Type,
                                        span: span.clone(),
                                    }),
                                    vec![],
                                ),
                                span: span.clone(),
                            })),
                            span: span.clone(),
                        };

                        let n_args = args.len();

                        // Build FfiApp with rel vars
                        let start_n = if is_transaction { 1 } else { 0 };
                        let actuals: Vec<(
                            core_ir::LocatedExpression,
                            core_ir::LocatedConstructor,
                        )> = args
                            .iter()
                            .enumerate()
                            .map(|(i, arg_t)| {
                                let rel_n = n_args - 1 - i + start_n;
                                (
                                    Located {
                                        node: core_ir::Expression::Rel(rel_n),
                                        span: span.clone(),
                                    },
                                    arg_t.clone(),
                                )
                            })
                            .collect();

                        let ffi_app = Located {
                            node: core_ir::Expression::FfiApp(m_name.clone(), x.clone(), actuals),
                            span: span.clone(),
                        };

                        let (app, result_t) = if is_transaction {
                            let trans_result = Located {
                                node: core_ir::Expression::Abs(
                                    "_".to_string(),
                                    unit_t.clone(),
                                    result_t.clone(),
                                    Box::new(ffi_app),
                                ),
                                span: span.clone(),
                            };
                            let fun_t = Located {
                                node: core_ir::Constructor::TFun(
                                    Box::new(unit_t.clone()),
                                    Box::new(result_t.clone()),
                                ),
                                span: span.clone(),
                            };
                            (trans_result, fun_t)
                        } else {
                            (ffi_app, result_t)
                        };

                        // Wrap in lambdas for each argument
                        let (abs, _, _) = args.iter().rev().enumerate().fold(
                            (app, result_t, n_args as isize - 1),
                            |(inner_e, ran, idx), (_, arg_t)| {
                                let name = format!("arg{}", idx);
                                let new_ran = Located {
                                    node: core_ir::Constructor::TFun(
                                        Box::new(arg_t.clone()),
                                        Box::new(ran.clone()),
                                    ),
                                    span: span.clone(),
                                };
                                let new_e = Located {
                                    node: core_ir::Expression::Abs(
                                        name,
                                        arg_t.clone(),
                                        ran,
                                        Box::new(inner_e),
                                    ),
                                    span: span.clone(),
                                };
                                (new_e, new_ran, idx - 1)
                            },
                        );
                        return abs;
                    }

                    // Otherwise just EFfi
                    core_ir::Expression::Ffi(m_name, x)
                }
            }
        }
        expl::Expression::App(e1, e2) => {
            core_ir::Expression::App(Box::new(corify_exp(st, *e1)), Box::new(corify_exp(st, *e2)))
        }
        expl::Expression::Abs(x, dom, ran, e1) => core_ir::Expression::Abs(
            x,
            corify_con(st, dom),
            corify_con(st, ran),
            Box::new(corify_exp(st, *e1)),
        ),
        expl::Expression::CApp(e1, c) => {
            core_ir::Expression::CApp(Box::new(corify_exp(st, *e1)), corify_con(st, c))
        }
        expl::Expression::CAbs(x, k, e1) => {
            core_ir::Expression::CAbs(x, Box::new(corify_kind(*k)), Box::new(corify_exp(st, *e1)))
        }
        expl::Expression::KApp(e1, k) => {
            core_ir::Expression::KApp(Box::new(corify_exp(st, *e1)), Box::new(corify_kind(*k)))
        }
        expl::Expression::KAbs(x, e1) => {
            core_ir::Expression::KAbs(x, Box::new(corify_exp(st, *e1)))
        }
        expl::Expression::Record(xes) => core_ir::Expression::Record(
            xes.into_iter()
                .map(|(c, e, t)| (corify_con(st, c), corify_exp(st, e), corify_con(st, t)))
                .collect(),
        ),
        expl::Expression::Field(e1, c, meta) => core_ir::Expression::Field(
            Box::new(corify_exp(st, *e1)),
            corify_con(st, c),
            core_ir::FieldMeta {
                field: corify_con(st, meta.field),
                rest: corify_con(st, meta.rest),
            },
        ),
        expl::Expression::Concat(e1, c1, e2, c2) => core_ir::Expression::Concat(
            Box::new(corify_exp(st, *e1)),
            corify_con(st, c1),
            Box::new(corify_exp(st, *e2)),
            corify_con(st, c2),
        ),
        expl::Expression::Cut(e1, c, meta) => core_ir::Expression::Cut(
            Box::new(corify_exp(st, *e1)),
            corify_con(st, c),
            core_ir::FieldMeta {
                field: corify_con(st, meta.field),
                rest: corify_con(st, meta.rest),
            },
        ),
        expl::Expression::CutMulti(e1, c, meta) => core_ir::Expression::CutMulti(
            Box::new(corify_exp(st, *e1)),
            corify_con(st, c),
            core_ir::RestMeta {
                rest: corify_con(st, meta.rest),
            },
        ),
        expl::Expression::Case(e1, pes, meta) => core_ir::Expression::Case(
            Box::new(corify_exp(st, *e1)),
            pes.into_iter()
                .map(|(p, e)| (corify_pat(st, p), corify_exp(st, e)))
                .collect(),
            core_ir::CaseMeta {
                disc: corify_con(st, meta.disc),
                result: corify_con(st, meta.result),
            },
        ),
        expl::Expression::Write(e1) => core_ir::Expression::Write(Box::new(corify_exp(st, *e1))),
        expl::Expression::Let(x, t, e1, e2) => core_ir::Expression::Let(
            x,
            corify_con(st, t),
            Box::new(corify_exp(st, *e1)),
            Box::new(corify_exp(st, *e2)),
        ),
    };
    Located { node, span }
}

// ---------------------------------------------------------------------------
// Classify a list of core constructors for datatype kind
// ---------------------------------------------------------------------------

fn classify_datatype_core(
    xncs: &[(String, usize, Option<core_ir::LocatedConstructor>)],
) -> DatatypeKind {
    let mut nullary = 0usize;
    let mut unary = 0usize;
    for (_, _, opt) in xncs {
        if opt.is_none() {
            nullary += 1;
        } else {
            unary += 1;
        }
    }
    if unary == 0 {
        DatatypeKind::Enum
    } else if nullary == 1 && unary == 1 {
        DatatypeKind::Option
    } else {
        DatatypeKind::Default
    }
}

// ---------------------------------------------------------------------------
// corify_decl
// ---------------------------------------------------------------------------

fn corify_decl(
    mods: &[String],
    d: expl::LocatedDeclaration,
    st: &mut St,
    counter: &mut usize,
    settings: &mut Settings,
    errors: &mut ErrorReporter,
) -> Vec<core_ir::LocatedDeclaration> {
    let span = d.span.clone();

    match d.node {
        // DCon
        expl::Declaration::Constructor(x, n, k, c) => {
            let n_new = st.bind_con(&x, n, counter);
            let ck = corify_kind(k);
            let cc = corify_con(st, c);
            vec![Located {
                node: core_ir::Declaration::Constructor(x, n_new, ck, cc),
                span,
            }]
        }

        // DDatatype
        expl::Declaration::Datatype(dts) => {
            // First pass: bind all the type names
            let mut dts_with_new_ids: Vec<(
                String,
                usize,
                Vec<String>,
                Vec<(String, usize, Option<expl::LocatedConstructor>)>,
            )> = Vec::new();
            for dt in dts {
                let n_new = st.bind_con(&dt.name, dt.id, counter);
                dts_with_new_ids.push((dt.name, n_new, dt.params, dt.constrs));
            }

            // Second pass: bind constructors, generate DVal decls
            let mut result_decls: Vec<core_ir::LocatedDeclaration> = Vec::new();
            let mut core_dts: Vec<core_ir::DatatypeDecl> = Vec::new();

            for (x, n_new, xs, xncs) in dts_with_new_ids {
                let mut core_xncs: Vec<(String, usize, Option<core_ir::LocatedConstructor>)> =
                    Vec::new();
                for (cx, cn, co) in xncs {
                    let (_pat_con, cn_new) = st.bind_constructor(&cx, cn, counter);
                    st.bind_constructor_val(&cx, cn, cn_new);
                    let co_core = co.map(|c| corify_con(st, c));
                    core_xncs.push((cx, cn_new, co_core));
                }

                let dk = classify_datatype_core(&core_xncs);
                let nxs = if xs.is_empty() { 0 } else { xs.len() - 1 };

                // Build the base type: CNamed n, applied to CRel params
                let base_t = Located {
                    node: core_ir::Constructor::Named(n_new),
                    span: span.clone(),
                };
                let t = xs.iter().enumerate().fold(base_t, |acc, (i, _)| Located {
                    node: core_ir::Constructor::App(
                        Box::new(acc),
                        Box::new(Located {
                            node: core_ir::Constructor::Rel(nxs - i),
                            span: span.clone(),
                        }),
                    ),
                    span: span.clone(),
                });

                let k_type = Located {
                    node: core_ir::Kind::Type,
                    span: span.clone(),
                };

                // Generate DVal for each constructor
                for (cx, cn_new, co_core) in &core_xncs {
                    let args: Vec<core_ir::LocatedConstructor> = xs
                        .iter()
                        .enumerate()
                        .map(|(i, _)| Located {
                            node: core_ir::Constructor::Rel(nxs - i),
                            span: span.clone(),
                        })
                        .collect();

                    let pat_con = core_ir::PatternConstructor::Var(*cn_new);

                    let (e, val_t) = match co_core {
                        None => (
                            Located {
                                node: core_ir::Expression::Constructor(dk, pat_con, args, None),
                                span: span.clone(),
                            },
                            t.clone(),
                        ),
                        Some(t_prime) => {
                            let fun_t = Located {
                                node: core_ir::Constructor::TFun(
                                    Box::new(t_prime.clone()),
                                    Box::new(t.clone()),
                                ),
                                span: span.clone(),
                            };
                            (
                                Located {
                                    node: core_ir::Expression::Abs(
                                        "x".to_string(),
                                        t_prime.clone(),
                                        t.clone(),
                                        Box::new(Located {
                                            node: core_ir::Expression::Constructor(
                                                dk,
                                                pat_con,
                                                args,
                                                Some(Box::new(Located {
                                                    node: core_ir::Expression::Rel(0),
                                                    span: span.clone(),
                                                })),
                                            ),
                                            span: span.clone(),
                                        }),
                                    ),
                                    span: span.clone(),
                                },
                                fun_t,
                            )
                        }
                    };

                    // Wrap in type abstractions for each param
                    let val_t_wrapped = xs.iter().rev().fold(val_t, |acc, xp| Located {
                        node: core_ir::Constructor::TCFun(
                            xp.clone(),
                            Box::new(k_type.clone()),
                            Box::new(acc),
                        ),
                        span: span.clone(),
                    });
                    let e_wrapped = xs.iter().rev().fold(e, |acc, xp| Located {
                        node: core_ir::Expression::CAbs(
                            xp.clone(),
                            Box::new(k_type.clone()),
                            Box::new(acc),
                        ),
                        span: span.clone(),
                    });

                    result_decls.push(Located {
                        node: core_ir::Declaration::Val(
                            cx.clone(),
                            *cn_new,
                            val_t_wrapped,
                            e_wrapped,
                            String::new(),
                        ),
                        span: span.clone(),
                    });
                }

                core_dts.push(core_ir::DatatypeDecl {
                    name: x,
                    id: n_new,
                    params: xs,
                    constrs: core_xncs,
                });
            }

            let mut out = vec![Located {
                node: core_ir::Declaration::Datatype(core_dts),
                span: span.clone(),
            }];
            out.extend(result_decls);
            out
        }

        // DDatatypeImp
        expl::Declaration::DatatypeImp {
            name: x,
            id: n,
            orig_mod: m1,
            orig_path: ms,
            orig_name: s,
            orig_constrs_path: _,
            constrs: xncs,
        } => {
            let n_new = st.bind_con(&x, n, counter);

            // Corify the constructor type reference
            let c_ref = expl::LocatedConstructor {
                node: expl::Constructor::ModProj(m1, ms.clone(), s.clone()),
                span: span.clone(),
            };
            let c_base = corify_con(st, c_ref);

            // Build the "inner" structure to look up constructors by name
            let mut inner_st = st.lookup_str_by_id(m1);
            for seg in &ms {
                inner_st = inner_st.lookup_str_by_name(seg);
            }

            // Process constructors
            let mut core_xncs: Vec<(String, usize, Option<core_ir::LocatedConstructor>)> =
                Vec::new();
            for (cx, cn, co) in xncs {
                let n_prime = inner_st.lookup_constructor_by_name(&cx);
                st.bind_constructor_as(&cx, cn, n_prime);
                let cn_new = st.bind_val(&cx, cn, counter);
                let co_core = co.map(|c| corify_con(st, c));
                core_xncs.push((cx, cn_new, co_core));
            }

            let _nxs = 0usize; // DatatypeImp xs is just params for kind
            let k_type = Located {
                node: core_ir::Kind::Type,
                span: span.clone(),
            };

            // Compute kind for the type alias
            // The original has xs params; since expl::Declaration::DatatypeImp doesn't carry xs directly,
            // we compute from the number of params in the con
            // Actually looking at the SML, xs comes from the DDatatypeImp node.
            // In Rust expl::Declaration::DatatypeImp doesn't have a `params` field either.
            // The kind k' = foldl (fn (_, k') => KArrow(k, k')) k xs — but xs is empty here.
            // We'll use the c_base kind directly.
            let k_prime = k_type.clone(); // KType since no extra params

            // Generate DVal for each constructor: corify the expression from the original module
            let mut cds: Vec<core_ir::LocatedDeclaration> = Vec::new();
            for (cx, cn_new, co_core) in &core_xncs {
                let val_t = match co_core {
                    None => c_base.clone(),
                    Some(t_prime) => Located {
                        node: core_ir::Constructor::TFun(
                            Box::new(t_prime.clone()),
                            Box::new(c_base.clone()),
                        ),
                        span: span.clone(),
                    },
                };

                // The expression is EModProj(m1, ms, cx)
                let e_expl = expl::LocatedExpression {
                    node: expl::Expression::ModProj(m1, ms.clone(), cx.clone()),
                    span: span.clone(),
                };
                let e_core = corify_exp(st, e_expl);

                cds.push(Located {
                    node: core_ir::Declaration::Val(cx.clone(), *cn_new, val_t, e_core, cx.clone()),
                    span: span.clone(),
                });
            }

            let mut out = vec![Located {
                node: core_ir::Declaration::Constructor(x, n_new, k_prime, c_base),
                span: span.clone(),
            }];
            out.extend(cds);
            out
        }

        // DVal (special case: body is ENamed n')
        expl::Declaration::Val(x, n, t, e) if matches!(e.node, expl::Expression::Named(_)) => {
            let n_prime = if let expl::Expression::Named(np) = e.node {
                np
            } else {
                unreachable!()
            };
            if let Some(pc) = st.lookup_constructor_by_id_opt(n_prime) {
                st.bind_constructor_as(&x, n, pc);
            }
            let n_new = st.bind_val(&x, n, counter);
            let s = do_restify(settings, &PathKind::Url, mods, &x);
            let e_named = expl::LocatedExpression {
                node: expl::Expression::Named(n_prime),
                span: span.clone(),
            };
            vec![Located {
                node: core_ir::Declaration::Val(
                    x,
                    n_new,
                    corify_con(st, t),
                    corify_exp(st, e_named),
                    s,
                ),
                span,
            }]
        }

        // DVal (general)
        expl::Declaration::Val(x, n, t, e) => {
            let n_new = st.bind_val(&x, n, counter);
            let s = do_restify(settings, &PathKind::Url, mods, &x);
            vec![Located {
                node: core_ir::Declaration::Val(x, n_new, corify_con(st, t), corify_exp(st, e), s),
                span,
            }]
        }

        // DValRec
        expl::Declaration::ValRec(vis) => {
            // First pass: bind all names
            let vis_bound: Vec<(
                String,
                usize,
                expl::LocatedConstructor,
                expl::LocatedExpression,
            )> = vis
                .into_iter()
                .map(|(x, n, t, e)| {
                    let n_new = st.bind_val(&x, n, counter);
                    (x, n_new, t, e)
                })
                .collect();

            let core_vis: Vec<(
                String,
                usize,
                core_ir::LocatedConstructor,
                core_ir::LocatedExpression,
                String,
            )> = vis_bound
                .into_iter()
                .map(|(x, n_new, t, e)| {
                    let s = do_restify(settings, &PathKind::Url, mods, &x);
                    (x, n_new, corify_con(st, t), corify_exp(st, e), s)
                })
                .collect();

            vec![Located {
                node: core_ir::Declaration::ValRec(core_vis),
                span,
            }]
        }

        // DSgn — nothing to emit
        expl::Declaration::Signature(_, _, _) => vec![],

        // DStr — functor definition
        expl::Declaration::Structure(x, n, _, str)
            if matches!(str.node, expl::Structure::Fun(_, _, _, _, _)) =>
        {
            if let expl::Structure::Fun(xa, na, _dom, _ran, body) = str.node {
                st.bind_functor(&x, n, xa, na, *body);
            }
            vec![]
        }

        // DStr — StrProj
        expl::Declaration::Structure(x, n, _, str)
            if matches!(str.node, expl::Structure::Proj(_, _)) =>
        {
            if let expl::Structure::Proj(inner_str, x_prime) = str.node {
                let (ds, inner) = corify_str(mods, *inner_str, st, counter, settings, errors);
                // Drop ds (no declarations from structure projections)
                let _ = ds;
                if let Some(sub_st) = inner.lookup_str_by_name_opt(&x_prime) {
                    st.bind_str(&x, n, &sub_st);
                } else {
                    let (xa, na, str2) = inner.lookup_functor_by_name(&x_prime);
                    st.bind_functor(&x, n, xa, na, str2);
                }
            }
            vec![]
        }

        // DStr — StrVar
        expl::Declaration::Structure(x, n, _, str)
            if matches!(str.node, expl::Structure::Var(_)) =>
        {
            if let expl::Structure::Var(n_prime) = str.node {
                if let Some((arg, dom, body)) = st.lookup_functor_by_id_opt(n_prime) {
                    st.bind_functor(&x, n, arg, dom, body);
                } else {
                    let sub_st = st.lookup_str_by_id(n_prime);
                    st.bind_str(&x, n, &sub_st);
                }
            }
            vec![]
        }

        // DStr — general
        expl::Declaration::Structure(x, n, _, str) => {
            let mods_prime: Vec<String> = if x == "anon" {
                mods.to_vec()
            } else {
                let mut v = vec![x.clone()];
                v.extend_from_slice(mods);
                v
            };
            let (ds, inner) = corify_str(&mods_prime, str, st, counter, settings, errors);
            st.bind_str(&x, n, &inner);
            ds
        }

        // DFfiStr
        expl::Declaration::FfiStr(m, n, sgn) => {
            if let expl::Signature::Const(sgis) = sgn.node {
                let mut ds: Vec<core_ir::LocatedDeclaration> = Vec::new();
                let mut cmap: HashMap<String, core_ir::LocatedConstructor> = HashMap::new();
                let mut conmap: HashMap<
                    String,
                    (
                        String,
                        Vec<String>,
                        Option<core_ir::LocatedConstructor>,
                        DatatypeKind,
                    ),
                > = HashMap::new();
                let mut trans: Option<usize> = None;

                for sgi in sgis {
                    match sgi.node {
                        expl::SignatureItem::ConAbs(x, sn, k) => {
                            let n_new = st.bind_con(&x, sn, counter);
                            // Record the FFI mapping for reverse lookup by explicit ID
                            st.con_ffi_map.insert(sn, (m.clone(), x.clone()));
                            if x == "transaction" {
                                trans = Some(sn);
                            }
                            let core_k = corify_kind(k);
                            let ffi_con = Located {
                                node: core_ir::Constructor::Ffi(m.clone(), x.clone()),
                                span: span.clone(),
                            };
                            ds.push(Located {
                                node: core_ir::Declaration::Constructor(x, n_new, core_k, ffi_con),
                                span: span.clone(),
                            });
                        }
                        expl::SignatureItem::Constructor(x, sn, k, _c) => {
                            let n_new = st.bind_con(&x, sn, counter);
                            st.con_ffi_map.insert(sn, (m.clone(), x.clone()));
                            let core_k = corify_kind(k);
                            let ffi_con = Located {
                                node: core_ir::Constructor::Ffi(m.clone(), x.clone()),
                                span: span.clone(),
                            };
                            ds.push(Located {
                                node: core_ir::Declaration::Constructor(x, n_new, core_k, ffi_con),
                                span: span.clone(),
                            });
                        }
                        expl::SignatureItem::Datatype(dts) => {
                            let k_type = Located {
                                node: core_ir::Kind::Type,
                                span: span.clone(),
                            };

                            for dt in dts {
                                let xs = &dt.params;
                                let k_prime = xs.iter().fold(k_type.clone(), |acc, _| Located {
                                    node: core_ir::Kind::Arrow(
                                        Box::new(k_type.clone()),
                                        Box::new(acc),
                                    ),
                                    span: span.clone(),
                                });

                                // Classify using expl constrs (all have optional type)
                                let dk = {
                                    let mut nullary = 0usize;
                                    let mut unary = 0usize;
                                    for (_, _, opt) in &dt.constrs {
                                        if opt.is_none() {
                                            nullary += 1;
                                        } else {
                                            unary += 1;
                                        }
                                    }
                                    if unary == 0 {
                                        DatatypeKind::Enum
                                    } else if nullary == 1 && unary == 1 {
                                        DatatypeKind::Option
                                    } else {
                                        DatatypeKind::Default
                                    }
                                };

                                let n_new = st.bind_con(&dt.name, dt.id, counter);

                                for (cx, cn, co) in &dt.constrs {
                                    let dt_con = Located {
                                        node: core_ir::Constructor::Named(n_new),
                                        span: span.clone(),
                                    };
                                    let args: Vec<core_ir::LocatedConstructor> = xs
                                        .iter()
                                        .enumerate()
                                        .map(|(i, _)| Located {
                                            node: core_ir::Constructor::Rel(i),
                                            span: span.clone(),
                                        })
                                        .collect();

                                    let co_core = co.as_ref().map(|c| corify_con(st, c.clone()));

                                    let pc = core_ir::PatternConstructor::Ffi {
                                        module: m.clone(),
                                        datatyp: dt.name.clone(),
                                        params: xs.clone(),
                                        con: cx.clone(),
                                        arg: co_core.clone(),
                                        kind: dk,
                                    };

                                    let wrap_t = |t: core_ir::LocatedConstructor| {
                                        xs.iter().rev().fold(t, |acc, xp| Located {
                                            node: core_ir::Constructor::TCFun(
                                                xp.clone(),
                                                Box::new(k_type.clone()),
                                                Box::new(acc),
                                            ),
                                            span: span.clone(),
                                        })
                                    };
                                    let wrap_e = |e: core_ir::LocatedExpression| {
                                        xs.iter().rev().fold(e, |acc, xp| Located {
                                            node: core_ir::Expression::CAbs(
                                                xp.clone(),
                                                Box::new(k_type.clone()),
                                                Box::new(acc),
                                            ),
                                            span: span.clone(),
                                        })
                                    };

                                    let (cmap_entry, dval) = match &co_core {
                                        None => {
                                            let wt = wrap_t(dt_con.clone());
                                            let we = wrap_e(Located {
                                                node: core_ir::Expression::Constructor(
                                                    dk,
                                                    pc.clone(),
                                                    args.clone(),
                                                    None,
                                                ),
                                                span: span.clone(),
                                            });
                                            let d = Located {
                                                node: core_ir::Declaration::Val(
                                                    cx.clone(),
                                                    *cn,
                                                    wt.clone(),
                                                    we,
                                                    String::new(),
                                                ),
                                                span: span.clone(),
                                            };
                                            (wt, d)
                                        }
                                        Some(t) => {
                                            let tf = Located {
                                                node: core_ir::Constructor::TFun(
                                                    Box::new(t.clone()),
                                                    Box::new(dt_con.clone()),
                                                ),
                                                span: span.clone(),
                                            };
                                            let e = wrap_e(Located {
                                                node: core_ir::Expression::Abs(
                                                    "x".to_string(),
                                                    t.clone(),
                                                    tf.clone(),
                                                    Box::new(Located {
                                                        node: core_ir::Expression::Constructor(
                                                            dk,
                                                            pc.clone(),
                                                            args.clone(),
                                                            Some(Box::new(Located {
                                                                node: core_ir::Expression::Rel(0),
                                                                span: span.clone(),
                                                            })),
                                                        ),
                                                        span: span.clone(),
                                                    }),
                                                ),
                                                span: span.clone(),
                                            });
                                            let wt = wrap_t(tf);
                                            let d = Located {
                                                node: core_ir::Declaration::Val(
                                                    cx.clone(),
                                                    *cn,
                                                    wt.clone(),
                                                    e,
                                                    String::new(),
                                                ),
                                                span: span.clone(),
                                            };
                                            (wt, d)
                                        }
                                    };

                                    st.bind_constructor_as(cx, *cn, pc);
                                    conmap.insert(
                                        cx.clone(),
                                        (dt.name.clone(), xs.clone(), co_core, dk),
                                    );
                                    cmap.insert(cx.clone(), cmap_entry);
                                    ds.push(dval);
                                }

                                let ffi_con = Located {
                                    node: core_ir::Constructor::Ffi(m.clone(), dt.name.clone()),
                                    span: span.clone(),
                                };
                                ds.push(Located {
                                    node: core_ir::Declaration::Constructor(
                                        dt.name.clone(),
                                        n_new,
                                        k_prime,
                                        ffi_con,
                                    ),
                                    span: span.clone(),
                                });
                            }
                        }
                        expl::SignatureItem::Val(x, _sn, c) => {
                            // Apply transactify if we know the transaction type
                            let c_core = match trans {
                                None => corify_con(st, c),
                                Some(trans_id) => transactify(st, trans_id, &m, c, &span),
                            };

                            if is_transactional(&c_core) {
                                let ffi_key = (m.clone(), x.clone());
                                if !settings.is_benign_effectful(&ffi_key) {
                                    settings.effectful.insert(ffi_key);
                                }
                            }

                            cmap.insert(x, c_core);
                        }
                        _ => {}
                    }
                }

                let ffi_st = St::ffi(m.clone(), cmap, conmap);
                st.bind_str(&m, n, &ffi_st);
                if m == "Basis" {
                    st.basis = Some(n);
                }
                ds
            } else {
                errors.report_at(span, "Non-const signature for FFI structure");
                vec![]
            }
        }

        // DExport
        expl::Declaration::Export(en, sgn, str) => {
            if let expl::Signature::Const(sgis) = sgn.node {
                // pathify: convert the str to (module_id, path_segments)
                fn pathify(s: &expl::Structure) -> Option<(usize, Vec<String>)> {
                    match s {
                        expl::Structure::Var(m) => Some((*m, vec![])),
                        expl::Structure::Proj(inner, seg) => {
                            pathify(&inner.node).map(|(m, mut ms)| {
                                ms.push(seg.clone());
                                (m, ms)
                            })
                        }
                        _ => None,
                    }
                }

                match pathify(&str.node) {
                    None => {
                        errors.report_at(span, "Structure is too fancy to export");
                        vec![]
                    }
                    Some((m, ms)) => {
                        let basis_n = match st.lookup_basis() {
                            None => panic!("Corify: Don't know number of Basis"),
                            Some(n) => n,
                        };

                        let mut wrap_decls: Vec<expl::LocatedDeclaration> = Vec::new();
                        let mut export_fns: Vec<Box<dyn Fn(&St) -> core_ir::LocatedDeclaration>> =
                            Vec::new();

                        // Debug: show what's in the signature
                        eprintln!("[DEBUG export] Processing Export, sgis count={}", sgis.len());
                        for sgi in &sgis {
                            match &sgi.node {
                                expl::SignatureItem::Val(s, _, t) => {
                                    eprintln!("[DEBUG export]   SgiVal '{}' type depth={}", s, con_depth(t));
                                    eprintln!("[DEBUG export]     type: {}", debug_con(t, 0));
                                }
                                _ => eprintln!("[DEBUG export]   non-val sgi"),
                            }
                        }

                        for sgi in sgis {
                            if let expl::SignatureItem::Val(s, _, t) = sgi.node {
                                // Check if it's a page (returns transaction xml)
                                if let Some((ran_prime, args)) = get_page(basis_n, &t, st) {
                                    let wrap_name = format!("wrap_{}", s);
                                    let unit_t = expl::LocatedConstructor {
                                        node: expl::Constructor::Record(
                                            Box::new(expl::LocatedKind {
                                                node: expl::Kind::Type,
                                                span: span.clone(),
                                            }),
                                            vec![],
                                        ),
                                        span: span.clone(),
                                    };
                                    let ran_unit = expl::LocatedConstructor {
                                        node: expl::Constructor::TRecord(Box::new(unit_t.clone())),
                                        span: span.clone(),
                                    };
                                    let ran_t = expl::LocatedConstructor {
                                        node: expl::Constructor::App(
                                            Box::new(expl::LocatedConstructor {
                                                node: expl::Constructor::ModProj(
                                                    basis_n,
                                                    vec![],
                                                    "transaction".to_string(),
                                                ),
                                                span: span.clone(),
                                            }),
                                            Box::new(ran_unit.clone()),
                                        ),
                                        span: span.clone(),
                                    };

                                    // Check for postBody in args
                                    let has_post_body = args.iter().any(|arg_t| {
                                        matches!(
                                            corify_con(st, arg_t.clone()).node,
                                            core_ir::Constructor::Ffi(ref bm, ref bx) if bm == "Basis" && bx == "postBody"
                                        )
                                    });

                                    let exp_kind = if has_post_body {
                                        ExportKind::Extern(Effect::ReadCookieWrite)
                                    } else {
                                        ExportKind::Link(Effect::ReadCookieWrite)
                                    };

                                    // Build the wrapper expression
                                    let base_e = expl::LocatedExpression {
                                        node: expl::Expression::ModProj(m, ms.clone(), s.clone()),
                                        span: span.clone(),
                                    };

                                    // Bind monad
                                    let ef = expl::LocatedExpression {
                                        node: expl::Expression::ModProj(
                                            basis_n,
                                            vec![],
                                            "bind".to_string(),
                                        ),
                                        span: span.clone(),
                                    };
                                    let trans_con = expl::LocatedConstructor {
                                        node: expl::Constructor::ModProj(
                                            basis_n,
                                            vec![],
                                            "transaction".to_string(),
                                        ),
                                        span: span.clone(),
                                    };
                                    let ef = expl::LocatedExpression {
                                        node: expl::Expression::CApp(
                                            Box::new(ef),
                                            trans_con.clone(),
                                        ),
                                        span: span.clone(),
                                    };
                                    let ef = expl::LocatedExpression {
                                        node: expl::Expression::CApp(
                                            Box::new(ef),
                                            ran_prime.clone(),
                                        ),
                                        span: span.clone(),
                                    };
                                    let ef = expl::LocatedExpression {
                                        node: expl::Expression::CApp(
                                            Box::new(ef),
                                            ran_unit.clone(),
                                        ),
                                        span: span.clone(),
                                    };
                                    let tm_e = expl::LocatedExpression {
                                        node: expl::Expression::ModProj(
                                            basis_n,
                                            vec![],
                                            "transaction_monad".to_string(),
                                        ),
                                        span: span.clone(),
                                    };
                                    let ef = expl::LocatedExpression {
                                        node: expl::Expression::App(Box::new(ef), Box::new(tm_e)),
                                        span: span.clone(),
                                    };

                                    // Apply base_e to all args
                                    let n_args = args.len();
                                    let ea = (0..n_args).rev().fold(base_e, |acc, i| {
                                        expl::LocatedExpression {
                                            node: expl::Expression::App(
                                                Box::new(acc),
                                                Box::new(expl::LocatedExpression {
                                                    node: expl::Expression::Rel(i),
                                                    span: span.clone(),
                                                }),
                                            ),
                                            span: span.clone(),
                                        }
                                    });
                                    let ef = expl::LocatedExpression {
                                        node: expl::Expression::App(Box::new(ef), Box::new(ea)),
                                        span: span.clone(),
                                    };

                                    let eat_t = expl::LocatedConstructor {
                                        node: expl::Constructor::App(
                                            Box::new(trans_con),
                                            Box::new(ran_unit),
                                        ),
                                        span: span.clone(),
                                    };
                                    let ea_inner = expl::LocatedExpression {
                                        node: expl::Expression::Write(Box::new(
                                            expl::LocatedExpression {
                                                node: expl::Expression::Rel(0),
                                                span: span.clone(),
                                            },
                                        )),
                                        span: span.clone(),
                                    };
                                    let ea = expl::LocatedExpression {
                                        node: expl::Expression::Abs(
                                            "p".to_string(),
                                            ran_prime.clone(),
                                            eat_t,
                                            Box::new(ea_inner),
                                        ),
                                        span: span.clone(),
                                    };
                                    let full_e = expl::LocatedExpression {
                                        node: expl::Expression::App(Box::new(ef), Box::new(ea)),
                                        span: span.clone(),
                                    };

                                    // Wrap in lambdas for each argument
                                    let (wrapped_e, wrapped_t) = args
                                        .iter()
                                        .rev()
                                        .enumerate()
                                        .fold((full_e, ran_t), |(body_e, body_t), (i, arg_t)| {
                                            let idx = n_args - 1 - i;
                                            let new_e = expl::LocatedExpression {
                                                node: expl::Expression::Abs(
                                                    format!("x{}", idx),
                                                    arg_t.clone(),
                                                    body_t.clone(),
                                                    Box::new(body_e),
                                                ),
                                                span: span.clone(),
                                            };
                                            let new_t = expl::LocatedConstructor {
                                                node: expl::Constructor::TFun(
                                                    Box::new(arg_t.clone()),
                                                    Box::new(body_t),
                                                ),
                                                span: span.clone(),
                                            };
                                            (new_e, new_t)
                                        });

                                    wrap_decls.push(expl::LocatedDeclaration {
                                        node: expl::Declaration::Val(
                                            wrap_name.clone(),
                                            0,
                                            wrapped_t,
                                            wrapped_e,
                                        ),
                                        span: span.clone(),
                                    });

                                    let _s_clone = s.clone();
                                    let wrap_name_clone = wrap_name.clone();
                                    let span_clone = span.clone();
                                    export_fns.push(Box::new(move |st2: &St| {
                                        let e = expl::LocatedExpression {
                                            node: expl::Expression::ModProj(
                                                en,
                                                vec![],
                                                wrap_name_clone.clone(),
                                            ),
                                            span: span_clone.clone(),
                                        };
                                        let ce = corify_exp(st2, e);
                                        match ce.node {
                                            core_ir::Expression::Named(n) => Located {
                                                node: core_ir::Declaration::Export(
                                                    exp_kind, n, false,
                                                ),
                                                span: span_clone.clone(),
                                            },
                                            _ => panic!(
                                                "Corify: Value to export didn't corify properly"
                                            ),
                                        }
                                    }));
                                }
                            }
                        }

                        // Corify the wrapper structure
                        let wrapper_str = expl::LocatedStructure {
                            node: expl::Structure::Const(wrap_decls),
                            span: span.clone(),
                        };

                        let m_st = st.lookup_str_by_id(m);
                        let m_st2 = ms.iter().fold(m_st, |acc, seg| acc.lookup_str_by_name(seg));
                        let wrapper_mods = m_st2.name();

                        let (ds, inner) =
                            corify_str(&wrapper_mods, wrapper_str, st, counter, settings, errors);
                        st.bind_str("wrapper", en, &inner);

                        let export_ds: Vec<core_ir::LocatedDeclaration> =
                            export_fns.iter().map(|f| f(st)).collect();

                        let mut out = ds;
                        out.extend(export_ds);
                        out
                    }
                }
            } else {
                errors.report_at(span, "Non-const signature for 'export'");
                vec![]
            }
        }

        // DTable
        expl::Declaration::Table {
            mod_id: _,
            name: x,
            name_id: n,
            con: c,
            exp: pe,
            pk_con: pc,
            pk_exp: ce,
            unique_con: cc,
        } => {
            let n_new = st.bind_val(&x, n, counter);
            let s = relify(&do_restify(settings, &PathKind::Table, mods, &x));
            vec![Located {
                node: core_ir::Declaration::Table {
                    sql_name: x.clone(),
                    id: n_new,
                    con: corify_con(st, c),
                    sql_con: s,
                    exp: corify_exp(st, pe),
                    pk_con: corify_con(st, pc),
                    pk_exp: corify_exp(st, ce),
                    unique_con: corify_con(st, cc),
                },
                span,
            }]
        }

        // DSequence
        expl::Declaration::Sequence(_mod_id, x, n) => {
            let n_new = st.bind_val(&x, n, counter);
            let s = relify(&do_restify(settings, &PathKind::Sequence, mods, &x));
            vec![Located {
                node: core_ir::Declaration::Sequence(x, n_new, s),
                span,
            }]
        }

        // DView
        expl::Declaration::View(_mod_id, x, n, e, c) => {
            let n_new = st.bind_val(&x, n, counter);
            let s = relify(&do_restify(settings, &PathKind::View, mods, &x));
            vec![Located {
                node: core_ir::Declaration::View(x, n_new, s, corify_exp(st, e), corify_con(st, c)),
                span,
            }]
        }

        // DIndex
        expl::Declaration::Index(e1, e2) => {
            vec![Located {
                node: core_ir::Declaration::Index(corify_exp(st, e1), corify_exp(st, e2)),
                span,
            }]
        }

        // DDatabase
        expl::Declaration::Database(s) => {
            vec![Located {
                node: core_ir::Declaration::Database(s),
                span,
            }]
        }

        // DCookie
        expl::Declaration::Cookie(_mod_id, x, n, c) => {
            let n_new = st.bind_val(&x, n, counter);
            let s = do_restify(settings, &PathKind::Cookie, mods, &x);
            vec![Located {
                node: core_ir::Declaration::Cookie(x, n_new, corify_con(st, c), s),
                span,
            }]
        }

        // DStyle
        expl::Declaration::Style(_mod_id, x, n) => {
            let n_new = st.bind_val(&x, n, counter);
            let s = relify(&do_restify(settings, &PathKind::Style, mods, &x));
            vec![Located {
                node: core_ir::Declaration::Style(x, n_new, s),
                span,
            }]
        }

        // DTask
        expl::Declaration::Task(e1, e2) => {
            vec![Located {
                node: core_ir::Declaration::Task(corify_exp(st, e1), corify_exp(st, e2)),
                span,
            }]
        }

        // DPolicy
        expl::Declaration::Policy(e1) => {
            vec![Located {
                node: core_ir::Declaration::Policy(corify_exp(st, e1)),
                span,
            }]
        }

        // DOnError
        expl::Declaration::OnError(m, ms, x) => {
            let mut sub_st = st.lookup_str_by_id(m);
            for seg in &ms {
                sub_st = sub_st.lookup_str_by_name(seg);
            }
            match sub_st.lookup_val_by_name(&x) {
                CoreVal::Normal(n) => vec![Located {
                    node: core_ir::Declaration::OnError(n),
                    span,
                }],
                _ => {
                    errors.report_at(span, "Wrong type of identifier for 'onError'");
                    vec![]
                }
            }
        }

        // DFfi
        expl::Declaration::Ffi(x, n, modes, t) => {
            let m_name = match st.name().as_slice() {
                [m] => m.clone(),
                _ => {
                    errors.report_at(
                        span.clone(),
                        "Used 'ffi' declaration beneath module top level",
                    );
                    String::new()
                }
            };

            let n_new = st.bind_val(&x, n, counter);
            let s = do_restify(settings, &PathKind::Url, mods, &x);
            let t_core = corify_con(st, t);

            fn num_args(c: &core_ir::LocatedConstructor) -> usize {
                match &c.node {
                    core_ir::Constructor::TFun(_, ran) => 1 + num_args(ran),
                    _ => 0,
                }
            }

            fn make_args(
                i: isize,
                t: &core_ir::LocatedConstructor,
                span: &Span,
            ) -> Vec<(core_ir::LocatedExpression, core_ir::LocatedConstructor)> {
                match &t.node {
                    core_ir::Constructor::TFun(dom, ran) => {
                        let mut rest = make_args(i - 1, ran, span);
                        rest.insert(
                            0,
                            (
                                Located {
                                    node: core_ir::Expression::Rel(i as usize),
                                    span: span.clone(),
                                },
                                *dom.clone(),
                            ),
                        );
                        rest
                    }
                    _ => vec![],
                }
            }

            fn get_ran(t: &core_ir::LocatedConstructor) -> core_ir::LocatedConstructor {
                match &t.node {
                    core_ir::Constructor::TFun(_, ran) => get_ran(ran),
                    _ => t.clone(),
                }
            }

            fn add_last_bit(
                t: &core_ir::LocatedConstructor,
                span: &Span,
            ) -> core_ir::LocatedConstructor {
                match &t.node {
                    core_ir::Constructor::TFun(dom, ran) => Located {
                        node: core_ir::Constructor::TFun(
                            dom.clone(),
                            Box::new(add_last_bit(ran, span)),
                        ),
                        span: span.clone(),
                    },
                    _ => {
                        let unit_t = Located {
                            node: core_ir::Constructor::TRecord(Box::new(Located {
                                node: core_ir::Constructor::Record(
                                    Box::new(Located {
                                        node: core_ir::Kind::Type,
                                        span: span.clone(),
                                    }),
                                    vec![],
                                ),
                                span: span.clone(),
                            })),
                            span: span.clone(),
                        };
                        Located {
                            node: core_ir::Constructor::TFun(Box::new(unit_t), Box::new(t.clone())),
                            span: span.clone(),
                        }
                    }
                }
            }

            let is_trans = is_transactional(&t_core);
            let n_total = num_args(&t_core);
            let arg_count = if is_trans {
                n_total
            } else {
                n_total.saturating_sub(1)
            };
            let actuals = make_args(arg_count as isize - 1, &t_core, &span);

            let ffi_app = Located {
                node: core_ir::Expression::FfiApp(m_name.clone(), x.clone(), actuals),
                span: span.clone(),
            };

            let unit_t = Located {
                node: core_ir::Constructor::TRecord(Box::new(Located {
                    node: core_ir::Constructor::Record(
                        Box::new(Located {
                            node: core_ir::Kind::Type,
                            span: span.clone(),
                        }),
                        vec![],
                    ),
                    span: span.clone(),
                })),
                span: span.clone(),
            };

            let (e, t_trans) = if is_trans {
                let ran = get_ran(&t_core);
                let abs = Located {
                    node: core_ir::Expression::Abs(
                        "_".to_string(),
                        unit_t.clone(),
                        ran,
                        Box::new(ffi_app),
                    ),
                    span: span.clone(),
                };
                let t2 = add_last_bit(&t_core, &span);
                (abs, t2)
            } else {
                (ffi_app, t_core.clone())
            };

            // Wrap in lambdas
            let e = wrap_abs(0, &t_core, &t_trans, e, &span);

            // Register FFI modes
            let ffi_key = (m_name.clone(), x.clone());
            let mut has_js_func = false;
            for mode in &modes {
                match mode {
                    crate::source::FfiMode::Effectful => {
                        settings.effectful.insert(ffi_key.clone());
                    }
                    crate::source::FfiMode::BenignEffectful => {
                        settings.benign.insert(ffi_key.clone());
                    }
                    crate::source::FfiMode::ClientOnly => {
                        settings.client_only.insert(ffi_key.clone());
                    }
                    crate::source::FfiMode::ServerOnly => {
                        settings.server_only.insert(ffi_key.clone());
                    }
                    crate::source::FfiMode::JsFunc(js_s) => {
                        settings.js_funcs.insert(ffi_key.clone(), js_s.clone());
                        has_js_func = true;
                    }
                }
            }
            if !has_js_func {
                settings.js_funcs.insert(ffi_key.clone(), x.clone());
            }
            if is_trans && !settings.is_benign_effectful(&ffi_key) {
                settings.effectful.insert(ffi_key);
            }

            vec![Located {
                node: core_ir::Declaration::Val(x, n_new, t_core, e, s),
                span,
            }]
        }
    }
}

// Helper: wrap an expression in lambda abstractions mirroring wrapAbs from SML
fn wrap_abs(
    i: usize,
    t: &core_ir::LocatedConstructor,
    t_trans: &core_ir::LocatedConstructor,
    e: core_ir::LocatedExpression,
    span: &Span,
) -> core_ir::LocatedExpression {
    match (&t.node, &t_trans.node) {
        (core_ir::Constructor::TFun(dom, ran), core_ir::Constructor::TFun(_, ran_trans)) => {
            let inner = wrap_abs(i + 1, ran, ran_trans, e, span);
            Located {
                node: core_ir::Expression::Abs(
                    format!("x{}", i),
                    *dom.clone(),
                    *ran_trans.clone(),
                    Box::new(inner),
                ),
                span: span.clone(),
            }
        }
        _ => e,
    }
}

// Helper: "transactify" — replace CNamed(trans_id) apps with CFfi("Basis", "transaction") apps
fn transactify(
    st: &St,
    trans_id: usize,
    m: &str,
    c: expl::LocatedConstructor,
    span: &Span,
) -> core_ir::LocatedConstructor {
    match c.node {
        expl::Constructor::TFun(dom, ran) => {
            let core_dom = corify_con(st, *dom);
            let ran_t = transactify(st, trans_id, m, *ran, span);
            Located {
                node: core_ir::Constructor::TFun(Box::new(core_dom), Box::new(ran_t)),
                span: span.clone(),
            }
        }
        expl::Constructor::App(f, arg) => {
            if let expl::Constructor::Named(id) = f.node {
                if id == trans_id {
                    let arg_core = corify_con(st, *arg);
                    let trans_ffi = Located {
                        node: core_ir::Constructor::Ffi(m.to_string(), "transaction".to_string()),
                        span: span.clone(),
                    };
                    return Located {
                        node: core_ir::Constructor::App(Box::new(trans_ffi), Box::new(arg_core)),
                        span: span.clone(),
                    };
                }
            }
            corify_con(
                st,
                Located {
                    node: expl::Constructor::App(f, arg),
                    span: span.clone(),
                },
            )
        }
        _ => corify_con(st, c),
    }
}

// Debug helpers
fn con_depth(t: &expl::LocatedConstructor) -> usize {
    match &t.node {
        expl::Constructor::App(f, _) => 1 + con_depth(f),
        expl::Constructor::TFun(d, r) => 1 + con_depth(d).max(con_depth(r)),
        expl::Constructor::TCFun(_, _, r) => 1 + con_depth(r),
        _ => 0,
    }
}

fn debug_con(t: &expl::LocatedConstructor, depth: usize) -> String {
    if depth > 6 { return "...".into(); }
    match &t.node {
        expl::Constructor::ModProj(m, ms, s) => format!("ModProj({},{:?},{})", m, ms, s),
        expl::Constructor::App(f, a) => format!("App({}, {})", debug_con(f, depth+1), debug_con(a, depth+1)),
        expl::Constructor::TFun(d, r) => format!("TFun({}, {})", debug_con(d, depth+1), debug_con(r, depth+1)),
        expl::Constructor::TCFun(x, _, r) => format!("TCFun({}, {})", x, debug_con(r, depth+1)),
        expl::Constructor::Record(_, fields) => format!("Record[{}]", fields.iter().map(|(k,_)| debug_con(k, depth+1)).collect::<Vec<_>>().join(",")),
        expl::Constructor::Name(s) => format!("Name({})", s),
        expl::Constructor::Named(id) => format!("Named({})", id),
        expl::Constructor::TRecord(inner) => format!("TRecord({})", debug_con(inner, depth+1)),
        _ => format!("{:?}", std::mem::discriminant(&t.node)),
    }
}

// Helper: check if an explicit type is a "page" type (returns transaction xml) and collect args.
// Works by corifying the type to core IR and checking for Basis.transaction(Basis.xml(Html, _, _)).
fn get_page(
    basis_n: usize,
    t: &expl::LocatedConstructor,
    st: &St,
) -> Option<(expl::LocatedConstructor, Vec<expl::LocatedConstructor>)> {
    get_page_inner(basis_n, t, vec![], st)
}

fn get_page_inner(
    basis_n: usize,
    t: &expl::LocatedConstructor,
    args: Vec<expl::LocatedConstructor>,
    st: &St,
) -> Option<(expl::LocatedConstructor, Vec<expl::LocatedConstructor>)> {
    match &t.node {
        expl::Constructor::App(f, arg) => {
            let is_trans = is_basis_transaction(basis_n, f, st);
            eprintln!("[DEBUG get_page] App: f={}, is_transaction={}", debug_con(f, 0), is_trans);
            if is_trans {
                let is_xml = is_xml_html(basis_n, arg, st);
                eprintln!("[DEBUG get_page] arg={}, is_xml_html={}", debug_con(arg, 0), is_xml);
                if is_xml {
                    return Some((arg.as_ref().clone(), args));
                }
            }
            None
        }
        expl::Constructor::TFun(dom, ran) => {
            eprintln!("[DEBUG get_page] TFun: recursing into ran");
            let mut new_args = args;
            new_args.push(*dom.clone());
            get_page_inner(basis_n, ran, new_args, st)
        }
        other => {
            eprintln!("[DEBUG get_page] no match: {:?}", std::mem::discriminant(other));
            None
        }
    }
}

/// Check if `f` is `Basis.transaction` — handles both ModProj and Named forms.
fn is_basis_transaction(basis_n: usize, f: &expl::LocatedConstructor, st: &St) -> bool {
    match &f.node {
        expl::Constructor::ModProj(basis, ms, s) => {
            *basis == basis_n && ms.is_empty() && s == "transaction"
        }
        expl::Constructor::Named(n) => {
            // Check via con_ffi_map: explicit ID → (module, name)
            matches!(st.lookup_con_ffi(*n), Some((m, x)) if m == "Basis" && x == "transaction")
        }
        _ => false,
    }
}

fn is_xml_html(basis_n: usize, t: &expl::LocatedConstructor, st: &St) -> bool {
    // Match: xml Html _ _
    // i.e. App(App(App(xml, Record([("Html", _)])), _), _)
    // Handle both ModProj and Named forms for "xml"
    match &t.node {
        expl::Constructor::App(f, _) => {
            match &f.node {
                expl::Constructor::App(f2, _) => {
                    match &f2.node {
                        expl::Constructor::App(f3, xml_arg) => {
                            let is_xml = match &f3.as_ref().node {
                                expl::Constructor::ModProj(basis, ms, s) => {
                                    *basis == basis_n && ms.is_empty() && s == "xml"
                                }
                                expl::Constructor::Named(n) => {
                                    let ffi = st.lookup_con_ffi(*n);
                                    eprintln!("[DEBUG is_xml_html] Named({}) → {:?}", n, ffi);
                                    matches!(ffi, Some((m, x)) if m == "Basis" && x == "xml")
                                }
                                _ => false,
                            };
                            if is_xml {
                                // Check xml_arg is the Html row: [Html = ()]
                                // In explicit IR, this appears as:
                                //   Record(_, [("Html", _)]) — a direct row literal
                                //   Named(n) where con_ffi_map[n] = ("Basis","html") — the `html` type synonym
                                //   Named(n) that corifies to Record([("Html", _)]) — other elaboration forms
                                let is_html = match &xml_arg.as_ref().node {
                                    expl::Constructor::Record(_, xcs) if xcs.len() == 1 => {
                                        matches!(&xcs[0].0.node, expl::Constructor::Name(n) if n == "Html")
                                    }
                                    expl::Constructor::Named(n) => {
                                        // Check if it's the "html" type synonym from Basis
                                        if matches!(st.lookup_con_ffi(*n), Some((m, x)) if m == "Basis" && x == "html") {
                                            true
                                        } else {
                                            // Try corifying and checking for Record [Html = ...]
                                            let core_con = corify_con(st, xml_arg.as_ref().clone());
                                            matches!(&core_con.node, core_ir::Constructor::Record(_, fields)
                                                if fields.len() == 1 &&
                                                   matches!(&fields[0].0.node, core_ir::Constructor::Name(n) if n == "Html"))
                                        }
                                    }
                                    _ => false,
                                };
                                return is_html;
                            } else {
                                false
                            }
                        }
                        _ => false,
                    }
                }
                _ => false,
            }
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// corify_str
// ---------------------------------------------------------------------------

// Returns (declarations, inner_St)
fn corify_str(
    mods: &[String],
    str: expl::LocatedStructure,
    st: &mut St,
    counter: &mut usize,
    settings: &mut Settings,
    errors: &mut ErrorReporter,
) -> (Vec<core_ir::LocatedDeclaration>, St) {
    match str.node {
        expl::Structure::Const(ds) => {
            st.enter(mods.to_vec());
            let mut out_ds: Vec<core_ir::LocatedDeclaration> = Vec::new();
            for d in ds {
                let new_ds = corify_decl(mods, d, st, counter, settings, errors);
                out_ds.extend(new_ds);
            }
            let inner_flat = st.leave();
            let inner_st = St::dummy(st.basis, inner_flat);
            (out_ds, inner_st)
        }
        expl::Structure::Var(n) => {
            let inner = st.lookup_str_by_id(n);
            (vec![], inner)
        }
        expl::Structure::Proj(inner_str, x) => {
            let (ds, inner) = corify_str(mods, *inner_str, st, counter, settings, errors);
            let sub = inner.lookup_str_by_name(&x);
            (ds, sub)
        }
        expl::Structure::Fun(_, _, _, _, _) => {
            panic!("Corify of nested functor definition")
        }
        expl::Structure::App(str1, str2) => {
            // Unwind str1 to find functor
            fn unwind_functor(
                str: &expl::Structure,
                st: &St,
            ) -> (String, usize, expl::LocatedStructure) {
                match str {
                    expl::Structure::Var(n) => st.lookup_functor_by_id(*n),
                    expl::Structure::Proj(inner, x) => {
                        let inner_st = unwind_str(&inner.node, st);
                        inner_st.lookup_functor_by_name(x)
                    }
                    _ => panic!("Corify of fancy functor application [2]"),
                }
            }

            fn unwind_str(str: &expl::Structure, st: &St) -> St {
                match str {
                    expl::Structure::Var(n) => st.lookup_str_by_id(*n),
                    expl::Structure::Proj(inner, x) => {
                        let inner_st = unwind_str(&inner.node, st);
                        inner_st.lookup_str_by_name(x)
                    }
                    _ => panic!("Corify of fancy functor application [1]"),
                }
            }

            let (xa, na, body) = unwind_functor(&str1.node, st);

            // Freshen all named ids in the functor body to avoid id capture.
            let body = crate::explicit::expl_rename::rename(counter, &xa, na, body);

            let (ds1, inner_prime) = corify_str(mods, *str2, st, counter, settings, errors);

            // Bind the argument
            st.bind_str(&xa, na, &inner_prime);
            let (ds2, inner) = corify_str(mods, body, st, counter, settings, errors);

            // Bind the argument in inner too
            // (in SML: inner = St.bindStr inner xa na inner')
            // We approximate by constructing a new St with xa bound
            let mut inner_with_arg = inner;
            inner_with_arg.bind_str(&xa, na, &inner_prime);

            let mut all_ds = ds1;
            all_ds.extend(ds2);
            (all_ds, inner_with_arg)
        }
    }
}

// ---------------------------------------------------------------------------
// max_name: compute max id across all declarations
// ---------------------------------------------------------------------------

fn max_name_str(str: &expl::Structure) -> usize {
    match str {
        expl::Structure::Const(ds) => max_name(ds),
        expl::Structure::Var(n) => *n,
        expl::Structure::Proj(s, _) => max_name_str(&s.node),
        expl::Structure::Fun(_, _, _, _, body) => max_name_str(&body.node),
        expl::Structure::App(s1, s2) => max_name_str(&s1.node).max(max_name_str(&s2.node)),
    }
}

fn max_name(ds: &[expl::LocatedDeclaration]) -> usize {
    ds.iter().fold(0, |acc, d| {
        let n = match &d.node {
            expl::Declaration::Constructor(_, n, _, _) => *n,
            expl::Declaration::Datatype(dts) => dts.iter().map(|dt| dt.id).max().unwrap_or(0),
            expl::Declaration::DatatypeImp { id: n, .. } => *n,
            expl::Declaration::Val(_, n, _, _) => *n,
            expl::Declaration::ValRec(vis) => vis.iter().map(|(_, n, _, _)| *n).max().unwrap_or(0),
            expl::Declaration::Signature(_, n, _) => *n,
            expl::Declaration::Structure(_, n, _, str) => (*n).max(max_name_str(&str.node)),
            expl::Declaration::FfiStr(_, n, _) => *n,
            expl::Declaration::Export(_, _, _) => 0,
            expl::Declaration::Table { name_id: n, .. } => *n,
            expl::Declaration::Sequence(_, _, n) => *n,
            expl::Declaration::View(_, _, n, _, _) => *n,
            expl::Declaration::Index(_, _) => 0,
            expl::Declaration::Database(_) => 0,
            expl::Declaration::Cookie(_, _, n, _) => *n,
            expl::Declaration::Style(_, _, n) => *n,
            expl::Declaration::Task(_, _) => 0,
            expl::Declaration::Policy(_) => 0,
            expl::Declaration::OnError(_, _, _) => 0,
            expl::Declaration::Ffi(_, n, _, _) => *n,
        };
        acc.max(n)
    })
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

pub fn corify(
    file: expl::File,
    settings: &mut Settings,
    errors: &mut ErrorReporter,
) -> Option<core_ir::File> {
    let mut counter = max_name(&file) + 1;
    let mut st = St::empty();

    let mut out: Vec<core_ir::LocatedDeclaration> = Vec::new();
    for d in file {
        let ds = corify_decl(&[], d, &mut st, &mut counter, settings, errors);
        out.extend(ds);
    }

    if errors.has_errors() {
        None
    } else {
        Some(out)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core as core_ir;
    use crate::core::Constructor;
    use crate::error_types::Located;

    #[test]
    fn do_restify_empty_mods_identity() {
        let s = Settings::default();
        let out = do_restify(&s, &PathKind::Any, &[], "foo");
        assert_eq!(out, "foo");
    }

    #[test]
    fn do_restify_strips_wrap_prefix() {
        let s = Settings::default();
        let out = do_restify(&s, &PathKind::Any, &[], "wrap_foo");
        assert_eq!(out, "foo");
    }

    #[test]
    fn do_restify_with_mods_reversed() {
        let s = Settings::default();
        let mods: Vec<String> = vec!["a".into(), "b".into()];
        let out = do_restify(&s, &PathKind::Any, &mods, "x");
        assert_eq!(out, "b/a/x");
    }

    #[test]
    fn do_restify_removes_dollar() {
        let s = Settings::default();
        let out = do_restify(&s, &PathKind::Any, &[], "foo$bar");
        assert_eq!(out, "foobar");
    }

    #[test]
    fn relify_slash_to_underscore() {
        assert_eq!(relify("a/b"), "a_b");
    }

    #[test]
    fn relify_no_slash_unchanged() {
        assert_eq!(relify("ab"), "ab");
    }

    #[test]
    fn alloc_increments() {
        let mut c = 0usize;
        assert_eq!(alloc(&mut c), 0);
        assert_eq!(alloc(&mut c), 1);
        assert_eq!(alloc(&mut c), 2);
    }

    #[test]
    fn is_transactional_basis_transaction() {
        let span = loc_dummy();
        let ffi = Located::new(
            Constructor::Ffi("Basis".into(), "transaction".into()),
            span.clone(),
        );
        let arg = Located::new(Constructor::Unit, span.clone());
        let app = Located::new(Constructor::App(Box::new(ffi), Box::new(arg)), span);
        assert!(is_transactional(&app));
    }

    #[test]
    fn is_transactional_ffi_int_false() {
        let c = Located::new(Constructor::Ffi("Basis".into(), "int".into()), loc_dummy());
        assert!(!is_transactional(&c));
    }

    #[test]
    fn classify_datatype_core_enum() {
        let xncs: Vec<(String, usize, Option<core_ir::LocatedConstructor>)> =
            vec![("A".into(), 0, None), ("B".into(), 1, None)];
        assert_eq!(classify_datatype_core(&xncs), DatatypeKind::Enum);
    }

    #[test]
    fn classify_datatype_core_option() {
        let unit = Located::new(Constructor::Unit, loc_dummy());
        let xncs: Vec<(String, usize, Option<core_ir::LocatedConstructor>)> =
            vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
        assert_eq!(classify_datatype_core(&xncs), DatatypeKind::Option);
    }

    #[test]
    fn classify_datatype_core_default() {
        let unit = Located::new(Constructor::Unit, loc_dummy());
        let xncs: Vec<(String, usize, Option<core_ir::LocatedConstructor>)> =
            vec![("C".into(), 0, Some(unit))];
        assert_eq!(classify_datatype_core(&xncs), DatatypeKind::Default);
    }

    #[test]
    fn flattening_name_normal() {
        let f = Flattening::new_normal(vec!["m".into(), "n".into()]);
        assert_eq!(f.name(), vec!["m", "n"]);
    }
}
