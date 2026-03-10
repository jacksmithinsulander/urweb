//! Monoize pass: Core → Mono conversion.
//!
//! Eliminates polymorphism by specializing every polymorphic function and
//! datatype at its call sites. Translates Core types/expressions/declarations
//! to their Mono counterparts.
//!
//! Mirrors `monoize.sml`.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use crate::core::{
    self, Constructor as CC, Declaration as CD, Expression as CE, LocatedConstructor,
    LocatedDeclaration, LocatedExpression, LocatedPattern, Pattern as CP,
    PatternConstructor as CPC,
};
use crate::datatype_kind::DatatypeKind;
use crate::error_types::{Located, Span};
use crate::monomorphized::utilities::classify_datatype as classify_datatype_mono;
use crate::monomorphized::{
    self as mono, BinopIntness, CaseMeta, DatatypeDecl as MonoDatatypeDecl, DatatypeDef,
    DatatypeRef, Decl, Exp, LocDecl, LocExp, LocPat, LocTyp, Pat, PatCon, Policy, Typ,
};
use crate::primitives::Prim;
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Environment for monoize (includes de Bruijn expression stack)
// ---------------------------------------------------------------------------

/// The type environment threaded through monoize.
///
/// Tracks both named (global) and relative (de Bruijn) value bindings,
/// so that we can look up types of Core expressions during translation.
#[derive(Clone)]
struct Env {
    /// De Bruijn expression variable types (innermost first).
    rel_e: Vec<LocatedConstructor>,
    /// Named values: id → (name, type, source_path).
    named_e: HashMap<usize, (String, LocatedConstructor, String)>,
    /// Datatypes: id → (name, type_params, constructors).
    datatypes: HashMap<
        usize,
        (
            String,
            Vec<String>,
            Vec<(String, usize, Option<LocatedConstructor>)>,
        ),
    >,
    /// Named constructors: id → optional definition.
    named_c: HashMap<usize, Option<LocatedConstructor>>,
}

impl Env {
    fn empty() -> Self {
        Env {
            rel_e: Vec::new(),
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            named_c: HashMap::new(),
        }
    }

    fn push_e_rel(mut self, typ: LocatedConstructor) -> Self {
        self.rel_e.push(typ);
        self
    }

    #[allow(dead_code)]
    fn lookup_e_rel(&self, n: usize) -> Option<&LocatedConstructor> {
        let len = self.rel_e.len();
        if n < len {
            Some(&self.rel_e[len - 1 - n])
        } else {
            None
        }
    }

    fn push_e_named(
        mut self,
        name: String,
        id: usize,
        typ: LocatedConstructor,
        src: String,
    ) -> Self {
        self.named_e.insert(id, (name, typ, src));
        self
    }

    fn lookup_e_named(&self, id: usize) -> Option<&(String, LocatedConstructor, String)> {
        self.named_e.get(&id)
    }

    fn push_datatype(
        mut self,
        id: usize,
        name: String,
        params: Vec<String>,
        constrs: Vec<(String, usize, Option<LocatedConstructor>)>,
    ) -> Self {
        self.datatypes.insert(id, (name, params, constrs));
        self
    }

    fn lookup_datatype(
        &self,
        id: usize,
    ) -> Option<&(
        String,
        Vec<String>,
        Vec<(String, usize, Option<LocatedConstructor>)>,
    )> {
        self.datatypes.get(&id)
    }

    fn push_c_named(mut self, id: usize, def: Option<LocatedConstructor>) -> Self {
        self.named_c.insert(id, def);
        self
    }

    /// Extend the environment with all bindings introduced by a Core declaration.
    fn decl_binds(self, decl: &LocatedDeclaration) -> Self {
        let loc = decl.span.clone();
        match &decl.node {
            CD::Constructor(_, id, _, c) => self.push_c_named(*id, Some(c.clone())),
            CD::Datatype(dts) => dts.iter().fold(self, |env, dt| {
                let env = env.push_datatype(
                    dt.id,
                    dt.name.clone(),
                    dt.params.clone(),
                    dt.constrs.clone(),
                );
                env.push_c_named(dt.id, None)
            }),
            CD::Val(x, n, t, _, s) => self.push_e_named(x.clone(), *n, t.clone(), s.clone()),
            CD::ValRec(vis) => vis.iter().fold(self, |env, (x, n, t, _, s)| {
                env.push_e_named(x.clone(), *n, t.clone(), s.clone())
            }),
            CD::Export(_, _, _) => self,
            CD::Table { sql_name, id, .. } => {
                // Table value type: Basis.string
                let t = Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone());
                self.push_e_named(sql_name.clone(), *id, t, sql_name.clone())
            }
            CD::Sequence(x, n, s) => {
                let t = Located::new(CC::Ffi("Basis".into(), "sql_sequence".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::View(x, n, s, _, _) => {
                let t = Located::new(CC::Ffi("Basis".into(), "sql_view".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::Cookie(x, n, _, s) => {
                let t = Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::Style(x, n, s) => {
                let t = Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone());
                self.push_e_named(x.clone(), *n, t, s.clone())
            }
            CD::Index(_, _) | CD::Database(_) | CD::Task(_, _) | CD::Policy(_) | CD::OnError(_) => {
                self
            }
        }
    }

    #[allow(dead_code)]
    fn bind_file(self, ds: &[LocatedDeclaration]) -> Self {
        ds.iter().fold(self, |env, d| env.decl_binds(d))
    }
}

// ---------------------------------------------------------------------------
// Fm: function-map for generated helper functions (MonoFooify.Fm)
// ---------------------------------------------------------------------------

/// A record for one generated helper function (DValRec entry).
type FmDecl = (String, usize, LocTyp, LocExp, String);

/// Simplified version of MonoFooify.Fm.
///
/// Accumulates lazily-generated helper functions (for URL/attribute encoding
/// of polymorphic types). Each call to monoExp may extend the Fm.
#[derive(Clone)]
struct Fm {
    count: usize,
    decls: Vec<FmDecl>,
}

impl Fm {
    fn empty(start: usize) -> Self {
        Fm {
            count: start,
            decls: Vec::new(),
        }
    }

    /// Allocate a fresh function id.
    fn fresh_name(&mut self) -> usize {
        let n = self.count;
        self.count += 1;
        n
    }

    /// Drain accumulated declarations as a single DValRec (if any), resetting the list.
    fn drain_decls(&mut self, loc: &Span) -> Vec<LocDecl> {
        if self.decls.is_empty() {
            Vec::new()
        } else {
            let ds = std::mem::take(&mut self.decls);
            vec![Located::new(Decl::ValRec(ds), loc.clone())]
        }
    }
}

// ---------------------------------------------------------------------------
// Name extraction
// ---------------------------------------------------------------------------

/// Extract a string field name from a Core constructor (should be CName s).
fn mono_name(con: &LocatedConstructor) -> String {
    match &con.node {
        CC::Name(s) => s.clone(),
        _ => "?".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Type translation: mono_type
// ---------------------------------------------------------------------------

/// Compute the head function and all arguments of a nested App chain.
///
/// Returns (head, args) where args[0] is the first applied argument.
fn strip_apps<'a>(
    con: &'a core::Constructor,
    args: &mut Vec<&'a LocatedConstructor>,
) -> &'a core::Constructor {
    match con {
        CC::App(f, arg) => {
            // We collect in reverse; caller must reverse.
            args.push(arg.as_ref());
            strip_apps(&f.node, args)
        }
        other => other,
    }
}

/// Translate a Core constructor (type) to a Mono type.
///
/// `dtmap` prevents infinite loops when translating recursive datatypes.
///
/// Mirrors `monoType` in `monoize.sml`.
fn mono_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    con: &LocatedConstructor,
) -> LocTyp {
    let loc = con.span.clone();
    use CC::*;
    match &con.node {
        // TFun → Mono.TFun
        TFun(c1, c2) => Located::new(
            Typ::Fun(
                Box::new(mono_type(env, dtmap, c1)),
                Box::new(mono_type(env, dtmap, c2)),
            ),
            loc,
        ),

        // Polymorphic TFun — error (shouldn't appear after monomorphisation)
        TCFun(_, _, _) => dummy_typ(&loc),

        // TRecord: rows of kind KType → Mono.TRecord
        TRecord(row) => mono_type_row(env, dtmap, &row.node, &loc),

        // Named datatype application
        Named(n) => {
            if let Some(r) = dtmap.get(n) {
                return Located::new(Typ::Datatype(*n, r.clone()), loc);
            }
            let r: DatatypeRef = Arc::new(Mutex::new(DatatypeDef {
                kind: DatatypeKind::Default,
                constrs: Vec::new(),
            }));
            dtmap.insert(*n, r.clone());
            if let Some((_, xs, xncs)) = env.lookup_datatype(*n) {
                if xs.is_empty() {
                    let constrs: Vec<_> = xncs
                        .iter()
                        .map(|(x, cn, to)| {
                            (
                                x.clone(),
                                *cn,
                                to.as_ref().map(|t| mono_type(env, dtmap, t)),
                            )
                        })
                        .collect();
                    let kind = classify_datatype_mono(&constrs);
                    *r.lock().unwrap() = DatatypeDef { kind, constrs };
                }
            }
            Located::new(Typ::Datatype(*n, r), loc)
        }

        // FFI types
        Ffi(m, x) => mono_type_ffi(m, x, &loc),

        // App chain: peel off all arguments, check head
        App(_, _) => {
            let mut args = Vec::new();
            let head = strip_apps(&con.node, &mut args);
            args.reverse(); // args[0] = first applied
            mono_type_app(env, dtmap, head, &args, &loc)
        }

        // Anything else is a poly error (Rel, Name, Record, Concat, etc.)
        _ => dummy_typ(&loc),
    }
}

/// Translate a record row constructor to Mono.TRecord.
fn mono_type_row(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    row: &core::Constructor,
    loc: &Span,
) -> LocTyp {
    match row {
        CC::Record(_, fields) => {
            let mut xcs: Vec<(String, LocTyp)> = fields
                .iter()
                .map(|(name_con, t)| (mono_name(name_con), mono_type(env, dtmap, t)))
                .collect();
            xcs.sort_by(|(a, _), (b, _)| a.cmp(b));
            Located::new(Typ::Record(xcs), loc.clone())
        }
        // Empty record row
        _ => Located::new(Typ::Record(Vec::new()), loc.clone()),
    }
}

/// Translate a bare FFI type name to a Mono type.
fn mono_type_ffi(m: &str, x: &str, loc: &Span) -> LocTyp {
    if m != "Basis" {
        return Located::new(Typ::Ffi(m.to_string(), x.to_string()), loc.clone());
    }
    match x {
        "unit" => Located::new(Typ::Record(Vec::new()), loc.clone()),
        // Types that become Basis.string
        "page" | "xhead" | "xbody" | "xtable" | "xtr" | "xform" | "url" | "mimeType"
        | "css_class" | "css_value" | "css_property" | "css_style" | "id" | "requestHeader"
        | "responseHeader" | "envVar" | "meta" | "data_attr_kind" | "data_attr" | "dml"
        | "sql_sequence" | "sql_relop" | "sql_direction" | "sql_limit" | "sql_offset" => {
            Located::new(
                Typ::Ffi("Basis".to_string(), "string".to_string()),
                loc.clone(),
            )
        }
        _ => Located::new(Typ::Ffi(m.to_string(), x.to_string()), loc.clone()),
    }
}

/// Translate a type-application chain (head applied to args) to a Mono type.
fn mono_type_app(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    head: &core::Constructor,
    args: &[&LocatedConstructor],
    loc: &Span,
) -> LocTyp {
    let last = args.last();
    match head {
        CC::Ffi(m, x) if m == "Basis" => {
            let string_t = || {
                Located::new(
                    Typ::Ffi("Basis".to_string(), "string".to_string()),
                    loc.clone(),
                )
            };
            let unit_t = || Located::new(Typ::Record(Vec::new()), loc.clone());
            match x.as_str() {
                "option" => {
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Option(Box::new(inner)), loc.clone())
                }
                "list" => {
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::List(Box::new(inner)), loc.clone())
                }
                "transaction" => {
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Fun(Box::new(unit_t()), Box::new(inner)), loc.clone())
                }
                "source" => Located::new(Typ::Source, loc.clone()),
                "signal" => {
                    let inner = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    Located::new(Typ::Signal(Box::new(inner)), loc.clone())
                }
                "http_cookie" => string_t(),
                "channel" => Located::new(
                    Typ::Ffi("Basis".to_string(), "channel".to_string()),
                    loc.clone(),
                ),
                // Types that map to string regardless of arguments
                "xml"
                | "xhtml"
                | "sql_table"
                | "sql_view"
                | "sql_query"
                | "sql_query1"
                | "sql_from_items"
                | "sql_exp"
                | "sql_expw"
                | "sql_window_function"
                | "primary_key"
                | "sql_constraints"
                | "sql_constraint"
                | "linkable"
                | "sql_order_by"
                | "propagation_mode"
                | "serialized"
                | "sql_injectable_prim"
                | "sql_injectable"
                | "sql_unary"
                | "sql_binary"
                | "sql_aggregate"
                | "sql_nfunc"
                | "sql_ufunc"
                | "sql_bfunc"
                | "sql_partition"
                | "sql_window"
                | "trigrammable" => string_t(),
                // Types that map to unit record
                "monad" | "sql_subset" | "sql_summable" | "sql_maxable" | "sql_arith"
                | "nullify" | "fieldsOf" => unit_t(),
                // eq: t -> t -> bool
                "eq" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
                    let inner =
                        Located::new(Typ::Fun(Box::new(t.clone()), Box::new(bool_t)), loc.clone());
                    Located::new(Typ::Fun(Box::new(t), Box::new(inner)), loc.clone())
                }
                // num: record with arithmetic operations
                "num" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    num_ty(t, loc)
                }
                // ord: record with comparison operations
                "ord" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    ord_ty(t, loc)
                }
                // show: t -> string
                "show" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
                    Located::new(Typ::Fun(Box::new(t), Box::new(s)), loc.clone())
                }
                // read: {Read: string -> option t, ReadError: string -> t}
                "read" => {
                    let t = last
                        .map(|t| mono_type(env, dtmap, t))
                        .unwrap_or(dummy_typ(loc));
                    read_ty(t, loc)
                }
                // matching: (string * string)
                "matching" => {
                    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
                    Located::new(
                        Typ::Record(vec![("1".into(), s.clone()), ("2".into(), s)]),
                        loc.clone(),
                    )
                }
                _ => dummy_typ(loc),
            }
        }
        // Named(n) applied to args — polymorphic datatype, not supported
        _ => dummy_typ(loc),
    }
}

fn num_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let ft = || {
        Located::new(
            Typ::Fun(Box::new(t.clone()), Box::new(t.clone())),
            loc.clone(),
        )
    };
    let ft2 = || Located::new(Typ::Fun(Box::new(t.clone()), Box::new(ft())), loc.clone());
    Located::new(
        Typ::Record(vec![
            ("Zero".into(), t.clone()),
            ("Neg".into(), ft()),
            ("Plus".into(), ft2()),
            ("Minus".into(), ft2()),
            ("Times".into(), ft2()),
            ("Div".into(), ft2()),
            ("Mod".into(), ft2()),
            ("Pow".into(), ft2()),
        ]),
        loc.clone(),
    )
}

fn ord_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp_t = || {
        Located::new(
            Typ::Fun(
                Box::new(t.clone()),
                Box::new(Located::new(
                    Typ::Fun(Box::new(t.clone()), Box::new(bool_t.clone())),
                    loc.clone(),
                )),
            ),
            loc.clone(),
        )
    };
    Located::new(
        Typ::Record(vec![("Lt".into(), cmp_t()), ("Le".into(), cmp_t())]),
        loc.clone(),
    )
}

fn read_ty(t: LocTyp, loc: &Span) -> LocTyp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let opt_t = Located::new(Typ::Option(Box::new(t.clone())), loc.clone());
    let read_fn = Located::new(Typ::Fun(Box::new(s.clone()), Box::new(opt_t)), loc.clone());
    let read_err_fn = Located::new(Typ::Fun(Box::new(s), Box::new(t)), loc.clone());
    Located::new(
        Typ::Record(vec![
            ("Read".into(), read_fn),
            ("ReadError".into(), read_err_fn),
        ]),
        loc.clone(),
    )
}

fn dummy_typ(loc: &Span) -> LocTyp {
    // Use a zero-element record as the dummy type (unit in Mono)
    Located::new(Typ::Record(Vec::new()), loc.clone())
}

// ---------------------------------------------------------------------------
// Pattern translation
// ---------------------------------------------------------------------------

fn mono_pat_con(pc: &CPC) -> PatCon {
    match pc {
        CPC::Var(n) => PatCon::Var(*n),
        CPC::Ffi {
            module,
            datatyp,
            params: _,
            con,
            arg,
            kind: _,
        } => PatCon::Ffi {
            module: module.clone(),
            datatyp: datatyp.clone(),
            con: con.clone(),
            arg: arg
                .as_ref()
                .map(|_t| Located::new(Typ::Record(Vec::new()), Span::dummy())), // simplified
        },
    }
}

/// Translate a Core pattern to a Mono pattern.
///
/// Mirrors `monoPat` in `monoize.sml`.
fn mono_pat(env: &Env, dtmap: &mut HashMap<usize, DatatypeRef>, pat: &LocatedPattern) -> LocPat {
    let loc = pat.span.clone();
    match &pat.node {
        CP::Var(x, t) => Located::new(Pat::Var(x.clone(), mono_type(env, dtmap, t)), loc),
        CP::Prim(p) => Located::new(Pat::Prim(p.clone()), loc),
        CP::Constructor(dk, pc, targs, po) => {
            if targs.is_empty() {
                // Nullary or payload constructor without type args
                let mo = po.as_ref().map(|p| Box::new(mono_pat(env, dtmap, p)));
                Located::new(Pat::Con(*dk, mono_pat_con(pc), mo), loc)
            } else if targs.len() == 1 {
                // Option-like or list-like patterns
                match pc {
                    CPC::Ffi {
                        module,
                        datatyp,
                        con,
                        ..
                    } if module == "Basis" && datatyp == "list" => {
                        // list None pattern → PNone(listify t)
                        let inner_t = mono_type(env, dtmap, &targs[0]);
                        let lt = listify(inner_t, &loc);
                        if po.is_none() {
                            Located::new(Pat::None(lt), loc)
                        } else {
                            let p = mono_pat(env, dtmap, po.as_ref().unwrap());
                            Located::new(Pat::Some(lt, Box::new(p)), loc)
                        }
                    }
                    _ => {
                        // Option pattern
                        let t = mono_type(env, dtmap, &targs[0]);
                        if po.is_none() {
                            Located::new(Pat::None(t), loc)
                        } else {
                            let p = mono_pat(env, dtmap, po.as_ref().unwrap());
                            Located::new(Pat::Some(t, Box::new(p)), loc)
                        }
                    }
                }
            } else {
                // Polymorphic constructor — error
                Located::new(Pat::Prim(Prim::Int(0)), loc)
            }
        }
        CP::Record(fields) => {
            let fs: Vec<_> = fields
                .iter()
                .map(|(name, p, t)| {
                    (
                        name.clone(),
                        mono_pat(env, dtmap, p),
                        mono_type(env, dtmap, t),
                    )
                })
                .collect();
            Located::new(Pat::Record(fs), loc)
        }
    }
}

fn listify(t: LocTyp, loc: &Span) -> LocTyp {
    Located::new(
        Typ::Record(vec![
            ("1".into(), t.clone()),
            (
                "2".into(),
                Located::new(Typ::List(Box::new(t)), loc.clone()),
            ),
        ]),
        loc.clone(),
    )
}

// ---------------------------------------------------------------------------
// Type class instance builders
// ---------------------------------------------------------------------------

/// Build `EBinop(Int, op, ERel(1), ERel(0))` — binary int op on two args.
fn int_binop(op: &str, loc: &Span) -> LocExp {
    Located::new(
        Exp::Binop(
            BinopIntness::Int,
            op.into(),
            Box::new(Located::new(Exp::Rel(1), loc.clone())),
            Box::new(Located::new(Exp::Rel(0), loc.clone())),
        ),
        loc.clone(),
    )
}

/// Build `EBinop(NotInt, op, ERel(1), ERel(0))` — binary float op on two args.
fn float_binop(op: &str, loc: &Span) -> LocExp {
    Located::new(
        Exp::Binop(
            BinopIntness::NotInt,
            op.into(),
            Box::new(Located::new(Exp::Rel(1), loc.clone())),
            Box::new(Located::new(Exp::Rel(0), loc.clone())),
        ),
        loc.clone(),
    )
}

/// Build `\x t. \y t. body` — a two-argument lambda with type `t`.
fn binary_abs(t: LocTyp, result_t: LocTyp, body: LocExp, loc: &Span) -> LocExp {
    let inner = Located::new(
        Exp::Abs("y".into(), t.clone(), result_t.clone(), Box::new(body)),
        loc.clone(),
    );
    Located::new(
        Exp::Abs(
            "x".into(),
            t.clone(),
            Located::new(Typ::Fun(Box::new(t), Box::new(result_t)), loc.clone()),
            Box::new(inner),
        ),
        loc.clone(),
    )
}

/// Build a num-typeclass record for type `t` with the given operations.
fn num_ex(
    t: LocTyp,
    zero: LocExp,
    neg: LocExp,
    plus: LocExp,
    minus: LocExp,
    times: LocExp,
    div: LocExp,
    modf: LocExp,
    pow: LocExp,
    loc: &Span,
) -> LocExp {
    let ft = Located::new(
        Typ::Fun(Box::new(t.clone()), Box::new(t.clone())),
        loc.clone(),
    );
    let ft2 = Located::new(
        Typ::Fun(Box::new(t.clone()), Box::new(ft.clone())),
        loc.clone(),
    );
    Located::new(
        Exp::Record(vec![
            ("Zero".into(), zero, t.clone()),
            ("Neg".into(), neg, ft.clone()),
            ("Plus".into(), plus, ft2.clone()),
            ("Minus".into(), minus, ft2.clone()),
            ("Times".into(), times, ft2.clone()),
            ("Div".into(), div, ft2.clone()),
            ("Mod".into(), modf, ft2.clone()),
            ("Pow".into(), pow, ft2),
        ]),
        loc.clone(),
    )
}

/// Build an ord-typeclass record `{Lt, Le}` for type `t`.
fn ord_ex(lt: LocExp, le: LocExp, loc: &Span) -> LocExp {
    // Placeholder type — ord records have function types but we don't track them here.
    let unit_t = Located::new(Typ::Record(vec![]), loc.clone());
    Located::new(
        Exp::Record(vec![
            ("Lt".into(), lt, unit_t.clone()),
            ("Le".into(), le, unit_t),
        ]),
        loc.clone(),
    )
}

/// Build `\x t. body_of_x` — a single-argument lambda.
fn unary_abs(x_name: &str, t: LocTyp, result_t: LocTyp, body: LocExp, loc: &Span) -> LocExp {
    Located::new(
        Exp::Abs(x_name.into(), t, result_t, Box::new(body)),
        loc.clone(),
    )
}

/// Generate the concrete `eq_X` function for a type: `\x y. x == y`.
fn make_eq_fun(t: LocTyp, op: &str, loc: &Span) -> LocExp {
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let body = int_binop(op, loc);
    binary_abs(t, bool_t, body, loc)
}

/// Generate the concrete `eq_string` function: `\x y. !strcmp(x, y) == 0`.
fn make_eq_string_fun(loc: &Span) -> LocExp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    // !strcmp(x, y) — use "!strcmp" as a binop (as SML does with EBinop(NotInt, "!strcmp", ...))
    let body = Located::new(
        Exp::Binop(
            BinopIntness::NotInt,
            "!strcmp".into(),
            Box::new(Located::new(Exp::Rel(1), loc.clone())),
            Box::new(Located::new(Exp::Rel(0), loc.clone())),
        ),
        loc.clone(),
    );
    binary_abs(s, bool_t, body, loc)
}

/// Generate a concrete binary-predicate function: `\x y. ffi_func(x, y)`.
fn make_ffi_cmp_fun(m: &str, f: &str, t: LocTyp, loc: &Span) -> LocExp {
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let body = Located::new(
        Exp::FfiApp(
            m.into(),
            f.into(),
            vec![
                (Located::new(Exp::Rel(1), loc.clone()), t.clone()),
                (Located::new(Exp::Rel(0), loc.clone()), t.clone()),
            ],
        ),
        loc.clone(),
    );
    binary_abs(t, bool_t, body, loc)
}

/// Generate `num_int`: the num record for Basis.int.
fn make_num_int(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
    let zero = Located::new(Exp::Prim(Prim::Int(0)), loc.clone());
    let neg = unary_abs(
        "x",
        t.clone(),
        t.clone(),
        Located::new(
            Exp::Unop("-".into(), Box::new(Located::new(Exp::Rel(0), loc.clone()))),
            loc.clone(),
        ),
        loc,
    );
    let b_plus = binary_abs(t.clone(), t.clone(), int_binop("+", loc), loc);
    let b_minus = binary_abs(t.clone(), t.clone(), int_binop("-", loc), loc);
    let b_times = binary_abs(t.clone(), t.clone(), int_binop("*", loc), loc);
    let b_div = binary_abs(t.clone(), t.clone(), int_binop("/", loc), loc);
    let b_mod = binary_abs(t.clone(), t.clone(), int_binop("%", loc), loc);
    let b_pow = binary_abs(t.clone(), t.clone(), int_binop("powl", loc), loc);
    num_ex(
        t, zero, neg, b_plus, b_minus, b_times, b_div, b_mod, b_pow, loc,
    )
}

/// Generate `num_float`: the num record for Basis.float.
fn make_num_float(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "float".into()), loc.clone());
    let zero = Located::new(Exp::Prim(Prim::Float(0.0)), loc.clone());
    let neg = unary_abs(
        "x",
        t.clone(),
        t.clone(),
        Located::new(
            Exp::Unop("-".into(), Box::new(Located::new(Exp::Rel(0), loc.clone()))),
            loc.clone(),
        ),
        loc,
    );
    let b_plus = binary_abs(t.clone(), t.clone(), float_binop("+", loc), loc);
    let b_minus = binary_abs(t.clone(), t.clone(), float_binop("-", loc), loc);
    let b_times = binary_abs(t.clone(), t.clone(), float_binop("*", loc), loc);
    let b_div = binary_abs(t.clone(), t.clone(), float_binop("fdiv", loc), loc);
    let b_mod = binary_abs(t.clone(), t.clone(), float_binop("fmod", loc), loc);
    let b_pow = binary_abs(t.clone(), t.clone(), float_binop("powf", loc), loc);
    num_ex(
        t, zero, neg, b_plus, b_minus, b_times, b_div, b_mod, b_pow, loc,
    )
}

/// Generate `ord_int`: the ord record for Basis.int.
fn make_ord_int(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), int_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_float`: the ord record for Basis.float.
fn make_ord_float(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "float".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), float_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_bool`.
fn make_ord_bool(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let bool_t = t.clone();
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), int_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_char`.
fn make_ord_char(loc: &Span) -> LocExp {
    let t = Located::new(Typ::Ffi("Basis".into(), "char".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let cmp = |op: &str| binary_abs(t.clone(), bool_t.clone(), int_binop(op, loc), loc);
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_string`: {Lt=\x y. strcmp(x,y)<0, Le=\x y. strcmp(x,y)<=0}.
fn make_ord_string(loc: &Span) -> LocExp {
    let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
    let bool_t = Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());
    let zero = Located::new(Exp::Prim(Prim::Int(0)), loc.clone());
    let cmp = |op: &str| {
        // strcmp(x, y) < 0
        let strcmp_body = Located::new(
            Exp::Binop(
                BinopIntness::Int,
                op.into(),
                Box::new(Located::new(
                    Exp::Binop(
                        BinopIntness::NotInt,
                        "strcmp".into(),
                        Box::new(Located::new(Exp::Rel(1), loc.clone())),
                        Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    ),
                    loc.clone(),
                )),
                Box::new(zero.clone()),
            ),
            loc.clone(),
        );
        binary_abs(s.clone(), bool_t.clone(), strcmp_body, loc)
    };
    ord_ex(cmp("<"), cmp("<="), loc)
}

/// Generate `ord_time`: {Lt=lt_time, Le=le_time}.
fn make_ord_ffi_cmp(m: &str, lt_f: &str, le_f: &str, t: LocTyp, loc: &Span) -> LocExp {
    let lt = make_ffi_cmp_fun(m, lt_f, t.clone(), loc);
    let le = make_ffi_cmp_fun(m, le_f, t, loc);
    ord_ex(lt, le, loc)
}

/// Handle `EFfi("Basis", x)` as a concrete type class instance.
/// Returns `Some(mono_exp)` for known patterns, `None` to fall through.
fn mono_basis_ffi(x: &str, loc: &Span) -> Option<LocExp> {
    match x {
        // ---- eq instances ----
        "eq_int" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "int".into()), loc.clone());
            Some(make_eq_fun(t, "==", loc))
        }
        "eq_float" | "eq_bool" | "eq_char" => {
            let ffi_name = match x {
                "eq_float" => "float",
                "eq_bool" => "bool",
                "eq_char" => "char",
                _ => unreachable!(),
            };
            let t = Located::new(Typ::Ffi("Basis".into(), ffi_name.into()), loc.clone());
            Some(make_eq_fun(t, "==", loc))
        }
        "eq_string" => Some(make_eq_string_fun(loc)),
        "eq_time" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "time".into()), loc.clone());
            Some(make_ffi_cmp_fun("Basis", "eq_time", t, loc))
        }
        "eq_calendardate" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "calendardate".into()), loc.clone());
            Some(make_ffi_cmp_fun("Basis", "eq_calendardate", t, loc))
        }
        "eq_clocktime" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "clocktime".into()), loc.clone());
            Some(make_ffi_cmp_fun("Basis", "eq_clocktime", t, loc))
        }

        // ---- num instances ----
        "num_int" => Some(make_num_int(loc)),
        "num_float" => Some(make_num_float(loc)),

        // ---- ord instances ----
        "ord_int" => Some(make_ord_int(loc)),
        "ord_float" => Some(make_ord_float(loc)),
        "ord_bool" => Some(make_ord_bool(loc)),
        "ord_char" => Some(make_ord_char(loc)),
        "ord_string" => Some(make_ord_string(loc)),
        "ord_time" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "time".into()), loc.clone());
            Some(make_ord_ffi_cmp("Basis", "lt_time", "le_time", t, loc))
        }
        "ord_clocktime" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "clocktime".into()), loc.clone());
            Some(make_ord_ffi_cmp(
                "Basis",
                "lt_clocktime",
                "le_clocktime",
                t,
                loc,
            ))
        }
        "ord_calendardate" => {
            let t = Located::new(Typ::Ffi("Basis".into(), "calendardate".into()), loc.clone());
            Some(make_ord_ffi_cmp(
                "Basis",
                "lt_calendardate",
                "le_calendardate",
                t,
                loc,
            ))
        }

        _ => None,
    }
}

/// Peel `CApp` layers: returns `(innermost_expr, type_args_innermost_first)`.
fn peel_capp(e: &LocatedExpression) -> (&LocatedExpression, Vec<&LocatedConstructor>) {
    let mut inner = e;
    let mut args = Vec::new();
    loop {
        match &inner.node {
            CE::CApp(inner_e, c) => {
                args.push(c as &LocatedConstructor);
                inner = inner_e;
            }
            _ => break,
        }
    }
    // args is [outermost_type_arg, ..., innermost_type_arg] — reverse so [0] = first applied
    args.reverse();
    (inner, args)
}

/// Handle ECApp chains over `EFfi("Basis", x)`.
/// Returns `Some(mono_exp)` for known patterns, `None` to fall through.
fn mono_basis_capp(
    env: &Env,
    x: &str,
    targs: &[&LocatedConstructor],
    loc: &Span,
) -> Option<LocExp> {
    let last_t = targs.last();
    let bool_t = || Located::new(Typ::Ffi("Basis".into(), "bool".into()), loc.clone());

    match x {
        // ECApp(EFfi("Basis", "eq"), t) → \f: t->t->bool. f
        "eq" | "mkEq" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let eq_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t), Box::new(bool_t())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    eq_t.clone(),
                    eq_t,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "ne"), t) → \f x y. !(f x y)
        "ne" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let b = bool_t();
            let b2 = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                loc.clone(),
            );
            let eq_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b2.clone())),
                loc.clone(),
            );
            // \f. \x. \y. !(f x y)
            let _app_fy = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let app_fx = Located::new(
                Exp::App(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let body = Located::new(
                Exp::App(
                    Box::new(app_fx),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let not_body = Located::new(Exp::Unop("!".into(), Box::new(body)), loc.clone());
            let inner_y = Located::new(
                Exp::Abs("y".into(), t.clone(), b.clone(), Box::new(not_body)),
                loc.clone(),
            );
            let inner_x = Located::new(
                Exp::Abs("x".into(), t.clone(), b2, Box::new(inner_y)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("f".into(), eq_t.clone(), eq_t, Box::new(inner_x)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "zero"), t) → \r: num t. r.Zero
        "zero" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let num_t = num_ty(t.clone(), loc);
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    "Zero".into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), num_t, t, Box::new(body)),
                loc.clone(),
            ))
        }
        "neg" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let num_t = num_ty(t.clone(), loc);
            let ft = Located::new(Typ::Fun(Box::new(t.clone()), Box::new(t)), loc.clone());
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    "Neg".into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), num_t, ft, Box::new(body)),
                loc.clone(),
            ))
        }
        "plus" | "minus" | "times" | "divide" | "mod" | "pow" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let num_t = num_ty(t.clone(), loc);
            let ft2 = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t.clone()), Box::new(t)),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let field_name = match x {
                "plus" => "Plus",
                "minus" => "Minus",
                "times" => "Times",
                "divide" => "Div",
                "mod" => "Mod",
                "pow" => "Pow",
                _ => unreachable!(),
            };
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    field_name.into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), num_t, ft2, Box::new(body)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "lt"), t) → \r: ord t. r.Lt
        "lt" | "le" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let ord_t = ord_ty(t.clone(), loc);
            let b = bool_t();
            let cmp_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t), Box::new(b)),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let field = if x == "lt" { "Lt" } else { "Le" };
            let body = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                    field.into(),
                ),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("r".into(), ord_t, cmp_t, Box::new(body)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "gt"), t) → \f x y. !(f.Le x y)
        "gt" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let ord_t = ord_ty(t.clone(), loc);
            let b = bool_t();
            let cmp_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let ret_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                loc.clone(),
            );
            // \f: ord t. \x. \y. !(f.Le x y)
            let le = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    "Le".into(),
                ),
                loc.clone(),
            );
            let app_le_x = Located::new(
                Exp::App(
                    Box::new(le),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let app_le_x_y = Located::new(
                Exp::App(
                    Box::new(app_le_x),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let not_body = Located::new(Exp::Unop("!".into(), Box::new(app_le_x_y)), loc.clone());
            let inner_y = Located::new(
                Exp::Abs("y".into(), t.clone(), b, Box::new(not_body)),
                loc.clone(),
            );
            let inner_x = Located::new(
                Exp::Abs("x".into(), t, ret_t, Box::new(inner_y)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("f".into(), ord_t, cmp_t, Box::new(inner_x)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "ge"), t) → \f x y. !(f.Lt x y)
        "ge" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let ord_t = ord_ty(t.clone(), loc);
            let b = bool_t();
            let cmp_t = Located::new(
                Typ::Fun(
                    Box::new(t.clone()),
                    Box::new(Located::new(
                        Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );
            let ret_t = Located::new(
                Typ::Fun(Box::new(t.clone()), Box::new(b.clone())),
                loc.clone(),
            );
            let lt = Located::new(
                Exp::Field(
                    Box::new(Located::new(Exp::Rel(2), loc.clone())),
                    "Lt".into(),
                ),
                loc.clone(),
            );
            let app_lt_x = Located::new(
                Exp::App(
                    Box::new(lt),
                    Box::new(Located::new(Exp::Rel(1), loc.clone())),
                ),
                loc.clone(),
            );
            let app_lt_x_y = Located::new(
                Exp::App(
                    Box::new(app_lt_x),
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            );
            let not_body = Located::new(Exp::Unop("!".into(), Box::new(app_lt_x_y)), loc.clone());
            let inner_y = Located::new(
                Exp::Abs("y".into(), t.clone(), b, Box::new(not_body)),
                loc.clone(),
            );
            let inner_x = Located::new(
                Exp::Abs("x".into(), t, ret_t, Box::new(inner_y)),
                loc.clone(),
            );
            Some(Located::new(
                Exp::Abs("f".into(), ord_t, cmp_t, Box::new(inner_x)),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "show"), t) → \f: t->string. f
        "show" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let s = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let show_t = Located::new(Typ::Fun(Box::new(t), Box::new(s)), loc.clone());
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    show_t.clone(),
                    show_t,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        // ECApp(EFfi("Basis", "read"), t) → \f: read_t. f
        "read" => {
            let t = last_t.map(|c| {
                let mut dtmap = HashMap::new();
                mono_type(env, &mut dtmap, c)
            })?;
            let read_t = read_ty(t, loc);
            Some(Located::new(
                Exp::Abs(
                    "f".into(),
                    read_t.clone(),
                    read_t,
                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                ),
                loc.clone(),
            ))
        }

        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Expression translation: mono_exp
// ---------------------------------------------------------------------------

/// Lift all ERel(n >= depth) by 1 in a Mono expression.
fn lift_exp_in_exp(depth: usize, e: LocExp) -> LocExp {
    crate::monomorphized::utilities::exp::map(e, &|t| t, &|node| match node {
        Exp::Rel(n) if n >= depth => Exp::Rel(n + 1),
        other => other,
    })
}

fn str_exp(s: impl Into<String>, loc: &Span) -> LocExp {
    Located::new(
        Exp::Prim(Prim::String(
            crate::primitives::StringMode::Normal,
            s.into(),
        )),
        loc.clone(),
    )
}

fn unit_exp(loc: &Span) -> LocExp {
    Located::new(Exp::Record(Vec::new()), loc.clone())
}

fn unit_typ(loc: &Span) -> LocTyp {
    Located::new(Typ::Record(Vec::new()), loc.clone())
}

/// Translate a Core expression to a Mono expression.
///
/// Returns `(mono_exp, updated_fm)`. The `Fm` accumulates helper function
/// declarations generated for URL/attribute encoding of polymorphic types.
///
/// Mirrors `monoExp` in `monoize.sml`.
fn mono_exp(env: &Env, fm: &mut Fm, exp: &LocatedExpression) -> LocExp {
    let loc = exp.span.clone();
    match &exp.node {
        // --------------- Primitives ---------------
        CE::Prim(p) => Located::new(Exp::Prim(p.clone()), loc),
        CE::Rel(n) => Located::new(Exp::Rel(*n), loc),
        CE::Named(n) => Located::new(Exp::Named(*n), loc),

        // --------------- Constructors ---------------
        CE::Constructor(dk, pc, targs, opt_e) => {
            if targs.is_empty() {
                let me = opt_e.as_ref().map(|e| Box::new(mono_exp(env, fm, e)));
                Located::new(Exp::Con(*dk, mono_pat_con(pc), me), loc)
            } else if targs.len() == 1 {
                match (pc, opt_e) {
                    (
                        CPC::Ffi {
                            module, datatyp, ..
                        },
                        _,
                    ) if module == "Basis" && datatyp == "list" => {
                        let mut dtmap = HashMap::new();
                        let inner_t = mono_type(env, &mut dtmap, &targs[0]);
                        let lt = listify(inner_t, &loc);
                        if opt_e.is_none() {
                            Located::new(Exp::None(lt), loc)
                        } else {
                            let e = mono_exp(env, fm, opt_e.as_ref().unwrap());
                            Located::new(Exp::Some(lt, Box::new(e)), loc)
                        }
                    }
                    (_, None) => {
                        let mut dtmap = HashMap::new();
                        let t = mono_type(env, &mut dtmap, &targs[0]);
                        Located::new(Exp::None(t), loc)
                    }
                    (_, Some(e)) => {
                        let mut dtmap = HashMap::new();
                        let t = mono_type(env, &mut dtmap, &targs[0]);
                        let me = mono_exp(env, fm, e);
                        Located::new(Exp::Some(t, Box::new(me)), loc)
                    }
                }
            } else {
                // Polymorphic — error
                Located::new(Exp::Prim(Prim::Int(0)), loc)
            }
        }

        // --------------- FFI ---------------
        CE::Ffi(m, x) => {
            // For Basis type class concrete instances, generate implementations.
            if m == "Basis" {
                if let Some(e) = mono_basis_ffi(x, &loc) {
                    return e;
                }
            }
            Located::new(Exp::Ffi(m.clone(), x.clone()), loc)
        }
        CE::FfiApp(m, x, args) => {
            let margs: Vec<_> = args
                .iter()
                .map(|(e, t)| {
                    let mut dtmap = HashMap::new();
                    (mono_exp(env, fm, e), mono_type(env, &mut dtmap, t))
                })
                .collect();
            Located::new(Exp::FfiApp(m.clone(), x.clone(), margs), loc)
        }

        // --------------- Application / Abstraction ---------------
        CE::App(e1, e2) => {
            let me1 = mono_exp(env, fm, e1);
            let me2 = mono_exp(env, fm, e2);
            Located::new(Exp::App(Box::new(me1), Box::new(me2)), loc)
        }
        CE::Abs(x, dom, ran, body) => {
            let mut dtmap = HashMap::new();
            let mdom = mono_type(env, &mut dtmap, dom);
            let mran = mono_type(env, &mut dtmap, ran);
            let env2 = env.clone().push_e_rel(dom.clone());
            let mbody = mono_exp(&env2, fm, body);
            Located::new(Exp::Abs(x.clone(), mdom, mran, Box::new(mbody)), loc)
        }

        // Type application: ECApp (e, _) — strip the type arg, or desugar type class instances.
        CE::CApp(_, _) => {
            let (head, targs) = peel_capp(exp);
            // Check for EFfi("Basis", x) head — desugar type class instances.
            if let CE::Ffi(m, x) = &head.node {
                if m == "Basis" {
                    if let Some(result) = mono_basis_capp(env, x, &targs, &loc) {
                        return result;
                    }
                }
            }
            // Fall through: translate head and strip all type args.
            mono_exp(env, fm, head)
        }

        // Type abstraction: strip completely (unsupported after specialize)
        CE::CAbs(_, _, _) | CE::KAbs(_, _) | CE::KApp(_, _) => {
            Located::new(Exp::Prim(Prim::Int(0)), loc)
        }

        // --------------- Records ---------------
        CE::Record(xets) => {
            let mut mxets: Vec<(String, LocExp, LocTyp)> = xets
                .iter()
                .map(|(name_con, e, t)| {
                    let mut dtmap = HashMap::new();
                    (
                        mono_name(name_con),
                        mono_exp(env, fm, e),
                        mono_type(env, &mut dtmap, t),
                    )
                })
                .collect();
            mxets.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));
            Located::new(Exp::Record(mxets), loc)
        }
        CE::Field(e, x, _) => {
            let me = mono_exp(env, fm, e);
            Located::new(Exp::Field(Box::new(me), mono_name(x)), loc)
        }
        // Record concatenation/cut: not supported at Mono level (should be gone)
        CE::Concat(_, _, _, _) | CE::Cut(_, _, _) | CE::CutMulti(_, _, _) => {
            Located::new(Exp::Prim(Prim::Int(0)), loc)
        }

        // --------------- Case ---------------
        CE::Case(e, arms, meta) => {
            let mut dtmap = HashMap::new();
            let me = mono_exp(env, fm, e);
            let marms: Vec<(LocPat, LocExp)> = arms
                .iter()
                .map(|(p, arm_e)| (mono_pat(env, &mut dtmap, p), mono_exp(env, fm, arm_e)))
                .collect();
            let disc = mono_type(env, &mut dtmap, &meta.disc);
            let result = mono_type(env, &mut dtmap, &meta.result);
            Located::new(
                Exp::Case(Box::new(me), marms, CaseMeta { disc, result }),
                loc,
            )
        }

        // --------------- Write ---------------
        CE::Write(e) => {
            // EWrite e → EAbs("_", unit, unit, EWrite(lift e))
            let me = mono_exp(env, fm, e);
            let un = unit_typ(&loc);
            let lifted = lift_exp_in_exp(0, me);
            Located::new(
                Exp::Abs(
                    "_".into(),
                    un.clone(),
                    un.clone(),
                    Box::new(Located::new(Exp::Write(Box::new(lifted)), loc.clone())),
                ),
                loc,
            )
        }

        // --------------- Closure ---------------
        CE::Closure(n, envs) => {
            let menvs: Vec<LocExp> = envs.iter().map(|e| mono_exp(env, fm, e)).collect();
            Located::new(Exp::Closure(*n, menvs), loc)
        }

        // --------------- Let ---------------
        CE::Let(x, t, e1, e2) => {
            let mut dtmap = HashMap::new();
            let mt = mono_type(env, &mut dtmap, t);
            let me1 = mono_exp(env, fm, e1);
            let env2 = env.clone().push_e_rel(t.clone());
            let me2 = mono_exp(&env2, fm, e2);
            Located::new(Exp::Let(x.clone(), mt, Box::new(me1), Box::new(me2)), loc)
        }

        // --------------- ServerCall ---------------
        CE::ServerCall(n, args, result_t, fmode) => {
            let mut dtmap = HashMap::new();
            let mt = mono_type(env, &mut dtmap, result_t);
            let margs: Vec<LocExp> = args.iter().map(|e| mono_exp(env, fm, e)).collect();

            // Get the function name/path from the env
            let name = env
                .lookup_e_named(*n)
                .map(|(_, _, s)| s.clone())
                .unwrap_or_default();

            // Build URL-encoded call string: name/arg1/arg2/...
            // (simplified: just pass args as Mono EServerCall)
            let call = if margs.is_empty() {
                str_exp(&name, &loc)
            } else {
                margs.iter().fold(str_exp(&name, &loc), |acc, arg| {
                    let slash = str_exp("/", &loc);
                    let cat1 =
                        Located::new(Exp::Strcat(Box::new(acc), Box::new(slash)), loc.clone());
                    Located::new(
                        Exp::Strcat(Box::new(cat1), Box::new(arg.clone())),
                        loc.clone(),
                    )
                })
            };

            use crate::export::Effect;
            let un = unit_typ(&loc);
            let e = Located::new(
                Exp::ServerCall(Box::new(call), mt, Effect::ReadOnly, *fmode),
                loc.clone(),
            );
            let e = lift_exp_in_exp(0, e);
            Located::new(Exp::Abs("_".into(), un.clone(), un, Box::new(e)), loc)
        }
    }
}

// ---------------------------------------------------------------------------
// Declaration translation: mono_decl
// ---------------------------------------------------------------------------

/// Translate a Core declaration to zero or more Mono declarations.
///
/// Returns `None` if the declaration should be dropped (e.g. DCon).
/// Returns `Some((new_env, mono_decls))` on success.
///
/// Mirrors `monoDecl` in `monoize.sml`.
fn mono_decl(
    env: Env,
    fm: &mut Fm,
    decl: &LocatedDeclaration,
    settings: &Settings,
) -> Option<(Env, Vec<LocDecl>)> {
    let loc = decl.span.clone();
    match &decl.node {
        // Type synonym — disappears in Mono
        CD::Constructor(_, _, _, _) => None,

        // Datatype — translate constructors
        CD::Datatype(dts) => {
            // Extend env before translating constructor types (for mutual recursion)
            let env2 = env.clone().decl_binds(decl);
            let mut dtmap = HashMap::new();

            let mono_dts: Vec<MonoDatatypeDecl> = dts
                .iter()
                .filter_map(|dt| {
                    if !dt.params.is_empty() {
                        return None; // Polymorphic — skip
                    }
                    if dt.name == "list" {
                        return None; // Built-in in Mono
                    }
                    let constrs: Vec<_> = dt
                        .constrs
                        .iter()
                        .map(|(x, n, to)| {
                            (
                                x.clone(),
                                *n,
                                to.as_ref().map(|t| mono_type(&env2, &mut dtmap, t)),
                            )
                        })
                        .collect();
                    Some(MonoDatatypeDecl {
                        name: dt.name.clone(),
                        id: dt.id,
                        constrs,
                    })
                })
                .collect();

            if mono_dts.is_empty() {
                None
            } else {
                let d = Located::new(Decl::Datatype(mono_dts), loc);
                Some((env2, vec![d]))
            }
        }

        // Value binding
        CD::Val(x, n, t, e, s) => {
            let mut dtmap = HashMap::new();
            let me = mono_exp(&env, fm, e);
            let mt = mono_type(&env, &mut dtmap, t);
            let env2 = env.push_e_named(x.clone(), *n, t.clone(), s.clone());
            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(
                Decl::Val(x.clone(), *n, mt, me, s.clone()),
                loc,
            ));
            Some((env2, out))
        }

        // Mutually recursive bindings
        CD::ValRec(vis) => {
            let env2 = vis.iter().fold(env, |env, (x, n, t, _, s)| {
                env.push_e_named(x.clone(), *n, t.clone(), s.clone())
            });
            let mut dtmap = HashMap::new();

            let mvis: Vec<_> = vis
                .iter()
                .map(|(x, n, t, e, s)| {
                    let mt = mono_type(&env2, &mut dtmap, t);
                    let me = mono_exp(&env2, fm, e);
                    (x.clone(), *n, mt, me, s.clone())
                })
                .collect();

            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(Decl::ValRec(mvis), loc));
            Some((env2, out))
        }

        // Export
        CD::Export(ek, n, has_state) => {
            let (_name, typ, src) = env
                .lookup_e_named(*n)
                .map(|(nm, t, s)| (nm.clone(), t.clone(), s.clone()))
                .unwrap_or((
                    "?".into(),
                    Located::new(CC::Ffi("Basis".into(), "unit".into()), loc.clone()),
                    "?".into(),
                ));

            let mut dtmap = HashMap::new();
            let (arg_types, ran) = unwind_type(&env, &mut dtmap, &typ, &loc);
            let d = Located::new(
                Decl::Export(ek.clone(), src.clone(), *n, arg_types, ran, *has_state),
                loc,
            );
            Some((env, vec![d]))
        }

        // Table
        CD::Table {
            sql_name,
            id,
            con,
            sql_con: _,
            exp: pe,
            pk_con: _,
            pk_exp: _,
            unique_con: _,
        } => {
            let mut dtmap = HashMap::new();
            let s = settings.mangle_sql_table(sql_name);
            let e_name = str_exp(&s, &loc);
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());

            let xts: Vec<(String, LocTyp)> = match &con.node {
                CC::Record(_, fields) => fields
                    .iter()
                    .map(|(name_con, col_t)| {
                        (mono_name(name_con), mono_type(&env, &mut dtmap, col_t))
                    })
                    .collect(),
                _ => Vec::new(),
            };

            let mpe = mono_exp(&env, fm, pe);
            let ce = Located::new(Exp::Record(Vec::new()), loc.clone()); // simplified pk/unique

            let env2 = env.push_e_named(
                sql_name.clone(),
                *id,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(
                Decl::Table(s.clone(), xts, mpe, ce),
                loc.clone(),
            ));
            out.push(Located::new(
                Decl::Val(sql_name.clone(), *id, t, e_name, s),
                loc,
            ));
            Some((env2, out))
        }

        // Sequence
        CD::Sequence(x, n, sql_name) => {
            let s = settings.mangle_sql(sql_name);
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let e = str_exp(&s, &loc);
            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let out = vec![
                Located::new(Decl::Sequence(s.clone()), loc.clone()),
                Located::new(Decl::Val(x.clone(), *n, t, e, s), loc),
            ];
            Some((env2, out))
        }

        // View
        CD::View(x, n, sql_name, e, con) => {
            let mut dtmap = HashMap::new();
            let s = settings.mangle_sql_table(sql_name);
            let e_name = str_exp(&s, &loc);
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());

            let xts: Vec<(String, LocTyp)> = match &con.node {
                CC::Record(_, fields) => fields
                    .iter()
                    .map(|(nm, ct)| (mono_name(nm), mono_type(&env, &mut dtmap, ct)))
                    .collect(),
                _ => Vec::new(),
            };

            let me = mono_exp(&env, fm, e);
            let view_e = Located::new(
                Exp::FfiApp("Basis".into(), "viewify".into(), vec![(me, t.clone())]),
                loc.clone(),
            );

            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(
                Decl::View(s.clone(), xts, view_e),
                loc.clone(),
            ));
            out.push(Located::new(Decl::Val(x.clone(), *n, t, e_name, s), loc));
            Some((env2, out))
        }

        // Index
        CD::Index(tab_e, cols_e) => {
            let tab_path = match &tab_e.node {
                CE::Named(n) => env
                    .lookup_e_named(*n)
                    .map(|(_, _, s)| s.clone())
                    .unwrap_or_default(),
                _ => return None,
            };
            let cols: Vec<(String, mono::IndexMode)> = match &cols_e.node {
                CE::Record(xms) => xms
                    .iter()
                    .filter_map(|(name_con, mode_e, _)| {
                        let name = mono_name(name_con);
                        let mode = extract_index_mode(mode_e)?;
                        Some((name, mode))
                    })
                    .collect(),
                _ => return None,
            };
            let d = Located::new(Decl::Index(tab_path, cols), loc);
            Some((env, vec![d]))
        }

        // Database — handled specially at top level
        CD::Database(_) => None,

        // Cookie
        CD::Cookie(x, n, _, s) => {
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let e = str_exp(s, &loc);
            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let out = vec![
                Located::new(Decl::Cookie(s.clone()), loc.clone()),
                Located::new(Decl::Val(x.clone(), *n, t, e, s.clone()), loc),
            ];
            Some((env2, out))
        }

        // Style
        CD::Style(x, n, s) => {
            let t = Located::new(Typ::Ffi("Basis".into(), "string".into()), loc.clone());
            let e = Located::new(
                Exp::Prim(Prim::String(crate::primitives::StringMode::Html, s.clone())),
                loc.clone(),
            );
            let env2 = env.push_e_named(
                x.clone(),
                *n,
                Located::new(CC::Ffi("Basis".into(), "string".into()), loc.clone()),
                s.clone(),
            );
            let out = vec![
                Located::new(Decl::Style(s.clone()), loc.clone()),
                Located::new(Decl::Val(x.clone(), *n, t, e, s.clone()), loc),
            ];
            Some((env2, out))
        }

        // Task
        CD::Task(e1, e2) => {
            let me1 = mono_exp(&env, fm, e1);
            let me2 = mono_exp(&env, fm, e2);

            let un = unit_typ(&loc);
            let e2_wrapped = Located::new(
                Exp::Abs(
                    "$x".into(),
                    un.clone(),
                    Located::new(
                        Typ::Fun(Box::new(un.clone()), Box::new(un.clone())),
                        loc.clone(),
                    ),
                    Box::new(Located::new(
                        Exp::Abs(
                            "$y".into(),
                            un.clone(),
                            un.clone(),
                            Box::new(Located::new(
                                Exp::App(
                                    Box::new(Located::new(
                                        Exp::App(
                                            Box::new(me2.clone()),
                                            Box::new(Located::new(Exp::Rel(1), loc.clone())),
                                        ),
                                        loc.clone(),
                                    )),
                                    Box::new(Located::new(Exp::Rel(0), loc.clone())),
                                ),
                                loc.clone(),
                            )),
                        ),
                        loc.clone(),
                    )),
                ),
                loc.clone(),
            );

            let mut out = fm.drain_decls(&loc);
            out.push(Located::new(Decl::Task(me1, e2_wrapped), loc));
            Some((env, out))
        }

        // Policy
        CD::Policy(e) => {
            let policies = extract_policies(&env, fm, e, &loc);
            let mut out = fm.drain_decls(&loc);
            out.extend(policies);
            Some((env, out))
        }

        // OnError
        CD::OnError(n) => {
            let d = Located::new(Decl::OnError(*n), loc);
            Some((env, vec![d]))
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers for mono_decl
// ---------------------------------------------------------------------------

/// Unwind a function type into `(arg_types, return_type)`.
fn unwind_type(
    env: &Env,
    dtmap: &mut HashMap<usize, DatatypeRef>,
    t: &LocatedConstructor,
    loc: &Span,
) -> (Vec<LocTyp>, LocTyp) {
    fn go(
        env: &Env,
        dtmap: &mut HashMap<usize, DatatypeRef>,
        t: &LocatedConstructor,
        loc: &Span,
        args: &mut Vec<LocTyp>,
    ) -> LocTyp {
        match &t.node {
            CC::TFun(dom, ran) => {
                args.push(mono_type(env, dtmap, dom));
                go(env, dtmap, ran, loc, args)
            }
            CC::App(f, arg) => match &f.node {
                CC::Ffi(m, x) if m == "Basis" && x == "transaction" => {
                    // transaction t → treat as returning t (with unit arg stripped)
                    args.push(Located::new(Typ::Record(Vec::new()), loc.clone()));
                    mono_type(env, dtmap, arg)
                }
                _ => mono_type(env, dtmap, t),
            },
            _ => mono_type(env, dtmap, t),
        }
    }
    let mut args = Vec::new();
    let ran = go(env, dtmap, t, loc, &mut args);
    (args, ran)
}

fn extract_index_mode(e: &LocatedExpression) -> Option<mono::IndexMode> {
    // Look at the head of CApp/EFfi chains
    fn head(e: &LocatedExpression) -> Option<(&str, &str)> {
        match &e.node {
            CE::Ffi(m, x) => Some((m.as_str(), x.as_str())),
            CE::CApp(inner, _) => head(inner),
            CE::App(inner, _) => head(inner),
            _ => None,
        }
    }
    match head(e) {
        Some(("Basis", "equality")) => Some(mono::IndexMode::Equality),
        Some(("Basis", "trigram")) => Some(mono::IndexMode::Trigram),
        Some(("Basis", "skipped")) => Some(mono::IndexMode::Skipped),
        _ => None,
    }
}

fn extract_policies(env: &Env, fm: &mut Fm, e: &LocatedExpression, loc: &Span) -> Vec<LocDecl> {
    match &e.node {
        CE::FfiApp(m, x, args) if m == "Basis" && x == "also" => {
            if let [(e1, _), (e2, _)] = args.as_slice() {
                let mut p1 = extract_policies(env, fm, e1, loc);
                let p2 = extract_policies(env, fm, e2, loc);
                p1.extend(p2);
                return p1;
            }
            Vec::new()
        }
        _ => {
            let (inner_e, make): (_, fn(LocExp) -> Policy) = match &e.node {
                CE::App(f, arg) => match &f.node {
                    CE::CApp(ff, _) => match &ff.node {
                        CE::CApp(fff, _) => match &fff.node {
                            CE::Ffi(m, x) if m == "Basis" => match x.as_str() {
                                "sendClient" => (arg.as_ref(), |e| Policy::Client(e)),
                                "mayInsert" => (arg.as_ref(), |e| Policy::Insert(e)),
                                "mayDelete" => (arg.as_ref(), |e| Policy::Delete(e)),
                                "mayUpdate" => (arg.as_ref(), |e| Policy::Update(e)),
                                _ => return Vec::new(),
                            },
                            _ => return Vec::new(),
                        },
                        _ => return Vec::new(),
                    },
                    _ => return Vec::new(),
                },
                CE::FfiApp(m, x, args) if m == "Basis" && x == "sendOwnIds" => {
                    if let [(arg, _)] = args.as_slice() {
                        let me = mono_exp(env, fm, arg);
                        return vec![Located::new(
                            Decl::Policy(Policy::Sequence(me)),
                            loc.clone(),
                        )];
                    }
                    return Vec::new();
                }
                _ => return Vec::new(),
            };
            let me = mono_exp(env, fm, inner_e);
            vec![Located::new(Decl::Policy(make(me)), loc.clone())]
        }
    }
}

// ---------------------------------------------------------------------------
// Max name computation
// ---------------------------------------------------------------------------

/// Compute the maximum named id used in a Core file.
fn max_name_in_file(file: &core::File) -> usize {
    let mut max = 0usize;
    for decl in file {
        max_name_in_decl(&decl.node, &mut max);
    }
    max
}

fn max_name_in_decl(d: &core::Declaration, max: &mut usize) {
    match d {
        CD::Constructor(_, n, _, _)
        | CD::Sequence(_, n, _)
        | CD::Cookie(_, n, _, _)
        | CD::Style(_, n, _)
        | CD::OnError(n) => update(max, *n),
        CD::Datatype(dts) => {
            for dt in dts {
                update(max, dt.id);
                for (_, cn, _) in &dt.constrs {
                    update(max, *cn);
                }
            }
        }
        CD::Val(_, n, _, _, _) => update(max, *n),
        CD::ValRec(vis) => {
            for (_, n, _, _, _) in vis {
                update(max, *n);
            }
        }
        CD::Export(_, n, _) => update(max, *n),
        CD::Table { id, .. } | CD::View(_, id, _, _, _) => update(max, *id),
        _ => {}
    }
}

fn update(max: &mut usize, n: usize) {
    if n > *max {
        *max = n;
    }
}

// ---------------------------------------------------------------------------
// Public entry point: monoize
// ---------------------------------------------------------------------------

/// Convert a Core file to a Mono file.
///
/// Mirrors `monoize` in `monoize.sml`.
pub fn monoize(
    file: core::File,
    settings: &Settings,
    _errors: &mut crate::error_types::ErrorReporter,
) -> Option<mono::File> {
    let mname = max_name_in_file(&file) + 1;
    let mut env = Env::empty();
    let mut fm = Fm::empty(mname);
    let mut decls: Vec<LocDecl> = Vec::new();

    for core_decl in &file {
        // Handle DDatabase specially (generates expunger + initializer)
        if let CD::Database(name) = &core_decl.node {
            let nexp = fm.fresh_name();
            let nini = fm.fresh_name();
            let loc = core_decl.span.clone();

            let un = unit_typ(&loc);
            let client_t = Located::new(Typ::Ffi("Basis".into(), "client".into()), loc.clone());

            let expunger_fn = Located::new(
                Exp::Abs(
                    "cli".into(),
                    client_t.clone(),
                    un.clone(),
                    Box::new(unit_exp(&loc)),
                ),
                loc.clone(),
            );
            let init_fn = Located::new(
                Exp::Abs("_".into(), un.clone(), un.clone(), Box::new(unit_exp(&loc))),
                loc.clone(),
            );

            decls.push(Located::new(
                Decl::Database {
                    name: name.clone(),
                    expunge: nexp,
                    initialize: nini,
                    uses_similar: false,
                },
                loc.clone(),
            ));
            decls.push(Located::new(
                Decl::Val(
                    "expunger".into(),
                    nexp,
                    Located::new(
                        Typ::Fun(Box::new(client_t), Box::new(un.clone())),
                        loc.clone(),
                    ),
                    expunger_fn,
                    "expunger".into(),
                ),
                loc.clone(),
            ));
            decls.push(Located::new(
                Decl::Val(
                    "initializer".into(),
                    nini,
                    Located::new(
                        Typ::Fun(Box::new(un.clone()), Box::new(un.clone())),
                        loc.clone(),
                    ),
                    init_fn,
                    "initializer".into(),
                ),
                loc.clone(),
            ));
            continue;
        }

        match mono_decl(env.clone(), &mut fm, core_decl, settings) {
            None => {
                env = env.decl_binds(core_decl);
            }
            Some((new_env, ds)) => {
                decls.extend(ds);
                env = new_env;
            }
        }
    }

    Some((decls, Vec::new()))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_file_monoizes_to_empty() {
        let settings = Settings::default();
        let mut errors = crate::error_types::ErrorReporter::new();
        let result = monoize(Vec::new(), &settings, &mut errors);
        assert!(result.is_some());
        let (decls, ps) = result.unwrap();
        assert!(decls.is_empty());
        assert!(ps.is_empty());
    }
}
