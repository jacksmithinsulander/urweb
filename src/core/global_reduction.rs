//! Global algebraic simplification of Core programs.
//!
//! Inlines globally-named constructors and expressions, beta-reduces lambdas,
//! eta-contracts records, and performs static case-arm elimination.  Unlike
//! `local_reduction`, this pass can substitute across declaration boundaries
//! because it maintains `named_c` / `named_e` maps that accumulate the
//! definitions of every top-level binding as it processes the file.
//!
//! Environment items extend local_reduction's two-tier (C / E) tracking with a
//! third tier for kind variables (K), matching the `env_item` in `reduce.sml`:
//!
//! - `UnknownK` / `KnownK(k)` — a kind variable, unknown or equal to `k`
//! - `UnknownC` / `KnownC(c)` — a type variable, unknown or equal to `c`
//! - `UnknownE` / `KnownE(e)` — an expression variable, unknown or equal to `e`
//! - `Lift(nk, nc, ne)`  — synthetic: expand to nk UnknownK + nc UnknownC + ne UnknownE
//!
//! Mirrors `reduce.sml`.

use std::collections::{BTreeSet, HashMap};

use crate::core::local_reduction::{shift_con, shift_exp};
use crate::core::*;
use crate::error_types::{Located, Span};
use crate::primitives::Prim;
use crate::settings::Settings;

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum EnvItem {
    UnknownK,
    KnownK(LocatedKind),
    UnknownC,
    KnownC(LocatedConstructor),
    UnknownE,
    KnownE(LocatedExpression),
    /// Synthetic: expands to nk UnknownK + nc UnknownC + ne UnknownE.
    Lift(usize, usize, usize),
}

type Env = Vec<EnvItem>;

/// Collapse Known* items: KnownK → nothing, KnownC → nothing, KnownE → nothing;
/// Lift(nk,nc,ne) → nk×UnknownK + nc×UnknownC + ne×UnknownE.
fn de_known(env: &[EnvItem]) -> Env {
    let mut out = Vec::with_capacity(env.len());
    for item in env {
        match item {
            EnvItem::KnownK(_) | EnvItem::KnownC(_) | EnvItem::KnownE(_) => {}
            EnvItem::Lift(nk, nc, ne) => {
                out.extend((0..*nk).map(|_| EnvItem::UnknownK));
                out.extend((0..*nc).map(|_| EnvItem::UnknownC));
                out.extend((0..*ne).map(|_| EnvItem::UnknownE));
            }
            x => out.push(x.clone()),
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Passive / notFfi predicates
// ---------------------------------------------------------------------------

fn passive(e: &Expression) -> bool {
    match e {
        Expression::Prim(_)
        | Expression::Rel(_)
        | Expression::Named(_)
        | Expression::Ffi(_, _)
        | Expression::Abs(_, _, _, _)
        | Expression::CAbs(_, _, _)
        | Expression::KAbs(_, _) => true,
        Expression::Constructor(_, _, _, None) => true,
        Expression::Constructor(_, _, _, Some(inner)) => passive(&inner.node),
        Expression::Record(fields) => fields.iter().all(|(_, e, _)| passive(&e.node)),
        Expression::Field(e, _, _) => passive(&e.node),
        _ => false,
    }
}

fn not_ffi(t: &Constructor) -> bool {
    !matches!(t, Constructor::Ffi(_, _))
}

fn function_inside_type(con: &LocatedConstructor) -> bool {
    match &con.node {
        Constructor::TFun(_, _) | Constructor::TCFun(_, _, _) => true,
        Constructor::Ffi(module, name)
            if module == "Basis"
                && matches!(
                    name.as_str(),
                    "transaction"
                        | "eq"
                        | "num"
                        | "ord"
                        | "show"
                        | "read"
                        | "sql_injectable_prim"
                        | "sql_injectable"
                ) =>
        {
            true
        }
        Constructor::App(function, arg) => {
            function_inside_type(function) || function_inside_type(arg)
        }
        Constructor::Abs(_, _, body) | Constructor::KAbs(_, body) | Constructor::TKFun(_, body) => {
            function_inside_type(body)
        }
        Constructor::TRecord(inner) => function_inside_type(inner),
        Constructor::KApp(inner, _) => function_inside_type(inner),
        Constructor::Record(_, fields) => fields
            .iter()
            .any(|(name, value)| function_inside_type(name) || function_inside_type(value)),
        Constructor::Concat(left, right) => {
            function_inside_type(left) || function_inside_type(right)
        }
        Constructor::Tuple(items) => items.iter().any(function_inside_type),
        Constructor::Proj(inner, _) => function_inside_type(inner),
        Constructor::Rel(_)
        | Constructor::Named(_)
        | Constructor::Name(_)
        | Constructor::Unit
        | Constructor::Map(_, _)
        | Constructor::Ffi(_, _) => false,
    }
}

fn is_erased_zero_witness_app(arg: &LocatedExpression, dom: &LocatedConstructor) -> bool {
    matches!(arg.node, Expression::Prim(Prim::Int(0)))
        && match &dom.node {
            Constructor::Unit => false,
            Constructor::Ffi(module, name) if module == "Basis" && name == "int" => false,
            _ => true,
        }
}

// ---------------------------------------------------------------------------
// Pattern variable count
// ---------------------------------------------------------------------------

fn pat_binds_n(p: &LocatedPattern) -> usize {
    match &p.node {
        Pattern::Var(_, _) => 1,
        Pattern::Prim(_) => 0,
        Pattern::Constructor(_, _, _, None) => 0,
        Pattern::Constructor(_, _, _, Some(inner)) => pat_binds_n(inner),
        Pattern::Record(fields) => fields.iter().map(|(_, p, _)| pat_binds_n(p)).sum(),
    }
}

// ---------------------------------------------------------------------------
// Expression use-count (for beta-inlining threshold)
// ---------------------------------------------------------------------------

fn count_exp(e: &LocatedExpression) -> usize {
    let mut n = 0;
    count_exp_rec(e, &mut n);
    n
}

fn count_exp_rec(e: &LocatedExpression, n: &mut usize) {
    *n += 1;
    match &e.node {
        Expression::App(f, a) => {
            count_exp_rec(f, n);
            count_exp_rec(a, n);
        }
        Expression::Abs(_, _, _, b) | Expression::KAbs(_, b) | Expression::Write(b) => {
            count_exp_rec(b, n)
        }
        Expression::CApp(e, _) | Expression::Field(e, _, _) => count_exp_rec(e, n),
        Expression::CAbs(_, _, b) => count_exp_rec(b, n),
        Expression::KApp(e, _) => count_exp_rec(e, n),
        Expression::FfiApp(_, _, args) => args.iter().for_each(|(e, _)| count_exp_rec(e, n)),
        Expression::Record(fs) => fs.iter().for_each(|(_, e, _)| count_exp_rec(e, n)),
        Expression::Concat(e1, _, e2, _) => {
            count_exp_rec(e1, n);
            count_exp_rec(e2, n);
        }
        Expression::Cut(e, _, _) | Expression::CutMulti(e, _, _) => count_exp_rec(e, n),
        Expression::Case(e, arms, _) => {
            count_exp_rec(e, n);
            arms.iter().for_each(|(_, b)| count_exp_rec(b, n));
        }
        Expression::Closure(_, es) | Expression::ServerCall(_, es, _, _) => {
            es.iter().for_each(|e| count_exp_rec(e, n))
        }
        Expression::Let(_, _, e1, e2) => {
            count_exp_rec(e1, n);
            count_exp_rec(e2, n);
        }
        Expression::Constructor(_, _, _, Some(e)) => count_exp_rec(e, n),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Count uses of named expressions (for inlining decisions)
// ---------------------------------------------------------------------------

fn count_named_uses(file: &[LocatedDeclaration]) -> HashMap<usize, usize> {
    let mut uses = HashMap::new();
    for d in file {
        count_uses_decl(d, &mut uses);
    }
    uses
}

fn count_uses_exp(e: &LocatedExpression, uses: &mut HashMap<usize, usize>) {
    match &e.node {
        Expression::Named(n) => *uses.entry(*n).or_insert(0) += 1,
        Expression::App(f, a) => {
            count_uses_exp(f, uses);
            count_uses_exp(a, uses);
        }
        Expression::Abs(_, _, _, b) | Expression::KAbs(_, b) | Expression::Write(b) => {
            count_uses_exp(b, uses)
        }
        Expression::CApp(e, _) | Expression::Field(e, _, _) => count_uses_exp(e, uses),
        Expression::CAbs(_, _, b) => count_uses_exp(b, uses),
        Expression::KApp(e, _) => count_uses_exp(e, uses),
        Expression::FfiApp(_, _, args) => args.iter().for_each(|(e, _)| count_uses_exp(e, uses)),
        Expression::Record(fs) => fs.iter().for_each(|(_, e, _)| count_uses_exp(e, uses)),
        Expression::Concat(e1, _, e2, _) => {
            count_uses_exp(e1, uses);
            count_uses_exp(e2, uses);
        }
        Expression::Cut(e, _, _) | Expression::CutMulti(e, _, _) => count_uses_exp(e, uses),
        Expression::Case(e, arms, _) => {
            count_uses_exp(e, uses);
            arms.iter().for_each(|(_, b)| count_uses_exp(b, uses));
        }
        Expression::Closure(_, es) | Expression::ServerCall(_, es, _, _) => {
            es.iter().for_each(|e| count_uses_exp(e, uses))
        }
        Expression::Let(_, _, e1, e2) => {
            count_uses_exp(e1, uses);
            count_uses_exp(e2, uses);
        }
        Expression::Constructor(_, _, _, Some(e)) => count_uses_exp(e, uses),
        _ => {}
    }
}

fn count_uses_decl(d: &LocatedDeclaration, uses: &mut HashMap<usize, usize>) {
    match &d.node {
        Declaration::Val(_, _, _, e, _) => count_uses_exp(e, uses),
        Declaration::ValRec(vis) => vis
            .iter()
            .for_each(|(_, _, _, e, _)| count_uses_exp(e, uses)),
        Declaration::Table {
            exp: pe,
            pk_exp: ce,
            ..
        } => {
            count_uses_exp(pe, uses);
            count_uses_exp(ce, uses);
        }
        Declaration::View(_, _, _, e, _) => count_uses_exp(e, uses),
        Declaration::Index(e1, e2) => {
            count_uses_exp(e1, uses);
            count_uses_exp(e2, uses);
        }
        Declaration::Task(e1, e2) => {
            count_uses_exp(e1, uses);
            count_uses_exp(e2, uses);
        }
        Declaration::Policy(e) => count_uses_exp(e, uses),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// is_poly: does a constructor mention polymorphic type abstractions?
// ---------------------------------------------------------------------------

fn is_poly_con(poly_c: &BTreeSet<usize>, con: &LocatedConstructor) -> bool {
    match &con.node {
        Constructor::TCFun(_, _, _) | Constructor::TKFun(_, _) => true,
        Constructor::Named(n) => poly_c.contains(n),
        Constructor::TFun(a, b) => is_poly_con(poly_c, a) || is_poly_con(poly_c, b),
        Constructor::TRecord(inner) => is_poly_con(poly_c, inner),
        Constructor::App(f, a) => is_poly_con(poly_c, f) || is_poly_con(poly_c, a),
        Constructor::Abs(_, _, b) | Constructor::KAbs(_, b) => is_poly_con(poly_c, b),
        Constructor::KApp(c, _) => is_poly_con(poly_c, c),
        Constructor::Record(_, pairs) => pairs.iter().any(|(_, c)| is_poly_con(poly_c, c)),
        Constructor::Concat(a, b) => is_poly_con(poly_c, a) || is_poly_con(poly_c, b),
        Constructor::Tuple(cs) => cs.iter().any(|c| is_poly_con(poly_c, c)),
        Constructor::Proj(c, _) => is_poly_con(poly_c, c),
        _ => false,
    }
}

fn is_policy(t: &Constructor) -> bool {
    match t {
        Constructor::Ffi(m, n) if m == "Basis" && n == "sql_policy" => true,
        Constructor::TFun(_, ran) => is_policy(&ran.node),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Monad helpers: build types and expressions for Basis.return / bind / etc.
// ---------------------------------------------------------------------------

fn k_type(l: &Span) -> LocatedKind {
    Located::new(Kind::Type, l.clone())
}

fn k_arrow(l: &Span) -> LocatedKind {
    Located::new(
        Kind::Arrow(Box::new(k_type(l)), Box::new(k_type(l))),
        l.clone(),
    )
}

/// `∀a :: Type. (a → m a)` where m is a CRel at the current binding depth.
fn return_type(m: &LocatedConstructor) -> LocatedConstructor {
    let l = &m.span;
    // Inside ∀a, the original m is one binder deeper → shift by 1
    let m1 = shift_con(m.clone(), 0, 1);
    let a = Located::new(Constructor::Rel(0), l.clone());
    let m_a = Located::new(
        Constructor::App(Box::new(m1), Box::new(a.clone())),
        l.clone(),
    );
    Located::new(
        Constructor::TCFun(
            "a".into(),
            Box::new(k_type(l)),
            Box::new(Located::new(
                Constructor::TFun(Box::new(a), Box::new(m_a)),
                l.clone(),
            )),
        ),
        l.clone(),
    )
}

/// `∀a ∀b. (m a → (a → m b) → m b)` where m is shifted 2 deep.
fn bind_type(m: &LocatedConstructor) -> LocatedConstructor {
    let l = &m.span;
    let m2 = shift_con(m.clone(), 0, 2);
    let a = Located::new(Constructor::Rel(1), l.clone());
    let b = Located::new(Constructor::Rel(0), l.clone());
    let m_a = Located::new(
        Constructor::App(Box::new(m2.clone()), Box::new(a.clone())),
        l.clone(),
    );
    let m_b = Located::new(Constructor::App(Box::new(m2), Box::new(b)), l.clone());
    let a_to_m_b = Located::new(
        Constructor::TFun(Box::new(a), Box::new(m_b.clone())),
        l.clone(),
    );
    let body = Located::new(
        Constructor::TFun(
            Box::new(m_a),
            Box::new(Located::new(
                Constructor::TFun(Box::new(a_to_m_b), Box::new(m_b)),
                l.clone(),
            )),
        ),
        l.clone(),
    );
    Located::new(
        Constructor::TCFun(
            "a".into(),
            Box::new(k_type(l)),
            Box::new(Located::new(
                Constructor::TCFun("b".into(), Box::new(k_type(l)), Box::new(body)),
                l.clone(),
            )),
        ),
        l.clone(),
    )
}

/// `{ Return: return_type(m), Bind: bind_type(m) }`
fn monad_record(m: &LocatedConstructor) -> LocatedConstructor {
    let l = &m.span;
    let ret_name = Located::new(Constructor::Name("Return".into()), l.clone());
    let bind_name = Located::new(Constructor::Name("Bind".into()), l.clone());
    let inner = Located::new(
        Constructor::Record(
            Box::new(k_type(l)),
            vec![(ret_name, return_type(m)), (bind_name, bind_type(m))],
        ),
        l.clone(),
    );
    Located::new(Constructor::TRecord(Box::new(inner)), l.clone())
}

/// Builds the expression for `EFfi("Basis", "return")`:
/// `ECAbs("m", K→K, ECAbs("a", K, EAbs("m_rec", monad(CRel 1), return_type(CRel 1),
///   ECApp(EField(ERel 0, "Return", ...), CRel 0))))`
fn make_return_exp(l: Span) -> LocatedExpression {
    let mk = |node| Located::new(node, l.clone());
    let m1 = Located::new(Constructor::Rel(1), l.clone());
    let a = Located::new(Constructor::Rel(0), l.clone());
    let ret_t = return_type(&m1);
    let mr = monad_record(&m1);
    let bind_t = bind_type(&m1);
    let rest_con = Located::new(
        Constructor::TRecord(Box::new(Located::new(
            Constructor::Record(
                Box::new(k_type(&l)),
                vec![(
                    Located::new(Constructor::Name("Bind".into()), l.clone()),
                    bind_t,
                )],
            ),
            l.clone(),
        ))),
        l.clone(),
    );
    let ret_field_name = Located::new(Constructor::Name("Return".into()), l.clone());
    let field = mk(Expression::Field(
        Box::new(mk(Expression::Rel(0))),
        ret_field_name,
        FieldMeta {
            field: ret_t.clone(),
            rest: rest_con,
        },
    ));
    let ec_app = mk(Expression::CApp(Box::new(field), a));
    let abs = mk(Expression::Abs("m_rec".into(), mr, ret_t, Box::new(ec_app)));
    let cabs_a = mk(Expression::CAbs(
        "a".into(),
        Box::new(k_type(&l)),
        Box::new(abs),
    ));
    mk(Expression::CAbs(
        "m".into(),
        Box::new(k_arrow(&l)),
        Box::new(cabs_a),
    ))
}

/// Builds the expression for `EFfi("Basis", "bind")`.
fn make_bind_exp(l: Span) -> LocatedExpression {
    let mk = |node| Located::new(node, l.clone());
    let m2 = Located::new(Constructor::Rel(2), l.clone());
    let a = Located::new(Constructor::Rel(1), l.clone());
    let b = Located::new(Constructor::Rel(0), l.clone());
    let bind_t = bind_type(&m2);
    let mr = monad_record(&m2);
    let ret_t = return_type(&m2);
    let rest_con = Located::new(
        Constructor::TRecord(Box::new(Located::new(
            Constructor::Record(
                Box::new(k_type(&l)),
                vec![(
                    Located::new(Constructor::Name("Return".into()), l.clone()),
                    ret_t,
                )],
            ),
            l.clone(),
        ))),
        l.clone(),
    );
    let _m2_a = Located::new(
        Constructor::App(Box::new(m2.clone()), Box::new(a.clone())),
        l.clone(),
    );
    let _m2_b = Located::new(
        Constructor::App(Box::new(m2), Box::new(b.clone())),
        l.clone(),
    );
    let bind_field_name = Located::new(Constructor::Name("Bind".into()), l.clone());
    let field = mk(Expression::Field(
        Box::new(mk(Expression::Rel(0))),
        bind_field_name,
        FieldMeta {
            field: bind_t.clone(),
            rest: rest_con,
        },
    ));
    let ec_app1 = mk(Expression::CApp(Box::new(field), a));
    let ec_app2 = mk(Expression::CApp(Box::new(ec_app1), b));
    let abs = mk(Expression::Abs(
        "m_rec".into(),
        mr,
        bind_t,
        Box::new(ec_app2),
    ));
    let cabs_b = mk(Expression::CAbs(
        "b".into(),
        Box::new(k_type(&l)),
        Box::new(abs),
    ));
    let cabs_a = mk(Expression::CAbs(
        "a".into(),
        Box::new(k_type(&l)),
        Box::new(cabs_b),
    ));
    mk(Expression::CAbs(
        "m".into(),
        Box::new(k_arrow(&l)),
        Box::new(cabs_a),
    ))
}

/// Builds the expression for `EFfi("Basis", "mkMonad")`: identity on the monad record.
fn make_mk_monad_exp(l: Span) -> LocatedExpression {
    let mk = |node| Located::new(node, l.clone());
    let m0 = Located::new(Constructor::Rel(0), l.clone());
    let mr = monad_record(&m0);
    let abs = mk(Expression::Abs(
        "m_rec".into(),
        mr.clone(),
        mr,
        Box::new(mk(Expression::Rel(0))),
    ));
    mk(Expression::CAbs(
        "m".into(),
        Box::new(k_arrow(&l)),
        Box::new(abs),
    ))
}

/// Builds `{ Return = EFfi("Basis","transaction_return"), Bind = EFfi("Basis","transaction_bind") }`.
fn make_transaction_monad_exp(l: Span) -> LocatedExpression {
    let mk = |node| Located::new(node, l.clone());
    let m = Located::new(
        Constructor::Ffi("Basis".into(), "transaction".into()),
        l.clone(),
    );
    let ret_t = return_type(&m);
    let bind_t = bind_type(&m);
    mk(Expression::Record(vec![
        (
            Located::new(Constructor::Name("Return".into()), l.clone()),
            mk(Expression::Ffi("Basis".into(), "transaction_return".into())),
            ret_t,
        ),
        (
            Located::new(Constructor::Name("Bind".into()), l.clone()),
            mk(Expression::Ffi("Basis".into(), "transaction_bind".into())),
            bind_t,
        ),
    ]))
}

/// Builds `{ Return = EFfi("Basis","signal_return"), Bind = EFfi("Basis","signal_bind") }`.
fn make_signal_monad_exp(l: Span) -> LocatedExpression {
    let mk = |node| Located::new(node, l.clone());
    let m = Located::new(Constructor::Ffi("Basis".into(), "signal".into()), l.clone());
    let ret_t = return_type(&m);
    let bind_t = bind_type(&m);
    mk(Expression::Record(vec![
        (
            Located::new(Constructor::Name("Return".into()), l.clone()),
            mk(Expression::Ffi("Basis".into(), "signal_return".into())),
            ret_t,
        ),
        (
            Located::new(Constructor::Name("Bind".into()), l.clone()),
            mk(Expression::Ffi("Basis".into(), "signal_bind".into())),
            bind_t,
        ),
    ]))
}

// ---------------------------------------------------------------------------
// Reducer — the main stateful transformer
// ---------------------------------------------------------------------------

struct Reducer {
    /// Globally-known constructors (from DCon).
    named_c: HashMap<usize, LocatedConstructor>,
    /// Globally-known expressions (from DVal when mayInline).
    named_e: HashMap<usize, LocatedExpression>,
}

impl Reducer {
    fn new() -> Self {
        Reducer {
            named_c: HashMap::new(),
            named_e: HashMap::new(),
        }
    }

    fn with_knowns(
        named_c: HashMap<usize, LocatedConstructor>,
        named_e: HashMap<usize, LocatedExpression>,
    ) -> Self {
        Reducer { named_c, named_e }
    }

    // -----------------------------------------------------------------------
    // Kind reduction
    // -----------------------------------------------------------------------

    fn reduce_kind(&self, env: &[EnvItem], kind: LocatedKind) -> LocatedKind {
        let span = kind.span.clone();
        let mk = |node| Located::new(node, span.clone());
        match kind.node {
            Kind::Type => mk(Kind::Type),
            Kind::Name => mk(Kind::Name),
            Kind::Unit => mk(Kind::Unit),
            Kind::Rel(n) => self.find_kind(env, n, n, 0, span),
            Kind::Arrow(k1, k2) => mk(Kind::Arrow(
                Box::new(self.reduce_kind(env, *k1)),
                Box::new(self.reduce_kind(env, *k2)),
            )),
            Kind::Record(k) => mk(Kind::Record(Box::new(self.reduce_kind(env, *k)))),
            Kind::Tuple(ks) => mk(Kind::Tuple(
                ks.into_iter().map(|k| self.reduce_kind(env, k)).collect(),
            )),
            Kind::Fun(x, k) => {
                let mut inner: Env = vec![EnvItem::UnknownK];
                inner.extend_from_slice(env);
                mk(Kind::Fun(x, Box::new(self.reduce_kind(&inner, *k))))
            }
        }
    }

    fn find_kind(
        &self,
        env: &[EnvItem],
        n_orig: usize,
        n: usize,
        nudge: isize,
        span: Span,
    ) -> LocatedKind {
        match env.first() {
            None => Located::new(Kind::Rel((n_orig as isize + nudge) as usize), span),
            Some(item) => match item {
                EnvItem::UnknownC | EnvItem::KnownC(_) | EnvItem::UnknownE | EnvItem::KnownE(_) => {
                    self.find_kind(&env[1..], n_orig, n, nudge, span)
                }
                EnvItem::Lift(lk, _, _) => {
                    self.find_kind(&env[1..], n_orig, n, nudge + *lk as isize, span)
                }
                EnvItem::UnknownK => {
                    if n == 0 {
                        Located::new(Kind::Rel((n_orig as isize + nudge) as usize), span)
                    } else {
                        self.find_kind(&env[1..], n_orig, n - 1, nudge, span)
                    }
                }
                EnvItem::KnownK(k) => {
                    if n == 0 {
                        // The known kind was bound at depth `lift` from current env start.
                        // We re-reduce it in a context that lifts any inner KRels correctly.
                        // Since we're at depth 0 and the known kind has no free KRels
                        // (it comes from a binding), just reduce it with an empty-ish env.
                        // For simplicity, use the tail env with no additional lift.
                        self.reduce_kind(&env[1..], k.clone())
                    } else {
                        self.find_kind(&env[1..], n_orig, n - 1, nudge - 1, span)
                    }
                }
            },
        }
    }

    // -----------------------------------------------------------------------
    // Constructor reduction
    // -----------------------------------------------------------------------

    fn reduce_con(&self, env: &[EnvItem], con: LocatedConstructor) -> LocatedConstructor {
        let span = con.span.clone();
        let mk = |node| Located::new(node, span.clone());
        match con.node {
            Constructor::TFun(a, b) => mk(Constructor::TFun(
                Box::new(self.reduce_con(env, *a)),
                Box::new(self.reduce_con(env, *b)),
            )),
            Constructor::TCFun(x, k, body) => {
                let mut inner: Env = vec![EnvItem::UnknownC];
                inner.extend_from_slice(env);
                mk(Constructor::TCFun(
                    x,
                    Box::new(self.reduce_kind(env, *k)),
                    Box::new(self.reduce_con(&inner, *body)),
                ))
            }
            Constructor::TKFun(x, body) => {
                let mut inner: Env = vec![EnvItem::UnknownK];
                inner.extend_from_slice(env);
                mk(Constructor::TKFun(
                    x,
                    Box::new(self.reduce_con(&inner, *body)),
                ))
            }
            Constructor::TRecord(inner) => {
                mk(Constructor::TRecord(Box::new(self.reduce_con(env, *inner))))
            }
            Constructor::Rel(n) => self.find_con(env, n, n, 0, 0, 0, span),
            Constructor::Named(n) => match self.named_c.get(&n) {
                None => mk(Constructor::Named(n)),
                Some(c) if matches!(c.node, Constructor::Named(m) if m == n) => {
                    mk(Constructor::Named(n))
                }
                Some(c) => self.reduce_con(env, c.clone()),
            },
            // Basis.monad expands to a kind-level abstraction
            Constructor::Ffi(ref m, ref f) if m == "Basis" && f == "monad" => {
                let l = &span;
                let m_rel = Located::new(Constructor::Rel(0), l.clone());
                let mr = monad_record(&m_rel);
                mk(Constructor::KAbs(
                    "m".into(),
                    Box::new(Located::new(Constructor::TRecord(Box::new(mr)), l.clone())),
                ))
            }
            Constructor::Ffi(m, f) => mk(Constructor::Ffi(m, f)),
            Constructor::App(f, a) => {
                let f_red = self.reduce_con(env, *f);
                let a_red = self.reduce_con(env, *a);
                match f_red.node {
                    // Beta: (fn _ :: _ => body) arg
                    Constructor::Abs(_, _, body) => {
                        let mut inner: Env = vec![EnvItem::KnownC(a_red)];
                        inner.extend_from_slice(&de_known(env));
                        self.reduce_con(&inner, *body)
                    }
                    // Map(dom,ran) applied to a record → expand
                    Constructor::App(ref map_node, ref mapper)
                        if matches!(map_node.node, Constructor::Map(_, _)) =>
                    {
                        if let Constructor::Map(_, ref ran) = map_node.node {
                            let ran = *ran.clone();
                            match a_red.node.clone() {
                                Constructor::Unit => {
                                    let ran_red = self.reduce_kind(env, ran);
                                    return Located::new(
                                        Constructor::Record(Box::new(ran_red), vec![]),
                                        span,
                                    );
                                }
                                Constructor::Record(_, ref xcs) if xcs.is_empty() => {
                                    let ran_red = self.reduce_kind(env, ran);
                                    return Located::new(
                                        Constructor::Record(Box::new(ran_red), vec![]),
                                        span,
                                    );
                                }
                                Constructor::Record(dom_k, mut xcs) => {
                                    let first = xcs.remove(0);
                                    let tail_rec = Located::new(
                                        Constructor::Record(
                                            Box::new(self.reduce_kind(env, *dom_k)),
                                            xcs,
                                        ),
                                        span.clone(),
                                    );
                                    // Apply the mapper to the current field value and recurse with
                                    // the full map application on the tail record.
                                    let f_first = self.reduce_con(
                                        &de_known(env),
                                        Located::new(
                                            Constructor::App(
                                                Box::new((**mapper).clone()),
                                                Box::new(first.1.clone()),
                                            ),
                                            span.clone(),
                                        ),
                                    );
                                    let f_tail = Located::new(
                                        Constructor::App(
                                            Box::new(f_red.clone()),
                                            Box::new(tail_rec),
                                        ),
                                        span.clone(),
                                    );
                                    let concat = Located::new(
                                        Constructor::Concat(
                                            Box::new(Located::new(
                                                Constructor::Record(
                                                    Box::new(ran),
                                                    vec![(first.0, f_first)],
                                                ),
                                                span.clone(),
                                            )),
                                            Box::new(f_tail),
                                        ),
                                        span.clone(),
                                    );
                                    return self.reduce_con(&de_known(env), concat);
                                }
                                _ => {}
                            }
                        }
                        mk(Constructor::App(Box::new(f_red), Box::new(a_red)))
                    }
                    other => mk(Constructor::App(
                        Box::new(Located::new(other, span.clone())),
                        Box::new(a_red),
                    )),
                }
            }
            Constructor::Abs(x, k, body) => {
                let mut inner: Env = vec![EnvItem::UnknownC];
                inner.extend_from_slice(env);
                mk(Constructor::Abs(
                    x,
                    Box::new(self.reduce_kind(env, *k)),
                    Box::new(self.reduce_con(&inner, *body)),
                ))
            }
            Constructor::KAbs(x, body) => {
                let mut inner: Env = vec![EnvItem::UnknownK];
                inner.extend_from_slice(env);
                mk(Constructor::KAbs(
                    x,
                    Box::new(self.reduce_con(&inner, *body)),
                ))
            }
            Constructor::KApp(c, k) => {
                let c_red = self.reduce_con(env, *c);
                match c_red.node {
                    Constructor::KAbs(_, body) => {
                        let mut inner: Env = vec![EnvItem::KnownK(*k)];
                        inner.extend_from_slice(&de_known(env));
                        self.reduce_con(&inner, *body)
                    }
                    other => mk(Constructor::KApp(
                        Box::new(Located::new(other, span.clone())),
                        Box::new(self.reduce_kind(env, *k)),
                    )),
                }
            }
            Constructor::Name(n) => mk(Constructor::Name(n)),
            Constructor::Record(k, xcs) => mk(Constructor::Record(
                Box::new(self.reduce_kind(env, *k)),
                xcs.into_iter()
                    .map(|(x, c)| (self.reduce_con(env, x), self.reduce_con(env, c)))
                    .collect(),
            )),
            Constructor::Concat(c1, c2) => {
                let c1_red = self.reduce_con(env, *c1);
                let c2_red = self.reduce_con(env, *c2);
                match (&c1_red.node, &c2_red.node) {
                    (Constructor::Record(k, xcs1), Constructor::Record(_, xcs2)) => {
                        let k = k.clone();
                        let mut all = xcs1.clone();
                        all.extend_from_slice(xcs2);
                        mk(Constructor::Record(k, all))
                    }
                    (Constructor::Record(_, xcs), _) if xcs.is_empty() => c2_red,
                    (_, Constructor::Record(_, xcs)) if xcs.is_empty() => c1_red,
                    _ => mk(Constructor::Concat(Box::new(c1_red), Box::new(c2_red))),
                }
            }
            Constructor::Map(dom, ran) => mk(Constructor::Map(
                Box::new(self.reduce_kind(env, *dom)),
                Box::new(self.reduce_kind(env, *ran)),
            )),
            Constructor::Unit => mk(Constructor::Unit),
            Constructor::Tuple(cs) => mk(Constructor::Tuple(
                cs.into_iter().map(|c| self.reduce_con(env, c)).collect(),
            )),
            Constructor::Proj(c, n) => {
                let c_red = self.reduce_con(env, *c);
                match c_red.node {
                    Constructor::Tuple(cs) => cs
                        .into_iter()
                        .nth(n.saturating_sub(1))
                        .unwrap_or_else(|| Located::new(Constructor::Unit, span.clone())),
                    other => mk(Constructor::Proj(
                        Box::new(Located::new(other, span.clone())),
                        n,
                    )),
                }
            }
        }
    }

    fn find_con(
        &self,
        env: &[EnvItem],
        n_orig: usize,
        n: usize,
        nudge: isize,
        lift_k: usize,
        lift_c: usize,
        span: Span,
    ) -> LocatedConstructor {
        match env.first() {
            None => Located::new(Constructor::Rel((n_orig as isize + nudge) as usize), span),
            Some(item) => match item {
                EnvItem::UnknownK => {
                    self.find_con(&env[1..], n_orig, n, nudge, lift_k + 1, lift_c, span)
                }
                EnvItem::KnownK(_) => {
                    self.find_con(&env[1..], n_orig, n, nudge, lift_k, lift_c, span)
                }
                EnvItem::UnknownE | EnvItem::KnownE(_) => {
                    self.find_con(&env[1..], n_orig, n, nudge, lift_k, lift_c, span)
                }
                EnvItem::Lift(lk, lc, _) => self.find_con(
                    &env[1..],
                    n_orig,
                    n,
                    nudge + *lc as isize,
                    lift_k + lk,
                    lift_c + lc,
                    span,
                ),
                EnvItem::UnknownC => {
                    if n == 0 {
                        Located::new(Constructor::Rel((n_orig as isize + nudge) as usize), span)
                    } else {
                        self.find_con(&env[1..], n_orig, n - 1, nudge, lift_k, lift_c + 1, span)
                    }
                }
                EnvItem::KnownC(c) => {
                    if n == 0 {
                        let mut lift_env: Env = vec![EnvItem::Lift(lift_k, lift_c, 0)];
                        lift_env.extend_from_slice(&env[1..]);
                        self.reduce_con(&lift_env, c.clone())
                    } else {
                        self.find_con(&env[1..], n_orig, n - 1, nudge - 1, lift_k, lift_c, span)
                    }
                }
            },
        }
    }

    // -----------------------------------------------------------------------
    // Pattern constructor reduction
    // -----------------------------------------------------------------------

    fn reduce_pat_con(&self, env: &[EnvItem], pc: PatternConstructor) -> PatternConstructor {
        match pc {
            PatternConstructor::Var(n) => PatternConstructor::Var(n),
            PatternConstructor::Ffi {
                module,
                datatyp,
                params,
                con,
                arg,
                kind,
            } => {
                let n = params.len();
                let inner_env: Env = (0..n)
                    .map(|_| EnvItem::UnknownC)
                    .chain(env.iter().cloned())
                    .collect();
                PatternConstructor::Ffi {
                    module,
                    datatyp,
                    params,
                    con,
                    arg: arg.map(|c| self.reduce_con(&inner_env, c)),
                    kind,
                }
            }
        }
    }

    fn reduce_pat(&self, env: &[EnvItem], p: LocatedPattern) -> LocatedPattern {
        let span = p.span.clone();
        let node = match p.node {
            Pattern::Var(x, t) => Pattern::Var(x, self.reduce_con(env, t)),
            Pattern::Prim(p) => Pattern::Prim(p),
            Pattern::Constructor(dk, pc, cs, inner) => Pattern::Constructor(
                dk,
                self.reduce_pat_con(env, pc),
                cs.into_iter().map(|c| self.reduce_con(env, c)).collect(),
                inner.map(|p| Box::new(self.reduce_pat(env, *p))),
            ),
            Pattern::Record(fields) => Pattern::Record(
                fields
                    .into_iter()
                    .map(|(x, p, t)| (x, self.reduce_pat(env, p), self.reduce_con(env, t)))
                    .collect(),
            ),
        };
        Located { node, span }
    }

    // -----------------------------------------------------------------------
    // Expression reduction
    // -----------------------------------------------------------------------

    fn reduce_exp(&self, env: &[EnvItem], exp: LocatedExpression) -> LocatedExpression {
        let span = exp.span.clone();
        let mk = |node| Located::new(node, span.clone());
        match exp.node {
            Expression::Prim(p) => mk(Expression::Prim(p)),
            Expression::Rel(n) => self.find_exp(env, n, n, 0, 0, 0, 0, span),
            Expression::Named(n) => match self.named_e.get(&n) {
                None => mk(Expression::Named(n)),
                Some(e) if matches!(e.node, Expression::Named(m) if m == n) => {
                    mk(Expression::Named(n))
                }
                Some(e) => self.reduce_exp(env, e.clone()),
            },
            Expression::Constructor(dk, pc, cs, eo) => mk(Expression::Constructor(
                dk,
                self.reduce_pat_con(env, pc),
                cs.into_iter().map(|c| self.reduce_con(env, c)).collect(),
                eo.map(|e| Box::new(self.reduce_exp(env, *e))),
            )),
            // Monad expansions
            Expression::Ffi(ref m, ref f) if m == "Basis" && f == "return" => make_return_exp(span),
            Expression::Ffi(ref m, ref f) if m == "Basis" && f == "bind" => make_bind_exp(span),
            Expression::Ffi(ref m, ref f) if m == "Basis" && f == "mkMonad" => {
                make_mk_monad_exp(span)
            }
            Expression::Ffi(ref m, ref f) if m == "Basis" && f == "transaction_monad" => {
                make_transaction_monad_exp(span)
            }
            Expression::Ffi(ref m, ref f) if m == "Basis" && f == "signal_monad" => {
                make_signal_monad_exp(span)
            }
            Expression::Ffi(m, f) => mk(Expression::Ffi(m, f)),
            Expression::FfiApp(m, f, args) => mk(Expression::FfiApp(
                m,
                f,
                args.into_iter()
                    .map(|(e, t)| (self.reduce_exp(env, e), self.reduce_con(env, t)))
                    .collect(),
            )),
            Expression::App(e1, e2) => {
                let de_env = de_known(env);
                let e1_red = self.reduce_exp(env, *e1);
                let e2_red = self.reduce_exp(env, *e2);
                let e1_span = e1_red.span.clone();
                match e1_red.node {
                    // ELet distribution: (let x = v in body) arg  →  let x = v in (body (lift arg))
                    Expression::Let(x, t, e1i, e2i) => {
                        let e2_lifted = shift_exp(e2_red, 0, 1, 0, 0);
                        let app =
                            Located::new(Expression::App(e2i, Box::new(e2_lifted)), span.clone());
                        let mut inner: Env = vec![EnvItem::UnknownE];
                        inner.extend_from_slice(&de_env);
                        let app_red = self.reduce_exp(&inner, app);
                        mk(Expression::Let(x, t, e1i, Box::new(app_red)))
                    }
                    // Beta: (fn x : dom => body) arg
                    Expression::Abs(x, dom, ran, body) => {
                        if is_erased_zero_witness_app(&e2_red, &dom) {
                            return Located::new(Expression::Abs(x, dom, ran, body), e1_span);
                        }
                        if count_exp(&body) <= 1
                            || passive(&e2_red.node)
                            || function_inside_type(&dom)
                        {
                            let mut inner: Env = vec![EnvItem::KnownE(e2_red)];
                            inner.extend_from_slice(&de_env);
                            self.reduce_exp(&inner, *body)
                        } else {
                            let dom_red = self.reduce_con(&de_env, dom);
                            let mut inner: Env = vec![EnvItem::UnknownE];
                            inner.extend_from_slice(&de_env);
                            let body_red = self.reduce_exp(&inner, *body);
                            mk(Expression::Let(
                                x,
                                dom_red,
                                Box::new(e2_red),
                                Box::new(body_red),
                            ))
                        }
                    }
                    // Push app through case when result is a function type
                    Expression::Case(
                        disc,
                        arms,
                        CaseMeta {
                            disc: d_t,
                            result: res_t,
                        },
                    ) if matches!(&res_t.node, Constructor::TFun(_, _)) => {
                        if let Constructor::TFun(_, c2) = res_t.node {
                            let c2_red = self.reduce_con(&de_env, *c2);
                            let arms_new = arms
                                .into_iter()
                                .map(|(p, body)| {
                                    let nb = pat_binds_n(&p);
                                    let mut pe: Env = (0..nb).map(|_| EnvItem::UnknownE).collect();
                                    pe.extend_from_slice(&de_env);
                                    let e2_lift = shift_exp(e2_red.clone(), 0, nb as isize, 0, 0);
                                    let app = Located::new(
                                        Expression::App(Box::new(body), Box::new(e2_lift)),
                                        span.clone(),
                                    );
                                    let body_new = self.reduce_exp(&pe, app);
                                    (p, body_new)
                                })
                                .collect();
                            let d_t_red = self.reduce_con(&de_env, d_t);
                            mk(Expression::Case(
                                disc,
                                arms_new,
                                CaseMeta {
                                    disc: d_t_red,
                                    result: c2_red,
                                },
                            ))
                        } else {
                            mk(Expression::App(
                                Box::new(Located::new(
                                    Expression::Case(
                                        disc,
                                        arms,
                                        CaseMeta {
                                            disc: d_t,
                                            result: res_t,
                                        },
                                    ),
                                    e1_span,
                                )),
                                Box::new(e2_red),
                            ))
                        }
                    }
                    other => mk(Expression::App(
                        Box::new(Located::new(other, e1_span)),
                        Box::new(e2_red),
                    )),
                }
            }
            Expression::Abs(x, dom, ran, body) => {
                let mut inner: Env = vec![EnvItem::UnknownE];
                inner.extend_from_slice(env);
                mk(Expression::Abs(
                    x,
                    self.reduce_con(env, dom),
                    self.reduce_con(env, ran),
                    Box::new(self.reduce_exp(&inner, *body)),
                ))
            }
            Expression::CApp(e, c) => {
                let e_red = self.reduce_exp(env, *e);
                let c_red = self.reduce_con(env, c);
                let e_red_span = e_red.span.clone();
                match e_red.node {
                    Expression::CAbs(_, _, body) => {
                        let mut inner: Env = vec![EnvItem::KnownC(c_red)];
                        inner.extend_from_slice(&de_known(env));
                        self.reduce_exp(&inner, *body)
                    }
                    // Push CApp through case with TCFun result
                    Expression::Case(
                        disc,
                        arms,
                        CaseMeta {
                            disc: d_t,
                            result: res_t,
                        },
                    ) if matches!(&res_t.node, Constructor::TCFun(_, _, _)) => {
                        if let Constructor::TCFun(_, _, c2) = res_t.node {
                            // Substitute c_red for CRel 0 in c2
                            let c2_sub = {
                                let sub_env: Env = vec![EnvItem::KnownC(c_red.clone())];
                                // Dummy reducer just for substitution
                                let tmp = Reducer::new();
                                tmp.reduce_con(&sub_env, *c2)
                            };
                            let de_env = de_known(env);
                            let c2_red = self.reduce_con(&de_env, c2_sub);
                            let d_t_red = self.reduce_con(&de_env, d_t);
                            let arms_new = arms
                                .into_iter()
                                .map(|(p, body)| {
                                    let nb = pat_binds_n(&p);
                                    let mut pe: Env = (0..nb).map(|_| EnvItem::UnknownE).collect();
                                    pe.extend_from_slice(&de_env);
                                    let capp = Located::new(
                                        Expression::CApp(Box::new(body), c_red.clone()),
                                        span.clone(),
                                    );
                                    let body_new = self.reduce_exp(&pe, capp);
                                    (p, body_new)
                                })
                                .collect();
                            mk(Expression::Case(
                                disc,
                                arms_new,
                                CaseMeta {
                                    disc: d_t_red,
                                    result: c2_red,
                                },
                            ))
                        } else {
                            mk(Expression::CApp(
                                Box::new(Located::new(
                                    Expression::Case(
                                        disc,
                                        arms,
                                        CaseMeta {
                                            disc: d_t,
                                            result: res_t,
                                        },
                                    ),
                                    e_red_span,
                                )),
                                c_red,
                            ))
                        }
                    }
                    other => mk(Expression::CApp(
                        Box::new(Located::new(other, e_red_span)),
                        c_red,
                    )),
                }
            }
            Expression::CAbs(x, k, body) => {
                let mut inner: Env = vec![EnvItem::UnknownC];
                inner.extend_from_slice(env);
                mk(Expression::CAbs(
                    x,
                    Box::new(self.reduce_kind(env, *k)),
                    Box::new(self.reduce_exp(&inner, *body)),
                ))
            }
            Expression::KApp(e, k) => {
                let e_red = self.reduce_exp(env, *e);
                match e_red.node {
                    Expression::KAbs(_, body) => {
                        let mut inner: Env = vec![EnvItem::KnownK(*k)];
                        inner.extend_from_slice(&de_known(env));
                        self.reduce_exp(&inner, *body)
                    }
                    other => mk(Expression::KApp(
                        Box::new(Located::new(other, span.clone())),
                        Box::new(self.reduce_kind(env, *k)),
                    )),
                }
            }
            Expression::KAbs(x, body) => {
                let mut inner: Env = vec![EnvItem::UnknownK];
                inner.extend_from_slice(env);
                mk(Expression::KAbs(
                    x,
                    Box::new(self.reduce_exp(&inner, *body)),
                ))
            }
            Expression::Record(fields) => mk(Expression::Record(
                fields
                    .into_iter()
                    .map(|(x, e, t)| {
                        (
                            self.reduce_con(env, x),
                            self.reduce_exp(env, e),
                            self.reduce_con(env, t),
                        )
                    })
                    .collect(),
            )),
            Expression::Field(e, c, FieldMeta { field, rest }) => {
                let e_red = self.reduce_exp(env, *e);
                let c_red = self.reduce_con(env, c);
                // If record literal and field name known, project directly
                if let (Expression::Record(xcs), Constructor::Name(ref x)) =
                    (&e_red.node, &c_red.node)
                {
                    if let Some((_, found_e, _)) = xcs
                        .iter()
                        .find(|(name, _, _)| matches!(&name.node, Constructor::Name(n) if n == x))
                    {
                        return found_e.clone();
                    }
                }
                mk(Expression::Field(
                    Box::new(e_red),
                    c_red,
                    FieldMeta {
                        field: self.reduce_con(env, field),
                        rest: self.reduce_con(env, rest),
                    },
                ))
            }
            Expression::Concat(e1, c1, e2, c2) => {
                let e1_red = self.reduce_exp(env, *e1);
                let e2_red = self.reduce_exp(env, *e2);
                match (&e1_red.node, &e2_red.node) {
                    (Expression::Record(xes1), Expression::Record(xes2)) => {
                        let mut all = xes1.clone();
                        all.extend_from_slice(xes2);
                        mk(Expression::Record(all))
                    }
                    _ => {
                        let c1_red = self.reduce_con(env, c1);
                        let c2_red = self.reduce_con(env, c2);
                        // If both type rows are known records, project fields
                        if let (Constructor::Record(_, xcs1), Constructor::Record(_, xcs2)) =
                            (&c1_red.node, &c2_red.node)
                        {
                            let (fields1, rest) = do_parts(&e1_red, xcs1, vec![], span.clone());
                            let (fields2, _) = do_parts(&e2_red, xcs2, rest, span.clone());
                            let fields = fields1.into_iter().chain(fields2).collect::<Vec<_>>();
                            if !fields.is_empty() {
                                let de_env = de_known(env);
                                return self.reduce_exp(&de_env, mk(Expression::Record(fields)));
                            }
                        }
                        mk(Expression::Concat(
                            Box::new(e1_red),
                            c1_red,
                            Box::new(e2_red),
                            c2_red,
                        ))
                    }
                }
            }
            Expression::Cut(e, c, FieldMeta { field, rest }) => {
                let e_red = self.reduce_exp(env, *e);
                let c_red = self.reduce_con(env, c);
                let rest_red = self.reduce_con(env, rest);
                // If record literal and field name known, filter directly
                if let (Expression::Record(xes), Constructor::Name(x)) = (&e_red.node, &c_red.node)
                {
                    if xes
                        .iter()
                        .all(|(n, _, _)| matches!(&n.node, Constructor::Name(_)))
                    {
                        let x = x.clone();
                        let filtered: Vec<_> = xes
                            .iter()
                            .filter(
                                |(n, _, _)| !matches!(&n.node, Constructor::Name(nm) if nm == &x),
                            )
                            .cloned()
                            .collect();
                        return mk(Expression::Record(filtered));
                    }
                }
                // If rest type is a known record, project fields
                if let Constructor::Record(_, xcs) = &rest_red.node {
                    let xcs = xcs.clone();
                    let (fields, _) = do_parts(&e_red, &xcs, vec![], span.clone());
                    if !fields.is_empty() {
                        let de_env = de_known(env);
                        return self.reduce_exp(&de_env, mk(Expression::Record(fields)));
                    }
                }
                mk(Expression::Cut(
                    Box::new(e_red),
                    c_red,
                    FieldMeta {
                        field: self.reduce_con(env, field),
                        rest: rest_red,
                    },
                ))
            }
            Expression::CutMulti(e, c, RestMeta { rest }) => {
                let e_red = self.reduce_exp(env, *e);
                let c_red = self.reduce_con(env, c);
                let rest_red = self.reduce_con(env, rest);
                // Record literal with known cut set → filter
                if let (Expression::Record(xes), Constructor::Record(_, xcs)) =
                    (&e_red.node, &c_red.node)
                {
                    if xes
                        .iter()
                        .all(|(n, _, _)| matches!(&n.node, Constructor::Name(_)))
                        && xcs
                            .iter()
                            .all(|(n, _)| matches!(&n.node, Constructor::Name(_)))
                    {
                        let cut: Vec<String> = xcs
                            .iter()
                            .filter_map(|(n, _)| {
                                if let Constructor::Name(x) = &n.node {
                                    Some(x.clone())
                                } else {
                                    None
                                }
                            })
                            .collect();
                        let filtered: Vec<_> = xes
                            .iter()
                            .filter(|(n, _, _)| {
                                !matches!(&n.node, Constructor::Name(x) if cut.contains(x))
                            })
                            .cloned()
                            .collect();
                        return mk(Expression::Record(filtered));
                    }
                }
                // If rest type is a known record, project fields
                if let Constructor::Record(_, xcs) = &rest_red.node {
                    let xcs = xcs.clone();
                    let (fields, _) = do_parts(&e_red, &xcs, vec![], span.clone());
                    if !fields.is_empty() {
                        let de_env = de_known(env);
                        return self.reduce_exp(&de_env, mk(Expression::Record(fields)));
                    }
                }
                mk(Expression::CutMulti(
                    Box::new(e_red),
                    c_red,
                    RestMeta { rest: rest_red },
                ))
            }
            // Single-arm case with empty record pattern: just the body
            Expression::Case(_, mut arms, _)
                if arms.len() == 1
                    && matches!(&arms[0].0.node, Pattern::Record(fs) if fs.is_empty()) =>
            {
                match arms.pop() {
                    Some((_, body)) => self.reduce_exp(env, body),
                    None => mk(Expression::Prim(Prim::Int(0))),
                }
            }
            Expression::Case(
                disc,
                arms,
                CaseMeta {
                    disc: d_t,
                    result: res_t,
                },
            ) => {
                // Try static matching before falling back to dynamic case
                match try_static_match(env, &arms, &disc) {
                    StaticMatch::Yes(extended_env, body) => self.reduce_exp(&extended_env, body),
                    StaticMatch::No => {
                        // All arms are statically impossible — shouldn't happen
                        self.push_case(*disc, arms, d_t, res_t, env, span)
                    }
                    StaticMatch::Maybe => self.push_case(*disc, arms, d_t, res_t, env, span),
                }
            }
            Expression::Write(e) => mk(Expression::Write(Box::new(self.reduce_exp(env, *e)))),
            Expression::Closure(n, es) => mk(Expression::Closure(
                n,
                es.into_iter().map(|e| self.reduce_exp(env, e)).collect(),
            )),
            Expression::Let(x, t, e1, e2) => {
                let e1_original = *e1;
                let e1_red = self.reduce_exp(env, e1_original.clone());
                let t_red = self.reduce_con(env, t);
                if not_ffi(&t_red.node)
                    && (passive(&e1_red.node)
                        || count_exp(&e2) <= 1
                        || function_inside_type(&t_red))
                {
                    // Match reduce.sml: re-reduce the original binding under the lifted env.
                    let mut inner: Env = vec![EnvItem::KnownE(e1_original)];
                    inner.extend_from_slice(env);
                    self.reduce_exp(&inner, *e2)
                } else {
                    let mut inner: Env = vec![EnvItem::UnknownE];
                    inner.extend_from_slice(env);
                    let e2_red = self.reduce_exp(&inner, *e2);
                    mk(Expression::Let(
                        x,
                        t_red,
                        Box::new(e1_red),
                        Box::new(e2_red),
                    ))
                }
            }
            Expression::ServerCall(n, args, t, fm) => mk(Expression::ServerCall(
                n,
                args.into_iter().map(|e| self.reduce_exp(env, e)).collect(),
                self.reduce_con(env, t),
                fm,
            )),
        }
    }

    fn push_case(
        &self,
        disc: LocatedExpression,
        arms: Vec<(LocatedPattern, LocatedExpression)>,
        d_t: LocatedConstructor,
        res_t: LocatedConstructor,
        env: &[EnvItem],
        span: Span,
    ) -> LocatedExpression {
        let mk = |node| Located::new(node, span.clone());
        let disc_red = self.reduce_exp(env, disc);
        let arms_red = arms
            .into_iter()
            .map(|(p, body)| {
                let nb = pat_binds_n(&p);
                let mut pe: Env = (0..nb).map(|_| EnvItem::UnknownE).collect();
                pe.extend_from_slice(env);
                let p_red = self.reduce_pat(env, p);
                let body_red = self.reduce_exp(&pe, body);
                (p_red, body_red)
            })
            .collect();
        mk(Expression::Case(
            Box::new(disc_red),
            arms_red,
            CaseMeta {
                disc: self.reduce_con(env, d_t),
                result: self.reduce_con(env, res_t),
            },
        ))
    }

    fn find_exp(
        &self,
        env: &[EnvItem],
        n_orig: usize,
        n: usize,
        nudge: isize,
        lift_k: usize,
        lift_c: usize,
        lift_e: usize,
        span: Span,
    ) -> LocatedExpression {
        match env.first() {
            None => Located::new(Expression::Rel((n_orig as isize + nudge) as usize), span),
            Some(item) => match item {
                EnvItem::UnknownK => self.find_exp(
                    &env[1..],
                    n_orig,
                    n,
                    nudge,
                    lift_k + 1,
                    lift_c,
                    lift_e,
                    span,
                ),
                EnvItem::KnownK(_) => {
                    self.find_exp(&env[1..], n_orig, n, nudge, lift_k, lift_c, lift_e, span)
                }
                EnvItem::UnknownC => self.find_exp(
                    &env[1..],
                    n_orig,
                    n,
                    nudge,
                    lift_k,
                    lift_c + 1,
                    lift_e,
                    span,
                ),
                EnvItem::KnownC(_) => {
                    self.find_exp(&env[1..], n_orig, n, nudge, lift_k, lift_c, lift_e, span)
                }
                EnvItem::Lift(lk, lc, le) => self.find_exp(
                    &env[1..],
                    n_orig,
                    n,
                    nudge + *le as isize,
                    lift_k + lk,
                    lift_c + lc,
                    lift_e + le,
                    span,
                ),
                EnvItem::UnknownE => {
                    if n == 0 {
                        Located::new(Expression::Rel((n_orig as isize + nudge) as usize), span)
                    } else {
                        self.find_exp(
                            &env[1..],
                            n_orig,
                            n - 1,
                            nudge,
                            lift_k,
                            lift_c,
                            lift_e + 1,
                            span,
                        )
                    }
                }
                EnvItem::KnownE(e) => {
                    if n == 0 {
                        // Match reduce.sml: re-run reduction under a synthetic
                        // Lift environment instead of pre-shifting and then
                        // lifting again.
                        let mut lift_env: Env = vec![EnvItem::Lift(lift_k, lift_c, lift_e)];
                        lift_env.extend_from_slice(&env[1..]);
                        self.reduce_exp(&lift_env, e.clone())
                    } else {
                        self.find_exp(
                            &env[1..],
                            n_orig,
                            n - 1,
                            nudge - 1,
                            lift_k,
                            lift_c,
                            lift_e,
                            span,
                        )
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// do_parts: project named fields from a record expression
// ---------------------------------------------------------------------------

/// For each `(name, typ)` in `xcs`, build `(name, e.name, typ)` for use in
/// expanding known-row Concat / Cut into a fresh Record literal.
fn do_parts(
    e: &LocatedExpression,
    xcs: &[(LocatedConstructor, LocatedConstructor)],
    mut rest_xcs: Vec<(LocatedConstructor, LocatedConstructor)>,
    span: Span,
) -> (
    Vec<(LocatedConstructor, LocatedExpression, LocatedConstructor)>,
    Vec<(LocatedConstructor, LocatedConstructor)>,
) {
    let k = Located::new(Kind::Type, span.clone());
    let fields = xcs
        .iter()
        .map(|(name, typ)| {
            let rest_con = Located::new(
                Constructor::Record(Box::new(k.clone()), rest_xcs.clone()),
                span.clone(),
            );
            let field_exp = Located::new(
                Expression::Field(
                    Box::new(e.clone()),
                    name.clone(),
                    FieldMeta {
                        field: typ.clone(),
                        rest: rest_con,
                    },
                ),
                span.clone(),
            );
            rest_xcs.insert(0, (name.clone(), typ.clone()));
            (name.clone(), field_exp, typ.clone())
        })
        .collect();
    (fields, rest_xcs)
}

// ---------------------------------------------------------------------------
// Static pattern matching
// ---------------------------------------------------------------------------

enum StaticMatch {
    Yes(Env, LocatedExpression),
    No,
    Maybe,
}

/// Check whether the discriminant `e` statically matches any pattern in `arms`.
/// Returns `Yes(env', body)` if the first matching arm is found statically,
/// `No` if the first arm definitely doesn't match, or `Maybe` to fall back to
/// dynamic dispatch.
fn try_static_match(
    env: &[EnvItem],
    arms: &[(LocatedPattern, LocatedExpression)],
    e: &LocatedExpression,
) -> StaticMatch {
    let baseline = env.len();
    for (pat, body) in arms {
        match match_pat(env, pat, e, baseline) {
            PatMatch::Yes(new_env) => return StaticMatch::Yes(new_env, body.clone()),
            PatMatch::No => continue,
            PatMatch::Maybe => return StaticMatch::Maybe,
        }
    }
    StaticMatch::No
}

enum PatMatch {
    Yes(Env),
    No,
    Maybe,
}

fn match_pat(
    env: &[EnvItem],
    pat: &LocatedPattern,
    e: &LocatedExpression,
    baseline: usize,
) -> PatMatch {
    match (&pat.node, &e.node) {
        (Pattern::Var(_, _), _) => {
            // Variable patterns always match; bind e (lifted by current depth delta)
            let lift = env.len() - baseline;
            let e_lifted = shift_exp(e.clone(), 0, lift as isize, 0, 0);
            let mut new_env: Env = vec![EnvItem::KnownE(e_lifted)];
            new_env.extend_from_slice(env);
            PatMatch::Yes(new_env)
        }
        (Pattern::Prim(p1), Expression::Prim(p2)) => {
            if prim_eq(p1, p2) {
                PatMatch::Yes(env.to_vec())
            } else {
                PatMatch::No
            }
        }
        (
            Pattern::Constructor(_, PatternConstructor::Var(n1), _, None),
            Expression::Constructor(_, PatternConstructor::Var(n2), _, None),
        ) => {
            if n1 == n2 {
                PatMatch::Yes(env.to_vec())
            } else {
                PatMatch::No
            }
        }
        (
            Pattern::Constructor(_, PatternConstructor::Var(n1), _, Some(sub_pat)),
            Expression::Constructor(_, PatternConstructor::Var(n2), _, Some(sub_exp)),
        ) => {
            if n1 != n2 {
                PatMatch::No
            } else {
                match_pat(env, sub_pat, sub_exp, baseline)
            }
        }
        (
            Pattern::Constructor(
                _,
                PatternConstructor::Ffi {
                    module: m1,
                    con: c1,
                    ..
                },
                _,
                None,
            ),
            Expression::Constructor(
                _,
                PatternConstructor::Ffi {
                    module: m2,
                    con: c2,
                    ..
                },
                _,
                None,
            ),
        ) => {
            if m1 == m2 && c1 == c2 {
                PatMatch::Yes(env.to_vec())
            } else {
                PatMatch::No
            }
        }
        (
            Pattern::Constructor(
                _,
                PatternConstructor::Ffi {
                    module: m1,
                    con: c1,
                    ..
                },
                _,
                Some(sub_pat),
            ),
            Expression::Constructor(
                _,
                PatternConstructor::Ffi {
                    module: m2,
                    con: c2,
                    ..
                },
                _,
                Some(sub_exp),
            ),
        ) => {
            if m1 != m2 || c1 != c2 {
                PatMatch::No
            } else {
                match_pat(env, sub_pat, sub_exp, baseline)
            }
        }
        (Pattern::Record(xps), Expression::Record(xes)) => {
            // Only works if all field names are known (CName)
            if xes
                .iter()
                .any(|(n, _, _)| !matches!(&n.node, Constructor::Name(_)))
            {
                return PatMatch::Maybe;
            }
            let mut cur_env: Env = env.to_vec();
            for (field_name, sub_pat, _) in xps {
                // Find matching field in record expression
                match xes.iter().find(|(n, _, _)| {
                    matches!(
                        &n.node,
                        Constructor::Name(record_label)
                            if record_label.as_str() == field_name.as_str()
                    )
                }) {
                    None => return PatMatch::No,
                    Some((_, sub_exp, _)) => {
                        match match_pat(&cur_env, sub_pat, sub_exp, baseline) {
                            PatMatch::No => return PatMatch::No,
                            PatMatch::Maybe => return PatMatch::Maybe,
                            PatMatch::Yes(new_env) => cur_env = new_env,
                        }
                    }
                }
            }
            PatMatch::Yes(cur_env)
        }
        _ => PatMatch::Maybe,
    }
}

fn prim_eq(p1: &Prim, p2: &Prim) -> bool {
    match (p1, p2) {
        (Prim::Int(a), Prim::Int(b)) => a == b,
        (Prim::Float(a), Prim::Float(b)) => a == b,
        (Prim::String(_, a), Prim::String(_, b)) => a == b,
        (Prim::Char(a), Prim::Char(b)) => a == b,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// mayInline decision
// ---------------------------------------------------------------------------

fn may_inline(
    poly_c: &BTreeSet<usize>,
    n: usize,
    t: &LocatedConstructor,
    e: &LocatedExpression,
    source_name: &str,
    uses: &HashMap<usize, usize>,
    settings: &Settings,
) -> bool {
    if settings.never_inline.contains(source_name) {
        return false;
    }
    let use_count = uses.get(&n).copied().unwrap_or(0);
    use_count <= 1
        || matches!(&e.node, Expression::Record(_))
        || is_policy(&t.node)
        || is_poly_con(poly_c, t)
        || contains_constructor_compile_time_ops(e)
        || count_exp(e) <= settings.core_inline as usize
}

fn contains_constructor_compile_time_ops(exp: &LocatedExpression) -> bool {
    fn capp_head<'a>(exp: &'a LocatedExpression) -> &'a LocatedExpression {
        let mut cur = exp;
        while let Expression::CApp(inner, _) = &cur.node {
            cur = inner;
        }
        cur
    }

    match &exp.node {
        Expression::CAbs(_, _, _) => true,
        Expression::CApp(function, _) => {
            !matches!(capp_head(function).node, Expression::Ffi(ref m, _) if m == "Basis")
                || contains_constructor_compile_time_ops(function)
        }
        Expression::Prim(_) | Expression::Rel(_) | Expression::Named(_) | Expression::Ffi(_, _) => {
            false
        }
        Expression::Constructor(_, _, _, arg) => arg
            .as_deref()
            .is_some_and(contains_constructor_compile_time_ops),
        Expression::FfiApp(_, _, args) => args
            .iter()
            .any(|(arg, _)| contains_constructor_compile_time_ops(arg)),
        Expression::App(left, right) => {
            contains_constructor_compile_time_ops(left)
                || contains_constructor_compile_time_ops(right)
        }
        Expression::Abs(_, _, _, body)
        | Expression::KAbs(_, body)
        | Expression::Write(body)
        | Expression::KApp(body, _) => contains_constructor_compile_time_ops(body),
        Expression::Record(fields) => fields
            .iter()
            .any(|(_, value, _)| contains_constructor_compile_time_ops(value)),
        Expression::Field(record, _, _)
        | Expression::Cut(record, _, _)
        | Expression::CutMulti(record, _, _) => contains_constructor_compile_time_ops(record),
        Expression::Concat(left, _, right, _) => {
            contains_constructor_compile_time_ops(left)
                || contains_constructor_compile_time_ops(right)
        }
        Expression::Case(disc, arms, _) => {
            contains_constructor_compile_time_ops(disc)
                || arms
                    .iter()
                    .any(|(_, arm)| contains_constructor_compile_time_ops(arm))
        }
        Expression::Closure(_, envs) | Expression::ServerCall(_, envs, _, _) => {
            envs.iter().any(contains_constructor_compile_time_ops)
        }
        Expression::Let(_, _, bound, body) => {
            contains_constructor_compile_time_ops(bound)
                || contains_constructor_compile_time_ops(body)
        }
    }
}

// ---------------------------------------------------------------------------
// Top-level reduce
// ---------------------------------------------------------------------------

/// Run the global reduction pass over a Core file.
///
/// Mirrors `Reduce.reduce` from `reduce.sml`.
fn reduce_pass(
    file: File,
    settings: &Settings,
    seed_named_c: HashMap<usize, LocatedConstructor>,
    seed_named_e: HashMap<usize, LocatedExpression>,
    seed_poly_c: BTreeSet<usize>,
) -> (
    File,
    HashMap<usize, LocatedConstructor>,
    HashMap<usize, LocatedExpression>,
    BTreeSet<usize>,
) {
    let uses = count_named_uses(&file);
    let mut reducer = Reducer::with_knowns(seed_named_c, seed_named_e);
    // poly_c: set of constructor ids whose types are polymorphic
    let mut poly_c = seed_poly_c;

    let mut out = Vec::with_capacity(file.len());
    for d in file {
        let span = d.span.clone();
        let mk_decl = |node| Located::new(node, span.clone());
        match d.node {
            Declaration::Constructor(x, n, k, c) => {
                let k_red = reducer.reduce_kind(&[], k);
                let c_red = reducer.reduce_con(&[], c);
                if is_poly_con(&poly_c, &c_red) {
                    poly_c.insert(n);
                }
                reducer.named_c.insert(n, c_red.clone());
                out.push(mk_decl(Declaration::Constructor(x, n, k_red, c_red)));
            }
            Declaration::Datatype(dts) => {
                let dts_red: Vec<crate::core::DatatypeDecl> = dts
                    .into_iter()
                    .map(|dt| {
                        let env: Env = (0..dt.params.len()).map(|_| EnvItem::UnknownC).collect();
                        let constrs: Vec<(String, usize, Option<LocatedConstructor>)> = dt
                            .constrs
                            .into_iter()
                            .map(|(cname, cid, co)| {
                                (cname, cid, co.map(|c| reducer.reduce_con(&env, c)))
                            })
                            .collect();
                        // If any constructor argument type is polymorphic, mark the datatype
                        if constrs.iter().any(
                            |(_, _, co): &(String, usize, Option<LocatedConstructor>)| {
                                co.as_ref().is_some_and(|c| is_poly_con(&poly_c, c))
                            },
                        ) {
                            poly_c.insert(dt.id);
                        }
                        crate::core::DatatypeDecl {
                            name: dt.name,
                            id: dt.id,
                            params: dt.params,
                            constrs,
                        }
                    })
                    .collect();
                out.push(mk_decl(Declaration::Datatype(dts_red)));
            }
            Declaration::Val(x, n, t, e, s) => {
                let t_red = reducer.reduce_con(&[], t);
                let e_red = reducer.reduce_exp(&[], e.clone());
                let inline = may_inline(&poly_c, n, &t_red, &e_red, &s, &uses, settings);
                if std::env::var("URWEB_DEBUG_GLOBAL_INLINE").ok().as_deref() == Some("1")
                    && matches!(
                        s.as_str(),
                        "foldUR" | "foldUR2" | "foldR2" | "mapUX" | "mapUX2"
                    )
                {
                    eprintln!(
                        "URWEB_DEBUG_GLOBAL_INLINE name={s}#{n} inline={inline} uses={} expr={:?}",
                        uses.get(&n).copied().unwrap_or(0),
                        e_red.node
                    );
                }
                if inline {
                    reducer.named_e.insert(n, e_red.clone());
                }
                out.push(mk_decl(Declaration::Val(x, n, t_red, e_red, s)));
            }
            Declaration::ValRec(vis) => {
                if std::env::var("URWEB_DEBUG_GLOBAL_INLINE").ok().as_deref() == Some("1") {
                    for (x, n, _, _, _) in &vis {
                        if matches!(
                            x.as_str(),
                            "foldUR" | "foldUR2" | "foldR2" | "mapUX" | "mapUX2"
                        ) {
                            eprintln!("URWEB_DEBUG_GLOBAL_INLINE valrec={x}#{n}");
                        }
                    }
                }
                let vis_red = vis
                    .into_iter()
                    .map(|(x, n, t, e, s)| {
                        (
                            x,
                            n,
                            reducer.reduce_con(&[], t),
                            reducer.reduce_exp(&[], e),
                            s,
                        )
                    })
                    .collect();
                out.push(mk_decl(Declaration::ValRec(vis_red)));
            }
            Declaration::Export(ek, n, has_state) => {
                out.push(mk_decl(Declaration::Export(ek, n, has_state)));
            }
            Declaration::Table {
                sql_name,
                id,
                con,
                sql_con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
            } => {
                out.push(mk_decl(Declaration::Table {
                    sql_name,
                    id,
                    con: reducer.reduce_con(&[], con),
                    sql_con,
                    exp: reducer.reduce_exp(&[], exp),
                    pk_con: reducer.reduce_con(&[], pk_con),
                    pk_exp: reducer.reduce_exp(&[], pk_exp),
                    unique_con: reducer.reduce_con(&[], unique_con),
                }));
            }
            Declaration::Sequence(x, n, sql) => {
                out.push(mk_decl(Declaration::Sequence(x, n, sql)));
            }
            Declaration::View(x, n, sql, e, c) => {
                out.push(mk_decl(Declaration::View(
                    x,
                    n,
                    sql,
                    reducer.reduce_exp(&[], e),
                    reducer.reduce_con(&[], c),
                )));
            }
            Declaration::Index(e1, e2) => {
                out.push(mk_decl(Declaration::Index(
                    reducer.reduce_exp(&[], e1),
                    reducer.reduce_exp(&[], e2),
                )));
            }
            Declaration::Database(s) => {
                out.push(mk_decl(Declaration::Database(s)));
            }
            Declaration::Cookie(x, n, c, s) => {
                out.push(mk_decl(Declaration::Cookie(
                    x,
                    n,
                    reducer.reduce_con(&[], c),
                    s,
                )));
            }
            Declaration::Style(x, n, s) => {
                out.push(mk_decl(Declaration::Style(x, n, s)));
            }
            Declaration::Task(e1, e2) => {
                out.push(mk_decl(Declaration::Task(
                    reducer.reduce_exp(&[], e1),
                    reducer.reduce_exp(&[], e2),
                )));
            }
            Declaration::Policy(e) => {
                out.push(mk_decl(Declaration::Policy(reducer.reduce_exp(&[], e))));
            }
            Declaration::OnError(n) => {
                out.push(mk_decl(Declaration::OnError(n)));
            }
        }
    }
    (out, reducer.named_c, reducer.named_e, poly_c)
}

pub fn reduce(file: File, settings: &Settings) -> File {
    let (_, named_c, named_e, poly_c) = reduce_pass(
        file.clone(),
        settings,
        HashMap::new(),
        HashMap::new(),
        BTreeSet::new(),
    );
    let (out, _, _, _) = reduce_pass(file, settings, named_c, named_e, poly_c);
    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use crate::settings::Settings;
    use anyhow::Context as _; // .with_context() on Option in tests

    fn dummy() -> Span {
        Span::dummy()
    }

    fn unit_con() -> LocatedConstructor {
        Located::new(Constructor::Unit, dummy())
    }

    fn prim_exp() -> LocatedExpression {
        Located::new(Expression::Prim(Prim::Int(0)), dummy())
    }

    fn record_row(names: &[&str]) -> Vec<(LocatedConstructor, LocatedConstructor)> {
        names
            .iter()
            .map(|name| {
                (
                    Located::new(Constructor::Name((*name).into()), dummy()),
                    unit_con(),
                )
            })
            .collect()
    }

    fn rest_row_names(meta: &FieldMeta) -> Option<Vec<String>> {
        match &meta.rest.node {
            Constructor::Record(_, fields) => Some(
                fields
                    .iter()
                    .filter_map(|(name, _)| match &name.node {
                        Constructor::Name(name) => Some(name.clone()),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => None,
        }
    }

    fn val_decl(id: usize, e: LocatedExpression) -> LocatedDeclaration {
        Located::new(
            Declaration::Val("x".into(), id, unit_con(), e, "x".into()),
            dummy(),
        )
    }

    fn export_decl(id: usize) -> LocatedDeclaration {
        Located::new(
            Declaration::Export(
                crate::export::ExportKind::Link(crate::export::Effect::ReadOnly),
                id,
                false,
            ),
            dummy(),
        )
    }

    #[test]
    fn empty_file_stays_empty() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Catches mutant: reduce panics or adds phantom decls on empty input.
        let result = reduce(vec![], &Settings::default());
        assert!(result.is_empty(), "reduce of empty file must be empty");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn val_decl_preserved() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Catches mutant: reduce drops Val declarations.
        let file = vec![val_decl(1, prim_exp()), export_decl(1)];
        let result = reduce(file, &Settings::default());
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Val(_, id, _, _, _) if *id == 1)),
            "Val decl must be preserved by reduce"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn database_decl_preserved() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Catches mutant: reduce drops Database declarations.
        let file = vec![Located::new(Declaration::Database("mydb".into()), dummy())];
        let result = reduce(file, &Settings::default());
        assert!(
            result
                .iter()
                .any(|d| matches!(&d.node, Declaration::Database(s) if s == "mydb")),
            "Database decl must be preserved by reduce"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn named_exp_inlined() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Catches mutant: named_e map is never populated, so Named refs are not inlined.
        // val f (id=1) : Unit = prim  -- use_count=1 (from id=2)
        // val g (id=2) : Unit = Named(1)
        // Named(1) should be inlined to prim since use_count <= 1.
        let named_ref = Located::new(Expression::Named(1), dummy());
        let file = vec![
            val_decl(1, prim_exp()),
            val_decl(2, named_ref),
            export_decl(2),
        ];
        let result = reduce(file, &Settings::default());
        // g's body should now be Prim(0) (inlined from f)
        let g_body = result
            .iter()
            .find_map(|d| match &d.node {
                Declaration::Val(_, 2, _, e, _) => Some(e.clone()),
                _ => None,
            })
            .with_context(|| "val id=2 must exist")?;
        assert!(
            matches!(g_body.node, Expression::Prim(_)),
            "Named(1) must be inlined to Prim when use_count <= 1"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn beta_reduction_of_app_abs() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Catches mutant: App + Abs case falls through to the App node constructor.
        // (fn x : Unit => Rel(0)) Prim(42)  →  Prim(42)
        let span = dummy();
        let body = Located::new(Expression::Rel(0), span.clone());
        let lam = Located::new(
            Expression::Abs("x".into(), unit_con(), unit_con(), Box::new(body)),
            span.clone(),
        );
        let arg = Located::new(Expression::Prim(Prim::Int(42)), span.clone());
        let app = Located::new(Expression::App(Box::new(lam), Box::new(arg)), span.clone());
        let file = vec![Located::new(
            Declaration::Val("f".into(), 1, unit_con(), app, "f".into()),
            span.clone(),
        )];
        let result = reduce(file, &Settings::default());
        // Find the Val declaration with id=1 and extract its body; panic with a message if absent.
        let body = match result.iter().find_map(|d| match &d.node {
            Declaration::Val(_, 1, _, e, _) => Some(e.clone()),
            _ => None,
        }) {
            Some(v) => v,
            None => panic!("no Val declaration with id=1 found in reduce output"),
        };
        assert!(
            matches!(body.node, Expression::Prim(Prim::Int(42))),
            "App of Abs must beta-reduce"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn app_inlines_non_passive_higher_order_argument() -> anyhow::Result<()> {
        let span = dummy();
        let field_name = Located::new(Constructor::Name("x".into()), span.clone());
        let dom = Located::new(
            Constructor::TFun(Box::new(unit_con()), Box::new(unit_con())),
            span.clone(),
        );
        let body = Located::new(
            Expression::Record(vec![
                (
                    field_name.clone(),
                    Located::new(Expression::Rel(0), span.clone()),
                    dom.clone(),
                ),
                (
                    Located::new(Constructor::Name("y".into()), span.clone()),
                    Located::new(Expression::Rel(0), span.clone()),
                    dom.clone(),
                ),
            ]),
            span.clone(),
        );
        let lam = Located::new(
            Expression::Abs("f".into(), dom.clone(), dom.clone(), Box::new(body)),
            span.clone(),
        );
        let arg = Located::new(
            Expression::App(
                Box::new(Located::new(
                    Expression::Ffi("Test".into(), "mk".into()),
                    span.clone(),
                )),
                Box::new(prim_exp()),
            ),
            span.clone(),
        );
        let reduced = Reducer::new().reduce_exp(
            &[],
            Located::new(Expression::App(Box::new(lam), Box::new(arg)), span),
        );
        assert!(
            matches!(reduced.node, Expression::Record(_)),
            "higher-order arguments should inline instead of introducing a let binder"
        );
        Ok(())
    }

    #[test]
    fn named_cabs_body_inlined_even_with_multiple_uses() -> anyhow::Result<()> {
        let cabs_body = Located::new(
            Expression::CAbs(
                "nm".into(),
                Box::new(Located::new(Kind::Name, dummy())),
                Box::new(Located::new(Expression::Prim(Prim::Int(0)), dummy())),
            ),
            dummy(),
        );
        let named_ref = Located::new(Expression::Named(1), dummy());
        let file = vec![
            val_decl(1, cabs_body),
            val_decl(2, named_ref.clone()),
            val_decl(3, named_ref),
            export_decl(2),
            export_decl(3),
        ];

        let result = reduce(file, &Settings::default());
        for wanted in [2, 3] {
            let body = result
                .iter()
                .find_map(|d| match &d.node {
                    Declaration::Val(_, id, _, e, _) if *id == wanted => Some(e.clone()),
                    _ => None,
                })
                .with_context(|| format!("val id={wanted} must exist"))?;
            assert!(
                matches!(body.node, Expression::CAbs(_, _, _)),
                "constructor-abstracted bodies must inline into use sites before monoization"
            );
        }
        Ok(())
    }

    #[test]
    fn non_basis_capps_mark_body_for_inlining() {
        let body = Located::new(
            Expression::CApp(
                Box::new(Located::new(Expression::Named(7), dummy())),
                unit_con(),
            ),
            dummy(),
        );
        assert!(contains_constructor_compile_time_ops(&body));
    }

    #[test]
    fn let_inlines_non_passive_higher_order_binding() -> anyhow::Result<()> {
        let span = dummy();
        let ty = Located::new(
            Constructor::TFun(Box::new(unit_con()), Box::new(unit_con())),
            span.clone(),
        );
        let bound = Located::new(
            Expression::App(
                Box::new(Located::new(
                    Expression::Ffi("Test".into(), "mk".into()),
                    span.clone(),
                )),
                Box::new(prim_exp()),
            ),
            span.clone(),
        );
        let body = Located::new(
            Expression::Record(vec![
                (
                    Located::new(Constructor::Name("x".into()), span.clone()),
                    Located::new(Expression::Rel(0), span.clone()),
                    ty.clone(),
                ),
                (
                    Located::new(Constructor::Name("y".into()), span.clone()),
                    Located::new(Expression::Rel(0), span.clone()),
                    ty.clone(),
                ),
            ]),
            span.clone(),
        );
        let reduced = Reducer::new().reduce_exp(
            &[],
            Located::new(
                Expression::Let("f".into(), ty, Box::new(bound), Box::new(body)),
                span,
            ),
        );
        assert!(
            matches!(reduced.node, Expression::Record(_)),
            "higher-order let bindings should inline instead of surviving to later passes"
        );
        Ok(())
    }

    #[test]
    fn missing_kind_binding_preserves_rel() {
        let reducer = Reducer::new();
        let found = reducer.find_kind(&[], 0, 0, 0, dummy());
        assert!(matches!(found.node, Kind::Rel(0)));
    }

    #[test]
    fn missing_constructor_binding_preserves_rel() {
        let reducer = Reducer::new();
        let found = reducer.find_con(&[], 0, 0, 0, 0, 0, dummy());
        assert!(matches!(found.node, Constructor::Rel(0)));
    }

    #[test]
    fn missing_expression_binding_preserves_rel() {
        let reducer = Reducer::new();
        let found = reducer.find_exp(&[], 0, 0, 0, 0, 0, 0, dummy());
        assert!(matches!(found.node, Expression::Rel(0)));
    }

    #[test]
    fn record_field_projection_reduces() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Catches mutant: Field of Record is not statically projected.
        // { x = Prim(1) }.x  →  Prim(1)
        let span = dummy();
        let field_name = Located::new(Constructor::Name("x".into()), span.clone());
        let field_t = unit_con();
        let rec = Located::new(
            Expression::Record(vec![(field_name.clone(), prim_exp(), field_t.clone())]),
            span.clone(),
        );
        let fm = FieldMeta {
            field: field_t,
            rest: Located::new(
                Constructor::Record(Box::new(Located::new(Kind::Type, span.clone())), vec![]),
                span.clone(),
            ),
        };
        let projection = Located::new(
            Expression::Field(Box::new(rec), field_name, fm),
            span.clone(),
        );
        let reducer = Reducer::new();
        let result = reducer.reduce_exp(&[], projection);
        assert!(
            matches!(result.node, Expression::Prim(_)),
            "Field of known Record must project"
        );
        Ok(()) // return success to the test harness
    }

    // --- Plan: Catch Missed Mutants - global_reduction ---

    #[test]
    fn reduce_exp_case_var_matches() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Kills: delete Var arm in match_pat. Case(_, [(Var, body)]) -> body.
        use crate::core::Pattern;
        let var_pat = Located::new(Pattern::Var("x".into(), unit_con()), dummy());
        let disc = Located::new(Expression::Prim(Prim::Int(0)), dummy());
        let body = Located::new(Expression::Prim(Prim::Int(77)), dummy());
        let case_meta = crate::core::CaseMeta {
            disc: unit_con(),
            result: unit_con(),
        };
        let case = Located::new(
            Expression::Case(Box::new(disc), vec![(var_pat, body)], case_meta),
            dummy(),
        );
        let reducer = Reducer::new();
        let result = reducer.reduce_exp(&[], case);
        assert!(
            matches!(result.node, Expression::Prim(Prim::Int(77))),
            "Var pattern must match and return body"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn reduce_exp_case_prim_equal_matches() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Kills: delete Prim arm, == -> != in match_pat.
        use crate::core::Pattern;
        let prim_pat = Located::new(Pattern::Prim(Prim::Int(1)), dummy());
        let disc = Located::new(Expression::Prim(Prim::Int(1)), dummy());
        let body = Located::new(Expression::Prim(Prim::Int(88)), dummy());
        let case_meta = crate::core::CaseMeta {
            disc: unit_con(),
            result: unit_con(),
        };
        let case = Located::new(
            Expression::Case(Box::new(disc), vec![(prim_pat, body)], case_meta),
            dummy(),
        );
        let reducer = Reducer::new();
        let result = reducer.reduce_exp(&[], case);
        assert!(
            matches!(result.node, Expression::Prim(Prim::Int(88))),
            "Prim(1) pattern must match Prim(1) disc"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn reduce_exp_case_prim_not_equal_no_match() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Kills: == -> !=. Prim(1) vs Prim(2) -> Case remains.
        use crate::core::Pattern;
        let prim_pat = Located::new(Pattern::Prim(Prim::Int(2)), dummy());
        let disc = Located::new(Expression::Prim(Prim::Int(1)), dummy());
        let body = Located::new(Expression::Prim(Prim::Int(88)), dummy());
        let case_meta = crate::core::CaseMeta {
            disc: unit_con(),
            result: unit_con(),
        };
        let case = Located::new(
            Expression::Case(Box::new(disc), vec![(prim_pat, body)], case_meta),
            dummy(),
        );
        let reducer = Reducer::new();
        let result = reducer.reduce_exp(&[], case);
        assert!(
            matches!(result.node, Expression::Case(_, _, _)),
            "Prim(2) must not match Prim(1)"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn reduce_exp_record_concat() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Kills: delete Record arm in Concat. Record + Record -> merged Record.
        let span = dummy();
        let field_name = Located::new(Constructor::Name("x".into()), span);
        let unit_ty = unit_con();
        let rec1 = Located::new(
            Expression::Record(vec![(
                field_name.clone(),
                Located::new(Expression::Prim(Prim::Int(1)), dummy()),
                unit_ty.clone(),
            )]),
            dummy(),
        );
        let rec2 = Located::new(
            Expression::Record(vec![(
                Located::new(Constructor::Name("y".into()), dummy()),
                Located::new(Expression::Prim(Prim::Int(2)), dummy()),
                unit_ty.clone(),
            )]),
            dummy(),
        );
        let concat_t = Located::new(
            Constructor::Concat(Box::new(unit_ty.clone()), Box::new(unit_ty)),
            dummy(),
        );
        let concat = Located::new(
            Expression::Concat(Box::new(rec1), concat_t.clone(), Box::new(rec2), concat_t),
            dummy(),
        );
        let reducer = Reducer::new();
        let result = reducer.reduce_exp(&[], concat);
        assert!(
            matches!(result.node, Expression::Record(_)),
            "Record + Record must reduce to merged Record"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn reduce_con_map_applies_mapper_to_each_field_value() -> anyhow::Result<()> {
        let type_k = Located::dummy(crate::core::Kind::Type);
        let tuple_k = Located::dummy(crate::core::Kind::Tuple(vec![
            type_k.clone(),
            type_k.clone(),
        ]));
        let row_k = Located::dummy(crate::core::Kind::Record(Box::new(tuple_k.clone())));

        let mapper = Located::dummy(Constructor::Abs(
            "t".into(),
            Box::new(tuple_k),
            Box::new(Located::dummy(Constructor::Proj(
                Box::new(Located::dummy(Constructor::Rel(0))),
                1,
            ))),
        ));

        let field_value = Located::dummy(Constructor::Tuple(vec![
            Located::dummy(Constructor::Ffi("Basis".into(), "string".into())),
            Located::dummy(Constructor::Ffi("Basis".into(), "int".into())),
        ]));

        let row = Located::dummy(Constructor::Record(
            Box::new(row_k.clone()),
            vec![(Located::dummy(Constructor::Name("A".into())), field_value)],
        ));

        let app = Located::dummy(Constructor::App(
            Box::new(Located::dummy(Constructor::App(
                Box::new(Located::dummy(Constructor::Map(
                    Box::new(row_k),
                    Box::new(type_k),
                ))),
                Box::new(mapper),
            ))),
            Box::new(row),
        ));

        let out = Reducer::new().reduce_con(&[], app);
        let Constructor::Record(_, fields) = out.node else {
            anyhow::bail!("expected Record, got {:?}", out)
        };
        assert_eq!(fields.len(), 1);
        assert!(
            matches!(
                fields[0].1.node,
                Constructor::Ffi(ref module, ref name) if module == "Basis" && name == "string"
            ),
            "expected mapper result to reduce to the tuple's first component, got {:?}",
            fields[0].1.node
        );
        Ok(())
    }

    #[test]
    fn concat_projection_preserves_sml_rest_row_order() -> anyhow::Result<()> {
        let span = dummy();
        let left_row = record_row(&["A", "B"]);
        let right_row = record_row(&["C"]);
        let left = Located::new(Expression::Rel(1), span.clone());
        let right = Located::new(Expression::Rel(0), span.clone());
        let left_ty = Located::new(
            Constructor::Record(Box::new(Located::new(Kind::Type, span.clone())), left_row),
            span.clone(),
        );
        let right_ty = Located::new(
            Constructor::Record(Box::new(Located::new(Kind::Type, span.clone())), right_row),
            span.clone(),
        );
        let concat = Located::new(
            Expression::Concat(Box::new(left), left_ty, Box::new(right), right_ty),
            span,
        );

        let reducer = Reducer::new();
        let result = reducer.reduce_exp(&[], concat);
        let Expression::Record(fields) = &result.node else {
            anyhow::bail!("concat projection should reduce to a record");
        };
        assert_eq!(fields.len(), 3, "concat should expose all fields");

        let Expression::Field(_, _, meta_a) = &fields[0].1.node else {
            anyhow::bail!("first field should remain a projection");
        };
        let Expression::Field(_, _, meta_b) = &fields[1].1.node else {
            anyhow::bail!("second field should remain a projection");
        };
        let Expression::Field(_, _, meta_c) = &fields[2].1.node else {
            anyhow::bail!("third field should remain a projection");
        };

        assert_eq!(rest_row_names(meta_a), Some(vec![]));
        assert_eq!(rest_row_names(meta_b), Some(vec!["A".into()]));
        assert_eq!(rest_row_names(meta_c), Some(vec!["B".into(), "A".into()]));
        Ok(())
    }

    #[test]
    fn named_inlined_when_use_count_one() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // Kills: may_inline, count_uses. val f=prim, val g=Named(f), export g -> g inlined.
        let file = vec![
            val_decl(1, prim_exp()),
            val_decl(2, Located::new(Expression::Named(1), dummy())),
            export_decl(2),
        ];
        let result = reduce(file, &Settings::default());
        let g = result
            .iter()
            .find_map(|d| match &d.node {
                Declaration::Val(_, 2, _, e, _) => Some(e),
                _ => None,
            })
            .with_context(|| "val 2 must exist")?;
        assert!(
            matches!(g.node, Expression::Prim(_)),
            "Named(1) must be inlined when use_count=1"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn forward_named_chain_inlined_across_later_bindings() -> anyhow::Result<()> {
        let file = vec![
            val_decl(1, Located::new(Expression::Named(2), dummy())),
            val_decl(2, Located::new(Expression::Named(3), dummy())),
            val_decl(3, prim_exp()),
            export_decl(1),
        ];
        let result = reduce(file, &Settings::default());
        let body = result
            .iter()
            .find_map(|d| match &d.node {
                Declaration::Val(_, 1, _, e, _) => Some(e),
                _ => None,
            })
            .with_context(|| "val 1 must exist")?;
        assert!(
            matches!(body.node, Expression::Prim(_)),
            "forward Named chains should inline after seeding a second pass"
        );
        Ok(())
    }

    #[test]
    fn forward_constructor_alias_reduced_in_later_pass() -> anyhow::Result<()> {
        let kind = Located::new(Kind::Type, dummy());
        let alias_decl = Located::new(
            Declaration::Constructor(
                "alias1".into(),
                1,
                kind.clone(),
                Located::new(Constructor::Named(2), dummy()),
            ),
            dummy(),
        );
        let target_decl = Located::new(
            Declaration::Constructor("alias2".into(), 2, kind, unit_con()),
            dummy(),
        );
        let val = Located::new(
            Declaration::Val(
                "x".into(),
                3,
                Located::new(Constructor::Named(1), dummy()),
                prim_exp(),
                "x".into(),
            ),
            dummy(),
        );
        let result = reduce(
            vec![alias_decl, target_decl, val, export_decl(3)],
            &Settings::default(),
        );
        let typ = result
            .iter()
            .find_map(|d| match &d.node {
                Declaration::Val(_, 3, t, _, _) => Some(t),
                _ => None,
            })
            .with_context(|| "val 3 must exist")?;
        assert!(
            matches!(typ.node, Constructor::Unit),
            "forward constructor aliases should resolve before final output"
        );
        Ok(())
    }

    // --- More tests to kill missed mutants ---

    #[test]
    fn passive_prim() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let e = Located::new(Expression::Prim(Prim::Int(0)), dummy());
        assert!(passive(&e.node), "Prim is passive");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn passive_rel() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let e = Located::new(Expression::Rel(0), dummy());
        assert!(passive(&e.node), "Rel is passive");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn passive_named() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let e = Located::new(Expression::Named(1), dummy());
        assert!(passive(&e.node), "Named is passive");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn passive_constructor_none() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        use crate::datatype_kind::DatatypeKind;
        let con = Located::new(
            Expression::Constructor(
                DatatypeKind::Enum,
                crate::core::PatternConstructor::Var(0),
                vec![],
                None,
            ),
            dummy(),
        );
        assert!(passive(&con.node), "Constructor(_,_,_,None) is passive");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn passive_constructor_some_inner_passive() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        use crate::datatype_kind::DatatypeKind;
        let inner = Located::new(Expression::Prim(Prim::Int(0)), dummy());
        let con = Located::new(
            Expression::Constructor(
                DatatypeKind::Enum,
                crate::core::PatternConstructor::Var(0),
                vec![],
                Some(Box::new(inner)),
            ),
            dummy(),
        );
        assert!(
            passive(&con.node),
            "Constructor with passive inner is passive"
        );
        Ok(()) // return success to the test harness
    }

    #[test]
    fn passive_app_not_passive() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let app = Located::new(
            Expression::App(Box::new(prim_exp()), Box::new(prim_exp())),
            dummy(),
        );
        assert!(!passive(&app.node), "App is not passive");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn not_ffi_unit() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = unit_con();
        assert!(not_ffi(&t.node), "Unit is not Ffi");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn not_ffi_false_for_ffi() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = Located::new(Constructor::Ffi("Basis".into(), "int".into()), dummy());
        assert!(!not_ffi(&t.node), "Ffi is ffi");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn pat_binds_n_var() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        use crate::core::Pattern;
        let p = Located::new(Pattern::Var("x".into(), unit_con()), dummy());
        assert_eq!(pat_binds_n(&p), 1);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn pat_binds_n_prim() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        use crate::core::Pattern;
        let p = Located::new(Pattern::Prim(Prim::Int(0)), dummy());
        assert_eq!(pat_binds_n(&p), 0);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn pat_binds_n_record() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        use crate::core::Pattern;
        let field_pat = Located::new(Pattern::Var("x".into(), unit_con()), dummy());
        let p = Located::new(
            Pattern::Record(vec![("x".into(), field_pat, unit_con())]),
            dummy(),
        );
        assert_eq!(pat_binds_n(&p), 1);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn count_exp_prim() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let e = prim_exp();
        assert_eq!(count_exp(&e), 1);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn count_exp_app() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let app = Located::new(
            Expression::App(Box::new(prim_exp()), Box::new(prim_exp())),
            dummy(),
        );
        assert_eq!(count_exp(&app), 3);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn count_named_uses_single() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let file = vec![
            val_decl(1, prim_exp()),
            val_decl(2, Located::new(Expression::Named(1), dummy())),
        ];
        let uses = count_named_uses(&file);
        assert_eq!(uses.get(&1), Some(&1));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_poly_con_named_in_set() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut poly = BTreeSet::new();
        poly.insert(5);
        let con = Located::new(Constructor::Named(5), dummy());
        assert!(is_poly_con(&poly, &con));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_poly_con_named_not_in_set() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let poly: BTreeSet<usize> = BTreeSet::new();
        let con = Located::new(Constructor::Named(5), dummy());
        assert!(!is_poly_con(&poly, &con));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_policy_sql_policy() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = Located::new(
            Constructor::Ffi("Basis".into(), "sql_policy".into()),
            dummy(),
        );
        assert!(is_policy(&t.node));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_policy_not_basis_int() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let t = Located::new(Constructor::Ffi("Basis".into(), "int".into()), dummy());
        assert!(!is_policy(&t.node));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn prim_eq_int_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(prim_eq(&Prim::Int(42), &Prim::Int(42)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn prim_eq_int_diff() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(!prim_eq(&Prim::Int(1), &Prim::Int(2)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn prim_eq_float_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(prim_eq(&Prim::Float(1.0), &Prim::Float(1.0)));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn prim_eq_string_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        use crate::primitives::StringMode;
        assert!(prim_eq(
            &Prim::String(StringMode::Normal, "a".into()),
            &Prim::String(StringMode::Normal, "a".into())
        ));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn prim_eq_string_diff() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        use crate::primitives::StringMode;
        assert!(!prim_eq(
            &Prim::String(StringMode::Normal, "a".into()),
            &Prim::String(StringMode::Normal, "b".into())
        ));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn prim_eq_char_same() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(prim_eq(&Prim::Char('x'), &Prim::Char('x')));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn prim_eq_char_diff() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        assert!(!prim_eq(&Prim::Char('a'), &Prim::Char('b')));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn passive_record_of_prim() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let field_name = Located::new(Constructor::Name("x".into()), dummy());
        let rec = Located::new(
            Expression::Record(vec![(field_name, prim_exp(), unit_con())]),
            dummy(),
        );
        assert!(passive(&rec.node));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn passive_field_of_prim() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let inner = prim_exp();
        let fm = FieldMeta {
            field: unit_con(),
            rest: Located::new(
                Constructor::Record(Box::new(Located::new(Kind::Type, dummy())), vec![]),
                dummy(),
            ),
        };
        let field = Located::new(
            Expression::Field(
                Box::new(inner),
                Located::new(Constructor::Name("x".into()), dummy()),
                fm,
            ),
            dummy(),
        );
        assert!(passive(&field.node));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn count_exp_prim_is_one() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let e = prim_exp();
        assert_eq!(count_exp(&e), 1);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn count_exp_app_counts_both() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let span = dummy();
        let app = Located::new(
            Expression::App(Box::new(prim_exp()), Box::new(prim_exp())),
            span,
        );
        assert_eq!(count_exp(&app), 3);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn count_named_uses_sees_named_refs() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let file = vec![
            val_decl(1, prim_exp()),
            val_decl(2, Located::new(Expression::Named(1), dummy())),
            val_decl(3, Located::new(Expression::Named(1), dummy())),
        ];
        let uses = count_named_uses(&file);
        assert_eq!(uses.get(&1), Some(&2));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_poly_con_ffi_false() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = Located::new(Constructor::Ffi("Basis".into(), "int".into()), dummy());
        let empty: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
        assert!(!is_poly_con(&empty, &c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_policy_basis_sql_policy() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = Constructor::Ffi("Basis".into(), "sql_policy".into());
        assert!(is_policy(&c));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn is_policy_basis_int_false() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let c = Constructor::Ffi("Basis".into(), "int".into());
        assert!(!is_policy(&c));
        Ok(()) // return success to the test harness
    }
}
