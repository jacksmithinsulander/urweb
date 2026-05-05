//! Utility traversals over the Expl AST.
//!
//! Ports `expl_util.sml`.

use crate::datatype_kind::DatatypeKind;
use crate::explicit::{
    CaseMeta, Constructor, Declaration, Expression, FieldMeta, Kind, LocatedConstructor,
    LocatedDeclaration, LocatedExpression, LocatedKind, RestMeta,
};

// ---------------------------------------------------------------------------
// classify_datatype
//
// Mirrors `ElabUtil.classifyDatatype` / `MonoUtil.classifyDatatype`.
// Given the constructor list `(name, id, payload_type option)` for a
// datatype, decides its runtime representation.
// ---------------------------------------------------------------------------

/// Decide the `DatatypeKind` for a datatype from its constructor list.
///
/// Rules (same as in the SML `classifyDatatype`):
///   - All nullary  → `Enum`
///   - Exactly one nullary + one unary  → `Option`
///   - Anything else  → `Default`
pub fn classify_datatype(
    constructor_specs: &[(String, usize, Option<LocatedConstructor>)],
) -> DatatypeKind {
    let nullary = constructor_specs
        .iter()
        .filter(|(_, _, arg_type)| arg_type.is_none())
        .count();
    let unary = constructor_specs
        .iter()
        .filter(|(_, _, arg_type)| arg_type.is_some())
        .count();
    if unary == 0 {
        DatatypeKind::Enum
    } else if nullary == 1 && unary == 1 {
        DatatypeKind::Option
    } else {
        DatatypeKind::Default
    }
}

// ---------------------------------------------------------------------------
// pub mod kind
// ---------------------------------------------------------------------------

pub mod kind {
    use super::*;

    // -----------------------------------------------------------------------
    // map — transform every sub-kind, bottom-up
    // -----------------------------------------------------------------------

    pub fn map<F>(kind: LocatedKind, visitor: &F) -> LocatedKind
    where
        F: Fn(Kind) -> Kind,
    {
        let span = kind.span.clone();
        let inner = map_node(kind.node, visitor);
        let transformed = visitor(inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_node<F>(kind_node: Kind, visitor: &F) -> Kind
    where
        F: Fn(Kind) -> Kind,
    {
        match kind_node {
            Kind::Arrow(left, right) => Kind::Arrow(
                Box::new(map(*left, visitor)),
                Box::new(map(*right, visitor)),
            ),
            Kind::Tuple(kinds) => Kind::Tuple(
                kinds
                    .into_iter()
                    .map(|kind_item| map(kind_item, visitor))
                    .collect(),
            ),
            Kind::Record(inner) => Kind::Record(Box::new(map(*inner, visitor))),
            Kind::Fun(param_name, body) => Kind::Fun(param_name, Box::new(map(*body, visitor))),
            other_variant => other_variant,
        }
    }

    // -----------------------------------------------------------------------
    // exists — check if any sub-kind satisfies a predicate
    // -----------------------------------------------------------------------

    pub fn exists<F>(kind: &LocatedKind, predicate: &F) -> bool
    where
        F: Fn(&Kind) -> bool,
    {
        if predicate(&kind.node) {
            return true;
        }
        match &kind.node {
            Kind::Arrow(left, right) => exists(left, predicate) || exists(right, predicate),
            Kind::Tuple(kinds) => kinds.iter().any(|kind_item| exists(kind_item, predicate)),
            Kind::Record(inner) => exists(inner, predicate),
            Kind::Fun(_, body) => exists(body, predicate),
            _ => false,
        }
    }

    // -----------------------------------------------------------------------
    // fold — accumulate state over every sub-kind, top-down
    // -----------------------------------------------------------------------

    pub fn fold<S, F>(kind: &LocatedKind, init: S, folder: &F) -> S
    where
        F: Fn(&Kind, S) -> S,
    {
        let accumulator = folder(&kind.node, init);
        match &kind.node {
            Kind::Arrow(left, right) => {
                let accumulator = fold(left, accumulator, folder);
                fold(right, accumulator, folder)
            }
            Kind::Tuple(kinds) => kinds
                .iter()
                .fold(accumulator, |acc, kind_item| fold(kind_item, acc, folder)),
            Kind::Record(inner) => fold(inner, accumulator, folder),
            Kind::Fun(_, body) => fold(body, accumulator, folder),
            _ => accumulator,
        }
    }
}

// ---------------------------------------------------------------------------
// pub mod con
// ---------------------------------------------------------------------------

pub mod con {
    use super::*;

    /// Binder context items for constructor traversal.
    #[derive(Debug, Clone)]
    pub enum Binder {
        /// Pushed when we descend under a kind binder.
        RelK(String),
        /// Pushed when we descend under a con binder.
        RelC(String, LocatedKind),
        /// Named constructor binding.
        NamedC(String, LocatedKind),
    }

    // -----------------------------------------------------------------------
    // map — transform every sub-con and sub-kind, bottom-up
    // -----------------------------------------------------------------------

    pub fn map<FK, FC>(
        constructor: LocatedConstructor,
        kind_mapper: &FK,
        constructor_mapper: &FC,
    ) -> LocatedConstructor
    where
        FK: Fn(Kind) -> Kind,
        FC: Fn(Constructor) -> Constructor,
    {
        map_b(
            constructor,
            &mut (),
            &|_, kind| kind_mapper(kind),
            &|_, constructor_node| constructor_mapper(constructor_node),
            &|_, _| {},
        )
    }

    // -----------------------------------------------------------------------
    // map_b — transform with a mutable binder context
    // -----------------------------------------------------------------------

    pub fn map_b<Ctx, FK, FC, FB>(
        constructor: LocatedConstructor,
        context: &mut Ctx,
        kind_mapper: &FK,
        constructor_mapper: &FC,
        bind_callback: &FB,
    ) -> LocatedConstructor
    where
        FK: Fn(&mut Ctx, Kind) -> Kind,
        FC: Fn(&mut Ctx, Constructor) -> Constructor,
        FB: Fn(&mut Ctx, &Binder),
        Ctx: Clone,
    {
        let span = constructor.span.clone();
        let inner = map_b_node(
            constructor.node,
            context,
            kind_mapper,
            constructor_mapper,
            bind_callback,
        );
        let transformed = constructor_mapper(context, inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_kind<Ctx, FK>(kind: LocatedKind, context: &mut Ctx, kind_mapper: &FK) -> LocatedKind
    where
        FK: Fn(&mut Ctx, Kind) -> Kind,
    {
        let span = kind.span.clone();
        let inner = match kind.node {
            Kind::Arrow(left, right) => Kind::Arrow(
                Box::new(map_kind(*left, context, kind_mapper)),
                Box::new(map_kind(*right, context, kind_mapper)),
            ),
            Kind::Tuple(kinds) => Kind::Tuple(
                kinds
                    .into_iter()
                    .map(|kind_item| map_kind(kind_item, context, kind_mapper))
                    .collect(),
            ),
            Kind::Record(inner) => Kind::Record(Box::new(map_kind(*inner, context, kind_mapper))),
            Kind::Fun(param_name, body) => {
                Kind::Fun(param_name, Box::new(map_kind(*body, context, kind_mapper)))
            }
            other => other,
        };
        let transformed = kind_mapper(context, inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_b_node<Ctx, FK, FC, FB>(
        constructor_node: Constructor,
        context: &mut Ctx,
        kind_mapper: &FK,
        constructor_mapper: &FC,
        bind_callback: &FB,
    ) -> Constructor
    where
        FK: Fn(&mut Ctx, Kind) -> Kind,
        FC: Fn(&mut Ctx, Constructor) -> Constructor,
        FB: Fn(&mut Ctx, &Binder),
        Ctx: Clone,
    {
        match constructor_node {
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::ModProj(..)
            | Constructor::Name(_)
            | Constructor::Unit => constructor_node,

            Constructor::TFun(left, right) => {
                let left_mapped = map_b(
                    *left,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                let right_mapped = map_b(
                    *right,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::TFun(Box::new(left_mapped), Box::new(right_mapped))
            }

            Constructor::TCFun(param_name, kind, body) => {
                let kind_mapped = map_kind(*kind, context, kind_mapper);
                bind_callback(
                    context,
                    &Binder::RelC(param_name.clone(), kind_mapped.clone()),
                );
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::TCFun(param_name, Box::new(kind_mapped), Box::new(body_mapped))
            }

            Constructor::TRecord(inner) => Constructor::TRecord(Box::new(map_b(
                *inner,
                context,
                kind_mapper,
                constructor_mapper,
                bind_callback,
            ))),

            Constructor::App(left, right) => {
                let left_mapped = map_b(
                    *left,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                let right_mapped = map_b(
                    *right,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::App(Box::new(left_mapped), Box::new(right_mapped))
            }

            Constructor::Abs(param_name, kind, body) => {
                let kind_mapped = map_kind(*kind, context, kind_mapper);
                bind_callback(
                    context,
                    &Binder::RelC(param_name.clone(), kind_mapped.clone()),
                );
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::Abs(param_name, Box::new(kind_mapped), Box::new(body_mapped))
            }

            Constructor::KAbs(param_name, body) => {
                bind_callback(context, &Binder::RelK(param_name.clone()));
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::KAbs(param_name, Box::new(body_mapped))
            }

            Constructor::KApp(constructor_part, kind_part) => {
                let constructor_mapped = map_b(
                    *constructor_part,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                let kind_mapped = map_kind(*kind_part, context, kind_mapper);
                Constructor::KApp(Box::new(constructor_mapped), Box::new(kind_mapped))
            }

            Constructor::TKFun(param_name, body) => {
                bind_callback(context, &Binder::RelK(param_name.clone()));
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::TKFun(param_name, Box::new(body_mapped))
            }

            Constructor::Record(record_kind, key_value_pairs) => {
                let kind_mapped = map_kind(*record_kind, context, kind_mapper);
                let pairs_mapped: Vec<_> = key_value_pairs
                    .into_iter()
                    .map(|(key_con, value_con)| {
                        let key_mapped = map_b(
                            key_con,
                            context,
                            kind_mapper,
                            constructor_mapper,
                            bind_callback,
                        );
                        let value_mapped = map_b(
                            value_con,
                            context,
                            kind_mapper,
                            constructor_mapper,
                            bind_callback,
                        );
                        (key_mapped, value_mapped)
                    })
                    .collect();
                Constructor::Record(Box::new(kind_mapped), pairs_mapped)
            }

            Constructor::Concat(left, right) => {
                let left_mapped = map_b(
                    *left,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                let right_mapped = map_b(
                    *right,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::Concat(Box::new(left_mapped), Box::new(right_mapped))
            }

            Constructor::Map(domain_kind, range_kind) => {
                let domain_mapped = map_kind(*domain_kind, context, kind_mapper);
                let range_mapped = map_kind(*range_kind, context, kind_mapper);
                Constructor::Map(Box::new(domain_mapped), Box::new(range_mapped))
            }

            Constructor::Tuple(constructors) => {
                let constructors_mapped: Vec<_> = constructors
                    .into_iter()
                    .map(|constructor_item| {
                        map_b(
                            constructor_item,
                            context,
                            kind_mapper,
                            constructor_mapper,
                            bind_callback,
                        )
                    })
                    .collect();
                Constructor::Tuple(constructors_mapped)
            }

            Constructor::Proj(inner, projection_index) => {
                let inner_mapped = map_b(
                    *inner,
                    context,
                    kind_mapper,
                    constructor_mapper,
                    bind_callback,
                );
                Constructor::Proj(Box::new(inner_mapped), projection_index)
            }

            // Map each arm's argument constructors; tag names are not constructors and pass through.
            Constructor::Enum(arms) => {
                let mapped_arms = arms
                    .into_iter()
                    .map(|(tag_name, arg_constructors)| {
                        // Map every argument constructor in this arm.
                        let mapped_args = arg_constructors
                            .into_iter()
                            .map(|arg_constructor| {
                                map_b(
                                    arg_constructor,
                                    context,
                                    kind_mapper,
                                    constructor_mapper,
                                    bind_callback,
                                )
                            })
                            .collect();
                        (tag_name, mapped_args)
                    })
                    .collect();
                Constructor::Enum(mapped_arms)
            }
        }
    }

    // -----------------------------------------------------------------------
    // exists — short-circuit traversal
    // -----------------------------------------------------------------------

    pub fn exists<FK, FC>(
        constructor: &LocatedConstructor,
        kind_predicate: &FK,
        constructor_predicate: &FC,
    ) -> bool
    where
        FK: Fn(&Kind) -> bool,
        FC: Fn(&Constructor) -> bool,
    {
        if constructor_predicate(&constructor.node) {
            return true;
        }
        match &constructor.node {
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::ModProj(..)
            | Constructor::Name(_)
            | Constructor::Unit => false,

            Constructor::TFun(left, right) => {
                exists(left, kind_predicate, constructor_predicate)
                    || exists(right, kind_predicate, constructor_predicate)
            }

            Constructor::TCFun(_, kind, body) => {
                kind::exists(kind, kind_predicate)
                    || exists(body, kind_predicate, constructor_predicate)
            }

            Constructor::TRecord(inner) => exists(inner, kind_predicate, constructor_predicate),

            Constructor::App(left, right) => {
                exists(left, kind_predicate, constructor_predicate)
                    || exists(right, kind_predicate, constructor_predicate)
            }

            Constructor::Abs(_, kind, body) => {
                kind::exists(kind, kind_predicate)
                    || exists(body, kind_predicate, constructor_predicate)
            }

            Constructor::KAbs(_, body) => exists(body, kind_predicate, constructor_predicate),

            Constructor::KApp(constructor_part, kind_part) => {
                exists(constructor_part, kind_predicate, constructor_predicate)
                    || kind::exists(kind_part, kind_predicate)
            }

            Constructor::TKFun(_, body) => exists(body, kind_predicate, constructor_predicate),

            Constructor::Record(record_kind, key_value_pairs) => {
                kind::exists(record_kind, kind_predicate)
                    || key_value_pairs.iter().any(|(key_con, value_con)| {
                        exists(key_con, kind_predicate, constructor_predicate)
                            || exists(value_con, kind_predicate, constructor_predicate)
                    })
            }

            Constructor::Concat(left, right) => {
                exists(left, kind_predicate, constructor_predicate)
                    || exists(right, kind_predicate, constructor_predicate)
            }

            Constructor::Map(domain_kind, range_kind) => {
                kind::exists(domain_kind, kind_predicate)
                    || kind::exists(range_kind, kind_predicate)
            }

            Constructor::Tuple(constructors) => constructors.iter().any(|constructor_item| {
                exists(constructor_item, kind_predicate, constructor_predicate)
            }),

            Constructor::Proj(inner, _) => exists(inner, kind_predicate, constructor_predicate),

            // Check predicate against every argument constructor in every arm.
            Constructor::Enum(arms) => arms.iter().any(|(_, arg_constructors)| {
                arg_constructors.iter().any(|arg_constructor| {
                    exists(arg_constructor, kind_predicate, constructor_predicate)
                })
            }),
        }
    }

    // -----------------------------------------------------------------------
    // fold — accumulate state
    // -----------------------------------------------------------------------

    pub fn fold<S, FK, FC>(
        constructor: &LocatedConstructor,
        init: S,
        fold_kind: &FK,
        fold_con: &FC,
    ) -> S
    where
        FK: Fn(&Kind, S) -> S,
        FC: Fn(&Constructor, S) -> S,
    {
        let accumulator = fold_con(&constructor.node, init);
        match &constructor.node {
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::ModProj(..)
            | Constructor::Name(_)
            | Constructor::Unit => accumulator,

            Constructor::TFun(left, right) => {
                let accumulator = fold(left, accumulator, fold_kind, fold_con);
                fold(right, accumulator, fold_kind, fold_con)
            }

            Constructor::TCFun(_, kind, body) => {
                let accumulator = kind::fold(kind, accumulator, fold_kind);
                fold(body, accumulator, fold_kind, fold_con)
            }

            Constructor::TRecord(inner) => fold(inner, accumulator, fold_kind, fold_con),

            Constructor::App(left, right) => {
                let accumulator = fold(left, accumulator, fold_kind, fold_con);
                fold(right, accumulator, fold_kind, fold_con)
            }

            Constructor::Abs(_, kind, body) => {
                let accumulator = kind::fold(kind, accumulator, fold_kind);
                fold(body, accumulator, fold_kind, fold_con)
            }

            Constructor::KAbs(_, body) => fold(body, accumulator, fold_kind, fold_con),

            Constructor::KApp(constructor_part, kind_part) => {
                let accumulator = fold(constructor_part, accumulator, fold_kind, fold_con);
                kind::fold(kind_part, accumulator, fold_kind)
            }

            Constructor::TKFun(_, body) => fold(body, accumulator, fold_kind, fold_con),

            Constructor::Record(record_kind, key_value_pairs) => {
                let accumulator = kind::fold(record_kind, accumulator, fold_kind);
                key_value_pairs
                    .iter()
                    .fold(accumulator, |acc, (key_con, value_con)| {
                        let acc = fold(key_con, acc, fold_kind, fold_con);
                        fold(value_con, acc, fold_kind, fold_con)
                    })
            }

            Constructor::Concat(left, right) => {
                let accumulator = fold(left, accumulator, fold_kind, fold_con);
                fold(right, accumulator, fold_kind, fold_con)
            }

            Constructor::Map(domain_kind, range_kind) => {
                let accumulator = kind::fold(domain_kind, accumulator, fold_kind);
                kind::fold(range_kind, accumulator, fold_kind)
            }

            Constructor::Tuple(constructors) => constructors
                .iter()
                .fold(accumulator, |acc, constructor_item| {
                    fold(constructor_item, acc, fold_kind, fold_con)
                }),

            Constructor::Proj(inner, _) => fold(inner, accumulator, fold_kind, fold_con),

            // Fold over every argument constructor in every arm; tag names are not constructors.
            Constructor::Enum(arms) => {
                arms.iter().fold(accumulator, |acc, (_, arg_constructors)| {
                    arg_constructors
                        .iter()
                        .fold(acc, |inner_acc, arg_constructor| {
                            fold(arg_constructor, inner_acc, fold_kind, fold_con)
                        })
                })
            }
        }
    }
}

// ---------------------------------------------------------------------------
// pub mod exp
// ---------------------------------------------------------------------------

pub mod exp {
    use super::*;

    /// Binder context items for expression traversal.
    #[derive(Debug, Clone)]
    pub enum Binder {
        RelK(String),
        RelC(String, LocatedKind),
        NamedC(String, LocatedKind),
        RelE(String, LocatedConstructor),
        NamedE(String, LocatedConstructor),
    }

    // -----------------------------------------------------------------------
    // map — transform every sub-expression, sub-con, and sub-kind, bottom-up
    // -----------------------------------------------------------------------

    pub fn map<FK, FC, FE>(e: LocatedExpression, fk: &FK, fc: &FC, fe: &FE) -> LocatedExpression
    where
        FK: Fn(Kind) -> Kind,
        FC: Fn(Constructor) -> Constructor,
        FE: Fn(Expression) -> Expression,
    {
        map_b(
            e,
            &mut (),
            &|_, k| fk(k),
            &|_, c| fc(c),
            &|_, e| fe(e),
            &|_, _| {},
        )
    }

    // -----------------------------------------------------------------------
    // map_b — transform with a mutable binder context
    // -----------------------------------------------------------------------

    pub fn map_b<Ctx, FK, FC, FE, FB>(
        e: LocatedExpression,
        ctx: &mut Ctx,
        fk: &FK,
        fc: &FC,
        fe: &FE,
        bind: &FB,
    ) -> LocatedExpression
    where
        FK: Fn(&mut Ctx, Kind) -> Kind,
        FC: Fn(&mut Ctx, Constructor) -> Constructor,
        FE: Fn(&mut Ctx, Expression) -> Expression,
        FB: Fn(&mut Ctx, &Binder),
        Ctx: Clone,
    {
        let span = e.span.clone();
        let inner = map_b_node(e.node, ctx, fk, fc, fe, bind);
        let transformed = fe(ctx, inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_kind_ctx<Ctx, FK>(k: LocatedKind, ctx: &mut Ctx, fk: &FK) -> LocatedKind
    where
        FK: Fn(&mut Ctx, Kind) -> Kind,
    {
        let span = k.span.clone();
        let inner = match k.node {
            Kind::Arrow(k1, k2) => Kind::Arrow(
                Box::new(map_kind_ctx(*k1, ctx, fk)),
                Box::new(map_kind_ctx(*k2, ctx, fk)),
            ),
            Kind::Tuple(ks) => {
                Kind::Tuple(ks.into_iter().map(|k| map_kind_ctx(k, ctx, fk)).collect())
            }
            Kind::Record(k) => Kind::Record(Box::new(map_kind_ctx(*k, ctx, fk))),
            Kind::Fun(x, k) => Kind::Fun(x, Box::new(map_kind_ctx(*k, ctx, fk))),
            other => other,
        };
        let transformed = fk(ctx, inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn map_b_node<Ctx, FK, FC, FE, FB>(
        e: Expression,
        ctx: &mut Ctx,
        fk: &FK,
        fc: &FC,
        fe: &FE,
        bind: &FB,
    ) -> Expression
    where
        FK: Fn(&mut Ctx, Kind) -> Kind,
        FC: Fn(&mut Ctx, Constructor) -> Constructor,
        FE: Fn(&mut Ctx, Expression) -> Expression,
        FB: Fn(&mut Ctx, &Binder),
        Ctx: Clone,
    {
        // Helper: map a LocatedConstructor threading ctx through without new binder pushes.
        let mfc = |c: LocatedConstructor, ctx: &mut Ctx| -> LocatedConstructor {
            con::map_b(c, ctx, fk, fc, &|_, _| {})
        };
        let mfk = |k: LocatedKind, ctx: &mut Ctx| -> LocatedKind { map_kind_ctx(k, ctx, fk) };
        let mfe = |e: LocatedExpression, ctx: &mut Ctx| -> LocatedExpression {
            map_b(e, ctx, fk, fc, fe, bind)
        };

        match e {
            Expression::Prim(_)
            | Expression::Rel(_)
            | Expression::Named(_)
            | Expression::ModProj(..) => e,

            Expression::App(e1, e2) => {
                let e1b = mfe(*e1, ctx);
                let e2b = mfe(*e2, ctx);
                Expression::App(Box::new(e1b), Box::new(e2b))
            }

            Expression::Abs(x, dom, ran, body) => {
                let dom2 = mfc(dom.clone(), ctx);
                let ran2 = mfc(ran, ctx);
                bind(ctx, &Binder::RelE(x.clone(), dom2.clone()));
                let body2 = mfe(*body, ctx);
                Expression::Abs(x, dom2, ran2, Box::new(body2))
            }

            Expression::CApp(e, c) => {
                let eb = mfe(*e, ctx);
                let cb = mfc(c, ctx);
                Expression::CApp(Box::new(eb), cb)
            }

            Expression::CAbs(x, k, body) => {
                let k2 = mfk(*k, ctx);
                bind(ctx, &Binder::RelC(x.clone(), k2.clone()));
                let body2 = mfe(*body, ctx);
                Expression::CAbs(x, Box::new(k2), Box::new(body2))
            }

            Expression::KAbs(x, body) => {
                bind(ctx, &Binder::RelK(x.clone()));
                let body2 = mfe(*body, ctx);
                Expression::KAbs(x, Box::new(body2))
            }

            Expression::KApp(e, k) => {
                let eb = mfe(*e, ctx);
                let k2 = mfk(*k, ctx);
                Expression::KApp(Box::new(eb), Box::new(k2))
            }

            Expression::Record(xets) => {
                let xets2 = xets
                    .into_iter()
                    .map(|(x, e, t)| {
                        let x2 = mfc(x, ctx);
                        let e2 = mfe(e, ctx);
                        let t2 = mfc(t, ctx);
                        (x2, e2, t2)
                    })
                    .collect();
                Expression::Record(xets2)
            }

            Expression::Field(e, c, FieldMeta { field, rest }) => {
                let eb = mfe(*e, ctx);
                let cb = mfc(c, ctx);
                let field2 = mfc(field, ctx);
                let rest2 = mfc(rest, ctx);
                Expression::Field(
                    Box::new(eb),
                    cb,
                    FieldMeta {
                        field: field2,
                        rest: rest2,
                    },
                )
            }

            Expression::Concat(e1, c1, e2, c2) => {
                let e1b = mfe(*e1, ctx);
                let c1b = mfc(c1, ctx);
                let e2b = mfe(*e2, ctx);
                let c2b = mfc(c2, ctx);
                Expression::Concat(Box::new(e1b), c1b, Box::new(e2b), c2b)
            }

            Expression::Cut(e, c, FieldMeta { field, rest }) => {
                let eb = mfe(*e, ctx);
                let cb = mfc(c, ctx);
                let field2 = mfc(field, ctx);
                let rest2 = mfc(rest, ctx);
                Expression::Cut(
                    Box::new(eb),
                    cb,
                    FieldMeta {
                        field: field2,
                        rest: rest2,
                    },
                )
            }

            Expression::CutMulti(e, c, RestMeta { rest }) => {
                let eb = mfe(*e, ctx);
                let cb = mfc(c, ctx);
                let rest2 = mfc(rest, ctx);
                Expression::CutMulti(Box::new(eb), cb, RestMeta { rest: rest2 })
            }

            Expression::Case(disc, arms, CaseMeta { disc: dt, result }) => {
                let disc2 = mfe(*disc, ctx);
                let arms2 = arms
                    .into_iter()
                    .map(|(p, e)| {
                        let e2 = mfe(e, ctx);
                        (p, e2)
                    })
                    .collect();
                let dt2 = mfc(dt, ctx);
                let result2 = mfc(result, ctx);
                Expression::Case(
                    Box::new(disc2),
                    arms2,
                    CaseMeta {
                        disc: dt2,
                        result: result2,
                    },
                )
            }

            Expression::Write(e) => {
                let eb = mfe(*e, ctx);
                Expression::Write(Box::new(eb))
            }

            Expression::Let(x, t, e1, e2) => {
                let t2 = mfc(t.clone(), ctx);
                let e1b = mfe(*e1, ctx);
                bind(ctx, &Binder::RelE(x.clone(), t2.clone()));
                let e2b = mfe(*e2, ctx);
                Expression::Let(x, t2, Box::new(e1b), Box::new(e2b))
            }
        }
    }

    // -----------------------------------------------------------------------
    // exists — short-circuit traversal
    // -----------------------------------------------------------------------

    pub fn exists<FK, FC, FE>(e: &LocatedExpression, fk: &FK, fc: &FC, fe: &FE) -> bool
    where
        FK: Fn(&Kind) -> bool,
        FC: Fn(&Constructor) -> bool,
        FE: Fn(&Expression) -> bool,
    {
        if fe(&e.node) {
            return true;
        }

        let ec = |c: &LocatedConstructor| con::exists(c, fk, fc);
        let ek = |k: &LocatedKind| kind::exists(k, fk);
        let ee = |e: &LocatedExpression| exists(e, fk, fc, fe);

        match &e.node {
            Expression::Prim(_)
            | Expression::Rel(_)
            | Expression::Named(_)
            | Expression::ModProj(..) => false,

            Expression::App(e1, e2) => ee(e1) || ee(e2),

            Expression::Abs(_, dom, ran, body) => ec(dom) || ec(ran) || ee(body),

            Expression::CApp(e, c) => ee(e) || ec(c),

            Expression::CAbs(_, k, body) => ek(k) || ee(body),

            Expression::KAbs(_, body) => ee(body),

            Expression::KApp(e, k) => ee(e) || ek(k),

            Expression::Record(xets) => xets.iter().any(|(x, e, t)| ec(x) || ee(e) || ec(t)),

            Expression::Field(e, c, FieldMeta { field, rest }) => {
                ee(e) || ec(c) || ec(field) || ec(rest)
            }

            Expression::Concat(e1, c1, e2, c2) => ee(e1) || ec(c1) || ee(e2) || ec(c2),

            Expression::Cut(e, c, FieldMeta { field, rest }) => {
                ee(e) || ec(c) || ec(field) || ec(rest)
            }

            Expression::CutMulti(e, c, RestMeta { rest }) => ee(e) || ec(c) || ec(rest),

            Expression::Case(disc, arms, CaseMeta { disc: dt, result }) => {
                ee(disc) || arms.iter().any(|(_, e)| ee(e)) || ec(dt) || ec(result)
            }

            Expression::Write(e) => ee(e),

            Expression::Let(_, t, e1, e2) => ec(t) || ee(e1) || ee(e2),
        }
    }

    // -----------------------------------------------------------------------
    // fold — accumulate state
    // -----------------------------------------------------------------------

    pub fn fold<S, FK, FC, FE>(e: &LocatedExpression, init: S, fk: &FK, fc: &FC, fe: &FE) -> S
    where
        FK: Fn(&Kind, S) -> S,
        FC: Fn(&Constructor, S) -> S,
        FE: Fn(&Expression, S) -> S,
    {
        let s = fe(&e.node, init);

        let fc2 = |c: &LocatedConstructor, s: S| con::fold(c, s, fk, fc);
        let fk2 = |k: &LocatedKind, s: S| kind::fold(k, s, fk);
        let fe2 = |e: &LocatedExpression, s: S| fold(e, s, fk, fc, fe);

        match &e.node {
            Expression::Prim(_)
            | Expression::Rel(_)
            | Expression::Named(_)
            | Expression::ModProj(..) => s,

            Expression::App(e1, e2) => {
                let s = fe2(e1, s);
                fe2(e2, s)
            }

            Expression::Abs(_, dom, ran, body) => {
                let s = fc2(dom, s);
                let s = fc2(ran, s);
                fe2(body, s)
            }

            Expression::CApp(e, c) => {
                let s = fe2(e, s);
                fc2(c, s)
            }

            Expression::CAbs(_, k, body) => {
                let s = fk2(k, s);
                fe2(body, s)
            }

            Expression::KAbs(_, body) => fe2(body, s),

            Expression::KApp(e, k) => {
                let s = fe2(e, s);
                fk2(k, s)
            }

            Expression::Record(xets) => xets.iter().fold(s, |s, (x, e, t)| {
                let s = fc2(x, s);
                let s = fe2(e, s);
                fc2(t, s)
            }),

            Expression::Field(e, c, FieldMeta { field, rest }) => {
                let s = fe2(e, s);
                let s = fc2(c, s);
                let s = fc2(field, s);
                fc2(rest, s)
            }

            Expression::Concat(e1, c1, e2, c2) => {
                let s = fe2(e1, s);
                let s = fc2(c1, s);
                let s = fe2(e2, s);
                fc2(c2, s)
            }

            Expression::Cut(e, c, FieldMeta { field, rest }) => {
                let s = fe2(e, s);
                let s = fc2(c, s);
                let s = fc2(field, s);
                fc2(rest, s)
            }

            Expression::CutMulti(e, c, RestMeta { rest }) => {
                let s = fe2(e, s);
                let s = fc2(c, s);
                fc2(rest, s)
            }

            Expression::Case(disc, arms, CaseMeta { disc: dt, result }) => {
                let s = fe2(disc, s);
                let s = arms.iter().fold(s, |s, (_, e)| fe2(e, s));
                let s = fc2(dt, s);
                fc2(result, s)
            }

            Expression::Write(e) => fe2(e, s),

            Expression::Let(_, t, e1, e2) => {
                let s = fc2(t, s);
                let s = fe2(e1, s);
                fe2(e2, s)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// pub mod decl
// ---------------------------------------------------------------------------

pub mod decl {
    use super::*;

    // -----------------------------------------------------------------------
    // map — transform every sub-node in a LocatedDeclaration
    // -----------------------------------------------------------------------

    pub fn map<FK, FC, FE, FD>(
        d: LocatedDeclaration,
        fk: &FK,
        fc: &FC,
        fe: &FE,
        fd: &FD,
    ) -> LocatedDeclaration
    where
        FK: Fn(Kind) -> Kind,
        FC: Fn(Constructor) -> Constructor,
        FE: Fn(Expression) -> Expression,
        FD: Fn(Declaration) -> Declaration,
    {
        let span = d.span.clone();
        let inner = map_node(d.node, fk, fc, fe);
        let transformed = fd(inner);
        crate::error_types::Located::new(transformed, span)
    }

    fn mk<FK, FC>(c: LocatedConstructor, fk: &FK, fc: &FC) -> LocatedConstructor
    where
        FK: Fn(Kind) -> Kind,
        FC: Fn(Constructor) -> Constructor,
    {
        con::map(c, fk, fc)
    }

    fn me<FK, FC, FE>(e: LocatedExpression, fk: &FK, fc: &FC, fe: &FE) -> LocatedExpression
    where
        FK: Fn(Kind) -> Kind,
        FC: Fn(Constructor) -> Constructor,
        FE: Fn(Expression) -> Expression,
    {
        exp::map(e, fk, fc, fe)
    }

    fn map_constrs<FK, FC>(
        constrs: Vec<(String, usize, Option<LocatedConstructor>)>,
        fk: &FK,
        fc: &FC,
    ) -> Vec<(String, usize, Option<LocatedConstructor>)>
    where
        FK: Fn(Kind) -> Kind,
        FC: Fn(Constructor) -> Constructor,
    {
        constrs
            .into_iter()
            .map(|(x, n, t)| (x, n, t.map(|t| mk(t, fk, fc))))
            .collect()
    }

    fn map_node<FK, FC, FE>(d: Declaration, fk: &FK, fc: &FC, fe: &FE) -> Declaration
    where
        FK: Fn(Kind) -> Kind,
        FC: Fn(Constructor) -> Constructor,
        FE: Fn(Expression) -> Expression,
    {
        let mfk = |k: LocatedKind| kind::map(k, fk);

        match d {
            Declaration::Constructor(x, n, k, c) => {
                let k2 = mfk(k);
                let c2 = mk(c, fk, fc);
                Declaration::Constructor(x, n, k2, c2)
            }

            Declaration::Datatype(dts) => {
                let dts2 = dts
                    .into_iter()
                    .map(|mut dt| {
                        dt.constrs = map_constrs(dt.constrs, fk, fc);
                        dt
                    })
                    .collect();
                Declaration::Datatype(dts2)
            }

            Declaration::DatatypeImp {
                name,
                id,
                orig_mod,
                orig_path,
                orig_name,
                orig_constrs_path,
                constrs,
            } => {
                let constrs2 = map_constrs(constrs, fk, fc);
                Declaration::DatatypeImp {
                    name,
                    id,
                    orig_mod,
                    orig_path,
                    orig_name,
                    orig_constrs_path,
                    constrs: constrs2,
                }
            }

            Declaration::Val(x, n, t, e) => {
                let t2 = mk(t, fk, fc);
                let e2 = me(e, fk, fc, fe);
                Declaration::Val(x, n, t2, e2)
            }

            Declaration::ValRec(vis) => {
                let vis2 = vis
                    .into_iter()
                    .map(|(x, n, t, e)| (x, n, mk(t, fk, fc), me(e, fk, fc, fe)))
                    .collect();
                Declaration::ValRec(vis2)
            }

            Declaration::Signature(x, n, s) => {
                // Sgn traversal is complex; leave as-is for now.
                Declaration::Signature(x, n, s)
            }

            Declaration::Structure(x, n, sgn, s) => Declaration::Structure(x, n, sgn, s),

            Declaration::FfiStr(x, n, sgn) => Declaration::FfiStr(x, n, sgn),

            Declaration::Export(m, sgn, s) => Declaration::Export(m, sgn, s),

            Declaration::Table {
                mod_id,
                name,
                name_id,
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
            } => Declaration::Table {
                mod_id,
                name,
                name_id,
                con: mk(con, fk, fc),
                exp: me(exp, fk, fc, fe),
                pk_con: mk(pk_con, fk, fc),
                pk_exp: me(pk_exp, fk, fc, fe),
                unique_con: mk(unique_con, fk, fc),
            },

            Declaration::Sequence(tn, x, n) => Declaration::Sequence(tn, x, n),

            Declaration::View(tn, x, n, e, c) => {
                Declaration::View(tn, x, n, me(e, fk, fc, fe), mk(c, fk, fc))
            }

            Declaration::Index(e1, e2) => {
                Declaration::Index(me(e1, fk, fc, fe), me(e2, fk, fc, fe))
            }

            Declaration::Database(s) => Declaration::Database(s),

            Declaration::Cookie(tn, x, n, c) => Declaration::Cookie(tn, x, n, mk(c, fk, fc)),

            Declaration::Style(tn, x, n) => Declaration::Style(tn, x, n),

            Declaration::Task(e1, e2) => Declaration::Task(me(e1, fk, fc, fe), me(e2, fk, fc, fe)),

            Declaration::Policy(e) => Declaration::Policy(me(e, fk, fc, fe)),

            Declaration::OnError(m, ms, x) => Declaration::OnError(m, ms, x),

            Declaration::Ffi(x, n, modes, t) => Declaration::Ffi(x, n, modes, mk(t, fk, fc)),
        }
    }

    // -----------------------------------------------------------------------
    // fold — accumulate state over a LocatedDeclaration
    // -----------------------------------------------------------------------

    pub fn fold<S, FK, FC, FE, FD>(
        d: &LocatedDeclaration,
        init: S,
        fk: &FK,
        fc: &FC,
        fe: &FE,
        fd: &FD,
    ) -> S
    where
        FK: Fn(&Kind, S) -> S,
        FC: Fn(&Constructor, S) -> S,
        FE: Fn(&Expression, S) -> S,
        FD: Fn(&Declaration, S) -> S,
    {
        let s = fd(&d.node, init);
        fold_node(&d.node, s, fk, fc, fe)
    }

    fn fc2<S, FK, FC>(c: &LocatedConstructor, s: S, fk: &FK, fc: &FC) -> S
    where
        FK: Fn(&Kind, S) -> S,
        FC: Fn(&Constructor, S) -> S,
    {
        con::fold(c, s, fk, fc)
    }

    fn fe2<S, FK, FC, FE>(e: &LocatedExpression, s: S, fk: &FK, fc: &FC, fe: &FE) -> S
    where
        FK: Fn(&Kind, S) -> S,
        FC: Fn(&Constructor, S) -> S,
        FE: Fn(&Expression, S) -> S,
    {
        exp::fold(e, s, fk, fc, fe)
    }

    fn fold_constrs<S, FK, FC>(
        constrs: &[(String, usize, Option<LocatedConstructor>)],
        init: S,
        fk: &FK,
        fc: &FC,
    ) -> S
    where
        FK: Fn(&Kind, S) -> S,
        FC: Fn(&Constructor, S) -> S,
    {
        constrs.iter().fold(init, |s, (_, _, t)| match t.as_ref() {
            None => s,
            Some(t_ref) => fc2(t_ref, s, fk, fc),
        })
    }

    fn fold_node<S, FK, FC, FE>(d: &Declaration, init: S, fk: &FK, fc: &FC, fe: &FE) -> S
    where
        FK: Fn(&Kind, S) -> S,
        FC: Fn(&Constructor, S) -> S,
        FE: Fn(&Expression, S) -> S,
    {
        match d {
            Declaration::Constructor(_, _, k, c) => {
                let s = kind::fold(k, init, fk);
                fc2(c, s, fk, fc)
            }

            Declaration::Datatype(dts) => dts
                .iter()
                .fold(init, |s, dt| fold_constrs(&dt.constrs, s, fk, fc)),

            Declaration::DatatypeImp { constrs, .. } => fold_constrs(constrs, init, fk, fc),

            Declaration::Val(_, _, t, e) => {
                let s = fc2(t, init, fk, fc);
                fe2(e, s, fk, fc, fe)
            }

            Declaration::ValRec(vis) => vis.iter().fold(init, |s, (_, _, t, e)| {
                let s = fc2(t, s, fk, fc);
                fe2(e, s, fk, fc, fe)
            }),

            Declaration::Table {
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
                ..
            } => {
                let s = fc2(con, init, fk, fc);
                let s = fe2(exp, s, fk, fc, fe);
                let s = fc2(pk_con, s, fk, fc);
                let s = fe2(pk_exp, s, fk, fc, fe);
                fc2(unique_con, s, fk, fc)
            }

            Declaration::View(_, _, _, e, c) => {
                let s = fe2(e, init, fk, fc, fe);
                fc2(c, s, fk, fc)
            }

            Declaration::Index(e1, e2) => {
                let s = fe2(e1, init, fk, fc, fe);
                fe2(e2, s, fk, fc, fe)
            }

            Declaration::Cookie(_, _, _, c) => fc2(c, init, fk, fc),

            Declaration::Task(e1, e2) => {
                let s = fe2(e1, init, fk, fc, fe);
                fe2(e2, s, fk, fc, fe)
            }

            Declaration::Policy(e) => fe2(e, init, fk, fc, fe),

            Declaration::Ffi(_, _, _, t) => fc2(t, init, fk, fc),

            _ => init,
        }
    }
}
