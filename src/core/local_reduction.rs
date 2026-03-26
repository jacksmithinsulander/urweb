//! Local algebraic simplification of Core programs.
//!
//! Performs beta/eta reduction and simple algebraic simplifications without
//! unfolding global named definitions. Used as a fast intra-body pass.
//!
//! The `Environment` is a stack of items that tracks what is known about each
//! de Bruijn variable. Items are:
//!
//! - `Unknown` — expression variable whose value is not known
//! - `Known(e)` — expression variable that equals `e`
//! - `UnknownC` — type variable whose value is not known
//! - `KnownC(c)` — type variable that equals `c`
//! - `Lift(lc, le)` — synthetic marker used inside `find_*` so substituted values
//!   get indices shifted after accumulating binders
//!
//! Mirrors `reduce_local.sml`.

#![allow(dead_code)]

use crate::core::*;
use crate::primitives::Prim;

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(crate) enum EnvItem {
    Unknown,
    Known(LocatedExpression),
    UnknownC,
    KnownC(LocatedConstructor),
    /// (con_lifts, exp_lifts) accumulated when traversing past Known/KnownC
    Lift(usize, usize),
}

type Environment = Vec<EnvItem>;

/// Removes all `Known` and `KnownC` items from the environment.
/// Used after a beta-step so previously substituted values do not interfere.
///
/// # Arguments
///
/// * `environment` - The environment to filter.
///
/// # Returns
///
/// A new environment containing only `Unknown`, `UnknownC`, and `Lift` items.
fn de_known(environment: &[EnvItem]) -> Environment {
    environment
        .iter()
        .filter(|item| !matches!(item, EnvItem::Known(_) | EnvItem::KnownC(_)))
        .cloned()
        .collect()
}

// ---------------------------------------------------------------------------
// Pattern-match result
// ---------------------------------------------------------------------------

enum MatchResult {
    Yes(Environment),
    No,
    Maybe,
}

// ---------------------------------------------------------------------------
// Shift helpers
// ---------------------------------------------------------------------------

/// Shifts all constructor de Bruijn indices >= `cutoff` by `delta`.
///
/// # Arguments
///
/// * `constructor` - The constructor tree to shift.
/// * `cutoff` - Indices >= this value are shifted.
/// * `delta` - Amount to add (may be negative).
///
/// # Returns
///
/// The constructor with de Bruijn indices updated; span is preserved.
pub fn shift_con(
    constructor: LocatedConstructor,
    cutoff: usize,
    delta: isize,
) -> LocatedConstructor {
    let span = constructor.span.clone();
    let node = match constructor.node {
        Constructor::Rel(de_bruijn_index) => {
            if de_bruijn_index >= cutoff {
                Constructor::Rel((de_bruijn_index as isize + delta) as usize)
            } else {
                Constructor::Rel(de_bruijn_index)
            }
        }
        Constructor::TFun(left_constructor, right_constructor) => Constructor::TFun(
            Box::new(shift_con(*left_constructor, cutoff, delta)),
            Box::new(shift_con(*right_constructor, cutoff, delta)),
        ),
        Constructor::TCFun(variable_name, kind, body) => Constructor::TCFun(
            variable_name,
            kind,
            Box::new(shift_con(*body, cutoff + 1, delta)),
        ),
        Constructor::TKFun(variable_name, body) => {
            Constructor::TKFun(variable_name, Box::new(shift_con(*body, cutoff, delta)))
        }
        Constructor::TRecord(inner) => {
            Constructor::TRecord(Box::new(shift_con(*inner, cutoff, delta)))
        }
        Constructor::Named(name_id) => Constructor::Named(name_id),
        Constructor::Ffi(module_name, type_name) => Constructor::Ffi(module_name, type_name),
        Constructor::App(function_constructor, argument_constructor) => Constructor::App(
            Box::new(shift_con(*function_constructor, cutoff, delta)),
            Box::new(shift_con(*argument_constructor, cutoff, delta)),
        ),
        Constructor::Abs(variable_name, kind, body) => Constructor::Abs(
            variable_name,
            kind,
            Box::new(shift_con(*body, cutoff + 1, delta)),
        ),
        Constructor::KAbs(variable_name, body) => {
            Constructor::KAbs(variable_name, Box::new(shift_con(*body, cutoff, delta)))
        }
        Constructor::KApp(constructor_part, kind_part) => Constructor::KApp(
            Box::new(shift_con(*constructor_part, cutoff, delta)),
            kind_part,
        ),
        Constructor::Name(name_string) => Constructor::Name(name_string),
        Constructor::Record(record_kind, key_value_pairs) => Constructor::Record(
            record_kind,
            key_value_pairs
                .into_iter()
                .map(|(key_constructor, value_constructor)| {
                    (
                        shift_con(key_constructor, cutoff, delta),
                        shift_con(value_constructor, cutoff, delta),
                    )
                })
                .collect(),
        ),
        Constructor::Concat(left_constructor, right_constructor) => Constructor::Concat(
            Box::new(shift_con(*left_constructor, cutoff, delta)),
            Box::new(shift_con(*right_constructor, cutoff, delta)),
        ),
        Constructor::Map(domain_kind, range_kind) => Constructor::Map(domain_kind, range_kind),
        Constructor::Unit => Constructor::Unit,
        Constructor::Tuple(constructors) => Constructor::Tuple(
            constructors
                .into_iter()
                .map(|constructor_item| shift_con(constructor_item, cutoff, delta))
                .collect(),
        ),
        Constructor::Proj(inner_constructor, projection_index) => Constructor::Proj(
            Box::new(shift_con(*inner_constructor, cutoff, delta)),
            projection_index,
        ),
    };
    Located { node, span }
}

/// Shifts expression de Bruijn indices >= `expression_cutoff` by `expression_delta`.
/// Also shifts constructor indices >= `constructor_cutoff` by `constructor_delta`.
///
/// # Arguments
///
/// * `expression` - The expression to shift.
/// * `expression_cutoff` - Expression indices >= this are shifted.
/// * `expression_delta` - Amount to add for expression indices.
/// * `constructor_cutoff` - Constructor indices >= this are shifted.
/// * `constructor_delta` - Amount to add for constructor indices.
///
/// # Returns
///
/// The expression with de Bruijn indices updated; span is preserved.
pub fn shift_exp(
    expression: LocatedExpression,
    expression_cutoff: usize,
    expression_delta: isize,
    constructor_cutoff: usize,
    constructor_delta: isize,
) -> LocatedExpression {
    let span = expression.span.clone();
    let shift_constructor = |constructor: LocatedConstructor| {
        shift_con(constructor, constructor_cutoff, constructor_delta)
    };
    let shift_pattern_constructor = |pattern_constructor: PatternConstructor| {
        shift_pat_con(pattern_constructor, constructor_cutoff, constructor_delta)
    };
    let node = match expression.node {
        Expression::Prim(primitive) => Expression::Prim(primitive),
        Expression::Rel(de_bruijn_index) => {
            if de_bruijn_index >= expression_cutoff {
                Expression::Rel((de_bruijn_index as isize + expression_delta) as usize)
            } else {
                Expression::Rel(de_bruijn_index)
            }
        }
        Expression::Named(name_id) => Expression::Named(name_id),
        Expression::Constructor(
            datatype_kind,
            pattern_constructor,
            constructor_arguments,
            optional_argument,
        ) => Expression::Constructor(
            datatype_kind,
            shift_pattern_constructor(pattern_constructor),
            constructor_arguments
                .into_iter()
                .map(shift_constructor)
                .collect(),
            optional_argument.map(|argument_expression| {
                Box::new(shift_exp(
                    *argument_expression,
                    expression_cutoff,
                    expression_delta,
                    constructor_cutoff,
                    constructor_delta,
                ))
            }),
        ),
        Expression::Ffi(module_name, symbol_name) => Expression::Ffi(module_name, symbol_name),
        Expression::FfiApp(module_name, function_name, arguments) => Expression::FfiApp(
            module_name,
            function_name,
            arguments
                .into_iter()
                .map(|(argument_expression, argument_constructor)| {
                    (
                        shift_exp(
                            argument_expression,
                            expression_cutoff,
                            expression_delta,
                            constructor_cutoff,
                            constructor_delta,
                        ),
                        shift_constructor(argument_constructor),
                    )
                })
                .collect(),
        ),
        Expression::App(function_expression, argument_expression) => Expression::App(
            Box::new(shift_exp(
                *function_expression,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            Box::new(shift_exp(
                *argument_expression,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
        ),
        Expression::Abs(variable_name, domain_type, range_type, body) => Expression::Abs(
            variable_name,
            shift_constructor(domain_type),
            shift_constructor(range_type),
            Box::new(shift_exp(
                *body,
                expression_cutoff + 1,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
        ),
        Expression::CApp(expression_function, type_argument) => Expression::CApp(
            Box::new(shift_exp(
                *expression_function,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            shift_constructor(type_argument),
        ),
        Expression::CAbs(variable_name, kind, body) => Expression::CAbs(
            variable_name,
            kind,
            Box::new(shift_exp(
                *body,
                expression_cutoff,
                expression_delta,
                constructor_cutoff + 1,
                constructor_delta,
            )),
        ),
        Expression::KApp(expression_function, kind_argument) => Expression::KApp(
            Box::new(shift_exp(
                *expression_function,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            kind_argument,
        ),
        Expression::KAbs(variable_name, body) => Expression::KAbs(
            variable_name,
            Box::new(shift_exp(
                *body,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
        ),
        Expression::Record(fields) => Expression::Record(
            fields
                .into_iter()
                .map(|(name_constructor, value_expression, type_constructor)| {
                    (
                        shift_constructor(name_constructor),
                        shift_exp(
                            value_expression,
                            expression_cutoff,
                            expression_delta,
                            constructor_cutoff,
                            constructor_delta,
                        ),
                        shift_constructor(type_constructor),
                    )
                })
                .collect(),
        ),
        Expression::Field(record_expression, field_constructor, field_meta) => Expression::Field(
            Box::new(shift_exp(
                *record_expression,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            shift_constructor(field_constructor),
            FieldMeta {
                field: shift_constructor(field_meta.field),
                rest: shift_constructor(field_meta.rest),
            },
        ),
        Expression::Concat(
            left_expression,
            left_constructor,
            right_expression,
            right_constructor,
        ) => Expression::Concat(
            Box::new(shift_exp(
                *left_expression,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            shift_constructor(left_constructor),
            Box::new(shift_exp(
                *right_expression,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            shift_constructor(right_constructor),
        ),
        Expression::Cut(record_expression, cut_constructor, cut_meta) => Expression::Cut(
            Box::new(shift_exp(
                *record_expression,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            shift_constructor(cut_constructor),
            FieldMeta {
                field: shift_constructor(cut_meta.field),
                rest: shift_constructor(cut_meta.rest),
            },
        ),
        Expression::CutMulti(record_expression, field_constructor, rest_meta) => {
            Expression::CutMulti(
                Box::new(shift_exp(
                    *record_expression,
                    expression_cutoff,
                    expression_delta,
                    constructor_cutoff,
                    constructor_delta,
                )),
                shift_constructor(field_constructor),
                RestMeta {
                    rest: shift_constructor(rest_meta.rest),
                },
            )
        }
        Expression::Case(discriminant_expression, arms, case_meta) => Expression::Case(
            Box::new(shift_exp(
                *discriminant_expression,
                expression_cutoff,
                expression_delta,
                constructor_cutoff,
                constructor_delta,
            )),
            arms.into_iter()
                .map(|(pattern, arm_body)| {
                    let binder_count = pat_binds_n(&pattern);
                    (
                        shift_pat(
                            pattern,
                            expression_cutoff,
                            expression_delta,
                            constructor_cutoff,
                            constructor_delta,
                        ),
                        shift_exp(
                            arm_body,
                            expression_cutoff + binder_count,
                            expression_delta,
                            constructor_cutoff,
                            constructor_delta,
                        ),
                    )
                })
                .collect(),
            CaseMeta {
                disc: shift_constructor(case_meta.disc),
                result: shift_constructor(case_meta.result),
            },
        ),
        Expression::Write(inner_expression) => Expression::Write(Box::new(shift_exp(
            *inner_expression,
            expression_cutoff,
            expression_delta,
            constructor_cutoff,
            constructor_delta,
        ))),
        Expression::Closure(closure_id, captured_expressions) => Expression::Closure(
            closure_id,
            captured_expressions
                .into_iter()
                .map(|captured_expression| {
                    shift_exp(
                        captured_expression,
                        expression_cutoff,
                        expression_delta,
                        constructor_cutoff,
                        constructor_delta,
                    )
                })
                .collect(),
        ),
        Expression::Let(variable_name, type_annotation, first_expression, second_expression) => {
            Expression::Let(
                variable_name,
                shift_constructor(type_annotation),
                Box::new(shift_exp(
                    *first_expression,
                    expression_cutoff,
                    expression_delta,
                    constructor_cutoff,
                    constructor_delta,
                )),
                Box::new(shift_exp(
                    *second_expression,
                    expression_cutoff + 1,
                    expression_delta,
                    constructor_cutoff,
                    constructor_delta,
                )),
            )
        }
        Expression::ServerCall(server_call_id, arguments, result_type, format_mode) => {
            Expression::ServerCall(
                server_call_id,
                arguments
                    .into_iter()
                    .map(|argument_expression| {
                        shift_exp(
                            argument_expression,
                            expression_cutoff,
                            expression_delta,
                            constructor_cutoff,
                            constructor_delta,
                        )
                    })
                    .collect(),
                shift_constructor(result_type),
                format_mode,
            )
        }
    };
    Located { node, span }
}

fn shift_pat_con(pc: PatternConstructor, cutoff_c: usize, delta_c: isize) -> PatternConstructor {
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
            // The arg type is in the scope of `params` type parameters
            let inner_cutoff = cutoff_c + params.len();
            PatternConstructor::Ffi {
                module,
                datatyp,
                params,
                con,
                arg: arg.map(|c| shift_con(c, inner_cutoff, delta_c)),
                kind,
            }
        }
    }
}

fn shift_pat(
    p: LocatedPattern,
    _cutoff_e: usize,
    _delta_e: isize,
    cutoff_c: usize,
    delta_c: isize,
) -> LocatedPattern {
    let span = p.span.clone();
    let sc = |c| shift_con(c, cutoff_c, delta_c);
    let node = match p.node {
        Pattern::Var(x, t) => Pattern::Var(x, sc(t)),
        Pattern::Prim(p) => Pattern::Prim(p),
        Pattern::Constructor(dk, pc, cs, inner) => Pattern::Constructor(
            dk,
            shift_pat_con(pc, cutoff_c, delta_c),
            cs.into_iter().map(sc).collect(),
            inner.map(|p| Box::new(shift_pat(*p, _cutoff_e, _delta_e, cutoff_c, delta_c))),
        ),
        Pattern::Record(fields) => Pattern::Record(
            fields
                .into_iter()
                .map(|(x, p, t)| {
                    (
                        x,
                        shift_pat(p, _cutoff_e, _delta_e, cutoff_c, delta_c),
                        sc(t),
                    )
                })
                .collect(),
        ),
    };
    Located { node, span }
}

/// Count the number of expression variables bound by a pattern.
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
// Constructor simplification
// ---------------------------------------------------------------------------

fn simplify_pat_con(env: &[EnvItem], pc: PatternConstructor) -> PatternConstructor {
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
            let mut inner_env: Environment = (0..n).map(|_| EnvItem::UnknownC).collect();
            inner_env.extend_from_slice(env);
            PatternConstructor::Ffi {
                module,
                datatyp,
                params,
                con,
                arg: arg.map(|c| simplify_con(&inner_env, c)),
                kind,
            }
        }
    }
}

/// Simplifies a constructor in the given environment (beta and map reductions, lookup of KnownC).
///
/// # Arguments
///
/// * `environment` - Stack of bindings (UnknownC, KnownC, etc.) for de Bruijn lookup.
/// * `constructor` - The constructor to simplify.
///
/// # Returns
///
/// The simplified constructor; span is preserved.
pub(crate) fn simplify_con(
    environment: &[EnvItem],
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    let span = constructor.span.clone();
    let mk = |node| Located {
        node,
        span: span.clone(),
    };
    match constructor.node {
        Constructor::TFun(left_constructor, right_constructor) => mk(Constructor::TFun(
            Box::new(simplify_con(environment, *left_constructor)),
            Box::new(simplify_con(environment, *right_constructor)),
        )),
        Constructor::TCFun(variable_name, kind, body) => {
            let extended_environment = prepend(EnvItem::UnknownC, environment);
            mk(Constructor::TCFun(
                variable_name,
                kind,
                Box::new(simplify_con(&extended_environment, *body)),
            ))
        }
        Constructor::TKFun(variable_name, body) => mk(Constructor::TKFun(
            variable_name,
            Box::new(simplify_con(environment, *body)),
        )),
        Constructor::TRecord(inner) => mk(Constructor::TRecord(Box::new(simplify_con(
            environment,
            *inner,
        )))),
        Constructor::Rel(de_bruijn_index) => {
            find_con(environment, de_bruijn_index, de_bruijn_index, 0, 0, &span)
        }
        Constructor::Named(_)
        | Constructor::Ffi(_, _)
        | Constructor::Name(_)
        | Constructor::Unit => constructor,
        Constructor::Map(_, _) => constructor,
        Constructor::App(function_constructor, argument_constructor) => {
            let simplified_function = simplify_con(environment, *function_constructor);
            let simplified_argument = simplify_con(environment, *argument_constructor);
            match simplified_function.node {
                // Beta: (fn _ :: _ => body) arg
                Constructor::Abs(_, _, body) => {
                    let extended_environment =
                        prepend(EnvItem::KnownC(simplified_argument), &de_known(environment));
                    simplify_con(&extended_environment, *body)
                }
                // Map reduction: (Map dom ran f) (Record(...))
                Constructor::App(ref map_f, _) if matches!(map_f.node, Constructor::Map(_, _)) => {
                    if let Constructor::Map(_, ran) = &map_f.node {
                        let ran = *ran.clone();
                        match &simplified_argument.node {
                            Constructor::Record(_, fields) if fields.is_empty() => {
                                mk(Constructor::Record(Box::new(ran), vec![]))
                            }
                            Constructor::Record(dom_k, fields) if !fields.is_empty() => {
                                // Expand: (Map dom ran f) [x=c, rest...]
                                // => [x = f c] ++ (Map dom ran f) [rest...]
                                let dom_k = *dom_k.clone();
                                let mut expanded = fields.clone();
                                let (first_x, first_c) = expanded.remove(0);
                                let applied = mk(Constructor::App(
                                    Box::new(Located {
                                        node: simplified_function.node.clone(),
                                        span: span.clone(),
                                    }),
                                    Box::new(first_c),
                                ));
                                let new_rec = mk(Constructor::Record(
                                    Box::new(ran.clone()),
                                    vec![(first_x, applied)],
                                ));
                                let rest_rec = mk(Constructor::Record(Box::new(dom_k), expanded));
                                let rest_applied = mk(Constructor::App(
                                    Box::new(Located {
                                        node: simplified_function.node,
                                        span: span.clone(),
                                    }),
                                    Box::new(rest_rec),
                                ));
                                let result = mk(Constructor::Concat(
                                    Box::new(new_rec),
                                    Box::new(rest_applied),
                                ));
                                simplify_con(&de_known(environment), result)
                            }
                            _ => mk(Constructor::App(
                                Box::new(Located {
                                    node: simplified_function.node,
                                    span: span.clone(),
                                }),
                                Box::new(simplified_argument),
                            )),
                        }
                    } else {
                        mk(Constructor::App(
                            Box::new(Located {
                                node: simplified_function.node,
                                span: span.clone(),
                            }),
                            Box::new(simplified_argument),
                        ))
                    }
                }
                other => mk(Constructor::App(
                    Box::new(Located {
                        node: other,
                        span: span.clone(),
                    }),
                    Box::new(simplified_argument),
                )),
            }
        }
        Constructor::Abs(variable_name, kind, body) => {
            let extended_environment = prepend(EnvItem::UnknownC, environment);
            mk(Constructor::Abs(
                variable_name,
                kind,
                Box::new(simplify_con(&extended_environment, *body)),
            ))
        }
        Constructor::KAbs(variable_name, body) => mk(Constructor::KAbs(
            variable_name,
            Box::new(simplify_con(environment, *body)),
        )),
        Constructor::KApp(constructor_part, kind_part) => {
            let simplified_constructor = simplify_con(environment, *constructor_part);
            match simplified_constructor.node {
                Constructor::KAbs(_, body) => simplify_con(&de_known(environment), *body),
                other => mk(Constructor::KApp(
                    Box::new(Located {
                        node: other,
                        span: span.clone(),
                    }),
                    kind_part,
                )),
            }
        }
        Constructor::Record(record_kind, key_value_pairs) => mk(Constructor::Record(
            record_kind,
            key_value_pairs
                .into_iter()
                .map(|(key_constructor, value_constructor)| {
                    (
                        simplify_con(environment, key_constructor),
                        simplify_con(environment, value_constructor),
                    )
                })
                .collect(),
        )),
        Constructor::Concat(left_constructor, right_constructor) => {
            let simplified_left = simplify_con(environment, *left_constructor);
            let simplified_right = simplify_con(environment, *right_constructor);
            match (&simplified_left.node, &simplified_right.node) {
                (
                    Constructor::Record(record_kind, key_value_pairs_left),
                    Constructor::Record(_, key_value_pairs_right),
                ) => {
                    let record_kind = record_kind.clone();
                    let mut all = key_value_pairs_left.clone();
                    all.extend(key_value_pairs_right.clone());
                    mk(Constructor::Record(record_kind, all))
                }
                (Constructor::Record(_, key_value_pairs), _) if key_value_pairs.is_empty() => {
                    simplified_right
                }
                (_, Constructor::Record(_, key_value_pairs)) if key_value_pairs.is_empty() => {
                    simplified_left
                }
                _ => mk(Constructor::Concat(
                    Box::new(simplified_left),
                    Box::new(simplified_right),
                )),
            }
        }
        Constructor::Tuple(constructors) => mk(Constructor::Tuple(
            constructors
                .into_iter()
                .map(|constructor_item| simplify_con(environment, constructor_item))
                .collect(),
        )),
        Constructor::Proj(inner_constructor, projection_index) => {
            let simplified_inner = simplify_con(environment, *inner_constructor);
            match simplified_inner.node {
                Constructor::Tuple(constructor_list) => {
                    constructor_list[projection_index - 1].clone()
                }
                other => mk(Constructor::Proj(
                    Box::new(Located {
                        node: other,
                        span: span.clone(),
                    }),
                    projection_index,
                )),
            }
        }
    }
}

/// Look up constructor de Bruijn index `n` in the environment.
///
/// - `n_orig`:     the original index (used when computing the final CRel value)
/// - `n_rem`:      remaining count to look up (decrements past UnknownC/KnownC)
/// - `nudge`:      accumulated index adjustment
/// - `lift_c`:     accumulated con-binder lift (for substituted values)
fn find_con(
    env: &[EnvItem],
    n_orig: usize,
    n_rem: usize,
    nudge: isize,
    lift_c: usize,
    span: &crate::error_types::Span,
) -> LocatedConstructor {
    match env.first() {
        None => {
            // Fallback (should not happen in well-formed programs)
            Located {
                node: Constructor::Rel((n_orig as isize + nudge) as usize),
                span: span.clone(),
            }
        }
        Some(item) => {
            let rest = &env[1..];
            match item {
                EnvItem::Unknown | EnvItem::Known(_) => {
                    // Expression binder: skip, does not affect con indexing
                    find_con(rest, n_orig, n_rem, nudge, lift_c, span)
                }
                EnvItem::Lift(lc, _le) => {
                    find_con(rest, n_orig, n_rem, nudge + *lc as isize, lift_c + lc, span)
                }
                EnvItem::UnknownC => {
                    if n_rem == 0 {
                        Located {
                            node: Constructor::Rel((n_orig as isize + nudge) as usize),
                            span: span.clone(),
                        }
                    } else {
                        find_con(rest, n_orig, n_rem - 1, nudge, lift_c + 1, span)
                    }
                }
                EnvItem::KnownC(c) => {
                    if n_rem == 0 {
                        // Substitute: simplify c in an env with Lift(lift_c,0) prepended
                        let env2 = prepend(EnvItem::Lift(lift_c, 0), rest);
                        simplify_con(&env2, c.clone())
                    } else {
                        // Past a KnownC: it "consumed" a slot, decrement nudge
                        find_con(rest, n_orig, n_rem - 1, nudge - 1, lift_c, span)
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Expression simplification
// ---------------------------------------------------------------------------

/// Simplify a pattern in env (types only, not expressions).
fn simplify_pat(env: &[EnvItem], p: LocatedPattern) -> LocatedPattern {
    let span = p.span.clone();
    let sc = |c| simplify_con(env, c);
    let node = match p.node {
        Pattern::Var(x, t) => Pattern::Var(x, sc(t)),
        Pattern::Prim(p) => Pattern::Prim(p),
        Pattern::Constructor(dk, pc, cs, inner) => Pattern::Constructor(
            dk,
            simplify_pat_con(env, pc),
            cs.into_iter().map(sc).collect(),
            inner.map(|p| Box::new(simplify_pat(env, *p))),
        ),
        Pattern::Record(fields) => Pattern::Record(
            fields
                .into_iter()
                .map(|(x, p, t)| (x, simplify_pat(env, p), sc(t)))
                .collect(),
        ),
    };
    Located { node, span }
}

/// Simplifies an expression in the given environment (beta and lookup of Known).
///
/// # Arguments
///
/// * `environment` - Stack of bindings for de Bruijn lookup.
/// * `expression` - The expression to simplify.
///
/// # Returns
///
/// The simplified expression; span is preserved.
pub(crate) fn simplify_exp(
    environment: &[EnvItem],
    expression: LocatedExpression,
) -> LocatedExpression {
    let span = expression.span.clone();
    let mk = |node| Located {
        node,
        span: span.clone(),
    };
    let shift_constructor =
        |constructor: LocatedConstructor| simplify_con(environment, constructor);
    match expression.node {
        Expression::Prim(primitive) => mk(Expression::Prim(primitive)),
        Expression::Rel(de_bruijn_index) => find_exp(
            environment,
            de_bruijn_index,
            de_bruijn_index,
            0,
            0,
            0,
            &span,
        ),
        Expression::Named(name_id) => mk(Expression::Named(name_id)),
        Expression::Constructor(
            datatype_kind,
            pattern_constructor,
            constructor_arguments,
            optional_argument,
        ) => mk(Expression::Constructor(
            datatype_kind,
            simplify_pat_con(environment, pattern_constructor),
            constructor_arguments
                .into_iter()
                .map(&shift_constructor)
                .collect(),
            optional_argument.map(|argument_expression| {
                Box::new(simplify_exp(environment, *argument_expression))
            }),
        )),
        Expression::Ffi(module_name, symbol_name) => mk(Expression::Ffi(module_name, symbol_name)),
        Expression::FfiApp(module_name, function_name, arguments) => mk(Expression::FfiApp(
            module_name,
            function_name,
            arguments
                .into_iter()
                .map(|(argument_expression, argument_constructor)| {
                    (
                        simplify_exp(environment, argument_expression),
                        shift_constructor(argument_constructor),
                    )
                })
                .collect(),
        )),
        Expression::App(function_expression, argument_expression) => {
            let simplified_function = simplify_exp(environment, *function_expression);
            let simplified_argument = simplify_exp(environment, *argument_expression);
            match simplified_function.node {
                Expression::Abs(_, _, _, body) => {
                    let extended_environment =
                        prepend(EnvItem::Known(simplified_argument), &de_known(environment));
                    simplify_exp(&extended_environment, *body)
                }
                other => mk(Expression::App(
                    Box::new(Located {
                        node: other,
                        span: span.clone(),
                    }),
                    Box::new(simplified_argument),
                )),
            }
        }
        Expression::Abs(variable_name, domain_type, range_type, body) => {
            let extended_environment = prepend(EnvItem::Unknown, environment);
            mk(Expression::Abs(
                variable_name,
                shift_constructor(domain_type),
                shift_constructor(range_type),
                Box::new(simplify_exp(&extended_environment, *body)),
            ))
        }
        Expression::CApp(expression_function, type_argument) => {
            let simplified_function = simplify_exp(environment, *expression_function);
            let simplified_type_argument = shift_constructor(type_argument);
            match simplified_function.node {
                Expression::CAbs(_, _, body) => {
                    let extended_environment = prepend(
                        EnvItem::KnownC(simplified_type_argument),
                        &de_known(environment),
                    );
                    simplify_exp(&extended_environment, *body)
                }
                other => mk(Expression::CApp(
                    Box::new(Located {
                        node: other,
                        span: span.clone(),
                    }),
                    simplified_type_argument,
                )),
            }
        }
        Expression::CAbs(variable_name, kind, body) => {
            let extended_environment = prepend(EnvItem::UnknownC, environment);
            mk(Expression::CAbs(
                variable_name,
                kind,
                Box::new(simplify_exp(&extended_environment, *body)),
            ))
        }
        Expression::KApp(expression_function, kind_argument) => mk(Expression::KApp(
            Box::new(simplify_exp(environment, *expression_function)),
            kind_argument,
        )),
        Expression::KAbs(variable_name, body) => mk(Expression::KAbs(
            variable_name,
            Box::new(simplify_exp(environment, *body)),
        )),
        Expression::Record(fields) => mk(Expression::Record(
            fields
                .into_iter()
                .map(|(name_constructor, value_expression, type_constructor)| {
                    (
                        shift_constructor(name_constructor),
                        simplify_exp(environment, value_expression),
                        shift_constructor(type_constructor),
                    )
                })
                .collect(),
        )),
        Expression::Field(record_expression, field_constructor, field_meta) => {
            let simplified_record = simplify_exp(environment, *record_expression);
            let simplified_field_constructor = shift_constructor(field_constructor);
            let simplified_meta = FieldMeta {
                field: shift_constructor(field_meta.field),
                rest: shift_constructor(field_meta.rest),
            };
            // Optimisation: (Record xcs).#field_name => matching field value
            match (&simplified_record.node, &simplified_field_constructor.node) {
                (Expression::Record(key_value_triples), Constructor::Name(field_name)) => {
                    let field_name = field_name.clone();
                    match key_value_triples.iter().find(|(key_constructor, _, _)| {
                        matches!(&key_constructor.node, Constructor::Name(name) if *name == field_name)
                    }) {
                        Some((_, value_expression, _)) => value_expression.clone(),
                        None => mk(Expression::Field(
                            Box::new(simplified_record),
                            simplified_field_constructor,
                            simplified_meta,
                        )),
                    }
                }
                _ => mk(Expression::Field(
                    Box::new(simplified_record),
                    simplified_field_constructor,
                    simplified_meta,
                )),
            }
        }
        Expression::Concat(
            left_expression,
            left_constructor,
            right_expression,
            right_constructor,
        ) => mk(Expression::Concat(
            Box::new(simplify_exp(environment, *left_expression)),
            shift_constructor(left_constructor),
            Box::new(simplify_exp(environment, *right_expression)),
            shift_constructor(right_constructor),
        )),
        Expression::Cut(record_expression, cut_constructor, cut_meta) => mk(Expression::Cut(
            Box::new(simplify_exp(environment, *record_expression)),
            shift_constructor(cut_constructor),
            FieldMeta {
                field: shift_constructor(cut_meta.field),
                rest: shift_constructor(cut_meta.rest),
            },
        )),
        Expression::CutMulti(record_expression, field_constructor, rest_meta) => {
            mk(Expression::CutMulti(
                Box::new(simplify_exp(environment, *record_expression)),
                shift_constructor(field_constructor),
                RestMeta {
                    rest: shift_constructor(rest_meta.rest),
                },
            ))
        }
        Expression::Case(discriminant_expression, arms, case_meta) => {
            let case_meta_simplified = CaseMeta {
                disc: shift_constructor(case_meta.disc),
                result: shift_constructor(case_meta.result),
            };
            let discriminant_simplified =
                simplify_exp(environment, *discriminant_expression.clone());

            // Try static case elimination
            let mut chosen_arm: Option<LocatedExpression> = None;
            let mut definitely_decided = false;

            'search: for (pattern, arm_body) in &arms {
                match try_match(environment, pattern, &discriminant_simplified) {
                    MatchResult::No => continue,
                    MatchResult::Maybe => {
                        // Cannot decide statically
                        break 'search;
                    }
                    MatchResult::Yes(arm_environment) => {
                        chosen_arm = Some(simplify_exp(&arm_environment, arm_body.clone()));
                        definitely_decided = true;
                        break 'search;
                    }
                }
            }

            let build_full_case =
                |arms: Vec<(LocatedPattern, LocatedExpression)>| -> LocatedExpression {
                    let arms_simplified: Vec<(LocatedPattern, LocatedExpression)> = arms
                        .into_iter()
                        .map(|(pattern, arm_body)| {
                            let binder_count = pat_binds_n(&pattern);
                            let pattern_simplified = simplify_pat(environment, pattern);
                            let mut arm_environment: Environment =
                                (0..binder_count).map(|_| EnvItem::Unknown).collect();
                            arm_environment.extend_from_slice(environment);
                            (pattern_simplified, simplify_exp(&arm_environment, arm_body))
                        })
                        .collect();
                    mk(Expression::Case(
                        Box::new(discriminant_simplified.clone()),
                        arms_simplified,
                        case_meta_simplified.clone(),
                    ))
                };

            if definitely_decided {
                match chosen_arm {
                    Some(arm) => arm,
                    None => {
                        eprintln!(
                            "{}",
                            crate::compiler_diagnostics::internal_compiler_error(
                                "local_reduction::simplify_exp",
                                "static case elimination decided a branch but the arm expression is missing",
                            )
                        );
                        build_full_case(arms)
                    }
                }
            } else {
                build_full_case(arms)
            }
        }
        Expression::Write(inner_expression) => mk(Expression::Write(Box::new(simplify_exp(
            environment,
            *inner_expression,
        )))),
        Expression::Closure(closure_id, captured_expressions) => mk(Expression::Closure(
            closure_id,
            captured_expressions
                .into_iter()
                .map(|captured_expression| simplify_exp(environment, captured_expression))
                .collect(),
        )),
        Expression::Let(variable_name, type_annotation, first_expression, second_expression) => {
            let extended_environment = prepend(EnvItem::Unknown, environment);
            mk(Expression::Let(
                variable_name,
                shift_constructor(type_annotation),
                Box::new(simplify_exp(environment, *first_expression)),
                Box::new(simplify_exp(&extended_environment, *second_expression)),
            ))
        }
        Expression::ServerCall(server_call_id, arguments, result_type, format_mode) => {
            mk(Expression::ServerCall(
                server_call_id,
                arguments
                    .into_iter()
                    .map(|argument_expression| simplify_exp(environment, argument_expression))
                    .collect(),
                shift_constructor(result_type),
                format_mode,
            ))
        }
    }
}

/// Look up expression de Bruijn index `n` in the environment.
///
/// - `n_orig`:     the original index
/// - `n_rem`:      remaining count
/// - `nudge`:      accumulated exp-index adjustment
/// - `lift_c`:     accumulated con-lift
/// - `lift_e`:     accumulated exp-lift
fn find_exp(
    env: &[EnvItem],
    n_orig: usize,
    n_rem: usize,
    nudge: isize,
    lift_c: usize,
    lift_e: usize,
    span: &crate::error_types::Span,
) -> LocatedExpression {
    match env.first() {
        None => Located {
            node: Expression::Rel((n_orig as isize + nudge) as usize),
            span: span.clone(),
        },
        Some(item) => {
            let rest = &env[1..];
            match item {
                EnvItem::Lift(lc, le) => find_exp(
                    rest,
                    n_orig,
                    n_rem,
                    nudge + *le as isize,
                    lift_c + lc,
                    lift_e + le,
                    span,
                ),
                EnvItem::UnknownC => find_exp(rest, n_orig, n_rem, nudge, lift_c + 1, lift_e, span),
                EnvItem::KnownC(_) => find_exp(rest, n_orig, n_rem, nudge, lift_c, lift_e, span),
                EnvItem::Unknown => {
                    if n_rem == 0 {
                        Located {
                            node: Expression::Rel((n_orig as isize + nudge) as usize),
                            span: span.clone(),
                        }
                    } else {
                        find_exp(rest, n_orig, n_rem - 1, nudge, lift_c, lift_e + 1, span)
                    }
                }
                EnvItem::Known(e) => {
                    if n_rem == 0 {
                        let env2 = prepend(EnvItem::Lift(lift_c, lift_e), rest);
                        simplify_exp(&env2, e.clone())
                    } else {
                        find_exp(rest, n_orig, n_rem - 1, nudge - 1, lift_c, lift_e, span)
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Pattern matching
// ---------------------------------------------------------------------------

fn try_match(env: &[EnvItem], p: &LocatedPattern, e: &LocatedExpression) -> MatchResult {
    let baseline = env.len();
    try_match_inner(env.to_vec(), p, e, baseline)
}

fn try_match_inner(
    env: Environment,
    p: &LocatedPattern,
    e: &LocatedExpression,
    baseline: usize,
) -> MatchResult {
    match (&p.node, &e.node) {
        (Pattern::Var(_, _), _) => {
            // Variable pattern always matches; record e (lifted for new binders)
            let n_lifts = env.len() - baseline;
            let lifted = shift_exp(e.clone(), 0, n_lifts as isize, 0, 0);
            MatchResult::Yes(prepend(EnvItem::Known(lifted), &env))
        }
        (Pattern::Prim(pp), Expression::Prim(ep)) => {
            if prim_eq(pp, ep) {
                MatchResult::Yes(env)
            } else {
                MatchResult::No
            }
        }
        (
            Pattern::Constructor(_, PatternConstructor::Var(n1), _, None),
            Expression::Constructor(_, PatternConstructor::Var(n2), _, None),
        ) => {
            if n1 == n2 {
                MatchResult::Yes(env)
            } else {
                MatchResult::No
            }
        }
        (
            Pattern::Constructor(_, PatternConstructor::Var(n1), _, Some(pp)),
            Expression::Constructor(_, PatternConstructor::Var(n2), _, Some(ee)),
        ) => {
            if n1 == n2 {
                try_match_inner(env, pp, ee, baseline)
            } else {
                MatchResult::No
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
                MatchResult::Yes(env)
            } else {
                MatchResult::No
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
                Some(pp),
            ),
            Expression::Constructor(
                _,
                PatternConstructor::Ffi {
                    module: m2,
                    con: c2,
                    ..
                },
                _,
                Some(ee),
            ),
        ) => {
            if m1 == m2 && c1 == c2 {
                try_match_inner(env, pp, ee, baseline)
            } else {
                MatchResult::No
            }
        }
        (Pattern::Record(xps), Expression::Record(xes)) => {
            // If any record field has a non-Name key, we can't decide
            if xes
                .iter()
                .any(|(x, _, _)| !matches!(x.node, Constructor::Name(_)))
            {
                return MatchResult::Maybe;
            }
            let mut cur_env = env;
            for (field_name, pp, _) in xps {
                match xes
                    .iter()
                    .find(|(x, _, _)| matches!(&x.node, Constructor::Name(n) if n == field_name))
                {
                    None => return MatchResult::No,
                    Some((_, ev, _)) => match try_match_inner(cur_env, pp, ev, baseline) {
                        MatchResult::No => return MatchResult::No,
                        MatchResult::Maybe => return MatchResult::Maybe,
                        MatchResult::Yes(env2) => cur_env = env2,
                    },
                }
            }
            MatchResult::Yes(cur_env)
        }
        _ => MatchResult::Maybe,
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
// Utilities
// ---------------------------------------------------------------------------

fn prepend(item: EnvItem, rest: &[EnvItem]) -> Environment {
    let mut v = vec![item];
    v.extend_from_slice(rest);
    v
}

// ---------------------------------------------------------------------------
// Top-level entry points
// ---------------------------------------------------------------------------

/// Algebraically simplify all expressions in a Core file.
pub fn reduce(file: File) -> File {
    file.into_iter()
        .map(|d| {
            let span = d.span.clone();
            let node = match d.node {
                Declaration::Val(x, n, t, e, s) => {
                    Declaration::Val(x, n, t, simplify_exp(&[] as &[EnvItem], e), s)
                }
                Declaration::ValRec(vis) => Declaration::ValRec(
                    vis.into_iter()
                        .map(|(x, n, t, e, s)| (x, n, t, simplify_exp(&[] as &[EnvItem], e), s))
                        .collect(),
                ),
                Declaration::Task(e1, e2) => Declaration::Task(
                    simplify_exp(&[] as &[EnvItem], e1),
                    simplify_exp(&[] as &[EnvItem], e2),
                ),
                Declaration::Policy(e) => Declaration::Policy(simplify_exp(&[] as &[EnvItem], e)),
                other => other,
            };
            Located { node, span }
        })
        .collect()
}

/// Simplifies a single expression with an empty environment (no global definitions unfolded).
///
/// # Arguments
///
/// * `expression` - The expression to reduce.
///
/// # Returns
///
/// The simplified expression (local beta/eta and algebraic simplification only).
pub fn reduce_exp(expression: LocatedExpression) -> LocatedExpression {
    simplify_exp(&[] as &[EnvItem], expression)
}

/// Simplifies a single constructor with an empty environment (no global definitions unfolded).
///
/// # Arguments
///
/// * `constructor` - The constructor to reduce.
///
/// # Returns
///
/// The simplified constructor (local beta and algebraic simplification only).
pub fn reduce_con(constructor: LocatedConstructor) -> LocatedConstructor {
    simplify_con(&[] as &[EnvItem], constructor)
}

// ---------------------------------------------------------------------------
// Unit tests — kill mutants in shift_con, shift_exp, reduce
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;
    use crate::primitives::Prim;

    #[test]
    fn shift_con_rel_at_cutoff_adds_delta() {
        // Rel(1) with cutoff 1, delta 1 → Rel(2). Kills + -> - and + -> * mutants.
        let c = Located::dummy(Constructor::Rel(1));
        let out = shift_con(c, 1, 1);
        assert!(matches!(out.node, Constructor::Rel(2)));
    }

    #[test]
    fn shift_con_rel_below_cutoff_unchanged() {
        // Rel(0) with cutoff 1 → Rel(0). Kills >= -> < mutant.
        let c = Located::dummy(Constructor::Rel(0));
        let out = shift_con(c, 1, 1);
        assert!(matches!(out.node, Constructor::Rel(0)));
    }

    #[test]
    fn shift_con_rel_negative_delta() {
        // Rel(2) with cutoff 1, delta -1 → Rel(1).
        let c = Located::dummy(Constructor::Rel(2));
        let out = shift_con(c, 1, -1);
        assert!(matches!(out.node, Constructor::Rel(1)));
    }

    #[test]
    fn shift_con_tfun_shifts_both_branches() {
        // TFun(Rel(0), Rel(2)) cutoff 1 delta 1: left stays 0, right 2→3.
        let left = Located::dummy(Constructor::Rel(0));
        let right = Located::dummy(Constructor::Rel(2));
        let c = Located::dummy(Constructor::TFun(Box::new(left), Box::new(right)));
        let out = shift_con(c, 1, 1);
        let Constructor::TFun(l, r) = &out.node else {
            panic!("expected TFun")
        };
        assert!(matches!(l.node, Constructor::Rel(0)));
        assert!(matches!(r.node, Constructor::Rel(3)));
    }

    #[test]
    fn shift_con_tcfun_shifts_body_with_cutoff_plus_one() {
        // TCFun body: shift_con(body, cutoff+1, delta). Rel(2) with cutoff 1, delta 1 → cutoff+1=2, Rel(2)>=2 → Rel(3).
        let body = Located::dummy(Constructor::Rel(2));
        let kind = Located::dummy(crate::core::Kind::Type);
        let c = Located::dummy(Constructor::TCFun(
            "a".into(),
            Box::new(kind),
            Box::new(body),
        ));
        let out = shift_con(c, 1, 1);
        let Constructor::TCFun(_, _, body_out) = &out.node else {
            panic!("expected TCFun")
        };
        assert!(matches!(body_out.node, Constructor::Rel(3)));
    }

    #[test]
    fn shift_con_abs_shifts_body_with_cutoff_plus_one() {
        // Abs body: shift_con(body, cutoff+1, delta). Rel(2) with cutoff 1, delta 1 → Rel(3).
        let body = Located::dummy(Constructor::Rel(2));
        let kind = Located::dummy(crate::core::Kind::Type);
        let c = Located::dummy(Constructor::Abs("x".into(), Box::new(kind), Box::new(body)));
        let out = shift_con(c, 1, 1);
        let Constructor::Abs(_, _, body_out) = &out.node else {
            panic!("expected Abs")
        };
        assert!(matches!(body_out.node, Constructor::Rel(3)));
    }

    #[test]
    fn shift_exp_abs_shifts_body_with_cutoff_plus_one() {
        // Abs body: shift_exp with expression_cutoff+1. Rel(2) with cutoff 1, delta 1 → Rel(3).
        let body = Located::dummy(Expression::Rel(2));
        let unit = Located::dummy(Constructor::Unit);
        let e = Located::dummy(Expression::Abs(
            "x".into(),
            unit.clone(),
            unit,
            Box::new(body),
        ));
        let out = shift_exp(e, 1, 1, 0, 0);
        let Expression::Abs(_, _, _, body_out) = &out.node else {
            panic!("expected Abs")
        };
        assert!(matches!(body_out.node, Expression::Rel(3)));
    }

    #[test]
    fn shift_exp_rel_at_cutoff_adds_delta() {
        // Rel(1) with cutoff 1, delta 1 → Rel(2).
        let e = Located::dummy(Expression::Rel(1));
        let out = shift_exp(e, 1, 1, 0, 0);
        assert!(matches!(out.node, Expression::Rel(2)));
    }

    #[test]
    fn shift_exp_rel_below_cutoff_unchanged() {
        let e = Located::dummy(Expression::Rel(0));
        let out = shift_exp(e, 1, 1, 0, 0);
        assert!(matches!(out.node, Expression::Rel(0)));
    }

    #[test]
    fn reduce_exp_identity_for_prim() {
        let e = Located::dummy(Expression::Prim(Prim::Int(42)));
        let out = reduce_exp(e.clone());
        assert!(matches!(out.node, Expression::Prim(_)));
    }

    #[test]
    fn reduce_con_unit_unchanged() {
        let c = Located::dummy(Constructor::Unit);
        let out = reduce_con(c);
        assert!(matches!(out.node, Constructor::Unit));
    }

    #[test]
    fn reduce_empty_file() {
        let file: crate::core::File = vec![];
        let out = reduce(file);
        assert!(out.is_empty());
    }

    #[test]
    fn reduce_val_simplifies_body() {
        let e = Located::dummy(Expression::Prim(Prim::Int(1)));
        let decl = Located::dummy(Declaration::Val(
            "x".into(),
            0,
            Located::dummy(Constructor::Unit),
            e,
            String::new(),
        ));
        let file = vec![decl];
        let out = reduce(file);
        assert_eq!(out.len(), 1);
        if let Declaration::Val(_, _, _, body, _) = &out[0].node {
            assert!(matches!(body.node, Expression::Prim(_)));
        } else {
            panic!("expected Val");
        }
    }

    // --- Plan: Catch Missed Mutants - local_reduction ---

    #[test]
    fn shift_con_rel_delta_two() {
        // Kills: + -> - and + -> * in Rel branch. Rel(1), cutoff 1, delta 2 -> Rel(3).
        let c = Located::dummy(Constructor::Rel(1));
        let out = shift_con(c, 1, 2);
        assert!(matches!(out.node, Constructor::Rel(3)));
    }

    #[test]
    fn shift_exp_rel_delta_two() {
        // Kills: + -> - and + -> * in Rel. Rel(1), cutoff 1, delta 2 -> Rel(3).
        let e = Located::dummy(Expression::Rel(1));
        let out = shift_exp(e, 1, 2, 0, 0);
        assert!(matches!(out.node, Expression::Rel(3)));
    }

    #[test]
    fn shift_con_rel_negative_delta_decrements() {
        // Kills: - -> + and - -> / in Rel. Rel(3), cutoff 1, delta -1 -> Rel(2).
        let c = Located::dummy(Constructor::Rel(3));
        let out = shift_con(c, 1, -1);
        assert!(matches!(out.node, Constructor::Rel(2)));
    }

    #[test]
    fn reduce_exp_field_of_record_projects() {
        // Kills: Field+Record arm in simplify_exp, find logic.
        let field_name = Located::dummy(Constructor::Name("x".into()));
        let unit_ty = Located::dummy(Constructor::Unit);
        let value = Located::dummy(Expression::Prim(Prim::Int(42)));
        let rec = Located::dummy(Expression::Record(vec![(
            field_name.clone(),
            value,
            unit_ty.clone(),
        )]));
        let meta = crate::core::FieldMeta {
            field: unit_ty.clone(),
            rest: Located::dummy(Constructor::Record(
                Box::new(Located::dummy(crate::core::Kind::Type)),
                vec![],
            )),
        };
        let field_exp = Located::dummy(Expression::Field(Box::new(rec), field_name, meta));
        let out = reduce_exp(field_exp);
        assert!(matches!(out.node, Expression::Prim(Prim::Int(42))));
    }

    #[test]
    fn reduce_exp_case_var_always_matches() {
        // Kills: delete Var arm in try_match. Case(disc, [(Var, body)]) -> body with subst.
        let disc = Located::dummy(Expression::Prim(Prim::Int(0)));
        let body = Located::dummy(Expression::Prim(Prim::Int(99)));
        let var_pat = Located::dummy(crate::core::Pattern::Var(
            "x".into(),
            Located::dummy(Constructor::Unit),
        ));
        let case_meta = crate::core::CaseMeta {
            disc: Located::dummy(Constructor::Unit),
            result: Located::dummy(Constructor::Unit),
        };
        let case = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(var_pat, body)],
            case_meta,
        ));
        let out = reduce_exp(case);
        assert!(matches!(out.node, Expression::Prim(Prim::Int(99))));
    }

    #[test]
    fn reduce_exp_case_prim_equal_matches() {
        // Kills: delete Prim arm, == -> !=. Case(Prim(1), [(Prim(1), body)]) -> body.
        let disc = Located::dummy(Expression::Prim(Prim::Int(1)));
        let body = Located::dummy(Expression::Prim(Prim::Int(100)));
        let prim_pat = Located::dummy(crate::core::Pattern::Prim(Prim::Int(1)));
        let case_meta = crate::core::CaseMeta {
            disc: Located::dummy(Constructor::Unit),
            result: Located::dummy(Constructor::Unit),
        };
        let case = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(prim_pat, body)],
            case_meta,
        ));
        let out = reduce_exp(case);
        assert!(matches!(out.node, Expression::Prim(Prim::Int(100))));
    }

    #[test]
    fn reduce_exp_case_prim_not_equal_continues() {
        // Kills: == -> !=. Case(Prim(1), [(Prim(2), body)]) -> Case (no match).
        let disc = Located::dummy(Expression::Prim(Prim::Int(1)));
        let body = Located::dummy(Expression::Prim(Prim::Int(100)));
        let prim_pat = Located::dummy(crate::core::Pattern::Prim(Prim::Int(2)));
        let case_meta = crate::core::CaseMeta {
            disc: Located::dummy(Constructor::Unit),
            result: Located::dummy(Constructor::Unit),
        };
        let case = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(prim_pat, body)],
            case_meta,
        ));
        let out = reduce_exp(case);
        // Should remain Case (no static match) since 1 != 2
        assert!(matches!(out.node, Expression::Case(_, _, _)));
    }

    #[test]
    fn reduce_exp_case_float_equal_matches() {
        let disc = Located::dummy(Expression::Prim(Prim::Float(1.5)));
        let body = Located::dummy(Expression::Prim(Prim::Int(101)));
        let prim_pat = Located::dummy(crate::core::Pattern::Prim(Prim::Float(1.5)));
        let case_meta = crate::core::CaseMeta {
            disc: Located::dummy(Constructor::Unit),
            result: Located::dummy(Constructor::Unit),
        };
        let case = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(prim_pat, body)],
            case_meta,
        ));
        let out = reduce_exp(case);
        assert!(matches!(out.node, Expression::Prim(Prim::Int(101))));
    }

    #[test]
    fn reduce_exp_case_string_equal_matches() {
        use crate::primitives::StringMode;
        let disc = Located::dummy(Expression::Prim(Prim::String(
            StringMode::Normal,
            "hi".into(),
        )));
        let body = Located::dummy(Expression::Prim(Prim::Int(102)));
        let prim_pat = Located::dummy(crate::core::Pattern::Prim(Prim::String(
            StringMode::Normal,
            "hi".into(),
        )));
        let case_meta = crate::core::CaseMeta {
            disc: Located::dummy(Constructor::Unit),
            result: Located::dummy(Constructor::Unit),
        };
        let case = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(prim_pat, body)],
            case_meta,
        ));
        let out = reduce_exp(case);
        assert!(matches!(out.node, Expression::Prim(Prim::Int(102))));
    }

    #[test]
    fn reduce_exp_case_char_equal_matches() {
        let disc = Located::dummy(Expression::Prim(Prim::Char('a')));
        let body = Located::dummy(Expression::Prim(Prim::Int(103)));
        let prim_pat = Located::dummy(crate::core::Pattern::Prim(Prim::Char('a')));
        let case_meta = crate::core::CaseMeta {
            disc: Located::dummy(Constructor::Unit),
            result: Located::dummy(Constructor::Unit),
        };
        let case = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(prim_pat, body)],
            case_meta,
        ));
        let out = reduce_exp(case);
        assert!(matches!(out.node, Expression::Prim(Prim::Int(103))));
    }

    #[test]
    fn reduce_con_record_concat_merges() {
        // Record + Record -> merged Record. Kills delete Record arm in simplify_con.
        let k = Located::dummy(crate::core::Kind::Type);
        let unit = Located::dummy(Constructor::Unit);
        let r1 = Located::dummy(Constructor::Record(
            Box::new(k.clone()),
            vec![(Located::dummy(Constructor::Name("x".into())), unit.clone())],
        ));
        let r2 = Located::dummy(Constructor::Record(
            Box::new(k),
            vec![(Located::dummy(Constructor::Name("y".into())), unit)],
        ));
        let concat = Located::dummy(Constructor::Concat(Box::new(r1), Box::new(r2)));
        let out = reduce_con(concat);
        let Constructor::Record(_, fields) = &out.node else {
            panic!("expected Record, got {:?}", out.node)
        };
        assert_eq!(fields.len(), 2);
    }

    #[test]
    fn pat_binds_n_var_one() {
        let p = Located::dummy(crate::core::Pattern::Var(
            "x".into(),
            Located::dummy(Constructor::Unit),
        ));
        assert_eq!(pat_binds_n(&p), 1);
    }

    #[test]
    fn pat_binds_n_prim_zero() {
        let p = Located::dummy(crate::core::Pattern::Prim(Prim::Int(0)));
        assert_eq!(pat_binds_n(&p), 0);
    }

    #[test]
    fn de_known_removes_known_and_knownc() {
        let unit = Located::dummy(Constructor::Unit);
        let env: Environment = vec![
            EnvItem::Unknown,
            EnvItem::Known(Located::dummy(Expression::Prim(Prim::Int(0)))),
            EnvItem::UnknownC,
            EnvItem::KnownC(unit),
            EnvItem::Lift(1, 1),
        ];
        let out = de_known(&env);
        assert_eq!(out.len(), 3);
        assert!(matches!(out[0], EnvItem::Unknown));
        assert!(matches!(out[1], EnvItem::UnknownC));
        assert!(matches!(out[2], EnvItem::Lift(1, 1)));
    }
}
