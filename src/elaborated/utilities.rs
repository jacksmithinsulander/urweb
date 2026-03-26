//! Traversal utilities for the Elab AST.
//!
//! Mirrors `elab_util.sml`.

#![allow(dead_code, unused_variables, unused_imports)]

use std::sync::{Arc, Mutex};

use crate::datatype_kind::DatatypeKind;
use crate::elaborated::*;
use crate::error_types::Located;

// ---------------------------------------------------------------------------
// classify_datatype
// ---------------------------------------------------------------------------

/// Classifies a datatype's representation kind from its constructor specifications.
///
/// # Arguments
///
/// * `constructor_specifications` - Slice of (name, id, optional argument type) for each constructor.
///
/// # Returns
///
/// `DatatypeKind::Enum` if all constructors are nullary, `DatatypeKind::Option` if exactly one nullary
/// and one unary, otherwise `DatatypeKind::Default`. Used to choose C representation.
pub fn classify_datatype(
    constructor_specifications: &[(String, usize, Option<LocatedConstructor>)],
) -> DatatypeKind {
    let mut nullary = 0usize;
    let mut unary = 0usize;
    for (_, _, optional_argument_type) in constructor_specifications {
        if optional_argument_type.is_none() {
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
/// Lifts constructor de Bruijn indices through `binder_count` binders.
pub(crate) fn mlift_con_in_con(
    binder_count: usize,
    constructor: LocatedConstructor,
) -> LocatedConstructor {
    crate::elaborated::type_operations::mlift_con_in_con(binder_count, constructor)
}

// ---------------------------------------------------------------------------
// Binder — unified traversal context type
// ---------------------------------------------------------------------------

/// Context element pushed when descending into a binding form.
#[derive(Debug, Clone)]
pub enum Binder {
    RelK(String),
    RelC(String, LocatedKind),
    NamedC(String, usize, LocatedKind, Option<LocatedConstructor>),
    RelE(String, LocatedConstructor),
    NamedE(String, usize, LocatedConstructor),
}

// ---------------------------------------------------------------------------
// kind module
// ---------------------------------------------------------------------------

pub mod kind {
    use super::*;

    /// Recursively maps over all sub-kinds with a post-order visitor (no binder context).
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind tree to map over.
    /// * `visitor` - Closure called on each sub-kind; returns the replacement.
    ///
    /// # Returns
    ///
    /// The kind tree with all nodes transformed.
    pub fn map(kind: LocatedKind, visitor: &dyn Fn(LocatedKind) -> LocatedKind) -> LocatedKind {
        map_b(kind, &mut vec![], &|_context, kind| visitor(kind))
    }

    /// Like `map` but provides a binder context to the callback.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind tree to map over.
    /// * `context` - Mutable binder stack; pushed/popped when entering/leaving binding forms.
    /// * `fold_kind_binder` - Called for each kind with (context, kind); returns replacement.
    ///
    /// # Returns
    ///
    /// The kind tree with all nodes transformed; final result passed through fold_kind_binder.
    pub fn map_b(
        kind: LocatedKind,
        context: &mut Vec<Binder>,
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
    ) -> LocatedKind {
        let span = kind.span.clone();
        let mapped = match kind.node {
            Kind::Type => Located::new(Kind::Type, span),
            Kind::Name => Located::new(Kind::Name, span),
            Kind::Unit => Located::new(Kind::Unit, span),
            Kind::Error => Located::new(Kind::Error, span),
            Kind::Rel(de_bruijn_index) => Located::new(Kind::Rel(de_bruijn_index), span),

            Kind::Arrow(left_kind, right_kind) => {
                let left_mapped = map_b(*left_kind, context, fold_kind_binder);
                let right_mapped = map_b(*right_kind, context, fold_kind_binder);
                Located::new(
                    Kind::Arrow(Box::new(left_mapped), Box::new(right_mapped)),
                    span,
                )
            }
            Kind::Record(inner) => {
                let inner_mapped = map_b(*inner, context, fold_kind_binder);
                Located::new(Kind::Record(Box::new(inner_mapped)), span)
            }
            Kind::Tuple(kinds) => {
                let kinds_mapped: Vec<LocatedKind> = kinds
                    .into_iter()
                    .map(|kind_item| map_b(kind_item, context, fold_kind_binder))
                    .collect();
                Located::new(Kind::Tuple(kinds_mapped), span)
            }
            Kind::Fun(variable_name, body) => {
                context.push(Binder::RelK(variable_name.clone()));
                let body_mapped = map_b(*body, context, fold_kind_binder);
                context.pop();
                Located::new(Kind::Fun(variable_name, Box::new(body_mapped)), span)
            }
            // Unification variable: if solved, recurse into the solution.
            Kind::Unif(span_inner, state, reference) => {
                let known_kind = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        KUnif::Known(known) => Some(*known.clone()),
                        KUnif::Unknown => None,
                    }
                };
                match known_kind {
                    Some(known_kind_value) => map_b(known_kind_value, context, fold_kind_binder),
                    None => Located::new(Kind::Unif(span_inner, state, reference), span),
                }
            }
            Kind::TupleUnif(span_inner, kind_index_pairs, reference) => {
                let known_kind = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        KUnif::Known(known) => Some(*known.clone()),
                        KUnif::Unknown => None,
                    }
                };
                match known_kind {
                    Some(known_kind_value) => map_b(known_kind_value, context, fold_kind_binder),
                    None => {
                        let pairs_mapped: Vec<(usize, LocatedKind)> = kind_index_pairs
                            .into_iter()
                            .map(|(index, kind_item)| {
                                (index, map_b(kind_item, context, fold_kind_binder))
                            })
                            .collect();
                        Located::new(Kind::TupleUnif(span_inner, pairs_mapped, reference), span)
                    }
                }
            }
        };
        fold_kind_binder(context, mapped)
    }

    /// Folds over all sub-kinds in pre-order (no binder context).
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind tree to fold over.
    /// * `initial_state` - Starting accumulator value.
    /// * `folder` - Closure called for each node with (kind reference, state); returns new state.
    ///
    /// # Returns
    ///
    /// The final accumulated state.
    pub fn fold<State>(
        kind: &LocatedKind,
        initial_state: State,
        folder: &dyn Fn(&LocatedKind, State) -> State,
    ) -> State {
        fold_b(kind, &[], initial_state, &|_context, kind, state| {
            folder(kind, state)
        })
    }

    /// Like `fold` but provides a binder context to the callback.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind tree to fold over.
    /// * `context` - Current binder stack (read-only).
    /// * `initial_state` - Starting accumulator value.
    /// * `fold_kind_binder` - Called for each kind with (context, kind, state); returns new state.
    ///
    /// # Returns
    ///
    /// The final accumulated state.
    pub fn fold_b<State>(
        kind: &LocatedKind,
        context: &[Binder],
        initial_state: State,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, State) -> State,
    ) -> State {
        let state = fold_kind_binder(context, kind, initial_state);
        match &kind.node {
            Kind::Type | Kind::Name | Kind::Unit | Kind::Error | Kind::Rel(_) => state,
            Kind::Arrow(left_kind, right_kind) => {
                let state = fold_b(left_kind, context, state, fold_kind_binder);
                fold_b(right_kind, context, state, fold_kind_binder)
            }
            Kind::Record(inner) => fold_b(inner, context, state, fold_kind_binder),
            Kind::Tuple(kinds) => kinds.iter().fold(state, |accumulator, kind_item| {
                fold_b(kind_item, context, accumulator, fold_kind_binder)
            }),
            Kind::Fun(variable_name, body) => {
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelK(variable_name.clone()));
                fold_b(body, &extended_context, state, fold_kind_binder)
            }
            Kind::Unif(_, _, reference) => {
                let known_kind = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        KUnif::Known(known) => Some(*known.clone()),
                        KUnif::Unknown => None,
                    }
                };
                match known_kind {
                    Some(known_kind_value) => {
                        fold_b(&known_kind_value, context, state, fold_kind_binder)
                    }
                    None => state,
                }
            }
            Kind::TupleUnif(_, kind_index_pairs, reference) => {
                let known_kind = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        KUnif::Known(known) => Some(*known.clone()),
                        KUnif::Unknown => None,
                    }
                };
                match known_kind {
                    Some(known_kind_value) => {
                        fold_b(&known_kind_value, context, state, fold_kind_binder)
                    }
                    None => kind_index_pairs
                        .iter()
                        .fold(state, |accumulator, (_, kind_item)| {
                            fold_b(kind_item, context, accumulator, fold_kind_binder)
                        }),
                }
            }
        }
    }

    /// Returns true if any sub-kind satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind tree to search.
    /// * `predicate` - Closure that returns true for a matching node.
    ///
    /// # Returns
    ///
    /// True when predicate returns true for at least one node (short-circuits).
    pub fn exists(kind: &LocatedKind, predicate: &dyn Fn(&LocatedKind) -> bool) -> bool {
        if predicate(kind) {
            return true;
        }
        match &kind.node {
            Kind::Type | Kind::Name | Kind::Unit | Kind::Error | Kind::Rel(_) => false,
            Kind::Arrow(left_kind, right_kind) => {
                exists(left_kind, predicate) || exists(right_kind, predicate)
            }
            Kind::Record(inner) => exists(inner, predicate),
            Kind::Tuple(kinds) => kinds.iter().any(|kind_item| exists(kind_item, predicate)),
            Kind::Fun(_, body) => exists(body, predicate),
            Kind::Unif(_, _, reference) => {
                let known_kind = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        KUnif::Known(known) => Some(*known.clone()),
                        KUnif::Unknown => None,
                    }
                };
                match known_kind {
                    Some(known_kind_value) => exists(&known_kind_value, predicate),
                    None => false,
                }
            }
            Kind::TupleUnif(_, kind_index_pairs, reference) => {
                let known_kind = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        KUnif::Known(known) => Some(*known.clone()),
                        KUnif::Unknown => None,
                    }
                };
                match known_kind {
                    Some(known_kind_value) => exists(&known_kind_value, predicate),
                    None => kind_index_pairs
                        .iter()
                        .any(|(_, kind_item)| exists(kind_item, predicate)),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// con module
// ---------------------------------------------------------------------------

pub mod con {
    use super::kind as kind_utilities;
    use super::*;

    /// Recursively maps over all sub-constructors and sub-kinds with post-order visitors (no binder context).
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to map over.
    /// * `kind_mapper` - Called for each kind; returns the replacement.
    /// * `constructor_mapper` - Called for each constructor; returns the replacement.
    ///
    /// # Returns
    ///
    /// The constructor tree with all nodes transformed.
    pub fn map(
        constructor: LocatedConstructor,
        kind_mapper: &dyn Fn(LocatedKind) -> LocatedKind,
        constructor_mapper: &dyn Fn(LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        map_b(
            constructor,
            &mut vec![],
            &|_context, kind| kind_mapper(kind),
            &|_context, constructor| constructor_mapper(constructor),
        )
    }

    /// Like `map` but provides a binder context to the callbacks.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to map over.
    /// * `context` - Mutable binder stack; pushed/popped when entering/leaving binding forms.
    /// * `fold_kind_binder` - Called for each kind with binder context.
    /// * `fold_con_binder` - Called for each constructor with binder context.
    ///
    /// # Returns
    ///
    /// The constructor tree with all nodes transformed; final result passed through fold_con_binder.
    pub fn map_b(
        constructor: LocatedConstructor,
        context: &mut Vec<Binder>,
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        let span = constructor.span.clone();
        let mapped = match constructor.node {
            Constructor::Rel(de_bruijn_index) => {
                Located::new(Constructor::Rel(de_bruijn_index), span)
            }
            Constructor::Named(name_id) => Located::new(Constructor::Named(name_id), span),
            Constructor::ModProj(module_id, path, name) => {
                Located::new(Constructor::ModProj(module_id, path, name), span)
            }
            Constructor::Name(name_string) => Located::new(Constructor::Name(name_string), span),
            Constructor::Unit => Located::new(Constructor::Unit, span),
            Constructor::Error => Located::new(Constructor::Error, span),

            Constructor::TFun(left_constructor, right_constructor) => {
                let left_mapped = map_b(
                    *left_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let right_mapped = map_b(
                    *right_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::TFun(Box::new(left_mapped), Box::new(right_mapped)),
                    span,
                )
            }
            Constructor::TCFun(explicitness, variable_name, kind, body) => {
                let kind_mapped = kind_utilities::map_b(*kind.clone(), context, fold_kind_binder);
                context.push(Binder::RelC(variable_name.clone(), *kind));
                let body_mapped = map_b(*body, context, fold_kind_binder, fold_con_binder);
                context.pop();
                Located::new(
                    Constructor::TCFun(
                        explicitness,
                        variable_name,
                        Box::new(kind_mapped),
                        Box::new(body_mapped),
                    ),
                    span,
                )
            }
            Constructor::TRecord(inner) => {
                let inner_mapped = map_b(*inner, context, fold_kind_binder, fold_con_binder);
                Located::new(Constructor::TRecord(Box::new(inner_mapped)), span)
            }
            Constructor::TDisjoint(left_constructor, middle_constructor, right_constructor) => {
                let left_mapped = map_b(
                    *left_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let middle_mapped = map_b(
                    *middle_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let right_mapped = map_b(
                    *right_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::TDisjoint(
                        Box::new(left_mapped),
                        Box::new(middle_mapped),
                        Box::new(right_mapped),
                    ),
                    span,
                )
            }
            Constructor::App(function_constructor, argument_constructor) => {
                let function_mapped = map_b(
                    *function_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let argument_mapped = map_b(
                    *argument_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::App(Box::new(function_mapped), Box::new(argument_mapped)),
                    span,
                )
            }
            Constructor::Abs(variable_name, kind, body) => {
                let kind_mapped = kind_utilities::map_b(*kind.clone(), context, fold_kind_binder);
                context.push(Binder::RelC(variable_name.clone(), *kind));
                let body_mapped = map_b(*body, context, fold_kind_binder, fold_con_binder);
                context.pop();
                Located::new(
                    Constructor::Abs(variable_name, Box::new(kind_mapped), Box::new(body_mapped)),
                    span,
                )
            }
            Constructor::KAbs(variable_name, body) => {
                context.push(Binder::RelK(variable_name.clone()));
                let body_mapped = map_b(*body, context, fold_kind_binder, fold_con_binder);
                context.pop();
                Located::new(
                    Constructor::KAbs(variable_name, Box::new(body_mapped)),
                    span,
                )
            }
            Constructor::KApp(constructor_part, kind_part) => {
                let constructor_mapped = map_b(
                    *constructor_part,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let kind_mapped = kind_utilities::map_b(*kind_part, context, fold_kind_binder);
                Located::new(
                    Constructor::KApp(Box::new(constructor_mapped), Box::new(kind_mapped)),
                    span,
                )
            }
            Constructor::TKFun(variable_name, body) => {
                context.push(Binder::RelK(variable_name.clone()));
                let body_mapped = map_b(*body, context, fold_kind_binder, fold_con_binder);
                context.pop();
                Located::new(
                    Constructor::TKFun(variable_name, Box::new(body_mapped)),
                    span,
                )
            }
            Constructor::Record(record_kind, key_value_pairs) => {
                let kind_mapped = kind_utilities::map_b(*record_kind, context, fold_kind_binder);
                let pairs_mapped: Vec<(LocatedConstructor, LocatedConstructor)> = key_value_pairs
                    .into_iter()
                    .map(|(key_constructor, value_constructor)| {
                        (
                            map_b(key_constructor, context, fold_kind_binder, fold_con_binder),
                            map_b(
                                value_constructor,
                                context,
                                fold_kind_binder,
                                fold_con_binder,
                            ),
                        )
                    })
                    .collect();
                Located::new(
                    Constructor::Record(Box::new(kind_mapped), pairs_mapped),
                    span,
                )
            }
            Constructor::Concat(left_constructor, right_constructor) => {
                let left_mapped = map_b(
                    *left_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let right_mapped = map_b(
                    *right_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::Concat(Box::new(left_mapped), Box::new(right_mapped)),
                    span,
                )
            }
            Constructor::Map(domain_kind, range_kind) => {
                let domain_mapped = kind_utilities::map_b(*domain_kind, context, fold_kind_binder);
                let range_mapped = kind_utilities::map_b(*range_kind, context, fold_kind_binder);
                Located::new(
                    Constructor::Map(Box::new(domain_mapped), Box::new(range_mapped)),
                    span,
                )
            }
            Constructor::Tuple(constructors) => {
                let constructors_mapped: Vec<LocatedConstructor> = constructors
                    .into_iter()
                    .map(|constructor_item| {
                        map_b(constructor_item, context, fold_kind_binder, fold_con_binder)
                    })
                    .collect();
                Located::new(Constructor::Tuple(constructors_mapped), span)
            }
            Constructor::Proj(inner_constructor, projection_index) => {
                let inner_mapped = map_b(
                    *inner_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::Proj(Box::new(inner_mapped), projection_index),
                    span,
                )
            }
            // Solved unification variable: lift indices and recurse.
            Constructor::Unif(binder_count, span_inner, kind_state, state, reference) => {
                let known_constructor = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        CUnif::Known(known) => Some(*known.clone()),
                        CUnif::Unknown => None,
                    }
                };
                match known_constructor {
                    Some(known_constructor_value) => {
                        let lifted = mlift_con_in_con(binder_count, known_constructor_value);
                        map_b(lifted, context, fold_kind_binder, fold_con_binder)
                    }
                    None => Located::new(
                        Constructor::Unif(binder_count, span_inner, kind_state, state, reference),
                        span,
                    ),
                }
            }
        };
        fold_con_binder(context, mapped)
    }

    /// Fold over all sub-constructors (and sub-kinds), accumulating state.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to fold over.
    /// * `init` - Initial accumulator value.
    /// * `fold_kind` - Called for each kind; (kind, accumulator) → new accumulator.
    /// * `fold_con` - Called for each constructor; (constructor, accumulator) → new accumulator.
    ///
    /// # Returns
    ///
    /// The final accumulator after post-order traversal.
    pub fn fold<Accumulator>(
        constructor: &LocatedConstructor,
        init: Accumulator,
        fold_kind: &dyn Fn(&LocatedKind, Accumulator) -> Accumulator,
        fold_con: &dyn Fn(&LocatedConstructor, Accumulator) -> Accumulator,
    ) -> Accumulator {
        fold_b(
            constructor,
            &[],
            init,
            &|_context, kind, accumulator| fold_kind(kind, accumulator),
            &|_context, constructor_item, accumulator| fold_con(constructor_item, accumulator),
        )
    }

    /// Like `fold` but with binder context passed to callbacks.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to fold over.
    /// * `context` - Binder stack at this node.
    /// * `init` - Initial accumulator value.
    /// * `fold_kind_binder` - Called for each kind with (context, kind, accumulator).
    /// * `fold_con_binder` - Called for each constructor with (context, constructor, accumulator).
    ///
    /// # Returns
    ///
    /// The final accumulator after post-order traversal.
    pub fn fold_b<Accumulator>(
        constructor: &LocatedConstructor,
        context: &[Binder],
        init: Accumulator,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, Accumulator) -> Accumulator,
        fold_con_binder: &dyn Fn(&[Binder], &LocatedConstructor, Accumulator) -> Accumulator,
    ) -> Accumulator {
        let accumulator = fold_con_binder(context, constructor, init);
        match &constructor.node {
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::ModProj(_, _, _)
            | Constructor::Name(_)
            | Constructor::Unit
            | Constructor::Error => accumulator,

            Constructor::TFun(left_constructor, right_constructor)
            | Constructor::App(left_constructor, right_constructor)
            | Constructor::Concat(left_constructor, right_constructor) => {
                let accumulator = fold_b(
                    left_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                fold_b(
                    right_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::TRecord(inner_constructor) | Constructor::Proj(inner_constructor, _) => {
                fold_b(
                    inner_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }

            Constructor::TDisjoint(left_constructor, middle_constructor, right_constructor) => {
                let accumulator = fold_b(
                    left_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let accumulator = fold_b(
                    middle_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                fold_b(
                    right_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }

            Constructor::TCFun(_, variable_name, kind, body) => {
                let accumulator = fold_kind_binder(context, kind, accumulator);
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelC(variable_name.clone(), *kind.clone()));
                fold_b(
                    body,
                    &extended_context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::Abs(variable_name, kind, body) => {
                let accumulator = fold_kind_binder(context, kind, accumulator);
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelC(variable_name.clone(), *kind.clone()));
                fold_b(
                    body,
                    &extended_context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::KAbs(variable_name, body) | Constructor::TKFun(variable_name, body) => {
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelK(variable_name.clone()));
                fold_b(
                    body,
                    &extended_context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::KApp(constructor_part, kind_part) => {
                let accumulator = fold_b(
                    constructor_part,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                fold_kind_binder(context, kind_part, accumulator)
            }
            Constructor::Record(record_kind, key_value_pairs) => {
                let accumulator = fold_kind_binder(context, record_kind, accumulator);
                key_value_pairs.iter().fold(
                    accumulator,
                    |acc, (key_constructor, value_constructor)| {
                        let acc = fold_b(
                            key_constructor,
                            context,
                            acc,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        fold_b(
                            value_constructor,
                            context,
                            acc,
                            fold_kind_binder,
                            fold_con_binder,
                        )
                    },
                )
            }
            Constructor::Map(domain_kind, range_kind) => {
                let accumulator = fold_kind_binder(context, domain_kind, accumulator);
                fold_kind_binder(context, range_kind, accumulator)
            }
            Constructor::Tuple(constructors) => {
                constructors
                    .iter()
                    .fold(accumulator, |acc, constructor_item| {
                        fold_b(
                            constructor_item,
                            context,
                            acc,
                            fold_kind_binder,
                            fold_con_binder,
                        )
                    })
            }
            Constructor::Unif(binder_count, _, _, _, reference) => {
                let known_constructor = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        CUnif::Known(known) => Some(*known.clone()),
                        CUnif::Unknown => None,
                    }
                };
                match known_constructor {
                    Some(known_constructor_value) => {
                        let lifted = mlift_con_in_con(*binder_count, known_constructor_value);
                        fold_b(
                            &lifted,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                        )
                    }
                    None => accumulator,
                }
            }
        }
    }

    /// Check whether any sub-constructor (or sub-kind) satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to search.
    /// * `kind_predicate` - Returns true for a matching kind node.
    /// * `constructor_predicate` - Returns true for a matching constructor node.
    ///
    /// # Returns
    ///
    /// True if any node (or descendant of a solved unification variable) satisfies the predicate.
    pub fn exists(
        constructor: &LocatedConstructor,
        kind_predicate: &dyn Fn(&LocatedKind) -> bool,
        constructor_predicate: &dyn Fn(&LocatedConstructor) -> bool,
    ) -> bool {
        if constructor_predicate(constructor) {
            return true;
        }
        match &constructor.node {
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::ModProj(_, _, _)
            | Constructor::Name(_)
            | Constructor::Unit
            | Constructor::Error => false,

            Constructor::TFun(left_constructor, right_constructor)
            | Constructor::App(left_constructor, right_constructor)
            | Constructor::Concat(left_constructor, right_constructor) => {
                exists(left_constructor, kind_predicate, constructor_predicate)
                    || exists(right_constructor, kind_predicate, constructor_predicate)
            }
            Constructor::TRecord(inner_constructor) | Constructor::Proj(inner_constructor, _) => {
                exists(inner_constructor, kind_predicate, constructor_predicate)
            }

            Constructor::TDisjoint(left_constructor, middle_constructor, right_constructor) => {
                exists(left_constructor, kind_predicate, constructor_predicate)
                    || exists(middle_constructor, kind_predicate, constructor_predicate)
                    || exists(right_constructor, kind_predicate, constructor_predicate)
            }

            Constructor::TCFun(_, _, kind, body) | Constructor::Abs(_, kind, body) => {
                kind::exists(kind, kind_predicate)
                    || exists(body, kind_predicate, constructor_predicate)
            }
            Constructor::KAbs(_, body) | Constructor::TKFun(_, body) => {
                exists(body, kind_predicate, constructor_predicate)
            }
            Constructor::KApp(constructor_part, kind_part) => {
                exists(constructor_part, kind_predicate, constructor_predicate)
                    || kind::exists(kind_part, kind_predicate)
            }
            Constructor::Record(record_kind, key_value_pairs) => {
                kind::exists(record_kind, kind_predicate)
                    || key_value_pairs
                        .iter()
                        .any(|(key_constructor, value_constructor)| {
                            exists(key_constructor, kind_predicate, constructor_predicate)
                                || exists(value_constructor, kind_predicate, constructor_predicate)
                        })
            }
            Constructor::Map(domain_kind, range_kind) => {
                kind::exists(domain_kind, kind_predicate)
                    || kind::exists(range_kind, kind_predicate)
            }
            Constructor::Tuple(constructors) => constructors.iter().any(|constructor_item| {
                exists(constructor_item, kind_predicate, constructor_predicate)
            }),
            Constructor::Unif(binder_count, _, _, _, reference) => {
                let known_constructor = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    match &*guard {
                        CUnif::Known(known) => Some(*known.clone()),
                        CUnif::Unknown => None,
                    }
                };
                match known_constructor {
                    Some(known_constructor_value) => {
                        let lifted = mlift_con_in_con(*binder_count, known_constructor_value);
                        exists(&lifted, kind_predicate, constructor_predicate)
                    }
                    None => false,
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// exp module
// ---------------------------------------------------------------------------

pub mod exp {
    use super::con as con_utilities;
    use super::kind as kind_utilities;
    use super::*;

    /// Helper: maps a constructor using the expression binder context, without
    /// capturing `context: &mut Vec<Binder>` (avoids E0500/E0502).
    fn do_map_constructor(
        constructor: LocatedConstructor,
        expression_context: &[Binder],
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        con_utilities::map_b(
            constructor,
            &mut vec![],
            &|_local_context, kind| fold_kind_binder(expression_context, kind),
            &|_local_context, constructor_item| {
                fold_con_binder(expression_context, constructor_item)
            },
        )
    }

    /// Recursively maps over all sub-expressions (and embedded cons/kinds), post-order.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to map over.
    /// * `kind_mapper` - Called for each kind; returns the replacement.
    /// * `constructor_mapper` - Called for each constructor; returns the replacement.
    /// * `expression_mapper` - Called for each expression; returns the replacement.
    ///
    /// # Returns
    ///
    /// The expression tree with all nodes transformed.
    pub fn map(
        expression: LocatedExpression,
        kind_mapper: &dyn Fn(LocatedKind) -> LocatedKind,
        constructor_mapper: &dyn Fn(LocatedConstructor) -> LocatedConstructor,
        expression_mapper: &dyn Fn(LocatedExpression) -> LocatedExpression,
    ) -> LocatedExpression {
        map_b(
            expression,
            &mut vec![],
            &|_context, kind| kind_mapper(kind),
            &|_context, constructor| constructor_mapper(constructor),
            &|_context, expression_item| expression_mapper(expression_item),
        )
    }

    /// Like `map` but provides a binder context to the callbacks.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to map over.
    /// * `context` - Mutable binder stack; pushed/popped when entering/leaving binding forms.
    /// * `fold_kind_binder` / `fold_con_binder` / `fold_exp_binder` - Callbacks with binder context.
    ///
    /// # Returns
    ///
    /// The expression tree with all nodes transformed; final result passed through fold_exp_binder.
    pub fn map_b(
        expression: LocatedExpression,
        context: &mut Vec<Binder>,
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fold_exp_binder: &dyn Fn(&[Binder], LocatedExpression) -> LocatedExpression,
    ) -> LocatedExpression {
        let span = expression.span.clone();
        let mapped = match expression.node {
            Expression::Prim(primitive) => Located::new(Expression::Prim(primitive), span),
            Expression::Rel(de_bruijn_index) => {
                Located::new(Expression::Rel(de_bruijn_index), span)
            }
            Expression::Named(name_id) => Located::new(Expression::Named(name_id), span),
            Expression::ModProj(module_id, path, name) => {
                Located::new(Expression::ModProj(module_id, path, name), span)
            }
            Expression::Error => Located::new(Expression::Error, span),

            Expression::Hole(r) => Located::new(Expression::Hole(r), span),

            Expression::Unif(reference) => {
                let known_expression = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    guard.clone()
                };
                match known_expression {
                    Some(known_exp) => map_b(
                        known_exp,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    ),
                    None => Located::new(Expression::Unif(reference), span),
                }
            }

            Expression::App(left_expression, right_expression) => {
                let left_mapped = map_b(
                    *left_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let right_mapped = map_b(
                    *right_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                Located::new(
                    Expression::App(Box::new(left_mapped), Box::new(right_mapped)),
                    span,
                )
            }
            Expression::Abs(variable_name, domain, range, body) => {
                let domain_mapped =
                    do_map_constructor(domain.clone(), context, fold_kind_binder, fold_con_binder);
                let range_mapped =
                    do_map_constructor(range, context, fold_kind_binder, fold_con_binder);
                context.push(Binder::RelE(variable_name.clone(), domain));
                let body_mapped = map_b(
                    *body,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                context.pop();
                Located::new(
                    Expression::Abs(
                        variable_name,
                        domain_mapped,
                        range_mapped,
                        Box::new(body_mapped),
                    ),
                    span,
                )
            }
            Expression::CApp(expression_function, constructor_argument) => {
                let expression_mapped = map_b(
                    *expression_function,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let constructor_mapped = do_map_constructor(
                    constructor_argument,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Expression::CApp(Box::new(expression_mapped), constructor_mapped),
                    span,
                )
            }
            Expression::CAbs(explicitness, variable_name, kind, body) => {
                let kind_mapped = fold_kind_binder(context, *kind.clone());
                context.push(Binder::RelC(variable_name.clone(), *kind));
                let body_mapped = map_b(
                    *body,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                context.pop();
                Located::new(
                    Expression::CAbs(
                        explicitness,
                        variable_name,
                        Box::new(kind_mapped),
                        Box::new(body_mapped),
                    ),
                    span,
                )
            }
            Expression::KAbs(variable_name, body) => {
                context.push(Binder::RelK(variable_name.clone()));
                let body_mapped = map_b(
                    *body,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                context.pop();
                Located::new(Expression::KAbs(variable_name, Box::new(body_mapped)), span)
            }
            Expression::KApp(expression_function, kind_argument) => {
                let expression_mapped = map_b(
                    *expression_function,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let kind_mapped = fold_kind_binder(context, *kind_argument);
                Located::new(
                    Expression::KApp(Box::new(expression_mapped), Box::new(kind_mapped)),
                    span,
                )
            }
            Expression::Record(fields) => {
                let fields_mapped: Vec<(
                    LocatedConstructor,
                    LocatedExpression,
                    LocatedConstructor,
                )> = fields
                    .into_iter()
                    .map(|(field_name, value_expression, field_type)| {
                        (
                            do_map_constructor(
                                field_name,
                                context,
                                fold_kind_binder,
                                fold_con_binder,
                            ),
                            map_b(
                                value_expression,
                                context,
                                fold_kind_binder,
                                fold_con_binder,
                                fold_exp_binder,
                            ),
                            do_map_constructor(
                                field_type,
                                context,
                                fold_kind_binder,
                                fold_con_binder,
                            ),
                        )
                    })
                    .collect();
                Located::new(Expression::Record(fields_mapped), span)
            }
            Expression::Field(record_expression, field_constructor, field_meta) => {
                let record_mapped = map_b(
                    *record_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let field_mapped = do_map_constructor(
                    field_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let meta_mapped = FieldMeta {
                    field: do_map_constructor(
                        field_meta.field.clone(),
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                    rest: do_map_constructor(
                        field_meta.rest.clone(),
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::Field(Box::new(record_mapped), field_mapped, meta_mapped),
                    span,
                )
            }
            Expression::Concat(
                left_expression,
                left_constructor,
                right_expression,
                right_constructor,
            ) => {
                let left_exp_mapped = map_b(
                    *left_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let left_con_mapped = do_map_constructor(
                    left_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let right_exp_mapped = map_b(
                    *right_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let right_con_mapped = do_map_constructor(
                    right_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Expression::Concat(
                        Box::new(left_exp_mapped),
                        left_con_mapped,
                        Box::new(right_exp_mapped),
                        right_con_mapped,
                    ),
                    span,
                )
            }
            Expression::Cut(record_expression, field_constructor, field_meta) => {
                let record_mapped = map_b(
                    *record_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let field_mapped = do_map_constructor(
                    field_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let meta_mapped = FieldMeta {
                    field: do_map_constructor(
                        field_meta.field.clone(),
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                    rest: do_map_constructor(
                        field_meta.rest.clone(),
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::Cut(Box::new(record_mapped), field_mapped, meta_mapped),
                    span,
                )
            }
            Expression::CutMulti(record_expression, field_constructor, rest_meta) => {
                let record_mapped = map_b(
                    *record_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let field_mapped = do_map_constructor(
                    field_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let meta_mapped = RestMeta {
                    rest: do_map_constructor(
                        rest_meta.rest.clone(),
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::CutMulti(Box::new(record_mapped), field_mapped, meta_mapped),
                    span,
                )
            }
            Expression::Case(discriminand, arms, case_meta) => {
                let discriminand_mapped = map_b(
                    *discriminand,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let arms_mapped: Vec<(LocatedPattern, LocatedExpression)> = arms
                    .into_iter()
                    .map(|(pattern, arm_expression)| {
                        let pattern_mapped =
                            map_pattern(pattern, context, fold_kind_binder, fold_con_binder);
                        let arm_binders = pattern_binders(&pattern_mapped);
                        for binder in &arm_binders {
                            context.push(binder.clone());
                        }
                        let arm_expression_mapped = map_b(
                            arm_expression,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        );
                        for _ in &arm_binders {
                            context.pop();
                        }
                        (pattern_mapped, arm_expression_mapped)
                    })
                    .collect();
                let meta_mapped = CaseMeta {
                    disc: do_map_constructor(
                        case_meta.disc.clone(),
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                    result: do_map_constructor(
                        case_meta.result.clone(),
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::Case(Box::new(discriminand_mapped), arms_mapped, meta_mapped),
                    span,
                )
            }
            Expression::Let(declarations, body, body_type) => {
                let (declarations_mapped, context_depth) = map_expression_declarations(
                    declarations,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let body_mapped = map_b(
                    *body,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let body_type_mapped =
                    do_map_constructor(body_type, context, fold_kind_binder, fold_con_binder);
                // Pop the binders added for ValRec (doVars-style).
                for _ in 0..context_depth {
                    context.pop();
                }
                Located::new(
                    Expression::Let(declarations_mapped, Box::new(body_mapped), body_type_mapped),
                    span,
                )
            }
        };
        fold_exp_binder(context, mapped)
    }

    /// Maps a list of `EDecl`s, pushing binders as we go.
    ///
    /// Returns the mapped declarations and the number of binders pushed (to pop after).
    fn map_expression_declarations(
        declarations: Vec<LocatedElaboratedDeclaration>,
        context: &mut Vec<Binder>,
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fold_exp_binder: &dyn Fn(&[Binder], LocatedExpression) -> LocatedExpression,
    ) -> (Vec<LocatedElaboratedDeclaration>, usize) {
        let mut result = Vec::with_capacity(declarations.len());
        let mut pushed_count = 0usize;
        for declaration in declarations {
            let span = declaration.span.clone();
            let (mapped_node, new_binders) = match declaration.node {
                ElaboratedDeclaration::Val(pattern, pattern_type, expression) => {
                    let pattern_mapped =
                        map_pattern(pattern, context, fold_kind_binder, fold_con_binder);
                    let type_mapped = do_map_constructor(
                        pattern_type,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    );
                    let expression_mapped = map_b(
                        expression,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    );
                    let binders = pattern_binders(&pattern_mapped);
                    (
                        ElaboratedDeclaration::Val(pattern_mapped, type_mapped, expression_mapped),
                        binders,
                    )
                }
                ElaboratedDeclaration::ValRec(valrec_entries) => {
                    // First pass: push binders for all names.
                    let pre_binders: Vec<Binder> = valrec_entries
                        .iter()
                        .map(|(variable_name, variable_type, _)| {
                            Binder::RelE(variable_name.clone(), variable_type.clone())
                        })
                        .collect();
                    for binder in &pre_binders {
                        context.push(binder.clone());
                    }
                    pushed_count += pre_binders.len();
                    // Second pass: map each entry in the extended context.
                    let entries_mapped: Vec<(String, LocatedConstructor, LocatedExpression)> =
                        valrec_entries
                            .into_iter()
                            .map(|(variable_name, variable_type, expression)| {
                                let type_mapped = do_map_constructor(
                                    variable_type,
                                    context,
                                    fold_kind_binder,
                                    fold_con_binder,
                                );
                                let expression_mapped = map_b(
                                    expression,
                                    context,
                                    fold_kind_binder,
                                    fold_con_binder,
                                    fold_exp_binder,
                                );
                                (variable_name, type_mapped, expression_mapped)
                            })
                            .collect();
                    (ElaboratedDeclaration::ValRec(entries_mapped), vec![])
                }
            };
            // Push binders from Val patterns (not already pushed above).
            for binder in &new_binders {
                context.push(binder.clone());
            }
            pushed_count += new_binders.len();
            result.push(Located::new(mapped_node, span));
        }
        (result, pushed_count)
    }

    fn map_pattern(
        pattern: LocatedPattern,
        context: &mut Vec<Binder>,
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedPattern {
        let span = pattern.span.clone();
        let node = match pattern.node {
            Pattern::Var(variable_name, variable_type) => Pattern::Var(
                variable_name,
                do_map_constructor(variable_type, context, fold_kind_binder, fold_con_binder),
            ),
            Pattern::Prim(primitive) => Pattern::Prim(primitive),
            Pattern::Constructor(
                datatype_kind,
                pattern_constructor,
                constructor_args,
                sub_pattern,
            ) => {
                let args_mapped: Vec<LocatedConstructor> = constructor_args
                    .into_iter()
                    .map(|arg| do_map_constructor(arg, context, fold_kind_binder, fold_con_binder))
                    .collect();
                let sub_pattern_mapped = sub_pattern.map(|sub| {
                    Box::new(map_pattern(
                        *sub,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ))
                });
                Pattern::Constructor(
                    datatype_kind,
                    pattern_constructor,
                    args_mapped,
                    sub_pattern_mapped,
                )
            }
            Pattern::Record(record_fields) => {
                let fields_mapped: Vec<(String, LocatedPattern, LocatedConstructor)> =
                    record_fields
                        .into_iter()
                        .map(|(field_name, sub_pattern, field_type)| {
                            let sub_pattern_mapped = map_pattern(
                                sub_pattern,
                                context,
                                fold_kind_binder,
                                fold_con_binder,
                            );
                            let type_mapped = do_map_constructor(
                                field_type,
                                context,
                                fold_kind_binder,
                                fold_con_binder,
                            );
                            (field_name, sub_pattern_mapped, type_mapped)
                        })
                        .collect();
                Pattern::Record(fields_mapped)
            }
        };
        Located::new(node, span)
    }

    fn pattern_binders(pattern: &LocatedPattern) -> Vec<Binder> {
        let mut binders = Vec::new();
        collect_pattern_binders(pattern, &mut binders);
        binders
    }

    fn collect_pattern_binders(pattern: &LocatedPattern, binders: &mut Vec<Binder>) {
        match &pattern.node {
            Pattern::Var(variable_name, variable_type) => {
                binders.push(Binder::RelE(variable_name.clone(), variable_type.clone()))
            }
            Pattern::Prim(_) => {}
            Pattern::Constructor(_, _, _, None) => {}
            Pattern::Constructor(_, _, _, Some(sub_pattern)) => {
                collect_pattern_binders(sub_pattern, binders)
            }
            Pattern::Record(record_fields) => {
                for (_, sub_pattern, _) in record_fields {
                    collect_pattern_binders(sub_pattern, binders);
                }
            }
        }
    }

    /// Fold over all sub-expressions (and embedded cons/kinds), accumulating state.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to fold over.
    /// * `init` - Initial accumulator value.
    /// * `fold_kind` / `fold_con` / `fold_exp` - Callbacks for kind, constructor, expression.
    ///
    /// # Returns
    ///
    /// The final accumulator after post-order traversal.
    pub fn fold<Accumulator>(
        expression: &LocatedExpression,
        init: Accumulator,
        fold_kind: &dyn Fn(&LocatedKind, Accumulator) -> Accumulator,
        fold_con: &dyn Fn(&LocatedConstructor, Accumulator) -> Accumulator,
        fold_exp: &dyn Fn(&LocatedExpression, Accumulator) -> Accumulator,
    ) -> Accumulator {
        fold_b(
            expression,
            &[],
            init,
            &|_context, kind, acc| fold_kind(kind, acc),
            &|_context, constructor, acc| fold_con(constructor, acc),
            &|_context, expression_item, acc| fold_exp(expression_item, acc),
        )
    }

    /// Like `fold` but with binder context passed to callbacks.
    pub fn fold_b<Accumulator>(
        expression: &LocatedExpression,
        context: &[Binder],
        init: Accumulator,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, Accumulator) -> Accumulator,
        fold_con_binder: &dyn Fn(&[Binder], &LocatedConstructor, Accumulator) -> Accumulator,
        fold_exp_binder: &dyn Fn(&[Binder], &LocatedExpression, Accumulator) -> Accumulator,
    ) -> Accumulator {
        let accumulator = fold_exp_binder(context, expression, init);
        match &expression.node {
            Expression::Prim(_)
            | Expression::Rel(_)
            | Expression::Named(_)
            | Expression::ModProj(_, _, _)
            | Expression::Error
            | Expression::Hole(_) => accumulator,

            Expression::Unif(reference) => {
                let known_expression = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    guard.clone()
                };
                match known_expression {
                    Some(known_exp) => fold_b(
                        &known_exp,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    ),
                    None => accumulator,
                }
            }

            Expression::App(left_expression, right_expression) => {
                let accumulator = fold_b(
                    left_expression,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                fold_b(
                    right_expression,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::Abs(variable_name, domain, range, body) => {
                let accumulator = con_utilities::fold_b(
                    domain,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let accumulator = con_utilities::fold_b(
                    range,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelE(variable_name.clone(), domain.clone()));
                fold_b(
                    body,
                    &extended_context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::CApp(expression_function, constructor_argument) => {
                let accumulator = fold_b(
                    expression_function,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                con_utilities::fold_b(
                    constructor_argument,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::CAbs(_, variable_name, kind, body) => {
                let accumulator = fold_kind_binder(context, kind, accumulator);
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelC(variable_name.clone(), *kind.clone()));
                fold_b(
                    body,
                    &extended_context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::KAbs(variable_name, body) => {
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelK(variable_name.clone()));
                fold_b(
                    body,
                    &extended_context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::KApp(expression_function, kind_argument) => {
                let accumulator = fold_b(
                    expression_function,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                fold_kind_binder(context, kind_argument, accumulator)
            }
            Expression::Record(fields) => fields.iter().fold(
                accumulator,
                |acc, (field_name, value_expression, field_type)| {
                    let acc = con_utilities::fold_b(
                        field_name,
                        context,
                        acc,
                        fold_kind_binder,
                        fold_con_binder,
                    );
                    let acc = fold_b(
                        value_expression,
                        context,
                        acc,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    );
                    con_utilities::fold_b(
                        field_type,
                        context,
                        acc,
                        fold_kind_binder,
                        fold_con_binder,
                    )
                },
            ),
            Expression::Field(record_expression, field_constructor, field_meta) => {
                let accumulator = fold_b(
                    record_expression,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let accumulator = con_utilities::fold_b(
                    field_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let accumulator = con_utilities::fold_b(
                    &field_meta.field,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                con_utilities::fold_b(
                    &field_meta.rest,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::Concat(
                left_expression,
                left_constructor,
                right_expression,
                right_constructor,
            ) => {
                let accumulator = fold_b(
                    left_expression,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let accumulator = con_utilities::fold_b(
                    left_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let accumulator = fold_b(
                    right_expression,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                con_utilities::fold_b(
                    right_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::Cut(record_expression, field_constructor, field_meta) => {
                let accumulator = fold_b(
                    record_expression,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let accumulator = con_utilities::fold_b(
                    field_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let accumulator = con_utilities::fold_b(
                    &field_meta.field,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                con_utilities::fold_b(
                    &field_meta.rest,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::CutMulti(record_expression, field_constructor, rest_meta) => {
                let accumulator = fold_b(
                    record_expression,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let accumulator = con_utilities::fold_b(
                    field_constructor,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                con_utilities::fold_b(
                    &rest_meta.rest,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::Case(discriminand, arms, case_meta) => {
                let accumulator = fold_b(
                    discriminand,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let accumulator =
                    arms.iter()
                        .fold(accumulator, |acc, (pattern, arm_expression)| {
                            let acc = fold_pattern(
                                pattern,
                                context,
                                acc,
                                fold_kind_binder,
                                fold_con_binder,
                            );
                            let mut extended_context = context.to_vec();
                            collect_pattern_binders_for_fold(pattern, &mut extended_context);
                            fold_b(
                                arm_expression,
                                &extended_context,
                                acc,
                                fold_kind_binder,
                                fold_con_binder,
                                fold_exp_binder,
                            )
                        });
                let accumulator = con_utilities::fold_b(
                    &case_meta.disc,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                );
                con_utilities::fold_b(
                    &case_meta.result,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::Let(declarations, body, body_type) => {
                let (accumulator, context_extension) = fold_expression_declarations(
                    declarations,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let mut extended_context = context.to_vec();
                extended_context.extend(context_extension);
                let accumulator = fold_b(
                    body,
                    &extended_context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                con_utilities::fold_b(
                    body_type,
                    context,
                    accumulator,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
        }
    }

    /// Folds over expression declarations, accumulating binder context.
    fn fold_expression_declarations<Accumulator>(
        declarations: &[LocatedElaboratedDeclaration],
        context: &[Binder],
        init: Accumulator,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, Accumulator) -> Accumulator,
        fold_con_binder: &dyn Fn(&[Binder], &LocatedConstructor, Accumulator) -> Accumulator,
        fold_exp_binder: &dyn Fn(&[Binder], &LocatedExpression, Accumulator) -> Accumulator,
    ) -> (Accumulator, Vec<Binder>) {
        let mut accumulator = init;
        let mut context_extension: Vec<Binder> = Vec::new();
        for declaration in declarations {
            let current_context: Vec<Binder> = context
                .iter()
                .chain(context_extension.iter())
                .cloned()
                .collect();
            match &declaration.node {
                ElaboratedDeclaration::Val(pattern, pattern_type, expression) => {
                    accumulator = con_utilities::fold_b(
                        pattern_type,
                        &current_context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                    );
                    accumulator = fold_b(
                        expression,
                        &current_context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    );
                    collect_pattern_binders_for_fold(pattern, &mut context_extension);
                }
                ElaboratedDeclaration::ValRec(valrec_entries) => {
                    // Push all names first, then fold each body.
                    let rec_binders: Vec<Binder> = valrec_entries
                        .iter()
                        .map(|(variable_name, variable_type, _)| {
                            Binder::RelE(variable_name.clone(), variable_type.clone())
                        })
                        .collect();
                    context_extension.extend(rec_binders);
                    let rec_context: Vec<Binder> = context
                        .iter()
                        .chain(context_extension.iter())
                        .cloned()
                        .collect();
                    for (_, variable_type, expression) in valrec_entries {
                        accumulator = con_utilities::fold_b(
                            variable_type,
                            &rec_context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        accumulator = fold_b(
                            expression,
                            &rec_context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        );
                    }
                }
            }
        }
        (accumulator, context_extension)
    }

    fn fold_pattern<Accumulator>(
        pattern: &LocatedPattern,
        context: &[Binder],
        init: Accumulator,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, Accumulator) -> Accumulator,
        fold_con_binder: &dyn Fn(&[Binder], &LocatedConstructor, Accumulator) -> Accumulator,
    ) -> Accumulator {
        match &pattern.node {
            Pattern::Var(_, variable_type) => con_utilities::fold_b(
                variable_type,
                context,
                init,
                fold_kind_binder,
                fold_con_binder,
            ),
            Pattern::Prim(_) => init,
            Pattern::Constructor(_, _, constructor_args, sub_pattern) => {
                let accumulator = constructor_args.iter().fold(init, |acc, constructor_arg| {
                    con_utilities::fold_b(
                        constructor_arg,
                        context,
                        acc,
                        fold_kind_binder,
                        fold_con_binder,
                    )
                });
                match sub_pattern {
                    None => accumulator,
                    Some(sub) => {
                        fold_pattern(sub, context, accumulator, fold_kind_binder, fold_con_binder)
                    }
                }
            }
            Pattern::Record(record_fields) => {
                record_fields
                    .iter()
                    .fold(init, |acc, (_, sub_pattern, field_type)| {
                        let acc = fold_pattern(
                            sub_pattern,
                            context,
                            acc,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        con_utilities::fold_b(
                            field_type,
                            context,
                            acc,
                            fold_kind_binder,
                            fold_con_binder,
                        )
                    })
            }
        }
    }

    fn collect_pattern_binders_for_fold(pattern: &LocatedPattern, binders_out: &mut Vec<Binder>) {
        match &pattern.node {
            Pattern::Var(variable_name, variable_type) => {
                binders_out.push(Binder::RelE(variable_name.clone(), variable_type.clone()))
            }
            Pattern::Prim(_) => {}
            Pattern::Constructor(_, _, _, None) => {}
            Pattern::Constructor(_, _, _, Some(sub_pattern)) => {
                collect_pattern_binders_for_fold(sub_pattern, binders_out)
            }
            Pattern::Record(record_fields) => {
                for (_, sub_pattern, _) in record_fields {
                    collect_pattern_binders_for_fold(sub_pattern, binders_out);
                }
            }
        }
    }

    /// Check whether any sub-expression (or embedded con/kind) satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to search.
    /// * `kind_predicate` / `constructor_predicate` / `expression_predicate` - Predicates for each node type.
    ///
    /// # Returns
    ///
    /// True if any node (or descendant of a solved unification variable) satisfies the predicate.
    pub fn exists(
        expression: &LocatedExpression,
        kind_predicate: &dyn Fn(&LocatedKind) -> bool,
        constructor_predicate: &dyn Fn(&LocatedConstructor) -> bool,
        expression_predicate: &dyn Fn(&LocatedExpression) -> bool,
    ) -> bool {
        if expression_predicate(expression) {
            return true;
        }
        match &expression.node {
            Expression::Prim(_)
            | Expression::Rel(_)
            | Expression::Named(_)
            | Expression::ModProj(_, _, _)
            | Expression::Error
            | Expression::Hole(_) => false,

            Expression::Unif(reference) => {
                let known_expression = {
                    let guard = crate::compiler_diagnostics::lock_for_compile(
                        reference.as_ref(),
                        "elaborated utilities unification cell",
                    );
                    guard.clone()
                };
                match known_expression {
                    Some(known_exp) => exists(
                        &known_exp,
                        kind_predicate,
                        constructor_predicate,
                        expression_predicate,
                    ),
                    None => false,
                }
            }

            Expression::App(left_expression, right_expression) => {
                exists(
                    left_expression,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || exists(
                    right_expression,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                )
            }
            Expression::Abs(_, domain, range, body) => {
                con_utilities::exists(domain, kind_predicate, constructor_predicate)
                    || con_utilities::exists(range, kind_predicate, constructor_predicate)
                    || exists(
                        body,
                        kind_predicate,
                        constructor_predicate,
                        expression_predicate,
                    )
            }
            Expression::CApp(expression_function, constructor_argument) => {
                exists(
                    expression_function,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || con_utilities::exists(
                    constructor_argument,
                    kind_predicate,
                    constructor_predicate,
                )
            }
            Expression::CAbs(_, _, kind, body) => {
                kind::exists(kind, kind_predicate)
                    || exists(
                        body,
                        kind_predicate,
                        constructor_predicate,
                        expression_predicate,
                    )
            }
            Expression::KAbs(_, body) => exists(
                body,
                kind_predicate,
                constructor_predicate,
                expression_predicate,
            ),
            Expression::KApp(expression_function, kind_argument) => {
                exists(
                    expression_function,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || kind::exists(kind_argument, kind_predicate)
            }
            Expression::Record(fields) => {
                fields
                    .iter()
                    .any(|(field_name, value_expression, field_type)| {
                        con_utilities::exists(field_name, kind_predicate, constructor_predicate)
                            || exists(
                                value_expression,
                                kind_predicate,
                                constructor_predicate,
                                expression_predicate,
                            )
                            || con_utilities::exists(
                                field_type,
                                kind_predicate,
                                constructor_predicate,
                            )
                    })
            }
            Expression::Field(record_expression, field_constructor, field_meta) => {
                exists(
                    record_expression,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || con_utilities::exists(field_constructor, kind_predicate, constructor_predicate)
                    || con_utilities::exists(
                        &field_meta.field,
                        kind_predicate,
                        constructor_predicate,
                    )
                    || con_utilities::exists(
                        &field_meta.rest,
                        kind_predicate,
                        constructor_predicate,
                    )
            }
            Expression::Concat(
                left_expression,
                left_constructor,
                right_expression,
                right_constructor,
            ) => {
                exists(
                    left_expression,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || con_utilities::exists(left_constructor, kind_predicate, constructor_predicate)
                    || exists(
                        right_expression,
                        kind_predicate,
                        constructor_predicate,
                        expression_predicate,
                    )
                    || con_utilities::exists(
                        right_constructor,
                        kind_predicate,
                        constructor_predicate,
                    )
            }
            Expression::Cut(record_expression, field_constructor, field_meta) => {
                exists(
                    record_expression,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || con_utilities::exists(field_constructor, kind_predicate, constructor_predicate)
                    || con_utilities::exists(
                        &field_meta.field,
                        kind_predicate,
                        constructor_predicate,
                    )
                    || con_utilities::exists(
                        &field_meta.rest,
                        kind_predicate,
                        constructor_predicate,
                    )
            }
            Expression::CutMulti(record_expression, field_constructor, rest_meta) => {
                exists(
                    record_expression,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || con_utilities::exists(field_constructor, kind_predicate, constructor_predicate)
                    || con_utilities::exists(&rest_meta.rest, kind_predicate, constructor_predicate)
            }
            Expression::Case(discriminand, arms, case_meta) => {
                exists(
                    discriminand,
                    kind_predicate,
                    constructor_predicate,
                    expression_predicate,
                ) || arms.iter().any(|(_, arm_expression)| {
                    exists(
                        arm_expression,
                        kind_predicate,
                        constructor_predicate,
                        expression_predicate,
                    )
                }) || con_utilities::exists(&case_meta.disc, kind_predicate, constructor_predicate)
                    || con_utilities::exists(
                        &case_meta.result,
                        kind_predicate,
                        constructor_predicate,
                    )
            }
            Expression::Let(declarations, body, body_type) => {
                declarations
                    .iter()
                    .any(|declaration| match &declaration.node {
                        ElaboratedDeclaration::Val(pattern, declaration_type, expression) => {
                            exists_pattern(pattern, kind_predicate, constructor_predicate)
                                || con_utilities::exists(
                                    declaration_type,
                                    kind_predicate,
                                    constructor_predicate,
                                )
                                || exists(
                                    expression,
                                    kind_predicate,
                                    constructor_predicate,
                                    expression_predicate,
                                )
                        }
                        ElaboratedDeclaration::ValRec(valrec_entries) => {
                            valrec_entries.iter().any(|(_, entry_type, expression)| {
                                con_utilities::exists(
                                    entry_type,
                                    kind_predicate,
                                    constructor_predicate,
                                ) || exists(
                                    expression,
                                    kind_predicate,
                                    constructor_predicate,
                                    expression_predicate,
                                )
                            })
                        }
                    })
                    || exists(
                        body,
                        kind_predicate,
                        constructor_predicate,
                        expression_predicate,
                    )
                    || con_utilities::exists(body_type, kind_predicate, constructor_predicate)
            }
        }
    }

    fn exists_pattern(
        pattern: &LocatedPattern,
        kind_predicate: &dyn Fn(&LocatedKind) -> bool,
        constructor_predicate: &dyn Fn(&LocatedConstructor) -> bool,
    ) -> bool {
        match &pattern.node {
            Pattern::Var(_, variable_type) => {
                con_utilities::exists(variable_type, kind_predicate, constructor_predicate)
            }
            Pattern::Prim(_) => false,
            Pattern::Constructor(_, _, constructor_args, sub_pattern) => {
                constructor_args.iter().any(|constructor_arg| {
                    con_utilities::exists(constructor_arg, kind_predicate, constructor_predicate)
                }) || sub_pattern
                    .as_ref()
                    .is_some_and(|sub| exists_pattern(sub, kind_predicate, constructor_predicate))
            }
            Pattern::Record(record_fields) => {
                record_fields.iter().any(|(_, sub_pattern, field_type)| {
                    exists_pattern(sub_pattern, kind_predicate, constructor_predicate)
                        || con_utilities::exists(field_type, kind_predicate, constructor_predicate)
                })
            }
        }
    }
}

// ---------------------------------------------------------------------------
// sgn module
// ---------------------------------------------------------------------------

pub mod sgn {
    use super::con as con_utilities;
    use super::kind as kutil;
    use super::*;

    /// Helper: maps a constructor in signature context (avoids capturing context).
    fn do_map_constructor(
        constructor: LocatedConstructor,
        signature_context: &[Binder],
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        con_utilities::map_b(
            constructor,
            &mut vec![],
            &|_local_context, kind| fold_kind_binder(signature_context, kind),
            &|_local_context, constructor_item| {
                fold_con_binder(signature_context, constructor_item)
            },
        )
    }

    fn do_map_kind(
        kind: LocatedKind,
        signature_context: &[Binder],
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
    ) -> LocatedKind {
        kutil::map_b(kind, &mut vec![], &|_local_context, kind_item| {
            fold_kind_binder(signature_context, kind_item)
        })
    }

    /// Recursively maps over a signature (post-order).
    ///
    /// # Arguments
    ///
    /// * `signature` - The signature tree to map over.
    /// * `kind_mapper` / `constructor_mapper` / `signature_mapper` - Callbacks for each node type.
    pub fn map(
        signature: LocatedSignature,
        kind_mapper: &dyn Fn(LocatedKind) -> LocatedKind,
        constructor_mapper: &dyn Fn(LocatedConstructor) -> LocatedConstructor,
        signature_mapper: &dyn Fn(LocatedSignature) -> LocatedSignature,
    ) -> LocatedSignature {
        map_b(
            signature,
            &mut vec![],
            &|_context, kind| kind_mapper(kind),
            &|_context, constructor| constructor_mapper(constructor),
            &|_context, signature_item| signature_mapper(signature_item),
        )
    }

    /// Like `map` but with binder context.
    pub fn map_b(
        signature: LocatedSignature,
        context: &mut Vec<Binder>,
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fc_b: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fs_b: &dyn Fn(&[Binder], LocatedSignature) -> LocatedSignature,
    ) -> LocatedSignature {
        let span = signature.span.clone();
        let mapped = match signature.node {
            Signature::Var(name_id) => Located::new(Signature::Var(name_id), span),
            Signature::Proj(module_id, path, name) => {
                Located::new(Signature::Proj(module_id, path, name), span)
            }
            Signature::Error => Located::new(Signature::Error, span),

            Signature::Const(items) => {
                let mut items_out = Vec::with_capacity(items.len());
                for item in items {
                    // Push context binder for this item before processing subsequent items.
                    let extra_binder = sgn_item_binder(&item, span.clone());
                    let item_mapped = map_sgn_item(item, context, fk_b, fc_b, fs_b);
                    items_out.push(item_mapped);
                    if let Some(binder) = extra_binder {
                        context.push(binder);
                    }
                }
                Located::new(Signature::Const(items_out), span)
            }
            Signature::Fun(module_id, name_id, domain, range) => {
                let domain_mapped = map_b(*domain, context, fk_b, fc_b, fs_b);
                // The domain's module-name is in scope for the range.
                let range_mapped = map_b(*range, context, fk_b, fc_b, fs_b);
                Located::new(
                    Signature::Fun(
                        module_id,
                        name_id,
                        Box::new(domain_mapped),
                        Box::new(range_mapped),
                    ),
                    span,
                )
            }
            Signature::Where(inner, path, name, constructor) => {
                let inner_mapped = map_b(*inner, context, fk_b, fc_b, fs_b);
                let constructor_mapped = do_map_constructor(constructor, context, fk_b, fc_b);
                Located::new(
                    Signature::Where(Box::new(inner_mapped), path, name, constructor_mapped),
                    span,
                )
            }
        };
        fs_b(context, mapped)
    }

    fn map_sgn_item(
        item: LocatedSignatureItem,
        context: &mut Vec<Binder>,
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fc_b: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fs_b: &dyn Fn(&[Binder], LocatedSignature) -> LocatedSignature,
    ) -> LocatedSignatureItem {
        let span = item.span.clone();
        let node = match item.node {
            SignatureItem::ConAbs(variable_name, name_id, kind) => {
                let kind_mapped = do_map_kind(kind, context, fk_b);
                SignatureItem::ConAbs(variable_name, name_id, kind_mapped)
            }
            SignatureItem::Constructor(variable_name, name_id, kind, constructor) => {
                let kind_mapped = do_map_kind(kind, context, fk_b);
                let constructor_mapped = do_map_constructor(constructor, context, fk_b, fc_b);
                SignatureItem::Constructor(variable_name, name_id, kind_mapped, constructor_mapped)
            }
            SignatureItem::Datatype(datatype_decls) => {
                let decls_mapped: Vec<DatatypeDecl> = datatype_decls
                    .into_iter()
                    .map(|decl| DatatypeDecl {
                        name: decl.name,
                        id: decl.id,
                        params: decl.params,
                        constrs: decl
                            .constrs
                            .into_iter()
                            .map(|(variable_name, name_id, optional_con)| {
                                (
                                    variable_name,
                                    name_id,
                                    optional_con.map(|constructor| {
                                        do_map_constructor(constructor, context, fk_b, fc_b)
                                    }),
                                )
                            })
                            .collect(),
                    })
                    .collect();
                SignatureItem::Datatype(decls_mapped)
            }
            SignatureItem::DatatypeImp {
                name,
                id,
                orig_mod,
                orig_path,
                orig_name,
                orig_constrs_path,
                constrs,
            } => {
                let constrs_mapped: Vec<(String, usize, Option<LocatedConstructor>)> = constrs
                    .into_iter()
                    .map(|(variable_name, name_id, optional_con)| {
                        (
                            variable_name,
                            name_id,
                            optional_con.map(|constructor| {
                                do_map_constructor(constructor, context, fk_b, fc_b)
                            }),
                        )
                    })
                    .collect();
                SignatureItem::DatatypeImp {
                    name,
                    id,
                    orig_mod,
                    orig_path,
                    orig_name,
                    orig_constrs_path,
                    constrs: constrs_mapped,
                }
            }
            SignatureItem::Val(variable_name, name_id, constructor) => {
                let constructor_mapped = do_map_constructor(constructor, context, fk_b, fc_b);
                SignatureItem::Val(variable_name, name_id, constructor_mapped)
            }
            SignatureItem::Structure(interface_module, variable_name, name_id, inner_signature) => {
                let signature_mapped = map_b(inner_signature, context, fk_b, fc_b, fs_b);
                SignatureItem::Structure(interface_module, variable_name, name_id, signature_mapped)
            }
            SignatureItem::Signature(variable_name, name_id, inner_signature) => {
                let signature_mapped = map_b(inner_signature, context, fk_b, fc_b, fs_b);
                SignatureItem::Signature(variable_name, name_id, signature_mapped)
            }
            SignatureItem::Constraint(left_constructor, right_constructor) => {
                let left_mapped = do_map_constructor(left_constructor, context, fk_b, fc_b);
                let right_mapped = do_map_constructor(right_constructor, context, fk_b, fc_b);
                SignatureItem::Constraint(left_mapped, right_mapped)
            }
            SignatureItem::ClassAbs(variable_name, name_id, kind) => {
                let kind_mapped = do_map_kind(kind, context, fk_b);
                SignatureItem::ClassAbs(variable_name, name_id, kind_mapped)
            }
            SignatureItem::Class(variable_name, name_id, kind, constructor) => {
                let kind_mapped = do_map_kind(kind, context, fk_b);
                let constructor_mapped = do_map_constructor(constructor, context, fk_b, fc_b);
                SignatureItem::Class(variable_name, name_id, kind_mapped, constructor_mapped)
            }
        };
        Located::new(node, span)
    }

    /// Compute the binder introduced by a signature item, if any.
    fn sgn_item_binder(
        item: &LocatedSignatureItem,
        loc: crate::error_types::Span,
    ) -> Option<Binder> {
        match &item.node {
            SignatureItem::ConAbs(x, n, k) => Some(Binder::NamedC(x.clone(), *n, k.clone(), None)),
            SignatureItem::Constructor(x, n, k, c) => {
                Some(Binder::NamedC(x.clone(), *n, k.clone(), Some(c.clone())))
            }
            SignatureItem::Datatype(_) => None, // Multiple binders; handled by caller if needed.
            SignatureItem::DatatypeImp { .. } => None,
            SignatureItem::Val(_, _, _) => None,
            SignatureItem::Structure(_, _, _, _) => None,
            SignatureItem::Signature(_, _, _) => None,
            SignatureItem::Constraint(_, _) => None,
            SignatureItem::ClassAbs(x, n, k) => {
                // ClassAbs introduces kind k -> Type
                let arr_span = loc;
                let k_type = Located::new(Kind::Type, arr_span.clone());
                let k_arr =
                    Located::new(Kind::Arrow(Box::new(k.clone()), Box::new(k_type)), arr_span);
                Some(Binder::NamedC(x.clone(), *n, k_arr, None))
            }
            SignatureItem::Class(x, n, k, c) => {
                let arr_span = loc;
                let k_type = Located::new(Kind::Type, arr_span.clone());
                let k_arr =
                    Located::new(Kind::Arrow(Box::new(k.clone()), Box::new(k_type)), arr_span);
                Some(Binder::NamedC(x.clone(), *n, k_arr, Some(c.clone())))
            }
        }
    }

    /// Fold over a signature.
    pub fn fold<S>(
        s: &LocatedSignature,
        init: S,
        fk: &dyn Fn(&LocatedKind, S) -> S,
        fc: &dyn Fn(&LocatedConstructor, S) -> S,
        fs: &dyn Fn(&LocatedSignature, S) -> S,
    ) -> S {
        fold_b(
            s,
            &[],
            init,
            &|_ctx, k, s| fk(k, s),
            &|_ctx, c, s| fc(c, s),
            &|_ctx, sg, s| fs(sg, s),
        )
    }

    pub fn fold_b<S>(
        sgn: &LocatedSignature,
        ctx: &[Binder],
        init: S,
        fk_b: &dyn Fn(&[Binder], &LocatedKind, S) -> S,
        fc_b: &dyn Fn(&[Binder], &LocatedConstructor, S) -> S,
        fs_b: &dyn Fn(&[Binder], &LocatedSignature, S) -> S,
    ) -> S {
        fold_b_inner(sgn, ctx, init, fk_b, fc_b, fs_b)
    }

    fn fold_b_inner<S>(
        s: &LocatedSignature,
        ctx: &[Binder],
        init: S,
        fk_b: &dyn Fn(&[Binder], &LocatedKind, S) -> S,
        fc_b: &dyn Fn(&[Binder], &LocatedConstructor, S) -> S,
        fs_b: &dyn Fn(&[Binder], &LocatedSignature, S) -> S,
    ) -> S {
        let st = fs_b(ctx, s, init);
        match &s.node {
            Signature::Var(_) | Signature::Proj(_, _, _) | Signature::Error => st,
            Signature::Const(items) => {
                let mut s = st;
                let mut ctx2 = ctx.to_vec();
                for item in items {
                    s = fold_sgn_item(item, &ctx2, s, fk_b, fc_b, fs_b);
                    if let Some(b) = sgn_item_binder_ref(item) {
                        ctx2.push(b);
                    }
                }
                s
            }
            Signature::Fun(_, _, dom, ran) => {
                let s = fold_b_inner(dom, ctx, st, fk_b, fc_b, fs_b);
                fold_b_inner(ran, ctx, s, fk_b, fc_b, fs_b)
            }
            Signature::Where(inner, _, _, c) => {
                let s = fold_b_inner(inner, ctx, st, fk_b, fc_b, fs_b);
                con_utilities::fold_b(c, ctx, s, fk_b, fc_b)
            }
        }
    }

    fn fold_sgn_item<S>(
        item: &LocatedSignatureItem,
        ctx: &[Binder],
        init: S,
        fk_b: &dyn Fn(&[Binder], &LocatedKind, S) -> S,
        fc_b: &dyn Fn(&[Binder], &LocatedConstructor, S) -> S,
        fs_b: &dyn Fn(&[Binder], &LocatedSignature, S) -> S,
    ) -> S {
        match &item.node {
            SignatureItem::ConAbs(_, _, k) => kutil::fold_b(k, ctx, init, fk_b),
            SignatureItem::Constructor(_, _, k, c) => {
                let s = kutil::fold_b(k, ctx, init, fk_b);
                con_utilities::fold_b(c, ctx, s, fk_b, fc_b)
            }
            SignatureItem::Datatype(dts) => dts.iter().fold(init, |acc, dt| {
                dt.constrs.iter().fold(acc, |acc2, (_, _, co)| match co {
                    None => acc2,
                    Some(c) => con_utilities::fold_b(c, ctx, acc2, fk_b, fc_b),
                })
            }),
            SignatureItem::DatatypeImp { constrs, .. } => {
                constrs.iter().fold(init, |acc, (_, _, co)| match co {
                    None => acc,
                    Some(c) => con_utilities::fold_b(c, ctx, acc, fk_b, fc_b),
                })
            }
            SignatureItem::Val(_, _, c) => con_utilities::fold_b(c, ctx, init, fk_b, fc_b),
            SignatureItem::Structure(_, _, _, s) => fold_b_inner(s, ctx, init, fk_b, fc_b, fs_b),
            SignatureItem::Signature(_, _, s) => fold_b_inner(s, ctx, init, fk_b, fc_b, fs_b),
            SignatureItem::Constraint(c1, c2) => {
                let s = con_utilities::fold_b(c1, ctx, init, fk_b, fc_b);
                con_utilities::fold_b(c2, ctx, s, fk_b, fc_b)
            }
            SignatureItem::ClassAbs(_, _, k) => kutil::fold_b(k, ctx, init, fk_b),
            SignatureItem::Class(_, _, k, c) => {
                let s = kutil::fold_b(k, ctx, init, fk_b);
                con_utilities::fold_b(c, ctx, s, fk_b, fc_b)
            }
        }
    }

    fn sgn_item_binder_ref(item: &LocatedSignatureItem) -> Option<Binder> {
        match &item.node {
            SignatureItem::ConAbs(x, n, k) => Some(Binder::NamedC(x.clone(), *n, k.clone(), None)),
            SignatureItem::Constructor(x, n, k, c) => {
                Some(Binder::NamedC(x.clone(), *n, k.clone(), Some(c.clone())))
            }
            _ => None,
        }
    }

    /// Check whether any sub-node satisfies the predicate.
    pub fn exists(
        s: &LocatedSignature,
        fk: &dyn Fn(&LocatedKind) -> bool,
        fc: &dyn Fn(&LocatedConstructor) -> bool,
        fs: &dyn Fn(&LocatedSignature) -> bool,
    ) -> bool {
        if fs(s) {
            return true;
        }
        match &s.node {
            Signature::Var(_) | Signature::Proj(_, _, _) | Signature::Error => false,
            Signature::Const(items) => items.iter().any(|item| exists_sgn_item(item, fk, fc, fs)),
            Signature::Fun(_, _, dom, ran) => exists(dom, fk, fc, fs) || exists(ran, fk, fc, fs),
            Signature::Where(inner, _, _, c) => {
                exists(inner, fk, fc, fs) || con_utilities::exists(c, fk, fc)
            }
        }
    }

    fn exists_sgn_item(
        item: &LocatedSignatureItem,
        fk: &dyn Fn(&LocatedKind) -> bool,
        fc: &dyn Fn(&LocatedConstructor) -> bool,
        fs: &dyn Fn(&LocatedSignature) -> bool,
    ) -> bool {
        match &item.node {
            SignatureItem::ConAbs(_, _, k) => kind::exists(k, fk),
            SignatureItem::Constructor(_, _, k, c) => {
                kind::exists(k, fk) || con_utilities::exists(c, fk, fc)
            }
            SignatureItem::Datatype(dts) => dts.iter().any(|dt| {
                dt.constrs.iter().any(|(_, _, co)| {
                    co.as_ref()
                        .is_some_and(|c| con_utilities::exists(c, fk, fc))
                })
            }),
            SignatureItem::DatatypeImp { constrs, .. } => constrs.iter().any(|(_, _, co)| {
                co.as_ref()
                    .is_some_and(|c| con_utilities::exists(c, fk, fc))
            }),
            SignatureItem::Val(_, _, c) => con_utilities::exists(c, fk, fc),
            SignatureItem::Structure(_, _, _, s) | SignatureItem::Signature(_, _, s) => {
                exists(s, fk, fc, fs)
            }
            SignatureItem::Constraint(c1, c2) => {
                con_utilities::exists(c1, fk, fc) || con_utilities::exists(c2, fk, fc)
            }
            SignatureItem::ClassAbs(_, _, k) => kind::exists(k, fk),
            SignatureItem::Class(_, _, k, c) => {
                kind::exists(k, fk) || con_utilities::exists(c, fk, fc)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// decl module
// ---------------------------------------------------------------------------

pub mod decl {
    use super::con as con_utilities;
    use super::exp as eutil;
    use super::kind as kutil;
    use super::sgn as sutil;
    use super::*;

    // Helper: map a con in decl context.
    fn do_map_c(
        c: LocatedConstructor,
        d_ctx: &[Binder],
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fc_b: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        con_utilities::map_b(c, &mut vec![], &|_local, k| fk_b(d_ctx, k), &|_local, c| {
            fc_b(d_ctx, c)
        })
    }

    fn do_map_k(
        k: LocatedKind,
        d_ctx: &[Binder],
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
    ) -> LocatedKind {
        kutil::map_b(k, &mut vec![], &|_local, k| fk_b(d_ctx, k))
    }

    fn do_map_e(
        e: LocatedExpression,
        d_ctx: &[Binder],
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fc_b: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fe_b: &dyn Fn(&[Binder], LocatedExpression) -> LocatedExpression,
    ) -> LocatedExpression {
        eutil::map_b(
            e,
            &mut vec![],
            &|_local, k| fk_b(d_ctx, k),
            &|_local, c| fc_b(d_ctx, c),
            &|_local, e| fe_b(d_ctx, e),
        )
    }

    fn do_map_s(
        s: LocatedSignature,
        d_ctx: &[Binder],
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fc_b: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fs_b: &dyn Fn(&[Binder], LocatedSignature) -> LocatedSignature,
    ) -> LocatedSignature {
        sutil::map_b(
            s,
            &mut vec![],
            &|_local, k| fk_b(d_ctx, k),
            &|_local, c| fc_b(d_ctx, c),
            &|_local, s| fs_b(d_ctx, s),
        )
    }

    /// Recursively map over a declaration and its nested structures.
    pub fn map(
        d: LocatedDeclaration,
        fk: &dyn Fn(LocatedKind) -> LocatedKind,
        fc: &dyn Fn(LocatedConstructor) -> LocatedConstructor,
        fe: &dyn Fn(LocatedExpression) -> LocatedExpression,
        fs: &dyn Fn(LocatedSignature) -> LocatedSignature,
        fst: &dyn Fn(LocatedStructure) -> LocatedStructure,
        fd: &dyn Fn(LocatedDeclaration) -> LocatedDeclaration,
    ) -> LocatedDeclaration {
        map_b(
            d,
            &mut vec![],
            &|_ctx, k| fk(k),
            &|_ctx, c| fc(c),
            &|_ctx, e| fe(e),
            &|_ctx, s| fs(s),
            &|_ctx, st| fst(st),
            &|_ctx, d| fd(d),
        )
    }

    pub fn map_b(
        d: LocatedDeclaration,
        ctx: &mut Vec<Binder>,
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fc_b: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fe_b: &dyn Fn(&[Binder], LocatedExpression) -> LocatedExpression,
        fs_b: &dyn Fn(&[Binder], LocatedSignature) -> LocatedSignature,
        fst_b: &dyn Fn(&[Binder], LocatedStructure) -> LocatedStructure,
        fd_b: &dyn Fn(&[Binder], LocatedDeclaration) -> LocatedDeclaration,
    ) -> LocatedDeclaration {
        let span = d.span.clone();
        let mapped = match d.node {
            Declaration::Constructor(x, n, k, c) => {
                let km = do_map_k(k, ctx, fk_b);
                let cm = do_map_c(c, ctx, fk_b, fc_b);
                Located::new(Declaration::Constructor(x, n, km, cm), span)
            }
            Declaration::Datatype(dts) => {
                let dtsm: Vec<DatatypeDecl> = dts
                    .into_iter()
                    .map(|dt| DatatypeDecl {
                        name: dt.name,
                        id: dt.id,
                        params: dt.params,
                        constrs: dt
                            .constrs
                            .into_iter()
                            .map(|(x, n, co)| (x, n, co.map(|c| do_map_c(c, ctx, fk_b, fc_b))))
                            .collect(),
                    })
                    .collect();
                Located::new(Declaration::Datatype(dtsm), span)
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
                let constrs_m = constrs
                    .into_iter()
                    .map(|(x, n, co)| (x, n, co.map(|c| do_map_c(c, ctx, fk_b, fc_b))))
                    .collect();
                Located::new(
                    Declaration::DatatypeImp {
                        name,
                        id,
                        orig_mod,
                        orig_path,
                        orig_name,
                        orig_constrs_path,
                        constrs: constrs_m,
                    },
                    span,
                )
            }
            Declaration::Val(x, n, ty, e) => {
                let tym = do_map_c(ty, ctx, fk_b, fc_b);
                let em = do_map_e(e, ctx, fk_b, fc_b, fe_b);
                Located::new(Declaration::Val(x, n, tym, em), span)
            }
            Declaration::ValRec(vis) => {
                let vim: Vec<(String, usize, LocatedConstructor, LocatedExpression)> = vis
                    .into_iter()
                    .map(|(x, n, ty, e)| {
                        let tym = do_map_c(ty, ctx, fk_b, fc_b);
                        let em = do_map_e(e, ctx, fk_b, fc_b, fe_b);
                        (x, n, tym, em)
                    })
                    .collect();
                Located::new(Declaration::ValRec(vim), span)
            }
            Declaration::Signature(x, n, s) => {
                let sm = do_map_s(s, ctx, fk_b, fc_b, fs_b);
                Located::new(Declaration::Signature(x, n, sm), span)
            }
            Declaration::Structure(x, n, sgn, str) => {
                let sgnm = do_map_s(sgn, ctx, fk_b, fc_b, fs_b);
                let strm = map_str(str, ctx, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                Located::new(Declaration::Structure(x, n, sgnm, strm), span)
            }
            Declaration::FfiStr(x, n, sgn) => {
                let sgnm = do_map_s(sgn, ctx, fk_b, fc_b, fs_b);
                Located::new(Declaration::FfiStr(x, n, sgnm), span)
            }
            Declaration::Constraint(c1, c2) => {
                let c1m = do_map_c(c1, ctx, fk_b, fc_b);
                let c2m = do_map_c(c2, ctx, fk_b, fc_b);
                Located::new(Declaration::Constraint(c1m, c2m), span)
            }
            Declaration::Export(n, sgn, str) => {
                let sgnm = do_map_s(sgn, ctx, fk_b, fc_b, fs_b);
                let strm = map_str(str, ctx, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                Located::new(Declaration::Export(n, sgnm, strm), span)
            }
            Declaration::Table {
                mod_id,
                name,
                name_id,
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
            } => Located::new(
                Declaration::Table {
                    mod_id,
                    name,
                    name_id,
                    con: do_map_c(con, ctx, fk_b, fc_b),
                    exp: do_map_e(exp, ctx, fk_b, fc_b, fe_b),
                    pk_con: do_map_c(pk_con, ctx, fk_b, fc_b),
                    pk_exp: do_map_e(pk_exp, ctx, fk_b, fc_b, fe_b),
                    unique_con: do_map_c(unique_con, ctx, fk_b, fc_b),
                },
                span,
            ),
            Declaration::Sequence(a, b, c) => Located::new(Declaration::Sequence(a, b, c), span),
            Declaration::View(a, b, c, e, con) => {
                let em = do_map_e(e, ctx, fk_b, fc_b, fe_b);
                let cm = do_map_c(con, ctx, fk_b, fc_b);
                Located::new(Declaration::View(a, b, c, em, cm), span)
            }
            Declaration::Index(e1, e2) => {
                let e1m = do_map_e(e1, ctx, fk_b, fc_b, fe_b);
                let e2m = do_map_e(e2, ctx, fk_b, fc_b, fe_b);
                Located::new(Declaration::Index(e1m, e2m), span)
            }
            Declaration::Database(s) => Located::new(Declaration::Database(s), span),
            Declaration::Cookie(a, b, c, con) => {
                let cm = do_map_c(con, ctx, fk_b, fc_b);
                Located::new(Declaration::Cookie(a, b, c, cm), span)
            }
            Declaration::Style(a, b, c) => Located::new(Declaration::Style(a, b, c), span),
            Declaration::Task(e1, e2) => {
                let e1m = do_map_e(e1, ctx, fk_b, fc_b, fe_b);
                let e2m = do_map_e(e2, ctx, fk_b, fc_b, fe_b);
                Located::new(Declaration::Task(e1m, e2m), span)
            }
            Declaration::Policy(e) => {
                let em = do_map_e(e, ctx, fk_b, fc_b, fe_b);
                Located::new(Declaration::Policy(em), span)
            }
            Declaration::OnError(a, b, c) => Located::new(Declaration::OnError(a, b, c), span),
            Declaration::Ffi(x, n, modes, t) => {
                let tm = do_map_c(t, ctx, fk_b, fc_b);
                Located::new(Declaration::Ffi(x, n, modes, tm), span)
            }
        };
        fd_b(ctx, mapped)
    }

    fn map_str(
        s: LocatedStructure,
        ctx: &mut Vec<Binder>,
        fk_b: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fc_b: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        fe_b: &dyn Fn(&[Binder], LocatedExpression) -> LocatedExpression,
        fs_b: &dyn Fn(&[Binder], LocatedSignature) -> LocatedSignature,
        fst_b: &dyn Fn(&[Binder], LocatedStructure) -> LocatedStructure,
        fd_b: &dyn Fn(&[Binder], LocatedDeclaration) -> LocatedDeclaration,
    ) -> LocatedStructure {
        let span = s.span.clone();
        let mapped = match s.node {
            Structure::Var(n) => Located::new(Structure::Var(n), span),
            Structure::Error => Located::new(Structure::Error, span),
            Structure::Const(decls) => {
                let mut decls_out = Vec::with_capacity(decls.len());
                for d in decls {
                    let dm = map_b(d, ctx, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                    decls_out.push(dm);
                }
                Located::new(Structure::Const(decls_out), span)
            }
            Structure::Proj(inner, x) => {
                let im = map_str(*inner, ctx, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                Located::new(Structure::Proj(Box::new(im), x), span)
            }
            Structure::Fun(x, n, dom, ran, body) => {
                let domm = do_map_s(dom, ctx, fk_b, fc_b, fs_b);
                let ranm = do_map_s(ran, ctx, fk_b, fc_b, fs_b);
                let bodym = map_str(*body, ctx, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                Located::new(Structure::Fun(x, n, domm, ranm, Box::new(bodym)), span)
            }
            Structure::App(s1, s2) => {
                let s1m = map_str(*s1, ctx, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                let s2m = map_str(*s2, ctx, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                Located::new(Structure::App(Box::new(s1m), Box::new(s2m)), span)
            }
        };
        fst_b(ctx, mapped)
    }

    /// Fold over all sub-nodes of a declaration.
    pub fn fold<S>(
        d: &LocatedDeclaration,
        init: S,
        fk: &dyn Fn(&LocatedKind, S) -> S,
        fc: &dyn Fn(&LocatedConstructor, S) -> S,
        fe: &dyn Fn(&LocatedExpression, S) -> S,
        fs: &dyn Fn(&LocatedSignature, S) -> S,
        fst: &dyn Fn(&LocatedStructure, S) -> S,
        fd: &dyn Fn(&LocatedDeclaration, S) -> S,
    ) -> S {
        fold_b(
            d,
            &[],
            init,
            &|_ctx, k, s| fk(k, s),
            &|_ctx, c, s| fc(c, s),
            &|_ctx, e, s| fe(e, s),
            &|_ctx, sg, s| fs(sg, s),
            &|_ctx, st, s| fst(st, s),
            &|_ctx, d, s| fd(d, s),
        )
    }

    pub fn fold_b<S>(
        d: &LocatedDeclaration,
        ctx: &[Binder],
        init: S,
        fk_b: &dyn Fn(&[Binder], &LocatedKind, S) -> S,
        fc_b: &dyn Fn(&[Binder], &LocatedConstructor, S) -> S,
        fe_b: &dyn Fn(&[Binder], &LocatedExpression, S) -> S,
        fs_b: &dyn Fn(&[Binder], &LocatedSignature, S) -> S,
        fst_b: &dyn Fn(&[Binder], &LocatedStructure, S) -> S,
        fd_b: &dyn Fn(&[Binder], &LocatedDeclaration, S) -> S,
    ) -> S {
        let s = fd_b(ctx, d, init);
        match &d.node {
            Declaration::Constructor(_, _, k, c) => {
                let s = kutil::fold_b(k, ctx, s, fk_b);
                con_utilities::fold_b(c, ctx, s, fk_b, fc_b)
            }
            Declaration::Datatype(dts) => dts.iter().fold(s, |acc, dt| {
                dt.constrs.iter().fold(acc, |acc2, (_, _, co)| match co {
                    None => acc2,
                    Some(c) => con_utilities::fold_b(c, ctx, acc2, fk_b, fc_b),
                })
            }),
            Declaration::DatatypeImp { constrs, .. } => {
                constrs.iter().fold(s, |acc, (_, _, co)| match co {
                    None => acc,
                    Some(c) => con_utilities::fold_b(c, ctx, acc, fk_b, fc_b),
                })
            }
            Declaration::Val(_, _, ty, e) => {
                let s = con_utilities::fold_b(ty, ctx, s, fk_b, fc_b);
                eutil::fold_b(e, ctx, s, fk_b, fc_b, fe_b)
            }
            Declaration::ValRec(vis) => vis.iter().fold(s, |acc, (_, _, ty, e)| {
                let acc = con_utilities::fold_b(ty, ctx, acc, fk_b, fc_b);
                eutil::fold_b(e, ctx, acc, fk_b, fc_b, fe_b)
            }),
            Declaration::Signature(_, _, sg) => sutil::fold_b(sg, ctx, s, fk_b, fc_b, fs_b),
            Declaration::Structure(_, _, sgn, str) => {
                let s = sutil::fold_b(sgn, ctx, s, fk_b, fc_b, fs_b);
                fold_str(str, ctx, s, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b)
            }
            Declaration::FfiStr(_, _, sgn) => sutil::fold_b(sgn, ctx, s, fk_b, fc_b, fs_b),
            Declaration::Constraint(c1, c2) => {
                let s = con_utilities::fold_b(c1, ctx, s, fk_b, fc_b);
                con_utilities::fold_b(c2, ctx, s, fk_b, fc_b)
            }
            Declaration::Export(_, sgn, str) => {
                let s = sutil::fold_b(sgn, ctx, s, fk_b, fc_b, fs_b);
                fold_str(str, ctx, s, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b)
            }
            Declaration::Table {
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
                ..
            } => {
                let s = con_utilities::fold_b(con, ctx, s, fk_b, fc_b);
                let s = eutil::fold_b(exp, ctx, s, fk_b, fc_b, fe_b);
                let s = con_utilities::fold_b(pk_con, ctx, s, fk_b, fc_b);
                let s = eutil::fold_b(pk_exp, ctx, s, fk_b, fc_b, fe_b);
                con_utilities::fold_b(unique_con, ctx, s, fk_b, fc_b)
            }
            Declaration::Sequence(_, _, _)
            | Declaration::Database(_)
            | Declaration::Style(_, _, _) => s,
            Declaration::View(_, _, _, e, c) => {
                let s = eutil::fold_b(e, ctx, s, fk_b, fc_b, fe_b);
                con_utilities::fold_b(c, ctx, s, fk_b, fc_b)
            }
            Declaration::Index(e1, e2) | Declaration::Task(e1, e2) => {
                let s = eutil::fold_b(e1, ctx, s, fk_b, fc_b, fe_b);
                eutil::fold_b(e2, ctx, s, fk_b, fc_b, fe_b)
            }
            Declaration::Cookie(_, _, _, c) => con_utilities::fold_b(c, ctx, s, fk_b, fc_b),
            Declaration::Policy(e) => eutil::fold_b(e, ctx, s, fk_b, fc_b, fe_b),
            Declaration::OnError(_, _, _) => s,
            Declaration::Ffi(_, _, _, t) => con_utilities::fold_b(t, ctx, s, fk_b, fc_b),
        }
    }

    fn fold_str<S>(
        st: &LocatedStructure,
        ctx: &[Binder],
        init: S,
        fk_b: &dyn Fn(&[Binder], &LocatedKind, S) -> S,
        fc_b: &dyn Fn(&[Binder], &LocatedConstructor, S) -> S,
        fe_b: &dyn Fn(&[Binder], &LocatedExpression, S) -> S,
        fs_b: &dyn Fn(&[Binder], &LocatedSignature, S) -> S,
        fst_b: &dyn Fn(&[Binder], &LocatedStructure, S) -> S,
        fd_b: &dyn Fn(&[Binder], &LocatedDeclaration, S) -> S,
    ) -> S {
        let s = fst_b(ctx, st, init);
        match &st.node {
            Structure::Var(_) | Structure::Error => s,
            Structure::Const(decls) => decls.iter().fold(s, |acc, d| {
                fold_b(d, ctx, acc, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b)
            }),
            Structure::Proj(inner, _) => {
                fold_str(inner, ctx, s, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b)
            }
            Structure::Fun(_, _, dom, ran, body) => {
                let s = sutil::fold_b(dom, ctx, s, fk_b, fc_b, fs_b);
                let s = sutil::fold_b(ran, ctx, s, fk_b, fc_b, fs_b);
                fold_str(body, ctx, s, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b)
            }
            Structure::App(s1, s2) => {
                let s = fold_str(s1, ctx, s, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b);
                fold_str(s2, ctx, s, fk_b, fc_b, fe_b, fs_b, fst_b, fd_b)
            }
        }
    }

    /// Check whether any sub-node of a declaration satisfies the predicate.
    pub fn exists(
        d: &LocatedDeclaration,
        fk: &dyn Fn(&LocatedKind) -> bool,
        fc: &dyn Fn(&LocatedConstructor) -> bool,
        fe: &dyn Fn(&LocatedExpression) -> bool,
        fs: &dyn Fn(&LocatedSignature) -> bool,
        fst: &dyn Fn(&LocatedStructure) -> bool,
        fd: &dyn Fn(&LocatedDeclaration) -> bool,
    ) -> bool {
        if fd(d) {
            return true;
        }
        match &d.node {
            Declaration::Constructor(_, _, k, c) => {
                kutil::exists(k, fk) || con_utilities::exists(c, fk, fc)
            }
            Declaration::Datatype(dts) => dts.iter().any(|dt| {
                dt.constrs.iter().any(|(_, _, co)| {
                    co.as_ref()
                        .is_some_and(|c| con_utilities::exists(c, fk, fc))
                })
            }),
            Declaration::DatatypeImp { constrs, .. } => constrs.iter().any(|(_, _, co)| {
                co.as_ref()
                    .is_some_and(|c| con_utilities::exists(c, fk, fc))
            }),
            Declaration::Val(_, _, ty, e) => {
                con_utilities::exists(ty, fk, fc) || eutil::exists(e, fk, fc, fe)
            }
            Declaration::ValRec(vis) => vis.iter().any(|(_, _, ty, e)| {
                con_utilities::exists(ty, fk, fc) || eutil::exists(e, fk, fc, fe)
            }),
            Declaration::Signature(_, _, sg) => sutil::exists(sg, fk, fc, fs),
            Declaration::Structure(_, _, sgn, str) => {
                sutil::exists(sgn, fk, fc, fs) || exists_str(str, fk, fc, fe, fs, fst, fd)
            }
            Declaration::FfiStr(_, _, sgn) => sutil::exists(sgn, fk, fc, fs),
            Declaration::Constraint(c1, c2) => {
                con_utilities::exists(c1, fk, fc) || con_utilities::exists(c2, fk, fc)
            }
            Declaration::Export(_, sgn, str) => {
                sutil::exists(sgn, fk, fc, fs) || exists_str(str, fk, fc, fe, fs, fst, fd)
            }
            Declaration::Table {
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
                ..
            } => {
                con_utilities::exists(con, fk, fc)
                    || eutil::exists(exp, fk, fc, fe)
                    || con_utilities::exists(pk_con, fk, fc)
                    || eutil::exists(pk_exp, fk, fc, fe)
                    || con_utilities::exists(unique_con, fk, fc)
            }
            Declaration::Sequence(_, _, _)
            | Declaration::Database(_)
            | Declaration::Style(_, _, _) => false,
            Declaration::View(_, _, _, e, c) => {
                eutil::exists(e, fk, fc, fe) || con_utilities::exists(c, fk, fc)
            }
            Declaration::Index(e1, e2) | Declaration::Task(e1, e2) => {
                eutil::exists(e1, fk, fc, fe) || eutil::exists(e2, fk, fc, fe)
            }
            Declaration::Cookie(_, _, _, c) => con_utilities::exists(c, fk, fc),
            Declaration::Policy(e) => eutil::exists(e, fk, fc, fe),
            Declaration::OnError(_, _, _) => false,
            Declaration::Ffi(_, _, _, t) => con_utilities::exists(t, fk, fc),
        }
    }

    fn exists_str(
        st: &LocatedStructure,
        fk: &dyn Fn(&LocatedKind) -> bool,
        fc: &dyn Fn(&LocatedConstructor) -> bool,
        fe: &dyn Fn(&LocatedExpression) -> bool,
        fs: &dyn Fn(&LocatedSignature) -> bool,
        fst: &dyn Fn(&LocatedStructure) -> bool,
        fd: &dyn Fn(&LocatedDeclaration) -> bool,
    ) -> bool {
        if fst(st) {
            return true;
        }
        match &st.node {
            Structure::Var(_) | Structure::Error => false,
            Structure::Const(decls) => decls.iter().any(|d| exists(d, fk, fc, fe, fs, fst, fd)),
            Structure::Proj(inner, _) => exists_str(inner, fk, fc, fe, fs, fst, fd),
            Structure::Fun(_, _, dom, ran, body) => {
                sutil::exists(dom, fk, fc, fs)
                    || sutil::exists(ran, fk, fc, fs)
                    || exists_str(body, fk, fc, fe, fs, fst, fd)
            }
            Structure::App(s1, s2) => {
                exists_str(s1, fk, fc, fe, fs, fst, fd) || exists_str(s2, fk, fc, fe, fs, fst, fd)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// file module
// ---------------------------------------------------------------------------

pub mod file {
    use super::*;

    /// Return the maximum named identifier appearing in the file.
    ///
    /// Mirrors `ElabUtil.File.maxName`.
    pub fn max_name(ds: &[LocatedDeclaration]) -> usize {
        ds.iter().fold(0usize, |acc, d| acc.max(max_name_decl(d)))
    }

    fn max_name_decl(d: &LocatedDeclaration) -> usize {
        match &d.node {
            Declaration::Constructor(_, n, _, _) => *n,
            Declaration::Datatype(dts) => dts.iter().fold(0, |acc, dt| {
                let acc = acc.max(dt.id);
                dt.constrs.iter().fold(acc, |acc2, (_, n, _)| acc2.max(*n))
            }),
            Declaration::DatatypeImp { id, constrs, .. } => {
                constrs.iter().fold(*id, |acc, (_, n, _)| acc.max(*n))
            }
            Declaration::Val(_, n, _, _) => *n,
            Declaration::ValRec(vis) => vis.iter().fold(0, |acc, (_, n, _, _)| acc.max(*n)),
            Declaration::Signature(_, n, sgn) => (*n).max(max_name_sgn(sgn)),
            Declaration::Structure(_, n, sgn, str) => {
                (*n).max(max_name_sgn(sgn)).max(max_name_str(str))
            }
            Declaration::FfiStr(_, n, sgn) => (*n).max(max_name_sgn(sgn)),
            Declaration::Constraint(_, _) => 0,
            Declaration::Export(_, _, _) => 0,
            Declaration::Table {
                mod_id, name_id, ..
            } => (*mod_id).max(*name_id),
            Declaration::Sequence(a, _, b) => (*a).max(*b),
            Declaration::View(a, _, b, _, _) => (*a).max(*b),
            Declaration::Index(_, _) => 0,
            Declaration::Database(_) => 0,
            Declaration::Cookie(a, _, b, _) => (*a).max(*b),
            Declaration::Style(a, _, b) => (*a).max(*b),
            Declaration::Task(_, _) => 0,
            Declaration::Policy(_) => 0,
            Declaration::OnError(_, _, _) => 0,
            Declaration::Ffi(_, n, _, _) => *n,
        }
    }

    fn max_name_str(s: &LocatedStructure) -> usize {
        match &s.node {
            Structure::Const(ds) => max_name(ds),
            Structure::Var(n) => *n,
            Structure::Proj(inner, _) => max_name_str(inner),
            Structure::Fun(_, n, dom, ran, body) => (*n)
                .max(max_name_sgn(dom))
                .max(max_name_sgn(ran))
                .max(max_name_str(body)),
            Structure::App(s1, s2) => max_name_str(s1).max(max_name_str(s2)),
            Structure::Error => 0,
        }
    }

    fn max_name_sgn(s: &LocatedSignature) -> usize {
        match &s.node {
            Signature::Const(items) => items
                .iter()
                .fold(0, |acc, item| acc.max(max_name_sgi(item))),
            Signature::Var(n) => *n,
            Signature::Fun(_, n, dom, ran) => (*n).max(max_name_sgn(dom)).max(max_name_sgn(ran)),
            Signature::Where(inner, _, _, _) => max_name_sgn(inner),
            Signature::Proj(n, _, _) => *n,
            Signature::Error => 0,
        }
    }

    fn max_name_sgi(item: &LocatedSignatureItem) -> usize {
        match &item.node {
            SignatureItem::ConAbs(_, n, _) => *n,
            SignatureItem::Constructor(_, n, _, _) => *n,
            SignatureItem::Datatype(dts) => dts.iter().fold(0, |acc, dt| {
                let acc = acc.max(dt.id);
                dt.constrs.iter().fold(acc, |acc2, (_, n, _)| acc2.max(*n))
            }),
            SignatureItem::DatatypeImp { id, constrs, .. } => {
                constrs.iter().fold(*id, |acc, (_, n, _)| acc.max(*n))
            }
            SignatureItem::Val(_, n, _) => *n,
            SignatureItem::Structure(_, _, n, sgn) => (*n).max(max_name_sgn(sgn)),
            SignatureItem::Signature(_, n, sgn) => (*n).max(max_name_sgn(sgn)),
            SignatureItem::Constraint(_, _) => 0,
            SignatureItem::ClassAbs(_, n, _) => *n,
            SignatureItem::Class(_, n, _, _) => *n,
        }
    }
}
