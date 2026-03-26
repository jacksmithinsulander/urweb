//! Traversal utilities for the Core AST.
//!
//! Provides generic map, fold, and exists operations over kinds, constructors,
//! expressions, declarations, and files. Used by Core passes for transformation
//! and analysis. The `Binder` enum tracks binding context when descending into
//! lambda/forall forms.
//!
//! - **kind**: map/fold/exists/compare over `Kind` trees
//! - **con**: map/fold/exists/compare over `Con` trees (types)
//! - **exp**: map/fold/exists over `Exp` trees
//! - **decl**: map/fold/exists over `Decl` trees
//! - **file**: max_name — maximum named id in a file
//!
//! Mirrors `core_util.sml`.

use crate::core::*;
use crate::datatype_kind::DatatypeKind;
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
/// and one unary, otherwise `DatatypeKind::Default`. Used to choose C representation (integer tag vs nullable pointer vs tagged struct).
///
/// Mirrors the `classify` function from `core_env.sml` / `elab_env.sml`.
pub fn classify_datatype(
    constructor_specifications: &[(String, usize, Option<LocatedConstructor>)],
) -> DatatypeKind {
    // Count nullary (no arg) vs unary (one arg) constructors.
    let mut nullary = 0usize;
    let mut unary = 0usize;
    for (_, _, argument_type) in constructor_specifications {
        if argument_type.is_none() {
            nullary += 1;
        } else {
            unary += 1;
        }
    }
    // Enum: all nullary → use integer tag
    if unary == 0 {
        DatatypeKind::Enum
    }
    // Option: exactly None + Some → use nullable pointer
    else if nullary == 1 && unary == 1 {
        DatatypeKind::Option
    }
    // Default: general case → use tagged struct
    else {
        DatatypeKind::Default
    }
}

// ---------------------------------------------------------------------------
// Binder — unified traversal context type
// ---------------------------------------------------------------------------

/// Context element pushed when descending into a binding form.
/// Used by map_b/fold_b to track what names are in scope.
#[derive(Debug, Clone)]
pub enum Binder {
    /// Kind variable (from KAbs, TKFun).
    RelK(String),
    /// Type variable with kind (from TCFun, Abs, CAbs).
    RelC(String, LocatedKind),
    /// Named constructor (from Con decl).
    NamedC(String, usize, LocatedKind, Option<LocatedConstructor>),
    /// Expression variable with type (from Abs, Let, Var pattern).
    RelE(String, LocatedConstructor),
    /// Named expression (from Val, datatype constructor).
    NamedE(String, usize, LocatedConstructor),
}

// ---------------------------------------------------------------------------
// kind module
// ---------------------------------------------------------------------------

pub mod kind {
    use super::*;
    use std::cmp::Ordering;

    /// Recursively maps over all sub-kinds using a post-order visitor.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind tree to map over.
    /// * `visitor` - Closure invoked on each (already-mapped) sub-kind; returns the replacement kind.
    ///
    /// # Returns
    ///
    /// The kind tree with all nodes transformed by the visitor (children first, then the node).
    pub fn map(kind: LocatedKind, visitor: &dyn Fn(LocatedKind) -> LocatedKind) -> LocatedKind {
        let span = kind.span.clone();
        // Recursively map children first (bottom-up), then apply visitor to the result.
        let mapped = match kind.node {
            Kind::Type => Located::new(Kind::Type, span),
            Kind::Name => Located::new(Kind::Name, span),
            Kind::Unit => Located::new(Kind::Unit, span),
            Kind::Rel(de_bruijn_index) => Located::new(Kind::Rel(de_bruijn_index), span),

            Kind::Arrow(left_kind, right_kind) => {
                let left_mapped = map(*left_kind, visitor);
                let right_mapped = map(*right_kind, visitor);
                Located::new(
                    Kind::Arrow(Box::new(left_mapped), Box::new(right_mapped)),
                    span,
                )
            }
            Kind::Record(inner) => {
                let inner_mapped = map(*inner, visitor);
                Located::new(Kind::Record(Box::new(inner_mapped)), span)
            }
            Kind::Tuple(kinds) => {
                let kinds_mapped: Vec<LocatedKind> = kinds
                    .into_iter()
                    .map(|kind_item| map(kind_item, visitor))
                    .collect();
                Located::new(Kind::Tuple(kinds_mapped), span)
            }
            Kind::Fun(variable_name, body) => {
                let body_mapped = map(*body, visitor);
                Located::new(Kind::Fun(variable_name, Box::new(body_mapped)), span)
            }
        };
        visitor(mapped)
    }

    /// Folds over all sub-kinds in pre-order, accumulating state.
    ///
    /// # Arguments
    ///
    /// * `kind` - The kind tree to fold over.
    /// * `initial_state` - Starting value for the accumulator.
    /// * `folder` - Closure called for each node with (kind reference, current state); returns new state.
    ///
    /// # Returns
    ///
    /// The final accumulated state after visiting every node.
    pub fn fold<State>(
        kind: &LocatedKind,
        initial_state: State,
        folder: &dyn Fn(&LocatedKind, State) -> State,
    ) -> State {
        let state = folder(kind, initial_state);
        match &kind.node {
            Kind::Type | Kind::Name | Kind::Unit | Kind::Rel(_) => state,
            Kind::Arrow(left_kind, right_kind) => {
                let state = fold(left_kind, state, folder);
                fold(right_kind, state, folder)
            }
            Kind::Record(inner) => fold(inner, state, folder),
            Kind::Tuple(kinds) => kinds.iter().fold(state, |accumulator, kind_item| {
                fold(kind_item, accumulator, folder)
            }),
            Kind::Fun(_, body) => fold(body, state, folder),
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
            Kind::Type | Kind::Name | Kind::Unit | Kind::Rel(_) => false,
            Kind::Arrow(left_kind, right_kind) => {
                exists(left_kind, predicate) || exists(right_kind, predicate)
            }
            Kind::Record(inner) => exists(inner, predicate),
            Kind::Tuple(kinds) => kinds.iter().any(|kind_item| exists(kind_item, predicate)),
            Kind::Fun(_, body) => exists(body, predicate),
        }
    }

    /// Total ordering over kinds for use in BTreeMap keys.
    ///
    /// # Arguments
    ///
    /// * `left_kind` - First kind to compare.
    /// * `right_kind` - Second kind to compare.
    ///
    /// # Returns
    ///
    /// `Ordering::Less` | `Equal` | `Greater` consistent with a total order.
    ///
    /// Mirrors `CoreUtil.Kind.compare`.
    pub fn compare(left_kind: &LocatedKind, right_kind: &LocatedKind) -> Ordering {
        use Kind::*;
        // Assigns a discriminant index to each variant for ordering.
        fn discriminant(kind_node: &Kind) -> u8 {
            match kind_node {
                Type => 0,
                Arrow(_, _) => 1,
                Name => 2,
                Record(_) => 3,
                Unit => 4,
                Tuple(_) => 5,
                Rel(_) => 6,
                Fun(_, _) => 7,
            }
        }
        let disc_left = discriminant(&left_kind.node);
        let disc_right = discriminant(&right_kind.node);
        if disc_left != disc_right {
            return disc_left.cmp(&disc_right);
        }
        match (&left_kind.node, &right_kind.node) {
            (Type, Type) => Ordering::Equal,
            (Name, Name) => Ordering::Equal,
            (Unit, Unit) => Ordering::Equal,
            (Rel(index_left), Rel(index_right)) => index_left.cmp(index_right),
            (Arrow(domain_left, range_left), Arrow(domain_right, range_right)) => {
                compare(domain_left, domain_right).then_with(|| compare(range_left, range_right))
            }
            (Record(left_inner), Record(right_inner)) => compare(left_inner, right_inner),
            (Tuple(kinds_left), Tuple(kinds_right)) => compare_kind_list(kinds_left, kinds_right),
            (Fun(_, body_left), Fun(_, body_right)) => compare(body_left, body_right),
            _ => Ordering::Equal,
        }
    }

    /// Lexicographic comparison of two kind lists.
    fn compare_kind_list(left_list: &[LocatedKind], right_list: &[LocatedKind]) -> Ordering {
        let length_ordering = left_list.len().cmp(&right_list.len());
        if length_ordering != Ordering::Equal {
            return length_ordering;
        }
        for (left_item, right_item) in left_list.iter().zip(right_list.iter()) {
            let item_ordering = compare(left_item, right_item);
            if item_ordering != Ordering::Equal {
                return item_ordering;
            }
        }
        Ordering::Equal
    }
}

// ---------------------------------------------------------------------------
// constructor module
// ---------------------------------------------------------------------------

pub mod constructor {
    use super::kind as kind_utilities;
    use super::*;
    use std::cmp::Ordering;

    /// Recursively maps over all sub-constructors and sub-kinds with post-order visitors.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to map over.
    /// * `kind_mapper` - Called for each kind; returns the replacement kind.
    /// * `constructor_mapper` - Called for each constructor; returns the replacement constructor.
    ///
    /// # Returns
    ///
    /// The constructor tree with all nodes transformed (no binder context passed to callbacks).
    pub fn map(
        constructor: LocatedConstructor,
        kind_mapper: &dyn Fn(LocatedKind) -> LocatedKind,
        constructor_mapper: &dyn Fn(LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        map_b(
            constructor,
            &mut vec![],
            kind_mapper,
            &|_context, kind| kind_mapper(kind),
            &|_context, constructor| constructor_mapper(constructor),
        )
    }

    /// Like `map` but provides a binder context to the callbacks when descending under binders.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to map over.
    /// * `context` - Mutable binder stack; pushed/popped when entering/leaving binding forms.
    /// * `kind_mapper` - Used for kinds that do not need context (e.g. in TCFun).
    /// * `fold_kind_binder` - Called for each kind with current binder context.
    /// * `fold_con_binder` - Called for each constructor with current binder context.
    ///
    /// # Returns
    ///
    /// The constructor tree with all nodes transformed; the final result is passed through `fold_con_binder`.
    pub fn map_b(
        constructor: LocatedConstructor,
        context: &mut Vec<Binder>,
        kind_mapper: &dyn Fn(LocatedKind) -> LocatedKind,
        _fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        let span = constructor.span.clone();
        let mapped = match constructor.node {
            Constructor::Rel(de_bruijn_index) => {
                Located::new(Constructor::Rel(de_bruijn_index), span)
            }
            Constructor::Named(name_id) => Located::new(Constructor::Named(name_id), span),
            Constructor::Ffi(module_name, type_name) => {
                Located::new(Constructor::Ffi(module_name, type_name), span)
            }
            Constructor::Name(name) => Located::new(Constructor::Name(name), span),
            Constructor::Unit => Located::new(Constructor::Unit, span),

            Constructor::TFun(left_constructor, right_constructor) => {
                let left_mapped = map_b(
                    *left_constructor,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                let right_mapped = map_b(
                    *right_constructor,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::TFun(Box::new(left_mapped), Box::new(right_mapped)),
                    span,
                )
            }
            Constructor::TRecord(inner) => {
                let inner_mapped = map_b(
                    *inner,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(Constructor::TRecord(Box::new(inner_mapped)), span)
            }
            Constructor::TCFun(variable_name, kind, body) => {
                let kind_mapped = kind_utilities::map(*kind.clone(), kind_mapper);
                context.push(Binder::RelC(variable_name.clone(), *kind));
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                context.pop();
                Located::new(
                    Constructor::TCFun(variable_name, Box::new(kind_mapped), Box::new(body_mapped)),
                    span,
                )
            }
            Constructor::App(function_constructor, argument_constructor) => {
                let function_mapped = map_b(
                    *function_constructor,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                let argument_mapped = map_b(
                    *argument_constructor,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::App(Box::new(function_mapped), Box::new(argument_mapped)),
                    span,
                )
            }
            Constructor::Abs(variable_name, kind, body) => {
                let kind_mapped = kind_utilities::map(*kind.clone(), kind_mapper);
                context.push(Binder::RelC(variable_name.clone(), *kind));
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                context.pop();
                Located::new(
                    Constructor::Abs(variable_name, Box::new(kind_mapped), Box::new(body_mapped)),
                    span,
                )
            }
            Constructor::KAbs(variable_name, body) => {
                context.push(Binder::RelK(variable_name.clone()));
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
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
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                let kind_mapped = kind_utilities::map(*kind_part, kind_mapper);
                Located::new(
                    Constructor::KApp(Box::new(constructor_mapped), Box::new(kind_mapped)),
                    span,
                )
            }
            Constructor::TKFun(variable_name, body) => {
                context.push(Binder::RelK(variable_name.clone()));
                let body_mapped = map_b(
                    *body,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                context.pop();
                Located::new(
                    Constructor::TKFun(variable_name, Box::new(body_mapped)),
                    span,
                )
            }
            Constructor::Record(record_kind, pairs) => {
                let kind_mapped = kind_utilities::map(*record_kind, kind_mapper);
                let pairs_mapped: Vec<(LocatedConstructor, LocatedConstructor)> = pairs
                    .into_iter()
                    .map(|(name_constructor, value_constructor)| {
                        let name_mapped = map_b(
                            name_constructor,
                            context,
                            kind_mapper,
                            _fold_kind_binder,
                            fold_con_binder,
                        );
                        let value_mapped = map_b(
                            value_constructor,
                            context,
                            kind_mapper,
                            _fold_kind_binder,
                            fold_con_binder,
                        );
                        (name_mapped, value_mapped)
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
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                let right_mapped = map_b(
                    *right_constructor,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::Concat(Box::new(left_mapped), Box::new(right_mapped)),
                    span,
                )
            }
            Constructor::Map(domain_kind, range_kind) => {
                let domain_mapped = kind_utilities::map(*domain_kind, kind_mapper);
                let range_mapped = kind_utilities::map(*range_kind, kind_mapper);
                Located::new(
                    Constructor::Map(Box::new(domain_mapped), Box::new(range_mapped)),
                    span,
                )
            }
            Constructor::Tuple(constructors) => {
                let constructors_mapped: Vec<LocatedConstructor> = constructors
                    .into_iter()
                    .map(|constructor_item| {
                        map_b(
                            constructor_item,
                            context,
                            kind_mapper,
                            _fold_kind_binder,
                            fold_con_binder,
                        )
                    })
                    .collect();
                Located::new(Constructor::Tuple(constructors_mapped), span)
            }
            Constructor::Proj(inner, projection_index) => {
                let inner_mapped = map_b(
                    *inner,
                    context,
                    kind_mapper,
                    _fold_kind_binder,
                    fold_con_binder,
                );
                Located::new(
                    Constructor::Proj(Box::new(inner_mapped), projection_index),
                    span,
                )
            }
        };
        fold_con_binder(context, mapped)
    }

    /// Folds over all sub-constructors and sub-kinds, accumulating state.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to fold over.
    /// * `initial_state` - Starting value for the accumulator.
    /// * `fold_kind` - Called for each kind with (kind reference, state); returns new state.
    /// * `fold_constructor` - Called for each constructor with (constructor reference, state); returns new state.
    ///
    /// # Returns
    ///
    /// The final accumulated state (no binder context passed to callbacks).
    pub fn fold<State>(
        constructor: &LocatedConstructor,
        initial_state: State,
        fold_kind: &dyn Fn(&LocatedKind, State) -> State,
        fold_constructor: &dyn Fn(&LocatedConstructor, State) -> State,
    ) -> State {
        fold_b(
            constructor,
            &[],
            initial_state,
            &|_context, kind, state| fold_kind(kind, state),
            &|_context, constructor, state| fold_constructor(constructor, state),
        )
    }

    /// Like `fold` but provides a binder context to the callbacks.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to fold over.
    /// * `context` - Current binder stack (read-only).
    /// * `initial_state` - Starting value for the accumulator.
    /// * `fold_kind_binder` - Called for each kind with (context, kind, state).
    /// * `fold_con_binder` - Called for each constructor with (context, constructor, state).
    ///
    /// # Returns
    ///
    /// The final accumulated state.
    pub fn fold_b<State>(
        constructor: &LocatedConstructor,
        context: &[Binder],
        initial_state: State,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, State) -> State,
        fold_con_binder: &dyn Fn(&[Binder], &LocatedConstructor, State) -> State,
    ) -> State {
        let state = fold_con_binder(context, constructor, initial_state);
        match &constructor.node {
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::Ffi(_, _)
            | Constructor::Name(_)
            | Constructor::Unit => state,

            Constructor::TFun(left_constructor, right_constructor)
            | Constructor::App(left_constructor, right_constructor)
            | Constructor::Concat(left_constructor, right_constructor) => {
                let state = fold_b(
                    left_constructor,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                fold_b(
                    right_constructor,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::TRecord(inner) | Constructor::Proj(inner, _) => {
                fold_b(inner, context, state, fold_kind_binder, fold_con_binder)
            }

            Constructor::TCFun(variable_name, kind, body) => {
                let state = fold_kind_binder(context, kind, state);
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelC(variable_name.clone(), *kind.clone()));
                fold_b(
                    body,
                    &extended_context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::Abs(variable_name, kind, body) => {
                let state = fold_kind_binder(context, kind, state);
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelC(variable_name.clone(), *kind.clone()));
                fold_b(
                    body,
                    &extended_context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::KAbs(variable_name, body) => {
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelK(variable_name.clone()));
                fold_b(
                    body,
                    &extended_context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::KApp(constructor_item, kind_part) => {
                let state = fold_b(
                    constructor_item,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                fold_kind_binder(context, kind_part, state)
            }
            Constructor::TKFun(variable_name, body) => {
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelK(variable_name.clone()));
                fold_b(
                    body,
                    &extended_context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Constructor::Record(record_kind, pairs) => {
                let state = fold_kind_binder(context, record_kind, state);
                pairs.iter().fold(
                    state,
                    |accumulator, (name_constructor, value_constructor)| {
                        let accumulator = fold_b(
                            name_constructor,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        fold_b(
                            value_constructor,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                        )
                    },
                )
            }
            Constructor::Map(domain_kind, range_kind) => {
                let state = fold_kind_binder(context, domain_kind, state);
                fold_kind_binder(context, range_kind, state)
            }
            Constructor::Tuple(constructors) => {
                constructors
                    .iter()
                    .fold(state, |accumulator, constructor_item| {
                        fold_b(
                            constructor_item,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                        )
                    })
            }
        }
    }

    /// Returns true if any sub-constructor or sub-kind satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor tree to search.
    /// * `predicate_kind` - Returns true for a matching kind.
    /// * `predicate_constructor` - Returns true for a matching constructor.
    ///
    /// # Returns
    ///
    /// True when either predicate returns true for at least one node (short-circuits).
    pub fn exists(
        constructor: &LocatedConstructor,
        predicate_kind: &dyn Fn(&LocatedKind) -> bool,
        predicate_constructor: &dyn Fn(&LocatedConstructor) -> bool,
    ) -> bool {
        if predicate_constructor(constructor) {
            return true;
        }
        match &constructor.node {
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::Ffi(_, _)
            | Constructor::Name(_)
            | Constructor::Unit => false,

            Constructor::TFun(left_constructor, right_constructor)
            | Constructor::App(left_constructor, right_constructor)
            | Constructor::Concat(left_constructor, right_constructor) => {
                exists(left_constructor, predicate_kind, predicate_constructor)
                    || exists(right_constructor, predicate_kind, predicate_constructor)
            }
            Constructor::TRecord(inner) | Constructor::Proj(inner, _) => {
                exists(inner, predicate_kind, predicate_constructor)
            }

            Constructor::TCFun(_, kind, body) | Constructor::Abs(_, kind, body) => {
                kind_utilities::exists(kind, predicate_kind)
                    || exists(body, predicate_kind, predicate_constructor)
            }
            Constructor::KAbs(_, body) | Constructor::TKFun(_, body) => {
                exists(body, predicate_kind, predicate_constructor)
            }
            Constructor::KApp(constructor_item, kind_part) => {
                exists(constructor_item, predicate_kind, predicate_constructor)
                    || kind_utilities::exists(kind_part, predicate_kind)
            }
            Constructor::Record(record_kind, pairs) => {
                kind_utilities::exists(record_kind, predicate_kind)
                    || pairs.iter().any(|(name_constructor, value_constructor)| {
                        exists(name_constructor, predicate_kind, predicate_constructor)
                            || exists(value_constructor, predicate_kind, predicate_constructor)
                    })
            }
            Constructor::Map(domain_kind, range_kind) => {
                kind_utilities::exists(domain_kind, predicate_kind)
                    || kind_utilities::exists(range_kind, predicate_kind)
            }
            Constructor::Tuple(constructors) => constructors.iter().any(|constructor_item| {
                exists(constructor_item, predicate_kind, predicate_constructor)
            }),
        }
    }

    /// Total ordering over constructors for use in BTreeMap keys.
    ///
    /// # Arguments
    ///
    /// * `left_constructor` - First constructor to compare.
    /// * `right_constructor` - Second constructor to compare.
    ///
    /// # Returns
    ///
    /// `Ordering::Less` | `Equal` | `Greater` consistent with a total order.
    ///
    /// Mirrors `CoreUtil.Con.compare`.
    pub fn compare(
        left_constructor: &LocatedConstructor,
        right_constructor: &LocatedConstructor,
    ) -> Ordering {
        use Constructor::*;
        fn discriminant(constructor_node: &Constructor) -> u8 {
            match constructor_node {
                TFun(_, _) => 0,
                TCFun(_, _, _) => 1,
                TRecord(_) => 2,
                Rel(_) => 3,
                Named(_) => 4,
                Ffi(_, _) => 5,
                App(_, _) => 6,
                Abs(_, _, _) => 7,
                Name(_) => 8,
                Record(_, _) => 9,
                Concat(_, _) => 10,
                Map(_, _) => 11,
                Unit => 12,
                Tuple(_) => 13,
                Proj(_, _) => 14,
                KAbs(_, _) => 15,
                KApp(_, _) => 16,
                TKFun(_, _) => 17,
            }
        }
        let disc_left = discriminant(&left_constructor.node);
        let disc_right = discriminant(&right_constructor.node);
        if disc_left != disc_right {
            return disc_left.cmp(&disc_right);
        }
        match (&left_constructor.node, &right_constructor.node) {
            (TFun(domain_left, range_left), TFun(domain_right, range_right)) => {
                compare(domain_left, domain_right).then_with(|| compare(range_left, range_right))
            }
            (TCFun(name_left, kind_left, body_left), TCFun(name_right, kind_right, body_right)) => {
                name_left
                    .cmp(name_right)
                    .then_with(|| kind_utilities::compare(kind_left, kind_right))
                    .then_with(|| compare(body_left, body_right))
            }
            (TRecord(left_inner), TRecord(right_inner)) => compare(left_inner, right_inner),
            (Rel(index_left), Rel(index_right)) => index_left.cmp(index_right),
            (Named(id_left), Named(id_right)) => id_left.cmp(id_right),
            (Ffi(module_left, type_left), Ffi(module_right, type_right)) => module_left
                .cmp(module_right)
                .then_with(|| type_left.cmp(type_right)),
            (App(function_left, argument_left), App(function_right, argument_right)) => {
                compare(function_left, function_right)
                    .then_with(|| compare(argument_left, argument_right))
            }
            (Abs(name_left, kind_left, body_left), Abs(name_right, kind_right, body_right)) => {
                name_left
                    .cmp(name_right)
                    .then_with(|| kind_utilities::compare(kind_left, kind_right))
                    .then_with(|| compare(body_left, body_right))
            }
            (Name(string_left), Name(string_right)) => string_left.cmp(string_right),
            (Record(kind_left, pairs_left), Record(kind_right, pairs_right)) => {
                kind_utilities::compare(kind_left, kind_right).then_with(|| {
                    let mut sorted_left = pairs_left.clone();
                    let mut sorted_right = pairs_right.clone();
                    sorted_left
                        .sort_by(|(left_key, _), (right_key, _)| compare(left_key, right_key));
                    sorted_right
                        .sort_by(|(left_key, _), (right_key, _)| compare(left_key, right_key));
                    compare_constructor_pair_list(&sorted_left, &sorted_right)
                })
            }
            (Concat(first_left, second_left), Concat(first_right, second_right)) => {
                compare(first_left, first_right).then_with(|| compare(second_left, second_right))
            }
            (Map(domain_left, range_left), Map(domain_right, range_right)) => {
                kind_utilities::compare(domain_left, domain_right)
                    .then_with(|| kind_utilities::compare(range_left, range_right))
            }
            (Unit, Unit) => Ordering::Equal,
            (Tuple(constructors_left), Tuple(constructors_right)) => {
                compare_constructor_list(constructors_left, constructors_right)
            }
            (Proj(inner_left, index_left), Proj(inner_right, index_right)) => index_left
                .cmp(index_right)
                .then_with(|| compare(inner_left, inner_right)),
            (KAbs(_, body_left), KAbs(_, body_right)) => compare(body_left, body_right),
            (KApp(constructor_left, kind_left), KApp(constructor_right, kind_right)) => {
                compare(constructor_left, constructor_right)
                    .then_with(|| kind_utilities::compare(kind_left, kind_right))
            }
            (TKFun(_, body_left), TKFun(_, body_right)) => compare(body_left, body_right),
            _ => Ordering::Equal,
        }
    }

    fn compare_constructor_list(
        left_list: &[LocatedConstructor],
        right_list: &[LocatedConstructor],
    ) -> Ordering {
        left_list.len().cmp(&right_list.len()).then_with(|| {
            for (left_item, right_item) in left_list.iter().zip(right_list.iter()) {
                let item_ordering = compare(left_item, right_item);
                if item_ordering != Ordering::Equal {
                    return item_ordering;
                }
            }
            Ordering::Equal
        })
    }

    fn compare_constructor_pair_list(
        left_list: &[(LocatedConstructor, LocatedConstructor)],
        right_list: &[(LocatedConstructor, LocatedConstructor)],
    ) -> Ordering {
        left_list.len().cmp(&right_list.len()).then_with(|| {
            for ((key_left, value_left), (key_right, value_right)) in
                left_list.iter().zip(right_list.iter())
            {
                let pair_ordering =
                    compare(key_left, key_right).then_with(|| compare(value_left, value_right));
                if pair_ordering != Ordering::Equal {
                    return pair_ordering;
                }
            }
            Ordering::Equal
        })
    }
}

// ---------------------------------------------------------------------------
// expression module
// ---------------------------------------------------------------------------

pub mod expression {
    use super::constructor as constructor_utilities;
    use super::kind as kind_utilities;
    use super::*;

    /// Maps a constructor using the current expression binder context (kinds/constructors do not add expression binders).
    ///
    /// # Arguments
    ///
    /// * `constructor` - The constructor to map.
    /// * `expression_context` - Current expression binders (passed through for kind/type lookups).
    /// * `fold_kind_binder` - Called for each kind with binder context.
    /// * `fold_con_binder` - Called for each constructor with binder context.
    ///
    /// # Returns
    ///
    /// The mapped constructor. Avoids capturing context in a closure that would block subsequent context.push().
    fn do_map_constructor(
        constructor: LocatedConstructor,
        expression_context: &[Binder],
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
    ) -> LocatedConstructor {
        constructor_utilities::map_b(
            constructor,
            &mut vec![],
            &|kind| fold_kind_binder(expression_context, kind),
            &|_local_context, kind| fold_kind_binder(expression_context, kind),
            &|_local_context, constructor| fold_con_binder(expression_context, constructor),
        )
    }

    /// Recursively maps over all sub-expressions, sub-constructors, and sub-kinds with post-order visitors.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to map over.
    /// * `kind_mapper` - Called for each kind.
    /// * `constructor_mapper` - Called for each constructor.
    /// * `expression_mapper` - Called for each expression.
    ///
    /// # Returns
    ///
    /// The expression tree with all nodes transformed (no binder context passed to callbacks).
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
            &|_context, expression| expression_mapper(expression),
        )
    }

    /// Like `map` but provides a binder context to the callbacks when descending under binders.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to map over.
    /// * `context` - Mutable binder stack; pushed/popped when entering/leaving binding forms.
    /// * `fold_kind_binder` - Called for each kind with current binder context.
    /// * `fold_con_binder` - Called for each constructor with current binder context.
    /// * `fold_exp_binder` - Called for each expression with current binder context.
    ///
    /// # Returns
    ///
    /// The expression tree with all nodes transformed; the final result is passed through `fold_exp_binder`.
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
            Expression::Ffi(module_name, symbol_name) => {
                Located::new(Expression::Ffi(module_name, symbol_name), span)
            }

            Expression::Constructor(
                datatype_kind,
                pattern_constructor,
                constructor_arguments,
                optional_argument,
            ) => {
                let constructor_arguments_mapped: Vec<LocatedConstructor> = constructor_arguments
                    .into_iter()
                    .map(|constructor| {
                        do_map_constructor(constructor, context, fold_kind_binder, fold_con_binder)
                    })
                    .collect();
                let optional_argument_mapped = optional_argument.map(|argument| {
                    Box::new(map_b(
                        *argument,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    ))
                });
                Located::new(
                    Expression::Constructor(
                        datatype_kind,
                        pattern_constructor,
                        constructor_arguments_mapped,
                        optional_argument_mapped,
                    ),
                    span,
                )
            }
            Expression::FfiApp(module_name, function_name, arguments) => {
                let arguments_mapped: Vec<(LocatedExpression, LocatedConstructor)> = arguments
                    .into_iter()
                    .map(|(argument_expression, argument_constructor)| {
                        let expression_mapped = map_b(
                            argument_expression,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        );
                        let constructor_mapped = do_map_constructor(
                            argument_constructor,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        (expression_mapped, constructor_mapped)
                    })
                    .collect();
                Located::new(
                    Expression::FfiApp(module_name, function_name, arguments_mapped),
                    span,
                )
            }
            Expression::App(function_expression, argument_expression) => {
                let function_mapped = map_b(
                    *function_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let argument_mapped = map_b(
                    *argument_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                Located::new(
                    Expression::App(Box::new(function_mapped), Box::new(argument_mapped)),
                    span,
                )
            }
            Expression::Abs(variable_name, domain_type, range_type, body) => {
                let domain_mapped = do_map_constructor(
                    domain_type.clone(),
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let range_mapped =
                    do_map_constructor(range_type, context, fold_kind_binder, fold_con_binder);
                context.push(Binder::RelE(variable_name.clone(), domain_type));
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
            Expression::CApp(expression_function, type_argument) => {
                let function_mapped = map_b(
                    *expression_function,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let constructor_mapped =
                    do_map_constructor(type_argument, context, fold_kind_binder, fold_con_binder);
                Located::new(
                    Expression::CApp(Box::new(function_mapped), constructor_mapped),
                    span,
                )
            }
            Expression::CAbs(variable_name, kind, body) => {
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
                    Expression::CAbs(variable_name, Box::new(kind_mapped), Box::new(body_mapped)),
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
                let function_mapped = map_b(
                    *expression_function,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let kind_mapped = fold_kind_binder(context, *kind_argument);
                Located::new(
                    Expression::KApp(Box::new(function_mapped), Box::new(kind_mapped)),
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
                    .map(|(field_name_constructor, field_value, field_type)| {
                        let name_mapped = do_map_constructor(
                            field_name_constructor,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        let value_mapped = map_b(
                            field_value,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        );
                        let type_mapped = do_map_constructor(
                            field_type,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        (name_mapped, value_mapped, type_mapped)
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
                let field_constructor_mapped = do_map_constructor(
                    field_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let meta_mapped = FieldMeta {
                    field: do_map_constructor(
                        field_meta.field,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                    rest: do_map_constructor(
                        field_meta.rest,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::Field(
                        Box::new(record_mapped),
                        field_constructor_mapped,
                        meta_mapped,
                    ),
                    span,
                )
            }
            Expression::Concat(
                left_expression,
                left_constructor,
                right_expression,
                right_constructor,
            ) => {
                let left_expr_mapped = map_b(
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
                let right_expr_mapped = map_b(
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
                        Box::new(left_expr_mapped),
                        left_con_mapped,
                        Box::new(right_expr_mapped),
                        right_con_mapped,
                    ),
                    span,
                )
            }
            Expression::Cut(record_expression, field_constructor, cut_meta) => {
                let record_mapped = map_b(
                    *record_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let field_constructor_mapped = do_map_constructor(
                    field_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let meta_mapped = FieldMeta {
                    field: do_map_constructor(
                        cut_meta.field,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                    rest: do_map_constructor(
                        cut_meta.rest,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::Cut(
                        Box::new(record_mapped),
                        field_constructor_mapped,
                        meta_mapped,
                    ),
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
                let field_constructor_mapped = do_map_constructor(
                    field_constructor,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let meta_mapped = RestMeta {
                    rest: do_map_constructor(
                        rest_meta.rest,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::CutMulti(
                        Box::new(record_mapped),
                        field_constructor_mapped,
                        meta_mapped,
                    ),
                    span,
                )
            }
            Expression::Case(discriminant_expression, arms, case_meta) => {
                let discriminant_mapped = map_b(
                    *discriminant_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let arms_mapped: Vec<(LocatedPattern, LocatedExpression)> = arms
                    .into_iter()
                    .map(|(pattern, arm_expression)| {
                        let pattern_mapped = map_pattern(
                            pattern,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        );
                        let arm_binders = pattern_binders_for_context(&pattern_mapped);
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
                let case_meta_mapped = CaseMeta {
                    disc: do_map_constructor(
                        case_meta.disc,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                    result: do_map_constructor(
                        case_meta.result,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                };
                Located::new(
                    Expression::Case(Box::new(discriminant_mapped), arms_mapped, case_meta_mapped),
                    span,
                )
            }
            Expression::Write(inner_expression) => {
                let inner_mapped = map_b(
                    *inner_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                Located::new(Expression::Write(Box::new(inner_mapped)), span)
            }
            Expression::Closure(closure_id, environment_expressions) => {
                let environment_mapped: Vec<LocatedExpression> = environment_expressions
                    .into_iter()
                    .map(|environment_expression| {
                        map_b(
                            environment_expression,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        )
                    })
                    .collect();
                Located::new(Expression::Closure(closure_id, environment_mapped), span)
            }
            Expression::Let(
                variable_name,
                type_annotation,
                first_expression,
                second_expression,
            ) => {
                let type_mapped = do_map_constructor(
                    type_annotation.clone(),
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let first_mapped = map_b(
                    *first_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                context.push(Binder::RelE(variable_name.clone(), type_annotation));
                let second_mapped = map_b(
                    *second_expression,
                    context,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                context.pop();
                Located::new(
                    Expression::Let(
                        variable_name,
                        type_mapped,
                        Box::new(first_mapped),
                        Box::new(second_mapped),
                    ),
                    span,
                )
            }
            Expression::ServerCall(server_call_id, arguments, result_type, format_mode) => {
                let arguments_mapped: Vec<LocatedExpression> = arguments
                    .into_iter()
                    .map(|argument_expression| {
                        map_b(
                            argument_expression,
                            context,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        )
                    })
                    .collect();
                let type_mapped =
                    do_map_constructor(result_type, context, fold_kind_binder, fold_con_binder);
                Located::new(
                    Expression::ServerCall(
                        server_call_id,
                        arguments_mapped,
                        type_mapped,
                        format_mode,
                    ),
                    span,
                )
            }
        };
        fold_exp_binder(context, mapped)
    }

    /// Maps a pattern, visiting its embedded types with the constructor binder callback.
    fn map_pattern(
        pattern: LocatedPattern,
        context: &mut Vec<Binder>,
        fold_kind_binder: &dyn Fn(&[Binder], LocatedKind) -> LocatedKind,
        fold_con_binder: &dyn Fn(&[Binder], LocatedConstructor) -> LocatedConstructor,
        _fold_exp_binder: &dyn Fn(&[Binder], LocatedExpression) -> LocatedExpression,
    ) -> LocatedPattern {
        let span = pattern.span.clone();
        let node = match pattern.node {
            Pattern::Var(variable_name, type_annotation) => Pattern::Var(
                variable_name,
                do_map_constructor(type_annotation, context, fold_kind_binder, fold_con_binder),
            ),
            Pattern::Prim(primitive) => Pattern::Prim(primitive),
            Pattern::Constructor(
                datatype_kind,
                pattern_constructor,
                constructor_arguments,
                optional_sub_pattern,
            ) => {
                let arguments_mapped: Vec<LocatedConstructor> = constructor_arguments
                    .into_iter()
                    .map(|constructor| {
                        do_map_constructor(constructor, context, fold_kind_binder, fold_con_binder)
                    })
                    .collect();
                let sub_pattern_mapped = optional_sub_pattern.map(|sub_pattern| {
                    Box::new(map_pattern(
                        *sub_pattern,
                        context,
                        fold_kind_binder,
                        fold_con_binder,
                        _fold_exp_binder,
                    ))
                });
                Pattern::Constructor(
                    datatype_kind,
                    pattern_constructor,
                    arguments_mapped,
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
                                _fold_exp_binder,
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

    /// Collects expression binders from a pattern for extending context when entering a case arm.
    fn pattern_binders_for_context(pattern: &LocatedPattern) -> Vec<Binder> {
        let mut output = Vec::new();
        collect_pattern_binders(pattern, &mut output);
        output
    }

    fn collect_pattern_binders(pattern: &LocatedPattern, output: &mut Vec<Binder>) {
        match &pattern.node {
            Pattern::Var(variable_name, type_annotation) => {
                output.push(Binder::RelE(variable_name.clone(), type_annotation.clone()))
            }
            Pattern::Prim(_) => {}
            Pattern::Constructor(_, _, _, None) => {}
            Pattern::Constructor(_, _, _, Some(sub_pattern)) => {
                collect_pattern_binders(sub_pattern, output)
            }
            Pattern::Record(record_fields) => {
                for (_, sub_pattern, _) in record_fields {
                    collect_pattern_binders(sub_pattern, output);
                }
            }
        }
    }

    /// Folds over all sub-expressions and embedded constructors/kinds, accumulating state.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to fold over.
    /// * `initial_state` - Starting value for the accumulator.
    /// * `fold_kind` - Called for each kind with (kind reference, state).
    /// * `fold_constructor` - Called for each constructor with (constructor reference, state).
    /// * `fold_expression` - Called for each expression with (expression reference, state).
    ///
    /// # Returns
    ///
    /// The final accumulated state (no binder context passed to callbacks).
    pub fn fold<State>(
        expression: &LocatedExpression,
        initial_state: State,
        fold_kind: &dyn Fn(&LocatedKind, State) -> State,
        fold_constructor: &dyn Fn(&LocatedConstructor, State) -> State,
        fold_expression: &dyn Fn(&LocatedExpression, State) -> State,
    ) -> State {
        fold_b(
            expression,
            &[],
            initial_state,
            &|_context, kind, state| fold_kind(kind, state),
            &|_context, constructor, state| fold_constructor(constructor, state),
            &|_context, expression, state| fold_expression(expression, state),
        )
    }

    /// Like `fold` but provides a binder context to the callbacks.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to fold over.
    /// * `context` - Current binder stack (read-only).
    /// * `initial_state` - Starting value for the accumulator.
    /// * `fold_kind_binder` - Called for each kind with (context, kind, state).
    /// * `fold_con_binder` - Called for each constructor with (context, constructor, state).
    /// * `fold_exp_binder` - Called for each expression with (context, expression, state).
    ///
    /// # Returns
    ///
    /// The final accumulated state.
    pub fn fold_b<State>(
        expression: &LocatedExpression,
        context: &[Binder],
        initial_state: State,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, State) -> State,
        fold_con_binder: &dyn Fn(&[Binder], &LocatedConstructor, State) -> State,
        fold_exp_binder: &dyn Fn(&[Binder], &LocatedExpression, State) -> State,
    ) -> State {
        let state = fold_exp_binder(context, expression, initial_state);
        match &expression.node {
            Expression::Prim(_)
            | Expression::Rel(_)
            | Expression::Named(_)
            | Expression::Ffi(_, _) => state,
            Expression::Constructor(_, _, constructor_arguments, optional_argument) => {
                let state = constructor_arguments
                    .iter()
                    .fold(state, |accumulator, constructor| {
                        constructor_utilities::fold_b(
                            constructor,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                        )
                    });
                match optional_argument {
                    None => state,
                    Some(argument_expression) => fold_b(
                        argument_expression,
                        context,
                        state,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    ),
                }
            }
            Expression::FfiApp(_, _, arguments) => arguments.iter().fold(
                state,
                |accumulator, (argument_expression, argument_constructor)| {
                    let accumulator = fold_b(
                        argument_expression,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    );
                    constructor_utilities::fold_b(
                        argument_constructor,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                    )
                },
            ),
            Expression::App(left_expression, right_expression) => {
                let state = fold_b(
                    left_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                fold_b(
                    right_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::Abs(variable_name, domain_type, range_type, body) => {
                let state = constructor_utilities::fold_b(
                    domain_type,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let state = constructor_utilities::fold_b(
                    range_type,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelE(variable_name.clone(), domain_type.clone()));
                fold_b(
                    body,
                    &extended_context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::CApp(expression_function, type_argument) => {
                let state = fold_b(
                    expression_function,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                constructor_utilities::fold_b(
                    type_argument,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::CAbs(variable_name, kind, body) => {
                let state = fold_kind_binder(context, kind, state);
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelC(variable_name.clone(), *kind.clone()));
                fold_b(
                    body,
                    &extended_context,
                    state,
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
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::KApp(expression_function, kind_argument) => {
                let state = fold_b(
                    expression_function,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                fold_kind_binder(context, kind_argument, state)
            }
            Expression::Record(fields) => fields.iter().fold(
                state,
                |accumulator, (field_name_constructor, field_value, field_type)| {
                    let accumulator = constructor_utilities::fold_b(
                        field_name_constructor,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                    );
                    let accumulator = fold_b(
                        field_value,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                        fold_exp_binder,
                    );
                    constructor_utilities::fold_b(
                        field_type,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                    )
                },
            ),
            Expression::Field(record_expression, field_constructor, field_meta) => {
                let state = fold_b(
                    record_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let state = constructor_utilities::fold_b(
                    field_constructor,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let state = constructor_utilities::fold_b(
                    &field_meta.field,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                constructor_utilities::fold_b(
                    &field_meta.rest,
                    context,
                    state,
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
                let state = fold_b(
                    left_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let state = constructor_utilities::fold_b(
                    left_constructor,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let state = fold_b(
                    right_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                constructor_utilities::fold_b(
                    right_constructor,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::Cut(record_expression, field_constructor, cut_meta) => {
                let state = fold_b(
                    record_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let state = constructor_utilities::fold_b(
                    field_constructor,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let state = constructor_utilities::fold_b(
                    &cut_meta.field,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                constructor_utilities::fold_b(
                    &cut_meta.rest,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::CutMulti(record_expression, field_constructor, rest_meta) => {
                let state = fold_b(
                    record_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let state = constructor_utilities::fold_b(
                    field_constructor,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                constructor_utilities::fold_b(
                    &rest_meta.rest,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::Case(discriminant_expression, arms, case_meta) => {
                let state = fold_b(
                    discriminant_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let state = arms
                    .iter()
                    .fold(state, |accumulator, (pattern, arm_expression)| {
                        let accumulator = fold_pattern(
                            pattern,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                        );
                        let mut extended_context = context.to_vec();
                        collect_pattern_binders_fold(pattern, &mut extended_context);
                        fold_b(
                            arm_expression,
                            &extended_context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        )
                    });
                let state = constructor_utilities::fold_b(
                    &case_meta.disc,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                constructor_utilities::fold_b(
                    &case_meta.result,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
            Expression::Write(inner_expression) => fold_b(
                inner_expression,
                context,
                state,
                fold_kind_binder,
                fold_con_binder,
                fold_exp_binder,
            ),
            Expression::Closure(_, environment_expressions) => {
                environment_expressions
                    .iter()
                    .fold(state, |accumulator, environment_expression| {
                        fold_b(
                            environment_expression,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        )
                    })
            }
            Expression::Let(
                variable_name,
                type_annotation,
                first_expression,
                second_expression,
            ) => {
                let state = constructor_utilities::fold_b(
                    type_annotation,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                );
                let state = fold_b(
                    first_expression,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                );
                let mut extended_context = context.to_vec();
                extended_context.push(Binder::RelE(variable_name.clone(), type_annotation.clone()));
                fold_b(
                    second_expression,
                    &extended_context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                    fold_exp_binder,
                )
            }
            Expression::ServerCall(_, arguments, result_type, _) => {
                let state = arguments
                    .iter()
                    .fold(state, |accumulator, argument_expression| {
                        fold_b(
                            argument_expression,
                            context,
                            accumulator,
                            fold_kind_binder,
                            fold_con_binder,
                            fold_exp_binder,
                        )
                    });
                constructor_utilities::fold_b(
                    result_type,
                    context,
                    state,
                    fold_kind_binder,
                    fold_con_binder,
                )
            }
        }
    }

    fn fold_pattern<State>(
        pattern: &LocatedPattern,
        context: &[Binder],
        initial_state: State,
        fold_kind_binder: &dyn Fn(&[Binder], &LocatedKind, State) -> State,
        fold_con_binder: &dyn Fn(&[Binder], &LocatedConstructor, State) -> State,
    ) -> State {
        match &pattern.node {
            Pattern::Var(_, type_annotation) => constructor_utilities::fold_b(
                type_annotation,
                context,
                initial_state,
                fold_kind_binder,
                fold_con_binder,
            ),
            Pattern::Prim(_) => initial_state,
            Pattern::Constructor(_, _, constructor_arguments, optional_sub_pattern) => {
                let state =
                    constructor_arguments
                        .iter()
                        .fold(initial_state, |accumulator, constructor| {
                            constructor_utilities::fold_b(
                                constructor,
                                context,
                                accumulator,
                                fold_kind_binder,
                                fold_con_binder,
                            )
                        });
                match optional_sub_pattern {
                    None => state,
                    Some(sub_pattern) => fold_pattern(
                        sub_pattern,
                        context,
                        state,
                        fold_kind_binder,
                        fold_con_binder,
                    ),
                }
            }
            Pattern::Record(record_fields) => record_fields.iter().fold(
                initial_state,
                |accumulator, (_, sub_pattern, field_type)| {
                    let accumulator = fold_pattern(
                        sub_pattern,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                    );
                    constructor_utilities::fold_b(
                        field_type,
                        context,
                        accumulator,
                        fold_kind_binder,
                        fold_con_binder,
                    )
                },
            ),
        }
    }

    fn collect_pattern_binders_fold(pattern: &LocatedPattern, context: &mut Vec<Binder>) {
        match &pattern.node {
            Pattern::Var(variable_name, type_annotation) => {
                context.push(Binder::RelE(variable_name.clone(), type_annotation.clone()))
            }
            Pattern::Prim(_) => {}
            Pattern::Constructor(_, _, _, None) => {}
            Pattern::Constructor(_, _, _, Some(sub_pattern)) => {
                collect_pattern_binders_fold(sub_pattern, context)
            }
            Pattern::Record(record_fields) => {
                for (_, sub_pattern, _) in record_fields {
                    collect_pattern_binders_fold(sub_pattern, context);
                }
            }
        }
    }

    /// Returns true if any sub-expression or embedded constructor/kind satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `expression` - The expression tree to search.
    /// * `predicate_kind` - Returns true for a matching kind.
    /// * `predicate_constructor` - Returns true for a matching constructor.
    /// * `predicate_expression` - Returns true for a matching expression.
    ///
    /// # Returns
    ///
    /// True when any predicate returns true for at least one node (short-circuits).
    pub fn exists(
        expression: &LocatedExpression,
        predicate_kind: &dyn Fn(&LocatedKind) -> bool,
        predicate_constructor: &dyn Fn(&LocatedConstructor) -> bool,
        predicate_expression: &dyn Fn(&LocatedExpression) -> bool,
    ) -> bool {
        if predicate_expression(expression) {
            return true;
        }
        match &expression.node {
            Expression::Prim(_)
            | Expression::Rel(_)
            | Expression::Named(_)
            | Expression::Ffi(_, _) => false,
            Expression::Constructor(_, _, constructor_arguments, optional_argument) => {
                constructor_arguments.iter().any(|constructor| {
                    constructor_utilities::exists(
                        constructor,
                        predicate_kind,
                        predicate_constructor,
                    )
                }) || optional_argument
                    .as_ref()
                    .is_some_and(|argument_expression| {
                        exists(
                            argument_expression,
                            predicate_kind,
                            predicate_constructor,
                            predicate_expression,
                        )
                    })
            }
            Expression::FfiApp(_, _, arguments) => {
                arguments
                    .iter()
                    .any(|(argument_expression, argument_constructor)| {
                        exists(
                            argument_expression,
                            predicate_kind,
                            predicate_constructor,
                            predicate_expression,
                        ) || constructor_utilities::exists(
                            argument_constructor,
                            predicate_kind,
                            predicate_constructor,
                        )
                    })
            }
            Expression::App(left_expression, right_expression) => {
                exists(
                    left_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || exists(
                    right_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                )
            }
            Expression::Abs(_, domain_type, range_type, body) => {
                constructor_utilities::exists(domain_type, predicate_kind, predicate_constructor)
                    || constructor_utilities::exists(
                        range_type,
                        predicate_kind,
                        predicate_constructor,
                    )
                    || exists(
                        body,
                        predicate_kind,
                        predicate_constructor,
                        predicate_expression,
                    )
            }
            Expression::CApp(expression_function, type_argument) => {
                exists(
                    expression_function,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || constructor_utilities::exists(
                    type_argument,
                    predicate_kind,
                    predicate_constructor,
                )
            }
            Expression::CAbs(_, kind, body) => {
                kind_utilities::exists(kind, predicate_kind)
                    || exists(
                        body,
                        predicate_kind,
                        predicate_constructor,
                        predicate_expression,
                    )
            }
            Expression::KAbs(_, body) | Expression::Write(body) => exists(
                body,
                predicate_kind,
                predicate_constructor,
                predicate_expression,
            ),
            Expression::KApp(expression_function, kind_argument) => {
                exists(
                    expression_function,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || kind_utilities::exists(kind_argument, predicate_kind)
            }
            Expression::Record(fields) => {
                fields
                    .iter()
                    .any(|(field_name_constructor, field_value, field_type)| {
                        constructor_utilities::exists(
                            field_name_constructor,
                            predicate_kind,
                            predicate_constructor,
                        ) || exists(
                            field_value,
                            predicate_kind,
                            predicate_constructor,
                            predicate_expression,
                        ) || constructor_utilities::exists(
                            field_type,
                            predicate_kind,
                            predicate_constructor,
                        )
                    })
            }
            Expression::Field(record_expression, field_constructor, field_meta) => {
                exists(
                    record_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || constructor_utilities::exists(
                    field_constructor,
                    predicate_kind,
                    predicate_constructor,
                ) || constructor_utilities::exists(
                    &field_meta.field,
                    predicate_kind,
                    predicate_constructor,
                ) || constructor_utilities::exists(
                    &field_meta.rest,
                    predicate_kind,
                    predicate_constructor,
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
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || constructor_utilities::exists(
                    left_constructor,
                    predicate_kind,
                    predicate_constructor,
                ) || exists(
                    right_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || constructor_utilities::exists(
                    right_constructor,
                    predicate_kind,
                    predicate_constructor,
                )
            }
            Expression::Cut(record_expression, field_constructor, cut_meta) => {
                exists(
                    record_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || constructor_utilities::exists(
                    field_constructor,
                    predicate_kind,
                    predicate_constructor,
                ) || constructor_utilities::exists(
                    &cut_meta.field,
                    predicate_kind,
                    predicate_constructor,
                ) || constructor_utilities::exists(
                    &cut_meta.rest,
                    predicate_kind,
                    predicate_constructor,
                )
            }
            Expression::CutMulti(record_expression, field_constructor, rest_meta) => {
                exists(
                    record_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || constructor_utilities::exists(
                    field_constructor,
                    predicate_kind,
                    predicate_constructor,
                ) || constructor_utilities::exists(
                    &rest_meta.rest,
                    predicate_kind,
                    predicate_constructor,
                )
            }
            Expression::Case(discriminant_expression, arms, case_meta) => {
                exists(
                    discriminant_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || arms.iter().any(|(_, arm_expression)| {
                    exists(
                        arm_expression,
                        predicate_kind,
                        predicate_constructor,
                        predicate_expression,
                    )
                }) || constructor_utilities::exists(
                    &case_meta.disc,
                    predicate_kind,
                    predicate_constructor,
                ) || constructor_utilities::exists(
                    &case_meta.result,
                    predicate_kind,
                    predicate_constructor,
                )
            }
            Expression::Closure(_, environment_expressions) => {
                environment_expressions
                    .iter()
                    .any(|environment_expression| {
                        exists(
                            environment_expression,
                            predicate_kind,
                            predicate_constructor,
                            predicate_expression,
                        )
                    })
            }
            Expression::Let(_, type_annotation, first_expression, second_expression) => {
                constructor_utilities::exists(
                    type_annotation,
                    predicate_kind,
                    predicate_constructor,
                ) || exists(
                    first_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                ) || exists(
                    second_expression,
                    predicate_kind,
                    predicate_constructor,
                    predicate_expression,
                )
            }
            Expression::ServerCall(_, arguments, result_type, _) => {
                arguments.iter().any(|argument_expression| {
                    exists(
                        argument_expression,
                        predicate_kind,
                        predicate_constructor,
                        predicate_expression,
                    )
                }) || constructor_utilities::exists(
                    result_type,
                    predicate_kind,
                    predicate_constructor,
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// declaration module
// ---------------------------------------------------------------------------

pub mod declaration {
    use super::constructor as constructor_utilities;
    use super::expression as expression_utilities;
    use super::kind as kind_utilities;
    use super::*;

    /// Recursively maps over all sub-nodes of a declaration (kinds, constructors, expressions, and the declaration itself).
    ///
    /// # Arguments
    ///
    /// * `declaration` - The declaration to map over.
    /// * `kind_mapper` - Called for each kind.
    /// * `constructor_mapper` - Called for each constructor.
    /// * `expression_mapper` - Called for each expression.
    /// * `declaration_mapper` - Called for the declaration node itself (post-order).
    ///
    /// # Returns
    ///
    /// The declaration with all sub-nodes transformed; the result is passed through `declaration_mapper`.
    pub fn map(
        declaration: LocatedDeclaration,
        kind_mapper: &dyn Fn(LocatedKind) -> LocatedKind,
        constructor_mapper: &dyn Fn(LocatedConstructor) -> LocatedConstructor,
        expression_mapper: &dyn Fn(LocatedExpression) -> LocatedExpression,
        declaration_mapper: &dyn Fn(LocatedDeclaration) -> LocatedDeclaration,
    ) -> LocatedDeclaration {
        let span = declaration.span.clone();
        let map_constructor = |constructor: LocatedConstructor| {
            constructor_utilities::map(constructor, kind_mapper, constructor_mapper)
        };
        let map_expression = |expression: LocatedExpression| {
            expression_utilities::map(
                expression,
                kind_mapper,
                constructor_mapper,
                expression_mapper,
            )
        };

        let mapped = match declaration.node {
            Declaration::Constructor(variable_name, name_id, kind, constructor) => {
                let kind_mapped = kind_utilities::map(kind, kind_mapper);
                let constructor_mapped = map_constructor(constructor);
                Located::new(
                    Declaration::Constructor(
                        variable_name,
                        name_id,
                        kind_mapped,
                        constructor_mapped,
                    ),
                    span,
                )
            }
            Declaration::Datatype(datatype_declarations) => {
                let datatypes_mapped: Vec<DatatypeDecl> = datatype_declarations
                    .into_iter()
                    .map(|datatype_declaration| DatatypeDecl {
                        name: datatype_declaration.name,
                        id: datatype_declaration.id,
                        params: datatype_declaration.params,
                        constrs: datatype_declaration
                            .constrs
                            .into_iter()
                            .map(|(variable_name, name_id, optional_constructor)| {
                                (
                                    variable_name,
                                    name_id,
                                    optional_constructor.map(map_constructor),
                                )
                            })
                            .collect(),
                    })
                    .collect();
                Located::new(Declaration::Datatype(datatypes_mapped), span)
            }
            Declaration::Val(variable_name, name_id, type_annotation, expression, comment) => {
                let type_mapped = map_constructor(type_annotation);
                let expression_mapped = map_expression(expression);
                Located::new(
                    Declaration::Val(
                        variable_name,
                        name_id,
                        type_mapped,
                        expression_mapped,
                        comment,
                    ),
                    span,
                )
            }
            Declaration::ValRec(mutually_recursive_bindings) => {
                let bindings_mapped: Vec<(
                    String,
                    usize,
                    LocatedConstructor,
                    LocatedExpression,
                    String,
                )> = mutually_recursive_bindings
                    .into_iter()
                    .map(
                        |(variable_name, name_id, type_annotation, expression, comment_string)| {
                            let type_mapped = map_constructor(type_annotation);
                            let expression_mapped = map_expression(expression);
                            (
                                variable_name,
                                name_id,
                                type_mapped,
                                expression_mapped,
                                comment_string,
                            )
                        },
                    )
                    .collect();
                Located::new(Declaration::ValRec(bindings_mapped), span)
            }
            Declaration::Export(export_kind, name_id, has_state) => {
                Located::new(Declaration::Export(export_kind, name_id, has_state), span)
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
            } => Located::new(
                Declaration::Table {
                    sql_name,
                    id,
                    con: map_constructor(con),
                    sql_con,
                    exp: map_expression(exp),
                    pk_con: map_constructor(pk_con),
                    pk_exp: map_expression(pk_exp),
                    unique_con: map_constructor(unique_con),
                },
                span,
            ),
            Declaration::Sequence(variable_name, name_id, sql_name) => Located::new(
                Declaration::Sequence(variable_name, name_id, sql_name),
                span,
            ),
            Declaration::View(variable_name, name_id, sql_string, expression, constructor) => {
                Located::new(
                    Declaration::View(
                        variable_name,
                        name_id,
                        sql_string,
                        map_expression(expression),
                        map_constructor(constructor),
                    ),
                    span,
                )
            }
            Declaration::Index(first_expression, second_expression) => Located::new(
                Declaration::Index(
                    map_expression(first_expression),
                    map_expression(second_expression),
                ),
                span,
            ),
            Declaration::Database(database_string) => {
                Located::new(Declaration::Database(database_string), span)
            }
            Declaration::Cookie(variable_name, name_id, constructor, cookie_string) => {
                Located::new(
                    Declaration::Cookie(
                        variable_name,
                        name_id,
                        map_constructor(constructor),
                        cookie_string,
                    ),
                    span,
                )
            }
            Declaration::Style(variable_name, name_id, style_string) => Located::new(
                Declaration::Style(variable_name, name_id, style_string),
                span,
            ),
            Declaration::Task(first_expression, second_expression) => Located::new(
                Declaration::Task(
                    map_expression(first_expression),
                    map_expression(second_expression),
                ),
                span,
            ),
            Declaration::Policy(policy_expression) => {
                Located::new(Declaration::Policy(map_expression(policy_expression)), span)
            }
            Declaration::OnError(handler_name_id) => {
                Located::new(Declaration::OnError(handler_name_id), span)
            }
        };
        declaration_mapper(mapped)
    }

    /// Folds over all sub-nodes of a declaration, accumulating state.
    ///
    /// # Arguments
    ///
    /// * `declaration` - The declaration to fold over.
    /// * `initial_state` - Starting value for the accumulator.
    /// * `fold_kind` - Called for each kind with (kind reference, state).
    /// * `fold_constructor` - Called for each constructor with (constructor reference, state).
    /// * `fold_expression` - Called for each expression with (expression reference, state).
    /// * `fold_declaration` - Called for the declaration with (declaration reference, state).
    ///
    /// # Returns
    ///
    /// The final accumulated state.
    pub fn fold<State>(
        declaration: &LocatedDeclaration,
        initial_state: State,
        fold_kind: &dyn Fn(&LocatedKind, State) -> State,
        fold_constructor: &dyn Fn(&LocatedConstructor, State) -> State,
        fold_expression: &dyn Fn(&LocatedExpression, State) -> State,
        fold_declaration: &dyn Fn(&LocatedDeclaration, State) -> State,
    ) -> State {
        let state = fold_declaration(declaration, initial_state);
        let fold_constructor_inner = |constructor: &LocatedConstructor, state: State| {
            constructor_utilities::fold(constructor, state, fold_kind, fold_constructor)
        };
        let fold_expression_inner = |expression: &LocatedExpression, state: State| {
            expression_utilities::fold(
                expression,
                state,
                fold_kind,
                fold_constructor,
                fold_expression,
            )
        };

        match &declaration.node {
            Declaration::Constructor(_, _, kind, constructor) => {
                let state = kind_utilities::fold(kind, state, fold_kind);
                fold_constructor_inner(constructor, state)
            }
            Declaration::Datatype(datatype_declarations) => {
                datatype_declarations
                    .iter()
                    .fold(state, |accumulator, datatype_declaration| {
                        datatype_declaration.constrs.iter().fold(
                            accumulator,
                            |inner_accumulator, (_, _, optional_constructor)| {
                                match optional_constructor {
                                    None => inner_accumulator,
                                    Some(constructor) => {
                                        fold_constructor_inner(constructor, inner_accumulator)
                                    }
                                }
                            },
                        )
                    })
            }
            Declaration::Val(_, _, type_annotation, expression, _) => {
                let state = fold_constructor_inner(type_annotation, state);
                fold_expression_inner(expression, state)
            }
            Declaration::ValRec(mutually_recursive_bindings) => {
                mutually_recursive_bindings.iter().fold(
                    state,
                    |accumulator, (_, _, type_annotation, expression, _)| {
                        let accumulator = fold_constructor_inner(type_annotation, accumulator);
                        fold_expression_inner(expression, accumulator)
                    },
                )
            }
            Declaration::Export(_, _, _)
            | Declaration::Sequence(_, _, _)
            | Declaration::Database(_)
            | Declaration::Style(_, _, _)
            | Declaration::OnError(_) => state,
            Declaration::Table {
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
                ..
            } => {
                let state = fold_constructor_inner(con, state);
                let state = fold_expression_inner(exp, state);
                let state = fold_constructor_inner(pk_con, state);
                let state = fold_expression_inner(pk_exp, state);
                fold_constructor_inner(unique_con, state)
            }
            Declaration::View(_, _, _, expression, constructor) => {
                let state = fold_expression_inner(expression, state);
                fold_constructor_inner(constructor, state)
            }
            Declaration::Index(first_expression, second_expression) => {
                let state = fold_expression_inner(first_expression, state);
                fold_expression_inner(second_expression, state)
            }
            Declaration::Cookie(_, _, constructor, _) => fold_constructor_inner(constructor, state),
            Declaration::Task(first_expression, second_expression) => {
                let state = fold_expression_inner(first_expression, state);
                fold_expression_inner(second_expression, state)
            }
            Declaration::Policy(policy_expression) => {
                fold_expression_inner(policy_expression, state)
            }
        }
    }

    /// Returns true if any sub-node of the declaration satisfies the corresponding predicate.
    ///
    /// # Arguments
    ///
    /// * `declaration` - The declaration to search.
    /// * `predicate_kind` - Returns true for a matching kind.
    /// * `predicate_constructor` - Returns true for a matching constructor.
    /// * `predicate_expression` - Returns true for a matching expression.
    /// * `predicate_declaration` - Returns true for a matching declaration node.
    ///
    /// # Returns
    ///
    /// True when any predicate returns true for at least one node (short-circuits).
    pub fn exists(
        declaration: &LocatedDeclaration,
        predicate_kind: &dyn Fn(&LocatedKind) -> bool,
        predicate_constructor: &dyn Fn(&LocatedConstructor) -> bool,
        predicate_expression: &dyn Fn(&LocatedExpression) -> bool,
        predicate_declaration: &dyn Fn(&LocatedDeclaration) -> bool,
    ) -> bool {
        if predicate_declaration(declaration) {
            return true;
        }
        let exists_constructor = |constructor: &LocatedConstructor| {
            constructor_utilities::exists(constructor, predicate_kind, predicate_constructor)
        };
        let exists_expression = |expression: &LocatedExpression| {
            expression_utilities::exists(
                expression,
                predicate_kind,
                predicate_constructor,
                predicate_expression,
            )
        };

        match &declaration.node {
            Declaration::Constructor(_, _, kind, constructor) => {
                kind_utilities::exists(kind, predicate_kind) || exists_constructor(constructor)
            }
            Declaration::Datatype(datatype_declarations) => {
                datatype_declarations.iter().any(|datatype_declaration| {
                    datatype_declaration
                        .constrs
                        .iter()
                        .any(|(_, _, optional_constructor)| {
                            optional_constructor
                                .as_ref()
                                .is_some_and(&exists_constructor)
                        })
                })
            }
            Declaration::Val(_, _, type_annotation, expression, _) => {
                exists_constructor(type_annotation) || exists_expression(expression)
            }
            Declaration::ValRec(mutually_recursive_bindings) => mutually_recursive_bindings
                .iter()
                .any(|(_, _, type_annotation, expression, _)| {
                    exists_constructor(type_annotation) || exists_expression(expression)
                }),
            Declaration::Export(_, _, _)
            | Declaration::Sequence(_, _, _)
            | Declaration::Database(_)
            | Declaration::Style(_, _, _)
            | Declaration::OnError(_) => false,
            Declaration::Table {
                con,
                exp,
                pk_con,
                pk_exp,
                unique_con,
                ..
            } => {
                exists_constructor(con)
                    || exists_expression(exp)
                    || exists_constructor(pk_con)
                    || exists_expression(pk_exp)
                    || exists_constructor(unique_con)
            }
            Declaration::View(_, _, _, expression, constructor) => {
                exists_expression(expression) || exists_constructor(constructor)
            }
            Declaration::Index(first_expression, second_expression)
            | Declaration::Task(first_expression, second_expression) => {
                exists_expression(first_expression) || exists_expression(second_expression)
            }
            Declaration::Cookie(_, _, constructor, _) => exists_constructor(constructor),
            Declaration::Policy(policy_expression) => exists_expression(policy_expression),
        }
    }
}

// ---------------------------------------------------------------------------
// file module
// ---------------------------------------------------------------------------

/// File-level utilities.
pub mod file {
    use super::*;

    /// Returns the maximum named identifier index used in the file (for allocating fresh ids).
    ///
    /// # Arguments
    ///
    /// * `declarations` - Slice of top-level declarations in the file.
    ///
    /// # Returns
    ///
    /// The maximum value among all named ids (Con, Val, ValRec, Table, Sequence, View, Cookie, Style, etc.).
    ///
    /// Mirrors `CoreUtil.File.maxName`.
    pub fn max_name(declarations: &[LocatedDeclaration]) -> usize {
        declarations
            .iter()
            .fold(0usize, |current_max, declaration| match &declaration.node {
                Declaration::Constructor(_, name_id, _, _) => current_max.max(*name_id),
                Declaration::Datatype(datatype_declarations) => datatype_declarations.iter().fold(
                    current_max,
                    |accumulator, datatype_declaration| {
                        let accumulator = accumulator.max(datatype_declaration.id);
                        datatype_declaration
                            .constrs
                            .iter()
                            .fold(accumulator, |inner_accumulator, (_, name_id, _)| {
                                inner_accumulator.max(*name_id)
                            })
                    },
                ),
                Declaration::Val(_, name_id, _, _, _) => current_max.max(*name_id),
                Declaration::ValRec(mutually_recursive_bindings) => mutually_recursive_bindings
                    .iter()
                    .fold(current_max, |accumulator, (_, name_id, _, _, _)| {
                        accumulator.max(*name_id)
                    }),
                Declaration::Export(_, _, _) => current_max,
                Declaration::Table { id, .. } => current_max.max(*id),
                Declaration::Sequence(_, name_id, _) => current_max.max(*name_id),
                Declaration::View(_, name_id, _, _, _) => current_max.max(*name_id),
                Declaration::Index(_, _) => current_max,
                Declaration::Database(_) => current_max,
                Declaration::Cookie(_, name_id, _, _) => current_max.max(*name_id),
                Declaration::Style(_, name_id, _) => current_max.max(*name_id),
                Declaration::Task(_, _) => current_max,
                Declaration::Policy(_) => current_max,
                Declaration::OnError(_) => current_max,
            })
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;

    #[test]
    fn classify_datatype_enum_all_nullary() {
        let xncs: Vec<(String, usize, Option<LocatedConstructor>)> = vec![
            ("A".into(), 0, None),
            ("B".into(), 1, None),
            ("C".into(), 2, None),
        ];
        assert_eq!(classify_datatype(&xncs), DatatypeKind::Enum);
    }

    #[test]
    fn classify_datatype_option_one_nullary_one_unary() {
        let unit = Located::dummy(Constructor::Unit);
        let xncs: Vec<(String, usize, Option<LocatedConstructor>)> =
            vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
        assert_eq!(classify_datatype(&xncs), DatatypeKind::Option);
    }

    #[test]
    fn classify_datatype_default_multiple_unary() {
        let unit = Located::dummy(Constructor::Unit);
        let xncs: Vec<(String, usize, Option<LocatedConstructor>)> = vec![
            ("A".into(), 0, Some(unit.clone())),
            ("B".into(), 1, Some(unit)),
        ];
        assert_eq!(classify_datatype(&xncs), DatatypeKind::Default);
    }

    /// Catches mutant: nullary==1 && unary==1 -> ||. (2 nullary, 1 unary) must be Default, not Option.
    #[test]
    fn classify_datatype_default_two_nullary_one_unary() {
        let unit = Located::dummy(Constructor::Unit);
        let xncs: Vec<(String, usize, Option<LocatedConstructor>)> = vec![
            ("A".into(), 0, None),
            ("B".into(), 1, None),
            ("C".into(), 2, Some(unit)),
        ];
        assert_eq!(classify_datatype(&xncs), DatatypeKind::Default);
    }

    #[test]
    fn kind_map_identity() {
        let k = Located::dummy(Kind::Arrow(
            Box::new(Located::dummy(Kind::Type)),
            Box::new(Located::dummy(Kind::Type)),
        ));
        let result = kind::map(k.clone(), &|x| x);
        assert!(matches!(result.node, Kind::Arrow(_, _)));
    }

    #[test]
    fn kind_fold_count() {
        let k = Located::dummy(Kind::Tuple(vec![
            Located::dummy(Kind::Type),
            Located::dummy(Kind::Unit),
        ]));
        let count = kind::fold(&k, 0usize, &|_k, acc| acc + 1);
        assert_eq!(count, 3); // root + Type + Unit
    }

    #[test]
    fn kind_exists_finds_rel() {
        let k = Located::dummy(Kind::Arrow(
            Box::new(Located::dummy(Kind::Rel(1))),
            Box::new(Located::dummy(Kind::Type)),
        ));
        assert!(kind::exists(&k, &|kr| matches!(kr.node, Kind::Rel(1))));
        assert!(!kind::exists(&k, &|kr| matches!(kr.node, Kind::Rel(99))));
    }

    #[test]
    fn kind_compare_ordering() {
        use std::cmp::Ordering;
        let t = Located::dummy(Kind::Type);
        let u = Located::dummy(Kind::Unit);
        assert_eq!(kind::compare(&t, &u), Ordering::Less);
        assert_eq!(kind::compare(&t, &t), Ordering::Equal);
        assert_eq!(kind::compare(&u, &t), Ordering::Greater);
    }

    /// Catches mutants: delete match arms, compare_list != -> ==.
    #[test]
    fn kind_compare_rel_and_tuple() {
        use std::cmp::Ordering;
        let r0 = Located::dummy(Kind::Rel(0));
        let r1 = Located::dummy(Kind::Rel(1));
        assert_eq!(kind::compare(&r0, &r1), Ordering::Less);
        assert_eq!(kind::compare(&r1, &r0), Ordering::Greater);
        let tuple_type = Located::dummy(Kind::Tuple(vec![Located::dummy(Kind::Type)]));
        let tuple_unit = Located::dummy(Kind::Tuple(vec![Located::dummy(Kind::Unit)]));
        assert_eq!(kind::compare(&tuple_type, &tuple_unit), Ordering::Less);
        let rec_type = Located::dummy(Kind::Record(Box::new(Located::dummy(Kind::Type))));
        let rec_unit = Located::dummy(Kind::Record(Box::new(Located::dummy(Kind::Unit))));
        assert_eq!(kind::compare(&rec_type, &rec_unit), Ordering::Less);
    }

    #[test]
    fn con_map_identity() {
        let c = Located::dummy(Constructor::Tuple(vec![
            Located::dummy(Constructor::Unit),
            Located::dummy(Constructor::Name("x".into())),
        ]));
        let result = constructor::map(c.clone(), &|k| k, &|c2| c2);
        assert!(matches!(result.node, Constructor::Tuple(_)));
    }

    #[test]
    fn con_fold_count() {
        let c = Located::dummy(Constructor::App(
            Box::new(Located::dummy(Constructor::Unit)),
            Box::new(Located::dummy(Constructor::Name("x".into()))),
        ));
        let count = constructor::fold(&c, 0usize, &|_k, acc| acc + 1, &|_c, acc| acc + 1);
        assert_eq!(count, 3); // App, Unit, Name
    }

    #[test]
    fn con_exists_finds_ffi() {
        let c = Located::dummy(Constructor::Ffi("M".into(), "T".into()));
        assert!(constructor::exists(
            &c,
            &|_| false,
            &|c| matches!(&c.node, Constructor::Ffi(m, t) if m == "M" && t == "T")
        ));
    }

    /// Catches mutant: exists -> true, || -> &&.
    #[test]
    fn con_exists_returns_false_when_absent() {
        let c = Located::dummy(Constructor::Unit);
        assert!(!constructor::exists(&c, &|_| false, &|c| matches!(
            &c.node,
            Constructor::Ffi(_, _)
        )));
        let nested = Located::dummy(Constructor::Tuple(vec![
            Located::dummy(Constructor::Unit),
            Located::dummy(Constructor::Name("x".into())),
        ]));
        assert!(!constructor::exists(&nested, &|_| false, &|c| matches!(
            &c.node,
            Constructor::Ffi(_, _)
        )));
    }

    /// Catches mutant: || -> && in TFun/App/Record branches (Ffi in right child only).
    #[test]
    fn con_exists_finds_ffi_in_right_branch() {
        let left = Located::dummy(Constructor::Unit);
        let right = Located::dummy(Constructor::Ffi("M".into(), "T".into()));
        let app = Located::dummy(Constructor::App(Box::new(left), Box::new(right)));
        assert!(constructor::exists(&app, &|_| false, &|c| matches!(
            &c.node,
            Constructor::Ffi(_, _)
        )));
    }

    #[test]
    fn con_compare_ordering() {
        use std::cmp::Ordering;
        let u = Located::dummy(Constructor::Unit);
        let n = Located::dummy(Constructor::Name("x".into()));
        // Name (disc 8) < Unit (disc 12)
        assert_eq!(constructor::compare(&n, &u), Ordering::Less);
        assert_eq!(constructor::compare(&u, &u), Ordering::Equal);
    }

    /// Catches mutants: delete match arms, compare_list/compare_pair_list != -> ==.
    #[test]
    fn con_compare_same_variant_different_content() {
        use std::cmp::Ordering;
        let na = Located::dummy(Constructor::Name("a".into()));
        let nb = Located::dummy(Constructor::Name("b".into()));
        assert_eq!(constructor::compare(&na, &nb), Ordering::Less);
        let ffi_m = Located::dummy(Constructor::Ffi("M".into(), "T".into()));
        let ffi_n = Located::dummy(Constructor::Ffi("N".into(), "U".into()));
        assert_eq!(constructor::compare(&ffi_m, &ffi_n), Ordering::Less);
        let t1 = Located::dummy(Constructor::Tuple(vec![Located::dummy(Constructor::Unit)]));
        let t2 = Located::dummy(Constructor::Tuple(vec![
            Located::dummy(Constructor::Unit),
            Located::dummy(Constructor::Unit),
        ]));
        assert_eq!(constructor::compare(&t1, &t2), Ordering::Less);
    }

    #[test]
    fn exp_map_identity() {
        let e = Located::dummy(Expression::App(
            Box::new(Located::dummy(Expression::Prim(
                crate::primitives::Prim::Int(0),
            ))),
            Box::new(Located::dummy(Expression::Prim(
                crate::primitives::Prim::Int(1),
            ))),
        ));
        let result = expression::map(e.clone(), &|k| k, &|c| c, &|e2| e2);
        assert!(matches!(result.node, Expression::App(_, _)));
    }

    #[test]
    fn exp_exists_finds_named() {
        let e = Located::dummy(Expression::Named(42));
        assert!(expression::exists(
            &e,
            &|_| false,
            &|_| false,
            &|e2| matches!(e2.node, Expression::Named(42))
        ));
    }

    /// Catches mutant: exists -> true, || -> &&.
    #[test]
    fn exp_exists_returns_false_when_absent() {
        let e = Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0)));
        assert!(!expression::exists(
            &e,
            &|_| false,
            &|_| false,
            &|e2| matches!(e2.node, Expression::Named(_))
        ));
        let app = Located::dummy(Expression::App(
            Box::new(Located::dummy(Expression::Prim(
                crate::primitives::Prim::Int(0),
            ))),
            Box::new(Located::dummy(Expression::Prim(
                crate::primitives::Prim::Int(1),
            ))),
        ));
        assert!(!expression::exists(
            &app,
            &|_| false,
            &|_| false,
            &|e2| matches!(e2.node, Expression::Named(_))
        ));
    }

    /// Catches mutant: || -> && in App/Abs/Let branches (Named in right child only).
    #[test]
    fn exp_exists_finds_named_in_right_branch() {
        let left = Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0)));
        let right = Located::dummy(Expression::Named(99));
        let app = Located::dummy(Expression::App(Box::new(left), Box::new(right)));
        assert!(expression::exists(
            &app,
            &|_| false,
            &|_| false,
            &|e2| matches!(e2.node, Expression::Named(99))
        ));
    }

    /// Catches mutant: declaration::exists -> true/false, || -> &&.
    #[test]
    fn declaration_exists_true_and_false() {
        let span = crate::error_types::Span::dummy();
        let val_decl = Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
                "".into(),
            ),
            span.clone(),
        );
        assert!(declaration::exists(
            &val_decl,
            &|_| false,
            &|_| false,
            &|e| matches!(e.node, Expression::Prim(_)),
            &|_| false,
        ));
        let export_decl = Located::new(
            Declaration::Export(
                crate::export::ExportKind::Link(crate::export::Effect::ReadOnly),
                0,
                false,
            ),
            span,
        );
        assert!(!declaration::exists(
            &export_decl,
            &|_| false,
            &|_| false,
            &|_| false,
            &|_| false,
        ));
    }

    /// Catches mutant: pat_binders_for_ctx returns vec![]. map_b Case must extend ctx with pattern binders.
    #[test]
    fn exp_map_b_case_arm_ctx_has_binders() {
        use crate::primitives::Prim;
        let ty = Located::dummy(Constructor::Unit);
        let disc = Located::dummy(Expression::Rel(0));
        let pat = Located::dummy(Pattern::Var("x".into(), ty.clone()));
        let arm_rhs = Located::dummy(Expression::Rel(0));
        let case_meta = crate::core::CaseMeta {
            disc: ty.clone(),
            result: ty,
        };
        let case_exp = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(pat, arm_rhs)],
            case_meta,
        ));
        let mut ctx = vec![];
        let result = expression::map_b(case_exp, &mut ctx, &|_, k| k, &|_, c| c, &|ctx, e| {
            if ctx.len() == 1 {
                Located::dummy(Expression::Prim(Prim::Int(999)))
            } else {
                e
            }
        });
        let Expression::Case(_, arms, _) = &result.node else {
            panic!("expected Case")
        };
        assert!(
            matches!(arms[0].1.node, Expression::Prim(Prim::Int(999))),
            "Case arm body must be mapped with pattern binder in ctx (pat_binders_for_ctx)"
        );
    }

    /// Catches mutant: || -> && in Declaration::Table (pk_con vs exp).
    /// Catches mutant: collect_pat_binders_fold. Case arm context must include pattern binders.
    #[test]
    fn exp_fold_b_case_arm_ctx_has_binders() {
        let ty = Located::dummy(Constructor::Unit);
        let disc = Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0)));
        let pat = Located::dummy(Pattern::Var("x".into(), ty.clone()));
        let arm_rhs = Located::dummy(Expression::Rel(0));
        let case_meta = crate::core::CaseMeta {
            disc: Located::dummy(Constructor::Unit),
            result: ty.clone(),
        };
        let case_exp = Located::dummy(Expression::Case(
            Box::new(disc),
            vec![(pat, arm_rhs)],
            case_meta,
        ));
        let total_ctx_len: usize = expression::fold_b(
            &case_exp,
            &[],
            0usize,
            &|_, _, s| s,
            &|_, _, s| s,
            &|ctx, _e, s| s + ctx.len(),
        );
        assert!(
            total_ctx_len >= 1,
            "Case arm RHS must see binder from Var pattern"
        );
    }

    #[test]
    fn declaration_exists_con_kind_only() {
        let span = crate::error_types::Span::dummy();
        let k = Located::dummy(Kind::Rel(5));
        let d = Located::new(
            Declaration::Constructor("T".into(), 1, k, Located::dummy(Constructor::Unit)),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|kr| matches!(kr.node, Kind::Rel(5)),
            &|_| false,
            &|_| false,
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_con_c_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Constructor(
                "T".into(),
                1,
                Located::dummy(Kind::Type),
                Located::dummy(Constructor::Unit),
            ),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|c| matches!(&c.node, Constructor::Unit),
            &|_| false,
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_valrec_ty_only() {
        let span = crate::error_types::Span::dummy();
        let ty = Located::dummy(Constructor::Unit);
        let d = Located::new(
            Declaration::ValRec(vec![(
                "x".into(),
                1,
                ty,
                Located::dummy(Expression::Rel(0)),
                "".into(),
            )]),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|c| matches!(&c.node, Constructor::Unit),
            &|_| false,
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_valrec_e_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::ValRec(vec![(
                "x".into(),
                1,
                Located::dummy(Constructor::Named(1)),
                Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
                "".into(),
            )]),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|_| false,
            &|e| matches!(e.node, Expression::Prim(_)),
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_table_con_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Table {
                sql_name: "t".into(),
                id: 1,
                con: Located::dummy(Constructor::Unit),
                sql_con: "".into(),
                exp: Located::dummy(Expression::Named(1)),
                pk_con: Located::dummy(Constructor::Named(1)),
                pk_exp: Located::dummy(Expression::Named(2)),
                unique_con: Located::dummy(Constructor::Named(3)),
            },
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|c| matches!(&c.node, Constructor::Unit),
            &|_| false,
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_table_exp_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Table {
                sql_name: "t".into(),
                id: 1,
                con: Located::dummy(Constructor::Named(1)),
                sql_con: "".into(),
                exp: Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
                pk_con: Located::dummy(Constructor::Named(1)),
                pk_exp: Located::dummy(Expression::Named(2)),
                unique_con: Located::dummy(Constructor::Named(3)),
            },
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|_| false,
            &|e| matches!(e.node, Expression::Prim(_)),
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_table_unique_con_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Table {
                sql_name: "t".into(),
                id: 1,
                con: Located::dummy(Constructor::Named(1)),
                sql_con: "".into(),
                exp: Located::dummy(Expression::Named(1)),
                pk_con: Located::dummy(Constructor::Named(1)),
                pk_exp: Located::dummy(Expression::Named(2)),
                unique_con: Located::dummy(Constructor::Unit),
            },
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|c| matches!(&c.node, Constructor::Unit),
            &|_| false,
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_view_e_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::View(
                "v".into(),
                1,
                "".into(),
                Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
                Located::dummy(Constructor::Named(1)),
            ),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|_| false,
            &|e| matches!(e.node, Expression::Prim(_)),
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_view_c_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::View(
                "v".into(),
                1,
                "".into(),
                Located::dummy(Expression::Rel(0)),
                Located::dummy(Constructor::Unit),
            ),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|c| matches!(&c.node, Constructor::Unit),
            &|_| false,
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_index_e1_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Index(
                Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
                Located::dummy(Expression::Rel(0)),
            ),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|_| false,
            &|e| matches!(e.node, Expression::Prim(_)),
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_index_e2_only() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Index(
                Located::dummy(Expression::Rel(0)),
                Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
            ),
            span,
        );
        assert!(declaration::exists(
            &d,
            &|_| false,
            &|_| false,
            &|e| matches!(e.node, Expression::Prim(_)),
            &|_| false,
        ));
    }

    #[test]
    fn declaration_exists_in_table_pk_exp() {
        let span = crate::error_types::Span::dummy();
        let table = Located::new(
            Declaration::Table {
                sql_name: "t".into(),
                id: 1,
                con: Located::dummy(Constructor::Unit),
                sql_con: "".into(),
                exp: Located::dummy(Expression::Prim(crate::primitives::Prim::Int(0))),
                pk_con: Located::dummy(Constructor::Unit),
                pk_exp: Located::dummy(Expression::Named(1)),
                unique_con: Located::dummy(Constructor::Unit),
            },
            span,
        );
        assert!(declaration::exists(
            &table,
            &|_| false,
            &|_| false,
            &|e| matches!(e.node, Expression::Named(1)),
            &|_| false,
        ));
    }

    #[test]
    fn file_max_name_empty() {
        assert_eq!(file::max_name(&[]), 0);
    }

    #[test]
    fn file_max_name_from_con() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Constructor(
                "T".into(),
                100,
                Located::dummy(Kind::Type),
                Located::dummy(Constructor::Unit),
            ),
            span,
        );
        assert_eq!(file::max_name(&[d]), 100);
    }

    #[test]
    fn file_max_name_from_datatype() {
        let span = crate::error_types::Span::dummy();
        let d = Located::new(
            Declaration::Datatype(vec![crate::core::DatatypeDecl {
                name: "T".into(),
                id: 10,
                params: vec![],
                constrs: vec![("C".into(), 99, None)],
            }]),
            span,
        );
        assert_eq!(file::max_name(&[d]), 99);
    }
}
