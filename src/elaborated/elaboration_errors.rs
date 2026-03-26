//! Elaboration error types and reporting.
//!
//! Translated from `elab_err.sml`.
//!
//! Each `compile_error_from_*` mapper turns a structured error enum into a [`CompileError`] (spans preserved
//! where the underlying AST carries them). [`format_kind_unification_failure`] and nested
//! [`compile_error_from_constructor_unification_failure`] produce human-readable text for embedding in larger
//! diagnostics.

use crate::elaborated::{
    LocatedConstructor, LocatedDeclaration, LocatedExpression, LocatedKind, LocatedPattern,
    LocatedSignature, LocatedSignatureItem,
};
use crate::error_types::{CompileError, Span};

// ---------------------------------------------------------------------------
// Kind errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum KindElaborationError {
    UnboundKindVariable(Span, String),
    WildcardDisallowedInSignature(Span),
}

/// Map a [`KindElaborationError`] to a [`CompileError`] at the appropriate span.
///
/// # Arguments
///
/// * `kind_elaboration_error` — Structured kind error from elaboration.
///
/// # Returns
///
/// [`CompileError::at`] (or equivalent) with user-facing text.
pub fn compile_error_from_kind_elaboration_error(
    kind_elaboration_error: &KindElaborationError,
) -> CompileError {
    match kind_elaboration_error {
        KindElaborationError::UnboundKindVariable(source_span, variable_name) => CompileError::at(
            source_span.clone(),
            format!("Unbound kind variable:  {}", variable_name),
        ),
        KindElaborationError::WildcardDisallowedInSignature(source_span) => {
            CompileError::at(source_span.clone(), "Wildcard not allowed in signature")
        }
    }
}

// ---------------------------------------------------------------------------
// Kind unification errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum KindUnificationFailure {
    OccursCheckFailed(LocatedKind, LocatedKind),
    IncompatibleKinds(LocatedKind, LocatedKind),
    ScopePreventsUnification(LocatedKind, LocatedKind),
}

/// Short English explanation of a [`KindUnificationFailure`] for nested messages (not a [`CompileError`] alone).
///
/// # Arguments
///
/// * `failure` — Kind unification failure.
///
/// # Returns
///
/// Single-line summary (uses `Debug` of kind nodes; for diagnostics only).
pub fn format_kind_unification_failure(failure: &KindUnificationFailure) -> String {
    match failure {
        KindUnificationFailure::OccursCheckFailed(found_kind, expected_kind) => {
            format!(
                "Kind occurs check failed: {:?} vs {:?}",
                found_kind.node, expected_kind.node
            )
        }
        KindUnificationFailure::IncompatibleKinds(found_kind, expected_kind) => {
            format!(
                "Incompatible kinds: {:?} vs {:?}",
                found_kind.node, expected_kind.node
            )
        }
        KindUnificationFailure::ScopePreventsUnification(first_kind, second_kind) => {
            format!(
                "Scoping prevents kind unification: {:?} vs {:?}",
                first_kind.node, second_kind.node
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum ConstructorElaborationError {
    UnboundConstructorVariable(Span, String),
    UnboundDatatypeName(Span, String),
    UnboundStructureReference(Span, String),
    ConstructorWrongKind(
        LocatedConstructor,
        LocatedKind,
        LocatedKind,
        KindUnificationFailure,
    ),
    DuplicateRecordFieldName(Span, String),
    ProjectionIndexOutOfBounds(LocatedConstructor, usize),
    ProjectionKindMismatch(LocatedConstructor, LocatedKind),
    ConstructorWildcardDisallowedInSignature(Span),
}

/// Map a [`ConstructorElaborationError`] to [`CompileError`].
///
/// # Arguments
///
/// * `constructor_elaboration_error` — Structured constructor error.
///
/// # Returns
///
/// Diagnostic with span taken from the offending node or explicit [`Span`] in `constructor_elaboration_error`.
pub fn compile_error_from_constructor_elaboration_error(
    constructor_elaboration_error: &ConstructorElaborationError,
) -> CompileError {
    match constructor_elaboration_error {
        ConstructorElaborationError::UnboundConstructorVariable(source_span, variable_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Unbound constructor variable:  {}", variable_name),
            )
        }
        ConstructorElaborationError::UnboundDatatypeName(source_span, datatype_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Unbound datatype:  {}", datatype_name),
            )
        }
        ConstructorElaborationError::UnboundStructureReference(source_span, structure_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Unbound structure:  {}", structure_name),
            )
        }
        ConstructorElaborationError::ConstructorWrongKind(
            constructor,
            found_kind,
            expected_kind,
            kind_failure,
        ) => {
            let message = format!(
                "Wrong kind; have {:?}, need {:?}; {}",
                found_kind.node,
                expected_kind.node,
                format_kind_unification_failure(kind_failure)
            );
            CompileError::at(constructor.span.clone(), message)
        }
        ConstructorElaborationError::DuplicateRecordFieldName(source_span, field_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Duplicate record field:  {}", field_name),
            )
        }
        ConstructorElaborationError::ProjectionIndexOutOfBounds(constructor, projection_index) => {
            CompileError::at(
                constructor.span.clone(),
                format!(
                    "Out of bounds constructor projection (index {})",
                    projection_index
                ),
            )
        }
        ConstructorElaborationError::ProjectionKindMismatch(constructor, kind) => CompileError::at(
            constructor.span.clone(),
            format!(
                "Projection from non-tuple constructor (kind {:?})",
                kind.node
            ),
        ),
        ConstructorElaborationError::ConstructorWildcardDisallowedInSignature(source_span) => {
            CompileError::at(source_span.clone(), "Wildcard not allowed in signature")
        }
    }
}

// ---------------------------------------------------------------------------
// Constructor unification errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum ConstructorUnificationFailure {
    NestedKindUnificationFailure(LocatedKind, LocatedKind, KindUnificationFailure),
    ConstructorOccursCheckFailed(LocatedConstructor, LocatedConstructor),
    IncompatibleConstructors(LocatedConstructor, LocatedConstructor),
    TypeFunctionExplicitnessMismatch(LocatedConstructor, LocatedConstructor),
    UnexpectedKindForKindofQuery(LocatedKind, LocatedConstructor, String),
    RecordConstructorUnificationFailure(
        LocatedConstructor,
        LocatedConstructor,
        Option<(
            LocatedConstructor,
            LocatedConstructor,
            LocatedConstructor,
            Option<Box<ConstructorUnificationFailure>>,
        )>,
    ),
    SuspendedLiftingClash(Span, Span),
    SubstitutionBlockedByDeepUnification(LocatedConstructor, LocatedConstructor),
    UnificationLiftingTooDeep,
    ScopePreventsConstructorUnification(LocatedConstructor, LocatedConstructor),
}

/// Map constructor unification failure to [`CompileError`] ([`CompileError::Plain`] when no single span fits).
///
/// Nested [`ConstructorUnificationFailure`] values in [`ConstructorUnificationFailure::RecordConstructorUnificationFailure`]
/// stringify via this function.
///
/// # Arguments
///
/// * `failure` — Unification failure from [`crate::elaborated::elaborate::unify_cons`] or related logic.
///
/// # Returns
///
/// Printable compiler error (may embed sub-messages from [`format_kind_unification_failure`]).
pub fn compile_error_from_constructor_unification_failure(
    failure: &ConstructorUnificationFailure,
) -> CompileError {
    match failure {
        ConstructorUnificationFailure::NestedKindUnificationFailure(
            found_kind,
            expected_kind,
            kind_failure,
        ) => {
            let message = format!(
                "Kind unification failure: have {:?}, need {:?}; {}",
                found_kind.node,
                expected_kind.node,
                format_kind_unification_failure(kind_failure)
            );
            CompileError::Plain(message)
        }
        ConstructorUnificationFailure::ConstructorOccursCheckFailed(left, right) => {
            CompileError::Plain(format!(
                "Constructor occurs check failed: {:?} vs {:?}",
                left.node, right.node
            ))
        }
        ConstructorUnificationFailure::IncompatibleConstructors(left, right) => {
            CompileError::Plain(format!(
                "Incompatible constructors: {:?} vs {:?}",
                left.node, right.node
            ))
        }
        ConstructorUnificationFailure::TypeFunctionExplicitnessMismatch(left, right) => {
            CompileError::Plain(format!(
                "Differing constructor function explicitness: {:?} vs {:?}",
                left.node, right.node
            ))
        }
        ConstructorUnificationFailure::UnexpectedKindForKindofQuery(
            kind,
            constructor,
            expectation,
        ) => {
            CompileError::Plain(format!(
                "Unexpected kind for kindof calculation (expecting {}): kind {:?}, con {:?}",
                expectation, kind.node, constructor.node
            ))
        }
        ConstructorUnificationFailure::RecordConstructorUnificationFailure(
            left_record,
            right_record,
            field_detail,
        ) => {
            let base = format!(
                "Can't unify record constructors: {:?} vs {:?}",
                left_record.node, right_record.node
            );
            let detail = if let Some((
                field_name_constructor,
                left_field_type,
                right_field_type,
                nested_failure,
            )) = field_detail
            {
                let field_message = format!(
                    "; field {:?}: {:?} vs {:?}",
                    field_name_constructor.node, left_field_type.node, right_field_type.node
                );
                let nested_message = if let Some(inner) = nested_failure {
                    format!(
                        "; {}",
                        compile_error_from_constructor_unification_failure(inner)
                    )
                } else {
                    String::new()
                };
                format!("{}{}", field_message, nested_message)
            } else {
                String::new()
            };
            CompileError::Plain(format!("{}{}", base, detail))
        }
        ConstructorUnificationFailure::SuspendedLiftingClash(first_span, second_span) => {
            CompileError::at(
                first_span.clone(),
                format!(
                    "Can't unify two unification variables that both have suspended liftings; other location: {}",
                    second_span
                ),
            )
        }
        ConstructorUnificationFailure::SubstitutionBlockedByDeepUnification(head, body) => {
            CompileError::at(
                head.span.clone(),
                format!(
                    "Substitution in constructor is blocked by a too-deep unification variable; body: {:?}",
                    body.node
                ),
            )
        }
        ConstructorUnificationFailure::UnificationLiftingTooDeep => CompileError::Plain(
            "Can't reverse-engineer unification variable lifting".to_string(),
        ),
        ConstructorUnificationFailure::ScopePreventsConstructorUnification(left, right) => {
            CompileError::Plain(format!(
                "Scoping prevents constructor unification: {:?} vs {:?}",
                left.node, right.node
            ))
        }
    }
}

// ---------------------------------------------------------------------------
// Expression errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum ExpressionElaborationError {
    UnboundExpressionVariable(Span, String),
    UnboundStructureInExpression(Span, String),
    ExpressionUnificationFailure(
        LocatedExpression,
        LocatedConstructor,
        LocatedConstructor,
        ConstructorUnificationFailure,
    ),
    UnificationVariableObstructsOperation(String, Span, LocatedConstructor),
    ExpressionWrongForm(String, LocatedExpression, LocatedConstructor),
    IncompatibleConstructors(LocatedConstructor, LocatedConstructor),
    DuplicatePatternVariable(Span, String),
    PatternUnificationFailure(
        LocatedPattern,
        LocatedConstructor,
        LocatedConstructor,
        ConstructorUnificationFailure,
    ),
    UnboundQualifiedConstructor(Span, Vec<String>, String),
    PatternConstructorGivenArgumentButExpectsNone(Span),
    PatternConstructorExpectsArgumentButNoneGiven(Span),
    InexhaustiveCaseAnalysis(Span, LocatedPattern),
    DuplicatePatternRecordField(Span, String),
    UnresolvableTypeClassInstance(Span, LocatedConstructor),
    TypeClassWildcardOutOfContext(Span, Option<(LocatedExpression, LocatedConstructor)>),
    IllegalRecursiveValueBinding(String, LocatedExpression),
}

/// Map an [`ExpressionElaborationError`] to [`CompileError`].
///
/// # Arguments
///
/// * `expression_error` — Pattern, unification, or binding error arising in [`crate::elaborated::elaborate::elab_exp`].
///
/// # Returns
///
/// Diagnostic at expression or pattern span; includes [`compile_error_from_constructor_unification_failure`]
/// when a [`ConstructorUnificationFailure`] is attached.
pub fn compile_error_from_expression_elaboration_error(
    expression_error: &ExpressionElaborationError,
) -> CompileError {
    match expression_error {
        ExpressionElaborationError::UnboundExpressionVariable(source_span, variable_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Unbound expression variable:  {}", variable_name),
            )
        }
        ExpressionElaborationError::UnboundStructureInExpression(source_span, structure_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Unbound structure:  {}", structure_name),
            )
        }
        ExpressionElaborationError::ExpressionUnificationFailure(
            expression,
            inferred_constructor,
            expected_constructor,
            unification_failure,
        ) => {
            let message = format!(
                "Unification failure; have con {:?}, need con {:?}; {}",
                inferred_constructor.node,
                expected_constructor.node,
                compile_error_from_constructor_unification_failure(unification_failure)
            );
            CompileError::at(expression.span.clone(), message)
        }
        ExpressionElaborationError::UnificationVariableObstructsOperation(
            operation_description,
            source_span,
            _blocking_constructor,
        ) => CompileError::at(
            source_span.clone(),
            format!("Unification variable blocks {}", operation_description),
        ),
        ExpressionElaborationError::ExpressionWrongForm(expected_form_name, expression, _type) => {
            CompileError::at(
                expression.span.clone(),
                format!("Expression is not a {}", expected_form_name),
            )
        }
        ExpressionElaborationError::IncompatibleConstructors(left, right) => CompileError::at(
            left.span.clone(),
            format!(
                "Incompatible constructors: {:?} vs {:?}",
                left.node, right.node
            ),
        ),
        ExpressionElaborationError::DuplicatePatternVariable(source_span, variable_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Duplicate pattern variable:  {}", variable_name),
            )
        }
        ExpressionElaborationError::PatternUnificationFailure(
            pattern,
            inferred_constructor,
            expected_constructor,
            unification_failure,
        ) => {
            let message = format!(
                "Unification failure for pattern; have con {:?}, need con {:?}; {}",
                inferred_constructor.node,
                expected_constructor.node,
                compile_error_from_constructor_unification_failure(unification_failure)
            );
            CompileError::at(pattern.span.clone(), message)
        }
        ExpressionElaborationError::UnboundQualifiedConstructor(
            source_span,
            module_path,
            constructor_name,
        ) => {
            let full_qualifier = {
                let mut path_components = module_path.clone();
                path_components.push(constructor_name.clone());
                path_components.join(".")
            };
            CompileError::at(
                source_span.clone(),
                format!("Unbound constructor {} in pattern", full_qualifier),
            )
        }
        ExpressionElaborationError::PatternConstructorGivenArgumentButExpectsNone(source_span) => {
            CompileError::at(
                source_span.clone(),
                "Constructor expects no argument but is used with argument",
            )
        }
        ExpressionElaborationError::PatternConstructorExpectsArgumentButNoneGiven(source_span) => {
            CompileError::at(
                source_span.clone(),
                "Constructor expects argument but is used with no argument",
            )
        }
        ExpressionElaborationError::InexhaustiveCaseAnalysis(source_span, pattern) => {
            CompileError::at(
                source_span.clone(),
                format!("Inexhaustive 'case'; missed case: {:?}", pattern.node),
            )
        }
        ExpressionElaborationError::DuplicatePatternRecordField(source_span, field_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Duplicate record field {} in pattern", field_name),
            )
        }
        ExpressionElaborationError::UnresolvableTypeClassInstance(
            source_span,
            class_constraint,
        ) => CompileError::at(
            source_span.clone(),
            format!(
                "Can't resolve type class instance; class constraint: {:?}",
                class_constraint.node
            ),
        ),
        ExpressionElaborationError::TypeClassWildcardOutOfContext(
            source_span,
            optional_context,
        ) => {
            let detail = if let Some((function_expression, function_type)) = optional_context {
                format!(
                    "; function: {:?}, type: {:?}",
                    function_expression.node, function_type.node
                )
            } else {
                String::new()
            };
            CompileError::at(
                source_span.clone(),
                format!("Type class wildcard occurs out of context{}", detail),
            )
        }
        ExpressionElaborationError::IllegalRecursiveValueBinding(
            bound_variable_name,
            right_hand_side,
        ) => CompileError::at(
            right_hand_side.span.clone(),
            format!(
                "Illegal 'val rec' righthand side (must be a function abstraction); variable: {}",
                bound_variable_name
            ),
        ),
    }
}

// ---------------------------------------------------------------------------
// Declaration errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum DeclarationElaborationError {
    KindUnifiersRemainUndetermined(Box<Vec<LocatedDeclaration>>),
    ConstructorUnifiersRemainUndetermined(Box<Vec<LocatedDeclaration>>),
    NonStrictlyPositiveDeclaration(LocatedDeclaration),
    TypeHoleFound(LocatedConstructor),
}

fn declarations_fallback_span(declarations: &[LocatedDeclaration]) -> Span {
    declarations
        .first()
        .map(|declaration| declaration.span.clone())
        .unwrap_or_else(Span::dummy)
}

/// Map declaration-hygiene errors to [`CompileError`].
///
/// # Arguments
///
/// * `declaration_error` — Post-elaboration declaration problem.
///
/// # Returns
///
/// [`CompileError::at`] for list-based issues; [`DeclarationElaborationError::TypeHoleFound`] uses
/// [`CompileError::Plain`] with constructor debug.
pub fn compile_error_from_declaration_elaboration_error(
    declaration_error: &DeclarationElaborationError,
) -> CompileError {
    match declaration_error {
        DeclarationElaborationError::KindUnifiersRemainUndetermined(declarations) => {
            CompileError::at(
                declarations_fallback_span(declarations),
                "Some kind unification variables are undetermined in declaration\n(look for them as \"<UNIF:...>\")",
            )
        }
        DeclarationElaborationError::ConstructorUnifiersRemainUndetermined(declarations) => {
            CompileError::at(
                declarations_fallback_span(declarations),
                "Some constructor unification variables are undetermined in declaration\n(look for them as \"<UNIF:...>\")",
            )
        }
        DeclarationElaborationError::NonStrictlyPositiveDeclaration(declaration) => {
            CompileError::at(
                declaration.span.clone(),
                "Non-strictly-positive datatype declaration (could allow non-termination)",
            )
        }
        DeclarationElaborationError::TypeHoleFound(constructor) => CompileError::Plain(format!(
            "Hole found with type: {:?}",
            constructor.node
        )),
    }
}

// ---------------------------------------------------------------------------
// Signature errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum SignatureElaborationError {
    UnboundSignatureName(Span, String),
    UnmatchedSignatureItem(Span, LocatedSignatureItem),
    SignatureItemKindUnificationFailed(
        Span,
        LocatedSignatureItem,
        LocatedKind,
        LocatedSignatureItem,
        LocatedKind,
        KindUnificationFailure,
    ),
    SignatureItemConstructorUnificationFailed(
        Span,
        LocatedSignatureItem,
        LocatedConstructor,
        LocatedSignatureItem,
        LocatedConstructor,
        ConstructorUnificationFailure,
    ),
    SignatureItemDatatypeSpecificationsMismatch(
        Span,
        LocatedSignatureItem,
        LocatedSignatureItem,
        Option<(
            LocatedConstructor,
            LocatedConstructor,
            ConstructorUnificationFailure,
        )>,
    ),
    IncompatibleSignatureShapes(Span, LocatedSignature, LocatedSignature),
    WhereClauseFieldUnavailable(LocatedSignature, String),
    WhereClauseKindMismatch(LocatedKind, LocatedKind, KindUnificationFailure),
    SignatureNotValidForInclude(LocatedSignature),
    DuplicateConstructorNameInSignature(Span, String),
    DuplicateValueNameInSignature(Span, String),
    DuplicateNestedSignatureName(Span, String),
    DuplicateStructureNameInSignature(Span, String),
    SignatureNotValidForOpenConstraints(LocatedSignature),
}

/// Map signature matching / `where` / duplicate-item errors to [`CompileError`].
///
/// # Arguments
///
/// * `signature_error` — Subtyping or signature elaboration problem.
///
/// # Returns
///
/// Diagnostic; may embed [`format_kind_unification_failure`] or [`compile_error_from_constructor_unification_failure`].
pub fn compile_error_from_signature_elaboration_error(
    signature_error: &SignatureElaborationError,
) -> CompileError {
    match signature_error {
        SignatureElaborationError::UnboundSignatureName(source_span, name) => CompileError::at(
            source_span.clone(),
            format!("Unbound signature variable:  {}", name),
        ),
        SignatureElaborationError::UnmatchedSignatureItem(source_span, item) => CompileError::at(
            source_span.clone(),
            format!("Unmatched signature item: {:?}", item.node),
        ),
        SignatureElaborationError::SignatureItemKindUnificationFailed(
            source_span,
            actual_item,
            actual_kind,
            expected_item,
            expected_kind,
            kind_failure,
        ) => CompileError::at(
            source_span.clone(),
            format!(
                "Kind unification failure in signature matching: have {:?} (kind {:?}), need {:?} (kind {:?}); {}",
                actual_item.node,
                actual_kind.node,
                expected_item.node,
                expected_kind.node,
                format_kind_unification_failure(kind_failure)
            ),
        ),
        SignatureElaborationError::SignatureItemConstructorUnificationFailed(
            source_span,
            actual_item,
            actual_constructor,
            expected_item,
            expected_constructor,
            constructor_failure,
        ) => CompileError::at(
            source_span.clone(),
            format!(
                "Constructor unification failure in signature matching: have {:?} (con {:?}), need {:?} (con {:?}); {}",
                actual_item.node,
                actual_constructor.node,
                expected_item.node,
                expected_constructor.node,
                compile_error_from_constructor_unification_failure(constructor_failure)
            ),
        ),
        SignatureElaborationError::SignatureItemDatatypeSpecificationsMismatch(
            source_span,
            first_item,
            second_item,
            optional_unification_detail,
        ) => {
            let detail = if let Some((
                left_constructor,
                right_constructor,
                unification_failure,
            )) = optional_unification_detail
            {
                format!(
                    "; unification error: {:?} vs {:?}; {}",
                    left_constructor.node,
                    right_constructor.node,
                    compile_error_from_constructor_unification_failure(unification_failure)
                )
            } else {
                String::new()
            };
            CompileError::at(
                source_span.clone(),
                format!(
                    "Mismatched 'datatype' specifications: {:?} vs {:?}{}",
                    first_item.node, second_item.node, detail
                ),
            )
        }
        SignatureElaborationError::IncompatibleSignatureShapes(
            source_span,
            left_signature,
            right_signature,
        ) => CompileError::at(
            source_span.clone(),
            format!(
                "Incompatible signatures: {:?} vs {:?}",
                left_signature.node, right_signature.node
            ),
        ),
        SignatureElaborationError::WhereClauseFieldUnavailable(signature, field_name) => {
            CompileError::at(
                signature.span.clone(),
                format!("Unavailable field for 'where': {}", field_name),
            )
        }
        SignatureElaborationError::WhereClauseKindMismatch(
            found_kind,
            expected_kind,
            kind_failure,
        ) => CompileError::at(
            found_kind.span.clone(),
            format!(
                "Wrong kind for 'where': have {:?}, need {:?}; {}",
                found_kind.node,
                expected_kind.node,
                format_kind_unification_failure(kind_failure)
            ),
        ),
        SignatureElaborationError::SignatureNotValidForInclude(signature) => CompileError::at(
            signature.span.clone(),
            "Invalid signature to 'include'",
        ),
        SignatureElaborationError::DuplicateConstructorNameInSignature(source_span, name) => {
            CompileError::at(
                source_span.clone(),
                format!("Duplicate constructor {} in signature", name),
            )
        }
        SignatureElaborationError::DuplicateValueNameInSignature(source_span, name) => {
            CompileError::at(
                source_span.clone(),
                format!("Duplicate value {} in signature", name),
            )
        }
        SignatureElaborationError::DuplicateNestedSignatureName(source_span, name) => {
            CompileError::at(
                source_span.clone(),
                format!("Duplicate signature {} in signature", name),
            )
        }
        SignatureElaborationError::DuplicateStructureNameInSignature(source_span, name) => {
            CompileError::at(
                source_span.clone(),
                format!("Duplicate structure {} in signature", name),
            )
        }
        SignatureElaborationError::SignatureNotValidForOpenConstraints(signature) => {
            CompileError::at(
                signature.span.clone(),
                "Invalid signature for 'open constraints'",
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Structure errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub enum StructureElaborationError {
    UnboundStructureVariable(Span, String),
    AppliedNonFunctor(LocatedSignature),
    FunctorRebindingAttempt(Span),
    StructureNotOpenable(LocatedSignature),
    ValueTypeKindIsNotType(
        Span,
        LocatedKind,
        (LocatedKind, LocatedKind, KindUnificationFailure),
    ),
    DuplicateDatatypeConstructorName(String, Span),
    ImportingNonDatatypeAsDatatype(Span),
}

/// Map structure elaboration errors to [`CompileError`].
///
/// # Arguments
///
/// * `structure_error` — Error from [`crate::elaborated::elaborate::elab_str`] paths.
///
/// # Returns
///
/// [`CompileError`] at structure or span carried in `structure_error`.
pub fn compile_error_from_structure_elaboration_error(
    structure_error: &StructureElaborationError,
) -> CompileError {
    match structure_error {
        StructureElaborationError::UnboundStructureVariable(source_span, structure_name) => {
            CompileError::at(
                source_span.clone(),
                format!("Unbound structure variable {}", structure_name),
            )
        }
        StructureElaborationError::AppliedNonFunctor(signature) => {
            CompileError::at(signature.span.clone(), "Application of non-functor")
        }
        StructureElaborationError::FunctorRebindingAttempt(source_span) => {
            CompileError::at(source_span.clone(), "Attempt to rebind functor")
        }
        StructureElaborationError::StructureNotOpenable(signature) => {
            CompileError::at(signature.span.clone(), "Un-openable structure")
        }
        StructureElaborationError::ValueTypeKindIsNotType(
            source_span,
            kind,
            (subkind_left, subkind_right, kind_failure),
        ) => CompileError::at(
            source_span.clone(),
            format!(
                "'val' type kind is not 'Type': kind {:?}, subkind 1 {:?}, subkind 2 {:?}; {}",
                kind.node,
                subkind_left.node,
                subkind_right.node,
                format_kind_unification_failure(kind_failure)
            ),
        ),
        StructureElaborationError::DuplicateDatatypeConstructorName(
            constructor_name,
            source_span,
        ) => CompileError::at(
            source_span.clone(),
            format!("Duplicate datatype constructor {}", constructor_name),
        ),
        StructureElaborationError::ImportingNonDatatypeAsDatatype(source_span) => CompileError::at(
            source_span.clone(),
            "Trying to import non-datatype as a datatype",
        ),
    }
}
