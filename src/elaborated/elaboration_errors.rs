//! Elaboration error types and reporting.
//!
//! Translated from `elab_err.sml`.
//!
//! Mappers use [`CompileError::type_at`] / [`CompileError::type_at_with_hint`] so user-facing output shows the
//! `-- TYPE` banner consistently with other type-checker phases.
//!
//! Each `compile_error_from_*` mapper turns a structured error enum into a [`CompileError`] (spans preserved
//! where the underlying AST carries them). [`format_kind_unification_failure`] and nested
//! [`compile_error_from_constructor_unification_failure`] produce human-readable text for embedding in larger
//! diagnostics.

use crate::diagnostics::{
    render_diagnostic_body, DiagnosticId, DiagnosticLocale, DiagnosticPayload,
};
use crate::elaborated::{
    LocatedConstructor, LocatedDeclaration, LocatedExpression, LocatedKind, LocatedPattern,
    LocatedSignature, LocatedSignatureItem,
};
use crate::error_types::{CompileError, Span};

/// Build a catalog payload for [`KindUnificationFailure`] (nested under constructor / signature errors).
///
/// # Arguments
///
/// * `failure` — Kind unification failure from the elaborator.
///
/// # Returns
///
/// [`DiagnosticPayload`] whose template takes `Debug` text placeholders.
pub fn kind_unification_payload(failure: &KindUnificationFailure) -> DiagnosticPayload {
    match failure {
        KindUnificationFailure::OccursCheckFailed(found_kind, expected_kind) => {
            DiagnosticPayload::new(
                DiagnosticId::KindOccursCheckFailed,
                vec![
                    format!("{:?}", found_kind.node),
                    format!("{:?}", expected_kind.node),
                ],
            )
        }
        KindUnificationFailure::IncompatibleKinds(found_kind, expected_kind) => {
            DiagnosticPayload::new(
                DiagnosticId::IncompatibleKinds,
                vec![
                    format!("{:?}", found_kind.node),
                    format!("{:?}", expected_kind.node),
                ],
            )
        }
        KindUnificationFailure::ScopePreventsUnification(first_kind, second_kind) => {
            DiagnosticPayload::new(
                DiagnosticId::ScopePreventsKindUnification,
                vec![
                    format!("{:?}", first_kind.node),
                    format!("{:?}", second_kind.node),
                ],
            )
        }
    }
}

/// Build a catalog payload for [`ConstructorUnificationFailure`] (plain or nested under other bodies).
///
/// # Arguments
///
/// * `failure` — Constructor unification failure from [`crate::elaborated::elaborate::unify_cons`].
///
/// # Returns
///
/// Fully localized tree when later rendered; record tails may embed English nested text for `{2}`.
pub fn constructor_unification_payload(
    failure: &ConstructorUnificationFailure,
) -> DiagnosticPayload {
    match failure {
        ConstructorUnificationFailure::NestedKindUnificationFailure(
            found_kind,
            expected_kind,
            kind_failure,
        ) => DiagnosticPayload::new(
            DiagnosticId::NestedKindUnificationFailure,
            vec![
                format!("{:?}", found_kind.node),
                format!("{:?}", expected_kind.node),
            ],
        )
        .with_suffix(kind_unification_payload(kind_failure)),
        ConstructorUnificationFailure::ConstructorOccursCheckFailed(left, right) => {
            DiagnosticPayload::new(
                DiagnosticId::ConstructorOccursCheckFailed,
                vec![format!("{:?}", left.node), format!("{:?}", right.node)],
            )
        }
        ConstructorUnificationFailure::IncompatibleConstructors(left, right) => {
            DiagnosticPayload::new(
                DiagnosticId::IncompatibleConstructorsUnif,
                vec![format!("{:?}", left.node), format!("{:?}", right.node)],
            )
        }
        ConstructorUnificationFailure::TypeFunctionExplicitnessMismatch(left, right) => {
            DiagnosticPayload::new(
                DiagnosticId::TypeFunctionExplicitnessMismatch,
                vec![format!("{:?}", left.node), format!("{:?}", right.node)],
            )
        }
        ConstructorUnificationFailure::UnexpectedKindForKindofQuery(
            kind,
            constructor,
            expectation,
        ) => DiagnosticPayload::new(
            DiagnosticId::UnexpectedKindForKindofQuery,
            vec![
                expectation.clone(),
                format!("{:?}", kind.node),
                format!("{:?}", constructor.node),
            ],
        ),
        ConstructorUnificationFailure::RecordConstructorUnificationFailure(
            left_record,
            right_record,
            field_detail,
        ) => {
            let mut part3 = String::new();
            if let Some((
                field_name_constructor,
                left_field_type,
                right_field_type,
                nested_failure,
            )) = field_detail
            {
                part3.push_str(&format!(
                    "; field {:?}: {:?} vs {:?}",
                    field_name_constructor.node, left_field_type.node, right_field_type.node
                ));
                if let Some(inner) = nested_failure {
                    part3.push_str("; ");
                    part3.push_str(&render_diagnostic_body(
                        &constructor_unification_payload(inner),
                        DiagnosticLocale::En,
                    ));
                }
            }
            DiagnosticPayload::new(
                DiagnosticId::RecordConstructorUnificationFailure,
                vec![
                    format!("{:?}", left_record.node),
                    format!("{:?}", right_record.node),
                    part3,
                ],
            )
        }
        ConstructorUnificationFailure::SuspendedLiftingClash(first_span, second_span) => {
            DiagnosticPayload::new(
                DiagnosticId::SuspendedLiftingClash,
                vec![first_span.to_string(), second_span.to_string()],
            )
        }
        ConstructorUnificationFailure::SubstitutionBlockedByDeepUnification(_head, body) => {
            DiagnosticPayload::new(
                DiagnosticId::SubstitutionBlockedByDeepUnification,
                vec![String::new(), format!("{:?}", body.node)],
            )
        }
        ConstructorUnificationFailure::UnificationLiftingTooDeep => {
            DiagnosticPayload::new(DiagnosticId::UnificationLiftingTooDeep, Vec::new())
        }
        ConstructorUnificationFailure::ScopePreventsConstructorUnification(left, right) => {
            DiagnosticPayload::new(
                DiagnosticId::ScopePreventsConstructorUnification,
                vec![format!("{:?}", left.node), format!("{:?}", right.node)],
            )
        }
    }
}

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
/// [`CompileError::type_at`] (or equivalent) with user-facing text.
pub fn compile_error_from_kind_elaboration_error(
    kind_elaboration_error: &KindElaborationError,
) -> CompileError {
    match kind_elaboration_error {
        KindElaborationError::UnboundKindVariable(source_span, variable_name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundKindVariable,
                    vec![variable_name.clone()],
                ),
                DiagnosticId::HintUnboundKindVariable,
                Vec::new(),
            )
        }
        KindElaborationError::WildcardDisallowedInSignature(source_span) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(DiagnosticId::WildcardDisallowedInSignature, Vec::new()),
                DiagnosticId::HintWildcardDisallowedInSignature,
                Vec::new(),
            )
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
    render_diagnostic_body(&kind_unification_payload(failure), DiagnosticLocale::En)
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
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundConstructorVariable,
                    vec![variable_name.clone()],
                ),
                DiagnosticId::HintUnboundConstructorVariable,
                Vec::new(),
            )
        }
        ConstructorElaborationError::UnboundDatatypeName(source_span, datatype_name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundDatatypeName,
                    vec![datatype_name.clone()],
                ),
                DiagnosticId::HintUnboundDatatypeName,
                Vec::new(),
            )
        }
        ConstructorElaborationError::UnboundStructureReference(source_span, structure_name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundStructureReference,
                    vec![structure_name.clone()],
                ),
                DiagnosticId::HintUnboundStructureReference,
                Vec::new(),
            )
        }
        ConstructorElaborationError::ConstructorWrongKind(
            constructor,
            found_kind,
            expected_kind,
            kind_failure,
        ) => CompileError::type_at_with_hint(
            constructor.span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::ConstructorWrongKind,
                vec![
                    format!("{:?}", found_kind.node),
                    format!("{:?}", expected_kind.node),
                ],
            )
            .with_suffix(kind_unification_payload(kind_failure)),
            DiagnosticId::HintConstructorWrongKind,
            Vec::new(),
        ),
        ConstructorElaborationError::DuplicateRecordFieldName(source_span, field_name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::DuplicateRecordFieldName,
                    vec![field_name.clone()],
                ),
                DiagnosticId::HintDuplicateRecordFieldName,
                Vec::new(),
            )
        }
        ConstructorElaborationError::ProjectionIndexOutOfBounds(constructor, projection_index) => {
            CompileError::type_at_with_hint(
                constructor.span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::ProjectionIndexOutOfBounds,
                    vec![projection_index.to_string()],
                ),
                DiagnosticId::HintProjectionIndexOutOfBounds,
                Vec::new(),
            )
        }
        ConstructorElaborationError::ProjectionKindMismatch(constructor, kind) => {
            CompileError::type_at_with_hint(
                constructor.span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::ProjectionKindMismatch,
                    vec![format!("{:?}", kind.node)],
                ),
                DiagnosticId::HintProjectionKindMismatch,
                Vec::new(),
            )
        }
        ConstructorElaborationError::ConstructorWildcardDisallowedInSignature(source_span) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::ConstructorWildcardDisallowedInSignatureConstructor,
                    Vec::new(),
                ),
                DiagnosticId::HintConstructorWildcardDisallowedInSignatureConstructor,
                Vec::new(),
            )
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
        ConstructorUnificationFailure::SuspendedLiftingClash(first_span, _second_span) => {
            CompileError::type_at(first_span.clone(), constructor_unification_payload(failure))
        }
        ConstructorUnificationFailure::SubstitutionBlockedByDeepUnification(head, _body) => {
            CompileError::type_at(head.span.clone(), constructor_unification_payload(failure))
        }
        _ => CompileError::Plain(constructor_unification_payload(failure)),
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
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundExpressionVariable,
                    vec![variable_name.clone()],
                ),
                DiagnosticId::HintUnboundExpressionVariable,
                Vec::new(),
            )
        }
        ExpressionElaborationError::UnboundStructureInExpression(source_span, structure_name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundStructureInExpression,
                    vec![structure_name.clone()],
                ),
                DiagnosticId::HintUnboundStructureInExpression,
                Vec::new(),
            )
        }
        ExpressionElaborationError::ExpressionUnificationFailure(
            expression,
            inferred_constructor,
            expected_constructor,
            unification_failure,
        ) => CompileError::type_at_with_hint(
            expression.span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::ExpressionUnificationFailure,
                vec![
                    format!("{:?}", inferred_constructor.node),
                    format!("{:?}", expected_constructor.node),
                ],
            )
            .with_suffix(constructor_unification_payload(unification_failure)),
            DiagnosticId::HintExpressionUnificationFailure,
            Vec::new(),
        ),
        ExpressionElaborationError::UnificationVariableObstructsOperation(
            operation_description,
            source_span,
            _blocking_constructor,
        ) => CompileError::type_at_with_hint(
            source_span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::UnificationVariableObstructsOperation,
                vec![operation_description.clone()],
            ),
            DiagnosticId::HintUnificationVariableObstructs,
            Vec::new(),
        ),
        ExpressionElaborationError::ExpressionWrongForm(expected_form_name, expression, _type) => {
            CompileError::type_at_with_hint(
                expression.span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::ExpressionWrongForm,
                    vec![expected_form_name.clone()],
                ),
                DiagnosticId::HintExpressionWrongForm,
                Vec::new(),
            )
        }
        ExpressionElaborationError::IncompatibleConstructors(left, right) => {
            CompileError::type_at_with_hint(
                left.span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::IncompatibleConstructorsExpression,
                    vec![format!("{:?}", left.node), format!("{:?}", right.node)],
                ),
                DiagnosticId::HintIncompatibleConstructorsExpression,
                Vec::new(),
            )
        }
        ExpressionElaborationError::DuplicatePatternVariable(source_span, variable_name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::DuplicatePatternVariable,
                    vec![variable_name.clone()],
                ),
                DiagnosticId::HintDuplicatePatternVariable,
                Vec::new(),
            )
        }
        ExpressionElaborationError::PatternUnificationFailure(
            pattern,
            inferred_constructor,
            expected_constructor,
            unification_failure,
        ) => CompileError::type_at_with_hint(
            pattern.span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::PatternUnificationFailure,
                vec![
                    format!("{:?}", inferred_constructor.node),
                    format!("{:?}", expected_constructor.node),
                ],
            )
            .with_suffix(constructor_unification_payload(unification_failure)),
            DiagnosticId::HintPatternUnificationFailure,
            Vec::new(),
        ),
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
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundQualifiedConstructor,
                    vec![full_qualifier],
                ),
                DiagnosticId::HintUnboundQualifiedConstructor,
                Vec::new(),
            )
        }
        ExpressionElaborationError::PatternConstructorGivenArgumentButExpectsNone(source_span) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::PatternConstructorGivenArgumentButExpectsNone,
                    Vec::new(),
                ),
                DiagnosticId::HintPatternConstructorGivenArgumentButExpectsNone,
                Vec::new(),
            )
        }
        ExpressionElaborationError::PatternConstructorExpectsArgumentButNoneGiven(source_span) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::PatternConstructorExpectsArgumentButNoneGiven,
                    Vec::new(),
                ),
                DiagnosticId::HintPatternConstructorExpectsArgumentButNoneGiven,
                Vec::new(),
            )
        }
        ExpressionElaborationError::InexhaustiveCaseAnalysis(source_span, pattern) => {
            CompileError::type_at(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::InexhaustiveCaseAnalysis,
                    vec![format!("{:?}", pattern.node)],
                ),
            )
        }
        ExpressionElaborationError::DuplicatePatternRecordField(source_span, field_name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::DuplicatePatternRecordField,
                    vec![field_name.clone()],
                ),
                DiagnosticId::HintDuplicatePatternRecordField,
                Vec::new(),
            )
        }
        ExpressionElaborationError::UnresolvableTypeClassInstance(
            source_span,
            class_constraint,
        ) => CompileError::type_at(
            source_span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::UnresolvableTypeClassInstance,
                vec![format!("{:?}", class_constraint.node)],
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
            CompileError::type_at(
                source_span.clone(),
                DiagnosticPayload::new(DiagnosticId::TypeClassWildcardOutOfContext, vec![detail]),
            )
        }
        ExpressionElaborationError::IllegalRecursiveValueBinding(
            bound_variable_name,
            right_hand_side,
        ) => CompileError::type_at_with_hint(
            right_hand_side.span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::IllegalRecursiveValueBinding,
                vec![bound_variable_name.clone()],
            ),
            DiagnosticId::HintIllegalRecursiveValueBinding,
            Vec::new(),
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
/// [`CompileError::type_at`] for list-based issues; [`DeclarationElaborationError::TypeHoleFound`] uses
/// [`CompileError::Plain`] with constructor debug.
pub fn compile_error_from_declaration_elaboration_error(
    declaration_error: &DeclarationElaborationError,
) -> CompileError {
    match declaration_error {
        DeclarationElaborationError::KindUnifiersRemainUndetermined(declarations) => {
            CompileError::type_at_with_hint(
                declarations_fallback_span(declarations),
                DiagnosticPayload::new(DiagnosticId::KindUnifiersRemainUndetermined, Vec::new()),
                DiagnosticId::HintKindUnifiersRemainUndetermined,
                Vec::new(),
            )
        }
        DeclarationElaborationError::ConstructorUnifiersRemainUndetermined(declarations) => {
            CompileError::type_at_with_hint(
                declarations_fallback_span(declarations),
                DiagnosticPayload::new(
                    DiagnosticId::ConstructorUnifiersRemainUndetermined,
                    Vec::new(),
                ),
                DiagnosticId::HintConstructorUnifiersRemainUndetermined,
                Vec::new(),
            )
        }
        DeclarationElaborationError::NonStrictlyPositiveDeclaration(declaration) => {
            CompileError::type_at_with_hint(
                declaration.span.clone(),
                DiagnosticPayload::new(DiagnosticId::NonStrictlyPositiveDeclaration, Vec::new()),
                DiagnosticId::HintNonStrictlyPositiveDeclaration,
                Vec::new(),
            )
        }
        DeclarationElaborationError::TypeHoleFound(constructor) => {
            CompileError::Plain(DiagnosticPayload::new(
                DiagnosticId::TypeHoleFoundInternal,
                vec![format!("{:?}", constructor.node)],
            ))
        }
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
        SignatureElaborationError::UnboundSignatureName(source_span, name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(DiagnosticId::UnboundSignatureName, vec![name.clone()]),
                DiagnosticId::HintUnboundSignatureName,
                Vec::new(),
            )
        }
        SignatureElaborationError::UnmatchedSignatureItem(source_span, item) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnmatchedSignatureItem,
                    vec![format!("{:?}", item.node)],
                ),
                DiagnosticId::HintUnmatchedSignatureItem,
                Vec::new(),
            )
        }
        SignatureElaborationError::SignatureItemKindUnificationFailed(
            source_span,
            actual_item,
            actual_kind,
            expected_item,
            expected_kind,
            kind_failure,
        ) => CompileError::type_at(
            source_span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::SignatureItemKindUnificationFailed,
                vec![
                    format!("{:?}", actual_item.node),
                    format!("{:?}", actual_kind.node),
                    format!("{:?}", expected_item.node),
                    format!("{:?}", expected_kind.node),
                ],
            )
            .with_suffix(kind_unification_payload(kind_failure)),
        ),
        SignatureElaborationError::SignatureItemConstructorUnificationFailed(
            source_span,
            actual_item,
            actual_constructor,
            expected_item,
            expected_constructor,
            constructor_failure,
        ) => CompileError::type_at(
            source_span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::SignatureItemConstructorUnificationFailed,
                vec![
                    format!("{:?}", actual_item.node),
                    format!("{:?}", actual_constructor.node),
                    format!("{:?}", expected_item.node),
                    format!("{:?}", expected_constructor.node),
                ],
            )
            .with_suffix(constructor_unification_payload(constructor_failure)),
        ),
        SignatureElaborationError::SignatureItemDatatypeSpecificationsMismatch(
            source_span,
            first_item,
            second_item,
            optional_unification_detail,
        ) => {
            let detail = if let Some((left_constructor, right_constructor, unification_failure)) =
                optional_unification_detail
            {
                format!(
                    "; unification error: {:?} vs {:?}; {}",
                    left_constructor.node,
                    right_constructor.node,
                    render_diagnostic_body(
                        &constructor_unification_payload(unification_failure),
                        DiagnosticLocale::En,
                    )
                )
            } else {
                String::new()
            };
            CompileError::type_at(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::SignatureItemDatatypeSpecificationsMismatch,
                    vec![
                        format!("{:?}", first_item.node),
                        format!("{:?}", second_item.node),
                        detail,
                    ],
                ),
            )
        }
        SignatureElaborationError::IncompatibleSignatureShapes(
            source_span,
            left_signature,
            right_signature,
        ) => CompileError::type_at(
            source_span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::IncompatibleSignatureShapes,
                vec![
                    format!("{:?}", left_signature.node),
                    format!("{:?}", right_signature.node),
                ],
            ),
        ),
        SignatureElaborationError::WhereClauseFieldUnavailable(signature, field_name) => {
            CompileError::type_at_with_hint(
                signature.span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::WhereClauseFieldUnavailable,
                    vec![field_name.clone()],
                ),
                DiagnosticId::HintWhereClauseFieldUnavailable,
                Vec::new(),
            )
        }
        SignatureElaborationError::WhereClauseKindMismatch(
            found_kind,
            expected_kind,
            kind_failure,
        ) => CompileError::type_at(
            found_kind.span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::WhereClauseKindMismatch,
                vec![
                    format!("{:?}", found_kind.node),
                    format!("{:?}", expected_kind.node),
                    render_diagnostic_body(
                        &kind_unification_payload(kind_failure),
                        DiagnosticLocale::En,
                    ),
                ],
            ),
        ),
        SignatureElaborationError::SignatureNotValidForInclude(signature) => {
            CompileError::type_at_with_hint(
                signature.span.clone(),
                DiagnosticPayload::new(DiagnosticId::SignatureNotValidForInclude, Vec::new()),
                DiagnosticId::HintSignatureNotValidForInclude,
                Vec::new(),
            )
        }
        SignatureElaborationError::DuplicateConstructorNameInSignature(source_span, name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::DuplicateConstructorNameInSignature,
                    vec![name.clone()],
                ),
                DiagnosticId::HintDuplicateConstructorNameInSignature,
                Vec::new(),
            )
        }
        SignatureElaborationError::DuplicateValueNameInSignature(source_span, name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::DuplicateValueNameInSignature,
                    vec![name.clone()],
                ),
                DiagnosticId::HintDuplicateValueNameInSignature,
                Vec::new(),
            )
        }
        SignatureElaborationError::DuplicateNestedSignatureName(source_span, name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::DuplicateNestedSignatureNameInSignature,
                    vec![name.clone()],
                ),
                DiagnosticId::HintDuplicateNestedSignatureNameInSignature,
                Vec::new(),
            )
        }
        SignatureElaborationError::DuplicateStructureNameInSignature(source_span, name) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::DuplicateStructureNameInSignature,
                    vec![name.clone()],
                ),
                DiagnosticId::HintDuplicateStructureNameInSignature,
                Vec::new(),
            )
        }
        SignatureElaborationError::SignatureNotValidForOpenConstraints(signature) => {
            CompileError::type_at_with_hint(
                signature.span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::SignatureNotValidForOpenConstraints,
                    Vec::new(),
                ),
                DiagnosticId::HintSignatureNotValidForOpenConstraints,
                Vec::new(),
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
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(
                    DiagnosticId::UnboundStructureVariable,
                    vec![structure_name.clone()],
                ),
                DiagnosticId::HintUnboundStructureVariable,
                Vec::new(),
            )
        }
        StructureElaborationError::AppliedNonFunctor(signature) => CompileError::type_at_with_hint(
            signature.span.clone(),
            DiagnosticPayload::new(DiagnosticId::AppliedNonFunctor, Vec::new()),
            DiagnosticId::HintAppliedNonFunctor,
            Vec::new(),
        ),
        StructureElaborationError::FunctorRebindingAttempt(source_span) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(DiagnosticId::FunctorRebindingAttempt, Vec::new()),
                DiagnosticId::HintFunctorRebindingAttempt,
                Vec::new(),
            )
        }
        StructureElaborationError::StructureNotOpenable(signature) => {
            CompileError::type_at_with_hint(
                signature.span.clone(),
                DiagnosticPayload::new(DiagnosticId::StructureNotOpenable, Vec::new()),
                DiagnosticId::HintStructureNotOpenable,
                Vec::new(),
            )
        }
        StructureElaborationError::ValueTypeKindIsNotType(
            source_span,
            kind,
            (subkind_left, subkind_right, kind_failure),
        ) => CompileError::type_at(
            source_span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::ValTypeKindIsNotType,
                vec![
                    format!("{:?}", kind.node),
                    format!("{:?}", subkind_left.node),
                    format!("{:?}", subkind_right.node),
                    render_diagnostic_body(
                        &kind_unification_payload(kind_failure),
                        DiagnosticLocale::En,
                    ),
                ],
            ),
        ),
        StructureElaborationError::DuplicateDatatypeConstructorName(
            constructor_name,
            source_span,
        ) => CompileError::type_at_with_hint(
            source_span.clone(),
            DiagnosticPayload::new(
                DiagnosticId::DuplicateDatatypeConstructorNameInGroup,
                vec![constructor_name.clone()],
            ),
            DiagnosticId::HintDuplicateDatatypeConstructorNameInGroup,
            Vec::new(),
        ),
        StructureElaborationError::ImportingNonDatatypeAsDatatype(source_span) => {
            CompileError::type_at_with_hint(
                source_span.clone(),
                DiagnosticPayload::new(DiagnosticId::ImportingNonDatatypeAsDatatype, Vec::new()),
                DiagnosticId::HintImportingNonDatatypeAsDatatype,
                Vec::new(),
            )
        }
    }
}
