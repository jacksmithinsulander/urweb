//! Tests for conversational compiler diagnostics: banner lines, `Hint:` sections, and elaboration copy.
//!
//! These tests avoid the full boot linkage when possible so they run even when the Basis is unavailable.

use ur::diagnostics::{DiagnosticId, DiagnosticLocale, DiagnosticPayload};
use ur::elaborated::elaboration_errors::{
    compile_error_from_expression_elaboration_error, compile_error_from_kind_elaboration_error,
    ExpressionElaborationError, KindElaborationError,
};
use ur::error_types::{CompileError, Pos, Span};

/// Build a compact [`Span`] used only to exercise [`CompileError`] rendering.
fn sample_span() -> Span {
    Span {
        file: "Example.ur".to_string(),
        first: Pos { line: 4, col: 2 },
        last: Pos { line: 4, col: 8 },
    }
}

#[test]
fn unbound_variable_diagnostic_includes_banner_hint_and_arrow() {
    let compile_error = compile_error_from_expression_elaboration_error(
        &ExpressionElaborationError::UnboundExpressionVariable(sample_span(), "myVar".into()),
    );
    let rendered = compile_error.to_string();
    assert!(
        rendered.contains("-- TYPE"),
        "elaboration mappers should use the TYPE banner, got:\n{rendered}"
    );
    assert!(
        rendered.contains("myVar"),
        "expected the unknown name in the text, got:\n{rendered}"
    );
    assert!(
        rendered.contains("I cannot find"),
        "expected conversational lead-in, got:\n{rendered}"
    );
    assert!(
        rendered.contains("Hint:"),
        "expected a Hint section, got:\n{rendered}"
    );
    assert!(
        rendered.contains("-->"),
        "expected location arrow, got:\n{rendered}"
    );
    assert!(
        rendered.contains("Example.ur"),
        "expected filename in output, got:\n{rendered}"
    );
}

#[test]
fn unbound_kind_diagnostic_suggests_annotation_fix() {
    let compile_error = compile_error_from_kind_elaboration_error(
        &KindElaborationError::UnboundKindVariable(sample_span(), "k".into()),
    );
    let rendered = compile_error.to_string();
    assert!(rendered.contains("kind"));
    assert!(rendered.contains("Hint:"));
    assert!(rendered.contains("::"));
}

#[test]
fn type_and_parse_variants_use_distinct_banners() {
    let span = sample_span();
    let type_err = CompileError::TypeError {
        span: span.clone(),
        payload: DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
    };
    assert!(type_err.to_string().contains("-- TYPE"));
    let parse_err = CompileError::ParseError {
        span,
        payload: DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
    };
    assert!(parse_err.to_string().contains("-- PARSE"));
}

#[test]
fn warning_uses_warning_banner() {
    let w = CompileError::warning_at(
        sample_span(),
        DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
    );
    assert!(w.to_string().contains("-- WARNING"));
}

#[test]
fn plain_error_still_uses_structured_banner() {
    let p = CompileError::Plain(DiagnosticPayload::new(
        DiagnosticId::LspUnusedValueNeverUsedFromEntry,
        vec!["config issue".into()],
    ));
    let s = p.to_string();
    assert!(s.contains("-- ERROR"));
    assert!(s.contains("config issue"));
}

#[test]
fn parse_helpers_use_parse_banner_and_hint() {
    let e = CompileError::parse_at_with_hint(
        sample_span(),
        DiagnosticPayload::new(DiagnosticId::MutationTestingBadPlaceholder, vec![]),
        DiagnosticId::HintParseUrSyntax,
        vec![],
    );
    let s = e.to_string();
    assert!(s.contains("-- PARSE"), "parse_at_with_hint: {s}");
    assert!(s.contains("Hint:"));
}

#[test]
fn lsp_diagnostic_text_matches_compiler_formatter() {
    let span = sample_span();
    let error = CompileError::type_at_with_hint(
        span,
        DiagnosticPayload::new(
            DiagnosticId::LspUnusedValueNeverUsedFromEntry,
            vec!["main idea".into()],
        ),
        DiagnosticId::HintLspUnusedValueNeverUsedFromEntry,
        vec![],
    );
    let compiler = ur::error_types::format_compile_error_for_user(&error, DiagnosticLocale::En);
    let diagnostic = ur::lsp_support::compile_error_to_diagnostic(&error, DiagnosticLocale::En);
    assert_eq!(diagnostic.message, compiler);
    assert!(compiler.contains("-- TYPE"));
    assert!(compiler.contains("Hint:"));
}

/// Smoke-test that three supported locales render without leaving raw placeholders for a multi-arg id.
#[test]
fn parse_failure_template_renders_in_en_sv_es() {
    let payload = DiagnosticPayload::new(
        DiagnosticId::ParseUrSyntaxFailed,
        vec!["Mod.ur".into(), "Unrecognized token".into(), String::new()],
    );
    for locale in [
        DiagnosticLocale::En,
        DiagnosticLocale::Sv,
        DiagnosticLocale::Es,
    ] {
        let rendered = ur::diagnostics::format_diagnostic_payload_for_user(&payload, locale);
        assert!(
            !rendered.contains("{0}") && !rendered.contains("{1}") && !rendered.contains("{2}"),
            "locale {locale:?} should expand placeholders: {rendered}"
        );
        assert!(rendered.contains("Mod.ur"), "{locale:?}: {rendered}");
    }
}
