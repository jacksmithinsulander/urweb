//! Integration tests for the preprocess ∘ parse pipeline (LangSec composed surface language).

use ur::error_types::ErrorReporter;
use ur::parse::{
    parse_ur, parse_urs, preprocess_urs, rewrite_case_expressions, rewrite_datatype_constructors,
    rewrite_sgn_where,
};

#[test]
fn preprocess_urs_inserts_brackets_for_bare_quantifier() {
    let src = "val f : nm :: Type -> int -> int";
    let pp = preprocess_urs(src);
    assert!(
        pp.contains("[nm :: Type]"),
        "expected bracketed quantifier, got: {pp:?}"
    );
}

#[test]
fn rewrite_sgn_where_splits_top_level_and_nested_where() {
    let src = "val x : int where y = z";
    let out = rewrite_sgn_where(src);
    assert!(
        out.contains("sgn_where"),
        "top-level where should become sgn_where: {out:?}"
    );
    let nested = "val x : (t where u = v)";
    let out2 = rewrite_sgn_where(nested);
    assert!(
        out2.contains("sgn_subwhere"),
        "nested where should become sgn_subwhere: {out2:?}"
    );
}

#[test]
fn ur_roundtrip_minimal_decl_parses_after_rewrites() {
    let mut errors = ErrorReporter::new();
    let src = "val x = 1\n";
    let out = parse_ur("t.ur", src, &mut errors);
    assert!(out.is_some(), "parse errors: {:?}", errors.errors);
}

#[test]
fn urs_val_line_parses_after_preprocess() {
    let mut errors = ErrorReporter::new();
    let src = "val x : int\n";
    let out = parse_urs("t.urs", src, &mut errors);
    assert!(out.is_some(), "parse_urs errors: {:?}", errors.errors);
}

#[test]
fn datatype_rewrite_chain_does_not_panic_on_empty() {
    assert_eq!(rewrite_datatype_constructors(""), "");
    assert_eq!(rewrite_sgn_where(""), "");
    assert_eq!(rewrite_case_expressions(""), "");
    assert_eq!(preprocess_urs(""), "");
}
