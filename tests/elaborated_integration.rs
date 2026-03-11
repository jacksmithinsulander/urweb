//! Integration tests for the Elaborated module.
//!
//! Catches mutants in elaborated::utilities::classify_datatype (Enum, Option, Default logic)
//! and type_operations::cons_eq_simple.

use urweb::datatype_kind::DatatypeKind;
use urweb::elaborated::type_operations::cons_eq_simple;
use urweb::elaborated::utilities::classify_datatype;
use urweb::elaborated::{Constructor, LocatedConstructor};
use urweb::error_types::Located;

#[test]
fn elaborated_classify_datatype_enum() {
    let constrs: Vec<(String, usize, Option<LocatedConstructor>)> =
        vec![("A".into(), 0, None), ("B".into(), 1, None)];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Enum);
}

#[test]
fn elaborated_classify_datatype_enum_single_nullary() {
    let constrs: Vec<(String, usize, Option<LocatedConstructor>)> = vec![("Unit".into(), 0, None)];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Enum);
}

#[test]
fn elaborated_classify_datatype_option() {
    let unit = Located::dummy(Constructor::Unit);
    let constrs: Vec<(String, usize, Option<LocatedConstructor>)> =
        vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Option);
}

#[test]
fn elaborated_classify_datatype_default() {
    let unit = Located::dummy(Constructor::Unit);
    let constrs: Vec<(String, usize, Option<LocatedConstructor>)> = vec![
        ("A".into(), 0, Some(unit.clone())),
        ("B".into(), 1, Some(unit)),
    ];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Default);
}

#[test]
fn elaborated_classify_datatype_default_two_nullary_one_unary() {
    // (2 nullary, 1 unary) must be Default, not Option. Catches && vs || mutant.
    let unit = Located::dummy(Constructor::Unit);
    let constrs: Vec<(String, usize, Option<LocatedConstructor>)> = vec![
        ("A".into(), 0, None),
        ("B".into(), 0, None),
        ("C".into(), 1, Some(unit)),
    ];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Default);
}

#[test]
fn elaborated_cons_eq_simple_unit_unit() {
    let u = Located::dummy(Constructor::Unit);
    assert!(
        cons_eq_simple(&u, &u),
        "cons_eq_simple(Unit, Unit) must be true"
    );
}

#[test]
fn elaborated_cons_eq_simple_unit_named_false() {
    let u = Located::dummy(Constructor::Unit);
    let n = Located::dummy(Constructor::Named(1));
    assert!(
        !cons_eq_simple(&u, &n),
        "cons_eq_simple(Unit, Named(1)) must be false"
    );
}

#[test]
fn elaborated_cons_eq_simple_named_named_same() {
    let n1 = Located::dummy(Constructor::Named(1));
    let n2 = Located::dummy(Constructor::Named(1));
    assert!(
        cons_eq_simple(&n1, &n2),
        "cons_eq_simple(Named(1), Named(1)) must be true"
    );
}

#[test]
fn elaborated_cons_eq_simple_named_named_different() {
    let n1 = Located::dummy(Constructor::Named(1));
    let n2 = Located::dummy(Constructor::Named(2));
    assert!(
        !cons_eq_simple(&n1, &n2),
        "cons_eq_simple(Named(1), Named(2)) must be false"
    );
}
