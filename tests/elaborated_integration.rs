//! Integration tests for the Elaborated module.
//!
//! Catches mutants in elaborated::utilities::classify_datatype (Enum, Option, Default logic),
//! type_operations::cons_eq_simple, kind::exists, con::exists, file::max_name.

use urweb::datatype_kind::DatatypeKind;
use urweb::elaborated::type_operations::cons_eq_simple;
use urweb::elaborated::utilities::{classify_datatype, con, file, kind};
use urweb::elaborated::{Constructor, Declaration, Kind};
use urweb::elaborated::{LocatedConstructor, LocatedKind};
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

// ---------------------------------------------------------------------------
// kind::exists, con::exists, file::max_name (utilities)
// ---------------------------------------------------------------------------

#[test]
fn elaborated_kind_exists_arrow() {
    let k_type = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Arrow(Box::new(k_type.clone()), Box::new(k_type)));
    let pred = |k: &LocatedKind| matches!(&k.node, Kind::Type);
    assert!(kind::exists(&k, &pred));
}

#[test]
fn elaborated_kind_exists_type_direct() {
    let k = Located::dummy(Kind::Type);
    let pred = |k: &LocatedKind| matches!(&k.node, Kind::Type);
    assert!(kind::exists(&k, &pred));
}

#[test]
fn elaborated_kind_exists_type_false() {
    let k = Located::dummy(Kind::Unit);
    let pred = |k: &LocatedKind| matches!(&k.node, Kind::Type);
    assert!(!kind::exists(&k, &pred));
}

#[test]
fn elaborated_con_exists_unit() {
    let c = Located::dummy(Constructor::Unit);
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::Unit);
    assert!(con::exists(&c, &kp, &cp));
}

#[test]
fn elaborated_con_exists_tfun_descends() {
    let u = Located::dummy(Constructor::Unit);
    let tfun = Located::dummy(Constructor::TFun(Box::new(u.clone()), Box::new(u)));
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::Unit);
    assert!(con::exists(&tfun, &kp, &cp));
}

#[test]
fn elaborated_file_max_name_empty() {
    assert_eq!(file::max_name(&[]), 0);
}

#[test]
fn elaborated_file_max_name_constructor() {
    let k = Located::dummy(Kind::Type);
    let c = Located::dummy(Constructor::Unit);
    let d = Located::dummy(Declaration::Constructor("X".into(), 100, k, c));
    assert_eq!(file::max_name(&[d]), 100);
}

#[test]
fn elaborated_file_max_name_val() {
    let u = Located::dummy(Constructor::Unit);
    let e = Located::dummy(urweb::elaborated::Expression::Prim(
        urweb::primitives::Prim::Int(0),
    ));
    let d = Located::dummy(Declaration::Val("x".into(), 42, u, e));
    assert_eq!(file::max_name(&[d]), 42);
}
