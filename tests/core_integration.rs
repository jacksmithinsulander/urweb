//! Integration tests for the Core module.
//!
//! These tests exercise the Core AST utilities and environment
//! as a cohesive unit, including classify_datatype, traversal (map/fold/exists),
//! file::max_name, Env building and lookup, and decl_binds.

use urweb::core::environment::Env;
use urweb::core::utilities::{classify_datatype, constructor, declaration, expression, file, kind};
use urweb::core::{Constructor, Declaration, FieldMeta, Kind, LocatedConstructor, Pattern};
use urweb::datatype_kind::DatatypeKind;
use urweb::error_types::{Located, Span};

fn span() -> Span {
    Span::dummy()
}

#[test]
fn integration_classify_then_env_datatype() {
    // Classify a datatype and then register it in the environment.
    let constructor_specifications: Vec<(String, usize, Option<LocatedConstructor>)> = vec![
        ("None".into(), 0, None),
        ("Some".into(), 1, Some(Located::dummy(Constructor::Unit))),
    ];
    let datatype_kind = classify_datatype(&constructor_specifications);
    assert_eq!(datatype_kind, DatatypeKind::Option);

    let env = Env::empty().push_datatype(10, vec!["a".into()], constructor_specifications);
    let (params, constrs) = env.lookup_datatype(10).unwrap();
    assert_eq!(params.len(), 1);
    assert_eq!(constrs.len(), 2);

    let some_info = env.lookup_constructor("Some").unwrap();
    assert_eq!(some_info.1, 10);
    assert_eq!(some_info.4, 1);
}

#[test]
fn integration_kind_traversal_then_compare() {
    // Build a kind, map over it, fold to count, and compare.
    let k = Located::dummy(Kind::Arrow(
        Box::new(Located::dummy(Kind::Rel(0))),
        Box::new(Located::dummy(Kind::Type)),
    ));

    let k2 = kind::map(k.clone(), &|x| x);
    assert!(matches!(k2.node, Kind::Arrow(_, _)));

    let count = kind::fold(&k, 0usize, &|_, acc| acc + 1);
    assert!(count >= 2);

    let k_same = k.clone();
    assert_eq!(kind::compare(&k, &k_same), std::cmp::Ordering::Equal);
}

#[test]
fn integration_kind_compare_each_variant() {
    let t = Located::dummy(Kind::Type);
    let n = Located::dummy(Kind::Name);
    let u = Located::dummy(Kind::Unit);
    let r0 = Located::dummy(Kind::Rel(0));
    let r1 = Located::dummy(Kind::Rel(1));
    assert_eq!(kind::compare(&t, &t), std::cmp::Ordering::Equal);
    assert_eq!(kind::compare(&n, &n), std::cmp::Ordering::Equal);
    assert_eq!(kind::compare(&u, &u), std::cmp::Ordering::Equal);
    assert_eq!(kind::compare(&r0, &r0), std::cmp::Ordering::Equal);
    assert!(kind::compare(&r0, &r1) != std::cmp::Ordering::Equal);
    let arr = Located::dummy(Kind::Arrow(Box::new(r0.clone()), Box::new(t.clone())));
    assert_eq!(kind::compare(&arr, &arr), std::cmp::Ordering::Equal);
    let rec = Located::dummy(Kind::Record(Box::new(t.clone())));
    assert_eq!(kind::compare(&rec, &rec), std::cmp::Ordering::Equal);
    let tup = Located::dummy(Kind::Tuple(vec![t.clone()]));
    assert_eq!(kind::compare(&tup, &tup), std::cmp::Ordering::Equal);
    let fun = Located::dummy(Kind::Fun("x".into(), Box::new(t)));
    assert_eq!(kind::compare(&fun, &fun), std::cmp::Ordering::Equal);
}

#[test]
fn integration_kind_compare_differing_variants_not_equal() {
    // Deleting match arms would make these return Equal incorrectly
    let t = Located::dummy(Kind::Type);
    let n = Located::dummy(Kind::Name);
    let u = Located::dummy(Kind::Unit);
    let r0 = Located::dummy(Kind::Rel(0));
    let r1 = Located::dummy(Kind::Rel(1));
    assert!(kind::compare(&t, &n) != std::cmp::Ordering::Equal);
    assert!(kind::compare(&n, &t) != std::cmp::Ordering::Equal);
    assert!(kind::compare(&t, &u) != std::cmp::Ordering::Equal);
    let arr = Located::dummy(Kind::Arrow(Box::new(r0.clone()), Box::new(t.clone())));
    assert!(kind::compare(&arr, &t) != std::cmp::Ordering::Equal);
    let rec = Located::dummy(Kind::Record(Box::new(t.clone())));
    let tup = Located::dummy(Kind::Tuple(vec![t.clone()]));
    assert!(kind::compare(&rec, &tup) != std::cmp::Ordering::Equal);
    let fun = Located::dummy(Kind::Fun("x".into(), Box::new(t.clone())));
    assert!(kind::compare(&fun, &arr) != std::cmp::Ordering::Equal);

    // Same variant, different content — delete (Arrow|Record|Fun) arm would fall to _ => Equal (wrong)
    let arr1 = Located::dummy(Kind::Arrow(Box::new(r0.clone()), Box::new(t.clone())));
    let arr2 = Located::dummy(Kind::Arrow(Box::new(r1.clone()), Box::new(t.clone())));
    assert!(kind::compare(&arr1, &arr2) != std::cmp::Ordering::Equal);
    let rec1 = Located::dummy(Kind::Record(Box::new(r0.clone())));
    let rec2 = Located::dummy(Kind::Record(Box::new(r1)));
    assert!(kind::compare(&rec1, &rec2) != std::cmp::Ordering::Equal);
    let fun1 = Located::dummy(Kind::Fun("x".into(), Box::new(r0.clone())));
    let fun2 = Located::dummy(Kind::Fun("x".into(), Box::new(t)));
    assert!(kind::compare(&fun1, &fun2) != std::cmp::Ordering::Equal);
}

#[test]
fn integration_con_traversal() {
    // Build a constructor, map and fold over it.
    let c = Located::dummy(Constructor::Tuple(vec![
        Located::dummy(Constructor::Unit),
        Located::dummy(Constructor::Ffi("M".into(), "T".into())),
    ]));

    let c2 = constructor::map(c.clone(), &|k| k, &|c| c);
    assert!(matches!(c2.node, Constructor::Tuple(_)));

    let has_ffi = constructor::exists(&c, &|_| false, &|c| {
        matches!(&c.node, Constructor::Ffi(_, _))
    });
    assert!(has_ffi);
}

#[test]
fn integration_constructor_exists_first_only() {
    let c = Located::dummy(Constructor::TFun(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Named(99))),
    ));
    assert!(constructor::exists(&c, &|_| false, &|cc| matches!(
        &cc.node,
        Constructor::Unit
    )));
}

#[test]
fn integration_constructor_exists_second_only() {
    let c = Located::dummy(Constructor::TFun(
        Box::new(Located::dummy(Constructor::Named(1))),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::exists(&c, &|_| false, &|cc| matches!(
        &cc.node,
        Constructor::Unit
    )));
}

#[test]
fn integration_constructor_exists_tcfun_kind_only() {
    let k = Located::dummy(Kind::Rel(5));
    let c = Located::dummy(Constructor::TCFun(
        "a".into(),
        Box::new(k),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::exists(
        &c,
        &|kr| matches!(&kr.node, Kind::Rel(5)),
        &|_| false
    ));
}

#[test]
fn integration_constructor_exists_kapp_first_only() {
    let c = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(constructor::exists(&c, &|_| false, &|cc| matches!(
        &cc.node,
        Constructor::Unit
    )));
}

#[test]
fn integration_constructor_exists_kapp_second_only() {
    let c = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Rel(0))),
        Box::new(Located::dummy(Kind::Rel(3))),
    ));
    assert!(constructor::exists(
        &c,
        &|kr| matches!(&kr.node, Kind::Rel(3)),
        &|_| false
    ));
}

#[test]
fn integration_constructor_compare_differing_rels() {
    let c1 = Located::dummy(Constructor::Rel(0));
    let c2 = Located::dummy(Constructor::Rel(1));
    assert!(constructor::compare(&c1, &c2) != std::cmp::Ordering::Equal);
}

#[test]
fn integration_constructor_compare_pair_list() {
    let r0 = Located::dummy(Constructor::Unit);
    let r1 = Located::dummy(Constructor::Unit);
    let c1 = Located::dummy(Constructor::Record(
        Box::new(Located::dummy(Kind::Type)),
        vec![(r0.clone(), r1.clone())],
    ));
    let c2 = Located::dummy(Constructor::Record(
        Box::new(Located::dummy(Kind::Type)),
        vec![(r0, r1)],
    ));
    assert_eq!(constructor::compare(&c1, &c2), std::cmp::Ordering::Equal);
}

#[test]
fn integration_constructor_compare_differing_variants_not_equal() {
    let unit = Located::dummy(Constructor::Unit);
    let c_tfun = Located::dummy(Constructor::TFun(
        Box::new(unit.clone()),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_tcfun = Located::dummy(Constructor::TCFun(
        "a".into(),
        Box::new(Located::dummy(Kind::Type)),
        Box::new(unit),
    ));
    assert!(constructor::compare(&c_tfun, &c_tcfun) != std::cmp::Ordering::Equal);
    let c_record = Located::dummy(Constructor::Record(
        Box::new(Located::dummy(Kind::Type)),
        vec![(
            Located::dummy(Constructor::Unit),
            Located::dummy(Constructor::Unit),
        )],
    ));
    assert!(constructor::compare(&c_tfun, &c_record) != std::cmp::Ordering::Equal);
}

#[test]
fn integration_constructor_compare_same_variant_different_content_not_equal() {
    // Delete match arm would fall to _ => Equal. Same variant, different inner => must be non-Equal.
    let k = Located::dummy(Kind::Type);
    let c_tfun1 = Located::dummy(Constructor::TFun(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_tfun2 = Located::dummy(Constructor::TFun(
        Box::new(Located::dummy(Constructor::Named(1))),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::compare(&c_tfun1, &c_tfun2) != std::cmp::Ordering::Equal);
    let c_trecord1 = Located::dummy(Constructor::TRecord(Box::new(Located::dummy(
        Constructor::Unit,
    ))));
    let c_trecord2 = Located::dummy(Constructor::TRecord(Box::new(Located::dummy(
        Constructor::Named(1),
    ))));
    assert!(constructor::compare(&c_trecord1, &c_trecord2) != std::cmp::Ordering::Equal);
    let c_app1 = Located::dummy(Constructor::App(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_app2 = Located::dummy(Constructor::App(
        Box::new(Located::dummy(Constructor::Named(1))),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::compare(&c_app1, &c_app2) != std::cmp::Ordering::Equal);
    let c_abs1 = Located::dummy(Constructor::Abs(
        "a".into(),
        Box::new(k.clone()),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_abs2 = Located::dummy(Constructor::Abs(
        "b".into(),
        Box::new(k.clone()),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::compare(&c_abs1, &c_abs2) != std::cmp::Ordering::Equal);
    let c_concat1 = Located::dummy(Constructor::Concat(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_concat2 = Located::dummy(Constructor::Concat(
        Box::new(Located::dummy(Constructor::Named(1))),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::compare(&c_concat1, &c_concat2) != std::cmp::Ordering::Equal);
    let c_map1 = Located::dummy(Constructor::Map(
        Box::new(Located::dummy(Kind::Type)),
        Box::new(Located::dummy(Kind::Type)),
    ));
    let c_map2 = Located::dummy(Constructor::Map(
        Box::new(Located::dummy(Kind::Rel(0))),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(constructor::compare(&c_map1, &c_map2) != std::cmp::Ordering::Equal);
    let c_proj1 = Located::dummy(Constructor::Proj(
        Box::new(Located::dummy(Constructor::Unit)),
        0,
    ));
    let c_proj2 = Located::dummy(Constructor::Proj(
        Box::new(Located::dummy(Constructor::Unit)),
        1,
    ));
    assert!(constructor::compare(&c_proj1, &c_proj2) != std::cmp::Ordering::Equal);
    let c_kabs1 = Located::dummy(Constructor::KAbs(
        "k".into(),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_kabs2 = Located::dummy(Constructor::KAbs(
        "k".into(),
        Box::new(Located::dummy(Constructor::Named(1))),
    ));
    assert!(constructor::compare(&c_kabs1, &c_kabs2) != std::cmp::Ordering::Equal);
    let c_kapp1 = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Kind::Type)),
    ));
    let c_kapp2 = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Named(1))),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(constructor::compare(&c_kapp1, &c_kapp2) != std::cmp::Ordering::Equal);
    let c_tkfun1 = Located::dummy(Constructor::TKFun(
        "k".into(),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_tkfun2 = Located::dummy(Constructor::TKFun(
        "k".into(),
        Box::new(Located::dummy(Constructor::Named(1))),
    ));
    assert!(constructor::compare(&c_tkfun1, &c_tkfun2) != std::cmp::Ordering::Equal);
    // TCFun: delete match arm would fall to _ => Equal. Same variant, different content.
    let k = Located::dummy(Kind::Type);
    let c_tcfun1 = Located::dummy(Constructor::TCFun(
        "a".into(),
        Box::new(k.clone()),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c_tcfun2 = Located::dummy(Constructor::TCFun(
        "b".into(),
        Box::new(k),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::compare(&c_tcfun1, &c_tcfun2) != std::cmp::Ordering::Equal);
    // Unit: two Units must compare Equal. Delete (Unit,Unit) arm would fall to _ (still Equal).
    let c_unit1 = Located::dummy(Constructor::Unit);
    let c_unit2 = Located::dummy(Constructor::Unit);
    assert_eq!(
        constructor::compare(&c_unit1, &c_unit2),
        std::cmp::Ordering::Equal
    );
}

#[test]
fn integration_constructor_compare_list_differing_middle() {
    // compare_list: tuples with different middle elements
    let c1 = Located::dummy(Constructor::Tuple(vec![
        Located::dummy(Constructor::Unit),
        Located::dummy(Constructor::Named(1)),
        Located::dummy(Constructor::Unit),
    ]));
    let c2 = Located::dummy(Constructor::Tuple(vec![
        Located::dummy(Constructor::Unit),
        Located::dummy(Constructor::Named(2)),
        Located::dummy(Constructor::Unit),
    ]));
    assert!(constructor::compare(&c1, &c2) != std::cmp::Ordering::Equal);
}

#[test]
fn integration_constructor_compare_pair_list_differing() {
    let k = Located::dummy(Kind::Type);
    let c1 = Located::dummy(Constructor::Record(
        Box::new(k.clone()),
        vec![(
            Located::dummy(Constructor::Unit),
            Located::dummy(Constructor::Named(1)),
        )],
    ));
    let c2 = Located::dummy(Constructor::Record(
        Box::new(k),
        vec![(
            Located::dummy(Constructor::Unit),
            Located::dummy(Constructor::Named(2)),
        )],
    ));
    assert!(constructor::compare(&c1, &c2) != std::cmp::Ordering::Equal);
}

#[test]
fn integration_constructor_exists_map_k1_only() {
    // Constructor::Map: only k1 matches. Catches || -> && mutant in Map branch.
    let c = Located::dummy(Constructor::Map(
        Box::new(Located::dummy(Kind::Rel(5))),
        Box::new(Located::dummy(Kind::Rel(0))),
    ));
    assert!(constructor::exists(
        &c,
        &|kr| matches!(&kr.node, Kind::Rel(5)),
        &|_| false,
    ));
}

#[test]
fn integration_constructor_exists_map_k2_only() {
    // Constructor::Map: only k2 matches.
    let c = Located::dummy(Constructor::Map(
        Box::new(Located::dummy(Kind::Rel(0))),
        Box::new(Located::dummy(Kind::Rel(5))),
    ));
    assert!(constructor::exists(
        &c,
        &|kr| matches!(&kr.node, Kind::Rel(5)),
        &|_| false,
    ));
}

#[test]
fn integration_constructor_exists_record_value_only() {
    // Record: only value in second pair matches (keys don't). Catches || -> && in pairs.any
    let k = Located::dummy(Kind::Type);
    let c = Located::dummy(Constructor::Record(
        Box::new(k),
        vec![
            (
                Located::dummy(Constructor::Named(1)),
                Located::dummy(Constructor::Named(2)),
            ),
            (
                Located::dummy(Constructor::Named(3)),
                Located::dummy(Constructor::Unit),
            ),
        ],
    ));
    assert!(constructor::exists(&c, &|_| false, &|cc| matches!(
        &cc.node,
        Constructor::Unit
    )));
}

#[test]
fn integration_exp_traversal() {
    // Build an expression, map and check exists.
    let e = Located::dummy(urweb::core::Expression::Let(
        "x".into(),
        Located::dummy(Constructor::Unit),
        Box::new(Located::dummy(urweb::core::Expression::Prim(
            urweb::primitives::Prim::Int(42),
        ))),
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
    ));

    let e2 = expression::map(e.clone(), &|k| k, &|c| c, &|e| e);
    assert!(matches!(e2.node, urweb::core::Expression::Let(_, _, _, _)));

    let has_prim = expression::exists(&e, &|_| false, &|_| false, &|e| {
        matches!(e.node, urweb::core::Expression::Prim(_))
    });
    assert!(has_prim);
}

#[test]
fn integration_expression_exists_app_first_only() {
    let e = Located::dummy(urweb::core::Expression::App(
        Box::new(Located::dummy(urweb::core::Expression::Prim(
            urweb::primitives::Prim::Int(0),
        ))),
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_abs_dom_only() {
    let e = Located::dummy(urweb::core::Expression::Abs(
        "x".into(),
        Located::dummy(Constructor::Unit),
        Located::dummy(Constructor::Named(1)),
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_capp_con_only() {
    let e = Located::dummy(urweb::core::Expression::CApp(
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        Located::dummy(Constructor::Unit),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_record_val_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Record(vec![(
        unit.clone(),
        prim,
        unit,
    )]));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_field_field_c_only() {
    // Field: only field_c matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(2)),
        rest: Located::dummy(Constructor::Named(3)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Field(
        Box::new(prim),
        Located::dummy(Constructor::Unit),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_field_field_only() {
    // Field: only meta.field matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Unit),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Field(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_field_rest_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: unit,
    };
    let e = Located::dummy(urweb::core::Expression::Field(
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_cut_rec_only() {
    // Cut: only rec matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Cut(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_cut_field_c_only() {
    // Cut: only field_c matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(2)),
        rest: Located::dummy(Constructor::Named(3)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Cut(
        Box::new(prim),
        Located::dummy(Constructor::Unit),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_cut_field_only() {
    // Cut: only meta.field matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Unit),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Cut(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_cut_rest_only() {
    // Cut: only meta.rest matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: unit,
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Cut(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_cutmulti_rec_only() {
    // CutMulti: only rec matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = urweb::core::RestMeta {
        rest: Located::dummy(Constructor::Named(1)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::CutMulti(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_cutmulti_field_c_only() {
    // CutMulti: only field_c matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = urweb::core::RestMeta {
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::CutMulti(
        Box::new(prim),
        Located::dummy(Constructor::Unit),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_cutmulti_rest_only() {
    // CutMulti: only meta.rest matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = urweb::core::RestMeta { rest: unit };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::CutMulti(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_concat_e2_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Concat(
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        unit.clone(),
        Box::new(prim),
        unit,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_con_cs_only() {
    // Exp::Con: only constructor in cs matches, not arg
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(urweb::core::Expression::Constructor(
        urweb::datatype_kind::DatatypeKind::Default,
        urweb::core::PatternConstructor::Var(0),
        vec![unit],
        Some(Box::new(Located::dummy(urweb::core::Expression::Rel(0)))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_con_arg_only() {
    // Exp::Con: only arg matches
    let _unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Constructor(
        urweb::datatype_kind::DatatypeKind::Default,
        urweb::core::PatternConstructor::Var(0),
        vec![Located::dummy(Constructor::Named(1))],
        Some(Box::new(prim)),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_ffiapp_ae_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::FfiApp(
        "M".into(),
        "f".into(),
        vec![(prim, unit)],
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_ffiapp_ac_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(urweb::core::Expression::FfiApp(
        "M".into(),
        "f".into(),
        vec![(Located::dummy(urweb::core::Expression::Rel(0)), unit)],
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_abs_body_only() {
    // Abs: only body matches (dom and ran don't). Catches || in dom||ran||body.
    let _unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Abs(
        "x".into(),
        Located::dummy(Constructor::Named(1)),
        Located::dummy(Constructor::Named(2)),
        Box::new(prim),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_abs_ran_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(urweb::core::Expression::Abs(
        "x".into(),
        Located::dummy(Constructor::Named(1)),
        unit,
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_kapp_ef_only() {
    // KApp: only ef matches. Catches || in exists(ef)||exists(k).
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::KApp(
        Box::new(prim),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_kapp_kind_only() {
    // KApp: only kind matches.
    let e = Located::dummy(urweb::core::Expression::KApp(
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        Box::new(Located::dummy(Kind::Rel(5))),
    ));
    assert!(expression::exists(
        &e,
        &|kr| matches!(&kr.node, Kind::Rel(5)),
        &|_| false,
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_capp_ef_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::CApp(Box::new(prim), unit));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_cabs_body_only() {
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::CAbs(
        "a".into(),
        Box::new(Located::dummy(Kind::Type)),
        Box::new(prim),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_record_name_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(urweb::core::Expression::Record(vec![(
        unit,
        Located::dummy(urweb::core::Expression::Rel(0)),
        Located::dummy(Constructor::Named(1)),
    )]));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_field_rec_only() {
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Field(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_concat_e1_c1_e2_c2_each() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Concat(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        unit,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_case_disc_only() {
    // Case: only disc matches.
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let meta = urweb::core::CaseMeta {
        disc: Located::dummy(Constructor::Named(1)),
        result: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(urweb::core::Expression::Case(
        Box::new(prim),
        vec![(
            Located::dummy(urweb::core::Pattern::Var("_".into(), unit)),
            Located::dummy(urweb::core::Expression::Rel(0)),
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_case_disc_meta_only() {
    // Case: only case_meta.disc matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = urweb::core::CaseMeta {
        disc: unit,
        result: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(urweb::core::Expression::Case(
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        vec![(
            Located::dummy(urweb::core::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Named(1)),
            )),
            Located::dummy(urweb::core::Expression::Rel(0)),
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_case_result_only() {
    // Case: only case_meta.result matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = urweb::core::CaseMeta {
        disc: Located::dummy(Constructor::Named(1)),
        result: unit,
    };
    let e = Located::dummy(urweb::core::Expression::Case(
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        vec![(
            Located::dummy(urweb::core::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Named(2)),
            )),
            Located::dummy(urweb::core::Expression::Rel(0)),
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_expression_exists_case_arm_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let meta = urweb::core::CaseMeta {
        disc: Located::dummy(Constructor::Named(1)),
        result: unit.clone(),
    };
    let e = Located::dummy(urweb::core::Expression::Case(
        Box::new(Located::dummy(urweb::core::Expression::Rel(0))),
        vec![(
            Located::dummy(urweb::core::Pattern::Var("_".into(), unit)),
            prim,
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_closure() {
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::Closure(0, vec![prim]));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_servercall_args_only() {
    let prim = Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
        0,
    )));
    let e = Located::dummy(urweb::core::Expression::ServerCall(
        0,
        vec![prim],
        Located::dummy(Constructor::Unit),
        urweb::settings::FailureMode::Error,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, urweb::core::Expression::Prim(_)),
    ));
}

#[test]
fn integration_expression_exists_servercall_ty_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(urweb::core::Expression::ServerCall(
        0,
        vec![Located::dummy(urweb::core::Expression::Rel(0))],
        unit,
        urweb::settings::FailureMode::Error,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
}

#[test]
fn integration_decl_map_and_fold() {
    let span = span();
    let d = Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
                0,
            ))),
            "".into(),
        ),
        span,
    );

    let d2 = declaration::map(d.clone(), &|k| k, &|c| c, &|e| e, &|d| d);
    assert!(matches!(d2.node, Declaration::Val(_, _, _, _, _)));

    let count = declaration::fold(
        &d,
        0usize,
        &|_, acc| acc + 1,
        &|_, acc| acc + 1,
        &|_, acc| acc + 1,
        &|_, acc| acc + 1,
    );
    assert!(count >= 1);
}

#[test]
fn integration_file_max_name_after_decl_binds() {
    let span = span();
    let decls = vec![
        Located::new(
            Declaration::Constructor(
                "T".into(),
                50,
                Located::dummy(Kind::Type),
                Located::dummy(Constructor::Unit),
            ),
            span.clone(),
        ),
        Located::new(
            Declaration::Val(
                "v".into(),
                100,
                Located::dummy(Constructor::Unit),
                Located::dummy(urweb::core::Expression::Prim(urweb::primitives::Prim::Int(
                    0,
                ))),
                "".into(),
            ),
            span,
        ),
    ];

    let max = file::max_name(&decls);
    assert_eq!(max, 100);

    let env = Env::empty().bind_file(&decls);
    env.lookup_c_named(50).unwrap();
    env.lookup_e_named(100).unwrap();
}

#[test]
fn integration_env_decl_binds_con_and_val() {
    let span = span();
    let decls = vec![
        Located::new(
            Declaration::Constructor(
                "T".into(),
                1,
                Located::dummy(Kind::Type),
                Located::dummy(Constructor::Unit),
            ),
            span.clone(),
        ),
        Located::new(
            Declaration::Val(
                "x".into(),
                2,
                Located::dummy(Constructor::Named(1)),
                Located::dummy(urweb::core::Expression::Rel(0)),
                "".into(),
            ),
            span,
        ),
    ];

    let env = Env::empty().bind_file(&decls);
    let (name, _, _) = env.lookup_c_named(1).unwrap();
    assert_eq!(name, "T");
    let (name, _) = env.lookup_e_named(2).unwrap();
    assert_eq!(name, "x");
}

#[test]
fn integration_pat_binds_with_env() {
    let ty = Located::dummy(Constructor::Unit);
    let p = Located::dummy(Pattern::Record(vec![
        (
            "a".into(),
            Located::dummy(Pattern::Var("x".into(), ty.clone())),
            ty.clone(),
        ),
        (
            "b".into(),
            Located::dummy(Pattern::Var("y".into(), ty.clone())),
            ty.clone(),
        ),
    ]));

    let n = urweb::core::environment::pat_binds_n(&p);
    assert_eq!(n, 2);

    let binds = urweb::core::environment::pat_binds_list(&p);
    assert_eq!(binds.len(), 2);
    assert!(binds.iter().any(|(s, _)| s == "x"));
    assert!(binds.iter().any(|(s, _)| s == "y"));
}
