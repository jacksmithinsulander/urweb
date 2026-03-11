//! Integration tests for the Core module.
//!
//! These tests exercise the Core AST utilities and environment
//! as a cohesive unit, including classify_datatype, traversal (map/fold/exists),
//! file::max_name, Env building and lookup, and decl_binds.
//!
//! Also includes tests for the core pipeline (reduce, especialize, effectize)
//! with exact assertions to catch missed mutants.

use urweb::compiler;
use urweb::core::environment::Env;
use urweb::core::utilities::{classify_datatype, constructor, declaration, expression, file, kind};
use urweb::core::{
    Constructor, Declaration, Expression, FieldMeta, Kind, LocatedConstructor, Pattern,
};
use urweb::datatype_kind::DatatypeKind;
use urweb::error_types::{Located, Span};
use urweb::export::{Effect, ExportKind};

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
fn integration_env_lookup_datatype_unbound_returns_err() {
    // Catches mutant: replace lookup_datatype result with Some/Default - unbound must return Err.
    let env = Env::empty();
    let result = env.lookup_datatype(999);
    assert!(
        result.is_err(),
        "lookup_datatype for unbound id must return Err (catches replace with Ok/Some mutant)"
    );
    let err = result.unwrap_err();
    assert!(
        format!("{}", err).contains("999"),
        "error message must mention unbound id"
    );
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

#[test]
fn integration_core_reduce_preserves_exact_decl_count() {
    // Kills: mutant that drops decls. Exact count assertion.
    let span = span();
    let file: urweb::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(42))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_reduce(file, &urweb::settings::Settings::default());
    assert_eq!(
        result.len(),
        2,
        "core_reduce must preserve exact decl count (catches drop-decl mutant)"
    );
}

#[test]
fn integration_core_especialize_preserves_exact_decl_count() {
    // Kills: mutant that drops or duplicates decls.
    let span = span();
    let file: urweb::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_especialize(file);
    assert_eq!(
        result.len(),
        2,
        "core_especialize must preserve exact decl count"
    );
}

#[test]
fn integration_core_effectize_preserves_exact_decl_count() {
    // Kills: mutant that drops decls in effectize.
    let span = span();
    let file: urweb::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_effectize(file, &urweb::settings::Settings::default());
    assert_eq!(
        result.len(),
        2,
        "core_effectize must preserve exact decl count"
    );
}

#[test]
fn integration_core_reduce_preserves_expression_shape() {
    // Kills: mutant that corrupts Val body. Assert expression stays Prim.
    let span = span();
    let file: urweb::core::File = vec![Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(17))),
            "".into(),
        ),
        span,
    )];
    let result = compiler::core_reduce(file, &urweb::settings::Settings::default());
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val decl");
    };
    assert!(
        matches!(
            body.node,
            Expression::Prim(urweb::primitives::Prim::Int(17))
        ),
        "core_reduce must preserve Prim expression shape"
    );
}

#[test]
fn integration_core_reduce_preserves_record_expression() {
    // Kills: passive() Record arm, count_exp_rec Record arm — reduce must not drop Record.
    let span = span();
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Record(vec![(
        unit.clone(),
        Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(1))),
        unit.clone(),
    )]));
    let file: urweb::core::File = vec![Located::new(
        Declaration::Val("x".into(), 1, unit.clone(), e, "".into()),
        span,
    )];
    let result = compiler::core_reduce(file, &urweb::settings::Settings::default());
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val");
    };
    assert!(
        matches!(&body.node, Expression::Record(_)),
        "core_reduce must preserve Record expression (catches passive/count_exp_rec Record arm)"
    );
}

#[test]
fn integration_core_reduce_preserves_constructor_with_payload() {
    // Kills: passive() Constructor(_, _, _, Some(inner)) arm.
    let span = span();
    let unit = Located::dummy(Constructor::Unit);
    let inner = Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(2)));
    let e = Located::dummy(Expression::Constructor(
        DatatypeKind::Option,
        urweb::core::PatternConstructor::Var(0),
        vec![unit.clone()],
        Some(Box::new(inner)),
    ));
    let file: urweb::core::File = vec![Located::new(
        Declaration::Val("x".into(), 1, unit, e, "".into()),
        span,
    )];
    let result = compiler::core_reduce(file, &urweb::settings::Settings::default());
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val");
    };
    assert!(
        matches!(&body.node, Expression::Constructor(_, _, _, Some(_))),
        "core_reduce must preserve Constructor with payload (catches passive Constructor arm)"
    );
}

#[test]
fn integration_core_reduce_local_preserves_decl_count() {
    // Kills: local_reduction mutants that drop decls.
    let span = span();
    let file: urweb::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_reduce_local(file);
    assert_eq!(
        result.len(),
        2,
        "core_reduce_local must preserve decl count"
    );
}

#[test]
fn integration_core_reduce_local_preserves_expression_shape() {
    // Kills: shift_exp/corrupt mutants.
    let span = span();
    let file: urweb::core::File = vec![Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(7))),
            "".into(),
        ),
        span,
    )];
    let result = compiler::core_reduce_local(file);
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val");
    };
    assert!(
        matches!(body.node, Expression::Prim(urweb::primitives::Prim::Int(7))),
        "core_reduce_local must preserve Prim shape"
    );
}

#[test]
fn integration_core_unpoly_preserves_decl_count() {
    // Kills: unpoly mutants that drop decls.
    let span = span();
    let file: urweb::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_unpoly(file);
    assert_eq!(result.len(), 2, "core_unpoly must preserve decl count");
}

#[test]
fn integration_core_untangle_preserves_non_valrec_decls() {
    // Kills: untangle mutants that drop or corrupt non-ValRec decls.
    let span = span();
    let file: urweb::core::File = vec![
        Located::new(Declaration::Database("db".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "v".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_untangle(file);
    assert_eq!(result.len(), 2);
    assert!(matches!(&result[0].node, Declaration::Database(_)));
    assert!(matches!(&result[1].node, Declaration::Val(_, 1, _, _, _)));
}

#[test]
fn integration_core_rpcify_rewrites_rpc_call_to_server_call_and_export() {
    // Catches rpcify mutants: Basis.rpc guard, match arms, rewrite logic.
    // Build: rpc ref (id 1), transaction fn (id 2), main that does rpc(trans).
    let sp = span();
    let unit_con = Located::dummy(Constructor::Unit);
    let transaction_unit = Located::dummy(Constructor::App(
        Box::new(Located::dummy(Constructor::Ffi(
            "Basis".into(),
            "transaction".into(),
        ))),
        Box::new(unit_con.clone()),
    ));
    let txn_type = Located::dummy(Constructor::TFun(
        Box::new(unit_con.clone()),
        Box::new(transaction_unit),
    ));
    let txn_body = Located::dummy(Expression::Abs(
        "x".into(),
        unit_con.clone(),
        Located::dummy(Constructor::App(
            Box::new(Located::dummy(Constructor::Ffi(
                "Basis".into(),
                "transaction".into(),
            ))),
            Box::new(unit_con.clone()),
        )),
        Box::new(Located::dummy(Expression::Prim(
            urweb::primitives::Prim::Int(0),
        ))),
    ));
    let rpc_call = Located::dummy(Expression::App(
        Box::new(Located::dummy(Expression::CApp(
            Box::new(Located::dummy(Expression::Ffi(
                "Basis".into(),
                "rpc".into(),
            ))),
            unit_con.clone(),
        ))),
        Box::new(Located::dummy(Expression::Named(2))),
    ));
    let file: urweb::core::File = vec![
        Located::new(
            Declaration::Val(
                "rpc".into(),
                1,
                unit_con.clone(),
                Located::dummy(Expression::Ffi("Basis".into(), "rpc".into())),
                "".into(),
            ),
            sp.clone(),
        ),
        Located::new(
            Declaration::Val("myTxn".into(), 2, txn_type, txn_body, "".into()),
            sp.clone(),
        ),
        Located::new(
            Declaration::Val("main".into(), 3, unit_con, rpc_call, "".into()),
            sp,
        ),
    ];
    let mut errors = urweb::error_types::ErrorReporter::new();
    let mut settings = urweb::settings::Settings::default();
    let result = compiler::core_rpcify(file, &mut settings, &mut errors);
    let out = result.expect("rpcify must succeed");
    let has_server_call = out.iter().any(|d| {
        urweb::core::utilities::declaration::exists(
            d,
            &|_| false,
            &|_| false,
            &|e| matches!(&e.node, Expression::ServerCall(2, _, _, _)),
            &|_| false,
        )
    });
    assert!(
        has_server_call,
        "rpcify must rewrite rpc(trans) to ServerCall(2, ...)"
    );
    let has_rpc_export = out.iter().any(|d| {
        matches!(
            &d.node,
            Declaration::Export(ExportKind::Rpc(Effect::ReadWrite), 2, false)
        )
    });
    assert!(
        has_rpc_export,
        "rpcify must emit Export(Rpc(ReadWrite), 2, false) for the transaction"
    );
}

#[test]
fn integration_core_specialize_preserves_decl_count() {
    // Catches specialize mutants: must not drop decls.
    let span = span();
    let file: urweb::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_specialize(file);
    assert_eq!(result.len(), 2, "core_specialize must preserve decl count");
}

#[test]
fn integration_core_specialize_preserves_expression_shape() {
    // Catches specialize mutants that corrupt Val body.
    let span = span();
    let file: urweb::core::File = vec![Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(Expression::Prim(urweb::primitives::Prim::Int(99))),
            "".into(),
        ),
        span,
    )];
    let result = compiler::core_specialize(file);
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val decl");
    };
    assert!(
        matches!(
            body.node,
            Expression::Prim(urweb::primitives::Prim::Int(99))
        ),
        "core_specialize must preserve Prim expression shape"
    );
}

// ---------------------------------------------------------------------------
// check_termination — kills "replace check_termination with ()" mutant
// ---------------------------------------------------------------------------

#[test]
fn integration_check_termination_rejects_non_terminating_valrec() {
    // Build a Core file with a ValRec that calls itself with the same argument (no structural decrease).
    // The termination checker must report an error (kills "replace check_termination with ()").
    use urweb::error_types::ErrorReporter;

    let unit_con = Located::dummy(Constructor::Unit);
    let ret_con = Located::dummy(Constructor::Named(1));
    let ty = Located::dummy(Constructor::TFun(
        Box::new(unit_con.clone()),
        Box::new(ret_con.clone()),
    ));
    // body: \x. f x  — recursive call with same arg, no decrease
    let rec_call = Located::dummy(Expression::App(
        Box::new(Located::dummy(Expression::Named(0))),
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    let body = Located::dummy(Expression::Abs(
        "x".into(),
        unit_con.clone(),
        ret_con,
        Box::new(rec_call),
    ));
    let file: urweb::core::File = vec![Located::dummy(Declaration::ValRec(vec![(
        "f".into(),
        0,
        ty,
        body,
        "".into(),
    )]))];
    let mut errors = ErrorReporter::new();
    compiler::check_termination(&file, &mut errors);
    assert!(
        errors.has_errors(),
        "check_termination must reject non-terminating ValRec (kills replace with () mutant)"
    );
}

#[test]
fn integration_check_termination_accepts_terminating_valrec() {
    // ValRec with non-recursive body: no recursive call, so no error.
    use urweb::error_types::ErrorReporter;

    let unit_con = Located::dummy(Constructor::Unit);
    let ty = Located::dummy(Constructor::TFun(
        Box::new(unit_con.clone()),
        Box::new(unit_con.clone()),
    ));
    let body = Located::dummy(Expression::Abs(
        "x".into(),
        unit_con.clone(),
        unit_con.clone(),
        Box::new(Located::dummy(Expression::Prim(
            urweb::primitives::Prim::Int(0),
        ))),
    ));
    let file: urweb::core::File = vec![Located::dummy(Declaration::ValRec(vec![(
        "f".into(),
        0,
        ty,
        body,
        "".into(),
    )]))];
    let mut errors = ErrorReporter::new();
    compiler::check_termination(&file, &mut errors);
    assert!(
        !errors.has_errors(),
        "check_termination must accept terminating ValRec"
    );
}
