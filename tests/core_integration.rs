//! Integration tests for the Core module.
//!
//! These tests exercise the Core AST utilities and environment
//! as a cohesive unit, including classify_datatype, traversal (map/fold/exists),
//! file::max_name, Env building and lookup, and decl_binds.
//!
//! Also includes tests for the core pipeline (reduce, especialize, effectize)
//! with exact assertions to catch missed mutants.

use anyhow::Context as _;
use ur::compiler;
use ur::core::environment::Env;
use ur::core::utilities::{classify_datatype, constructor, declaration, expression, file, kind};
use ur::core::{
    Constructor, Declaration, Expression, FieldMeta, Kind, LocatedConstructor, LocatedExpression,
    Pattern,
};
use ur::datatype_kind::DatatypeKind;
use ur::error_types::{Located, Span};
use ur::export::{Effect, ExportKind};

fn span() -> Span {
    Span::dummy()
}

#[test]
fn integration_classify_then_env_datatype() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Classify a datatype and then register it in the environment.
    let constructor_specifications: Vec<(String, usize, Option<LocatedConstructor>)> = vec![
        ("None".into(), 0, None),
        ("Some".into(), 1, Some(Located::dummy(Constructor::Unit))),
    ];
    let datatype_kind = classify_datatype(&constructor_specifications);
    assert_eq!(datatype_kind, DatatypeKind::Option);

    let env = Env::empty().push_datatype(10, vec!["a".into()], constructor_specifications);
    // look up datatype with id 10; must succeed since it was just pushed
    let (params, constrs) = match env.lookup_datatype(10) {
        Ok(v) => v,
        Err(e) => panic!("lookup_datatype(10) failed: {e}"),
    };
    assert_eq!(params.len(), 1);
    assert_eq!(constrs.len(), 2);

    // look up constructor named "Some"; must succeed since it was registered with the datatype
    let some_info = match env.lookup_constructor("Some") {
        Some(info) => info,
        None => panic!("lookup_constructor(\"Some\") returned None"),
    };
    assert_eq!(some_info.1, 10);
    assert_eq!(some_info.4, 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_kind_traversal_then_compare() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_kind_compare_each_variant() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_kind_compare_differing_variants_not_equal() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_con_traversal() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_first_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::TFun(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Named(99))),
    ));
    assert!(constructor::exists(&c, &|_| false, &|cc| matches!(
        &cc.node,
        Constructor::Unit
    )));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_second_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::TFun(
        Box::new(Located::dummy(Constructor::Named(1))),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(constructor::exists(&c, &|_| false, &|cc| matches!(
        &cc.node,
        Constructor::Unit
    )));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_tcfun_kind_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_kapp_first_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(constructor::exists(&c, &|_| false, &|cc| matches!(
        &cc.node,
        Constructor::Unit
    )));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_kapp_second_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Rel(0))),
        Box::new(Located::dummy(Kind::Rel(3))),
    ));
    assert!(constructor::exists(
        &c,
        &|kr| matches!(&kr.node, Kind::Rel(3)),
        &|_| false
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_compare_differing_rels() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c1 = Located::dummy(Constructor::Rel(0));
    let c2 = Located::dummy(Constructor::Rel(1));
    assert!(constructor::compare(&c1, &c2) != std::cmp::Ordering::Equal);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_compare_pair_list() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_compare_differing_variants_not_equal() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_compare_same_variant_different_content_not_equal() -> anyhow::Result<()>
{
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_compare_list_differing_middle() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_compare_pair_list_differing() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_map_k1_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_map_k2_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_record_value_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_exp_traversal() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Build an expression, map and check exists.
    let e = Located::dummy(ur::core::Expression::Let(
        "x".into(),
        Located::dummy(Constructor::Unit),
        Box::new(Located::dummy(ur::core::Expression::Prim(
            ur::primitives::Prim::Int(42),
        ))),
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
    ));

    let e2 = expression::map(e.clone(), &|k| k, &|c| c, &|e| e);
    assert!(matches!(e2.node, ur::core::Expression::Let(_, _, _, _)));

    let has_prim = expression::exists(&e, &|_| false, &|_| false, &|e| {
        matches!(e.node, ur::core::Expression::Prim(_))
    });
    assert!(has_prim);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_app_first_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e = Located::dummy(ur::core::Expression::App(
        Box::new(Located::dummy(ur::core::Expression::Prim(
            ur::primitives::Prim::Int(0),
        ))),
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_abs_dom_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e = Located::dummy(ur::core::Expression::Abs(
        "x".into(),
        Located::dummy(Constructor::Unit),
        Located::dummy(Constructor::Named(1)),
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_capp_con_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e = Located::dummy(ur::core::Expression::CApp(
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        Located::dummy(Constructor::Unit),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_record_val_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Record(vec![(
        unit.clone(),
        prim,
        unit,
    )]));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_field_field_c_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Field: only field_c matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(2)),
        rest: Located::dummy(Constructor::Named(3)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Field(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_field_field_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Field: only meta.field matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Unit),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Field(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_field_rest_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: unit,
    };
    let e = Located::dummy(ur::core::Expression::Field(
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cut_rec_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Cut: only rec matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Cut(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cut_field_c_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Cut: only field_c matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(2)),
        rest: Located::dummy(Constructor::Named(3)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Cut(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cut_field_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Cut: only meta.field matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Unit),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Cut(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cut_rest_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Cut: only meta.rest matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: unit,
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Cut(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cutmulti_rec_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // CutMulti: only rec matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = ur::core::RestMeta {
        rest: Located::dummy(Constructor::Named(1)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::CutMulti(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cutmulti_field_c_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // CutMulti: only field_c matches.
    let _unit = Located::dummy(Constructor::Unit);
    let meta = ur::core::RestMeta {
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::CutMulti(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cutmulti_rest_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // CutMulti: only meta.rest matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = ur::core::RestMeta { rest: unit };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::CutMulti(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_concat_e2_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Concat(
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        unit.clone(),
        Box::new(prim),
        unit,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_con_cs_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Exp::Con: only constructor in cs matches, not arg
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ur::core::Expression::Constructor(
        ur::datatype_kind::DatatypeKind::Default,
        ur::core::PatternConstructor::Var(0),
        vec![unit],
        Some(Box::new(Located::dummy(ur::core::Expression::Rel(0)))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_con_arg_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Exp::Con: only arg matches
    let _unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Constructor(
        ur::datatype_kind::DatatypeKind::Default,
        ur::core::PatternConstructor::Var(0),
        vec![Located::dummy(Constructor::Named(1))],
        Some(Box::new(prim)),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_ffiapp_ae_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::FfiApp(
        "M".into(),
        "f".into(),
        vec![(prim, unit)],
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_ffiapp_ac_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ur::core::Expression::FfiApp(
        "M".into(),
        "f".into(),
        vec![(Located::dummy(ur::core::Expression::Rel(0)), unit)],
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_abs_body_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Abs: only body matches (dom and ran don't). Catches || in dom||ran||body.
    let _unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Abs(
        "x".into(),
        Located::dummy(Constructor::Named(1)),
        Located::dummy(Constructor::Named(2)),
        Box::new(prim),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_abs_ran_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ur::core::Expression::Abs(
        "x".into(),
        Located::dummy(Constructor::Named(1)),
        unit,
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_kapp_ef_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // KApp: only ef matches. Catches || in exists(ef)||exists(k).
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::KApp(
        Box::new(prim),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_kapp_kind_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // KApp: only kind matches.
    let e = Located::dummy(ur::core::Expression::KApp(
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        Box::new(Located::dummy(Kind::Rel(5))),
    ));
    assert!(expression::exists(
        &e,
        &|kr| matches!(&kr.node, Kind::Rel(5)),
        &|_| false,
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_capp_ef_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::CApp(Box::new(prim), unit));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_cabs_body_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::CAbs(
        "a".into(),
        Box::new(Located::dummy(Kind::Type)),
        Box::new(prim),
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_record_name_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ur::core::Expression::Record(vec![(
        unit,
        Located::dummy(ur::core::Expression::Rel(0)),
        Located::dummy(Constructor::Named(1)),
    )]));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_field_rec_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let _unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Field(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_concat_e1_c1_e2_c2_each() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Concat(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        unit,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_case_disc_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Case: only disc matches.
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let meta = ur::core::CaseMeta {
        disc: Located::dummy(Constructor::Named(1)),
        result: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(ur::core::Expression::Case(
        Box::new(prim),
        vec![(
            Located::dummy(ur::core::Pattern::Var("_".into(), unit)),
            Located::dummy(ur::core::Expression::Rel(0)),
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_case_disc_meta_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Case: only case_meta.disc matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = ur::core::CaseMeta {
        disc: unit,
        result: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(ur::core::Expression::Case(
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        vec![(
            Located::dummy(ur::core::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Named(1)),
            )),
            Located::dummy(ur::core::Expression::Rel(0)),
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_case_result_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Case: only case_meta.result matches.
    let unit = Located::dummy(Constructor::Unit);
    let meta = ur::core::CaseMeta {
        disc: Located::dummy(Constructor::Named(1)),
        result: unit,
    };
    let e = Located::dummy(ur::core::Expression::Case(
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        vec![(
            Located::dummy(ur::core::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Named(2)),
            )),
            Located::dummy(ur::core::Expression::Rel(0)),
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_case_arm_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let meta = ur::core::CaseMeta {
        disc: Located::dummy(Constructor::Named(1)),
        result: unit.clone(),
    };
    let e = Located::dummy(ur::core::Expression::Case(
        Box::new(Located::dummy(ur::core::Expression::Rel(0))),
        vec![(
            Located::dummy(ur::core::Pattern::Var("_".into(), unit)),
            prim,
        )],
        meta,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_closure() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::Closure(0, vec![prim]));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_servercall_args_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let prim = Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(ur::core::Expression::ServerCall(
        0,
        vec![prim],
        Located::dummy(Constructor::Unit),
        ur::settings::FailureMode::Error,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|_| false,
        &|ex| matches!(ex.node, ur::core::Expression::Prim(_)),
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_servercall_ty_only() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ur::core::Expression::ServerCall(
        0,
        vec![Located::dummy(ur::core::Expression::Rel(0))],
        unit,
        ur::settings::FailureMode::Error,
    ));
    assert!(expression::exists(
        &e,
        &|_| false,
        &|c| matches!(&c.node, Constructor::Unit),
        &|_| false,
    ));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_decl_map_and_fold() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let span = span();
    let d = Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0))),
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_file_max_name_after_decl_binds() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
                Located::dummy(ur::core::Expression::Prim(ur::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];

    let max = file::max_name(&decls);
    assert_eq!(max, 100);

    let env = Env::empty().bind_file(&decls);
    // verify constructor with id 50 is bound after bind_file; failure means a decl was not registered
    match env.lookup_c_named(50) {
        Ok(_) => {}
        Err(e) => panic!("lookup_c_named(50) failed: {e}"),
    }
    // verify expression with id 100 is bound after bind_file; failure means a decl was not registered
    match env.lookup_e_named(100) {
        Ok(_) => {}
        Err(e) => panic!("lookup_e_named(100) failed: {e}"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_env_decl_binds_con_and_val() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
                Located::dummy(ur::core::Expression::Rel(0)),
                "".into(),
            ),
            span,
        ),
    ];

    let env = Env::empty().bind_file(&decls);
    // look up constructor with id 1; must succeed after bind_file with a Constructor decl
    let (name, _, _) = match env.lookup_c_named(1) {
        Ok(v) => v,
        Err(e) => panic!("lookup_c_named(1) failed: {e}"),
    };
    assert_eq!(name, "T");
    // look up expression with id 2; must succeed after bind_file with a Val decl
    let (name, _) = match env.lookup_e_named(2) {
        Ok(v) => v,
        Err(e) => panic!("lookup_e_named(2) failed: {e}"),
    };
    assert_eq!(name, "x");
    Ok(()) // return success to the test harness
}

#[test]
fn integration_env_lookup_datatype_unbound_returns_err() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_pat_binds_with_env() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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

    let n = ur::core::environment::pat_binds_n(&p);
    assert_eq!(n, 2);

    let binds = ur::core::environment::pat_binds_list(&p);
    assert_eq!(binds.len(), 2);
    assert!(binds.iter().any(|(s, _)| s == "x"));
    assert!(binds.iter().any(|(s, _)| s == "y"));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_reduce_preserves_exact_decl_count() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: mutant that drops decls. Exact count assertion.
    let span = span();
    let file: ur::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(ur::primitives::Prim::Int(42))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_reduce(file, &ur::settings::Settings::default());
    assert_eq!(
        result.len(),
        2,
        "core_reduce must preserve exact decl count (catches drop-decl mutant)"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_especialize_preserves_exact_decl_count() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: mutant that drops or duplicates decls.
    let span = span();
    let file: ur::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_effectize_preserves_exact_decl_count() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: mutant that drops decls in effectize.
    let span = span();
    let file: ur::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_effectize(file, &ur::settings::Settings::default());
    assert_eq!(
        result.len(),
        2,
        "core_effectize must preserve exact decl count"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_reduce_preserves_expression_shape() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: mutant that corrupts Val body. Assert expression stays Prim.
    let span = span();
    let file: ur::core::File = vec![Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(Expression::Prim(ur::primitives::Prim::Int(17))),
            "".into(),
        ),
        span,
    )];
    let result = compiler::core_reduce(file, &ur::settings::Settings::default());
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val decl");
    };
    assert!(
        matches!(body.node, Expression::Prim(ur::primitives::Prim::Int(17))),
        "core_reduce must preserve Prim expression shape"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_reduce_preserves_record_expression() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: passive() Record arm, count_exp_rec Record arm — reduce must not drop Record.
    let span = span();
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Record(vec![(
        unit.clone(),
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(1))),
        unit.clone(),
    )]));
    let file: ur::core::File = vec![Located::new(
        Declaration::Val("x".into(), 1, unit.clone(), e, "".into()),
        span,
    )];
    let result = compiler::core_reduce(file, &ur::settings::Settings::default());
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val");
    };
    assert!(
        matches!(&body.node, Expression::Record(_)),
        "core_reduce must preserve Record expression (catches passive/count_exp_rec Record arm)"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_reduce_preserves_constructor_with_payload() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: passive() Constructor(_, _, _, Some(inner)) arm.
    let span = span();
    let unit = Located::dummy(Constructor::Unit);
    let inner = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(2)));
    let e = Located::dummy(Expression::Constructor(
        DatatypeKind::Option,
        ur::core::PatternConstructor::Var(0),
        vec![unit.clone()],
        Some(Box::new(inner)),
    ));
    let file: ur::core::File = vec![Located::new(
        Declaration::Val("x".into(), 1, unit, e, "".into()),
        span,
    )];
    let result = compiler::core_reduce(file, &ur::settings::Settings::default());
    assert_eq!(result.len(), 1);
    let Declaration::Val(_, _, _, body, _) = &result[0].node else {
        panic!("expected Val");
    };
    assert!(
        matches!(&body.node, Expression::Constructor(_, _, _, Some(_))),
        "core_reduce must preserve Constructor with payload (catches passive Constructor arm)"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_reduce_local_preserves_decl_count() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: local_reduction mutants that drop decls.
    let span = span();
    let file: ur::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_reduce_local_preserves_expression_shape() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: shift_exp/corrupt mutants.
    let span = span();
    let file: ur::core::File = vec![Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(Expression::Prim(ur::primitives::Prim::Int(7))),
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
        matches!(body.node, Expression::Prim(ur::primitives::Prim::Int(7))),
        "core_reduce_local must preserve Prim shape"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_unpoly_preserves_decl_count() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: unpoly mutants that drop decls.
    let span = span();
    let file: ur::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_unpoly(file);
    assert_eq!(result.len(), 2, "core_unpoly must preserve decl count");
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_untangle_preserves_non_valrec_decls() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Kills: untangle mutants that drop or corrupt non-ValRec decls.
    let span = span();
    let file: ur::core::File = vec![
        Located::new(Declaration::Database("db".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "v".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_untangle(file);
    assert_eq!(result.len(), 2);
    assert!(matches!(&result[0].node, Declaration::Database(_)));
    assert!(matches!(&result[1].node, Declaration::Val(_, 1, _, _, _)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_rpcify_rewrites_rpc_call_to_server_call_and_export() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
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
        Box::new(Located::dummy(Expression::Prim(ur::primitives::Prim::Int(
            0,
        )))),
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
    let file: ur::core::File = vec![
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
    let mut errors = ur::error_types::ErrorReporter::new_silent();
    let settings = ur::settings::Settings::default();
    let result = compiler::core_rpcify(file, &settings, &mut errors);
    let out = result.with_context(|| "rpcify must succeed")?;
    let has_server_call = out.iter().any(|d| {
        ur::core::utilities::declaration::exists(
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
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_specialize_preserves_decl_count() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Catches specialize mutants: must not drop decls.
    let span = span();
    let file: ur::core::File = vec![
        Located::new(Declaration::Database("d".into()), span.clone()),
        Located::new(
            Declaration::Val(
                "x".into(),
                1,
                Located::dummy(Constructor::Unit),
                Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
                "".into(),
            ),
            span,
        ),
    ];
    let result = compiler::core_specialize(file);
    assert_eq!(result.len(), 2, "core_specialize must preserve decl count");
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_specialize_preserves_expression_shape() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Catches specialize mutants that corrupt Val body.
    let span = span();
    let file: ur::core::File = vec![Located::new(
        Declaration::Val(
            "x".into(),
            1,
            Located::dummy(Constructor::Unit),
            Located::dummy(Expression::Prim(ur::primitives::Prim::Int(99))),
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
        matches!(body.node, Expression::Prim(ur::primitives::Prim::Int(99))),
        "core_specialize must preserve Prim expression shape"
    );
    Ok(()) // return success to the test harness
}

// ---------------------------------------------------------------------------
// check_termination — kills "replace check_termination with ()" mutant
// ---------------------------------------------------------------------------

#[test]
fn integration_check_termination_rejects_non_terminating_valrec() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Build a Core file with a ValRec that calls itself with the same argument (no structural decrease).
    // The termination checker must report an error (kills "replace check_termination with ()").
    use ur::error_types::ErrorReporter;

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
    let file: ur::core::File = vec![Located::dummy(Declaration::ValRec(vec![(
        "f".into(),
        0,
        ty,
        body,
        "".into(),
    )]))];
    let mut errors = ErrorReporter::new_silent();
    compiler::check_termination(&file, &mut errors);
    assert!(
        errors.has_errors(),
        "check_termination must reject non-terminating ValRec (kills replace with () mutant)"
    );
    Ok(()) // return success to the test harness
}

#[test]
fn integration_check_termination_accepts_terminating_valrec() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // ValRec with non-recursive body: no recursive call, so no error.
    use ur::error_types::ErrorReporter;

    let unit_con = Located::dummy(Constructor::Unit);
    let ty = Located::dummy(Constructor::TFun(
        Box::new(unit_con.clone()),
        Box::new(unit_con.clone()),
    ));
    let body = Located::dummy(Expression::Abs(
        "x".into(),
        unit_con.clone(),
        unit_con.clone(),
        Box::new(Located::dummy(Expression::Prim(ur::primitives::Prim::Int(
            0,
        )))),
    ));
    let file: ur::core::File = vec![Located::dummy(Declaration::ValRec(vec![(
        "f".into(),
        0,
        ty,
        body,
        "".into(),
    )]))];
    let mut errors = ErrorReporter::new_silent();
    compiler::check_termination(&file, &mut errors);
    assert!(
        !errors.has_errors(),
        "check_termination must accept terminating ValRec"
    );
    Ok(()) // return success to the test harness
}

// ---------------------------------------------------------------------------
// Phase 1: global_reduction, local_reduction, unpoly, especialize, specialize,
// export_tagging, marshal_check — kill missed mutants
// ---------------------------------------------------------------------------

use ur::core::global_reduction;
use ur::core::local_reduction;
use ur::core::unpoly;

#[test]
fn integration_local_reduction_shift_con_tfun() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // shift_con on TFun: both branches must be shifted. Catches delete-arm mutants.
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let tfun = Located::dummy(Constructor::TFun(
        Box::new(rel1.clone()),
        Box::new(unit.clone()),
    ));
    let out = local_reduction::shift_con(tfun, 1, 1);
    match &out.node {
        Constructor::TFun(a, b) => {
            assert!(matches!(a.node, Constructor::Rel(2)));
            assert!(matches!(b.node, Constructor::Unit));
        }
        _ => panic!("expected TFun"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_rel() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // shift_exp on Rel: index >= cutoff gets shifted. Catches + -> - mutant.
    let e = Located::dummy(Expression::Rel(2));
    let out = local_reduction::shift_exp(e, 1, 1, 0, 0);
    assert!(matches!(out.node, Expression::Rel(3)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_reduce_con_unit() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::Unit);
    let out = local_reduction::reduce_con(c);
    assert!(matches!(out.node, Constructor::Unit));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_reduce_exp_prim() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(42)));
    let out = local_reduction::reduce_exp(e);
    assert!(matches!(out.node, Expression::Prim(_)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_rel_at_depth() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Rel(0) at depth 0: 0 >= 0, so open. Catches >= -> < mutant.
    let c = Located::dummy(Constructor::Rel(0));
    assert!(unpoly::is_open(&c));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_closed_unit() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Unit has no free Rel, so not open.
    let c_closed = Located::dummy(Constructor::Unit);
    assert!(!unpoly::is_open(&c_closed));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_tfun_recurses() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // TFun(Unit, Rel(1)): Rel(1) at depth 0 is open.
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let tfun = Located::dummy(Constructor::TFun(Box::new(unit), Box::new(rel1)));
    assert!(unpoly::is_open(&tfun));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_unravel_capp_named() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let n = Located::dummy(Expression::Named(99));
    let res = unpoly::unravel_capp(&n);
    assert!(res.is_some());
    // destructure the unravel_capp result; Some was verified on the line above
    let (id, args) = match res {
        Some(v) => v,
        None => panic!("unravel_capp returned None for Named(99)"),
    };
    assert_eq!(id, 99);
    assert!(args.is_empty());
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_unravel_capp_capp_layer() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let named = Located::dummy(Expression::Named(5));
    let unit_con = Located::dummy(Constructor::Unit);
    let capp = Located::dummy(Expression::CApp(Box::new(named), unit_con));
    let res = unpoly::unravel_capp(&capp);
    assert!(res.is_some());
    // destructure the unravel_capp result; Some was verified on the line above
    let (id, args) = match res {
        Some(v) => v,
        None => panic!("unravel_capp returned None for CApp(Named(5), _)"),
    };
    assert_eq!(id, 5);
    assert_eq!(args.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_minimal_val() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::Val("x".into(), 0, unit, prim, "".into()));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_valrec() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let ty = Located::dummy(Constructor::TFun(
        Box::new(unit.clone()),
        Box::new(unit.clone()),
    ));
    let body = Located::dummy(Expression::Abs(
        "x".into(),
        unit.clone(),
        unit.clone(),
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    let decl = Located::dummy(Declaration::ValRec(vec![(
        "f".into(),
        0,
        ty,
        body,
        "".into(),
    )]));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_especialize_minimal() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Val(
        "x".into(),
        0,
        unit,
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
        "".into(),
    ));
    let file: ur::core::File = vec![decl];
    let out = ur::core::especialize::especialize(file);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_specialize_minimal() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Val(
        "x".into(),
        0,
        unit,
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
        "".into(),
    ));
    let file: ur::core::File = vec![decl];
    let out = ur::core::specialize::specialize(file);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_export_tagging_tag_minimal() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Val(
        "x".into(),
        0,
        unit,
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
        "".into(),
    ));
    let file: ur::core::File = vec![decl];
    let mut reported = Vec::new();
    let out = ur::core::export_tagging::tag(file, &mut |_s, payload| {
        reported.push(ur::diagnostics::render_diagnostic_body(
            &payload,
            ur::diagnostics::DiagnosticLocale::En,
        ));
    });
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_marshal_check_accepts_prim() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Val(
        "x".into(),
        0,
        unit,
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
        "".into(),
    ));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let mut errors = ur::error_types::ErrorReporter::new_silent();
    ur::core::marshal_check::check(&file, &settings, &mut errors);
    assert!(!errors.has_errors());
    Ok(()) // return success to the test harness
}

// ---------------------------------------------------------------------------
// Phase 1 expanded: more local_reduction, unpoly, global_reduction, rpc, effect, untangle
// ---------------------------------------------------------------------------

#[test]
fn integration_local_reduction_shift_con_record() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let k = Located::dummy(Kind::Type);
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let rec = Located::dummy(Constructor::Record(Box::new(k), vec![(rel1.clone(), unit)]));
    let out = local_reduction::shift_con(rec, 1, 1);
    match &out.node {
        Constructor::Record(_, pairs) => {
            assert_eq!(pairs.len(), 1);
            assert!(matches!(pairs[0].0.node, Constructor::Rel(2)));
        }
        _ => panic!("expected Record"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_concat() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let concat = Located::dummy(Constructor::Concat(Box::new(rel1.clone()), Box::new(unit)));
    let out = local_reduction::shift_con(concat, 1, 1);
    match &out.node {
        Constructor::Concat(a, b) => {
            assert!(matches!(a.node, Constructor::Rel(2)));
            assert!(matches!(b.node, Constructor::Unit));
        }
        _ => panic!("expected Concat"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_tuple() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel0 = Located::dummy(Constructor::Rel(0));
    let rel1 = Located::dummy(Constructor::Rel(1));
    let tup = Located::dummy(Constructor::Tuple(vec![rel0, rel1]));
    let out = local_reduction::shift_con(tup, 1, 1);
    match &out.node {
        Constructor::Tuple(cs) => {
            assert_eq!(cs.len(), 2);
            assert!(matches!(cs[0].node, Constructor::Rel(0)));
            assert!(matches!(cs[1].node, Constructor::Rel(2)));
        }
        _ => panic!("expected Tuple"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_proj() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel1 = Located::dummy(Constructor::Rel(1));
    let tup = Located::dummy(Constructor::Tuple(vec![rel1]));
    let proj = Located::dummy(Constructor::Proj(Box::new(tup), 0));
    let out = local_reduction::shift_con(proj, 1, 1);
    match &out.node {
        Constructor::Proj(c, n) => {
            assert_eq!(*n, 0);
            if let Constructor::Tuple(cs) = &c.node {
                assert!(matches!(cs[0].node, Constructor::Rel(2)))
            }
        }
        _ => panic!("expected Proj"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_app() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let n = Located::dummy(Constructor::Named(1));
    let rel1 = Located::dummy(Constructor::Rel(1));
    let app = Located::dummy(Constructor::App(Box::new(n), Box::new(rel1)));
    let out = local_reduction::shift_con(app, 1, 1);
    match &out.node {
        Constructor::App(f, a) => {
            assert!(matches!(f.node, Constructor::Named(1)));
            assert!(matches!(a.node, Constructor::Rel(2)));
        }
        _ => panic!("expected App"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_trecord() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel1 = Located::dummy(Constructor::Rel(1));
    let trec = Located::dummy(Constructor::TRecord(Box::new(rel1)));
    let out = local_reduction::shift_con(trec, 1, 1);
    match &out.node {
        Constructor::TRecord(inner) => assert!(matches!(inner.node, Constructor::Rel(2))),
        _ => panic!("expected TRecord"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_app() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel0 = Located::dummy(Expression::Rel(0));
    let rel2 = Located::dummy(Expression::Rel(2));
    let app = Located::dummy(Expression::App(Box::new(rel0), Box::new(rel2)));
    let out = local_reduction::shift_exp(app, 1, 1, 0, 0);
    match &out.node {
        Expression::App(f, a) => {
            assert!(matches!(f.node, Expression::Rel(0)));
            assert!(matches!(a.node, Expression::Rel(3)));
        }
        _ => panic!("expected App"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_sub_con_in_con_rel_replaced() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel0 = Located::dummy(Constructor::Rel(0));
    let out = unpoly::sub_con_in_con(0, &unit, rel0);
    assert!(matches!(out.node, Constructor::Unit));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_sub_con_in_con_rel_unchanged_wrong_depth() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let out = unpoly::sub_con_in_con(0, &unit, rel1);
    assert!(matches!(out.node, Constructor::Rel(1)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_sub_con_in_con_tfun_recurses() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel0 = Located::dummy(Constructor::Rel(0));
    let tfun = Located::dummy(Constructor::TFun(Box::new(rel0), Box::new(unit.clone())));
    let out = unpoly::sub_con_in_con(0, &unit, tfun);
    match &out.node {
        Constructor::TFun(a, b) => {
            assert!(matches!(a.node, Constructor::Unit));
            assert!(matches!(b.node, Constructor::Unit));
        }
        _ => panic!("expected TFun"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_datatype() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let k = Located::dummy(Kind::Type);
    let unit = Located::dummy(Constructor::Unit);
    let dt = ur::core::DatatypeDecl {
        name: "T".into(),
        id: 0,
        params: vec![],
        constrs: vec![("A".into(), 1, None), ("B".into(), 2, Some(unit.clone()))],
    };
    let decl = Located::dummy(Declaration::Datatype(vec![dt]));
    let con = Located::dummy(Declaration::Constructor("C".into(), 3, k, unit.clone()));
    let file: ur::core::File = vec![decl, con];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert!(out.len() >= 2);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_constructor_decl() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let k = Located::dummy(Kind::Type);
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Constructor("C".into(), 0, k, unit));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_sequence() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Sequence("s".into(), 0, "s".into()));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_database() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Database("db".into()));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_rpcify_minimal_val() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Val(
        "x".into(),
        0,
        unit,
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
        "".into(),
    ));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let mut errors = ur::error_types::ErrorReporter::new_silent();
    let result = compiler::core_rpcify(file, &settings, &mut errors);
    assert!(result.is_some());
    // extract the file from the Some; is_some() was asserted above
    let rpcified = match result {
        Some(v) => v,
        None => panic!("core_rpcify returned None for minimal val file"),
    };
    assert_eq!(rpcified.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_effectize_minimal_val() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Val(
        "x".into(),
        0,
        unit,
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
        "".into(),
    ));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = compiler::core_effectize(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_untangle_minimal_val() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Val(
        "x".into(),
        0,
        unit,
        Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0))),
        "".into(),
    ));
    let file: ur::core::File = vec![decl];
    let out = compiler::core_untangle(file);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_especialize_valrec() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let ty = Located::dummy(Constructor::TFun(
        Box::new(unit.clone()),
        Box::new(unit.clone()),
    ));
    let body = Located::dummy(Expression::Abs(
        "x".into(),
        unit.clone(),
        unit.clone(),
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    let decl = Located::dummy(Declaration::ValRec(vec![(
        "f".into(),
        0,
        ty,
        body,
        "".into(),
    )]));
    let file: ur::core::File = vec![decl];
    let out = ur::core::especialize::especialize(file);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_specialize_datatype() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let dt = ur::core::DatatypeDecl {
        name: "T".into(),
        id: 0,
        params: vec![],
        constrs: vec![("A".into(), 1, None), ("B".into(), 2, Some(unit))],
    };
    let decl = Located::dummy(Declaration::Datatype(vec![dt]));
    let file: ur::core::File = vec![decl];
    let out = ur::core::specialize::specialize(file);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_reduce_con_record() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let k = Located::dummy(Kind::Type);
    let unit = Located::dummy(Constructor::Unit);
    let rec = Located::dummy(Constructor::Record(Box::new(k), vec![(unit.clone(), unit)]));
    let out = local_reduction::reduce_con(rec);
    assert!(matches!(out.node, Constructor::Record(_, _)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_reduce_con_named() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::Named(5));
    let out = local_reduction::reduce_con(c);
    assert!(matches!(out.node, Constructor::Named(5)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_reduce_exp_let() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let rel = Located::dummy(Expression::Rel(0));
    let let_expr = Located::dummy(Expression::Let(
        "x".into(),
        unit,
        Box::new(prim),
        Box::new(rel),
    ));
    let out = local_reduction::reduce_exp(let_expr);
    assert!(matches!(out.node, Expression::Let(_, _, _, _)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_named_false() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::Named(1));
    assert!(!unpoly::is_open(&c));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_ffi_false() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::Ffi("M".into(), "T".into()));
    assert!(!unpoly::is_open(&c));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_record_recurses() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let k = Located::dummy(Kind::Type);
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let rec = Located::dummy(Constructor::Record(Box::new(k), vec![(unit, rel1)]));
    assert!(unpoly::is_open(&rec));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_abs() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Abs binds one var; body Rel(2) with cutoff 1+1=2 becomes Rel(3)
    let unit = Located::dummy(Constructor::Unit);
    let rel2 = Located::dummy(Expression::Rel(2));
    let abs = Located::dummy(Expression::Abs(
        "x".into(),
        unit.clone(),
        unit,
        Box::new(rel2),
    ));
    let out = local_reduction::shift_exp(abs, 1, 1, 0, 0);
    match &out.node {
        Expression::Abs(_, _, _, body) => assert!(matches!(body.node, Expression::Rel(3))),
        _ => panic!("expected Abs"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_let() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Let binds one var; body Rel(2) with cutoff 1+1=2 becomes Rel(3)
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let rel2 = Located::dummy(Expression::Rel(2));
    let let_expr = Located::dummy(Expression::Let(
        "x".into(),
        unit,
        Box::new(prim),
        Box::new(rel2),
    ));
    let out = local_reduction::shift_exp(let_expr, 1, 1, 0, 0);
    match &out.node {
        Expression::Let(_, _, _, body) => assert!(matches!(body.node, Expression::Rel(3))),
        _ => panic!("expected Let"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_record() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel2 = Located::dummy(Expression::Rel(2));
    let name_f = Located::dummy(Constructor::Name("f".into()));
    let fields = vec![(name_f, rel2, unit)];
    let rec_exp = Located::dummy(Expression::Record(fields));
    let out = local_reduction::shift_exp(rec_exp, 1, 1, 0, 0);
    match &out.node {
        Expression::Record(fs) => {
            assert_eq!(fs.len(), 1);
            assert!(matches!(fs[0].1.node, Expression::Rel(3)));
        }
        _ => panic!("expected Record"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_unravel_capp_returns_none_for_non_capp() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let res = unpoly::unravel_capp(&prim);
    assert!(res.is_none());
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_export() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Export(
        ExportKind::Link(Effect::ReadOnly),
        0,
        false,
    ));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_core_rpcify_database() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Database("db".into()));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let mut errors = ur::error_types::ErrorReporter::new_silent();
    let result = compiler::core_rpcify(file, &settings, &mut errors);
    assert!(result.is_some());
    // extract the file from the Some; is_some() was asserted above
    let rpcified = match result {
        Some(v) => v,
        None => panic!("core_rpcify returned None for database file"),
    };
    assert_eq!(rpcified.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_marshal_check_database_ok() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Database("db".into()));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let mut errors = ur::error_types::ErrorReporter::new_silent();
    ur::core::marshal_check::check(&file, &settings, &mut errors);
    assert!(!errors.has_errors());
    Ok(()) // return success to the test harness
}

#[test]
fn integration_export_tagging_database() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Database("db".into()));
    let file: ur::core::File = vec![decl];
    let mut reported = Vec::new();
    let out = ur::core::export_tagging::tag(file, &mut |_s, payload| {
        reported.push(ur::diagnostics::render_diagnostic_body(
            &payload,
            ur::diagnostics::DiagnosticLocale::En,
        ));
    });
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_tcfun() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // TCFun binds one kind var; body Rel(2) with cutoff 1+1=2 becomes Rel(3)
    let k = Located::dummy(Kind::Type);
    let rel2 = Located::dummy(Constructor::Rel(2));
    let tcfun = Located::dummy(Constructor::TCFun("a".into(), Box::new(k), Box::new(rel2)));
    let out = local_reduction::shift_con(tcfun, 1, 1);
    match &out.node {
        Constructor::TCFun(_, _, body) => assert!(matches!(body.node, Constructor::Rel(3))),
        _ => panic!("expected TCFun"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_abs() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    // Abs (constructor-level) binds one; body Rel(2) with cutoff 1+1=2 becomes Rel(3)
    let k = Located::dummy(Kind::Type);
    let rel2 = Located::dummy(Constructor::Rel(2));
    let abs = Located::dummy(Constructor::Abs("a".into(), Box::new(k), Box::new(rel2)));
    let out = local_reduction::shift_con(abs, 1, 1);
    match &out.node {
        Constructor::Abs(_, _, body) => assert!(matches!(body.node, Constructor::Rel(3))),
        _ => panic!("expected Abs"),
    }
    Ok(()) // return success to the test harness
}

// ---------------------------------------------------------------------------
// Phase B: Core systematic variant coverage (local_reduction, global_reduction,
// file::max_name, unpoly, termination_check)
// ---------------------------------------------------------------------------

#[test]
fn integration_local_reduction_shift_con_kabs() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel2 = Located::dummy(Constructor::Rel(2));
    let kabs = Located::dummy(Constructor::KAbs("k".into(), Box::new(rel2)));
    let out = local_reduction::shift_con(kabs, 1, 1);
    match &out.node {
        Constructor::KAbs(_, body) => assert!(matches!(body.node, Constructor::Rel(3))),
        _ => panic!("expected KAbs"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_con_kapp() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel1 = Located::dummy(Constructor::Rel(1));
    let k = Located::dummy(Kind::Type);
    let kapp = Located::dummy(Constructor::KApp(Box::new(rel1), Box::new(k)));
    let out = local_reduction::shift_con(kapp, 1, 1);
    match &out.node {
        Constructor::KApp(c, _) => assert!(matches!(c.node, Constructor::Rel(2))),
        _ => panic!("expected KApp"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_capp() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel2 = Located::dummy(Expression::Rel(2));
    let unit = Located::dummy(Constructor::Unit);
    let capp = Located::dummy(Expression::CApp(Box::new(rel2), unit));
    let out = local_reduction::shift_exp(capp, 1, 1, 0, 0);
    match &out.node {
        Expression::CApp(e, _) => assert!(matches!(e.node, Expression::Rel(3))),
        _ => panic!("expected CApp"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_cabs() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let k = Located::dummy(Kind::Type);
    let rel2 = Located::dummy(Expression::Rel(2));
    let cabs = Located::dummy(Expression::CAbs("a".into(), Box::new(k), Box::new(rel2)));
    let out = local_reduction::shift_exp(cabs, 1, 1, 0, 0);
    match &out.node {
        Expression::CAbs(_, _, body) => assert!(matches!(body.node, Expression::Rel(3))),
        _ => panic!("expected CAbs"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_kabs() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel2 = Located::dummy(Expression::Rel(2));
    let kabs = Located::dummy(Expression::KAbs("k".into(), Box::new(rel2)));
    let out = local_reduction::shift_exp(kabs, 1, 1, 0, 0);
    match &out.node {
        Expression::KAbs(_, body) => assert!(matches!(body.node, Expression::Rel(3))),
        _ => panic!("expected KAbs"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_shift_exp_write() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let write = Located::dummy(Expression::Write(Box::new(prim)));
    let out = local_reduction::shift_exp(write, 0, 0, 0, 0);
    assert!(matches!(out.node, Expression::Write(_)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_reduce_con_tuple() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let tup = Located::dummy(Constructor::Tuple(vec![unit.clone(), unit]));
    let out = local_reduction::reduce_con(tup);
    assert!(matches!(out.node, Constructor::Tuple(_)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_local_reduction_reduce_con_concat() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let concat = Located::dummy(Constructor::Concat(Box::new(unit.clone()), Box::new(unit)));
    let out = local_reduction::reduce_con(concat);
    assert!(matches!(out.node, Constructor::Concat(_, _)));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_cookie() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Cookie("c".into(), 0, unit, "".into()));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_style() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Style("s".into(), 0, "".into()));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_onerror() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::OnError(0));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_file_max_name_table() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::Table {
        sql_name: "t".into(),
        id: 99,
        con: unit.clone(),
        sql_con: "".into(),
        exp: prim.clone(),
        pk_con: unit.clone(),
        pk_exp: prim.clone(),
        unique_con: unit,
    });
    assert_eq!(file::max_name(&[decl]), 99);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_file_max_name_cookie() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let decl = Located::dummy(Declaration::Cookie("c".into(), 42, unit, "".into()));
    assert_eq!(file::max_name(&[decl]), 42);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_file_max_name_style() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let decl = Located::dummy(Declaration::Style("s".into(), 7, "".into()));
    assert_eq!(file::max_name(&[decl]), 7);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_sub_con_in_con_record() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let k = Located::dummy(Kind::Type);
    let rel0 = Located::dummy(Constructor::Rel(0));
    let rec_c = Located::dummy(Constructor::Record(Box::new(k), vec![(rel0, unit.clone())]));
    let out = unpoly::sub_con_in_con(0, &unit, rec_c);
    match &out.node {
        Constructor::Record(_, pairs) => {
            assert_eq!(pairs.len(), 1);
            assert!(matches!(pairs[0].0.node, Constructor::Unit));
        }
        _ => panic!("expected Record"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_sub_con_in_con_concat() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel0 = Located::dummy(Constructor::Rel(0));
    let concat = Located::dummy(Constructor::Concat(Box::new(rel0), Box::new(unit.clone())));
    let out = unpoly::sub_con_in_con(0, &unit, concat);
    match &out.node {
        Constructor::Concat(a, b) => {
            assert!(matches!(a.node, Constructor::Unit));
            assert!(matches!(b.node, Constructor::Unit));
        }
        _ => panic!("expected Concat"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_sub_con_in_con_tuple() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel0 = Located::dummy(Constructor::Rel(0));
    let tup = Located::dummy(Constructor::Tuple(vec![rel0, unit.clone()]));
    let out = unpoly::sub_con_in_con(0, &unit, tup);
    match &out.node {
        Constructor::Tuple(cs) => {
            assert_eq!(cs.len(), 2);
            assert!(matches!(cs[0].node, Constructor::Unit));
            assert!(matches!(cs[1].node, Constructor::Unit));
        }
        _ => panic!("expected Tuple"),
    }
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_concat() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let concat = Located::dummy(Constructor::Concat(Box::new(unit), Box::new(rel1)));
    assert!(unpoly::is_open(&concat));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_tuple() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let rel1 = Located::dummy(Constructor::Rel(1));
    let tup = Located::dummy(Constructor::Tuple(vec![unit, rel1]));
    assert!(unpoly::is_open(&tup));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_unpoly_is_open_proj() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let rel1 = Located::dummy(Constructor::Rel(1));
    let tup = Located::dummy(Constructor::Tuple(vec![rel1]));
    let proj = Located::dummy(Constructor::Proj(Box::new(tup), 1));
    assert!(unpoly::is_open(&proj));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_unit() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let c = Located::dummy(Constructor::Unit);
    let pred = |cc: &LocatedConstructor| matches!(&cc.node, Constructor::Unit);
    assert!(constructor::exists(&c, &|_| false, &pred));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_constructor_exists_concat() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let concat = Located::dummy(Constructor::Concat(Box::new(unit.clone()), Box::new(unit)));
    let pred = |cc: &LocatedConstructor| matches!(&cc.node, Constructor::Unit);
    assert!(constructor::exists(&concat, &|_| false, &pred));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_prim() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let pred = |ee: &LocatedExpression| matches!(&ee.node, Expression::Prim(_));
    assert!(expression::exists(&e, &|_| false, &|_| false, &pred));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_expression_exists_app() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let app = Located::dummy(Expression::App(Box::new(prim.clone()), Box::new(prim)));
    let pred = |ee: &LocatedExpression| matches!(&ee.node, Expression::App(_, _));
    assert!(expression::exists(&app, &|_| false, &|_| false, &pred));
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_table() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::Table {
        sql_name: "t".into(),
        id: 0,
        con: unit.clone(),
        sql_con: "".into(),
        exp: prim.clone(),
        pk_con: unit.clone(),
        pk_exp: prim.clone(),
        unique_con: unit,
    });
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_view() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let exp = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::View("v".into(), 0, "".into(), exp, unit));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_index() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e1 = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e2 = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::Index(e1, e2));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_task() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e1 = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e2 = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::Task(e1, e2));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_global_reduction_reduce_policy() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::Policy(e));
    let file: ur::core::File = vec![decl];
    let settings = ur::settings::Settings::new();
    let out = global_reduction::reduce(file, &settings);
    assert_eq!(out.len(), 1);
    Ok(()) // return success to the test harness
}

#[test]
fn integration_termination_check_valrec_non_recursive() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let body = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::ValRec(vec![(
        "f".into(),
        0,
        unit.clone(),
        body,
        "".into(),
    )]));
    let file: ur::core::File = vec![decl];
    let _settings = ur::settings::Settings::new();
    let mut errors = ur::error_types::ErrorReporter::new_silent();
    ur::core::termination_check::check(&file, &mut errors);
    assert!(!errors.has_errors());
    Ok(()) // return success to the test harness
}

#[test]
fn integration_declaration_exists_val() -> anyhow::Result<()> {
    // test returns Result to allow ? propagation
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Declaration::Val("x".into(), 0, unit, prim, "".into()));
    let pred_d =
        |d: &ur::core::LocatedDeclaration| matches!(&d.node, Declaration::Val(_, _, _, _, _));
    assert!(declaration::exists(
        &decl,
        &|_| false,
        &|_| false,
        &|_| false,
        &pred_d
    ));
    Ok(()) // return success to the test harness
}
