//! Integration tests for the Explicit module.

use ur::compiler;
use ur::datatype_kind::DatatypeKind;
use ur::error_types::Located;
use ur::explicit::utilities::{classify_datatype, con, decl, exp, kind};
use ur::explicit::{CaseMeta, Constructor, Declaration, Expression, FieldMeta, Kind, RestMeta};

#[test]
fn explicit_classify_datatype_enum() {
    let constrs: Vec<(String, usize, Option<ur::explicit::LocatedConstructor>)> =
        vec![("A".into(), 0, None), ("B".into(), 1, None)];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Enum);
}

#[test]
fn explicit_classify_datatype_enum_single_nullary() {
    let constrs: Vec<(String, usize, Option<ur::explicit::LocatedConstructor>)> =
        vec![("Unit".into(), 0, None)];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Enum);
}

#[test]
fn explicit_classify_datatype_option() {
    let unit = Located::dummy(Constructor::Unit);
    let constrs: Vec<(String, usize, Option<ur::explicit::LocatedConstructor>)> =
        vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Option);
}

#[test]
fn explicit_classify_datatype_default() {
    let unit = Located::dummy(Constructor::Unit);
    let constrs: Vec<(String, usize, Option<ur::explicit::LocatedConstructor>)> = vec![
        ("A".into(), 0, Some(unit.clone())),
        ("B".into(), 1, Some(unit)),
    ];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Default);
}

#[test]
fn explicit_classify_datatype_default_two_nullary_one_unary() {
    // (2 nullary, 1 unary) must be Default, not Option. Catches && vs || mutant.
    let unit = Located::dummy(Constructor::Unit);
    let constrs: Vec<(String, usize, Option<ur::explicit::LocatedConstructor>)> = vec![
        ("A".into(), 0, None),
        ("B".into(), 0, None),
        ("C".into(), 1, Some(unit)),
    ];
    assert_eq!(classify_datatype(&constrs), DatatypeKind::Default);
}

#[test]
fn explicit_kind_exists() {
    let k = Located::dummy(Kind::Arrow(
        Box::new(Located::dummy(Kind::Rel(1))),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(kind::exists(&k, &|kr| matches!(kr, Kind::Rel(1))));
    assert!(!kind::exists(&k, &|kr| matches!(kr, Kind::Rel(99))));
}

#[test]
fn explicit_kind_exists_in_tuple() {
    let k = Located::dummy(Kind::Tuple(vec![Located::dummy(Kind::Rel(42))]));
    assert!(kind::exists(&k, &|kr| matches!(kr, Kind::Rel(42))));
}

#[test]
fn explicit_kind_exists_in_record() {
    let k = Located::dummy(Kind::Record(Box::new(Located::dummy(Kind::Rel(7)))));
    assert!(kind::exists(&k, &|kr| matches!(kr, Kind::Rel(7))));
}

#[test]
fn explicit_kind_exists_in_fun() {
    let k = Located::dummy(Kind::Fun(
        "x".into(),
        Box::new(Located::dummy(Kind::Rel(99))),
    ));
    assert!(kind::exists(&k, &|kr| matches!(kr, Kind::Rel(99))));
}

#[test]
fn explicit_kind_fold_visits_arrow() {
    let k = Located::dummy(Kind::Arrow(
        Box::new(Located::dummy(Kind::Type)),
        Box::new(Located::dummy(Kind::Unit)),
    ));
    let count = kind::fold(&k, 0usize, &|_, n| n + 1);
    assert!(count >= 3, "fold must visit Arrow and sub-kinds");
}

#[test]
fn explicit_kind_fold_visits_tuple() {
    let k = Located::dummy(Kind::Tuple(vec![Located::dummy(Kind::Rel(1))]));
    let count = kind::fold(&k, 0usize, &|_, n| n + 1);
    assert_eq!(count, 2, "fold must visit Tuple and Rel(1)");
}

#[test]
fn explicit_kind_fold_visits_record() {
    let k = Located::dummy(Kind::Record(Box::new(Located::dummy(Kind::Rel(2)))));
    let count = kind::fold(&k, 0usize, &|_, n| n + 1);
    assert_eq!(count, 2, "fold must visit Record and Rel(2)");
}

#[test]
fn explicit_kind_fold_visits_fun() {
    let k = Located::dummy(Kind::Fun(
        "x".into(),
        Box::new(Located::dummy(Kind::Rel(3))),
    ));
    let count = kind::fold(&k, 0usize, &|_, n| n + 1);
    assert_eq!(count, 2, "fold must visit Fun and Rel(3)");
}

#[test]
fn explicit_con_exists() {
    let c = Located::dummy(Constructor::Unit);
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_app_first_only() {
    // App(Unit, Rel(0)): fc matches Unit (in c1), not Rel (in c2). Short-circuit || must yield true.
    let c = Located::dummy(Constructor::App(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Rel(0))),
    ));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_tfun_first_only() {
    // TFun(Unit, Rel(0)): fc matches Unit in c1, not Rel in c2.
    let c = Located::dummy(Constructor::TFun(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Rel(0))),
    ));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_record_kind_only() {
    // Record(kind with Rel(1), [(Unit,Unit)]): fk matches Rel(1) in kind; fc never matches Unit.
    let k = Located::dummy(Kind::Record(Box::new(Located::dummy(Kind::Rel(1)))));
    let unit = Located::dummy(Constructor::Unit);
    let c = Located::dummy(Constructor::Record(Box::new(k), vec![(unit.clone(), unit)]));
    assert!(con::exists(&c, &|kr| matches!(kr, Kind::Rel(1)), &|_| {
        false
    }));
}

#[test]
fn explicit_con_exists_record_xcs_only() {
    // Record(kind Type, [(Rel(0), Unit)]): kind doesn't match; fc matches Unit in value.
    let k = Located::dummy(Kind::Type);
    let c = Located::dummy(Constructor::Record(
        Box::new(k),
        vec![(
            Located::dummy(Constructor::Rel(0)),
            Located::dummy(Constructor::Unit),
        )],
    ));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_returns_false_when_nothing_matches() {
    let c = Located::dummy(Constructor::Unit);
    assert!(!con::exists(&c, &|_| false, &|_| false));
}

#[test]
fn explicit_con_exists_concat_first_only() {
    let c = Located::dummy(Constructor::Concat(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Constructor::Rel(0))),
    ));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_concat_second_only() {
    let c = Located::dummy(Constructor::Concat(
        Box::new(Located::dummy(Constructor::Rel(0))),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_tuple_any() {
    let c = Located::dummy(Constructor::Tuple(vec![
        Located::dummy(Constructor::Rel(0)),
        Located::dummy(Constructor::Unit),
        Located::dummy(Constructor::Rel(1)),
    ]));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_map_first_kind_only() {
    let c = Located::dummy(Constructor::Map(
        Box::new(Located::dummy(Kind::Rel(7))),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(con::exists(&c, &|kr| matches!(kr, Kind::Rel(7)), &|_| {
        false
    }));
}

#[test]
fn explicit_con_exists_tcfun_body_only() {
    // TCFun: kind has Type, body has Unit. fc matches Unit in body.
    let body = Located::dummy(Constructor::Unit);
    let k = Located::dummy(Kind::Type);
    let c = Located::dummy(Constructor::TCFun("x".into(), Box::new(k), Box::new(body)));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_abs_body_only() {
    // Abs: kind Type, body Unit. fc matches body.
    let body = Located::dummy(Constructor::Unit);
    let k = Located::dummy(Kind::Type);
    let c = Located::dummy(Constructor::Abs("x".into(), Box::new(k), Box::new(body)));
    assert!(con::exists(&c, &|_| false, &|cc| matches!(
        cc,
        Constructor::Unit
    )));
}

#[test]
fn explicit_con_exists_kapp_kind_only() {
    // KApp(Unit, Rel(7)): fc doesn't match c, fk matches k.
    let c = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(Located::dummy(Kind::Rel(7))),
    ));
    assert!(con::exists(&c, &|kr| matches!(kr, Kind::Rel(7)), &|_| {
        false
    }));
}

#[test]
fn explicit_con_exists_map_second_kind_only() {
    // Map(Type, Rel(8)): k1 doesn't match, k2 matches.
    let c = Located::dummy(Constructor::Map(
        Box::new(Located::dummy(Kind::Type)),
        Box::new(Located::dummy(Kind::Rel(8))),
    ));
    assert!(con::exists(&c, &|kr| matches!(kr, Kind::Rel(8)), &|_| {
        false
    }));
}

#[test]
fn explicit_exp_exists_returns_false_when_nothing_matches() {
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    assert!(!exp::exists(&e, &|_| false, &|_| false, &|_| false));
}

#[test]
fn explicit_exp_exists_returns_true_when_fe_matches() {
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(42)));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_app_first_only() {
    let e = Located::dummy(Expression::App(
        Box::new(Located::dummy(Expression::Prim(ur::primitives::Prim::Int(
            1,
        )))),
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_decl_map_preserves_datatype_constrs() {
    let unit = Located::dummy(Constructor::Unit);
    let dt = ur::explicit::DatatypeDecl {
        name: "T".into(),
        id: 0,
        params: vec![],
        constrs: vec![("A".into(), 0, None), ("B".into(), 1, Some(unit))],
    };
    let d = Located::dummy(Declaration::Datatype(vec![dt]));
    let d2 = decl::map(d, &|k| k, &|c| c, &|e| e, &|x| x);
    let Declaration::Datatype(dts) = &d2.node else {
        panic!("expected Datatype")
    };
    assert_eq!(dts.len(), 1);
    assert_eq!(
        dts[0].constrs.len(),
        2,
        "map_constrs must preserve constr count"
    );
}

#[test]
fn explicit_exp_exists_capp_exp_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::CApp(
        Box::new(Located::dummy(Expression::Prim(ur::primitives::Prim::Int(
            0,
        )))),
        unit,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_app_second_only() {
    let e = Located::dummy(Expression::App(
        Box::new(Located::dummy(Expression::Rel(0))),
        Box::new(Located::dummy(Expression::Prim(ur::primitives::Prim::Int(
            1,
        )))),
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_capp_con_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::CApp(
        Box::new(Located::dummy(Expression::Rel(0))),
        unit,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_abs_body_only() {
    let unit = Located::dummy(Constructor::Unit);
    let body = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(Expression::Abs(
        "x".into(),
        unit.clone(),
        unit.clone(),
        Box::new(body),
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_cabs_body_only() {
    let body = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let k = Located::dummy(Kind::Type);
    let e = Located::dummy(Expression::CAbs("x".into(), Box::new(k), Box::new(body)));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_kapp_kind_only() {
    let k = Located::dummy(Kind::Rel(9));
    let e = Located::dummy(Expression::KApp(
        Box::new(Located::dummy(Expression::Rel(0))),
        Box::new(k),
    ));
    assert!(exp::exists(
        &e,
        &|kr| matches!(kr, Kind::Rel(9)),
        &|_| false,
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_kapp_exp_only() {
    let e = Located::dummy(Expression::KApp(
        Box::new(Located::dummy(Expression::Prim(ur::primitives::Prim::Int(
            0,
        )))),
        Box::new(Located::dummy(Kind::Type)),
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_kabs_body_only() {
    let body = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(Expression::KAbs("x".into(), Box::new(body)));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_record_x_only() {
    // Record(x,e,t): only x (first con) matches - ec(x)
    let unit = Located::dummy(Constructor::Unit);
    let other = Located::dummy(Constructor::Named(99));
    let e = Located::dummy(Expression::Record(vec![(
        unit,
        Located::dummy(Expression::Rel(0)),
        other,
    )]));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_record_t_only() {
    // Record(x,e,t): only t (third con) matches - ec(t)
    let unit = Located::dummy(Constructor::Unit);
    let other = Located::dummy(Constructor::Named(99));
    let e = Located::dummy(Expression::Record(vec![(
        other,
        Located::dummy(Expression::Rel(0)),
        unit,
    )]));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_abs_dom_only() {
    let unit = Located::dummy(Constructor::Unit);
    let other = Located::dummy(Constructor::Named(1));
    let e = Located::dummy(Expression::Abs(
        "x".into(),
        unit,
        other,
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_abs_ran_only() {
    let unit = Located::dummy(Constructor::Unit);
    let other = Located::dummy(Constructor::Named(1));
    let e = Located::dummy(Expression::Abs(
        "x".into(),
        other,
        unit,
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_cabs_kind_only() {
    let k = Located::dummy(Kind::Rel(7));
    let e = Located::dummy(Expression::CAbs(
        "x".into(),
        Box::new(k),
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    assert!(exp::exists(
        &e,
        &|kr| matches!(kr, Kind::Rel(7)),
        &|_| false,
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_let_t_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Let(
        "x".into(),
        unit,
        Box::new(Located::dummy(Expression::Rel(0))),
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_let_e1_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(Expression::Let(
        "x".into(),
        unit,
        Box::new(prim),
        Box::new(Located::dummy(Expression::Rel(0))),
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_record_middle_only() {
    // (x, e, t): only e matches
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(Expression::Record(vec![(unit.clone(), prim, unit)]));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_concat_e2_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(Expression::Concat(
        Box::new(Located::dummy(Expression::Rel(0))),
        unit.clone(),
        Box::new(prim),
        unit,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_let_e2_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(Expression::Let(
        "x".into(),
        unit,
        Box::new(Located::dummy(Expression::Rel(0))),
        Box::new(prim),
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

// Case: ee(disc) || arms.iter().any(...) || ec(dt) || ec(result) — each || must short-circuit correctly
#[test]
fn explicit_exp_exists_case_disc_only() {
    let unit = Located::dummy(Constructor::Unit);
    let disc = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let arm_exp = Located::dummy(Expression::Rel(0));
    let meta = CaseMeta {
        disc: unit.clone(),
        result: unit,
    };
    let e = Located::dummy(Expression::Case(
        Box::new(disc),
        vec![(
            Located::dummy(ur::explicit::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Unit),
            )),
            arm_exp,
        )],
        meta,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_case_arm_only() {
    let unit = Located::dummy(Constructor::Unit);
    let disc = Located::dummy(Expression::Rel(0));
    let arm_exp = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let meta = CaseMeta {
        disc: unit.clone(),
        result: unit,
    };
    let e = Located::dummy(Expression::Case(
        Box::new(disc),
        vec![(
            Located::dummy(ur::explicit::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Unit),
            )),
            arm_exp,
        )],
        meta,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_case_dt_only() {
    let unit = Located::dummy(Constructor::Unit);
    let disc = Located::dummy(Expression::Rel(0));
    let arm_exp = Located::dummy(Expression::Rel(0));
    let meta = CaseMeta {
        disc: unit.clone(),                             // dt in CaseMeta — ec matches Unit
        result: Located::dummy(Constructor::Named(99)), // no match
    };
    let e = Located::dummy(Expression::Case(
        Box::new(disc),
        vec![(
            Located::dummy(ur::explicit::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Named(1)),
            )),
            arm_exp,
        )],
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_case_result_only() {
    let unit = Located::dummy(Constructor::Unit);
    let disc = Located::dummy(Expression::Rel(0));
    let arm_exp = Located::dummy(Expression::Rel(0));
    let meta = CaseMeta {
        disc: Located::dummy(Constructor::Named(1)),
        result: unit, // result matches Unit
    };
    let e = Located::dummy(Expression::Case(
        Box::new(disc),
        vec![(
            Located::dummy(ur::explicit::Pattern::Var(
                "_".into(),
                Located::dummy(Constructor::Named(1)),
            )),
            arm_exp,
        )],
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_field_rest_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: unit,
    };
    let e = Located::dummy(Expression::Field(
        Box::new(Located::dummy(Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_field_field_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: unit,
        rest: Located::dummy(Constructor::Named(1)),
    };
    let e = Located::dummy(Expression::Field(
        Box::new(Located::dummy(Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_field_e_only() {
    let _unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(Expression::Field(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_field_c_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(Expression::Field(
        Box::new(Located::dummy(Expression::Rel(0))),
        unit,
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_concat_e1_only() {
    let unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let e = Located::dummy(Expression::Concat(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        Box::new(Located::dummy(Expression::Rel(0))),
        unit,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_concat_c1_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Concat(
        Box::new(Located::dummy(Expression::Rel(0))),
        unit,
        Box::new(Located::dummy(Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_concat_c2_only() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Concat(
        Box::new(Located::dummy(Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        Box::new(Located::dummy(Expression::Rel(0))),
        unit,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_cut_e_only() {
    let _unit = Located::dummy(Constructor::Unit);
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(Expression::Cut(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_cut_c_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(Expression::Cut(
        Box::new(Located::dummy(Expression::Rel(0))),
        unit,
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_cut_field_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: unit,
        rest: Located::dummy(Constructor::Named(2)),
    };
    let e = Located::dummy(Expression::Cut(
        Box::new(Located::dummy(Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_cut_rest_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = FieldMeta {
        field: Located::dummy(Constructor::Named(1)),
        rest: unit,
    };
    let e = Located::dummy(Expression::Cut(
        Box::new(Located::dummy(Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_cutmulti_e_only() {
    let prim = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let meta = RestMeta {
        rest: Located::dummy(Constructor::Named(1)),
    };
    let e = Located::dummy(Expression::CutMulti(
        Box::new(prim),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(&e, &|_| false, &|_| false, &|ex| matches!(
        ex,
        Expression::Prim(_)
    )));
}

#[test]
fn explicit_exp_exists_cutmulti_c_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = RestMeta {
        rest: Located::dummy(Constructor::Named(1)),
    };
    let e = Located::dummy(Expression::CutMulti(
        Box::new(Located::dummy(Expression::Rel(0))),
        unit,
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

#[test]
fn explicit_exp_exists_cutmulti_rest_only() {
    let unit = Located::dummy(Constructor::Unit);
    let meta = RestMeta { rest: unit };
    let e = Located::dummy(Expression::CutMulti(
        Box::new(Located::dummy(Expression::Rel(0))),
        Located::dummy(Constructor::Named(1)),
        meta,
    ));
    assert!(exp::exists(
        &e,
        &|_| false,
        &|cc| matches!(cc, Constructor::Unit),
        &|_| false
    ));
}

// decl::fold_node — each Decl arm must be visited (deleting arm falls through to _ => init)
#[test]
fn explicit_decl_fold_con_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let k = Located::dummy(Kind::Type);
    let d = Located::dummy(Declaration::Constructor("T".into(), 0, k, unit));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(
        n >= 2,
        "fold must visit Con's kind and con (catches delete arm mutant)"
    );
}

#[test]
fn explicit_decl_fold_datatypeimp_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let d = Located::dummy(Declaration::DatatypeImp {
        name: "T".into(),
        id: 0,
        orig_mod: 0,
        orig_path: vec![],
        orig_name: "T".into(),
        orig_constrs_path: vec![],
        constrs: vec![("A".into(), 0, Some(unit))],
    });
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 1, "fold must visit DatatypeImp constrs");
}

#[test]
fn explicit_decl_fold_valrec_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::ValRec(vec![("x".into(), 0, unit, e)]));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 2, "fold must visit ValRec's type and exp");
}

#[test]
fn explicit_decl_fold_datatype_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let dt = ur::explicit::DatatypeDecl {
        name: "T".into(),
        id: 0,
        params: vec![],
        constrs: vec![("A".into(), 0, Some(unit))],
    };
    let d = Located::dummy(Declaration::Datatype(vec![dt]));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 1, "fold must visit Datatype constrs");
}

#[test]
fn explicit_decl_fold_val_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::Val("x".into(), 0, unit, e));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 2, "fold must visit Val's type and exp");
}

#[test]
fn explicit_decl_fold_table_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Rel(0));
    let d = Located::dummy(Declaration::Table {
        mod_id: 0,
        name: "T".into(),
        name_id: 0,
        con: unit.clone(),
        exp: e.clone(),
        pk_con: unit.clone(),
        pk_exp: e,
        unique_con: unit,
    });
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 2, "fold must visit Table's con/exp");
}

#[test]
fn explicit_decl_fold_view_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Rel(0));
    let d = Located::dummy(Declaration::View(0, "V".into(), 0, e, unit));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 2, "fold must visit View's exp and con");
}

#[test]
fn explicit_decl_fold_index_visits() {
    let e1 = Located::dummy(Expression::Rel(0));
    let e2 = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::Index(e1, e2));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 1, "fold must visit Index exp");
}

#[test]
fn explicit_decl_fold_cookie_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let d = Located::dummy(Declaration::Cookie(0, "c".into(), 0, unit));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 1, "fold must visit Cookie con");
}

#[test]
fn explicit_decl_fold_task_visits() {
    let e1 = Located::dummy(Expression::Rel(0));
    let e2 = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::Task(e1, e2));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 1, "fold must visit Task exp");
}

#[test]
fn explicit_decl_fold_policy_visits() {
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::Policy(e));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 1, "fold must visit Policy exp");
}

#[test]
fn explicit_decl_fold_ffi_visits() {
    let unit = Located::dummy(Constructor::Unit);
    let d = Located::dummy(Declaration::Ffi("f".into(), 0, vec![], unit));
    let n = decl::fold(
        &d,
        0usize,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s + 1,
        &|_, s| s,
    );
    assert!(n >= 1, "fold must visit Ffi type");
}

#[test]
fn explicit_corify_minimal_file_returns_non_empty_core() {
    // Kills: corify mutants that return None or empty core for valid explicit input.
    let file: ur::explicit::File = vec![Located::dummy(Declaration::Database("db".into()))];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(
        result.is_some(),
        "corify must return Some for minimal explicit file (catches replace with None)"
    );
    let core_file = result.unwrap();
    assert!(
        !core_file.is_empty(),
        "corify must produce at least one Core decl (catches replace with Default::default())"
    );
    assert!(
        core_file
            .iter()
            .any(|d| matches!(&d.node, ur::core::Declaration::Database(_))),
        "corify must produce Database decl"
    );
}

// ---------------------------------------------------------------------------
// Phase 3: corify variants, explicit environment (lift_kind_in_kind, lift_con_in_con)
// ---------------------------------------------------------------------------

use ur::explicit::environment;

#[test]
fn explicit_corify_val_produces_core_val() {
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let prim = Located::dummy(ur::explicit::Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(ur::explicit::Declaration::Val("x".into(), 0, unit, prim));
    let file: ur::explicit::File = vec![decl];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(
        core_file
            .iter()
            .any(|d| matches!(&d.node, ur::core::Declaration::Val(_, _, _, _, _))),
        "corify must produce Val decl"
    );
}

#[test]
fn explicit_corify_datatype_produces_core_datatype() {
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let dt = ur::explicit::DatatypeDecl {
        name: "T".into(),
        id: 0,
        params: vec![],
        constrs: vec![("A".into(), 1, None), ("B".into(), 2, Some(unit))],
    };
    let decl = Located::dummy(ur::explicit::Declaration::Datatype(vec![dt]));
    let file: ur::explicit::File = vec![decl];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(
        core_file
            .iter()
            .any(|d| matches!(&d.node, ur::core::Declaration::Datatype(_))),
        "corify must produce Datatype decl"
    );
}

#[test]
fn explicit_lift_kind_in_kind_rel_at_bound() {
    let k = Located::dummy(ur::explicit::Kind::Rel(0));
    let out = environment::lift_kind_in_kind(k, 0);
    assert!(matches!(out.node, ur::explicit::Kind::Rel(1)));
}

#[test]
fn explicit_lift_kind_in_kind_rel_below_bound() {
    let k = Located::dummy(ur::explicit::Kind::Rel(0));
    let out = environment::lift_kind_in_kind(k, 1);
    assert!(matches!(out.node, ur::explicit::Kind::Rel(0)));
}

#[test]
fn explicit_lift_con_in_con_rel_at_bound() {
    let c = Located::dummy(ur::explicit::Constructor::Rel(0));
    let out = environment::lift_con_in_con(c, 0);
    assert!(matches!(out.node, ur::explicit::Constructor::Rel(1)));
}

#[test]
fn explicit_lift_con_in_con_unit_unchanged() {
    let c = Located::dummy(ur::explicit::Constructor::Unit);
    let out = environment::lift_con_in_con(c, 0);
    assert!(matches!(out.node, ur::explicit::Constructor::Unit));
}

// ---------------------------------------------------------------------------
// Phase 3 expanded: corify (Sequence, Cookie, Style, Ffi, Constructor), lift_con variants
// ---------------------------------------------------------------------------

#[test]
fn explicit_corify_sequence_produces_core_sequence() {
    let decl = Located::dummy(ur::explicit::Declaration::Sequence(0, "s".into(), 1));
    let file: ur::explicit::File = vec![decl];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(core_file
        .iter()
        .any(|d| matches!(&d.node, ur::core::Declaration::Sequence(_, _, _))));
}

#[test]
fn explicit_corify_cookie_produces_core_cookie() {
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let decl = Located::dummy(ur::explicit::Declaration::Cookie(0, "c".into(), 1, unit));
    let file: ur::explicit::File = vec![decl];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(core_file
        .iter()
        .any(|d| matches!(&d.node, ur::core::Declaration::Cookie(_, _, _, _))));
}

#[test]
fn explicit_corify_style_produces_core_style() {
    let decl = Located::dummy(ur::explicit::Declaration::Style(0, "s".into(), 1));
    let file: ur::explicit::File = vec![decl];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(core_file
        .iter()
        .any(|d| matches!(&d.node, ur::core::Declaration::Style(_, _, _))));
}

#[test]
fn explicit_corify_constructor_produces_core_constructor() {
    let k = Located::dummy(ur::explicit::Kind::Type);
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let decl = Located::dummy(ur::explicit::Declaration::Constructor(
        "C".into(),
        0,
        k,
        unit,
    ));
    let file: ur::explicit::File = vec![decl];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(core_file
        .iter()
        .any(|d| matches!(&d.node, ur::core::Declaration::Constructor(_, _, _, _))));
}

#[test]
fn explicit_lift_con_in_con_record() {
    let k = Located::dummy(ur::explicit::Kind::Type);
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let rel0 = Located::dummy(ur::explicit::Constructor::Rel(0));
    let rec = Located::dummy(ur::explicit::Constructor::Record(
        Box::new(k),
        vec![(rel0, unit)],
    ));
    let out = environment::lift_con_in_con(rec, 0);
    match &out.node {
        ur::explicit::Constructor::Record(_, pairs) => {
            assert_eq!(pairs.len(), 1);
            assert!(matches!(pairs[0].0.node, ur::explicit::Constructor::Rel(1)));
        }
        _ => panic!("expected Record"),
    }
}

#[test]
fn explicit_lift_con_in_con_concat() {
    let rel0 = Located::dummy(ur::explicit::Constructor::Rel(0));
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let concat = Located::dummy(ur::explicit::Constructor::Concat(
        Box::new(rel0),
        Box::new(unit),
    ));
    let out = environment::lift_con_in_con(concat, 0);
    match &out.node {
        ur::explicit::Constructor::Concat(a, b) => {
            assert!(matches!(a.node, ur::explicit::Constructor::Rel(1)));
            assert!(matches!(b.node, ur::explicit::Constructor::Unit));
        }
        _ => panic!("expected Concat"),
    }
}

#[test]
fn explicit_lift_con_in_con_tuple() {
    let rel0 = Located::dummy(ur::explicit::Constructor::Rel(0));
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let tup = Located::dummy(ur::explicit::Constructor::Tuple(vec![rel0, unit]));
    let out = environment::lift_con_in_con(tup, 0);
    match &out.node {
        ur::explicit::Constructor::Tuple(cs) => {
            assert_eq!(cs.len(), 2);
            assert!(matches!(cs[0].node, ur::explicit::Constructor::Rel(1)));
            assert!(matches!(cs[1].node, ur::explicit::Constructor::Unit));
        }
        _ => panic!("expected Tuple"),
    }
}

#[test]
fn explicit_lift_con_in_con_tfun() {
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let rel1 = Located::dummy(ur::explicit::Constructor::Rel(1));
    let tfun = Located::dummy(ur::explicit::Constructor::TFun(
        Box::new(unit),
        Box::new(rel1),
    ));
    let out = environment::lift_con_in_con(tfun, 1);
    match &out.node {
        ur::explicit::Constructor::TFun(_, b) => {
            assert!(matches!(b.node, ur::explicit::Constructor::Rel(2)))
        }
        _ => panic!("expected TFun"),
    }
}

// Phase D: corify Export/Task/Policy/Index, lift_con_in_con KAbs/KApp/Proj/TRecord, lift_kind_in_con
#[test]
fn explicit_corify_index_produces_core_index() {
    let prim = Located::dummy(ur::explicit::Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl_db = Located::dummy(ur::explicit::Declaration::Database("db".into()));
    let decl_idx = Located::dummy(ur::explicit::Declaration::Index(prim.clone(), prim));
    let file: ur::explicit::File = vec![decl_db, decl_idx];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(core_file
        .iter()
        .any(|d| matches!(&d.node, ur::core::Declaration::Index(_, _))));
}

#[test]
fn explicit_corify_task_produces_core_task() {
    let prim = Located::dummy(ur::explicit::Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl_db = Located::dummy(ur::explicit::Declaration::Database("db".into()));
    let decl_task = Located::dummy(ur::explicit::Declaration::Task(prim.clone(), prim));
    let file: ur::explicit::File = vec![decl_db, decl_task];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(core_file
        .iter()
        .any(|d| matches!(&d.node, ur::core::Declaration::Task(_, _))));
}

#[test]
fn explicit_corify_policy_produces_core_policy() {
    let prim = Located::dummy(ur::explicit::Expression::Prim(ur::primitives::Prim::Int(0)));
    let decl_db = Located::dummy(ur::explicit::Declaration::Database("db".into()));
    let decl_policy = Located::dummy(ur::explicit::Declaration::Policy(prim));
    let file: ur::explicit::File = vec![decl_db, decl_policy];
    let mut settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let result = compiler::corify(file, &mut settings, &mut errors);
    assert!(result.is_some());
    let core_file = result.unwrap();
    assert!(core_file
        .iter()
        .any(|d| matches!(&d.node, ur::core::Declaration::Policy(_))));
}

#[test]
fn explicit_lift_con_in_con_kabs() {
    let rel0 = Located::dummy(ur::explicit::Constructor::Rel(0));
    let kabs = Located::dummy(ur::explicit::Constructor::KAbs("a".into(), Box::new(rel0)));
    let out = environment::lift_con_in_con(kabs, 0);
    match &out.node {
        ur::explicit::Constructor::KAbs(_, b) => {
            assert!(
                matches!(b.node, ur::explicit::Constructor::Rel(1)),
                "KAbs does not bind con, so Rel(0) lifts to Rel(1)"
            );
        }
        _ => panic!("expected KAbs"),
    }
}

#[test]
fn explicit_lift_con_in_con_kapp() {
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let k = Located::dummy(ur::explicit::Kind::Type);
    let kapp = Located::dummy(ur::explicit::Constructor::KApp(
        Box::new(unit),
        Box::new(k.clone()),
    ));
    let out = environment::lift_con_in_con(kapp, 0);
    assert!(matches!(out.node, ur::explicit::Constructor::KApp(_, _)));
}

#[test]
fn explicit_lift_con_in_con_proj() {
    let rel0 = Located::dummy(ur::explicit::Constructor::Rel(0));
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let tup = Located::dummy(ur::explicit::Constructor::Tuple(vec![rel0, unit]));
    let proj = Located::dummy(ur::explicit::Constructor::Proj(Box::new(tup), 1));
    let out = environment::lift_con_in_con(proj, 0);
    match &out.node {
        ur::explicit::Constructor::Proj(c, 1) => {
            if let ur::explicit::Constructor::Tuple(cs) = &c.node {
                assert!(matches!(cs[0].node, ur::explicit::Constructor::Rel(1)));
            }
        }
        _ => panic!("expected Proj"),
    }
}

#[test]
fn explicit_lift_con_in_con_trecord() {
    let rel0 = Located::dummy(ur::explicit::Constructor::Rel(0));
    let trec = Located::dummy(ur::explicit::Constructor::TRecord(Box::new(rel0)));
    let out = environment::lift_con_in_con(trec, 0);
    match &out.node {
        ur::explicit::Constructor::TRecord(c) => {
            assert!(matches!(c.node, ur::explicit::Constructor::Rel(1)));
        }
        _ => panic!("expected TRecord"),
    }
}

#[test]
fn explicit_lift_kind_in_con_kabs() {
    let _k_type = Located::dummy(ur::explicit::Kind::Type);
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let kabs = Located::dummy(ur::explicit::Constructor::KAbs("a".into(), Box::new(unit)));
    let out = environment::lift_kind_in_con(kabs, 0);
    assert!(matches!(out.node, ur::explicit::Constructor::KAbs(_, _)));
}

#[test]
fn explicit_lift_kind_in_con_kapp() {
    let k_rel = Located::dummy(ur::explicit::Kind::Rel(0));
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let kapp = Located::dummy(ur::explicit::Constructor::KApp(
        Box::new(unit),
        Box::new(k_rel.clone()),
    ));
    let out = environment::lift_kind_in_con(kapp, 0);
    match &out.node {
        ur::explicit::Constructor::KApp(_, k) => {
            assert!(matches!(k.node, ur::explicit::Kind::Rel(1)));
        }
        _ => panic!("expected KApp"),
    }
}

#[test]
fn explicit_lift_kind_in_con_proj() {
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let tup = Located::dummy(ur::explicit::Constructor::Tuple(vec![unit]));
    let proj = Located::dummy(ur::explicit::Constructor::Proj(Box::new(tup), 1));
    let out = environment::lift_kind_in_con(proj, 0);
    assert!(matches!(out.node, ur::explicit::Constructor::Proj(_, 1)));
}

#[test]
fn explicit_lift_kind_in_con_trecord() {
    let unit = Located::dummy(ur::explicit::Constructor::Unit);
    let trec = Located::dummy(ur::explicit::Constructor::TRecord(Box::new(unit)));
    let out = environment::lift_kind_in_con(trec, 0);
    assert!(matches!(out.node, ur::explicit::Constructor::TRecord(_)));
}
