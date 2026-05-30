//! Integration tests for the Monomorphized module.
//!
//! Catches mutants in mono utilities, typ::compare, environment, classify_datatype.

use std::cmp::Ordering;
use ur::datatype_kind::DatatypeKind;
use ur::error_types::Located;
use ur::monomorphized::utilities;
use ur::monomorphized::utilities::typ;
use ur::monomorphized::{environment, Exp, Pat, PatCon, Typ};

#[test]
fn mono_classify_datatype_enum() {
    let constrs: Vec<(String, usize, Option<ur::monomorphized::LocTyp>)> =
        vec![("A".into(), 0, None), ("B".into(), 1, None)];
    assert_eq!(
        utilities::classify_datatype(0, &constrs),
        DatatypeKind::Enum
    );
}

#[test]
fn mono_classify_datatype_option() {
    let unit = Located::dummy(Typ::Source);
    let constrs: Vec<(String, usize, Option<ur::monomorphized::LocTyp>)> =
        vec![("None".into(), 0, None), ("Some".into(), 1, Some(unit))];
    assert_eq!(
        utilities::classify_datatype(0, &constrs),
        DatatypeKind::Option
    );
}

#[test]
fn mono_classify_datatype_default() {
    let unit = Located::dummy(Typ::Source);
    let constrs: Vec<(String, usize, Option<ur::monomorphized::LocTyp>)> = vec![
        ("A".into(), 0, Some(unit.clone())),
        ("B".into(), 1, Some(unit)),
    ];
    assert_eq!(
        utilities::classify_datatype(0, &constrs),
        DatatypeKind::Default
    );
}

#[test]
fn mono_sort_fields_orders_alphabetically() {
    let mut fields: Vec<(String, i32)> = vec![("z".into(), 3), ("a".into(), 1), ("m".into(), 2)];
    utilities::sort_fields(&mut fields);
    assert_eq!(fields[0].0, "a");
    assert_eq!(fields[1].0, "m");
    assert_eq!(fields[2].0, "z");
}

#[test]
fn mono_typ_compare_same_fun_equal() {
    let unit = Located::dummy(Typ::Source);
    let t = Located::dummy(Typ::Fun(Box::new(unit.clone()), Box::new(unit.clone())));
    assert_eq!(typ::compare(&t, &t), Ordering::Equal);
}

#[test]
fn mono_typ_compare_source_source_equal() {
    let t = Located::dummy(Typ::Source);
    assert_eq!(typ::compare(&t, &t), Ordering::Equal);
}

#[test]
fn mono_typ_compare_fun_vs_source_not_equal() {
    let unit = Located::dummy(Typ::Source);
    let fun_typ = Located::dummy(Typ::Fun(Box::new(unit.clone()), Box::new(unit)));
    let source_typ = Located::dummy(Typ::Source);
    assert!(typ::compare(&fun_typ, &source_typ) != Ordering::Equal);
}

#[test]
fn mono_typ_compare_record_differ() {
    let unit = Located::dummy(Typ::Source);
    let r1 = Located::dummy(Typ::Record(vec![("a".into(), unit.clone())]));
    let r2 = Located::dummy(Typ::Record(vec![("b".into(), unit)]));
    assert!(typ::compare(&r1, &r2) != Ordering::Equal);
}

#[test]
fn mono_lift_exp_in_exp_rel_at_bound() {
    let e = Located::dummy(Exp::Rel(0));
    let out = environment::lift_exp_in_exp(0, &e);
    assert!(matches!(out.node, Exp::Rel(1)));
}

#[test]
fn mono_lift_exp_in_exp_rel_below_bound() {
    let e = Located::dummy(Exp::Rel(0));
    let out = environment::lift_exp_in_exp(1, &e);
    assert!(matches!(out.node, Exp::Rel(0)));
}

#[test]
fn mono_pat_binds_n_var() {
    let unit = Located::dummy(Typ::Source);
    let p = Located::dummy(Pat::Var("x".into(), unit));
    assert_eq!(environment::pat_binds_n(&p), 1);
}

#[test]
fn mono_pat_binds_n_prim() {
    let p = Located::dummy(Pat::Prim(ur::primitives::Prim::Int(0)));
    assert_eq!(environment::pat_binds_n(&p), 0);
}

// ---------------------------------------------------------------------------
// Phase 4 expanded: typ::compare, exp::exists, decl::exists, environment, fuse
// ---------------------------------------------------------------------------

use ur::monomorphized::utilities::{decl, exp};

#[test]
fn mono_typ_compare_option() {
    let unit = Located::dummy(Typ::Source);
    let opt = Located::dummy(Typ::Option(Box::new(unit)));
    assert_eq!(typ::compare(&opt, &opt), Ordering::Equal);
}

#[test]
fn mono_typ_compare_list() {
    let unit = Located::dummy(Typ::Source);
    let lst = Located::dummy(Typ::List(Box::new(unit)));
    assert_eq!(typ::compare(&lst, &lst), Ordering::Equal);
}

#[test]
fn mono_typ_compare_signal() {
    let unit = Located::dummy(Typ::Source);
    let sig = Located::dummy(Typ::Signal(Box::new(unit)));
    assert_eq!(typ::compare(&sig, &sig), Ordering::Equal);
}

#[test]
fn mono_typ_compare_datatype() {
    let def = std::sync::Arc::new(std::sync::Mutex::new(ur::monomorphized::DatatypeDef {
        kind: DatatypeKind::Enum,
        constrs: vec![],
    }));
    let dt = Located::dummy(Typ::Datatype(1, def));
    assert_eq!(typ::compare(&dt, &dt), Ordering::Equal);
}

#[test]
fn mono_typ_compare_ffi() {
    let ffi = Located::dummy(Typ::Ffi("M".into(), "T".into()));
    assert_eq!(typ::compare(&ffi, &ffi), Ordering::Equal);
}

#[test]
fn mono_exp_exists_app() {
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let app = Located::dummy(Exp::App(Box::new(prim.clone()), Box::new(prim)));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::App(_, _));
    assert!(exp::exists(&app, &ft, &fe));
}

#[test]
fn mono_exp_exists_abs() {
    let unit = Located::dummy(Typ::Source);
    let rel = Located::dummy(Exp::Rel(0));
    let abs = Located::dummy(Exp::Abs("x".into(), unit.clone(), unit, Box::new(rel)));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Abs(_, _, _, _));
    assert!(exp::exists(&abs, &ft, &fe));
}

#[test]
fn mono_exp_exists_let() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let let_e = Located::dummy(Exp::Let(
        "x".into(),
        unit,
        Box::new(prim.clone()),
        Box::new(prim),
    ));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Let(_, _, _, _));
    assert!(exp::exists(&let_e, &ft, &fe));
}

#[test]
fn mono_exp_exists_record() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let fields = vec![("f".into(), prim, unit)];
    let rec_e = Located::dummy(Exp::Record(fields));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Record(_));
    assert!(exp::exists(&rec_e, &ft, &fe));
}

#[test]
fn mono_exp_exists_strcat() {
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let strcat = Located::dummy(Exp::Strcat(Box::new(prim.clone()), Box::new(prim)));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Strcat(_, _));
    assert!(exp::exists(&strcat, &ft, &fe));
}

#[test]
fn mono_exp_exists_seq() {
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let seq = Located::dummy(Exp::Seq(Box::new(prim.clone()), Box::new(prim)));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Seq(_, _));
    assert!(exp::exists(&seq, &ft, &fe));
}

#[test]
fn mono_exp_exists_write() {
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let write = Located::dummy(Exp::Write(Box::new(prim)));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Write(_));
    assert!(exp::exists(&write, &ft, &fe));
}

#[test]
fn mono_exp_exists_none() {
    let unit = Located::dummy(Typ::Source);
    let none_e = Located::dummy(Exp::None(unit));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::None(_));
    assert!(exp::exists(&none_e, &ft, &fe));
}

#[test]
fn mono_exp_exists_some() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let some_e = Located::dummy(Exp::Some(unit, Box::new(prim)));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Some(_, _));
    assert!(exp::exists(&some_e, &ft, &fe));
}

#[test]
fn mono_sub_exp_in_exp_rel() {
    let rep = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(42)));
    let body = Located::dummy(Exp::Rel(0));
    let out = environment::sub_exp_in_exp(0, &rep, &body);
    assert!(matches!(out.node, Exp::Prim(ur::primitives::Prim::Int(42))));
}

#[test]
fn mono_multi_lift_rel() {
    let e = Located::dummy(Exp::Rel(0));
    let out = environment::multi_lift(2, &e);
    assert!(matches!(out.node, Exp::Rel(2)));
}

#[test]
fn mono_pat_binds_n_con() {
    let pcon = PatCon::Var(0);
    let p = Located::dummy(Pat::Con(DatatypeKind::Enum, pcon, None));
    assert_eq!(environment::pat_binds_n(&p), 0);
}

#[test]
fn mono_pat_binds_n_record() {
    let unit = Located::dummy(Typ::Source);
    let pvar = Located::dummy(Pat::Var("x".into(), unit.clone()));
    let fields = vec![("f".into(), pvar, unit)];
    let p = Located::dummy(Pat::Record(fields));
    assert_eq!(environment::pat_binds_n(&p), 1);
}

#[test]
fn mono_pat_binds_n_some() {
    let unit = Located::dummy(Typ::Source);
    let pvar = Located::dummy(Pat::Var("x".into(), unit.clone()));
    let p = Located::dummy(Pat::Some(unit, Box::new(pvar)));
    assert_eq!(environment::pat_binds_n(&p), 1);
}

#[test]
fn mono_pat_binds_n_none() {
    let unit = Located::dummy(Typ::Source);
    let p = Located::dummy(Pat::None(unit));
    assert_eq!(environment::pat_binds_n(&p), 0);
}

#[test]
fn mono_fuse_empty() {
    let file: ur::monomorphized::File = (vec![], vec![]);
    let out = ur::monomorphized::fuse::fuse(file);
    assert!(out.0.is_empty());
    assert!(out.1.is_empty());
}

#[test]
fn mono_untangle_empty() {
    let file: ur::monomorphized::File = (vec![], vec![]);
    let out = ur::monomorphized::untangle::untangle(file);
    assert!(out.0.is_empty());
    assert!(out.1.is_empty());
}

#[test]
fn mono_shake_empty() {
    let file: ur::monomorphized::File = (vec![], vec![]);
    let out = ur::monomorphized::mono_shake::shake(file);
    assert!(out.0.is_empty());
    assert!(out.1.is_empty());
}

#[test]
fn mono_decl_exists_datatype() {
    let unit = Located::dummy(Typ::Source);
    let dt = ur::monomorphized::DatatypeDecl {
        name: "T".into(),
        id: 0,
        constrs: vec![("A".into(), 1, None), ("B".into(), 2, Some(unit))],
    };
    let decl = Located::dummy(ur::monomorphized::Decl::Datatype(vec![dt]));
    let ft = |_: &Typ| false;
    let fe = |_: &Exp| false;
    let fd = |d: &ur::monomorphized::Decl| matches!(d, ur::monomorphized::Decl::Datatype(_));
    assert!(decl::exists(&decl, &ft, &fe, &fd));
}

#[test]
fn mono_typ_exists_option() {
    let unit = Located::dummy(Typ::Source);
    let opt = Located::dummy(Typ::Option(Box::new(unit)));
    let pred = |t: &Typ| matches!(t, Typ::Option(_));
    assert!(typ::exists(&opt, &pred));
}

// Phase E: Monomorphized pipeline and utilities
use ur::export::{Effect, ExportKind};
use ur::monomorphized::Decl;

#[test]
fn mono_script_check_classify_val() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Decl::Val("x".into(), 1, unit, prim, "".into()));
    let file: ur::monomorphized::File = (vec![decl], vec![]);
    let settings = ur::settings::Settings::new();
    let mut errors = ur::error_types::ErrorReporter::new();
    let out = ur::monomorphized::script_check::classify(file, &settings, &mut errors);
    assert_eq!(out.0.len(), 1);
}

#[test]
fn mono_sig_check_passthrough() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Decl::Val("x".into(), 0, unit, prim, "".into()));
    let file: ur::monomorphized::File = (vec![decl], vec![]);
    let out = ur::monomorphized::sig_check::check(file);
    assert_eq!(out.0.len(), 1);
}

#[test]
fn mono_path_check_empty() {
    let file: ur::monomorphized::File = (vec![], vec![]);
    let mut errors = ur::error_types::ErrorReporter::new();
    ur::monomorphized::path_check::check(&file, &mut errors);
    assert!(!errors.has_errors());
}

#[test]
fn mono_db_mode_check_classify_empty() {
    let file: ur::monomorphized::File = (vec![], vec![]);
    let out = ur::monomorphized::db_mode_check::classify(file);
    assert!(out.0.is_empty());
}

#[test]
fn mono_fuse_non_empty() {
    let _unit = Located::dummy(Typ::Source);
    let dt = ur::monomorphized::DatatypeDecl {
        name: "T".into(),
        id: 0,
        constrs: vec![("A".into(), 1, None)],
    };
    let decl = Located::dummy(Decl::Datatype(vec![dt]));
    let file: ur::monomorphized::File = (vec![decl], vec![]);
    let out = ur::monomorphized::fuse::fuse(file);
    assert!(!out.0.is_empty());
}

#[test]
fn mono_shake_non_empty() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let val_decl = Located::dummy(Decl::Val("x".into(), 0, unit.clone(), prim, "".into()));
    let export_decl = Located::dummy(Decl::Export(
        ExportKind::Link(Effect::ReadOnly),
        "main".into(),
        0,
        vec![],
        unit,
        false,
    ));
    let file: ur::monomorphized::File = (vec![val_decl, export_decl], vec![]);
    let out = ur::monomorphized::mono_shake::shake(file);
    assert!(!out.0.is_empty());
}

#[test]
fn mono_decl_exists_val() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Decl::Val("x".into(), 0, unit, prim, "".into()));
    let ft = |_: &Typ| false;
    let fe = |_: &Exp| false;
    let fd = |d: &Decl| matches!(d, Decl::Val(_, _, _, _, _));
    assert!(decl::exists(&decl, &ft, &fe, &fd));
}

#[test]
fn mono_decl_exists_sequence() {
    let decl = Located::dummy(Decl::Sequence("s".into()));
    let ft = |_: &Typ| false;
    let fe = |_: &Exp| false;
    let fd = |d: &Decl| matches!(d, Decl::Sequence(_));
    assert!(decl::exists(&decl, &ft, &fe, &fd));
}

#[test]
fn mono_decl_exists_cookie() {
    let decl = Located::dummy(Decl::Cookie("c".into()));
    let ft = |_: &Typ| false;
    let fe = |_: &Exp| false;
    let fd = |d: &Decl| matches!(d, Decl::Cookie(_));
    assert!(decl::exists(&decl, &ft, &fe, &fd));
}

#[test]
fn mono_decl_exists_style() {
    let decl = Located::dummy(Decl::Style("s".into()));
    let ft = |_: &Typ| false;
    let fe = |_: &Exp| false;
    let fd = |d: &Decl| matches!(d, Decl::Style(_));
    assert!(decl::exists(&decl, &ft, &fe, &fd));
}

#[test]
fn mono_exp_exists_unop() {
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let unop = Located::dummy(Exp::Unop("neg".into(), Box::new(prim)));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Unop(_, _));
    assert!(exp::exists(&unop, &ft, &fe));
}

#[test]
fn mono_exp_exists_binop() {
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let binop = Located::dummy(Exp::Binop(
        ur::monomorphized::BinopIntness::Int,
        "add".into(),
        Box::new(prim.clone()),
        Box::new(prim),
    ));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Binop(_, _, _, _));
    assert!(exp::exists(&binop, &ft, &fe));
}

#[test]
fn mono_exp_exists_field() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let rec_exp = Located::dummy(Exp::Record(vec![("f".into(), prim, unit)]));
    let field = Located::dummy(Exp::Field(Box::new(rec_exp), "f".into()));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Field(_, _));
    assert!(exp::exists(&field, &ft, &fe));
}

#[test]
fn mono_exp_exists_case() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let pvar = Located::dummy(Pat::Var("x".into(), unit.clone()));
    let meta = ur::monomorphized::CaseMeta {
        disc: unit.clone(),
        result: unit,
    };
    let case = Located::dummy(Exp::Case(
        Box::new(prim),
        vec![(
            pvar,
            Located::dummy(Exp::Prim(ur::primitives::Prim::Int(1))),
        )],
        meta,
    ));
    let ft = |_: &Typ| false;
    let fe = |e: &Exp| matches!(e, Exp::Case(_, _, _));
    assert!(exp::exists(&case, &ft, &fe));
}

#[test]
fn mono_decl_exists_export() {
    let unit = Located::dummy(Typ::Source);
    let decl = Located::dummy(Decl::Export(
        ExportKind::Link(Effect::ReadOnly),
        "main".into(),
        0,
        vec![],
        unit,
        false,
    ));
    let ft = |_: &Typ| false;
    let fe = |_: &Exp| false;
    let fd = |d: &Decl| matches!(d, Decl::Export(_, _, _, _, _, _));
    assert!(decl::exists(&decl, &ft, &fe, &fd));
}

#[test]
fn mono_side_check_empty() {
    let file: ur::monomorphized::File = (vec![], vec![]);
    let settings = ur::settings::Settings::default();
    let mut errors = ur::error_types::ErrorReporter::new();
    let (out, env_vars) = ur::monomorphized::side_check::check(file, &settings, &mut errors);
    assert!(out.0.is_empty());
    assert!(env_vars.is_empty());
    assert!(!errors.has_errors());
}

#[test]
fn mono_untangle_non_empty() {
    let unit = Located::dummy(Typ::Source);
    let prim = Located::dummy(Exp::Prim(ur::primitives::Prim::Int(0)));
    let decl = Located::dummy(Decl::Val("x".into(), 0, unit, prim, "".into()));
    let file: ur::monomorphized::File = (vec![decl], vec![]);
    let out = ur::monomorphized::untangle::untangle(file);
    assert!(!out.0.is_empty());
}
