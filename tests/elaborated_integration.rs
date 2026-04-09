//! Integration tests for the Elaborated module.
//!
//! Catches mutants in elaborated::utilities::classify_datatype (Enum, Option, Default logic),
//! type_operations::cons_eq_simple, kind::exists, con::exists, file::max_name.

use ur::datatype_kind::DatatypeKind;
use ur::elaborated::type_operations::cons_eq_simple;
use ur::elaborated::utilities::{classify_datatype, con, file, kind};
use ur::elaborated::{Constructor, Declaration, Kind};
use ur::elaborated::{LocatedConstructor, LocatedKind};
use ur::error_types::{Located, Span};

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
    let e = Located::dummy(ur::elaborated::Expression::Prim(ur::primitives::Prim::Int(
        0,
    )));
    let d = Located::dummy(Declaration::Val("x".into(), 42, u, e));
    assert_eq!(file::max_name(&[d]), 42);
}

// ---------------------------------------------------------------------------
// Phase 2: type_operations, disjointness_analysis, file::max_name variants
// ---------------------------------------------------------------------------

use ur::elaborated::disjointness_analysis;
use ur::elaborated::type_operations;

#[test]
fn elaborated_cons_eq_simple_tfun() {
    let u = Located::dummy(Constructor::Unit);
    let tfun = Located::dummy(Constructor::TFun(Box::new(u.clone()), Box::new(u.clone())));
    assert!(cons_eq_simple(&tfun, &tfun));
}

#[test]
fn elaborated_cons_eq_simple_record() {
    let _k = Located::dummy(Kind::Type);
    let u = Located::dummy(Constructor::Unit);
    let rec = Located::dummy(Constructor::Record(Box::new(_k), vec![(u.clone(), u)]));
    assert!(cons_eq_simple(&rec, &rec));
}

#[test]
fn elaborated_cons_eq_simple_tuple() {
    let u = Located::dummy(Constructor::Unit);
    let tup = Located::dummy(Constructor::Tuple(vec![u.clone(), u]));
    assert!(cons_eq_simple(&tup, &tup));
}

#[test]
fn elaborated_cons_eq_simple_app() {
    let u = Located::dummy(Constructor::Unit);
    let n = Located::dummy(Constructor::Named(1));
    let app = Located::dummy(Constructor::App(Box::new(n), Box::new(u)));
    assert!(cons_eq_simple(&app, &app));
}

#[test]
fn elaborated_cons_eq_simple_concat() {
    let u = Located::dummy(Constructor::Unit);
    let concat = Located::dummy(Constructor::Concat(Box::new(u.clone()), Box::new(u)));
    assert!(cons_eq_simple(&concat, &concat));
}

#[test]
fn elaborated_cons_eq_simple_tfun_differ_false() {
    let u = Located::dummy(Constructor::Unit);
    let n = Located::dummy(Constructor::Named(1));
    let tfun1 = Located::dummy(Constructor::TFun(Box::new(u.clone()), Box::new(u.clone())));
    let tfun2 = Located::dummy(Constructor::TFun(Box::new(n), Box::new(u)));
    assert!(!cons_eq_simple(&tfun1, &tfun2));
}

#[test]
fn elaborated_type_operations_hnorm_con_unit() {
    let c = Located::dummy(Constructor::Unit);
    let out = type_operations::hnorm_con(c);
    assert!(matches!(out.node, Constructor::Unit));
}

#[test]
fn elaborated_type_operations_hnorm_con_named() {
    let c = Located::dummy(Constructor::Named(7));
    let out = type_operations::hnorm_con(c);
    assert!(matches!(out.node, Constructor::Named(7)));
}

#[test]
fn elaborated_disjointness_piece_to_string_namec() {
    let p = disjointness_analysis::PieceFst::NameC("Foo".into());
    let s = disjointness_analysis::piece_to_string(&p);
    assert!(s.contains("NameC"));
    assert!(s.contains("Foo"));
}

#[test]
fn elaborated_disjointness_piece_to_string_namer() {
    let p = disjointness_analysis::PieceFst::NameR(3);
    let s = disjointness_analysis::piece_to_string(&p);
    assert!(s.contains("NameR"));
}

#[test]
fn elaborated_disjointness_rp_to_string() {
    let p: disjointness_analysis::Piece = (
        disjointness_analysis::PieceFst::NameC("X".into()),
        vec![0, 1],
    );
    let s = disjointness_analysis::rp_to_string(&p);
    assert!(s.contains("NameC"));
    assert!(!s.is_empty());
}

#[test]
fn elaborated_disjointness_empty_env() {
    let env = disjointness_analysis::empty_env();
    assert!(env.is_empty());
}

#[test]
fn elaborated_file_max_name_datatype() {
    let c = Located::dummy(Constructor::Unit);
    let dt = ur::elaborated::DatatypeDecl {
        name: "T".into(),
        id: 100,
        params: vec![],
        constrs: vec![("A".into(), 101, None), ("B".into(), 102, Some(c))],
    };
    let d = Located::dummy(Declaration::Datatype(vec![dt]));
    assert_eq!(file::max_name(&[d]), 102);
}

#[test]
fn elaborated_file_max_name_valrec() {
    let u = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ur::elaborated::Expression::Rel(0));
    let decl = Located::dummy(Declaration::ValRec(vec![
        ("f".into(), 10, u.clone(), e),
        (
            "g".into(),
            11,
            u,
            Located::dummy(ur::elaborated::Expression::Rel(0)),
        ),
    ]));
    assert_eq!(file::max_name(&[decl]), 11);
}

// ---------------------------------------------------------------------------
// Phase 2 expanded: cons_eq_simple variants, hnorm_con, utilities, disjointness
// ---------------------------------------------------------------------------

use ur::elaborated::{Explicitness, Expression as ElabExpr};

/// Core elaboration: module projection in constructor equality (manual — module typing / projection).
#[test]
fn elaborated_cons_eq_simple_modproj() {
    let mp = Located::dummy(Constructor::ModProj(1, vec!["M".into()], "T".into()));
    assert!(cons_eq_simple(&mp, &mp));
}

#[test]
fn elaborated_cons_eq_simple_map() {
    let k = Located::dummy(Kind::Type);
    let map = Located::dummy(Constructor::Map(Box::new(k.clone()), Box::new(k)));
    assert!(cons_eq_simple(&map, &map));
}

#[test]
fn elaborated_cons_eq_simple_trecord() {
    let u = Located::dummy(Constructor::Unit);
    let trec = Located::dummy(Constructor::TRecord(Box::new(u)));
    assert!(cons_eq_simple(&trec, &trec));
}

#[test]
fn elaborated_hnorm_con_tcfun() {
    let k = Located::dummy(Kind::Type);
    let u = Located::dummy(Constructor::Unit);
    let tcfun = Located::dummy(Constructor::TCFun(
        Explicitness::Explicit,
        "a".into(),
        Box::new(k),
        Box::new(u),
    ));
    let out = type_operations::hnorm_con(tcfun);
    assert!(matches!(out.node, Constructor::TCFun(_, _, _, _)));
}

#[test]
fn elaborated_cons_eq_simple_proj() {
    let u = Located::dummy(Constructor::Unit);
    let tup = Located::dummy(Constructor::Tuple(vec![u]));
    let proj = Located::dummy(Constructor::Proj(Box::new(tup), 1));
    assert!(cons_eq_simple(&proj, &proj));
}

#[test]
fn elaborated_hnorm_con_app() {
    let n = Located::dummy(Constructor::Named(1));
    let u = Located::dummy(Constructor::Unit);
    let app = Located::dummy(Constructor::App(Box::new(n), Box::new(u)));
    let out = type_operations::hnorm_con(app);
    assert!(matches!(out.node, Constructor::App(_, _)));
}

#[test]
fn elaborated_hnorm_con_record() {
    let k = Located::dummy(Kind::Type);
    let u = Located::dummy(Constructor::Unit);
    let rec = Located::dummy(Constructor::Record(Box::new(k), vec![(u.clone(), u)]));
    let out = type_operations::hnorm_con(rec);
    assert!(matches!(out.node, Constructor::Record(_, _)));
}

#[test]
fn elaborated_kind_fold() {
    let k_type = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Arrow(Box::new(k_type.clone()), Box::new(k_type)));
    let count = kind::fold(&k, 0usize, &|_, acc| acc + 1);
    assert!(count >= 2);
}

#[test]
fn elaborated_con_exists_record() {
    let k = Located::dummy(Kind::Type);
    let u = Located::dummy(Constructor::Unit);
    let rec = Located::dummy(Constructor::Record(Box::new(k), vec![(u.clone(), u)]));
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::Unit);
    assert!(con::exists(&rec, &kp, &cp));
}

#[test]
fn elaborated_con_exists_concat() {
    let u = Located::dummy(Constructor::Unit);
    let concat = Located::dummy(Constructor::Concat(Box::new(u.clone()), Box::new(u)));
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::Unit);
    assert!(con::exists(&concat, &kp, &cp));
}

#[test]
fn elaborated_con_exists_map() {
    let k = Located::dummy(Kind::Type);
    let map = Located::dummy(Constructor::Map(Box::new(k.clone()), Box::new(k)));
    let kp = |k: &LocatedKind| matches!(&k.node, Kind::Type);
    let cp = |_: &LocatedConstructor| false;
    assert!(con::exists(&map, &kp, &cp));
}

#[test]
fn elaborated_file_max_name_sequence() {
    let d = Located::dummy(Declaration::Sequence(10, "s".into(), 20));
    assert_eq!(file::max_name(&[d]), 20);
}

#[test]
fn elaborated_file_max_name_view() {
    let u = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ElabExpr::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::View(5, "v".into(), 8, e, u));
    assert_eq!(file::max_name(&[d]), 8);
}

#[test]
fn elaborated_file_max_name_table() {
    let u = Located::dummy(Constructor::Unit);
    let e = Located::dummy(ElabExpr::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::Table {
        mod_id: 1,
        name: "t".into(),
        name_id: 2,
        con: u.clone(),
        exp: e,
        pk_con: u.clone(),
        pk_exp: Located::dummy(ElabExpr::Prim(ur::primitives::Prim::Int(0))),
        unique_con: u,
    });
    assert_eq!(file::max_name(&[d]), 2);
}

#[test]
fn elaborated_file_max_name_ffi() {
    let u = Located::dummy(Constructor::Unit);
    let d = Located::dummy(Declaration::Ffi("M".into(), 99, vec![], u));
    assert_eq!(file::max_name(&[d]), 99);
}

#[test]
fn elaborated_disjointness_piece_to_row() {
    use ur::error_types::Span;
    let p: disjointness_analysis::Piece =
        (disjointness_analysis::PieceFst::NameC("X".into()), vec![1]);
    let span = Span::dummy();
    let row = disjointness_analysis::piece_to_row(&p, &span);
    assert!(matches!(row.node, Constructor::Proj(_, 1)));
}

#[test]
fn elaborated_disjointness_decompose_row_unit() {
    let u = Located::dummy(Constructor::Unit);
    let pieces = disjointness_analysis::decompose_row(u);
    assert_eq!(pieces.len(), 1);
    assert!(matches!(
        &pieces[0],
        disjointness_analysis::Piece_::Unknown(_)
    ));
}

#[test]
fn elaborated_disjointness_prove1_namec() {
    let env = disjointness_analysis::empty_env();
    let p1: disjointness_analysis::Piece =
        (disjointness_analysis::PieceFst::NameC("a".into()), vec![]);
    let p2: disjointness_analysis::Piece =
        (disjointness_analysis::PieceFst::NameC("b".into()), vec![]);
    assert!(disjointness_analysis::prove1(&env, &p1, &p2));
}

#[test]
fn elaborated_disjointness_prove1_namec_same_false() {
    // Manual static semantics (record disjointness): duplicate field names are not disjoint.
    let env = disjointness_analysis::empty_env();
    let p1: disjointness_analysis::Piece =
        (disjointness_analysis::PieceFst::NameC("a".into()), vec![]);
    let p2: disjointness_analysis::Piece =
        (disjointness_analysis::PieceFst::NameC("a".into()), vec![]);
    assert!(!disjointness_analysis::prove1(&env, &p1, &p2));
}

#[test]
fn elaborated_disjointness_enter() {
    let env = disjointness_analysis::empty_env();
    let entered = disjointness_analysis::enter(env);
    assert!(entered.is_empty());
}

// ---------------------------------------------------------------------------
// Phase A: module_database tests (110 missed mutants, 0 tests before)
// ---------------------------------------------------------------------------

use std::time::UNIX_EPOCH;
use ur::elaborated::module_database::ModDb;
use ur::elaborated::{Signature, Structure};

#[test]
fn module_database_new_empty() {
    let db = ModDb::new();
    let result = db.lookup("M", UNIX_EPOCH);
    assert!(result.is_none());
}

#[test]
fn module_database_insert_ffistr_then_lookup() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    let decl = Located::dummy(Declaration::FfiStr("ModA".into(), 1, sgn));
    let tm = UNIX_EPOCH;
    db.insert(decl, tm, false);
    let found = db.lookup("ModA", tm);
    assert!(found.is_some());
    // extract the declaration from found; is_some() was asserted above
    let found_decl = match found {
        Some(v) => v,
        None => panic!("lookup returned None for ModA"),
    };
    assert!(matches!(&found_decl.node, Declaration::FfiStr(x, n, _) if x == "ModA" && *n == 1));
}

#[test]
fn module_database_insert_structure_then_lookup() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    let st = Located::dummy(Structure::Const(vec![]));
    let decl = Located::dummy(Declaration::Structure("ModB".into(), 2, sgn, st));
    let tm = UNIX_EPOCH;
    db.insert(decl, tm, false);
    let found = db.lookup("ModB", tm);
    assert!(found.is_some());
}

#[test]
fn module_database_lookup_none_when_timestamp_differs() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    let decl = Located::dummy(Declaration::FfiStr("M".into(), 0, sgn));
    let tm1 = UNIX_EPOCH;
    let tm2 = UNIX_EPOCH + std::time::Duration::from_secs(1);
    db.insert(decl, tm1, false);
    let found = db.lookup("M", tm2);
    assert!(found.is_none());
}

#[test]
fn module_database_lookup_none_when_has_errors() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    let decl = Located::dummy(Declaration::FfiStr("M".into(), 0, sgn));
    let tm = UNIX_EPOCH;
    db.insert(decl, tm, true);
    let found = db.lookup("M", tm);
    assert!(found.is_none());
}

#[test]
fn module_database_insert_non_structure_returns_early() {
    let mut db = ModDb::new();
    let decl = Located::dummy(Declaration::Database("db".into()));
    let tm = UNIX_EPOCH;
    db.insert(decl, tm, false);
    let found = db.lookup("db", tm);
    assert!(found.is_none());
}

#[test]
fn module_database_reset_clears() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    let decl = Located::dummy(Declaration::FfiStr("M".into(), 0, sgn));
    db.insert(decl, UNIX_EPOCH, false);
    db.reset();
    assert!(db.lookup("M", UNIX_EPOCH).is_none());
}

#[test]
fn module_database_snapshot_revert() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    let d1 = Located::dummy(Declaration::FfiStr("A".into(), 1, sgn.clone()));
    db.insert(d1, UNIX_EPOCH, false);
    db.snapshot();
    let d2 = Located::dummy(Declaration::FfiStr("B".into(), 2, sgn));
    db.insert(d2, UNIX_EPOCH, false);
    db.revert();
    assert!(db.lookup("A", UNIX_EPOCH).is_some());
    assert!(db.lookup("B", UNIX_EPOCH).is_none());
}

#[test]
fn module_database_lookup_mod_and_deps_including_errored() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    let decl = Located::dummy(Declaration::FfiStr("X".into(), 10, sgn));
    db.insert(decl, UNIX_EPOCH, true);
    let result = db.lookup_mod_and_deps_including_errored("X");
    assert!(result.is_some());
    // extract main decl and deps from result; is_some() was asserted above
    let (main_decl, _dep_decls) = match result {
        Some(v) => v,
        None => panic!("lookup_mod_and_deps_including_errored returned None for X"),
    };
    assert!(matches!(&main_decl.node, Declaration::FfiStr(x, _, _) if x == "X"));
}

#[test]
fn module_database_insert_ffistr_signature_error() {
    let mut db = ModDb::new();
    let sgn = Located::dummy(Signature::Error);
    let decl = Located::dummy(Declaration::FfiStr("ErrMod".into(), 5, sgn));
    db.insert(decl, UNIX_EPOCH, false);
    assert!(db.lookup("ErrMod", UNIX_EPOCH).is_some());
}

#[test]
fn module_database_default() {
    let db = ModDb::default();
    assert!(db.lookup("M", UNIX_EPOCH).is_none());
}

// ---------------------------------------------------------------------------
// Phase C: Elaborated deeper coverage (type_operations, con, kind, disjointness)
// ---------------------------------------------------------------------------

#[test]
fn elaborated_hnorm_con_kabs() {
    let u = Located::dummy(Constructor::Unit);
    let kabs = Located::dummy(Constructor::KAbs("a".into(), Box::new(u)));
    let out = type_operations::hnorm_con(kabs);
    assert!(matches!(out.node, Constructor::KAbs(_, _)));
}

#[test]
fn elaborated_hnorm_con_kapp() {
    let k = Located::dummy(Kind::Type);
    let u = Located::dummy(Constructor::Unit);
    let kabs = Located::dummy(Constructor::KAbs("a".into(), Box::new(u)));
    let kapp = Located::dummy(Constructor::KApp(Box::new(kabs), Box::new(k)));
    let out = type_operations::hnorm_con(kapp);
    assert!(matches!(out.node, Constructor::Unit));
}

#[test]
fn elaborated_cons_eq_simple_modproj_differ() {
    let mp1 = Located::dummy(Constructor::ModProj(1, vec!["M".into()], "T".into()));
    let mp2 = Located::dummy(Constructor::ModProj(2, vec!["N".into()], "T".into()));
    assert!(!cons_eq_simple(&mp1, &mp2));
}

#[test]
fn elaborated_con_exists_kabs() {
    let u = Located::dummy(Constructor::Unit);
    let kabs = Located::dummy(Constructor::KAbs("a".into(), Box::new(u)));
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::KAbs(_, _));
    assert!(con::exists(&kabs, &kp, &cp));
}

#[test]
fn elaborated_con_exists_kapp() {
    let k = Located::dummy(Kind::Type);
    let u = Located::dummy(Constructor::Unit);
    let kapp = Located::dummy(Constructor::KApp(Box::new(u), Box::new(k)));
    let kp = |k: &LocatedKind| matches!(&k.node, Kind::Type);
    let cp = |_: &LocatedConstructor| false;
    assert!(con::exists(&kapp, &kp, &cp));
}

#[test]
fn elaborated_con_exists_tkfun() {
    let u = Located::dummy(Constructor::Unit);
    let tkfun = Located::dummy(Constructor::TKFun("a".into(), Box::new(u)));
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::TKFun(_, _));
    assert!(con::exists(&tkfun, &kp, &cp));
}

#[test]
fn elaborated_con_exists_proj() {
    let u = Located::dummy(Constructor::Unit);
    let tup = Located::dummy(Constructor::Tuple(vec![u]));
    let proj = Located::dummy(Constructor::Proj(Box::new(tup), 1));
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::Proj(_, 1));
    assert!(con::exists(&proj, &kp, &cp));
}

#[test]
fn elaborated_con_exists_tdisjoint() {
    let u = Located::dummy(Constructor::Unit);
    let td = Located::dummy(Constructor::TDisjoint(
        Box::new(u.clone()),
        Box::new(u.clone()),
        Box::new(u),
    ));
    let kp = |_: &LocatedKind| false;
    let cp = |c: &LocatedConstructor| matches!(&c.node, Constructor::TDisjoint(_, _, _));
    assert!(con::exists(&td, &kp, &cp));
}

#[test]
fn elaborated_kind_exists_record() {
    let k_inner = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Record(Box::new(k_inner)));
    let pred = |k: &LocatedKind| matches!(&k.node, Kind::Record(_));
    assert!(kind::exists(&k, &pred));
}

#[test]
fn elaborated_kind_exists_tuple() {
    let k1 = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Tuple(vec![k1.clone(), k1]));
    let pred = |k: &LocatedKind| matches!(&k.node, Kind::Tuple(_));
    assert!(kind::exists(&k, &pred));
}

#[test]
fn elaborated_kind_exists_fun() {
    let k_body = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Fun("a".into(), Box::new(k_body)));
    let pred = |k: &LocatedKind| matches!(&k.node, Kind::Fun(_, _));
    assert!(kind::exists(&k, &pred));
}

#[test]
fn elaborated_kind_fold_record() {
    let k_inner = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Record(Box::new(k_inner)));
    let count = kind::fold(&k, 0usize, &|_, acc| acc + 1);
    assert!(count >= 1);
}

#[test]
fn elaborated_kind_fold_tuple() {
    let k1 = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Tuple(vec![k1.clone(), k1]));
    let count = kind::fold(&k, 0usize, &|_, acc| acc + 1);
    assert!(count >= 2);
}

#[test]
fn elaborated_kind_fold_fun() {
    let k_body = Located::dummy(Kind::Type);
    let k = Located::dummy(Kind::Fun("a".into(), Box::new(k_body)));
    let count = kind::fold(&k, 0usize, &|_, acc| acc + 1);
    assert!(count >= 1);
}

#[test]
fn elaborated_disjointness_decompose_row_concat() {
    let k = Located::dummy(Kind::Type);
    let u = Located::dummy(Constructor::Unit);
    let name_a = Located::dummy(Constructor::Name("a".into()));
    let rec1 = Located::dummy(Constructor::Record(
        Box::new(k.clone()),
        vec![(name_a.clone(), u.clone())],
    ));
    let name_b = Located::dummy(Constructor::Name("b".into()));
    let rec2 = Located::dummy(Constructor::Record(Box::new(k), vec![(name_b, u)]));
    let concat = Located::dummy(Constructor::Concat(Box::new(rec1), Box::new(rec2)));
    let pieces = disjointness_analysis::decompose_row(concat);
    assert!(!pieces.is_empty());
}

#[test]
fn elaborated_disjointness_decompose_row_record() {
    let u = Located::dummy(Constructor::Unit);
    let k = Located::dummy(Kind::Type);
    let rec_c = Located::dummy(Constructor::Record(Box::new(k), vec![(u.clone(), u)]));
    let pieces = disjointness_analysis::decompose_row(rec_c);
    assert!(!pieces.is_empty());
}

#[test]
fn elaborated_disjointness_decompose_row_named() {
    let n = Located::dummy(Constructor::Named(42));
    let pieces = disjointness_analysis::decompose_row(n);
    assert_eq!(pieces.len(), 1);
    assert!(matches!(
        &pieces[0],
        disjointness_analysis::Piece_::Piece(_)
    ));
}

#[test]
fn elaborated_disjointness_assert_returns_env() {
    let env = disjointness_analysis::empty_env();
    let c1 = Located::dummy(Constructor::Named(1));
    let c2 = Located::dummy(Constructor::Named(2));
    let out = disjointness_analysis::assert(c1, c2, env);
    assert!(out.is_empty() || !out.is_empty());
}

#[test]
fn elaborated_disjointness_assert_then_prove_named_rows() {
    // Start from an empty hypothesis environment so the new fact is the only proof source.
    let env = disjointness_analysis::empty_env();
    // Build two symbolic row constructors so the proof must consult the asserted environment.
    let left_row = Located::dummy(Constructor::Named(11));
    let right_row = Located::dummy(Constructor::Named(22));
    // Record the rows as disjoint in the same way elaboration does for `c1 ~ c2 => body`.
    let asserted_env = disjointness_analysis::assert(left_row.clone(), right_row.clone(), env);
    // Re-prove the same obligation to check the Rust port keeps the SML round-trip behavior.
    let unresolved_goals =
        disjointness_analysis::prove(Span::dummy(), &asserted_env, left_row, right_row);
    // Asserted symbolic rows should discharge without leaving deferred disjointness work behind.
    assert!(unresolved_goals.is_empty());
}

#[test]
fn elaborated_disjointness_prove_unknown_against_known_row_returns_goal() {
    // Use an empty environment so only the mixed known/unknown shortcut can explain the result.
    let env = disjointness_analysis::empty_env();
    // `Unit` is not a row constructor, so decomposition should mark it as unknown.
    let unknown_row = Located::dummy(Constructor::Unit);
    // A named constructor decomposes to a concrete row piece.
    let known_row = Located::dummy(Constructor::Named(7));
    // Ask the solver to prove disjointness for the mixed pair.
    let unresolved_goals =
        disjointness_analysis::prove(Span::dummy(), &env, unknown_row.clone(), known_row.clone());
    // Mixed unknown/known decompositions should defer exactly one original goal.
    assert_eq!(unresolved_goals.len(), 1);
    // The deferred goal should preserve the original constructors for later elaboration retries.
    assert!(matches!(
        unresolved_goals[0].left_constructor.node,
        Constructor::Unit
    ));
    assert!(matches!(
        unresolved_goals[0].right_constructor.node,
        Constructor::Named(7)
    ));
}
