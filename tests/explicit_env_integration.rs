//! Integration tests for the Explicit Env module.
//! Catches mutants in lift_kind_in_kind, lift_con_in_con, Env methods.

use ur::error_types::Located;
use ur::explicit::environment::{
    lift_con_in_con, lift_kind_in_con, lift_kind_in_kind, Env, EnvError,
};
use ur::explicit::{Constructor, Declaration, Expression, Kind, Signature, SignatureItem};

#[test]
fn lift_kind_in_kind_rel_ge_bound() {
    let k = Located::dummy(Kind::Rel(5));
    let out = lift_kind_in_kind(k, 3);
    assert!(
        matches!(out.node, Kind::Rel(6)),
        "Rel(5) >= bound 3 => Rel(6)"
    );
}

#[test]
fn lift_kind_in_kind_rel_lt_bound() {
    let k = Located::dummy(Kind::Rel(2));
    let out = lift_kind_in_kind(k, 3);
    assert!(
        matches!(out.node, Kind::Rel(2)),
        "Rel(2) < bound 3 => Rel(2) unchanged"
    );
}

#[test]
fn lift_kind_in_kind_arrow_recursive() {
    let k = Located::dummy(Kind::Arrow(
        Box::new(Located::dummy(Kind::Rel(0))),
        Box::new(Located::dummy(Kind::Rel(1))),
    ));
    let out = lift_kind_in_kind(k, 0);
    let Kind::Arrow(k1, k2) = &out.node else {
        panic!("expected Arrow")
    };
    assert!(matches!(k1.as_ref().node, Kind::Rel(1)));
    assert!(matches!(k2.as_ref().node, Kind::Rel(2)));
}

#[test]
fn lift_con_in_con_rel_ge_bound() {
    let c = Located::dummy(Constructor::Rel(4));
    let out = lift_con_in_con(c, 2);
    assert!(
        matches!(out.node, Constructor::Rel(5)),
        "Rel(4) >= bound 2 => Rel(5)"
    );
}

#[test]
fn lift_con_in_con_rel_uses_plus_not_minus() {
    // n+1 not n-1. Rel(3) with bound 1: 3>=1 => Rel(4). Mutant n-1 would give Rel(2).
    let c = Located::dummy(Constructor::Rel(3));
    let out = lift_con_in_con(c, 1);
    assert!(
        matches!(out.node, Constructor::Rel(4)),
        "Rel(3) >= bound 1 => Rel(4)"
    );
}

#[test]
fn lift_con_in_con_rel_lt_bound() {
    let c = Located::dummy(Constructor::Rel(1));
    let out = lift_con_in_con(c, 2);
    assert!(
        matches!(out.node, Constructor::Rel(1)),
        "Rel(1) < bound 2 => Rel(1) unchanged"
    );
}

#[test]
fn lift_kind_in_kind_fun_binds() {
    // Kind::Fun(x, body) uses bound+1 for body. Rel(0) in body stays 0 (bound); Rel(1) => Rel(2).
    let body = Located::dummy(Kind::Rel(1));
    let k = Located::dummy(Kind::Fun("a".into(), Box::new(body)));
    let out = lift_kind_in_kind(k, 0);
    let Kind::Fun(_, body_out) = &out.node else {
        panic!("expected Fun")
    };
    assert!(
        matches!(body_out.as_ref().node, Kind::Rel(2)),
        "Fun binds; Rel(1) in body => Rel(2)"
    );
}

#[test]
fn lift_kind_in_kind_fun_bound_plus_one() {
    // bound+1 (not bound*1). Rel(0) in body with bound 0: new binder, stays 0. Mutant bound*1 would use 0, Rel(0)>=0 => Rel(1).
    let body = Located::dummy(Kind::Rel(0));
    let k = Located::dummy(Kind::Fun("a".into(), Box::new(body)));
    let out = lift_kind_in_kind(k, 0);
    let Kind::Fun(_, body_out) = &out.node else {
        panic!("expected Fun")
    };
    assert!(
        matches!(body_out.as_ref().node, Kind::Rel(0)),
        "Fun body Rel(0) stays 0 (bound+1=1, 0<1)"
    );
}

#[test]
fn lift_con_in_con_abs_binds() {
    // Abs(x, k, body): body is processed with bound+1. Rel(1) in body is free => becomes Rel(2).
    let k = Located::dummy(Kind::Type);
    let body = Located::dummy(Constructor::Rel(1)); // free var before Abs
    let c = Located::dummy(Constructor::Abs("x".into(), Box::new(k), Box::new(body)));
    let out = lift_con_in_con(c, 0);
    let Constructor::Abs(_, _, body_out) = &out.node else {
        panic!("expected Abs")
    };
    assert!(
        matches!(body_out.as_ref().node, Constructor::Rel(2)),
        "Abs binds; Rel(1) in body (free) => Rel(2)"
    );
}

#[test]
fn lift_kind_in_con_tcfun_lifts_kind_param() {
    // TCFun has a kind param. lift_kind_in_con processes it with bound.
    let k = Located::dummy(Kind::Rel(1)); // kind with Rel(1)
    let body = Located::dummy(Constructor::Unit);
    let c = Located::dummy(Constructor::TCFun("a".into(), Box::new(k), Box::new(body)));
    let out = lift_kind_in_con(c, 0);
    let Constructor::TCFun(_, k_out, _) = &out.node else {
        panic!("expected TCFun")
    };
    // Kind::Rel(1) >= bound 0 => Rel(2)
    assert!(matches!(k_out.as_ref().node, Kind::Rel(2)));
}

#[test]
fn lift_kind_in_con_kabs_bound_plus_one_not_star() {
    // bound+1 not bound*1. With bound=1: body gets bound 2. Kind::Rel(1) in body (ref to outer) stays.
    // Mutant bound*1=1 would process body with bound 1, Rel(1)>=1 => Rel(2) (wrong).
    let inner_k = Located::dummy(Kind::Rel(1));
    let body = Located::dummy(Constructor::KApp(
        Box::new(Located::dummy(Constructor::Unit)),
        Box::new(inner_k),
    ));
    let c = Located::dummy(Constructor::KAbs("k".into(), Box::new(body)));
    let out = lift_kind_in_con(c, 1);
    let Constructor::KAbs(_, body_out) = &out.node else {
        panic!("expected KAbs")
    };
    let Constructor::KApp(_, k_out) = &body_out.as_ref().node else {
        panic!("expected KApp in body")
    };
    assert!(
        matches!(k_out.as_ref().node, Kind::Rel(1)),
        "KAbs body with bound 1: Rel(1) stays (bound+1=2)"
    );
}

#[test]
fn lift_kind_in_con_kabs_increments_bound_for_body() {
    // KAbs binds kind; body uses bound+1. Body with Kind::Rel(1) (ref to outer) becomes Rel(2).
    let inner_k = Located::dummy(Kind::Rel(1));
    let body = Located::dummy(Constructor::TCFun(
        "a".into(),
        Box::new(inner_k),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c = Located::dummy(Constructor::KAbs("k".into(), Box::new(body)));
    let out = lift_kind_in_con(c, 0);
    let Constructor::KAbs(_, body_out) = &out.node else {
        panic!("expected KAbs")
    };
    let Constructor::TCFun(_, k_out, _) = &body_out.as_ref().node else {
        panic!("expected TCFun in body")
    };
    assert!(matches!(k_out.as_ref().node, Kind::Rel(2)));
}

#[test]
fn lift_kind_in_con_tkfun_bound_plus_one() {
    // TKFun body uses bound+1. With bound 0, body gets bound 1. Kind::Rel(0) in body stays (0<1).
    // Mutant bound*1=0 would make Rel(0) become Rel(1).
    let inner_k = Located::dummy(Kind::Rel(0));
    let body = Located::dummy(Constructor::TCFun(
        "a".into(),
        Box::new(inner_k),
        Box::new(Located::dummy(Constructor::Unit)),
    ));
    let c = Located::dummy(Constructor::TKFun("k".into(), Box::new(body)));
    let out = lift_kind_in_con(c, 0);
    let Constructor::TKFun(_, body_out) = &out.node else {
        panic!("expected TKFun")
    };
    let Constructor::TCFun(_, k_out, _) = &body_out.as_ref().node else {
        panic!("expected TCFun in body")
    };
    assert!(matches!(k_out.as_ref().node, Kind::Rel(0)));
}

#[test]
fn lift_con_in_con_tcfun_binds() {
    // TCFun binds con. Body uses bound+1. Rel(2) with bound 1 => body bound 2 => Rel(3).
    let k = Located::dummy(Kind::Type);
    let body = Located::dummy(Constructor::Rel(2));
    let c = Located::dummy(Constructor::TCFun("a".into(), Box::new(k), Box::new(body)));
    let out = lift_con_in_con(c, 1);
    let Constructor::TCFun(_, _, body_out) = &out.node else {
        panic!("expected TCFun")
    };
    assert!(matches!(body_out.as_ref().node, Constructor::Rel(3)));
}

#[test]
fn lift_con_in_con_abs_bound_plus_one_not_star() {
    // bound+1 not bound*1. Abs with bound=1: body gets bound 2. Constructor::Rel(1) in body (ref to binder) stays.
    // Mutant bound*1=1 would process body with bound 1, Rel(1)>=1 => Rel(2) (wrong).
    let k = Located::dummy(Kind::Type);
    let body = Located::dummy(Constructor::Rel(1));
    let c = Located::dummy(Constructor::Abs("x".into(), Box::new(k), Box::new(body)));
    let out = lift_con_in_con(c, 1);
    let Constructor::Abs(_, _, body_out) = &out.node else {
        panic!("expected Abs")
    };
    assert!(
        matches!(body_out.as_ref().node, Constructor::Rel(1)),
        "Abs body with bound 1: Rel(1) stays (bound+1=2)"
    );
}

#[test]
fn lift_con_in_con_tcfun_bound_plus_one() {
    // bound+1 not bound-1. bound 1 => body bound 2. Rel(1) in body: 1<2 stays. Mutant bound-1=0: Rel(1)>=0 => Rel(2).
    let k = Located::dummy(Kind::Type);
    let body = Located::dummy(Constructor::Rel(1));
    let c = Located::dummy(Constructor::TCFun("a".into(), Box::new(k), Box::new(body)));
    let out = lift_con_in_con(c, 1);
    let Constructor::TCFun(_, _, body_out) = &out.node else {
        panic!("expected TCFun")
    };
    assert!(matches!(body_out.as_ref().node, Constructor::Rel(1)));
}

#[test]
fn lift_con_in_con_kabs_does_not_increment_bound() {
    // KAbs binds kind, not con. Body uses same bound.
    let body = Located::dummy(Constructor::Rel(1));
    let c = Located::dummy(Constructor::KAbs("k".into(), Box::new(body)));
    let out = lift_con_in_con(c, 0);
    let Constructor::KAbs(_, body_out) = &out.node else {
        panic!("expected KAbs")
    };
    // Rel(1) >= bound 0 => Rel(2)
    assert!(matches!(body_out.as_ref().node, Constructor::Rel(2)));
}

#[test]
fn env_error_display() {
    let e = EnvError::UnboundRel(42);
    let s = format!("{}", e);
    assert!(s.contains("42"));
    assert!(s.contains("unbound"));
}

#[test]
fn env_push_k_rel_returns_new_env() {
    let env = Env::new();
    let env2 = env.push_k_rel("a".into());
    assert_ne!(std::ptr::addr_of!(env), std::ptr::addr_of!(env2));
    assert_eq!(env2.rel_k.len(), 1);
    assert_eq!(env2.rel_k[0], "a");
}

#[test]
fn env_lookup_k_rel() {
    let env = Env::new().push_k_rel("x".into()).push_k_rel("y".into());
    assert_eq!(env.lookup_k_rel(0).unwrap(), "y");
    assert_eq!(env.lookup_k_rel(1).unwrap(), "x");
    assert!(matches!(env.lookup_k_rel(2), Err(EnvError::UnboundRel(2))));
}

#[test]
fn env_push_c_rel_returns_new_env() {
    let k = Located::dummy(Kind::Type);
    let env = Env::new();
    let env2 = env.push_c_rel("a".into(), k);
    assert_eq!(env2.rel_c.len(), 1);
}

#[test]
fn env_push_c_named() {
    let mut env = Env::new();
    let k = Located::dummy(Kind::Type);
    env.push_c_named("T".into(), 10, k, None);
    let (name, _, _) = env.lookup_c_named(10).unwrap();
    assert_eq!(name, "T");
}

#[test]
fn env_push_e_rel() {
    let mut env = Env::new();
    let t = Located::dummy(Constructor::Unit);
    env.push_e_rel("x".into(), t);
    let (name, _) = env.lookup_e_rel(0).unwrap();
    assert_eq!(name, "x");
}

#[test]
fn env_push_e_named() {
    let mut env = Env::new();
    let t = Located::dummy(Constructor::Unit);
    env.push_e_named("v".into(), 7, t);
    let (name, _) = env.lookup_e_named(7).unwrap();
    assert_eq!(name, "v");
}

#[test]
fn env_push_sgn_named() {
    let mut env = Env::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    env.push_sgn_named("M".into(), 1, sgn);
    let (name, _) = env.lookup_sgn_named(1).unwrap();
    assert_eq!(name, "M");
}

#[test]
fn env_push_str_named() {
    let mut env = Env::new();
    let sgn = Located::dummy(Signature::Const(vec![]));
    env.push_str_named("S".into(), 2, sgn);
    let (name, _) = env.lookup_str_named(2).unwrap();
    assert_eq!(name, "S");
}

#[test]
fn env_decl_binds_con() {
    let k = Located::dummy(Kind::Type);
    let c = Located::dummy(Constructor::Unit);
    let d = Located::dummy(Declaration::Constructor("T".into(), 99, k, c));
    let mut env = Env::new();
    env.decl_binds(&d);
    let (name, _, _) = env.lookup_c_named(99).unwrap();
    assert_eq!(name, "T");
}

#[test]
fn env_decl_binds_datatype_with_params() {
    // Exercises nxs - i - 1 in decl_binds (line 385); Rel indices in base type
    let dt = ur::explicit::DatatypeDecl {
        name: "T".into(),
        id: 10,
        params: vec!["a".into()],
        constrs: vec![("Mk".into(), 11, None)],
    };
    let d = Located::dummy(Declaration::Datatype(vec![dt]));
    let mut env = Env::new();
    env.decl_binds(&d);
    let (_, t) = env.lookup_e_named(11).unwrap();
    // Type is TCFun("a", Type, App(Named(10), Rel(0))); body must contain Rel(0)
    let Constructor::TCFun(_, _, body) = &t.node else {
        panic!("expected TCFun")
    };
    let Constructor::App(_, arg) = &body.as_ref().node else {
        panic!("expected App")
    };
    assert!(
        matches!(arg.as_ref().node, Constructor::Rel(0)),
        "param ref in App must be Rel(0)"
    );
}

#[test]
fn env_decl_binds_datatype_two_params() {
    // With 2 params, base type is App(App(Named(10), Rel(1)), Rel(0)). Catches nxs-i-1 mutant.
    let dt = ur::explicit::DatatypeDecl {
        name: "T".into(),
        id: 20,
        params: vec!["a".into(), "b".into()],
        constrs: vec![("Mk".into(), 21, None)],
    };
    let d = Located::dummy(Declaration::Datatype(vec![dt]));
    let mut env = Env::new();
    env.decl_binds(&d);
    let (_, t) = env.lookup_e_named(21).unwrap();
    // TCFun("b", ..., TCFun("a", ..., App(App(Named(20), Rel(1)), Rel(0))))
    let Constructor::TCFun(_, _, inner) = &t.node else {
        panic!("expected TCFun")
    };
    let Constructor::TCFun(_, _, body) = &inner.as_ref().node else {
        panic!("expected inner TCFun")
    };
    let Constructor::App(inner_app, arg0) = &body.as_ref().node else {
        panic!("expected App")
    };
    assert!(
        matches!(arg0.as_ref().node, Constructor::Rel(0)),
        "innermost arg must be Rel(0)"
    );
    let Constructor::App(_, arg1) = &inner_app.as_ref().node else {
        panic!("expected outer App")
    };
    assert!(
        matches!(arg1.as_ref().node, Constructor::Rel(1)),
        "outer arg must be Rel(1)"
    );
}

#[test]
fn env_pat_binds_adds_variable() {
    let t = Located::dummy(Constructor::Unit);
    let p = Located::dummy(ur::explicit::Pattern::Var("z".into(), t));
    let mut env = Env::new();
    env.pat_binds(&p);
    let (name, _) = env.lookup_e_rel(0).unwrap();
    assert_eq!(name, "z");
}

#[test]
fn env_decl_binds_val() {
    let t = Located::dummy(Constructor::Unit);
    let e = Located::dummy(Expression::Prim(ur::primitives::Prim::Int(0)));
    let d = Located::dummy(Declaration::Val("x".into(), 5, t, e));
    let mut env = Env::new();
    env.decl_binds(&d);
    let (name, _) = env.lookup_e_named(5).unwrap();
    assert_eq!(name, "x");
}

#[test]
fn env_sgi_binds_con() {
    let k = Located::dummy(Kind::Type);
    let c = Located::dummy(Constructor::Unit);
    let sgi = Located::dummy(SignatureItem::Constructor("C".into(), 8, k, c));
    let mut env = Env::new();
    env.sgi_binds(&sgi);
    let (name, _, _) = env.lookup_c_named(8).unwrap();
    assert_eq!(name, "C");
}

// Phase 5 expanded: lift_con_in_con Record, Concat, Map, Tuple, TCFun; Env push/lookup
#[test]
fn lift_con_in_con_record_recurses() {
    let k = Located::dummy(Kind::Type);
    let rel0 = Located::dummy(Constructor::Rel(0));
    let unit = Located::dummy(Constructor::Unit);
    let rec = Located::dummy(Constructor::Record(Box::new(k), vec![(rel0, unit)]));
    let out = lift_con_in_con(rec, 0);
    match &out.node {
        Constructor::Record(_, pairs) => {
            assert_eq!(pairs.len(), 1);
            assert!(matches!(pairs[0].0.node, Constructor::Rel(1)));
        }
        _ => panic!("expected Record"),
    }
}

#[test]
fn lift_con_in_con_map_unchanged() {
    let k = Located::dummy(Kind::Type);
    let map = Located::dummy(Constructor::Map(Box::new(k.clone()), Box::new(k)));
    let out = lift_con_in_con(map, 0);
    assert!(matches!(out.node, Constructor::Map(_, _)));
}

#[test]
fn lift_con_in_con_app_recurses() {
    let n = Located::dummy(Constructor::Named(1));
    let rel0 = Located::dummy(Constructor::Rel(0));
    let app = Located::dummy(Constructor::App(Box::new(n), Box::new(rel0)));
    let out = lift_con_in_con(app, 0);
    match &out.node {
        Constructor::App(_, arg) => assert!(matches!(arg.node, Constructor::Rel(1))),
        _ => panic!("expected App"),
    }
}

#[test]
fn lift_con_in_con_proj_recurses() {
    let rel0 = Located::dummy(Constructor::Rel(0));
    let tup = Located::dummy(Constructor::Tuple(vec![rel0]));
    let proj = Located::dummy(Constructor::Proj(Box::new(tup), 1));
    let out = lift_con_in_con(proj, 0);
    match &out.node {
        Constructor::Proj(inner, n) => {
            assert_eq!(*n, 1);
            if let Constructor::Tuple(cs) = &inner.node {
                assert!(matches!(cs[0].node, Constructor::Rel(1)))
            }
        }
        _ => panic!("expected Proj"),
    }
}

#[test]
fn lift_kind_in_kind_record_recurses() {
    let rel1 = Located::dummy(Kind::Rel(1));
    let k = Located::dummy(Kind::Record(Box::new(rel1)));
    let out = lift_kind_in_kind(k, 0);
    match &out.node {
        Kind::Record(inner) => assert!(matches!(inner.node, Kind::Rel(2))),
        _ => panic!("expected Record"),
    }
}

#[test]
fn lift_kind_in_kind_tuple_recurses() {
    let rel1 = Located::dummy(Kind::Rel(1));
    let k = Located::dummy(Kind::Tuple(vec![rel1]));
    let out = lift_kind_in_kind(k, 0);
    match &out.node {
        Kind::Tuple(ks) => assert!(matches!(ks[0].node, Kind::Rel(2))),
        _ => panic!("expected Tuple"),
    }
}

#[test]
fn env_push_c_rel_then_lookup() {
    let k = Located::dummy(Kind::Type);
    let mut env = Env::new();
    env = env.push_c_rel("a".into(), k);
    let (name, _) = env.lookup_c_rel(0).unwrap();
    assert_eq!(name, "a");
}

#[test]
fn env_push_e_rel_then_lookup() {
    let t = Located::dummy(Constructor::Unit);
    let mut env = Env::new();
    env.push_e_rel("x".into(), t);
    let (name, _) = env.lookup_e_rel(0).unwrap();
    assert_eq!(name, "x");
}
