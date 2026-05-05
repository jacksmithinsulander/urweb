//! Environment for the Expl (explicit elaboration) IR.
//!
//! Mirrors `expl_env.sml`.

use std::collections::HashMap;

use crate::error_types::Located;
use crate::explicit::*;

// ---------------------------------------------------------------------------
// Lifting utilities
// ---------------------------------------------------------------------------

/// Lift kind de Bruijn indices ≥ `bound` by 1 within a kind.
pub fn lift_kind_in_kind(k: LocatedKind, bound: usize) -> LocatedKind {
    let span = k.span.clone();
    let node = match k.node {
        Kind::Rel(n) => {
            if n >= bound {
                Kind::Rel(n + 1)
            } else {
                Kind::Rel(n)
            }
        }
        Kind::Arrow(k1, k2) => Kind::Arrow(
            Box::new(lift_kind_in_kind(*k1, bound)),
            Box::new(lift_kind_in_kind(*k2, bound)),
        ),
        Kind::Record(inner) => Kind::Record(Box::new(lift_kind_in_kind(*inner, bound))),
        Kind::Tuple(ks) => Kind::Tuple(
            ks.into_iter()
                .map(|ki| lift_kind_in_kind(ki, bound))
                .collect(),
        ),
        Kind::Fun(x, body) => Kind::Fun(x, Box::new(lift_kind_in_kind(*body, bound + 1))),
        other => other,
    };
    Located::new(node, span)
}

/// Lift kind de Bruijn indices ≥ `bound` by 1 within a constructor.
/// The constructor-level binder counter is NOT affected; only kind binders
/// (KAbs / TKFun) increment the bound.
pub fn lift_kind_in_con(c: LocatedConstructor, bound: usize) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::Rel(_)
        | Constructor::Named(_)
        | Constructor::ModProj(_, _, _)
        | Constructor::Name(_)
        | Constructor::Unit => c.node,
        Constructor::TFun(c1, c2) => Constructor::TFun(
            Box::new(lift_kind_in_con(*c1, bound)),
            Box::new(lift_kind_in_con(*c2, bound)),
        ),
        Constructor::TCFun(x, k, body) => Constructor::TCFun(
            x,
            Box::new(lift_kind_in_kind(*k, bound)),
            Box::new(lift_kind_in_con(*body, bound)), // TCFun binds a con, not a kind
        ),
        Constructor::TRecord(c) => Constructor::TRecord(Box::new(lift_kind_in_con(*c, bound))),
        Constructor::App(c1, c2) => Constructor::App(
            Box::new(lift_kind_in_con(*c1, bound)),
            Box::new(lift_kind_in_con(*c2, bound)),
        ),
        Constructor::Abs(x, k, body) => Constructor::Abs(
            x,
            Box::new(lift_kind_in_kind(*k, bound)),
            Box::new(lift_kind_in_con(*body, bound)), // Abs binds a con, not a kind
        ),
        Constructor::KAbs(x, body) => {
            // KAbs binds a kind variable — increment bound in body
            Constructor::KAbs(x, Box::new(lift_kind_in_con(*body, bound + 1)))
        }
        Constructor::KApp(c, k) => Constructor::KApp(
            Box::new(lift_kind_in_con(*c, bound)),
            Box::new(lift_kind_in_kind(*k, bound)),
        ),
        Constructor::TKFun(x, body) => {
            // TKFun binds a kind variable — increment bound in body
            Constructor::TKFun(x, Box::new(lift_kind_in_con(*body, bound + 1)))
        }
        Constructor::Record(k, pairs) => Constructor::Record(
            Box::new(lift_kind_in_kind(*k, bound)),
            pairs
                .into_iter()
                .map(|(n, v)| (lift_kind_in_con(n, bound), lift_kind_in_con(v, bound)))
                .collect(),
        ),
        Constructor::Concat(c1, c2) => Constructor::Concat(
            Box::new(lift_kind_in_con(*c1, bound)),
            Box::new(lift_kind_in_con(*c2, bound)),
        ),
        Constructor::Map(k1, k2) => Constructor::Map(
            Box::new(lift_kind_in_kind(*k1, bound)),
            Box::new(lift_kind_in_kind(*k2, bound)),
        ),
        Constructor::Tuple(cs) => {
            Constructor::Tuple(cs.into_iter().map(|c| lift_kind_in_con(c, bound)).collect())
        }
        Constructor::Proj(c, n) => Constructor::Proj(Box::new(lift_kind_in_con(*c, bound)), n),
        // Lift kind indices in each arm's argument constructors; tag names are not constructors.
        Constructor::Enum(arms) => Constructor::Enum(
            arms.into_iter()
                .map(|(tag_name, arg_constructors)| {
                    // Lift kind indices in every argument constructor for this arm.
                    let lifted_args = arg_constructors
                        .into_iter()
                        .map(|arg_constructor| lift_kind_in_con(arg_constructor, bound))
                        .collect();
                    (tag_name, lifted_args)
                })
                .collect(),
        ),
    };
    Located::new(node, span)
}

/// Lift constructor de Bruijn indices ≥ `bound` by 1 within a constructor.
/// Only constructor binders (Abs / TCFun) increment the bound.
pub fn lift_con_in_con(c: LocatedConstructor, bound: usize) -> LocatedConstructor {
    let span = c.span.clone();
    let node = match c.node {
        Constructor::Rel(n) => {
            if n >= bound {
                Constructor::Rel(n + 1)
            } else {
                Constructor::Rel(n)
            }
        }
        Constructor::Named(_)
        | Constructor::ModProj(_, _, _)
        | Constructor::Name(_)
        | Constructor::Unit => c.node,
        Constructor::TFun(c1, c2) => Constructor::TFun(
            Box::new(lift_con_in_con(*c1, bound)),
            Box::new(lift_con_in_con(*c2, bound)),
        ),
        Constructor::TCFun(x, k, body) => Constructor::TCFun(
            x,
            k,
            Box::new(lift_con_in_con(*body, bound + 1)), // binds a con
        ),
        Constructor::TRecord(c) => Constructor::TRecord(Box::new(lift_con_in_con(*c, bound))),
        Constructor::App(c1, c2) => Constructor::App(
            Box::new(lift_con_in_con(*c1, bound)),
            Box::new(lift_con_in_con(*c2, bound)),
        ),
        Constructor::Abs(x, k, body) => Constructor::Abs(
            x,
            k,
            Box::new(lift_con_in_con(*body, bound + 1)), // binds a con
        ),
        Constructor::KAbs(x, body) => {
            // KAbs binds a kind, not a con — bound stays the same
            Constructor::KAbs(x, Box::new(lift_con_in_con(*body, bound)))
        }
        Constructor::KApp(c, k) => Constructor::KApp(Box::new(lift_con_in_con(*c, bound)), k),
        Constructor::TKFun(x, body) => {
            // TKFun binds a kind, not a con — bound stays the same
            Constructor::TKFun(x, Box::new(lift_con_in_con(*body, bound)))
        }
        Constructor::Record(k, pairs) => Constructor::Record(
            k,
            pairs
                .into_iter()
                .map(|(n, v)| (lift_con_in_con(n, bound), lift_con_in_con(v, bound)))
                .collect(),
        ),
        Constructor::Concat(c1, c2) => Constructor::Concat(
            Box::new(lift_con_in_con(*c1, bound)),
            Box::new(lift_con_in_con(*c2, bound)),
        ),
        Constructor::Map(k1, k2) => Constructor::Map(k1, k2),
        Constructor::Tuple(cs) => {
            Constructor::Tuple(cs.into_iter().map(|c| lift_con_in_con(c, bound)).collect())
        }
        Constructor::Proj(c, n) => Constructor::Proj(Box::new(lift_con_in_con(*c, bound)), n),
        // Lift constructor indices in each arm's argument constructors; tag names are not constructors.
        Constructor::Enum(arms) => Constructor::Enum(
            arms.into_iter()
                .map(|(tag_name, arg_constructors)| {
                    // Lift constructor indices in every argument constructor for this arm.
                    let lifted_args = arg_constructors
                        .into_iter()
                        .map(|arg_constructor| lift_con_in_con(arg_constructor, bound))
                        .collect();
                    (tag_name, lifted_args)
                })
                .collect(),
        ),
    };
    Located::new(node, span)
}

/// Lift constructor indices by 1 from index 0 (i.e., past a new outermost binder).
pub fn lift(c: LocatedConstructor) -> LocatedConstructor {
    lift_con_in_con(c, 0)
}

// ---------------------------------------------------------------------------
// Lookup errors
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum EnvError {
    UnboundRel(usize),
    UnboundNamed(usize),
}

impl std::fmt::Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::UnboundRel(n) => write!(f, "unbound relative variable #{}", n),
            EnvError::UnboundNamed(n) => write!(f, "unbound named identifier #{}", n),
        }
    }
}

// ---------------------------------------------------------------------------
// Environment
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct Env {
    /// Stack of kind-level de Bruijn variables (most recent at front).
    pub rel_k: Vec<String>,

    /// Stack of con-level de Bruijn variables (most recent at front).
    pub rel_c: Vec<(String, LocatedKind)>,
    /// Named constructors: id → (name, kind, optional definition).
    pub named_c: HashMap<usize, (String, LocatedKind, Option<LocatedConstructor>)>,

    /// Stack of expression-level de Bruijn variables (most recent at front).
    pub rel_e: Vec<(String, LocatedConstructor)>,
    /// Named expressions: id → (name, type).
    pub named_e: HashMap<usize, (String, LocatedConstructor)>,

    /// Named signatures: id → (name, signature).
    pub sgn: HashMap<usize, (String, LocatedSignature)>,

    /// Named structures: id → (name, signature).
    pub str_map: HashMap<usize, (String, LocatedSignature)>,
}

impl Env {
    pub fn new() -> Self {
        Env {
            rel_k: Vec::new(),
            rel_c: Vec::new(),
            named_c: HashMap::new(),
            rel_e: Vec::new(),
            named_e: HashMap::new(),
            sgn: HashMap::new(),
            str_map: HashMap::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Kind variables
    // -----------------------------------------------------------------------

    /// Push a new kind-level variable, lifting existing kind annotations.
    pub fn push_k_rel(&self, x: String) -> Self {
        let mut env = self.clone();
        env.rel_k.insert(0, x);
        // Lift kind indices in existing constructor variables
        env.rel_c = env
            .rel_c
            .into_iter()
            .map(|(name, k)| (name, lift_kind_in_kind(k, 0)))
            .collect();
        // Lift kind indices in existing expression types
        env.rel_e = env
            .rel_e
            .into_iter()
            .map(|(name, c)| (name, lift_kind_in_con(c, 0)))
            .collect();
        env
    }

    pub fn lookup_k_rel(&self, n: usize) -> Result<&str, EnvError> {
        self.rel_k
            .get(n)
            .map(|s| s.as_str())
            .ok_or(EnvError::UnboundRel(n))
    }

    // -----------------------------------------------------------------------
    // Constructor variables
    // -----------------------------------------------------------------------

    /// Push a new con-level variable, lifting existing con refs by 1.
    pub fn push_c_rel(&self, x: String, k: LocatedKind) -> Self {
        let mut env = self.clone();
        env.rel_c.insert(0, (x, k));
        // Lift con indices in named constructors' optional definitions
        env.named_c = env
            .named_c
            .into_iter()
            .map(|(id, (name, k2, co))| (id, (name, k2, co.map(lift))))
            .collect();
        // Lift con indices in existing expression types
        env.rel_e = env
            .rel_e
            .into_iter()
            .map(|(name, c)| (name, lift(c)))
            .collect();
        // Lift con indices in named expression types
        env.named_e = env
            .named_e
            .into_iter()
            .map(|(id, (name, c))| (id, (name, lift(c))))
            .collect();
        env
    }

    pub fn lookup_c_rel(&self, n: usize) -> Result<&(String, LocatedKind), EnvError> {
        self.rel_c.get(n).ok_or(EnvError::UnboundRel(n))
    }

    /// Add a named constructor.
    pub fn push_c_named(
        &mut self,
        x: String,
        n: usize,
        k: LocatedKind,
        co: Option<LocatedConstructor>,
    ) {
        self.named_c.insert(n, (x, k, co));
    }

    pub fn lookup_c_named(
        &self,
        n: usize,
    ) -> Result<&(String, LocatedKind, Option<LocatedConstructor>), EnvError> {
        self.named_c.get(&n).ok_or(EnvError::UnboundNamed(n))
    }

    // -----------------------------------------------------------------------
    // Expression variables
    // -----------------------------------------------------------------------

    pub fn push_e_rel(&mut self, x: String, t: LocatedConstructor) {
        self.rel_e.insert(0, (x, t));
    }

    pub fn lookup_e_rel(&self, n: usize) -> Result<&(String, LocatedConstructor), EnvError> {
        self.rel_e.get(n).ok_or(EnvError::UnboundRel(n))
    }

    pub fn push_e_named(&mut self, x: String, n: usize, t: LocatedConstructor) {
        self.named_e.insert(n, (x, t));
    }

    pub fn lookup_e_named(&self, n: usize) -> Result<&(String, LocatedConstructor), EnvError> {
        self.named_e.get(&n).ok_or(EnvError::UnboundNamed(n))
    }

    // -----------------------------------------------------------------------
    // Signatures
    // -----------------------------------------------------------------------

    pub fn push_sgn_named(&mut self, x: String, n: usize, s: LocatedSignature) {
        self.sgn.insert(n, (x, s));
    }

    pub fn lookup_sgn_named(&self, n: usize) -> Result<&(String, LocatedSignature), EnvError> {
        self.sgn.get(&n).ok_or(EnvError::UnboundNamed(n))
    }

    // -----------------------------------------------------------------------
    // Structures
    // -----------------------------------------------------------------------

    pub fn push_str_named(&mut self, x: String, n: usize, s: LocatedSignature) {
        self.str_map.insert(n, (x, s));
    }

    pub fn lookup_str_named(&self, n: usize) -> Result<&(String, LocatedSignature), EnvError> {
        self.str_map.get(&n).ok_or(EnvError::UnboundNamed(n))
    }

    // -----------------------------------------------------------------------
    // Bind all names introduced by a declaration
    // -----------------------------------------------------------------------

    pub fn decl_binds(&mut self, d: &LocatedDeclaration) {
        let loc = d.span.clone();
        let k_type = Located::new(Kind::Type, loc.clone());

        match &d.node {
            Declaration::Constructor(x, n, k, c) => {
                self.push_c_named(x.clone(), *n, k.clone(), Some(c.clone()));
            }
            Declaration::Datatype(dts) => {
                for dt in dts {
                    let nxs = dt.params.len();
                    // Build the kind: KType -> KType -> ... -> KType (nxs arrows)
                    let mut kb = k_type.clone();
                    for _ in &dt.params {
                        kb = Located::new(
                            Kind::Arrow(Box::new(k_type.clone()), Box::new(kb)),
                            loc.clone(),
                        );
                    }
                    self.push_c_named(dt.name.clone(), dt.id, kb, None);

                    // Build the base type: (CNamed n) applied to CRel(nxs-1) ... CRel(0)
                    let mut tb: LocatedConstructor =
                        Located::new(Constructor::Named(dt.id), loc.clone());
                    for i in 0..nxs {
                        tb = Located::new(
                            Constructor::App(
                                Box::new(tb),
                                Box::new(Located::new(Constructor::Rel(nxs - i - 1), loc.clone())),
                            ),
                            loc.clone(),
                        );
                    }

                    for (x2, n2, to) in &dt.constrs {
                        // t = case to of NONE => tb | SOME t => TFun(t, tb)
                        let t_body = match to {
                            None => tb.clone(),
                            Some(arg) => Located::new(
                                Constructor::TFun(Box::new(arg.clone()), Box::new(tb.clone())),
                                loc.clone(),
                            ),
                        };
                        // Wrap in TCFun for each type parameter
                        let t = dt.params.iter().rev().fold(t_body, |t_acc, p| {
                            Located::new(
                                Constructor::TCFun(
                                    p.clone(),
                                    Box::new(k_type.clone()),
                                    Box::new(t_acc),
                                ),
                                loc.clone(),
                            )
                        });
                        self.push_e_named(x2.clone(), *n2, t);
                    }
                }
            }
            Declaration::DatatypeImp {
                name,
                id,
                orig_mod,
                orig_path,
                orig_name,
                orig_constrs_path: _,
                constrs,
            } => {
                let t = Located::new(
                    Constructor::ModProj(*orig_mod, orig_path.clone(), orig_name.clone()),
                    loc.clone(),
                );
                self.push_c_named(name.clone(), *id, k_type.clone(), Some(t));

                let tb: LocatedConstructor = Located::new(Constructor::Named(*id), loc.clone());
                for (x2, n2, to) in constrs {
                    let t = match to {
                        None => tb.clone(),
                        Some(arg) => Located::new(
                            Constructor::TFun(Box::new(arg.clone()), Box::new(tb.clone())),
                            loc.clone(),
                        ),
                    };
                    self.push_e_named(x2.clone(), *n2, t);
                }
            }
            Declaration::Val(x, n, t, _) => {
                self.push_e_named(x.clone(), *n, t.clone());
            }
            Declaration::ValRec(vis) => {
                for (x, n, t, _) in vis {
                    self.push_e_named(x.clone(), *n, t.clone());
                }
            }
            Declaration::Signature(x, n, s) => {
                self.push_sgn_named(x.clone(), *n, s.clone());
            }
            Declaration::Structure(x, n, sgn, _) => {
                self.push_str_named(x.clone(), *n, sgn.clone());
            }
            Declaration::FfiStr(x, n, sgn) => {
                self.push_str_named(x.clone(), *n, sgn.clone());
            }
            Declaration::Export(_, _, _) => {}
            Declaration::Table {
                mod_id,
                name,
                name_id,
                con,
                pk_con,
                unique_con,
                ..
            } => {
                let ct = Located::new(
                    Constructor::ModProj(*mod_id, vec![], "sql_table".to_string()),
                    loc.clone(),
                );
                let ct = Located::new(
                    Constructor::App(Box::new(ct), Box::new(con.clone())),
                    loc.clone(),
                );
                let pcu = Located::new(
                    Constructor::Concat(Box::new(pk_con.clone()), Box::new(unique_con.clone())),
                    loc.clone(),
                );
                let ct = Located::new(Constructor::App(Box::new(ct), Box::new(pcu)), loc.clone());
                self.push_e_named(name.clone(), *name_id, ct);
            }
            Declaration::Sequence(mod_id, x, n) => {
                let t = Located::new(
                    Constructor::ModProj(*mod_id, vec![], "sql_sequence".to_string()),
                    loc.clone(),
                );
                self.push_e_named(x.clone(), *n, t);
            }
            Declaration::View(mod_id, x, n, _, c) => {
                let ct = Located::new(
                    Constructor::ModProj(*mod_id, vec![], "sql_view".to_string()),
                    loc.clone(),
                );
                let ct = Located::new(
                    Constructor::App(Box::new(ct), Box::new(c.clone())),
                    loc.clone(),
                );
                self.push_e_named(x.clone(), *n, ct);
            }
            Declaration::Index(_, _) => {}
            Declaration::Database(_) => {}
            Declaration::Cookie(mod_id, x, n, c) => {
                let base = Located::new(
                    Constructor::ModProj(*mod_id, vec![], "http_cookie".to_string()),
                    loc.clone(),
                );
                let t = Located::new(
                    Constructor::App(Box::new(base), Box::new(c.clone())),
                    loc.clone(),
                );
                self.push_e_named(x.clone(), *n, t);
            }
            Declaration::Style(mod_id, x, n) => {
                let t = Located::new(
                    Constructor::ModProj(*mod_id, vec![], "css_class".to_string()),
                    loc.clone(),
                );
                self.push_e_named(x.clone(), *n, t);
            }
            Declaration::Task(_, _) => {}
            Declaration::Policy(_) => {}
            Declaration::OnError(_, _, _) => {}
            Declaration::Ffi(x, n, _, t) => {
                self.push_e_named(x.clone(), *n, t.clone());
            }
        }
    }

    // -----------------------------------------------------------------------
    // Bind all names from a signature item
    // -----------------------------------------------------------------------

    pub fn sgi_binds(&mut self, sgi: &LocatedSignatureItem) {
        let loc = sgi.span.clone();
        let k_type = Located::new(Kind::Type, loc.clone());

        match &sgi.node {
            SignatureItem::ConAbs(x, n, k) => {
                self.push_c_named(x.clone(), *n, k.clone(), None);
            }
            SignatureItem::Constructor(x, n, k, c) => {
                self.push_c_named(x.clone(), *n, k.clone(), Some(c.clone()));
            }
            SignatureItem::Datatype(dts) => {
                for dt in dts {
                    // Build kind: KType -> ... -> KType (dt.params.len() arrows)
                    let mut k = k_type.clone();
                    for _ in &dt.params {
                        k = Located::new(
                            Kind::Arrow(Box::new(k_type.clone()), Box::new(k)),
                            loc.clone(),
                        );
                    }
                    self.push_c_named(dt.name.clone(), dt.id, k, None);

                    let tb: LocatedConstructor =
                        Located::new(Constructor::Named(dt.id), loc.clone());
                    for (x2, n2, to) in &dt.constrs {
                        let t_body = match to {
                            None => tb.clone(),
                            Some(arg) => Located::new(
                                Constructor::TFun(Box::new(arg.clone()), Box::new(tb.clone())),
                                loc.clone(),
                            ),
                        };
                        let t = dt.params.iter().rev().fold(t_body, |acc, p| {
                            Located::new(
                                Constructor::TCFun(
                                    p.clone(),
                                    Box::new(k_type.clone()),
                                    Box::new(acc),
                                ),
                                loc.clone(),
                            )
                        });
                        self.push_e_named(x2.clone(), *n2, t);
                    }
                }
            }
            SignatureItem::DatatypeImp {
                name,
                id,
                orig_mod,
                orig_path,
                orig_name,
                orig_constrs_path: _,
                constrs,
            } => {
                let t = Located::new(
                    Constructor::ModProj(*orig_mod, orig_path.clone(), orig_name.clone()),
                    loc.clone(),
                );
                self.push_c_named(name.clone(), *id, k_type.clone(), Some(t));

                let tb: LocatedConstructor = Located::new(Constructor::Named(*id), loc.clone());
                for (x2, n2, to) in constrs {
                    let t = match to {
                        None => tb.clone(),
                        Some(arg) => Located::new(
                            Constructor::TFun(Box::new(arg.clone()), Box::new(tb.clone())),
                            loc.clone(),
                        ),
                    };
                    self.push_e_named(x2.clone(), *n2, t);
                }
            }
            SignatureItem::Val(x, n, t) => {
                self.push_e_named(x.clone(), *n, t.clone());
            }
            SignatureItem::Signature(x, n, s) => {
                self.push_sgn_named(x.clone(), *n, s.clone());
            }
            SignatureItem::Structure(x, n, s) => {
                self.push_str_named(x.clone(), *n, s.clone());
            }
        }
    }

    // -----------------------------------------------------------------------
    // Bind all names from a pattern (expression variables)
    // -----------------------------------------------------------------------

    pub fn pat_binds(&mut self, p: &LocatedPattern) {
        match &p.node {
            Pattern::Var(x, t) => self.push_e_rel(x.clone(), t.clone()),
            Pattern::Prim(_) => {}
            Pattern::Constructor(_, _, _, None) => {}
            Pattern::Constructor(_, _, _, Some(sub)) => self.pat_binds(sub),
            Pattern::Record(fields) => {
                for (_, sub_p, _) in fields {
                    self.pat_binds(sub_p);
                }
            }
        }
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::new()
    }
}
