//! Environment for the Core AST — name resolution after elaboration.
//!
//! Provides a lookup environment for Core's named constructors, expressions,
//! and datatypes. Used when transforming or type-checking Core code. All
//! bindings keyed by globally-unique `usize` ids.
//!
//! - **Env**: push_c_named_as, lookup_c_named, push_e_named_as, lookup_e_named,
//!   push_datatype, lookup_datatype, lookup_constructor, decl_binds, bind_file
//! - **pat_binds_n**: count variables bound by a pattern
//! - **pat_binds_list**: collect (name, type) pairs from a pattern
//!
//! Mirrors `core_env.sml`.
//!
//! Core uses only *named* (globally-unique integer) bindings after elaboration.
//! There are no relative (de Bruijn) bindings in the public interface here,
//! unlike the Elab environment which also tracks relative bindings for
//! class resolution and implicit arguments.

use std::collections::HashMap;

use crate::core::*;
use crate::datatype_kind::DatatypeKind;

use super::utilities::classify_datatype;

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// Errors that can arise when looking up an identifier in the environment.
#[derive(Debug, Clone)]
pub enum EnvError {
    /// No constructor with the given id is in scope.
    UnboundNamedC(usize),
    /// No expression with the given id is in scope.
    UnboundNamedE(usize),
    /// No datatype with the given id is in scope.
    UnboundDatatype(usize),
}

impl std::fmt::Display for EnvError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnvError::UnboundNamedC(n) => write!(f, "unbound named constructor: {n}"),
            EnvError::UnboundNamedE(n) => write!(f, "unbound named expression: {n}"),
            EnvError::UnboundDatatype(n) => write!(f, "unbound datatype: {n}"),
        }
    }
}

impl std::error::Error for EnvError {}

// ---------------------------------------------------------------------------
// Env
// ---------------------------------------------------------------------------

/// The Core elaboration environment.
///
/// All bindings use globally-unique integer names (`usize` ids).
/// Constructor variables that still use de Bruijn indices (e.g. from
/// `CAbs` / `KAbs`) are handled transparently by callers — this struct
/// only tracks named entries.
#[derive(Debug, Clone)]
pub struct Env {
    /// Named constructors: id → (name, kind, optional definition).
    pub named_c: HashMap<usize, (String, LocatedKind, Option<LocatedConstructor>)>,

    /// Named expressions: id → (name, type).
    pub named_e: HashMap<usize, (String, LocatedConstructor)>,

    /// Datatypes: datatype_id → (type_params, constructors).
    ///
    /// Constructors are stored as `(constr_name, constr_id, optional_arg_type)`.
    pub datatypes: HashMap<
        usize,
        (
            Vec<String>,
            Vec<(String, usize, Option<LocatedConstructor>)>,
        ),
    >,

    /// Constructor lookup by name:
    /// constr_name → (DatatypeKind, datatype_id, type_params, optional_arg_type, constr_id).
    pub constructors: HashMap<
        String,
        (
            DatatypeKind,
            usize,
            Vec<String>,
            Option<LocatedConstructor>,
            usize,
        ),
    >,
}

impl Env {
    // -----------------------------------------------------------------------
    // Construction
    // -----------------------------------------------------------------------

    /// Create an empty environment.
    pub fn empty() -> Self {
        Env {
            named_c: HashMap::new(),
            named_e: HashMap::new(),
            datatypes: HashMap::new(),
            constructors: HashMap::new(),
        }
    }

    // -----------------------------------------------------------------------
    // Named constructor bindings
    // -----------------------------------------------------------------------

    /// Add a named constructor binding.
    ///
    /// Mirrors `pushCNamed` in `core_env.sml`.
    pub fn push_c_named_as(
        mut self,
        name: String,
        id: usize,
        kind: LocatedKind,
        optional_definition: Option<LocatedConstructor>,
    ) -> Self {
        self.named_c.insert(id, (name, kind, optional_definition));
        self
    }

    /// Look up a named constructor by id.
    ///
    /// Returns `(name, kind, optional_definition)`.
    ///
    /// Mirrors `lookupCNamed` in `core_env.sml`.
    pub fn lookup_c_named(
        &self,
        id: usize,
    ) -> Result<&(String, LocatedKind, Option<LocatedConstructor>), EnvError> {
        self.named_c.get(&id).ok_or(EnvError::UnboundNamedC(id))
    }

    // -----------------------------------------------------------------------
    // Named expression bindings
    // -----------------------------------------------------------------------

    /// Add a named expression binding.
    ///
    /// Mirrors `pushENamed` in `core_env.sml`.
    pub fn push_e_named_as(
        mut self,
        name: String,
        id: usize,
        expression_type: LocatedConstructor,
    ) -> Self {
        self.named_e.insert(id, (name, expression_type));
        self
    }

    /// Look up a named expression by id.
    ///
    /// Returns `(name, type)`.
    ///
    /// Mirrors `lookupENamed` in `core_env.sml`.
    pub fn lookup_e_named(&self, id: usize) -> Result<&(String, LocatedConstructor), EnvError> {
        self.named_e.get(&id).ok_or(EnvError::UnboundNamedE(id))
    }

    // -----------------------------------------------------------------------
    // Datatype bindings
    // -----------------------------------------------------------------------

    /// Register a datatype and its constructors.
    ///
    /// Also indexes each constructor by name under `constructors`.
    ///
    /// Mirrors `pushDatatype` in `core_env.sml`.
    pub fn push_datatype(
        mut self,
        datatype_id: usize,
        type_params: Vec<String>,
        constructor_specifications: Vec<(String, usize, Option<LocatedConstructor>)>,
    ) -> Self {
        // Classify the datatype's representation kind.
        let datatype_kind = classify_datatype(&constructor_specifications);

        // Index each constructor by its string name.
        for (constructor_name, constructor_id, argument_type) in &constructor_specifications {
            self.constructors.insert(
                constructor_name.clone(),
                (
                    datatype_kind,
                    datatype_id,
                    type_params.clone(),
                    argument_type.clone(),
                    *constructor_id,
                ),
            );
        }

        self.datatypes
            .insert(datatype_id, (type_params, constructor_specifications));
        self
    }

    /// Look up a datatype by id.
    ///
    /// Returns `(type_params, constructors)`.
    ///
    /// Mirrors `lookupDatatype` in `core_env.sml`.
    pub fn lookup_datatype(
        &self,
        id: usize,
    ) -> Result<
        &(
            Vec<String>,
            Vec<(String, usize, Option<LocatedConstructor>)>,
        ),
        EnvError,
    > {
        self.datatypes.get(&id).ok_or(EnvError::UnboundDatatype(id))
    }

    /// Look up a constructor by its string name.
    ///
    /// Returns `(DatatypeKind, datatype_id, type_params, optional_arg_type, constr_id)`.
    ///
    /// Mirrors `lookupConstructor` in `core_env.sml`.
    pub fn lookup_constructor(
        &self,
        name: &str,
    ) -> Option<&(
        DatatypeKind,
        usize,
        Vec<String>,
        Option<LocatedConstructor>,
        usize,
    )> {
        self.constructors.get(name)
    }

    // -----------------------------------------------------------------------
    // Bulk helpers (mirrors `declBinds` in `core_env.sml`)
    // -----------------------------------------------------------------------

    /// Extend the environment with all the bindings introduced by a declaration.
    ///
    /// Mirrors `declBinds` in `core_env.sml`.
    pub fn decl_binds(self, declaration: &LocatedDeclaration) -> Self {
        match &declaration.node {
            Declaration::Constructor(x, n, k, c) => {
                self.push_c_named_as(x.clone(), *n, k.clone(), Some(c.clone()))
            }
            Declaration::Datatype(dts) => {
                dts.iter().fold(self, |env, dt| {
                    // Kind for the datatype: Type, or (Type -> Type) for one param, etc.
                    let base_k = Located::dummy(Kind::Type);
                    let k = dt.params.iter().rev().fold(base_k.clone(), |acc, _| {
                        Located::new(
                            Kind::Arrow(Box::new(base_k.clone()), Box::new(acc)),
                            declaration.span.clone(),
                        )
                    });

                    let env = env.push_c_named_as(dt.name.clone(), dt.id, k, None);
                    let env = env.push_datatype(dt.id, dt.params.clone(), dt.constrs.clone());

                    // Each constructor is also a value (e.g. Some : option α).
                    let self_type =
                        Located::new(Constructor::Named(dt.id), declaration.span.clone());
                    // Apply type params: Option α = App (Named option_id) (Rel 0)
                    let self_type = dt.params.iter().enumerate().fold(self_type, |acc, (i, _)| {
                        Located::new(
                            Constructor::App(
                                Box::new(acc),
                                Box::new(Located::new(
                                    Constructor::Rel(i),
                                    declaration.span.clone(),
                                )),
                            ),
                            declaration.span.clone(),
                        )
                    });

                    dt.constrs.iter().fold(env, |env, (cname, cid, arg_type)| {
                        // C : arg_type -> T α (or just T α if nullary)
                        let con_type = match arg_type {
                            None => self_type.clone(),
                            Some(t) => Located::new(
                                Constructor::TFun(Box::new(t.clone()), Box::new(self_type.clone())),
                                declaration.span.clone(),
                            ),
                        };
                        // Wrap in TCFun for each param: ∀α. arg_type -> T α
                        let con_type = dt.params.iter().rev().fold(con_type, |acc, param| {
                            Located::new(
                                Constructor::TCFun(
                                    param.clone(),
                                    Box::new(Located::dummy(Kind::Type)),
                                    Box::new(acc),
                                ),
                                declaration.span.clone(),
                            )
                        });
                        env.push_e_named_as(cname.clone(), *cid, con_type)
                    })
                })
            }
            Declaration::Val(x, n, t, _e, _s) => self.push_e_named_as(x.clone(), *n, t.clone()),
            Declaration::ValRec(vis) => vis.iter().fold(self, |env, (x, n, t, _, _)| {
                env.push_e_named_as(x.clone(), *n, t.clone())
            }),
            Declaration::Export(_, _, _) => self,
            Declaration::Table {
                sql_name,
                id,
                con,
                sql_con: _,
                exp: _,
                pk_con,
                pk_exp: _,
                unique_con,
            } => {
                // Table type: Basis.sql_table con (pk ++ unique)
                let ffi_table = Located::new(
                    Constructor::Ffi("Basis".to_string(), "sql_table".to_string()),
                    declaration.span.clone(),
                );
                let concat = Located::new(
                    Constructor::Concat(Box::new(pk_con.clone()), Box::new(unique_con.clone())),
                    declaration.span.clone(),
                );
                let ct = Located::new(
                    Constructor::App(Box::new(ffi_table), Box::new(con.clone())),
                    declaration.span.clone(),
                );
                let ct = Located::new(
                    Constructor::App(Box::new(ct), Box::new(concat)),
                    declaration.span.clone(),
                );
                self.push_e_named_as(sql_name.clone(), *id, ct)
            }
            Declaration::Sequence(x, n, _sql_name) => {
                let t = Located::new(
                    Constructor::Ffi("Basis".to_string(), "sql_sequence".to_string()),
                    declaration.span.clone(),
                );
                self.push_e_named_as(x.clone(), *n, t)
            }
            Declaration::View(x, n, _s, _e, c) => {
                let ffi_view = Located::new(
                    Constructor::Ffi("Basis".to_string(), "sql_view".to_string()),
                    declaration.span.clone(),
                );
                let ct = Located::new(
                    Constructor::App(Box::new(ffi_view), Box::new(c.clone())),
                    declaration.span.clone(),
                );
                self.push_e_named_as(x.clone(), *n, ct)
            }
            Declaration::Index(_, _) => self,
            Declaration::Database(_) => self,
            Declaration::Cookie(x, n, c, _s) => {
                let ffi_cookie = Located::new(
                    Constructor::Ffi("Basis".to_string(), "http_cookie".to_string()),
                    declaration.span.clone(),
                );
                let ct = Located::new(
                    Constructor::App(Box::new(ffi_cookie), Box::new(c.clone())),
                    declaration.span.clone(),
                );
                self.push_e_named_as(x.clone(), *n, ct)
            }
            Declaration::Style(x, n, _s) => {
                let t = Located::new(
                    Constructor::Ffi("Basis".to_string(), "css_class".to_string()),
                    declaration.span.clone(),
                );
                self.push_e_named_as(x.clone(), *n, t)
            }
            Declaration::Task(_, _) => self,
            Declaration::Policy(_) => self,
            Declaration::OnError(_) => self,
        }
    }

    /// Extend the environment with all bindings from an entire file.
    pub fn bind_file(self, ds: &[LocatedDeclaration]) -> Self {
        ds.iter().fold(self, |env, d| env.decl_binds(d))
    }
}

// ---------------------------------------------------------------------------
// Pattern helpers (mirrors `patBinds` / `patBindsN` / `patBindsL`)
// ---------------------------------------------------------------------------

/// Count how many expression variables are bound by a pattern.
///
/// Mirrors `patBindsN` in `core_env.sml`.
pub fn pat_binds_n(pattern: &LocatedPattern) -> usize {
    match &pattern.node {
        Pattern::Var(_, _) => 1,
        Pattern::Prim(_) => 0,
        Pattern::Constructor(_, _, _, None) => 0,
        Pattern::Constructor(_, _, _, Some(sub_pattern)) => pat_binds_n(sub_pattern),
        Pattern::Record(fields) => fields
            .iter()
            .map(|(_, sub_pattern, _)| pat_binds_n(sub_pattern))
            .sum(),
    }
}

/// Collect the list of `(name, type)` pairs bound by a pattern.
///
/// Mirrors `patBindsL` in `core_env.sml`.
pub fn pat_binds_list(pattern: &LocatedPattern) -> Vec<(String, LocatedConstructor)> {
    let mut output = Vec::new();
    collect_pat_binds(pattern, &mut output);
    output
}

fn collect_pat_binds(pattern: &LocatedPattern, output: &mut Vec<(String, LocatedConstructor)>) {
    match &pattern.node {
        Pattern::Var(name, expression_type) => output.push((name.clone(), expression_type.clone())),
        Pattern::Prim(_) => {}                    // No bindings
        Pattern::Constructor(_, _, _, None) => {} // Nullary con binds nothing
        Pattern::Constructor(_, _, _, Some(sub_pattern)) => collect_pat_binds(sub_pattern, output),
        Pattern::Record(fields) => {
            for (_, sub_pattern, _) in fields {
                collect_pat_binds(sub_pattern, output);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::Located;

    #[test]
    fn env_empty_creates_fresh_env() {
        let env = Env::empty();
        assert!(env.named_c.is_empty());
        assert!(env.named_e.is_empty());
        assert!(env.datatypes.is_empty());
        assert!(env.constructors.is_empty());
    }

    /// Catches mutant: EnvError::fmt.
    #[test]
    fn env_error_display() {
        let e = EnvError::UnboundNamedC(42);
        let s = format!("{}", e);
        assert!(s.contains("42"));
        assert!(s.contains("constructor"));
    }

    #[test]
    fn env_push_and_lookup_c_named() {
        let k = Located::dummy(Kind::Type);
        let c = Located::dummy(Constructor::Unit);
        let env = Env::empty().push_c_named_as("T".into(), 1, k.clone(), Some(c.clone()));
        let entry = env.lookup_c_named(1).unwrap();
        assert_eq!(entry.0, "T");
        assert!(matches!(
            env.lookup_c_named(99),
            Err(EnvError::UnboundNamedC(99))
        ));
    }

    #[test]
    fn env_push_and_lookup_e_named() {
        let t = Located::dummy(Constructor::Unit);
        let env = Env::empty().push_e_named_as("x".into(), 42, t.clone());
        let entry = env.lookup_e_named(42).unwrap();
        assert_eq!(entry.0, "x");
        assert!(matches!(
            env.lookup_e_named(99),
            Err(EnvError::UnboundNamedE(99))
        ));
    }

    #[test]
    fn env_push_and_lookup_datatype() {
        let env = Env::empty().push_datatype(
            10,
            vec!["a".into()],
            vec![("C".into(), 11, None), ("D".into(), 12, None)],
        );
        let (params, constrs) = env.lookup_datatype(10).unwrap();
        assert_eq!(params, &["a".to_string()]);
        assert_eq!(constrs.len(), 2);
        assert!(matches!(
            env.lookup_datatype(99),
            Err(EnvError::UnboundDatatype(99))
        ));
    }

    #[test]
    fn env_lookup_constructor_by_name() {
        let env = Env::empty().push_datatype(
            10,
            vec![],
            vec![("Some".into(), 1, Some(Located::dummy(Constructor::Unit)))],
        );
        let info = env.lookup_constructor("Some").unwrap();
        assert_eq!(info.1, 10); // datatype id
        assert_eq!(info.4, 1); // constr id
    }

    #[test]
    fn pat_binds_n_var() {
        let p = Located::dummy(Pattern::Var("x".into(), Located::dummy(Constructor::Unit)));
        assert_eq!(pat_binds_n(&p), 1);
    }

    #[test]
    fn pat_binds_n_prim() {
        let p = Located::dummy(Pattern::Prim(crate::primitives::Prim::Int(0)));
        assert_eq!(pat_binds_n(&p), 0);
    }

    #[test]
    fn pat_binds_list_var() {
        let ty = Located::dummy(Constructor::Unit);
        let p = Located::dummy(Pattern::Var("x".into(), ty.clone()));
        let binds = pat_binds_list(&p);
        assert_eq!(binds.len(), 1);
        assert_eq!(binds[0].0, "x");
    }

    #[test]
    fn pat_binds_list_record() {
        let ty = Located::dummy(Constructor::Unit);
        let p = Located::dummy(Pattern::Record(vec![(
            "f".into(),
            Located::dummy(Pattern::Var("x".into(), ty.clone())),
            ty.clone(),
        )]));
        let binds = pat_binds_list(&p);
        assert_eq!(binds.len(), 1);
        assert_eq!(binds[0].0, "x");
    }
}
