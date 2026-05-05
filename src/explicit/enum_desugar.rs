//! Desugaring pass: anonymous sum types (`Constructor::Enum`) → named datatypes.
//!
//! `Constructor::Enum(arms)` is a source-level anonymous sum introduced by the
//! syntax `[Tag1 | Tag2 of Con1 * Con2]`.  The corify pass (which lowers expl
//! to core) can only handle named `Declaration::Datatype`; it has no case for
//! inline enum constructors.
//!
//! This pass rewrites every `Constructor::Enum` occurrence in the explicit AST
//! by:
//! 1. Allocating a fresh named ID for the anonymous datatype.
//! 2. Allocating a fresh named ID for each constructor arm.
//! 3. Synthesising a `Declaration::Datatype` for the anonymous type and
//!    prepending it before the declaration that contains the `Constructor::Enum`.
//! 4. Replacing `Constructor::Enum(arms)` with `Constructor::Named(fresh_id)`.
//!
//! The pass runs after `explify` and before `corify`.

use crate::elaborated::environment::new_named_id;
use crate::error_types::Located;
use crate::explicit::{
    Constructor, DatatypeDecl, Declaration, File, LocatedConstructor, LocatedDeclaration,
};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Desugar all `Constructor::Enum` nodes in `file`, replacing them with
/// `Constructor::Named` references and prepending fresh `Declaration::Datatype`
/// declarations for each anonymous sum type.
///
/// # Arguments
///
/// * `file` — The explicit AST file to desugar; consumed and rebuilt.
///
/// # Returns
///
/// A new `File` with no `Constructor::Enum` nodes.
pub fn desugar(file: File) -> File {
    // Process each declaration, potentially expanding it into multiple
    // declarations when `Constructor::Enum` nodes are found inside it.
    file.into_iter()
        .flat_map(|located_decl| desugar_declaration(located_decl))
        .collect()
}

// ---------------------------------------------------------------------------
// Declaration-level desugaring
// ---------------------------------------------------------------------------

/// Desugar a single top-level declaration.
///
/// Returns a `Vec` because desugaring an enum inside the declaration may
/// require prepending new `Declaration::Datatype` declarations.
///
/// # Arguments
///
/// * `located_decl` — A single located top-level declaration.
///
/// # Returns
///
/// One or more declarations: any freshly synthesised datatypes followed by
/// the (possibly rewritten) original declaration.
fn desugar_declaration(located_decl: LocatedDeclaration) -> Vec<LocatedDeclaration> {
    let span = located_decl.span.clone();
    let mut emitted_datatypes: Vec<LocatedDeclaration> = Vec::new();

    // Rewrite the declaration node, collecting emitted datatypes via the closure.
    let rewritten_node = desugar_decl_node(located_decl.node, &mut emitted_datatypes);

    // Prepend synthesised datatypes before the rewritten declaration.
    let mut result = emitted_datatypes;
    result.push(Located::new(rewritten_node, span));
    result
}

/// Rewrite the interior of a declaration, mutating `emitted_datatypes` for
/// any `Constructor::Enum` nodes encountered.
///
/// # Arguments
///
/// * `decl_node` — The declaration node to rewrite; consumed.
/// * `emitted_datatypes` — Accumulates fresh `Declaration::Datatype` nodes.
///
/// # Returns
///
/// The rewritten declaration node.
fn desugar_decl_node(
    decl_node: Declaration,
    emitted_datatypes: &mut Vec<LocatedDeclaration>,
) -> Declaration {
    match decl_node {
        Declaration::Constructor(name, id, kind, con) => {
            // Rewrite the constructor expression for the defined name.
            let rewritten_con = rewrite_con(con, emitted_datatypes);
            Declaration::Constructor(name, id, kind, rewritten_con)
        }
        Declaration::Val(name, id, con_type, expression) => {
            // Rewrite the type annotation of the val declaration.
            let rewritten_type = rewrite_con(con_type, emitted_datatypes);
            Declaration::Val(name, id, rewritten_type, expression)
        }
        Declaration::ValRec(bindings) => {
            // Rewrite type annotations for each mutually-recursive binding.
            let rewritten_bindings = bindings
                .into_iter()
                .map(|(name, id, con_type, expression)| {
                    // Rewrite the type annotation; body expressions are not traversed
                    // here as expressions do not carry inline enum types in constructor
                    // position in the explicit AST (types are resolved by elaboration).
                    let rewritten_type = rewrite_con(con_type, emitted_datatypes);
                    (name, id, rewritten_type, expression)
                })
                .collect();
            Declaration::ValRec(rewritten_bindings)
        }
        Declaration::Datatype(datatype_decls) => {
            // Rewrite any `Constructor::Enum` appearing in constructor argument types.
            let rewritten_decls = datatype_decls
                .into_iter()
                .map(|dt| rewrite_datatype_decl(dt, emitted_datatypes))
                .collect();
            Declaration::Datatype(rewritten_decls)
        }
        // All other declaration forms do not carry constructor types at the
        // top level and do not need desugaring.  (Expressions inside
        // declarations are not traversed: the explicit AST does not allow
        // inline enum types inside expressions — they are resolved to
        // Constructor::Named during elaboration.)
        other => other,
    }
}

/// Rewrite a `DatatypeDecl` node, desugaring any `Constructor::Enum` that
/// appears in constructor argument types.
///
/// # Arguments
///
/// * `dt` — The datatype declaration to rewrite; consumed.
/// * `emitted_datatypes` — Accumulates fresh `Declaration::Datatype` nodes.
///
/// # Returns
///
/// The rewritten datatype declaration.
fn rewrite_datatype_decl(
    dt: DatatypeDecl,
    emitted_datatypes: &mut Vec<LocatedDeclaration>,
) -> DatatypeDecl {
    // Rewrite each constructor's optional argument type.
    let rewritten_constrs = dt
        .constrs
        .into_iter()
        .map(|(constr_name, constr_id, opt_arg_type)| {
            let rewritten_opt_arg =
                opt_arg_type.map(|arg_type| rewrite_con(arg_type, emitted_datatypes));
            (constr_name, constr_id, rewritten_opt_arg)
        })
        .collect();
    DatatypeDecl {
        name: dt.name,
        id: dt.id,
        params: dt.params,
        constrs: rewritten_constrs,
    }
}

// ---------------------------------------------------------------------------
// Constructor-level rewriting
// ---------------------------------------------------------------------------

/// Recursively rewrite a constructor, replacing every `Constructor::Enum`
/// with a fresh `Constructor::Named` and emitting a corresponding
/// `Declaration::Datatype`.
///
/// # Arguments
///
/// * `located_con` — The constructor to rewrite; consumed.
/// * `emitted_datatypes` — Accumulates fresh `Declaration::Datatype` nodes.
///
/// # Returns
///
/// The rewritten constructor (no `Constructor::Enum` nodes remain).
fn rewrite_con(
    located_con: LocatedConstructor,
    emitted_datatypes: &mut Vec<LocatedDeclaration>,
) -> LocatedConstructor {
    let span = located_con.span.clone();
    let rewritten_node = rewrite_con_node(located_con.node, emitted_datatypes, &span);
    Located::new(rewritten_node, span)
}

/// Rewrite the interior of a constructor node, bottom-up.
///
/// When a `Constructor::Enum(arms)` is encountered:
///  1. Each arm's argument constructors are first recursively rewritten.
///  2. A fresh `Declaration::Datatype` is synthesised and pushed to
///     `emitted_datatypes`.
///  3. The `Constructor::Enum` is replaced by `Constructor::Named(fresh_id)`.
///
/// # Arguments
///
/// * `con_node` — The constructor node; consumed.
/// * `emitted_datatypes` — Accumulates fresh `Declaration::Datatype` nodes.
/// * `span` — The span of the enclosing `LocatedConstructor`.
///
/// # Returns
///
/// The rewritten constructor node.
fn rewrite_con_node(
    con_node: Constructor,
    emitted_datatypes: &mut Vec<LocatedDeclaration>,
    span: &crate::error_types::Span,
) -> Constructor {
    match con_node {
        // Leaf constructors — no sub-constructors to rewrite.
        Constructor::Rel(_)
        | Constructor::Named(_)
        | Constructor::ModProj(..)
        | Constructor::Name(_)
        | Constructor::Unit => con_node,

        Constructor::TFun(left, right) => {
            let rewritten_left = rewrite_con(*left, emitted_datatypes);
            let rewritten_right = rewrite_con(*right, emitted_datatypes);
            Constructor::TFun(Box::new(rewritten_left), Box::new(rewritten_right))
        }
        Constructor::TCFun(param_name, kind, body) => {
            // Kind carries no constructor-level types; only the body needs rewriting.
            let rewritten_body = rewrite_con(*body, emitted_datatypes);
            Constructor::TCFun(param_name, kind, Box::new(rewritten_body))
        }
        Constructor::TRecord(inner) => {
            let rewritten_inner = rewrite_con(*inner, emitted_datatypes);
            Constructor::TRecord(Box::new(rewritten_inner))
        }
        Constructor::App(left, right) => {
            let rewritten_left = rewrite_con(*left, emitted_datatypes);
            let rewritten_right = rewrite_con(*right, emitted_datatypes);
            Constructor::App(Box::new(rewritten_left), Box::new(rewritten_right))
        }
        Constructor::Abs(param_name, kind, body) => {
            let rewritten_body = rewrite_con(*body, emitted_datatypes);
            Constructor::Abs(param_name, kind, Box::new(rewritten_body))
        }
        Constructor::KAbs(param_name, body) => {
            let rewritten_body = rewrite_con(*body, emitted_datatypes);
            Constructor::KAbs(param_name, Box::new(rewritten_body))
        }
        Constructor::KApp(constructor_part, kind_part) => {
            let rewritten_constructor = rewrite_con(*constructor_part, emitted_datatypes);
            Constructor::KApp(Box::new(rewritten_constructor), kind_part)
        }
        Constructor::TKFun(param_name, body) => {
            let rewritten_body = rewrite_con(*body, emitted_datatypes);
            Constructor::TKFun(param_name, Box::new(rewritten_body))
        }
        Constructor::Record(record_kind, key_value_pairs) => {
            let rewritten_pairs = key_value_pairs
                .into_iter()
                .map(|(key_con, value_con)| {
                    (
                        rewrite_con(key_con, emitted_datatypes),
                        rewrite_con(value_con, emitted_datatypes),
                    )
                })
                .collect();
            Constructor::Record(record_kind, rewritten_pairs)
        }
        Constructor::Concat(left, right) => {
            let rewritten_left = rewrite_con(*left, emitted_datatypes);
            let rewritten_right = rewrite_con(*right, emitted_datatypes);
            Constructor::Concat(Box::new(rewritten_left), Box::new(rewritten_right))
        }
        Constructor::Map(domain_kind, range_kind) => {
            // `Map` carries only kinds, not constructors.
            Constructor::Map(domain_kind, range_kind)
        }
        Constructor::Tuple(constructors) => {
            let rewritten_constructors = constructors
                .into_iter()
                .map(|constructor_item| rewrite_con(constructor_item, emitted_datatypes))
                .collect();
            Constructor::Tuple(rewritten_constructors)
        }
        Constructor::Proj(inner, projection_index) => {
            let rewritten_inner = rewrite_con(*inner, emitted_datatypes);
            Constructor::Proj(Box::new(rewritten_inner), projection_index)
        }

        // The key case: desugar an anonymous sum type.
        Constructor::Enum(arms) => {
            // Allocate a fresh global ID for the synthesised anonymous datatype.
            let datatype_id = new_named_id();

            // Synthesise one named datatype constructor per arm.
            // Multi-argument arms are encoded as a single constructor with a
            // `Constructor::Tuple` argument (matching how the elaborator
            // represents tuples in datatype payloads).
            let synthesised_constrs: Vec<(String, usize, Option<LocatedConstructor>)> = arms
                .into_iter()
                .map(|(arm_tag_name, arm_arg_constructors)| {
                    // Recursively rewrite any nested enums in arm argument types.
                    let rewritten_args: Vec<LocatedConstructor> = arm_arg_constructors
                        .into_iter()
                        .map(|arg_con| rewrite_con(arg_con, emitted_datatypes))
                        .collect();

                    // Build the payload constructor for this arm.
                    let payload_opt = match rewritten_args.len() {
                        // Nullary arm: no payload.
                        0 => None,
                        // Unary arm: payload is the single arg constructor.
                        1 => Some(rewritten_args.into_iter().next().unwrap()),
                        // Multi-argument arm: wrap in a Tuple constructor.
                        _ => {
                            let tuple_span = span.clone();
                            Some(Located::new(Constructor::Tuple(rewritten_args), tuple_span))
                        }
                    };

                    // Allocate a fresh ID for each constructor arm.
                    let constr_id = new_named_id();
                    (arm_tag_name, constr_id, payload_opt)
                })
                .collect();

            // Synthesise the anonymous datatype declaration.
            // No type parameters: anonymous sum types are always monomorphic
            // in their surface form.  (Parameterised anonymous sums require
            // explicit named datatypes in source.)
            let synthesised_dt = DatatypeDecl {
                name: format!("$Anon{}", datatype_id), // Internal name — not user-visible.
                id: datatype_id,
                params: vec![], // Monomorphic; no type parameters.
                constrs: synthesised_constrs,
            };

            // Emit the synthesised datatype as a preceding declaration.
            emitted_datatypes.push(Located::new(
                Declaration::Datatype(vec![synthesised_dt]),
                span.clone(),
            ));

            // Replace `Constructor::Enum` with a reference to the fresh datatype.
            Constructor::Named(datatype_id)
        }
    }
}
