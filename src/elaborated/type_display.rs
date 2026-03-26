//! Pretty-print elaborated [`Constructor`] and [`Kind`] for LSP hover / diagnostics.
//! Human-readable surface roughly aligned with Ur/Web type syntax (not a full `elab_print` port).
//!
//! [`format_constructor`] and [`format_kind`] cap recursion depth to avoid blowups on cyclic types.

use std::fmt::Write;

use crate::elaborated::{Constructor, Kind, LocatedConstructor, LocatedKind};

const MAX_RECURSION_DEPTH: u32 = 48;

/// Pretty-print a constructor for hovers / diagnostics (truncates past a fixed max depth).
///
/// # Arguments
///
/// * `constructor` — Elaborated constructor.
///
/// # Returns
///
/// Owned string (ASCII-ish; uses `…` when depth-capped).
pub fn format_constructor(constructor: &LocatedConstructor) -> String {
    let mut output_buffer = String::new();
    let _ = write_constructor_into(&mut output_buffer, constructor, 0);
    output_buffer
}

/// Pretty-print a kind (same depth cap as [`format_constructor`]).
///
/// # Arguments
///
/// * `kind` — Elaborated kind.
///
/// # Returns
///
/// Display string.
pub fn format_kind(kind: &LocatedKind) -> String {
    let mut output_buffer = String::new();
    let _ = write_kind_into(&mut output_buffer, kind, 0);
    output_buffer
}

fn write_constructor_into(
    output_buffer: &mut String,
    constructor: &LocatedConstructor,
    recursion_depth: u32,
) -> std::fmt::Result {
    if recursion_depth > MAX_RECURSION_DEPTH {
        return write!(output_buffer, "…");
    }
    match &constructor.node {
        Constructor::TFun(domain, codomain) => {
            let parenthesize_domain = matches!(
                domain.node,
                Constructor::TFun(_, _) | Constructor::TCFun(_, _, _, _)
            );
            if parenthesize_domain {
                write!(output_buffer, "(")?;
            }
            write_constructor_into(output_buffer, domain, recursion_depth + 1)?;
            if parenthesize_domain {
                write!(output_buffer, ")")?;
            }
            write!(output_buffer, " -> ")?;
            write_constructor_into(output_buffer, codomain, recursion_depth + 1)
        }
        Constructor::TCFun(explicitness, binder_name, parameter_kind, body) => {
            match explicitness {
                crate::elaborated::Explicitness::Implicit => write!(output_buffer, "?")?,
                crate::elaborated::Explicitness::Explicit => {}
            }
            write!(output_buffer, "{} : ", binder_name)?;
            write_kind_into(output_buffer, parameter_kind, recursion_depth + 1)?;
            write!(output_buffer, " -> ")?;
            write_constructor_into(output_buffer, body, recursion_depth + 1)
        }
        Constructor::TRecord(row) => {
            write!(output_buffer, "{{ ")?;
            write_constructor_into(output_buffer, row, recursion_depth + 1)?;
            write!(output_buffer, " }}")
        }
        Constructor::TDisjoint(left, right, result) => {
            write_constructor_into(output_buffer, left, recursion_depth + 1)?;
            write!(output_buffer, " * ")?;
            write_constructor_into(output_buffer, right, recursion_depth + 1)?;
            write!(output_buffer, " -> ")?;
            write_constructor_into(output_buffer, result, recursion_depth + 1)
        }
        Constructor::Rel(de_bruijn_index) => write!(output_buffer, "'{}", de_bruijn_index),
        Constructor::Named(global_id) => write!(output_buffer, "#{}", global_id),
        Constructor::ModProj(structure_id, module_path, component_name) => {
            write!(output_buffer, "mod{}:", structure_id)?;
            for path_segment in module_path {
                write!(output_buffer, "{}.", path_segment)?;
            }
            write!(output_buffer, "{}", component_name)
        }
        Constructor::App(function, argument) => {
            write_constructor_into(output_buffer, function, recursion_depth + 1)?;
            write!(output_buffer, " ")?;
            let parenthesize_argument = !matches!(
                argument.node,
                Constructor::Name(_)
                    | Constructor::Unit
                    | Constructor::Rel(_)
                    | Constructor::Named(_)
            );
            if parenthesize_argument {
                write!(output_buffer, "(")?;
            }
            write_constructor_into(output_buffer, argument, recursion_depth + 1)?;
            if parenthesize_argument {
                write!(output_buffer, ")")
            } else {
                Ok(())
            }
        }
        Constructor::Abs(binder_name, parameter_kind, body) => {
            write!(output_buffer, "{} : ", binder_name)?;
            write_kind_into(output_buffer, parameter_kind, recursion_depth + 1)?;
            write!(output_buffer, " -> ")?;
            write_constructor_into(output_buffer, body, recursion_depth + 1)
        }
        Constructor::KAbs(binder_name, body) => {
            write!(output_buffer, "{}:: ", binder_name)?;
            write_constructor_into(output_buffer, body, recursion_depth + 1)
        }
        Constructor::KApp(head, argument_kind) => {
            write_constructor_into(output_buffer, head, recursion_depth + 1)?;
            write!(output_buffer, "[")?;
            write_kind_into(output_buffer, argument_kind, recursion_depth + 1)?;
            write!(output_buffer, "]")
        }
        Constructor::TKFun(binder_name, body) => {
            write!(output_buffer, "{} ~> ", binder_name)?;
            write_constructor_into(output_buffer, body, recursion_depth + 1)
        }
        Constructor::Name(label) => write!(output_buffer, "{}", label),
        Constructor::Record(row_kind, fields) => {
            write!(output_buffer, "{{")?;
            write_kind_into(output_buffer, row_kind, recursion_depth + 1)?;
            for (field_name, field_type) in fields {
                write!(output_buffer, ", ")?;
                write_constructor_into(output_buffer, field_name, recursion_depth + 1)?;
                write!(output_buffer, " : ")?;
                write_constructor_into(output_buffer, field_type, recursion_depth + 1)?;
            }
            write!(output_buffer, "}}")
        }
        Constructor::Concat(left_row, right_row) => {
            write_constructor_into(output_buffer, left_row, recursion_depth + 1)?;
            write!(output_buffer, " ++ ")?;
            write_constructor_into(output_buffer, right_row, recursion_depth + 1)
        }
        Constructor::Map(domain_kind, codomain_kind) => {
            write!(output_buffer, "map(")?;
            write_kind_into(output_buffer, domain_kind, recursion_depth + 1)?;
            write!(output_buffer, ", ")?;
            write_kind_into(output_buffer, codomain_kind, recursion_depth + 1)?;
            write!(output_buffer, ")")
        }
        Constructor::Unit => write!(output_buffer, "()"),
        Constructor::Tuple(components) => {
            write!(output_buffer, "(")?;
            for (component_index, component) in components.iter().enumerate() {
                if component_index > 0 {
                    write!(output_buffer, " * ")?;
                }
                write_constructor_into(output_buffer, component, recursion_depth + 1)?;
            }
            write!(output_buffer, ")")
        }
        Constructor::Proj(tuple, index) => {
            write_constructor_into(output_buffer, tuple, recursion_depth + 1)?;
            write!(output_buffer, ".{}", index)
        }
        Constructor::Error => write!(output_buffer, "<error>"),
        Constructor::Unif(_, _, _, name, _) => write!(output_buffer, "?{}", name),
    }
}

fn write_kind_into(
    output_buffer: &mut String,
    kind: &LocatedKind,
    recursion_depth: u32,
) -> std::fmt::Result {
    if recursion_depth > MAX_RECURSION_DEPTH {
        return write!(output_buffer, "…");
    }
    match &kind.node {
        Kind::Type => write!(output_buffer, "Type"),
        Kind::Arrow(domain, codomain) => {
            write_kind_into(output_buffer, domain, recursion_depth + 1)?;
            write!(output_buffer, " -> ")?;
            write_kind_into(output_buffer, codomain, recursion_depth + 1)
        }
        Kind::Name => write!(output_buffer, "Name"),
        Kind::Record(inner) => {
            write!(output_buffer, "{{ ")?;
            write_kind_into(output_buffer, inner, recursion_depth + 1)?;
            write!(output_buffer, " }}")
        }
        Kind::Unit => write!(output_buffer, "()"),
        Kind::Tuple(components) => {
            write!(output_buffer, "(")?;
            for (component_index, component) in components.iter().enumerate() {
                if component_index > 0 {
                    write!(output_buffer, " * ")?;
                }
                write_kind_into(output_buffer, component, recursion_depth + 1)?;
            }
            write!(output_buffer, ")")
        }
        Kind::Error => write!(output_buffer, "<kind error>"),
        Kind::Unif(_, name, _) => write!(output_buffer, "?{}", name),
        Kind::TupleUnif(_, _, _) => write!(output_buffer, "?tuple"),
        Kind::Rel(de_bruijn_index) => write!(output_buffer, "'{}", de_bruijn_index),
        Kind::Fun(binder_name, body) => {
            write!(output_buffer, "{} -> ", binder_name)?;
            write_kind_into(output_buffer, body, recursion_depth + 1)
        }
    }
}
