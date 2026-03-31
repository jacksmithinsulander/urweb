//! Pretty-print elaborated [`crate::elaborated::Constructor`], [`crate::elaborated::Kind`],
//! signatures, patterns, and expressions for LSP hovers and **catalog diagnostic placeholders**
//! (never raw `Debug` of `Located` / unification cells).
//!
//! [`format_constructor`] and [`format_kind`] cap recursion depth to avoid blowups on cyclic types.

use std::fmt::Write;

use crate::datatype_kind::DatatypeKind;
use crate::elaborated::{
    Constructor, Expression, ImportMode, Kind, LocatedConstructor, LocatedExpression, LocatedKind,
    LocatedPattern, LocatedSignature, LocatedSignatureItem, Pattern, PatternConstructor, Signature,
    SignatureItem,
};
use crate::primitives::Prim;

const MAX_RECURSION_DEPTH: u32 = 48;
/// Cap how many top-level signature items appear in [`format_signature`] summaries.
const MAX_SIGNATURE_ITEM_LIST: usize = 16;

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

/// User-facing one-line summary of a signature item (for “missing / extra item” diagnostics).
///
/// # Arguments
///
/// * `item` — Elaborated signature item (name + classifier text).
///
/// # Returns
///
/// Single-line string capped by the same recursion limit as [`format_kind`].
pub fn format_signature_item(item: &LocatedSignatureItem) -> String {
    let mut output_buffer = String::new();
    let _ = write_signature_item_into(&mut output_buffer, item, 0);
    output_buffer
}

/// User-facing summary of a signature shape (for incompatible-signature errors).
///
/// # Arguments
///
/// * `signature` — Elaborated module/signature type.
///
/// # Returns
///
/// Braced item list (first [`MAX_SIGNATURE_ITEM_LIST`] items, then an ellipsis).
pub fn format_signature(signature: &LocatedSignature) -> String {
    let mut output_buffer = String::new();
    let _ = write_signature_into(&mut output_buffer, signature, 0);
    output_buffer
}

/// Pretty-print an elaborated pattern (exhaustiveness / case analysis messages).
///
/// # Arguments
///
/// * `pattern` — Elaborated pattern after [`crate::elaborated::elaborate::elab_pat`].
///
/// # Returns
///
/// Surface-ish pattern text (not necessarily valid Ur source).
pub fn format_pattern(pattern: &LocatedPattern) -> String {
    let mut output_buffer = String::new();
    let _ = write_pattern_into(&mut output_buffer, pattern, 0);
    output_buffer
}

/// Pretty-print an elaborated expression when a type error needs expression context.
///
/// # Arguments
///
/// * `expression` — Elaborated expression subtree.
///
/// # Returns
///
/// Abbreviated expression (large `Record` / `Let` nodes truncated); metavariables as `<expr_meta>`.
pub fn format_expression(expression: &LocatedExpression) -> String {
    let mut output_buffer = String::new();
    let _ = write_expression_into(&mut output_buffer, expression, 0);
    output_buffer
}

fn write_signature_item_into(
    output_buffer: &mut String,
    item: &LocatedSignatureItem,
    recursion_depth: u32,
) -> std::fmt::Result {
    if recursion_depth > MAX_RECURSION_DEPTH {
        return write!(output_buffer, "…");
    }
    match &item.node {
        SignatureItem::ConAbs(name, _, kind) => {
            write!(output_buffer, "con `{}` : ", name)?;
            write_kind_into(output_buffer, kind, recursion_depth + 1)
        }
        SignatureItem::Constructor(name, _, kind, constructor) => {
            write!(output_buffer, "constructor `{}` : ", name)?;
            write_kind_into(output_buffer, kind, recursion_depth + 1)?;
            write!(output_buffer, " = ")?;
            write_constructor_into(output_buffer, constructor, recursion_depth + 1)
        }
        SignatureItem::Datatype(declarations) => {
            if let Some(first) = declarations.first() {
                write!(
                    output_buffer,
                    "datatype `{}` (and {} more)",
                    first.name,
                    declarations.len().saturating_sub(1),
                )
            } else {
                write!(output_buffer, "datatype <empty>")
            }
        }
        SignatureItem::DatatypeImp { name, .. } => write!(output_buffer, "datatype `{}` (import)", name),
        SignatureItem::Val(name, _, constructor) => {
            write!(output_buffer, "val `{}` : ", name)?;
            write_constructor_into(output_buffer, constructor, recursion_depth + 1)
        }
        SignatureItem::Structure(import_mode, name, _, inner_signature) => {
            let mode_label = match import_mode {
                ImportMode::Import => "import",
                ImportMode::Skip => "skip",
            };
            write!(output_buffer, "structure `{}` ({}) : ", name, mode_label)?;
            write_signature_into(output_buffer, inner_signature, recursion_depth + 1)
        }
        SignatureItem::Signature(name, _, inner_signature) => {
            write!(output_buffer, "signature `{}` = ", name)?;
            write_signature_into(output_buffer, inner_signature, recursion_depth + 1)
        }
        SignatureItem::Constraint(left, right) => {
            write!(output_buffer, "constraint ")?;
            write_constructor_into(output_buffer, left, recursion_depth + 1)?;
            write!(output_buffer, " ~~ ")?;
            write_constructor_into(output_buffer, right, recursion_depth + 1)
        }
        SignatureItem::ClassAbs(name, _, kind) => {
            write!(output_buffer, "class `{}` : ", name)?;
            write_kind_into(output_buffer, kind, recursion_depth + 1)
        }
        SignatureItem::Class(name, _, kind, witness) => {
            write!(output_buffer, "class `{}` : ", name)?;
            write_kind_into(output_buffer, kind, recursion_depth + 1)?;
            write!(output_buffer, " = ")?;
            write_constructor_into(output_buffer, witness, recursion_depth + 1)
        }
    }
}

fn write_signature_into(
    output_buffer: &mut String,
    signature: &LocatedSignature,
    recursion_depth: u32,
) -> std::fmt::Result {
    if recursion_depth > MAX_RECURSION_DEPTH {
        return write!(output_buffer, "…");
    }
    match &signature.node {
        Signature::Const(items) => {
            write!(output_buffer, "{{ ")?;
            let limit = items.len().min(MAX_SIGNATURE_ITEM_LIST);
            for (index, signature_item) in items.iter().take(limit).enumerate() {
                if index > 0 {
                    write!(output_buffer, "; ")?;
                }
                write_signature_item_into(output_buffer, signature_item, recursion_depth + 1)?;
            }
            if items.len() > limit {
                write!(
                    output_buffer,
                    "; … (+{} items)",
                    items.len().saturating_sub(limit),
                )?;
            }
            write!(output_buffer, " }}")
        }
        Signature::Var(de_bruijn_index) => write!(output_buffer, "'sgn{}", de_bruijn_index),
        Signature::Fun(parameter_name, _, domain, codomain) => {
            write!(output_buffer, "Functor `{}` ", parameter_name)?;
            write_signature_into(output_buffer, domain, recursion_depth + 1)?;
            write!(output_buffer, " → ")?;
            write_signature_into(output_buffer, codomain, recursion_depth + 1)
        }
        Signature::Where(inner, path, field_name, witness_constructor) => {
            write_signature_into(output_buffer, inner, recursion_depth + 1)?;
            write!(output_buffer, " where ")?;
            if path.is_empty() {
                write!(output_buffer, "{}", field_name)?;
            } else {
                write!(output_buffer, "{}.{}", path.join("."), field_name)?;
            }
            write!(output_buffer, " = ")?;
            write_constructor_into(output_buffer, witness_constructor, recursion_depth + 1)
        }
        Signature::Proj(structure_id, module_path, component_name) => {
            write!(output_buffer, "mod{}:", structure_id)?;
            for segment in module_path {
                write!(output_buffer, "{}.", segment)?;
            }
            write!(output_buffer, "{}", component_name)
        }
        Signature::Error => write!(output_buffer, "<signature error>"),
    }
}

fn write_pattern_constructor_into(
    output_buffer: &mut String,
    pattern_constructor: &PatternConstructor,
) -> std::fmt::Result {
    match pattern_constructor {
        PatternConstructor::Var(tag) => write!(output_buffer, "dt#{}", tag),
        PatternConstructor::Proj(structure_id, module_path, name) => {
            write!(output_buffer, "mod{}:", structure_id)?;
            for segment in module_path {
                write!(output_buffer, "{}.", segment)?;
            }
            write!(output_buffer, "{}", name)
        }
    }
}

fn write_datatype_kind_hint(output_buffer: &mut String, datatype_kind: DatatypeKind) -> std::fmt::Result {
    let label = match datatype_kind {
        DatatypeKind::Enum => "enum",
        DatatypeKind::Option => "option",
        DatatypeKind::Default => "dt",
    };
    write!(output_buffer, "[{}] ", label)
}

fn write_pattern_into(
    output_buffer: &mut String,
    pattern: &LocatedPattern,
    recursion_depth: u32,
) -> std::fmt::Result {
    if recursion_depth > MAX_RECURSION_DEPTH {
        return write!(output_buffer, "…");
    }
    match &pattern.node {
        Pattern::Var(variable_name, annotated_type) => {
            write!(output_buffer, "{} : ", variable_name)?;
            write_constructor_into(output_buffer, annotated_type, recursion_depth + 1)
        }
        Pattern::Prim(primitive) => write_prim_short(output_buffer, primitive),
        Pattern::Constructor(datatype_kind, pattern_constructor, type_arguments, optional_subpattern) => {
            write_datatype_kind_hint(output_buffer, *datatype_kind)?;
            write_pattern_constructor_into(output_buffer, pattern_constructor)?;
            if !type_arguments.is_empty() {
                write!(output_buffer, " [")?;
                for (arg_index, type_argument) in type_arguments.iter().enumerate() {
                    if arg_index > 0 {
                        write!(output_buffer, ", ")?;
                    }
                    write_constructor_into(output_buffer, type_argument, recursion_depth + 1)?;
                }
                write!(output_buffer, "]")?;
            }
            if let Some(sub) = optional_subpattern {
                write!(output_buffer, " ")?;
                write_pattern_into(output_buffer, sub, recursion_depth + 1)?;
            }
            Ok(())
        }
        Pattern::Record(field_rows) => {
            write!(output_buffer, "{{ ")?;
            for (field_index, (field_label, subpattern, _field_type)) in field_rows.iter().enumerate() {
                if field_index > 0 {
                    write!(output_buffer, ", ")?;
                }
                write!(output_buffer, "{} = ", field_label)?;
                write_pattern_into(output_buffer, subpattern, recursion_depth + 1)?;
            }
            write!(output_buffer, " }}")
        }
    }
}

fn write_prim_short(output_buffer: &mut String, primitive: &Prim) -> std::fmt::Result {
    match primitive {
        Prim::Int(value) => write!(output_buffer, "{}", value),
        Prim::Float(value) => write!(output_buffer, "{}", value),
        Prim::Char(character) => write!(output_buffer, "'{}'", character),
        Prim::String(_, text) => {
            let shortened: String = text.chars().take(32).collect();
            let ellipsis = if text.chars().count() > 32 { "…" } else { "" };
            write!(output_buffer, "\"{}{}\"", shortened, ellipsis)
        }
    }
}

fn write_expression_into(
    output_buffer: &mut String,
    expression: &LocatedExpression,
    recursion_depth: u32,
) -> std::fmt::Result {
    if recursion_depth > MAX_RECURSION_DEPTH {
        return write!(output_buffer, "…");
    }
    match &expression.node {
        Expression::Prim(primitive) => write_prim_short(output_buffer, primitive),
        Expression::Rel(index) => write!(output_buffer, "'e{}", index),
        Expression::Named(global_id) => write!(output_buffer, "#e{}", global_id),
        Expression::ModProj(structure_id, module_path, component_name) => {
            write!(output_buffer, "mod{}:", structure_id)?;
            for segment in module_path {
                write!(output_buffer, "{}.", segment)?;
            }
            write!(output_buffer, "{}", component_name)
        }
        Expression::App(function, argument) => {
            write_expression_into(output_buffer, function, recursion_depth + 1)?;
            write!(output_buffer, " ")?;
            write_expression_into(output_buffer, argument, recursion_depth + 1)
        }
        Expression::Abs(
            binder_name,
            domain_constructor,
            codomain_constructor,
            body,
        ) => {
            write!(
                output_buffer,
                "\\{} : {} ; {} . ",
                binder_name,
                format_constructor(domain_constructor),
                format_constructor(codomain_constructor),
            )?;
            write_expression_into(output_buffer, body, recursion_depth + 1)
        }
        Expression::CApp(head, type_argument) => {
            write_expression_into(output_buffer, head, recursion_depth + 1)?;
            write!(output_buffer, " [{}]", format_constructor(type_argument))
        }
        Expression::CAbs(explicitness, binder_name, parameter_kind, body) => {
            match explicitness {
                crate::elaborated::Explicitness::Implicit => write!(output_buffer, "?")?,
                crate::elaborated::Explicitness::Explicit => {}
            }
            write!(
                output_buffer,
                "/\\{} : {} . ",
                binder_name,
                format_kind(parameter_kind),
            )?;
            write_expression_into(output_buffer, body, recursion_depth + 1)
        }
        Expression::KAbs(binder_name, body) => {
            write!(output_buffer, "Λ{} . ", binder_name)?;
            write_expression_into(output_buffer, body, recursion_depth + 1)
        }
        Expression::KApp(head, kind_argument) => {
            write_expression_into(output_buffer, head, recursion_depth + 1)?;
            write!(output_buffer, " [{}]", format_kind(kind_argument))
        }
        Expression::Record(field_rows) => {
            write!(output_buffer, "{{ ")?;
            let display_limit = field_rows.len().min(6usize);
            for (row_index, (label_constructor, field_expression, _value_type)) in
                field_rows.iter().take(display_limit).enumerate()
            {
                if row_index > 0 {
                    write!(output_buffer, ", ")?;
                }
                write_constructor_into(output_buffer, label_constructor, recursion_depth + 1)?;
                write!(output_buffer, " = ")?;
                write_expression_into(output_buffer, field_expression, recursion_depth + 1)?;
            }
            if field_rows.len() > display_limit {
                write!(
                    output_buffer,
                    ", … (+{})",
                    field_rows.len().saturating_sub(display_limit),
                )?;
            }
            write!(output_buffer, " }}")
        }
        Expression::Field(head, label_constructor, _field_meta) => {
            write_expression_into(output_buffer, head, recursion_depth + 1)?;
            write!(output_buffer, ".")?;
            write_constructor_into(output_buffer, label_constructor, recursion_depth + 1)
        }
        Expression::Concat(left, _left_row, right, _right_row) => {
            write_expression_into(output_buffer, left, recursion_depth + 1)?;
            write!(output_buffer, " ^ ")?;
            write_expression_into(output_buffer, right, recursion_depth + 1)
        }
        Expression::Cut(head, label_constructor, _field_meta) => {
            write_expression_into(output_buffer, head, recursion_depth + 1)?;
            write!(output_buffer, " \\ ")?;
            write_constructor_into(output_buffer, label_constructor, recursion_depth + 1)
        }
        Expression::CutMulti(head, label_constructor, _rest_meta) => {
            write_expression_into(output_buffer, head, recursion_depth + 1)?;
            write!(output_buffer, " \\\\ ")?;
            write_constructor_into(output_buffer, label_constructor, recursion_depth + 1)
        }
        Expression::Case(scrutinee, arms, _case_meta) => {
            write!(output_buffer, "case ")?;
            write_expression_into(output_buffer, scrutinee, recursion_depth + 1)?;
            write!(output_buffer, " of {} arm(s)", arms.len())
        }
        Expression::Error => write!(output_buffer, "<expression error>"),
        Expression::Unif(_) => write!(output_buffer, "<expr meta>"),
        Expression::Hole(_) => write!(output_buffer, "<type hole>"),
        Expression::Let(declarations, body, _body_type) => {
            write!(output_buffer, "let {} decl in ", declarations.len())?;
            write_expression_into(output_buffer, body, recursion_depth + 1)
        }
    }
}
