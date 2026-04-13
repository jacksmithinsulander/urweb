//! Rejects full-stack Ur/Web surface declarations when [`LanguageCompilationProfile::UrCore`] is active.

use crate::diagnostics::{DiagnosticId, DiagnosticPayload};
use crate::error_types::{CompileError, ErrorReporter};
use crate::settings::LanguageCompilationProfile;
use crate::source::{Decl, LocDecl, LocSgnItem, Sgn, SgnItem, Str};

/// Appends one Ur-core rejection diagnostic and marks validation failure.
fn report_ur_core_surface_rejection(
    errors: &mut ErrorReporter,
    keyword: String,
    module_file: &str,
    outcome: &mut bool,
) {
    errors.report(CompileError::Plain(DiagnosticPayload::new(
        DiagnosticId::UrCoreSurfaceDeclNotAllowed,
        vec![keyword, module_file.to_string()],
    )));
    *outcome = false;
}

/// Maps forbidden top-level declarations to a short keyword for diagnostics.
fn forbidden_decl_keyword(declaration: &Decl) -> Option<&'static str> {
    match declaration {
        Decl::Export(_) => Some("export"),
        Decl::Table(_, _, _, _) => Some("table"),
        Decl::Sequence(_) => Some("sequence"),
        Decl::View(_, _) => Some("view"),
        Decl::Index(_, _, _) => Some("index"),
        Decl::Database(_) => Some("database"),
        Decl::Cookie(_, _) => Some("cookie"),
        Decl::Style(_) => Some("style"),
        Decl::Task(_, _) => Some("task"),
        Decl::Policy(_) => Some("policy"),
        Decl::OnError(_, _, _) => Some("onError"),
        _ => None,
    }
}

/// Walks a declaration list, rejecting constructs that only belong to the Ur/Web stack.
fn walk_decl_list_for_ur_core(
    declarations: &[LocDecl],
    module_file: &str,
    errors: &mut ErrorReporter,
    outcome: &mut bool,
) {
    for declaration in declarations {
        if let Some(keyword) = forbidden_decl_keyword(&declaration.node) {
            report_ur_core_surface_rejection(errors, keyword.to_string(), module_file, outcome);
        }
        if let Decl::Str(_, _, _, located_structure, _) = &declaration.node {
            walk_structure_for_ur_core(&located_structure.node, module_file, errors, outcome);
        }
    }
}

/// Recurses into functor bodies and nested structures.
fn walk_structure_for_ur_core(
    structure: &Str,
    module_file: &str,
    errors: &mut ErrorReporter,
    outcome: &mut bool,
) {
    match structure {
        Str::Const(nested) => walk_decl_list_for_ur_core(nested, module_file, errors, outcome),
        Str::Fun(_, _, _, body) => {
            walk_structure_for_ur_core(&body.node, module_file, errors, outcome)
        }
        Str::App(func, arg) => {
            walk_structure_for_ur_core(&func.node, module_file, errors, outcome);
            walk_structure_for_ur_core(&arg.node, module_file, errors, outcome);
        }
        Str::Proj(inner, _) => {
            walk_structure_for_ur_core(&inner.node, module_file, errors, outcome)
        }
        Str::Var(_) => {}
    }
}

/// Rejects `table` in signatures and walks nested module signatures.
fn walk_signature_items_for_ur_core(
    items: &[LocSgnItem],
    module_file: &str,
    errors: &mut ErrorReporter,
    outcome: &mut bool,
) {
    for item in items {
        match &item.node {
            SgnItem::Table(_, _, _, _) => {
                report_ur_core_surface_rejection(errors, "table".into(), module_file, outcome);
            }
            SgnItem::Str(_, nested) => {
                walk_signature_for_ur_core(&nested.node, module_file, errors, outcome)
            }
            SgnItem::Sgn(_, nested) => {
                walk_signature_for_ur_core(&nested.node, module_file, errors, outcome)
            }
            SgnItem::Functor(_, _, dom, ran) => {
                walk_signature_for_ur_core(&dom.node, module_file, errors, outcome);
                walk_signature_for_ur_core(&ran.node, module_file, errors, outcome);
            }
            _ => {}
        }
    }
}

/// Dispatches signature shapes for nested walks.
fn walk_signature_for_ur_core(
    signature: &Sgn,
    module_file: &str,
    errors: &mut ErrorReporter,
    outcome: &mut bool,
) {
    match signature {
        Sgn::Const(items) => walk_signature_items_for_ur_core(items, module_file, errors, outcome),
        Sgn::Fun(_, dom, ran) => {
            walk_signature_for_ur_core(&dom.node, module_file, errors, outcome);
            walk_signature_for_ur_core(&ran.node, module_file, errors, outcome);
        }
        Sgn::Where(inner, _, _, _) => {
            walk_signature_for_ur_core(&inner.node, module_file, errors, outcome)
        }
        Sgn::Var(_) | Sgn::Proj(_, _, _) => {}
    }
}

/// Validates parsed user `.ur` declarations for Ur core restrictions.
///
/// # Parameters
///
/// * `profile` — Language profile from compiler settings.
/// * `declarations` — Top-level declarations from one user module.
/// * `module_file` — Diagnostic label (usually the `.ur` path).
/// * `errors` — Diagnostic sink.
///
/// # Returns
///
/// `true` when nothing forbidden was found (or profile is not Ur core).
pub fn validate_user_ur_module_for_profile(
    profile: LanguageCompilationProfile,
    declarations: &[LocDecl],
    module_file: &str,
    errors: &mut ErrorReporter,
) -> bool {
    if profile != LanguageCompilationProfile::UrCore {
        return true;
    }
    let mut outcome = true;
    walk_decl_list_for_ur_core(declarations, module_file, errors, &mut outcome);
    outcome
}

/// Validates parsed user `.urs` items for Ur core restrictions.
///
/// # Returns
///
/// `true` when nothing forbidden was found (or profile is not Ur core).
pub fn validate_user_urs_module_for_profile(
    profile: LanguageCompilationProfile,
    items: &[LocSgnItem],
    module_file: &str,
    errors: &mut ErrorReporter,
) -> bool {
    if profile != LanguageCompilationProfile::UrCore {
        return true;
    }
    let mut outcome = true;
    walk_signature_items_for_ur_core(items, module_file, errors, &mut outcome);
    outcome
}
