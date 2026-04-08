//! Parser for Ur/Web source files.
//!
//! - **parse_ur**: parse `.ur` files into `source::File`
//! - **parse_urs**: parse `.urs` signature files
//! - **lexer**: tokenization (Logos)
//!
//! ## Strict recognition (LangSec-oriented)
//!
//! - **CFG gate**: This crate's `build.rs` runs LALRPOP on every build; shift/reduce and
//!   reduce/reduce conflicts **fail the build** — the surface language is not treated
//!   as “best effort” at table generation time.
//! - **Lexer**: invalid or unterminated literals yield [`lexical_analyzer::LexError`];
//!   there is no silent recovery into a token stream.
//! - **Expression spine**: [`expr_langsec`] defines the reference recognizer for the
//!   comparison → arithmetic → juxtaposition tier; grammar actions that fold AST
//!   nodes use explicit [`Result`] paths (e.g. fallible `=>?`) where an invariant
//!   could be broken instead of panicking in the parser.
//!   **Regression lock:** after changing `ArithExp` / precedence in `grammar.lalrpop`, extend
//!   [`expr_langsec`] and `tests::langsec_spine_equiv` in this module so the CFG stays aligned
//!   with the recognizer (LangSec: one formal language for the spine).
//!
//! ## Preprocess ∘ parse (composed surface language)
//!
//! The **accepted** `.ur` text is not only `L(grammar)` on raw bytes; it is the
//! preimage of that grammar under a **specified** preprocessor chain:
//!
//! 1. **`.ur`**: `rewrite_datatype_constructors` → `rewrite_sgn_where` → `rewrite_case_expressions`,
//!    then [`parse_ur`](parse_ur) runs [`XmlAwareLexer`](lexical_analyzer::XmlAwareLexer) + `FileParser`.
//! 2. **`.urs`**: [`preprocess_urs`](preprocess_urs) (fuel-bounded), then lexer + `SgnItemsParser`.
//!
//! These rewrites are **total** string transducers on UTF-8 (invalid surrogate-edge cases are
//! ordinary char iteration). [`preprocess_urs`](preprocess_urs) can truncate with the remainder
//! appended if fuel exhausts — documented in its body. Integration tests in `tests/langsec_preprocess.rs`
//! pin representative rewrite + parse behavior.
//!
//! **Style:** new/edited Rust here follows [README.md](../../README.md) Rust code style (exceptions documented there).

pub mod expected_symbol_labels;
pub mod expr_langsec;
pub mod grammar_helpers;
pub mod lexical_analyzer;
mod sql_compat;
pub mod xml_helpers;

/// Name for LALRPOP reduce-value tuples (keeps generated `grammar.rs` clippy-clean for `type_complexity`).
#[cfg(generated_parser)]
pub type GrammarConLamTriple = (
    usize,
    Vec<(String, Option<crate::source::LocCon>, crate::source::LocExp)>,
    usize,
);

// `build.rs` always runs LALRPOP and sets `cargo:rustc-cfg=generated_parser` on success.
#[cfg(generated_parser)]
mod grammar {
    include!(concat!(env!("OUT_DIR"), "/parse/grammar.rs"));
}

use crate::diagnostics::{render_diagnostic_body, DiagnosticId, DiagnosticPayload};
use crate::error_types::{CompileError, ErrorReporter, Span};
use crate::source::{File, LocSgnItem};

#[macro_use]
mod urs_preprocess_macros;
mod preprocess_urs;

pub use preprocess_urs::preprocess_urs;

/// Test-only: override initial fuel for the next [`preprocess_urs`] call(s). Pass `None` to disable.
///
/// # Arguments
///
/// * `fuel` — Maximum preprocess steps, or `None` for the production default.
///
/// # Returns
///
/// Nothing.
#[cfg(test)]
pub fn test_set_preprocess_urs_fuel_override(fuel: Option<usize>) {
    preprocess_urs::set_test_fuel_override(fuel);
}

fn pp_kw_cont(c: u8) -> bool {
    matches!(
        c,
        b'_' | b'\'' | b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z'
    )
}

/// Upper bound on `for`-loop rounds for byte preprocessors (replaces unbounded `while scan < len`).
///
/// # Parameters
///
/// * `source_byte_length` — Length of the UTF-8 input being scanned.
///
/// # Returns
///
/// A cap of `length + 1` so a single pass cannot iterate more than linearly in input size.
#[inline]
fn preprocess_byte_scan_round_limit(source_byte_length: usize) -> usize {
    source_byte_length.saturating_add(1)
}

fn is_case_keyword(b: &[u8], i: usize) -> bool {
    if i + 4 > b.len() || &b[i..i + 4] != b"case" {
        return false;
    }
    if i > 0 && pp_kw_cont(b[i - 1]) {
        return false;
    }
    if i + 4 < b.len() && pp_kw_cont(b[i + 4]) {
        return false;
    }
    true
}

fn is_of_keyword(b: &[u8], i: usize) -> bool {
    if i + 2 > b.len() || &b[i..i + 2] != b"of" {
        return false;
    }
    if i > 0 && pp_kw_cont(b[i - 1]) {
        return false;
    }
    if i + 2 < b.len() && pp_kw_cont(b[i + 2]) {
        return false;
    }
    true
}

fn span_is_dummy_for_parser_repair(span: &Span) -> bool {
    span.first.line == 0 && span.first.col == 0 && span.last.line == 0 && span.last.col == 0
}

fn repair_misparsed_lambda_annotation_expression(expression: &mut crate::source::LocExp) {
    use crate::source::{Con, EDecl, Exp, Pat};

    match &mut expression.node {
        Exp::Annot(inner, constructor) => {
            repair_misparsed_lambda_annotation_expression(inner);
            repair_misparsed_lambda_annotation_constructor(constructor);
        }
        Exp::Var(_, _, _) | Exp::Prim(_) | Exp::Wild | Exp::Hole | Exp::KAbs(_, _) => {}
        Exp::App(function_expression, argument_expression) => {
            repair_misparsed_lambda_annotation_expression(function_expression);
            repair_misparsed_lambda_annotation_expression(argument_expression);
        }
        Exp::Abs(_, annotation, body) => {
            if let Some(annotation_constructor) = annotation {
                repair_misparsed_lambda_annotation_constructor(annotation_constructor);
            }
            repair_misparsed_lambda_annotation_expression(body);
        }
        Exp::CApp(inner, constructor) => {
            repair_misparsed_lambda_annotation_expression(inner);
            repair_misparsed_lambda_annotation_constructor(constructor);
        }
        Exp::CAbs(_, _, kind, body) => {
            repair_misparsed_lambda_annotation_kind(kind);
            repair_misparsed_lambda_annotation_expression(body);
        }
        Exp::Disjoint(left, right, body) => {
            repair_misparsed_lambda_annotation_constructor(left);
            repair_misparsed_lambda_annotation_constructor(right);
            repair_misparsed_lambda_annotation_expression(body);
        }
        Exp::DisjointApp(inner) => repair_misparsed_lambda_annotation_expression(inner),
        Exp::Record(fields, _) => {
            for (field_constructor, field_expression) in fields {
                repair_misparsed_lambda_annotation_constructor(field_constructor);
                repair_misparsed_lambda_annotation_expression(field_expression);
            }
        }
        Exp::Field(inner, field_constructor)
        | Exp::Cut(inner, field_constructor)
        | Exp::CutMulti(inner, field_constructor) => {
            repair_misparsed_lambda_annotation_expression(inner);
            repair_misparsed_lambda_annotation_constructor(field_constructor);
        }
        Exp::Concat(left, right) => {
            repair_misparsed_lambda_annotation_expression(left);
            repair_misparsed_lambda_annotation_expression(right);
        }
        Exp::Case(scrutinee, branches) => {
            repair_misparsed_lambda_annotation_expression(scrutinee);
            for (pattern, branch_expression) in branches.iter_mut() {
                repair_misparsed_lambda_annotation_pattern(pattern);
                repair_misparsed_lambda_annotation_expression(branch_expression);
            }
            repair_single_branch_lambda_annotation_case(branches);
            repair_nested_case_branch_grouping(branches);
        }
        Exp::Let(declarations, body) => {
            for declaration in declarations {
                match &mut declaration.node {
                    EDecl::Val(pattern, bound_expression) => {
                        repair_misparsed_lambda_annotation_pattern(pattern);
                        repair_misparsed_lambda_annotation_expression(bound_expression);
                    }
                    EDecl::ValRec(bindings) => {
                        for (_, annotation, bound_expression) in bindings {
                            if let Some(annotation_constructor) = annotation {
                                repair_misparsed_lambda_annotation_constructor(
                                    annotation_constructor,
                                );
                            }
                            repair_misparsed_lambda_annotation_expression(bound_expression);
                        }
                    }
                }
            }
            repair_misparsed_lambda_annotation_expression(body);
        }
        Exp::Infix(_, left, right) => {
            repair_misparsed_lambda_annotation_expression(left);
            repair_misparsed_lambda_annotation_expression(right);
        }
    }

    fn repair_single_branch_lambda_annotation_case(
        branches: &mut Vec<(crate::source::LocPat, crate::source::LocExp)>,
    ) {
        if branches.len() != 1 {
            return;
        }
        let (pattern, branch_expression) = &mut branches[0];
        let Pat::Annot(inner_pattern, annotation_constructor) = &mut pattern.node else {
            return;
        };
        let Pat::Var(_) = inner_pattern.node else {
            return;
        };
        let Con::Var(module_path, _) = &annotation_constructor.node else {
            return;
        };
        if !module_path.is_empty() {
            return;
        }
        let Exp::Abs(argument_name, None, inner_body) = &branch_expression.node else {
            return;
        };
        if !span_is_dummy_for_parser_repair(&branch_expression.span) {
            return;
        }
        let applied_argument = crate::error_types::Located::new(
            Con::Var(Vec::new(), argument_name.clone()),
            branch_expression.span.clone(),
        );
        let repaired_annotation = crate::error_types::Located::new(
            Con::App(
                Box::new(annotation_constructor.clone()),
                Box::new(applied_argument),
            ),
            annotation_constructor.span.clone(),
        );
        *annotation_constructor = repaired_annotation;
        *branch_expression = inner_body.as_ref().clone();
    }

    fn repair_nested_case_branch_grouping(
        branches: &mut Vec<(crate::source::LocPat, crate::source::LocExp)>,
    ) {
        let initial_len = branches.len();
        for _ in 0..initial_len {
            let mut repair_index: Option<usize> = None;
            for index in 0..branches.len().saturating_sub(1) {
                if branch_expression_accepts_nested_case_branches(&branches[index].1) {
                    repair_index = Some(index);
                }
            }
            let Some(index) = repair_index else {
                return;
            };
            let trailing_branches: Vec<(crate::source::LocPat, crate::source::LocExp)> =
                branches.drain(index + 1..).collect();
            match branches.get_mut(index) {
                Some((_, branch_expression)) => {
                    append_nested_case_branches(branch_expression, trailing_branches);
                }
                None => return,
            }
        }

        fn branch_expression_accepts_nested_case_branches(
            expression: &crate::source::LocExp,
        ) -> bool {
            match &expression.node {
                Exp::Case(_, _) => true,
                Exp::Annot(inner, _) => branch_expression_accepts_nested_case_branches(inner),
                _ => false,
            }
        }

        fn append_nested_case_branches(
            expression: &mut crate::source::LocExp,
            mut trailing_branches: Vec<(crate::source::LocPat, crate::source::LocExp)>,
        ) {
            match &mut expression.node {
                Exp::Case(_, inner_branches) => inner_branches.append(&mut trailing_branches),
                Exp::Annot(inner, _) => append_nested_case_branches(inner, trailing_branches),
                _ => {}
            }
        }
    }

    fn repair_misparsed_lambda_annotation_pattern(pattern: &mut crate::source::LocPat) {
        use crate::source::Pat;
        match &mut pattern.node {
            Pat::Var(_) | Pat::Prim(_) => {}
            Pat::Con(_, _, argument_pattern) => {
                if let Some(argument_pattern) = argument_pattern {
                    repair_misparsed_lambda_annotation_pattern(argument_pattern);
                }
            }
            Pat::Record(fields, _) => {
                for (_, field_pattern) in fields {
                    repair_misparsed_lambda_annotation_pattern(field_pattern);
                }
            }
            Pat::Annot(inner_pattern, annotation_constructor) => {
                repair_misparsed_lambda_annotation_pattern(inner_pattern);
                repair_misparsed_lambda_annotation_constructor(annotation_constructor);
            }
        }
    }

    fn repair_misparsed_lambda_annotation_constructor(constructor: &mut crate::source::LocCon) {
        use crate::source::Con;
        match &mut constructor.node {
            Con::Annot(inner, kind) => {
                repair_misparsed_lambda_annotation_constructor(inner);
                repair_misparsed_lambda_annotation_kind(kind);
            }
            Con::TFun(left, right) | Con::Concat(left, right) => {
                repair_misparsed_lambda_annotation_constructor(left);
                repair_misparsed_lambda_annotation_constructor(right);
            }
            Con::TCFun(_, _, kind, body) => {
                repair_misparsed_lambda_annotation_kind(kind);
                repair_misparsed_lambda_annotation_constructor(body);
            }
            Con::TRecord(inner) | Con::KAbs(_, inner) | Con::TKFun(_, inner) => {
                repair_misparsed_lambda_annotation_constructor(inner);
            }
            Con::TDisjoint(left, right, body) => {
                repair_misparsed_lambda_annotation_constructor(left);
                repair_misparsed_lambda_annotation_constructor(right);
                repair_misparsed_lambda_annotation_constructor(body);
            }
            Con::App(function_constructor, argument_constructor) => {
                repair_misparsed_lambda_annotation_constructor(function_constructor);
                repair_misparsed_lambda_annotation_constructor(argument_constructor);
            }
            Con::Abs(_, kind, body) => {
                if let Some(kind) = kind {
                    repair_misparsed_lambda_annotation_kind(kind);
                }
                repair_misparsed_lambda_annotation_constructor(body);
            }
            Con::Record(fields) => {
                for (field_name, field_value) in fields {
                    repair_misparsed_lambda_annotation_constructor(field_name);
                    repair_misparsed_lambda_annotation_constructor(field_value);
                }
            }
            Con::Tuple(items) => {
                for item in items {
                    repair_misparsed_lambda_annotation_constructor(item);
                }
            }
            Con::Proj(inner, _) => repair_misparsed_lambda_annotation_constructor(inner),
            Con::Var(_, _) | Con::Name(_) | Con::Map | Con::Unit | Con::Wild(_) => {}
        }
    }

    fn repair_misparsed_lambda_annotation_kind(kind: &mut crate::source::LocKind) {
        use crate::source::Kind;
        match &mut kind.node {
            Kind::Arrow(left, right) => {
                repair_misparsed_lambda_annotation_kind(left);
                repair_misparsed_lambda_annotation_kind(right);
            }
            Kind::Record(inner) | Kind::Fun(_, inner) => {
                repair_misparsed_lambda_annotation_kind(inner);
            }
            Kind::Tuple(items) => {
                for item in items {
                    repair_misparsed_lambda_annotation_kind(item);
                }
            }
            Kind::Type | Kind::Name | Kind::Unit | Kind::Wild | Kind::Var(_) => {}
        }
    }
}

fn repair_misparsed_lambda_annotation_file(file: &mut File) {
    use crate::source::Decl;

    for declaration in file {
        match &mut declaration.node {
            Decl::Con(_, _, constructor) => {
                repair_misparsed_lambda_annotation_constructor_in_decl(constructor)
            }
            Decl::Datatype(datatypes) => {
                for datatype in datatypes {
                    for (_, argument_constructor) in &mut datatype.constrs {
                        if let Some(argument_constructor) = argument_constructor {
                            repair_misparsed_lambda_annotation_constructor_in_decl(
                                argument_constructor,
                            );
                        }
                    }
                }
            }
            Decl::Val(pattern, expression) => {
                repair_misparsed_lambda_annotation_pattern_in_decl(pattern);
                repair_misparsed_lambda_annotation_expression(expression);
            }
            Decl::ValRec(bindings) => {
                for (_, annotation, expression) in bindings {
                    if let Some(annotation_constructor) = annotation {
                        repair_misparsed_lambda_annotation_constructor_in_decl(
                            annotation_constructor,
                        );
                    }
                    repair_misparsed_lambda_annotation_expression(expression);
                }
            }
            _ => {}
        }
    }

    fn repair_misparsed_lambda_annotation_pattern_in_decl(pattern: &mut crate::source::LocPat) {
        use crate::source::Pat;
        match &mut pattern.node {
            Pat::Var(_) | Pat::Prim(_) => {}
            Pat::Con(_, _, argument_pattern) => {
                if let Some(argument_pattern) = argument_pattern {
                    repair_misparsed_lambda_annotation_pattern_in_decl(argument_pattern);
                }
            }
            Pat::Record(fields, _) => {
                for (_, field_pattern) in fields {
                    repair_misparsed_lambda_annotation_pattern_in_decl(field_pattern);
                }
            }
            Pat::Annot(inner_pattern, annotation_constructor) => {
                repair_misparsed_lambda_annotation_pattern_in_decl(inner_pattern);
                repair_misparsed_lambda_annotation_constructor_in_decl(annotation_constructor);
            }
        }
    }

    fn repair_misparsed_lambda_annotation_constructor_in_decl(
        constructor: &mut crate::source::LocCon,
    ) {
        use crate::source::Con;
        match &mut constructor.node {
            Con::Annot(inner, kind) => {
                repair_misparsed_lambda_annotation_constructor_in_decl(inner);
                repair_misparsed_lambda_annotation_kind_in_decl(kind);
            }
            Con::TFun(left, right) | Con::Concat(left, right) => {
                repair_misparsed_lambda_annotation_constructor_in_decl(left);
                repair_misparsed_lambda_annotation_constructor_in_decl(right);
            }
            Con::TCFun(_, _, kind, body) => {
                repair_misparsed_lambda_annotation_kind_in_decl(kind);
                repair_misparsed_lambda_annotation_constructor_in_decl(body);
            }
            Con::TRecord(inner) | Con::KAbs(_, inner) | Con::TKFun(_, inner) => {
                repair_misparsed_lambda_annotation_constructor_in_decl(inner);
            }
            Con::TDisjoint(left, right, body) => {
                repair_misparsed_lambda_annotation_constructor_in_decl(left);
                repair_misparsed_lambda_annotation_constructor_in_decl(right);
                repair_misparsed_lambda_annotation_constructor_in_decl(body);
            }
            Con::App(function_constructor, argument_constructor) => {
                repair_misparsed_lambda_annotation_constructor_in_decl(function_constructor);
                repair_misparsed_lambda_annotation_constructor_in_decl(argument_constructor);
            }
            Con::Abs(_, kind, body) => {
                if let Some(kind) = kind {
                    repair_misparsed_lambda_annotation_kind_in_decl(kind);
                }
                repair_misparsed_lambda_annotation_constructor_in_decl(body);
            }
            Con::Record(fields) => {
                for (field_name, field_value) in fields {
                    repair_misparsed_lambda_annotation_constructor_in_decl(field_name);
                    repair_misparsed_lambda_annotation_constructor_in_decl(field_value);
                }
            }
            Con::Tuple(items) => {
                for item in items {
                    repair_misparsed_lambda_annotation_constructor_in_decl(item);
                }
            }
            Con::Proj(inner, _) => repair_misparsed_lambda_annotation_constructor_in_decl(inner),
            Con::Var(_, _) | Con::Name(_) | Con::Map | Con::Unit | Con::Wild(_) => {}
        }
    }

    fn repair_misparsed_lambda_annotation_kind_in_decl(kind: &mut crate::source::LocKind) {
        use crate::source::Kind;
        match &mut kind.node {
            Kind::Arrow(left, right) => {
                repair_misparsed_lambda_annotation_kind_in_decl(left);
                repair_misparsed_lambda_annotation_kind_in_decl(right);
            }
            Kind::Record(inner) | Kind::Fun(_, inner) => {
                repair_misparsed_lambda_annotation_kind_in_decl(inner);
            }
            Kind::Tuple(items) => {
                for item in items {
                    repair_misparsed_lambda_annotation_kind_in_decl(item);
                }
            }
            Kind::Type | Kind::Name | Kind::Unit | Kind::Wild | Kind::Var(_) => {}
        }
    }
}

fn skip_ml_comment_bytes(b: &[u8], mut i: usize, n: usize) -> usize {
    let mut depth = 1usize;
    let scan_budget = n.saturating_mul(2).saturating_add(1);
    for _ in 0..scan_budget {
        if i >= n || depth == 0 {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            i += 2;
            depth += 1;
        } else if i + 1 < n && b[i] == b'*' && b[i + 1] == b')' {
            i += 2;
            depth -= 1;
        } else {
            i += 1;
        }
    }
    i
}

fn skip_string_bytes(b: &[u8], mut i: usize, n: usize) -> usize {
    let scan_budget = n.saturating_sub(i).saturating_add(1);
    for _ in 0..scan_budget {
        if i >= n {
            break;
        }
        if b[i] == b'"' {
            return i + 1;
        }
        if b[i] == b'\\' && i + 1 < n {
            i += 2;
        } else {
            i += 1;
        }
    }
    n
}

/// Byte index just after the `of` in `case` ⟨scrutinee⟩ `of`, or `None` if unterminated.
fn scan_case_of_end(b: &[u8], mut i: usize, n: usize) -> Option<usize> {
    let mut depth = 0i32;
    let scan_budget = n.saturating_mul(2).saturating_add(1);
    for _ in 0..scan_budget {
        if i >= n {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            i = skip_ml_comment_bytes(b, i + 2, n);
            continue;
        }
        if b[i] == b'"' {
            i = skip_string_bytes(b, i + 1, n);
            continue;
        }
        if depth == 0 && is_of_keyword(b, i) {
            return Some(i + 2);
        }
        match b.get(i).copied() {
            Some(b'(' | b'[' | b'{') => {
                depth += 1;
                i += 1;
            }
            Some(b')' | b']' | b'}') => {
                depth = (depth - 1).max(0);
                i += 1;
            }
            Some(_) => i += 1,
            None => break,
        }
    }
    None
}

fn arm_sep_at(b: &[u8], i: usize, n: usize) -> bool {
    if i + 8 > n || &b[i..i + 8] != b"arm_sep" {
        return false;
    }
    match b.get(i + 8).copied() {
        None => true,
        Some(c) => !pp_kw_cont(c),
    }
}

fn case_end_at(b: &[u8], i: usize, n: usize) -> bool {
    if i + 8 > n || &b[i..i + 8] != b"case_end" {
        return false;
    }
    match b.get(i + 8).copied() {
        None => true,
        Some(c) => !pp_kw_cont(c),
    }
}

fn case_bar_at(b: &[u8], i: usize, n: usize) -> bool {
    if i + 8 > n || &b[i..i + 8] != b"case_bar" {
        return false;
    }
    match b.get(i + 8).copied() {
        None => true,
        Some(c) => !pp_kw_cont(c),
    }
}

fn emit_ws_comments_prefix(out: &mut String, input: &str, b: &[u8], i: &mut usize, n: usize) {
    let scan_budget = n.saturating_add(1);
    for _ in 0..scan_budget {
        if *i >= n {
            break;
        }
        if pp_urs_is_ws!(b[*i]) {
            out.push(b[*i] as char);
            *i += 1;
            continue;
        }
        if *i + 1 < n && b[*i] == b'(' && b[*i + 1] == b'*' {
            let start = *i;
            *i = skip_ml_comment_bytes(b, *i + 2, n);
            out.push_str(&input[start..*i]);
            continue;
        }
        if b[*i] == b'"' {
            let start = *i;
            *i = skip_string_bytes(b, *i + 1, n);
            out.push_str(&input[start..*i]);
            continue;
        }
        break;
    }
}

/// Pass-through scan (legacy hook): `case`/`of` arm rewriting is done in
/// `rewrite_case_arm_separators` to match `urweb.grm` `barOpt branch branchs` — no forced
/// `arm_sep` after every `of`.
///
/// # Arguments
///
/// * `input` — UTF-8 source text.
///
/// # Returns
///
/// Same string (identity).
pub fn rewrite_case_leading_bars(input: &str) -> String {
    input.to_string()
}

/// After each `case … of | …`, replace subsequent arm-separator `|` at arm-body depth 0 with
/// `arm_sep` (see `grammar.lalrpop` `CaseArmSep`). Pattern scan stops at the first `=>` at
/// paren depth 0; bodies treat `(* … *)` and `"…"` like the leading-bar pass.  Patterns with
/// top-level `|` (or-pats) can confuse this pass — parenthesize if needed.
///
/// # Arguments
///
/// * `input` — UTF-8 `.ur` / `.urs` source before parsing.
///
/// # Returns
///
/// Transformed source safe for the case-arm grammar.
pub fn rewrite_case_arm_separators(input: &str) -> String {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum BodyStop {
        NextArm,
        CaseDone,
    }

    fn copy_ml_comment(out: &mut String, input: &str, b: &[u8], mut i: usize, n: usize) -> usize {
        let start = i;
        i = skip_ml_comment_bytes(b, i + 2, n);
        out.push_str(&input[start..i]);
        i
    }

    fn copy_string(out: &mut String, input: &str, b: &[u8], mut i: usize, n: usize) -> usize {
        let start = i;
        i = skip_string_bytes(b, i + 1, n);
        out.push_str(&input[start..i]);
        i
    }

    /// Copy [`pattern_scan_index`..] to `pattern_output` until `=>` at nesting depth 0; returns the index after `=>`.
    fn scan_pat_to_arrow(
        pattern_output: &mut String,
        input_text: &str,
        source_bytes: &[u8],
        mut pattern_scan_index: usize,
        source_byte_length: usize,
    ) -> Option<usize> {
        let mut bracket_nesting_depth = 0i32;
        let scan_round_limit = preprocess_byte_scan_round_limit(source_byte_length);
        for _pattern_scan_round in 0..scan_round_limit {
            if pattern_scan_index >= source_byte_length {
                return None;
            }
            if pattern_scan_index + 1 < source_byte_length
                && source_bytes[pattern_scan_index] == b'('
                && source_bytes[pattern_scan_index + 1] == b'*'
            {
                pattern_scan_index = copy_ml_comment(
                    pattern_output,
                    input_text,
                    source_bytes,
                    pattern_scan_index,
                    source_byte_length,
                );
                continue;
            }
            if source_bytes[pattern_scan_index] == b'"' {
                pattern_scan_index = copy_string(
                    pattern_output,
                    input_text,
                    source_bytes,
                    pattern_scan_index,
                    source_byte_length,
                );
                continue;
            }
            if bracket_nesting_depth == 0
                && pattern_scan_index + 1 < source_byte_length
                && source_bytes[pattern_scan_index] == b'='
                && source_bytes[pattern_scan_index + 1] == b'>'
            {
                pattern_output.push_str("=>");
                return Some(pattern_scan_index + 2);
            }
            match source_bytes[pattern_scan_index] {
                b'(' | b'[' | b'{' => {
                    pattern_output.push(source_bytes[pattern_scan_index] as char);
                    bracket_nesting_depth += 1;
                    pattern_scan_index += 1;
                }
                b')' | b']' | b'}' => {
                    pattern_output.push(source_bytes[pattern_scan_index] as char);
                    bracket_nesting_depth = (bracket_nesting_depth - 1).max(0);
                    pattern_scan_index += 1;
                }
                _other_byte => {
                    let unicode_char = input_text[pattern_scan_index..].chars().next()?;
                    pattern_output.push(unicode_char);
                    pattern_scan_index += unicode_char.len_utf8();
                }
            }
        }
        None
    }

    /// Scan a case arm body, writing raw text to a local buffer.
    /// Returns `(stop_pos, stop_reason, body_text)`.
    ///
    /// Stops (does NOT consume) at:
    ///  - `arm_sep` / `|` at depth 0              → NextArm
    ///  - `)` / `]` / `}` at depth 0             → CaseDone (closes enclosing bracket)
    ///  - `in` / `end` of enclosing `let`         → CaseDone
    ///  - `fun` / `val` / `and` at depth 0        → CaseDone (new top-level decl)
    ///
    /// `;` is NOT a stop — it sequences monadic actions within an arm body.
    /// Nested case expressions' `|` separators are inside bracketed subterms or
    /// will be handled by the recursive rewrite applied to the returned body.
    fn scan_body(
        input_text: &str,
        source_bytes: &[u8],
        mut body_scan_index: usize,
        source_byte_length: usize,
    ) -> Option<(usize, BodyStop, String)> {
        let mut body_text_accumulator = String::new();
        let mut bracket_nesting_depth = 0i32;
        let mut open_let_keyword_depth = 0i32;
        let scan_round_limit = preprocess_byte_scan_round_limit(source_byte_length);
        for _body_scan_round in 0..scan_round_limit {
            if body_scan_index >= source_byte_length {
                break;
            }
            if body_scan_index + 1 < source_byte_length
                && source_bytes[body_scan_index] == b'('
                && source_bytes[body_scan_index + 1] == b'*'
            {
                body_scan_index = copy_ml_comment(
                    &mut body_text_accumulator,
                    input_text,
                    source_bytes,
                    body_scan_index,
                    source_byte_length,
                );
                continue;
            }
            if source_bytes[body_scan_index] == b'"' {
                body_scan_index = copy_string(
                    &mut body_text_accumulator,
                    input_text,
                    source_bytes,
                    body_scan_index,
                    source_byte_length,
                );
                continue;
            }
            if bracket_nesting_depth == 0
                && arm_sep_at(source_bytes, body_scan_index, source_byte_length)
            {
                return Some((body_scan_index, BodyStop::NextArm, body_text_accumulator));
            }
            if bracket_nesting_depth == 0
                && case_end_at(source_bytes, body_scan_index, source_byte_length)
            {
                return Some((body_scan_index, BodyStop::CaseDone, body_text_accumulator));
            }
            if bracket_nesting_depth == 0 && source_bytes[body_scan_index] == b'|' {
                return Some((body_scan_index, BodyStop::NextArm, body_text_accumulator));
            }
            // `)` / `]` / `}` at depth 0 close an enclosing bracket → arm ends
            if bracket_nesting_depth == 0
                && matches!(source_bytes[body_scan_index], b')' | b']' | b'}')
            {
                return Some((body_scan_index, BodyStop::CaseDone, body_text_accumulator));
            }
            if bracket_nesting_depth == 0
                && pp_kw_word_at(source_bytes, body_scan_index, source_byte_length, b"let")
            {
                body_text_accumulator.push_str("let");
                body_scan_index += 3;
                open_let_keyword_depth += 1;
                continue;
            }
            if bracket_nesting_depth == 0
                && pp_kw_word_at(source_bytes, body_scan_index, source_byte_length, b"in")
            {
                match open_let_keyword_depth.cmp(&0) {
                    std::cmp::Ordering::Greater => {
                        body_text_accumulator.push_str("in");
                        body_scan_index += 2;
                    }
                    std::cmp::Ordering::Equal | std::cmp::Ordering::Less => {
                        return Some((body_scan_index, BodyStop::CaseDone, body_text_accumulator));
                    }
                }
                continue;
            }
            if bracket_nesting_depth == 0
                && pp_kw_word_at(source_bytes, body_scan_index, source_byte_length, b"end")
            {
                match open_let_keyword_depth.cmp(&0) {
                    std::cmp::Ordering::Greater => {
                        body_text_accumulator.push_str("end");
                        body_scan_index += 3;
                        open_let_keyword_depth -= 1;
                    }
                    std::cmp::Ordering::Equal | std::cmp::Ordering::Less => {
                        return Some((body_scan_index, BodyStop::CaseDone, body_text_accumulator));
                    }
                }
                continue;
            }
            if bracket_nesting_depth == 0 && open_let_keyword_depth == 0 {
                for declaration_keyword in &[b"fun" as &[u8], b"val", b"and"] {
                    if pp_kw_word_at(
                        source_bytes,
                        body_scan_index,
                        source_byte_length,
                        declaration_keyword,
                    ) {
                        return Some((body_scan_index, BodyStop::CaseDone, body_text_accumulator));
                    }
                }
            }
            match source_bytes[body_scan_index] {
                b'(' | b'[' | b'{' => {
                    body_text_accumulator.push(source_bytes[body_scan_index] as char);
                    bracket_nesting_depth += 1;
                    body_scan_index += 1;
                }
                b')' | b']' | b'}' => {
                    body_text_accumulator.push(source_bytes[body_scan_index] as char);
                    bracket_nesting_depth -= 1;
                    body_scan_index += 1;
                }
                _other_byte => {
                    let unicode_char = input_text[body_scan_index..].chars().next()?;
                    body_text_accumulator.push(unicode_char);
                    body_scan_index += unicode_char.len_utf8();
                }
            }
        }
        Some((body_scan_index, BodyStop::CaseDone, body_text_accumulator))
    }

    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n.saturating_add(32));
    let mut i = 0usize;
    let cap = n.saturating_add(1);
    for _ in 0..cap {
        if i >= n {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if is_case_keyword(b, i) {
            let after_case = i + 4;
            if let Some(after_of) = scan_case_of_end(b, after_case, n) {
                out.push_str(&input[i..after_of]);
                let mut j = after_of;
                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                // `urweb.grm` `barOpt`: optional leading `|` — `case_bar`, never `arm_sep`.
                if case_bar_at(b, j, n) {
                    out.push_str(&input[j..j + 8]);
                    j += 8;
                } else if arm_sep_at(b, j, n) {
                    out.push_str(" case_bar ");
                    j += 8;
                } else if b.get(j) == Some(&b'|') {
                    out.push_str(" case_bar ");
                    j += 1;
                }
                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                // Each arm advances `j`; cap iterations by source length so malformed input cannot spin.
                let case_arm_budget = n.saturating_add(1);
                let mut case_arms_resolved = false;
                'case_arms: for _ in 0..case_arm_budget {
                    let Some(after_arrow) = scan_pat_to_arrow(&mut out, input, b, j, n) else {
                        out.push_str(&input[j..]);
                        return out;
                    };
                    j = after_arrow;
                    let Some((stop_i, stop, raw_body)) = scan_body(input, b, j, n) else {
                        out.push_str(&input[j..]);
                        return out;
                    };
                    j = stop_i;
                    // Recursively preprocess nested case expressions within the arm body
                    out.push_str(&rewrite_case_arm_separators(&raw_body));
                    match stop {
                        BodyStop::CaseDone => {
                            if case_end_at(b, j, n) {
                                out.push_str(&input[j..j + 8]);
                                i = j + 8;
                            } else {
                                out.push_str(" case_end ");
                                i = j;
                            }
                            case_arms_resolved = true;
                            break 'case_arms;
                        }
                        BodyStop::NextArm => {
                            if arm_sep_at(b, j, n) {
                                out.push_str(&input[j..j + 8]);
                                j += 8;
                                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                                continue;
                            }
                            if b.get(j) == Some(&b'|') {
                                out.push_str(" arm_sep ");
                                j += 1;
                                emit_ws_comments_prefix(&mut out, input, b, &mut j, n);
                                continue;
                            }
                            out.push_str(&input[j..]);
                            return out;
                        }
                    }
                }
                if !case_arms_resolved {
                    out.push_str(&input[j..]);
                    return out;
                }
                continue;
            }
        }
        let Some(ch) = input[i..].chars().next() else {
            break;
        };
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Compose [`rewrite_case_leading_bars`] and [`rewrite_case_arm_separators`] for `case` preprocessing.
///
/// # Returns
///
/// Rewritten UTF-8 string.
pub fn rewrite_case_expressions(src: &str) -> String {
    rewrite_case_arm_separators(&rewrite_case_leading_bars(src))
}

/// Rewrite bare kind binders `nm :: KindExpr ->` to `[nm :: KindExpr] ->`.
///
/// In Ur/Web, `nm :: K -> C` is valid at the constructor level (equivalent to `[nm :: K] -> C`).
/// Adding this as a grammar rule causes LR(1) conflicts because `IDENT` is used for both
/// `AtomConNode` and `KindAtom`.  The preprocessor handles the common case by scanning for
/// `lowercase-ident :: kind ->` patterns and wrapping in brackets.
///
/// # Arguments
///
/// * `src` — Signature or source fragment.
///
/// # Returns
///
/// Source with bracketed kind binders inserted where detected.
pub fn rewrite_bare_kind_binders(source_text: &str) -> String {
    let source_bytes = source_text.as_bytes();
    let source_byte_length = source_bytes.len();
    let mut output_text = String::with_capacity(source_byte_length);
    let mut scan_index = 0usize;
    // Track depth inside `[...]` brackets. Inside brackets the binder is already bracketed.
    let mut square_bracket_depth: i32 = 0;
    let outer_scan_limit = preprocess_byte_scan_round_limit(source_byte_length);
    for _outer_scan_round in 0..outer_scan_limit {
        if scan_index >= source_byte_length {
            break;
        }
        if scan_index + 1 < source_byte_length
            && source_bytes[scan_index] == b'('
            && source_bytes[scan_index + 1] == b'*'
        {
            let comment_span_start = scan_index;
            scan_index = skip_ml_comment_bytes(source_bytes, scan_index + 2, source_byte_length);
            output_text.push_str(&source_text[comment_span_start..scan_index]);
            continue;
        }
        if source_bytes[scan_index] == b'"' {
            let string_span_start = scan_index;
            scan_index = skip_string_bytes(source_bytes, scan_index + 1, source_byte_length);
            output_text.push_str(&source_text[string_span_start..scan_index]);
            continue;
        }
        if (source_bytes[scan_index].is_ascii_lowercase() || source_bytes[scan_index] == b'_')
            && square_bracket_depth == 0
        {
            if scan_index > 0 && pp_kw_cont(source_bytes[scan_index - 1]) {
                output_text.push(source_bytes[scan_index] as char);
                scan_index += 1;
                continue;
            }
            let identifier_byte_start = scan_index;
            let identifier_tail_limit = preprocess_byte_scan_round_limit(source_byte_length);
            for _identifier_byte_round in 0..identifier_tail_limit {
                if scan_index >= source_byte_length || !pp_kw_cont(source_bytes[scan_index]) {
                    break;
                }
                scan_index += 1;
            }
            let binder_identifier = &source_text[identifier_byte_start..scan_index];
            let whitespace_after_id_start = scan_index;
            let horizontal_whitespace_limit = preprocess_byte_scan_round_limit(source_byte_length);
            for _whitespace_round in 0..horizontal_whitespace_limit {
                if scan_index >= source_byte_length
                    || !matches!(source_bytes[scan_index], b' ' | b'\t' | b'\n' | b'\r')
                {
                    break;
                }
                scan_index += 1;
            }
            let whitespace_between_id_and_colons =
                &source_text[whitespace_after_id_start..scan_index];
            let is_triple_colon = scan_index + 3 <= source_byte_length
                && &source_bytes[scan_index..scan_index + 3] == b":::"
                && source_bytes.get(scan_index + 3).copied() != Some(b':');
            let is_double_colon = !is_triple_colon
                && scan_index + 2 <= source_byte_length
                && &source_bytes[scan_index..scan_index + 2] == b"::"
                && source_bytes.get(scan_index + 2).copied() != Some(b':');
            match (is_triple_colon, is_double_colon) {
                (true, _) | (_, true) => {
                    let colon_token: &'static str = match is_triple_colon {
                        true => ":::",
                        false => "::",
                    };
                    scan_index += colon_token.len();
                    let whitespace_after_colons_start = scan_index;
                    let after_colon_ws_limit = preprocess_byte_scan_round_limit(source_byte_length);
                    for _after_colon_ws_round in 0..after_colon_ws_limit {
                        if scan_index >= source_byte_length
                            || !matches!(source_bytes[scan_index], b' ' | b'\t')
                        {
                            break;
                        }
                        scan_index += 1;
                    }
                    let whitespace_after_colons =
                        &source_text[whitespace_after_colons_start..scan_index];
                    let kind_expression_start = scan_index;
                    let mut kind_paren_depth = 0i32;
                    let mut found_top_level_arrow = false;
                    let mut arrow_byte_index = scan_index;
                    let mut kind_scan_index = scan_index;
                    let kind_scan_limit = preprocess_byte_scan_round_limit(source_byte_length);
                    for _kind_scan_round in 0..kind_scan_limit {
                        if kind_scan_index >= source_byte_length {
                            break;
                        }
                        if kind_scan_index + 1 < source_byte_length
                            && source_bytes[kind_scan_index] == b'('
                            && source_bytes[kind_scan_index + 1] == b'*'
                        {
                            kind_scan_index = skip_ml_comment_bytes(
                                source_bytes,
                                kind_scan_index + 2,
                                source_byte_length,
                            );
                            continue;
                        }
                        if source_bytes[kind_scan_index] == b'"' {
                            kind_scan_index = skip_string_bytes(
                                source_bytes,
                                kind_scan_index + 1,
                                source_byte_length,
                            );
                            continue;
                        }
                        match source_bytes[kind_scan_index] {
                            b'(' | b'[' | b'{' => {
                                kind_paren_depth += 1;
                                kind_scan_index += 1;
                            }
                            b')' | b']' | b'}' => {
                                kind_paren_depth -= 1;
                                if kind_paren_depth < 0 {
                                    break;
                                }
                                kind_scan_index += 1;
                            }
                            _other
                                if kind_paren_depth == 0
                                    && kind_scan_index + 2 <= source_byte_length
                                    && &source_bytes[kind_scan_index..kind_scan_index + 2]
                                        == b"->" =>
                            {
                                found_top_level_arrow = true;
                                arrow_byte_index = kind_scan_index;
                                break;
                            }
                            _other
                                if kind_paren_depth == 0
                                    && matches!(
                                        source_bytes[kind_scan_index],
                                        b',' | b'=' | b'|' | b';'
                                    ) =>
                            {
                                break;
                            }
                            _other => {
                                kind_scan_index += 1;
                            }
                        }
                    }
                    match found_top_level_arrow {
                        true => {
                            let kind_expression_text =
                                source_text[kind_expression_start..arrow_byte_index].trim_end();
                            output_text.push('[');
                            output_text.push_str(binder_identifier);
                            output_text.push_str(whitespace_between_id_and_colons);
                            output_text.push_str(colon_token);
                            output_text.push_str(whitespace_after_colons);
                            output_text.push_str(kind_expression_text);
                            output_text.push_str("] -> ");
                            scan_index = arrow_byte_index + 2;
                            let spaces_after_arrow_limit =
                                preprocess_byte_scan_round_limit(source_byte_length);
                            for _spaces_after_arrow in 0..spaces_after_arrow_limit {
                                if scan_index >= source_byte_length
                                    || !matches!(source_bytes[scan_index], b' ' | b'\t')
                                {
                                    break;
                                }
                                scan_index += 1;
                            }
                        }
                        false => {
                            output_text.push_str(binder_identifier);
                            output_text.push_str(whitespace_between_id_and_colons);
                            output_text.push_str(colon_token);
                            output_text.push_str(whitespace_after_colons);
                        }
                    }
                    continue;
                }
                (false, false) => {
                    output_text.push_str(binder_identifier);
                    output_text.push_str(whitespace_between_id_and_colons);
                    continue;
                }
            }
        }
        let next_char = source_text[scan_index..].chars().next().unwrap_or('\0');
        match next_char {
            '[' => square_bracket_depth += 1,
            ']' => square_bracket_depth -= 1,
            _ => {}
        }
        output_text.push(next_char);
        scan_index += next_char.len_utf8();
    }
    output_text
}

/// Strip SQL table-constraint continuation lines from `.ur` source.
///
/// In Ur/Web, `table name : {fields}` declarations may be followed by indented
/// SQL constraint clauses (`PRIMARY KEY ...`, `CONSTRAINT ...`, `UNIQUE ...`, `CHECK ...`).
/// These clauses are not part of the Ur/Web AST but are SQL DDL extras.  The Rust
/// parser would otherwise consume the UIDENT tokens as constructor applications of
/// the table type.  Stripping them here keeps the grammar simple.
///
/// We replace each constraint line with a blank line to preserve line numbers.
///
/// # Arguments
///
/// * `src` — `.ur` source containing `table` declarations.
///
/// # Returns
///
/// Source with constraint-only lines blanked (line count preserved).
pub fn strip_table_constraints(src: &str) -> String {
    fn is_constraint_line(trimmed: &str) -> bool {
        trimmed.starts_with("PRIMARY ")
            || trimmed.starts_with("PRIMARY\t")
            || trimmed.starts_with("CONSTRAINT ")
            || trimmed.starts_with("CONSTRAINT\t")
            || trimmed.starts_with("UNIQUE ")
            || trimmed.starts_with("UNIQUE\t")
            || trimmed.starts_with("CHECK ")
            || trimmed.starts_with("CHECK\t")
    }

    let mut result = String::with_capacity(src.len());
    for line in src.split('\n') {
        let trimmed = line.trim_start();
        if !trimmed.is_empty() && is_constraint_line(trimmed) {
            // Replace with blank line preserving line count
            result.push('\n');
        } else {
            result.push_str(line);
            result.push('\n');
        }
    }
    // Remove the trailing extra newline we added (split produces N+1 pieces for N newlines)
    if (result.ends_with('\n') && !src.ends_with('\n'))
        || (result.ends_with("\n\n") && src.ends_with('\n'))
    {
        result.pop();
    }
    result
}

fn pp_kw_word_at(b: &[u8], i: usize, n: usize, word: &[u8]) -> bool {
    if i + word.len() > n || &b[i..i + word.len()] != word {
        return false;
    }
    if i > 0 && pp_kw_cont(b[i - 1]) {
        return false;
    }
    let after = i + word.len();
    if after < n && pp_kw_cont(b[after]) {
        return false;
    }
    true
}

/// Rewrite SQL-context expression splices `{expr}` → `(expr)` when the content is NOT a record.
///
/// Ur/Web allows `{expr}` inside SQL expressions (SELECT/WHERE/etc.) to splice a Ur/Web value.
/// The LR(1) grammar can't distinguish `{field = val}` (record) from `{expr}` (SQL splice)
/// in a single lookahead. This pass converts the SQL-splice form to `(expr)` which is
/// unambiguously a parenthesized expression.
///
/// Heuristic: a `{...}` block is a SQL splice if, after skipping whitespace/comments, the first
/// non-ws token is NOT followed by `=` (record field separator) and is NOT `...` or `}`.
///
/// # Arguments
///
/// * `input` — `.ur` source with SQL splices.
///
/// # Returns
///
/// Source where eligible `{...}` become `(...)`.
pub fn rewrite_sql_brace_splices(source_text: &str) -> String {
    let source_bytes = source_text.as_bytes();
    let source_byte_length = source_bytes.len();
    let mut output_text = String::with_capacity(source_byte_length);
    let mut scan_index = 0usize;
    let outer_limit = preprocess_byte_scan_round_limit(source_byte_length);
    for _outer_round in 0..outer_limit {
        if scan_index >= source_byte_length {
            break;
        }
        if scan_index + 1 < source_byte_length
            && source_bytes[scan_index] == b'('
            && source_bytes[scan_index + 1] == b'*'
        {
            let comment_start = scan_index;
            scan_index = skip_ml_comment_bytes(source_bytes, scan_index + 2, source_byte_length);
            output_text.push_str(&source_text[comment_start..scan_index]);
            continue;
        }
        if source_bytes[scan_index] == b'"' {
            let string_start = scan_index;
            scan_index = skip_string_bytes(source_bytes, scan_index + 1, source_byte_length);
            output_text.push_str(&source_text[string_start..scan_index]);
            continue;
        }
        if source_bytes[scan_index] != b'{' {
            let unicode_char = source_text[scan_index..].chars().next().unwrap_or('\0');
            output_text.push(unicode_char);
            scan_index += unicode_char.len_utf8();
            continue;
        }
        let mut after_brace_index = scan_index + 1;
        let ws1_limit = preprocess_byte_scan_round_limit(source_byte_length);
        for _ws_round in 0..ws1_limit {
            if after_brace_index >= source_byte_length
                || !pp_urs_is_ws!(source_bytes[after_brace_index])
            {
                break;
            }
            after_brace_index += 1;
        }
        if after_brace_index + 1 < source_byte_length
            && source_bytes[after_brace_index] == b'('
            && source_bytes[after_brace_index + 1] == b'*'
        {
            after_brace_index =
                skip_ml_comment_bytes(source_bytes, after_brace_index + 2, source_byte_length);
            let ws2_limit = preprocess_byte_scan_round_limit(source_byte_length);
            for _ws2_round in 0..ws2_limit {
                if after_brace_index >= source_byte_length
                    || !pp_urs_is_ws!(source_bytes[after_brace_index])
                {
                    break;
                }
                after_brace_index += 1;
            }
        }
        let treat_brace_block_as_sql_splice: bool = match after_brace_index >= source_byte_length {
            true => false,
            false => match source_bytes[after_brace_index] {
                b'[' | b'}' => false,
                _first_byte
                    if after_brace_index + 2 < source_byte_length
                        && &source_bytes[after_brace_index..after_brace_index + 3] == b"..." =>
                {
                    false
                }
                first_byte if first_byte.is_ascii_alphabetic() || first_byte == b'_' => {
                    let mut after_ident_index = after_brace_index + 1;
                    let ident_tail_limit = preprocess_byte_scan_round_limit(source_byte_length);
                    for _ident_tail in 0..ident_tail_limit {
                        if after_ident_index >= source_byte_length
                            || !(source_bytes[after_ident_index].is_ascii_alphanumeric()
                                || source_bytes[after_ident_index] == b'_'
                                || source_bytes[after_ident_index] == b'\'')
                        {
                            break;
                        }
                        after_ident_index += 1;
                    }
                    let after_ident_ws_limit = preprocess_byte_scan_round_limit(source_byte_length);
                    for _after_ident_ws in 0..after_ident_ws_limit {
                        if after_ident_index >= source_byte_length
                            || !pp_urs_is_ws!(source_bytes[after_ident_index])
                        {
                            break;
                        }
                        after_ident_index += 1;
                    }
                    match (
                        after_ident_index < source_byte_length
                            && source_bytes[after_ident_index] == b'=',
                        after_ident_index + 1 < source_byte_length,
                        source_bytes.get(after_ident_index + 1).copied(),
                    ) {
                        (true, true, Some(b'>')) | (true, true, Some(b'=')) => true,
                        (true, _, _) => false,
                        _ => true,
                    }
                }
                _starts_like_expression => true,
            },
        };
        match treat_brace_block_as_sql_splice {
            false => {
                output_text.push('{');
                scan_index += 1;
            }
            true => {
                output_text.push('(');
                scan_index += 1;
                let mut brace_paren_depth = 1i32;
                let depth_limit = preprocess_byte_scan_round_limit(source_byte_length);
                for _depth_round in 0..depth_limit {
                    if scan_index >= source_byte_length || brace_paren_depth <= 0 {
                        break;
                    }
                    match (
                        scan_index + 1 < source_byte_length,
                        source_bytes.get(scan_index).copied(),
                        source_bytes.get(scan_index + 1).copied(),
                    ) {
                        (true, Some(b'('), Some(b'*')) => {
                            let copy_start = scan_index;
                            scan_index = skip_ml_comment_bytes(
                                source_bytes,
                                scan_index + 2,
                                source_byte_length,
                            );
                            output_text.push_str(&source_text[copy_start..scan_index]);
                        }
                        (_, Some(b'"'), _) => {
                            let copy_start = scan_index;
                            scan_index =
                                skip_string_bytes(source_bytes, scan_index + 1, source_byte_length);
                            output_text.push_str(&source_text[copy_start..scan_index]);
                        }
                        (_, Some(b'{'), _) => {
                            output_text.push('(');
                            brace_paren_depth += 1;
                            scan_index += 1;
                        }
                        (_, Some(b'}'), _) => {
                            brace_paren_depth -= 1;
                            output_text.push(')');
                            scan_index += 1;
                        }
                        _ => {
                            let unicode_char =
                                source_text[scan_index..].chars().next().unwrap_or('\0');
                            output_text.push(unicode_char);
                            scan_index += unicode_char.len_utf8();
                        }
                    }
                }
            }
        }
    }
    output_text
}

/// After `datatype` … `=`, rewrite constructor-list `|` and payload `of` to magic tokens so the
/// grammar need not share `|` / `of` with patterns and other constructs (LangSec / LALR).
/// Rewrite keyword `where` for signatures: `sgn_where` at paren depth 0, `sgn_subwhere` when
/// nested in `(...)`, so LR(1) can separate top-level vs inner `Sgn` boundaries.
///
/// # Arguments
///
/// * `input` — UTF-8 source containing signature `where` clauses.
///
/// # Returns
///
/// Transformed UTF-8 source.
pub fn rewrite_sgn_where(input: &str) -> String {
    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n.saturating_add(16));
    let mut i = 0usize;
    let mut paren_depth = 0i32;
    let cap = n.saturating_add(1);
    for _ in 0..cap {
        if i >= n {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'(' {
            paren_depth += 1;
            out.push('(');
            i += 1;
            continue;
        }
        if b[i] == b')' {
            paren_depth = (paren_depth - 1).max(0);
            out.push(')');
            i += 1;
            continue;
        }
        if pp_kw_word_at(b, i, n, b"where") {
            if paren_depth == 0 {
                out.push_str("sgn_where");
            } else {
                out.push_str("sgn_subwhere");
            }
            i += 5;
            continue;
        }
        let Some(ch) = input[i..].chars().next() else {
            break;
        };
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// After `datatype` `=`, rewrite constructor `|` / `of` to magic tokens for the LALRPOP grammar.
///
/// # Arguments
///
/// * `input` — Source containing `datatype` declarations.
///
/// # Returns
///
/// Transformed source.
pub fn rewrite_datatype_constructors(input: &str) -> String {
    /// Locates the first `=` at paren/bracket depth 0 in a `datatype` header (skips comments/strings).
    fn find_dtype_equals(
        input_text: &str,
        source_bytes: &[u8],
        mut scan_index: usize,
        source_byte_length: usize,
    ) -> Option<usize> {
        let mut paren_bracket_depth = 0i32;
        let scan_limit = preprocess_byte_scan_round_limit(source_byte_length);
        for _scan_round in 0..scan_limit {
            if scan_index >= source_byte_length {
                return None;
            }
            if scan_index + 1 < source_byte_length
                && source_bytes[scan_index] == b'('
                && source_bytes[scan_index + 1] == b'*'
            {
                scan_index =
                    skip_ml_comment_bytes(source_bytes, scan_index + 2, source_byte_length);
                continue;
            }
            if source_bytes[scan_index] == b'"' {
                scan_index = skip_string_bytes(source_bytes, scan_index + 1, source_byte_length);
                continue;
            }
            match source_bytes[scan_index] {
                b'(' | b'[' | b'{' => {
                    paren_bracket_depth += 1;
                    scan_index += 1;
                }
                b')' | b']' | b'}' => {
                    paren_bracket_depth = (paren_bracket_depth - 1).max(0);
                    scan_index += 1;
                }
                b'=' if paren_bracket_depth == 0 => return Some(scan_index),
                _other_byte => {
                    let utf8_width = match input_text
                        .get(scan_index..)
                        .and_then(|suffix| suffix.chars().next())
                    {
                        Some(ch) => ch.len_utf8(),
                        None => return None,
                    };
                    scan_index += utf8_width;
                }
            }
        }
        None
    }

    fn rewrite_dt_body(
        output_accumulator: &mut String,
        input_text: &str,
        source_bytes: &[u8],
        mut scan_index: usize,
        source_byte_length: usize,
    ) -> usize {
        let mut paren_bracket_depth = 0i32;
        let mut follows_uppercase_identifier = false;
        let scan_limit = preprocess_byte_scan_round_limit(source_byte_length);
        for _body_round in 0..scan_limit {
            if scan_index >= source_byte_length {
                break;
            }
            if scan_index + 1 < source_byte_length
                && source_bytes[scan_index] == b'('
                && source_bytes[scan_index + 1] == b'*'
            {
                let comment_copy_start = scan_index;
                scan_index =
                    skip_ml_comment_bytes(source_bytes, scan_index + 2, source_byte_length);
                output_accumulator.push_str(&input_text[comment_copy_start..scan_index]);
                continue;
            }
            if source_bytes[scan_index] == b'"' {
                let string_copy_start = scan_index;
                scan_index = skip_string_bytes(source_bytes, scan_index + 1, source_byte_length);
                output_accumulator.push_str(&input_text[string_copy_start..scan_index]);
                continue;
            }
            if paren_bracket_depth == 0
                && pp_kw_word_at(source_bytes, scan_index, source_byte_length, b"and")
            {
                if follows_uppercase_identifier {
                    output_accumulator.push_str(" dt_con0 ");
                }
                output_accumulator.push_str(" dt_done ");
                return scan_index;
            }
            if paren_bracket_depth == 0 && source_bytes[scan_index] == b';' {
                if follows_uppercase_identifier {
                    output_accumulator.push_str(" dt_con0 ");
                }
                output_accumulator.push_str(" dt_done ");
                return scan_index;
            }
            if paren_bracket_depth == 0 {
                for declaration_keyword in &[
                    b"datatype" as &[u8],
                    b"con",
                    b"val",
                    b"fun",
                    b"type",
                    b"class",
                    b"structure",
                    b"signature",
                    b"open",
                    b"constraint",
                    b"table",
                    b"sequence",
                    b"view",
                    b"cookie",
                    b"style",
                    b"task",
                    b"policy",
                    b"include",
                ] {
                    if pp_kw_word_at(
                        source_bytes,
                        scan_index,
                        source_byte_length,
                        declaration_keyword,
                    ) {
                        if follows_uppercase_identifier {
                            output_accumulator.push_str(" dt_con0 ");
                        }
                        output_accumulator.push_str(" dt_done ");
                        return scan_index;
                    }
                }
            }
            if paren_bracket_depth == 0 && source_bytes[scan_index] == b'|' {
                if follows_uppercase_identifier {
                    output_accumulator.push_str(" dt_con0 ");
                }
                output_accumulator.push_str(" dt_bar ");
                scan_index += 1;
                follows_uppercase_identifier = false;
                continue;
            }
            if paren_bracket_depth == 0
                && follows_uppercase_identifier
                && pp_kw_word_at(source_bytes, scan_index, source_byte_length, b"of")
            {
                output_accumulator.push_str(" dtype_of ");
                scan_index += 2;
                follows_uppercase_identifier = false;
                continue;
            }
            if paren_bracket_depth == 0 && source_bytes[scan_index].is_ascii_uppercase() {
                let uppercase_token_start = scan_index;
                scan_index += 1;
                let uident_tail_limit = preprocess_byte_scan_round_limit(source_byte_length);
                for _uident_tail in 0..uident_tail_limit {
                    if scan_index >= source_byte_length
                        || !(source_bytes[scan_index].is_ascii_alphanumeric()
                            || source_bytes[scan_index] == b'_'
                            || source_bytes[scan_index] == b'\'')
                    {
                        break;
                    }
                    scan_index += 1;
                }
                output_accumulator.push_str(&input_text[uppercase_token_start..scan_index]);
                follows_uppercase_identifier = true;
                continue;
            }
            if source_bytes[scan_index].is_ascii_whitespace() {
                output_accumulator.push(source_bytes[scan_index] as char);
                scan_index += 1;
                continue;
            }
            follows_uppercase_identifier = false;
            match source_bytes[scan_index] {
                b'(' | b'[' | b'{' => {
                    output_accumulator.push(source_bytes[scan_index] as char);
                    paren_bracket_depth += 1;
                    scan_index += 1;
                }
                b')' | b']' | b'}' => {
                    output_accumulator.push(source_bytes[scan_index] as char);
                    paren_bracket_depth = (paren_bracket_depth - 1).max(0);
                    scan_index += 1;
                }
                _other => {
                    let Some(unicode_char) = input_text[scan_index..].chars().next() else {
                        break;
                    };
                    output_accumulator.push(unicode_char);
                    scan_index += unicode_char.len_utf8();
                }
            }
        }
        if paren_bracket_depth == 0 {
            if follows_uppercase_identifier {
                output_accumulator.push_str(" dt_con0 ");
            }
            output_accumulator.push_str(" dt_done ");
        }
        scan_index
    }

    let b = input.as_bytes();
    let n = b.len();
    let mut out = String::with_capacity(n.saturating_add(64));
    let mut i = 0usize;
    let cap = n.saturating_add(1);
    for _ in 0..cap {
        if i >= n {
            break;
        }
        if i + 1 < n && b[i] == b'(' && b[i + 1] == b'*' {
            let start = i;
            i = skip_ml_comment_bytes(b, i + 2, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if b[i] == b'"' {
            let start = i;
            i = skip_string_bytes(b, i + 1, n);
            out.push_str(&input[start..i]);
            continue;
        }
        if pp_kw_word_at(b, i, n, b"datatype") {
            let start = i;
            i += b"datatype".len();
            if let Some(eq) = find_dtype_equals(input, b, i, n) {
                out.push_str(&input[start..eq]);
                out.push('=');
                i = eq + 1;
                i = rewrite_dt_body(&mut out, input, b, i, n);
                continue;
            }
            out.push_str(&input[start..i]);
            continue;
        }
        let Some(ch) = input[i..].chars().next() else {
            break;
        };
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

/// Pre-process a `.urs` source string to convert bare implicit constructor
/// quantifiers into bracketed form that the LR(1) grammar can parse without
/// conflicts.
///
/// Transforms:
///   `name :: KindAtom ->`   →  `[name :: KindAtom] ->`
///   `name ::: KindAtom ->`  →  `[name ::: KindAtom] ->`
///
/// KindAtom can be an identifier, `{...}` (record kind), or `(...)` (arrow
/// kind in parens).  Characters inside `(* *)` comments and `"..."` strings
/// are left untouched.
///
/// The transformation is only applied when the `IDENT ::` pattern appears
/// INSIDE a type expression, not as the subject of a declaration keyword
/// (`con`, `class`, `type`, `structure`, `signature`, `datatype`).
///
/// ## Signature `LTYPE` / `CON` alignment (`urweb.lex`)
/// The reference lexer maps `type` → `LTYPE` and `con` → `CON`. Bare abstract
/// `type t` and default `class c` lines would require optional-empty LR slices
/// next to `=` / `::` continuations. We rewrite **simple** lines (no `=`, no `::`)
/// so the CFG stays single-recognizer strict:
/// - `type t` → `con t :: Type`
/// - `class c` → `class c :: Type -> Type` (default kind, matching `SgiClassAbs`)
///
/// ## Signature `con` / `class` kind definitions (`sgn_def_con`)
/// After `:: Kind`, the grammar expects a dedicated keyword `sgn_def_con` before the
/// defining `Con` so `=` is not overloaded and no ε competes with the RHS. Source
/// files still write ordinary `=`; we rewrite the first defining `=` after `::` on
/// `con` / `class` lines to `sgn_def_con`.
///
/// Line-oriented pass (not yet composed into [`preprocess_urs`]); kept for tooling / future merge.
#[allow(dead_code)]
fn rewrite_sig_type_class_abstract_lines(input: &str) -> String {
    fn ident_head(rest: &str) -> Option<(String, &str)> {
        let mut it = rest.chars();
        let c0 = it.next()?;
        if !(c0.is_ascii_alphabetic() || c0 == '_') {
            return None;
        }
        let mut id = c0.to_string();
        for c in it.by_ref() {
            if c.is_ascii_alphanumeric() || c == '_' || c == '\'' {
                id.push(c);
            } else {
                break;
            }
        }
        let consumed = id.len();
        Some((id, &rest[consumed..]))
    }

    /// First single `=` in `s` that is not part of `==`, `=>`, `<=`, `>=`, `!=`, or `:=`.
    /// Replaced by `sgn_def_con` (see `rewrite_con_class_kind_def_eq`).
    fn find_defining_single_eq(line_text: &str) -> Option<usize> {
        let bytes = line_text.as_bytes();
        let byte_length = bytes.len();
        let mut byte_index = 0usize;
        let scan_limit = preprocess_byte_scan_round_limit(byte_length);
        for _equals_scan_round in 0..scan_limit {
            if byte_index >= byte_length {
                break;
            }
            if bytes[byte_index] != b'=' {
                byte_index += 1;
                continue;
            }
            let skip_width: Option<usize> = match (
                bytes.get(byte_index + 1).copied(),
                byte_index
                    .checked_sub(1)
                    .and_then(|previous_index| bytes.get(previous_index).copied()),
            ) {
                (Some(b'='), _) | (Some(b'>'), _) => Some(2usize),
                (_, Some(b'<')) | (_, Some(b'>')) | (_, Some(b'!')) | (_, Some(b':')) => {
                    Some(1usize)
                }
                _ => None,
            };
            match skip_width {
                Some(advance) => {
                    byte_index += advance;
                }
                None => return Some(byte_index),
            }
        }
        None
    }

    /// `con nm :: K` / `class nm :: K` without a defining RHS: insert `sgn_abs` before `::`
    /// so abstract and `sgn_def_con` definitions use disjoint grammar prefixes.
    /// Also handles lines prefixed by `dt_done ` from `rewrite_datatype_constructors`.
    fn rewrite_con_class_sgn_abs(trimmed: &str) -> Option<String> {
        if trimmed.contains("sgn_def_con") || trimmed.contains("sgn_abs") {
            return None;
        }
        // Strip dt_done prefix that rewrite_datatype_constructors may have prepended
        let (keep_prefix, s) = if let Some(r) = trimmed.strip_prefix("dt_done") {
            let r = r.trim_start();
            (&trimmed[..trimmed.len() - r.len()], r)
        } else {
            ("", trimmed)
        };
        if !(s.starts_with("con ") || s.starts_with("class ")) {
            return None;
        }
        if !s.contains("::") {
            return None;
        }
        let (kw, rest) = if let Some(r) = s.strip_prefix("con ") {
            ("con ", r)
        } else if let Some(r) = s.strip_prefix("class ") {
            ("class ", r)
        } else {
            return None;
        };
        let (id, after_id) = ident_head(rest)?;
        let after_ws = after_id.trim_start();
        if !after_ws.starts_with("::") {
            return None;
        }
        Some(format!("{keep_prefix}{kw}{id} sgn_abs {after_ws}"))
    }

    fn rewrite_con_class_kind_def_eq(trimmed: &str) -> Option<String> {
        if trimmed.contains("sgn_def_con") {
            return None;
        }
        if !(trimmed.starts_with("con ") || trimmed.starts_with("class ")) {
            return None;
        }
        let dc = trimmed.find("::")?;
        let after_colons = trimmed.get(dc + 2..)?;
        let eq_rel = find_defining_single_eq(after_colons)?;
        let abs = dc + 2 + eq_rel;
        let mut s = String::with_capacity(trimmed.len() + 1);
        s.push_str(&trimmed[..abs]);
        s.push_str(" sgn_def_con ");
        s.push_str(trimmed.get(abs + 1..).unwrap_or(""));
        Some(s)
    }

    let mut out = String::with_capacity(input.len().saturating_add(256));
    let lines: Vec<&str> = input.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        let trimmed = line.trim_start();
        let indent_len = line.len().saturating_sub(trimmed.len());
        let indent = &line[..indent_len];

        let mut new_trimmed = trimmed.to_string();
        if !new_trimmed.contains('=') && !new_trimmed.contains("::") {
            if let Some(rest) = new_trimmed.strip_prefix("type ") {
                if let Some((id, after)) = ident_head(rest) {
                    let after_trim = after.trim_start();
                    if after_trim.is_empty() || after_trim.starts_with("(*") {
                        new_trimmed = format!("con {id} :: Type{after}");
                    }
                }
            } else if let Some(rest) = new_trimmed.strip_prefix("class ") {
                if let Some((id, after)) = ident_head(rest) {
                    let after_trim = after.trim_start();
                    if after_trim.is_empty() || after_trim.starts_with("(*") {
                        new_trimmed = format!("class {id} :: Type -> Type{after}");
                    }
                }
            }
        }
        if let Some(nt) = rewrite_con_class_kind_def_eq(&new_trimmed) {
            new_trimmed = nt;
        }
        if let Some(nt) = rewrite_con_class_sgn_abs(&new_trimmed) {
            new_trimmed = nt;
        }
        out.push_str(indent);
        out.push_str(&new_trimmed);
    }
    if input.ends_with('\n') && !lines.is_empty() {
        out.push('\n');
    }
    out
}

/// Preprocessed excerpt of `lib/ur/basis.urs` around byte `pos` (dev helpers / mutation tests).
///
/// # Arguments
///
/// * `pos` — Byte index into the preprocessed buffer.
/// * `before` / `after` — Bytes to include on each side.
///
/// # Returns
///
/// Slice of the preprocessed basis as `String`.
///
/// # Errors
///
/// If `basis.urs` cannot be read from disk.
pub fn basis_urs_preprocessed_window(
    pos: usize,
    before: usize,
    after: usize,
) -> std::io::Result<String> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/ur/basis.urs");
    let src = std::fs::read_to_string(path)?;
    let pp = preprocess_urs(&src);
    let start = pos.saturating_sub(before);
    let end = (pos + after).min(pp.len());
    Ok(pp[start..end].to_string())
}

/// Replace `( * )` (SQL aggregate wildcard) with `( sql_star )` so the grammar doesn't need
/// `"*"` as an expression token (which conflicts with multiplication).
/// Only replaces `*` when it is the sole non-whitespace content between a matching `(…)` pair
/// (and the `(` is NOT the start of a comment `(*`).
///
/// # Returns
///
/// Source with `( sql_star )` placeholders.
pub fn rewrite_sql_star(source_text: &str) -> String {
    let source_bytes = source_text.as_bytes();
    let source_byte_length = source_bytes.len();
    let mut output_text = String::with_capacity(source_byte_length);
    let mut scan_index = 0usize;
    let outer_limit = preprocess_byte_scan_round_limit(source_byte_length);
    for _sql_star_scan_round in 0..outer_limit {
        if scan_index >= source_byte_length {
            break;
        }
        if scan_index + 1 < source_byte_length
            && source_bytes[scan_index] == b'('
            && source_bytes[scan_index + 1] == b'*'
        {
            let comment_start = scan_index;
            scan_index = skip_ml_comment_bytes(source_bytes, scan_index + 2, source_byte_length);
            output_text.push_str(&source_text[comment_start..scan_index]);
            continue;
        }
        if source_bytes[scan_index] == b'"' {
            let string_start = scan_index;
            scan_index = skip_string_bytes(source_bytes, scan_index + 1, source_byte_length);
            output_text.push_str(&source_text[string_start..scan_index]);
            continue;
        }
        if source_bytes[scan_index] == b'(' {
            let mut after_open_paren = scan_index + 1;
            let ws_after_open_limit = preprocess_byte_scan_round_limit(source_byte_length);
            for _skip_ws_after_paren in 0..ws_after_open_limit {
                if after_open_paren >= source_byte_length
                    || !matches!(source_bytes[after_open_paren], b' ' | b'\t' | b'\n' | b'\r')
                {
                    break;
                }
                after_open_paren += 1;
            }
            if after_open_paren < source_byte_length && source_bytes[after_open_paren] == b'*' {
                let mut after_star = after_open_paren + 1;
                let ws_after_star_limit = preprocess_byte_scan_round_limit(source_byte_length);
                for _skip_ws_after_star in 0..ws_after_star_limit {
                    if after_star >= source_byte_length
                        || !matches!(source_bytes[after_star], b' ' | b'\t' | b'\n' | b'\r')
                    {
                        break;
                    }
                    after_star += 1;
                }
                if after_star < source_byte_length && source_bytes[after_star] == b')' {
                    output_text.push_str("( sql_star )");
                    scan_index = after_star + 1;
                    continue;
                }
            }
        }
        let unicode_char = source_text[scan_index..].chars().next().unwrap_or('\0');
        output_text.push(unicode_char);
        scan_index += unicode_char.len_utf8();
    }
    output_text
}

/// Convert `{expr}` → `(expr)` when the `{` immediately follows a SQL keyword that introduces
/// a boolean or expression context: `WHERE`, `HAVING`, `ON` (case-sensitive, as Ur/Web SQL uses
/// uppercase).  Only the outermost braces are rewritten; inner `{...}` remains untouched.
/// Record literals (`{field = ...}`) and text-splices (`{[...]}`) are never touched.
///
/// # Returns
///
/// Transformed UTF-8 source.
pub fn rewrite_sql_keyword_brace_splices(source_text: &str) -> String {
    let source_bytes = source_text.as_bytes();
    let source_byte_length = source_bytes.len();
    let mut output_text = String::with_capacity(source_byte_length);
    let mut scan_index = 0usize;
    const SQL_KEYWORDS_AFTER_WHICH_BRACE_IS_SPLICE: &[&[u8]] = &[b"WHERE", b"HAVING", b"ON"];
    let outer_scan_limit = preprocess_byte_scan_round_limit(source_byte_length);
    for _keyword_brace_round in 0..outer_scan_limit {
        if scan_index >= source_byte_length {
            break;
        }
        if scan_index + 1 < source_byte_length
            && source_bytes[scan_index] == b'('
            && source_bytes[scan_index + 1] == b'*'
        {
            let comment_span_start = scan_index;
            scan_index = skip_ml_comment_bytes(source_bytes, scan_index + 2, source_byte_length);
            output_text.push_str(&source_text[comment_span_start..scan_index]);
            continue;
        }
        if source_bytes[scan_index] == b'"' {
            let string_span_start = scan_index;
            scan_index = skip_string_bytes(source_bytes, scan_index + 1, source_byte_length);
            output_text.push_str(&source_text[string_span_start..scan_index]);
            continue;
        }
        let mut consumed_sql_keyword_branch = false;
        for keyword_bytes in SQL_KEYWORDS_AFTER_WHICH_BRACE_IS_SPLICE {
            let keyword_byte_length = keyword_bytes.len();
            if scan_index + keyword_byte_length > source_byte_length {
                continue;
            }
            if !source_bytes[scan_index..scan_index + keyword_byte_length]
                .eq_ignore_ascii_case(keyword_bytes)
            {
                continue;
            }
            let keyword_at_token_start = scan_index == 0
                || ({
                    let previous_byte = source_bytes[scan_index - 1];
                    !previous_byte.is_ascii_alphanumeric() && previous_byte != b'_'
                });
            let keyword_at_token_end = scan_index + keyword_byte_length >= source_byte_length
                || ({
                    let next_byte = source_bytes[scan_index + keyword_byte_length];
                    !next_byte.is_ascii_alphanumeric() && next_byte != b'_'
                });
            match (keyword_at_token_start, keyword_at_token_end) {
                (true, true) => {}
                _ => continue,
            }
            output_text.push_str(&source_text[scan_index..scan_index + keyword_byte_length]);
            scan_index += keyword_byte_length;
            let whitespace_after_keyword_start = scan_index;
            let ws_limit = preprocess_byte_scan_round_limit(source_byte_length);
            for _after_keyword_ws in 0..ws_limit {
                if scan_index >= source_byte_length
                    || !matches!(source_bytes[scan_index], b' ' | b'\t' | b'\n' | b'\r')
                {
                    break;
                }
                scan_index += 1;
            }
            output_text.push_str(&source_text[whitespace_after_keyword_start..scan_index]);
            if scan_index < source_byte_length && source_bytes[scan_index] == b'{' {
                let mut peek_index = scan_index + 1;
                let comment_peek_limit = preprocess_byte_scan_round_limit(source_byte_length);
                for _leading_comment_round in 0..comment_peek_limit {
                    if peek_index + 1 >= source_byte_length
                        || !(source_bytes[peek_index] == b'('
                            && source_bytes[peek_index + 1] == b'*')
                    {
                        break;
                    }
                    peek_index =
                        skip_ml_comment_bytes(source_bytes, peek_index + 2, source_byte_length);
                    let after_comment_ws_limit =
                        preprocess_byte_scan_round_limit(source_byte_length);
                    for _after_comment_ws in 0..after_comment_ws_limit {
                        if peek_index >= source_byte_length
                            || !matches!(source_bytes[peek_index], b' ' | b'\t' | b'\n' | b'\r')
                        {
                            break;
                        }
                        peek_index += 1;
                    }
                }
                let inside_brace_ws_limit = preprocess_byte_scan_round_limit(source_byte_length);
                for _inside_brace_ws in 0..inside_brace_ws_limit {
                    if peek_index >= source_byte_length
                        || !matches!(source_bytes[peek_index], b' ' | b'\t' | b'\n' | b'\r')
                    {
                        break;
                    }
                    peek_index += 1;
                }
                let treat_brace_as_sql_splice: bool = match peek_index >= source_byte_length {
                    true => false,
                    false => match source_bytes[peek_index] {
                        b'[' | b'}' => false,
                        _ellipsis
                            if peek_index + 2 < source_byte_length
                                && &source_bytes[peek_index..peek_index + 3] == b"..." =>
                        {
                            false
                        }
                        head if head.is_ascii_alphabetic() || head == b'_' => {
                            let mut after_ident_index = peek_index + 1;
                            let ident_suffix_limit =
                                preprocess_byte_scan_round_limit(source_byte_length);
                            for _ident_suffix in 0..ident_suffix_limit {
                                if after_ident_index >= source_byte_length
                                    || !(source_bytes[after_ident_index].is_ascii_alphanumeric()
                                        || source_bytes[after_ident_index] == b'_'
                                        || source_bytes[after_ident_index] == b'\'')
                                {
                                    break;
                                }
                                after_ident_index += 1;
                            }
                            let ident_ws_limit =
                                preprocess_byte_scan_round_limit(source_byte_length);
                            for _after_ident_ws in 0..ident_ws_limit {
                                if after_ident_index >= source_byte_length
                                    || !matches!(source_bytes[after_ident_index], b' ' | b'\t')
                                {
                                    break;
                                }
                                after_ident_index += 1;
                            }
                            match (
                                after_ident_index < source_byte_length
                                    && source_bytes[after_ident_index] == b'=',
                                after_ident_index + 1 < source_byte_length,
                                source_bytes.get(after_ident_index + 1).copied(),
                            ) {
                                (true, true, Some(b'>')) | (true, true, Some(b'=')) => true,
                                (true, _, _) => false,
                                _ => true,
                            }
                        }
                        _expression_like => true,
                    },
                };
                if treat_brace_as_sql_splice {
                    output_text.push('(');
                    scan_index += 1;
                    let mut brace_nesting_depth = 1i32;
                    let depth_limit = preprocess_byte_scan_round_limit(source_byte_length);
                    for _brace_copy_round in 0..depth_limit {
                        if scan_index >= source_byte_length || brace_nesting_depth <= 0 {
                            break;
                        }
                        match (
                            scan_index + 1 < source_byte_length,
                            source_bytes.get(scan_index).copied(),
                            source_bytes.get(scan_index + 1).copied(),
                        ) {
                            (true, Some(b'('), Some(b'*')) => {
                                let copy_start = scan_index;
                                scan_index = skip_ml_comment_bytes(
                                    source_bytes,
                                    scan_index + 2,
                                    source_byte_length,
                                );
                                output_text.push_str(&source_text[copy_start..scan_index]);
                            }
                            (_, Some(b'"'), _) => {
                                let copy_start = scan_index;
                                scan_index = skip_string_bytes(
                                    source_bytes,
                                    scan_index + 1,
                                    source_byte_length,
                                );
                                output_text.push_str(&source_text[copy_start..scan_index]);
                            }
                            (_, Some(b'{'), _) => {
                                output_text.push('{');
                                brace_nesting_depth += 1;
                                scan_index += 1;
                            }
                            (_, Some(b'}'), _) => {
                                brace_nesting_depth -= 1;
                                match brace_nesting_depth.cmp(&0) {
                                    std::cmp::Ordering::Greater => output_text.push('}'),
                                    _ => output_text.push(')'),
                                }
                                scan_index += 1;
                            }
                            _ => {
                                let ch = source_text[scan_index..].chars().next().unwrap_or('\0');
                                output_text.push(ch);
                                scan_index += ch.len_utf8();
                            }
                        }
                    }
                }
            }
            consumed_sql_keyword_branch = true;
            break;
        }
        if consumed_sql_keyword_branch {
            continue;
        }
        let unicode_char = source_text[scan_index..].chars().next().unwrap_or('\0');
        output_text.push(unicode_char);
        scan_index += unicode_char.len_utf8();
    }
    output_text
}

/// Preprocess `.ur` source exactly like [`parse_ur`] before the lexer (rewrites only, no parse).
///
/// Language server semantic tokens and similar tools use this for a consistent surface.
///
/// # Returns
///
/// Transformed source string.
pub fn preprocess_ur_for_parse(src: &str) -> String {
    sql_compat::rewrite_legacy_sql_placeholders(&rewrite_case_expressions(&rewrite_sgn_where(
        &rewrite_datatype_constructors(&rewrite_bare_kind_binders(&rewrite_sql_star(
            &rewrite_sql_keyword_brace_splices(&strip_table_constraints(src)),
        ))),
    )))
}

/// Turn a LALRPOP [`lalrpop_util::ParseError`] into a short user-facing line (not full `Debug`).
///
/// # Arguments
///
/// * `parse_error` — Parser failure after [`lexical_analyzer::XmlAwareLexer`].
///
/// # Returns
///
/// One or two sentences suitable for catalog placeholder `{1}` on parse failures.
#[cfg(generated_parser)]
fn format_parse_error_for_user(
    parse_error: &lalrpop_util::ParseError<
        usize,
        lexical_analyzer::Token,
        lexical_analyzer::LexError,
    >,
) -> String {
    use lalrpop_util::ParseError;
    match parse_error {
        ParseError::InvalidToken { location } => {
            format!("invalid token at byte offset {location}")
        }
        ParseError::UnrecognizedEof { location, expected } => {
            format!(
                "unexpected end of input at byte {location}; expected one of: {}",
                expected_symbol_labels::join_friendly_expected_labels(expected),
            )
        }
        ParseError::UnrecognizedToken { token, expected } => {
            let (start, unexpected_token, end) = token;
            format!(
                "unexpected token {unexpected_token} at bytes {start}–{end}; expected one of: {}",
                expected_symbol_labels::join_friendly_expected_labels(expected),
            )
        }
        ParseError::ExtraToken { token } => {
            let (start, extra_token, end) = token;
            format!("extra token {extra_token} at bytes {start}–{end}")
        }
        ParseError::User { error } => {
            format!("lexical error: {}", error.message)
        }
    }
}

/// Parse one `.ur` module after the standard preprocessor chain and LALRPOP parse.
///
/// # Arguments
///
/// * `_filename` — Label for diagnostics (may be a path or virtual `file:` string).
/// * `source` — Raw UTF-8 module text.
/// * `errors` — Receives a plain or spanned error on failure.
/// * `project_db` — Effective database / LangSec profile for this compile (`ur.toml`, `.urp`, CLI).
///
/// # Returns
///
/// Parsed [`File`] (declaration vector) or `None` when the parser fails or code was built without `generated_parser`.
///
/// # Errors
///
/// Does not return `Result`; failures are appended to `errors` and yield `None`.
pub fn parse_ur(
    _filename: &str,
    source: &str,
    errors: &mut ErrorReporter,
    project_db: crate::db::ProjectDb,
) -> Option<File> {
    #[cfg(generated_parser)]
    {
        let _parse_profile = project_db.langsec_parse_profile();
        let _ = (_parse_profile, project_db); // LangSec tiers branch on profile + db
        let pre = preprocess_ur_for_parse(source);
        let lexer = lexical_analyzer::XmlAwareLexer::new(&pre);
        match grammar::FileParser::new().parse(lexer) {
            Ok(mut file) => {
                crate::source::attach_file_label_to_source_file(&mut file, _filename, &pre);
                repair_misparsed_lambda_annotation_file(&mut file);
                if let Err(detail) = sql_compat::repair_sql_placeholders_in_file(&mut file) {
                    let label_span = Span {
                        file: _filename.to_string(),
                        ..Span::dummy()
                    };
                    let payload = DiagnosticPayload::new(
                        DiagnosticId::ParseUrSyntaxFailed,
                        vec![
                            _filename.to_string(),
                            format!("legacy SQL compatibility rewrite failed: {detail}"),
                            String::new(),
                        ],
                    );
                    errors.report(CompileError::parse_at_with_hint(
                        label_span,
                        payload,
                        DiagnosticId::HintParseUrSyntax,
                        vec![],
                    ));
                    return None;
                }
                Some(file)
            }
            Err(parse_error) => {
                let detail = format_parse_error_for_user(&parse_error);
                let label_span = Span {
                    file: _filename.to_string(),
                    ..Span::dummy()
                };
                let markup_heuristic = pre.contains("<xml") || pre.contains("<XML");
                let xml_note = if markup_heuristic {
                    format!(
                        "\n\n{}",
                        render_diagnostic_body(
                            &DiagnosticPayload::new(DiagnosticId::ParseUrXmlHeuristicNote, vec![]),
                            errors.diagnostic_locale,
                        )
                    )
                } else {
                    String::new()
                };
                let payload = DiagnosticPayload::new(
                    DiagnosticId::ParseUrSyntaxFailed,
                    vec![_filename.to_string(), detail, xml_note],
                );
                if markup_heuristic {
                    errors.report(CompileError::xml_at_with_hint(
                        label_span,
                        payload,
                        DiagnosticId::HintParseUrSyntax,
                        vec![],
                    ));
                } else {
                    errors.report(CompileError::parse_at_with_hint(
                        label_span,
                        payload,
                        DiagnosticId::HintParseUrSyntax,
                        vec![],
                    ));
                }
                None
            }
        }
    }
    #[cfg(not(generated_parser))]
    {
        let _ = (_filename, source, project_db);
        errors.report(CompileError::Plain(DiagnosticPayload::new(
            DiagnosticId::ParserNotLinkedUr,
            vec![],
        )));
        None
    }
}

/// Count top-level declarations by parsing `source` as `.ur` with default [`crate::db::ProjectDb`].
///
/// # Arguments
///
/// * `virtual_path` — Filename label for [`parse_ur`].
/// * `source` — Module source.
/// * `errors` — Parse error sink.
///
/// # Returns
///
/// `Some(len)` of the top-level vector, or `None` on parse failure.
pub fn parse_top_level_decl_count(
    virtual_path: &str,
    source: &str,
    errors: &mut ErrorReporter,
) -> Option<usize> {
    parse_ur(
        virtual_path,
        source,
        errors,
        crate::db::ProjectDb::default(),
    )
    .map(|f| f.len())
}

/// Parse a `.urs` signature file after [`preprocess_urs`].
///
/// # Arguments
///
/// * `_filename` — Label for error messages.
/// * `source` — Raw signature source.
/// * `errors` — Diagnostic sink.
///
/// # Returns
///
/// Vector of located signature items, or `None` on failure / missing generated parser.
///
/// # Errors
///
/// Recorded in `errors`; function returns `None`.
pub fn parse_urs(
    _filename: &str,
    source: &str,
    errors: &mut ErrorReporter,
) -> Option<Vec<LocSgnItem>> {
    #[cfg(generated_parser)]
    {
        // Pre-process to convert bare implicit quantifiers `nm :: Kind ->`
        // to bracketed form `[nm :: Kind] ->` which the LR grammar handles.
        let preprocessed = preprocess_urs(source);
        let lexer = lexical_analyzer::XmlAwareLexer::new(&preprocessed);
        match grammar::SgnItemsParser::new().parse(lexer) {
            Ok(mut items) => {
                crate::source::attach_file_label_to_signature_items(
                    &mut items,
                    _filename,
                    &preprocessed,
                );
                Some(items)
            }
            Err(parse_error) => {
                let detail = format_parse_error_for_user(&parse_error);
                let label_span = Span {
                    file: _filename.to_string(),
                    ..Span::dummy()
                };
                errors.report(CompileError::parse_at_with_hint(
                    label_span,
                    DiagnosticPayload::new(
                        DiagnosticId::ParseUrsSyntaxFailed,
                        vec![_filename.to_string(), detail],
                    ),
                    DiagnosticId::HintParseUrsSyntax,
                    vec![],
                ));
                None
            }
        }
    }
    #[cfg(not(generated_parser))]
    {
        let _ = (_filename, source);
        errors.report(CompileError::Plain(DiagnosticPayload::new(
            DiagnosticId::ParserNotLinkedUrs,
            vec![],
        )));
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preprocess_urs_low_fuel_appends_remainder_without_panic() {
        let src = "val f : nm :: Type -> int -> int\n";
        test_set_preprocess_urs_fuel_override(Some(8));
        let out = preprocess_urs(src);
        test_set_preprocess_urs_fuel_override(None);
        assert!(
            !out.is_empty(),
            "fuel exhaustion must return partial output + suffix, not panic"
        );
        assert!(
            out.contains("nm") || out.contains("val"),
            "output should retain source text: {out:?}"
        );
    }

    #[test]
    fn parse_ur_returns_none_without_generated_parser() {
        let mut errors = ErrorReporter::new_silent();
        let result = parse_ur(
            "test.ur",
            "val x = 1",
            &mut errors,
            crate::db::ProjectDb::default(),
        );
        #[cfg(not(generated_parser))]
        {
            assert!(result.is_none());
            assert!(errors.has_errors());
        }
        #[cfg(generated_parser)]
        {
            let file = result.expect("val x = 1 should parse");
            assert_eq!(file.len(), 1, "single top-level val decl");
        }
    }

    /// LALRPOP actions use empty `Span::file`; post-parse attach must fill it for diagnostics.
    #[test]
    #[cfg(generated_parser)]
    fn parse_ur_sets_file_on_inner_spans() {
        use crate::source::Decl;
        let mut errors = ErrorReporter::new_silent();
        let path = "dir/Example.ur";
        let file = parse_ur(
            path,
            "val x = 1",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .expect("parse");
        let Decl::Val(pat, exp) = &file[0].node else {
            panic!("expected Val decl");
        };
        assert_eq!(pat.span.file, path);
        assert_eq!(exp.span.file, path);
        assert_eq!(exp.span.first.line, 1);
    }

    #[test]
    #[cfg(generated_parser)]
    fn parse_ur_remapped_spans_track_multiline_line_numbers() {
        use crate::source::Decl;
        let mut errors = ErrorReporter::new_silent();
        let file = parse_ur(
            "m.ur",
            "val a = 1\nval b = 2",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .expect("parse");
        let Decl::Val(_, exp_b) = &file[1].node else {
            panic!("expected second Val");
        };
        assert_eq!(
            exp_b.span.first.line, 2,
            "second declaration should remap to physical line 2"
        );
    }

    /// `@@x` lexes to [`Token::AtDontInferPath`] → [`Exp::Var`] with [`Inference::DontInfer`].
    #[test]
    #[cfg(generated_parser)]
    fn parse_double_at_path_is_dont_infer_var() {
        use crate::source::{Decl, Exp, Inference};
        let mut errors = ErrorReporter::new_silent();
        let file = parse_ur(
            "t.ur",
            "val u = @@x",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .expect("parse");
        let Decl::Val(_, e) = &file[0].node else {
            panic!("expected Val");
        };
        assert!(matches!(
            &e.node,
            Exp::Var(q, n, Inference::DontInfer) if q.is_empty() && n == "x"
        ));
    }

    /// Qualified `@Foo.bar` is one [`Token::AtTypesOnlyPath`] (ML longest `path`).
    #[test]
    #[cfg(generated_parser)]
    fn parse_at_qualified_module_path_is_one_var() {
        use crate::source::{Decl, Exp, Inference};
        let mut errors = ErrorReporter::new_silent();
        let file = parse_ur(
            "t.ur",
            "val u = @Foo.bar",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .expect("parse");
        let Decl::Val(_, e) = &file[0].node else {
            panic!("expected Val");
        };
        assert!(matches!(
            &e.node,
            Exp::Var(q, n, Inference::TypesOnly)
                if q == &vec!["Foo".to_string()] && n == "bar"
        ));
    }

    /// Single `@` → [`Inference::TypesOnly`] ([`Token::AtTypesOnlyPath`]).
    #[test]
    #[cfg(generated_parser)]
    fn parse_single_at_path_is_types_only_var() {
        use crate::source::{Decl, Exp, Inference};
        let mut errors = ErrorReporter::new_silent();
        let file = parse_ur(
            "t.ur",
            "val u = @x",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .expect("parse");
        let Decl::Val(_, e) = &file[0].node else {
            panic!("expected Val");
        };
        assert!(matches!(
            &e.node,
            Exp::Var(q, n, Inference::TypesOnly) if q.is_empty() && n == "x"
        ));
    }

    /// Upstream `eapps BANG` → [`Exp::DisjointApp`] via postfix `!`.
    #[test]
    #[cfg(generated_parser)]
    fn parse_bang_postfix_wraps_operand_in_disjoint_app() {
        use crate::source::{Decl, Exp};
        let mut errors = ErrorReporter::new_silent();
        let file = parse_ur(
            "t.ur",
            "val u = x !",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .expect("parse");
        let Decl::Val(_, e) = &file[0].node else {
            panic!("expected Val");
        };
        assert!(matches!(&e.node, Exp::DisjointApp(_)));
    }

    #[test]
    fn debug_cookie_bars() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/demo/cookie.ur");
        let Ok(src) = std::fs::read_to_string(path) else {
            return;
        };
        let pp = preprocess_ur_for_parse(&src);
        for (i, c) in pp.char_indices() {
            if c == '|' {
                let s = i.saturating_sub(40);
                let e = (i + 40).min(pp.len());
                tracing::debug!(index = i, window = ?&pp[s..e], "preprocess_ur '|' bar location");
            }
        }
        tracing::debug!(total_len = pp.len(), "preprocess_ur cookie.ur scan");
    }

    #[test]
    fn pp_basis_context() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/ur/basis.urs");
        let Ok(content) = std::fs::read_to_string(path) else {
            return;
        };
        let pp = preprocess_urs(&content);
        let pos: usize = 504;
        let start = pos.saturating_sub(300);
        let end = (pos + 200).min(pp.len());
        tracing::debug!(pos, window = %&pp[start..end], "preprocessed basis.urs window");
        tracing::debug!(pos, char_at = ?pp.chars().nth(pos), "preprocessed char");
    }

    #[test]
    fn basis_urs_window_matches_fixed_width() {
        let pos = 38564usize;
        let before = 200usize;
        let after = 100usize;
        let s = basis_urs_preprocessed_window(pos, before, after).expect("read basis.urs");
        assert_eq!(
            s.len(),
            before + after,
            "slice must use (pos + after).min(len) — catches + → - / * mutants"
        );
    }

    #[test]
    fn parse_top_level_decl_count_tracks_parser() {
        let mut errors = ErrorReporter::new_silent();
        let n = parse_top_level_decl_count("test.ur", "val x = 1", &mut errors);
        #[cfg(not(generated_parser))]
        {
            assert!(n.is_none());
            assert!(errors.has_errors());
        }
        #[cfg(generated_parser)]
        {
            assert_eq!(n, Some(1), "smoke parse must count exactly one decl");
        }
    }

    #[test]
    fn parse_ur_two_vals_requires_two_decls() {
        let mut errors = ErrorReporter::new_silent();
        let n = parse_ur(
            "t.ur",
            "val a = 1\nval b = 2",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .map(|f| f.len());
        #[cfg(generated_parser)]
        {
            assert_eq!(
                n,
                Some(2),
                "catches parse_top_level_decl_count -> Some(1) style mutants"
            );
        }
        #[cfg(not(generated_parser))]
        {
            assert!(n.is_none());
        }
    }

    #[test]
    fn parse_top_level_decl_count_matches_parse_ur_len() {
        let mut e1 = ErrorReporter::new_silent();
        let mut e2 = ErrorReporter::new_silent();
        let src = "val p = 1\nval q = 2\nval r = 3";
        let a = parse_top_level_decl_count("m.ur", src, &mut e1);
        let b = parse_ur("m.ur", src, &mut e2, crate::db::ProjectDb::default()).map(|f| f.len());
        assert_eq!(a, b);
        #[cfg(generated_parser)]
        assert_eq!(a, Some(3));
    }

    #[test]
    fn parse_urs_returns_none_without_generated_parser() {
        let mut errors = ErrorReporter::new_silent();
        let result = parse_urs("test.urs", "val x : int", &mut errors);
        #[cfg(not(generated_parser))]
        {
            assert!(result.is_none());
            assert!(errors.has_errors());
        }
        #[cfg(generated_parser)]
        {
            let items = result.expect("val x : int should parse as a signature");
            assert!(
                !items.is_empty(),
                "catches parse_urs -> Some(vec![]) mutants"
            );
        }
    }

    #[test]
    #[cfg(generated_parser)]
    fn parse_urs_sets_file_on_inner_spans() {
        use crate::source::SgnItem;
        let mut errors = ErrorReporter::new_silent();
        let path = "sig/M.urs";
        let items = parse_urs(path, "val x : int", &mut errors).expect("parse");
        let SgnItem::Val(_, c) = &items[0].node else {
            panic!("expected Val item");
        };
        assert_eq!(c.span.file, path);
    }

    /// LALRPOP `ArithExp` vs [`expr_langsec::parse_cmp_app_spine`] on the same token stream
    /// (subset: atoms + paren / arithmetic / cons / strcat; no postfix `.` / `[Con]`).
    #[cfg(generated_parser)]
    mod langsec_spine_equiv {
        use super::*;
        use crate::error_types::{Located, Span};
        use crate::parse::expr_langsec::{parse_cmp_app_spine, ExprRecognizeError, TokenCursor};
        use crate::parse::lexical_analyzer::{tokenize_xml_aware, Token};
        use crate::primitives::Prim;
        use crate::source::{Decl, Exp, Inference};

        fn line_starts_for(src: &str) -> Vec<usize> {
            let mut v = vec![0usize];
            for (i, c) in src.char_indices() {
                if c == '\n' {
                    v.push(i + c.len_utf8());
                }
            }
            v
        }

        fn span_at(file: &str, line_starts: &[usize], lo: usize, hi: usize) -> Span {
            Span::from_offsets(file, lo, hi, line_starts)
        }

        fn spine_langsec_primary(
            cur: &mut TokenCursor<'_>,
        ) -> Result<Located<Exp>, ExprRecognizeError> {
            let Some((l, tok, r)) = cur.peek().cloned() else {
                return Err(ExprRecognizeError::UnexpectedEof);
            };
            match &tok {
                Token::UrwebPut => {
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(
                            vec!["UrwebNative".into()],
                            "urweb_put".into(),
                            Inference::DontInfer,
                        ),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::UrwebGet => {
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(
                            vec!["UrwebNative".into()],
                            "urweb_get".into(),
                            Inference::DontInfer,
                        ),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::UrwebTbTransfer => {
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(
                            vec!["UrwebNative".into()],
                            "urweb_tb_transfer".into(),
                            Inference::DontInfer,
                        ),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Ident(name) | Token::UpperIdent(name) => {
                    let name = name.clone();
                    cur.bump();
                    Ok(Located::new(
                        Exp::Var(vec![], name, Inference::Infer),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Int(n) => {
                    let n = *n;
                    cur.bump();
                    Ok(Located::new(
                        Exp::Prim(Prim::Int(n)),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Float(f) => {
                    let f = *f;
                    cur.bump();
                    Ok(Located::new(
                        Exp::Prim(Prim::Float(f)),
                        span_at(cur.file, cur.line_starts, l, r),
                    ))
                }
                Token::Unit => {
                    cur.bump();
                    Ok(Located::dummy(Exp::Record(vec![], false)))
                }
                Token::Lparen => {
                    cur.bump();
                    let inner = parse_cmp_app_spine(cur, spine_langsec_primary)?;
                    match cur.bump() {
                        Some((_, Token::Rparen, r2)) => Ok(Located::new(
                            inner.node,
                            span_at(cur.file, cur.line_starts, l, r2),
                        )),
                        _ => Err(ExprRecognizeError::UnbalancedParen { at_byte: l }),
                    }
                }
                _ => Err(ExprRecognizeError::ExpectedPrimary { at_byte: l }),
            }
        }

        fn exp_structure_eq(a: &Located<Exp>, b: &Located<Exp>) -> bool {
            exp_node_eq(&a.node, &b.node)
        }

        fn exp_node_eq(a: &Exp, b: &Exp) -> bool {
            match (a, b) {
                (Exp::Var(qa, na, ia), Exp::Var(qb, nb, ib)) => qa == qb && na == nb && ia == ib,
                (Exp::Prim(pa), Exp::Prim(pb)) => pa == pb,
                (Exp::Record(fa, sa), Exp::Record(fb, sb)) => {
                    fa.is_empty() && fb.is_empty() && sa == sb
                }
                (Exp::App(fa, xa), Exp::App(fb, xb)) => {
                    exp_structure_eq(fa, fb) && exp_structure_eq(xa, xb)
                }
                (Exp::Infix(oa, la, ra), Exp::Infix(ob, lb, rb)) => {
                    oa == ob && exp_structure_eq(la, lb) && exp_structure_eq(ra, rb)
                }
                _ => false,
            }
        }

        #[test]
        fn lalrpop_arith_exp_matches_expr_langsec() {
            let cases = [
                "a + b * c",
                "f g h",
                "f x * y",
                "(a + b) * c",
                "a :: b :: c",
                "a + b :: c",
                "a :: b + c",
                "a + b = c",
                "a ^ b",
                "()",
                "1",
                "(1 + 2) * 3",
            ];
            for expr in cases {
                let file_src = format!("val _ = {}\n", expr);
                let mut errs = ErrorReporter::new_silent();
                let Some(file) = parse_ur(
                    "equiv.ur",
                    &file_src,
                    &mut errs,
                    crate::db::ProjectDb::default(),
                ) else {
                    panic!("parse_ur failed for {:?}: {:?}", expr, errs.errors);
                };
                let Some(got) = file.iter().find_map(|d| {
                    if let Decl::Val(_, e) = &d.node {
                        Some(e.clone())
                    } else {
                        None
                    }
                }) else {
                    panic!("no val decl for {:?}", expr);
                };

                let toks = tokenize_xml_aware(expr)
                    .unwrap_or_else(|e| panic!("lex {:?}: {}", expr, e.message));
                let line_starts = line_starts_for(expr);
                let mut cur = TokenCursor::new(&toks, &line_starts, "");
                let spine = parse_cmp_app_spine(&mut cur, spine_langsec_primary)
                    .unwrap_or_else(|e| panic!("langsec {:?}: {:?}", expr, e));
                assert!(
                    cur.at_end(),
                    "leftover tokens for {:?} at {}",
                    expr,
                    cur.pos
                );
                assert!(
                    exp_structure_eq(&got, &spine),
                    "spine mismatch {:?}\n LALR {:?}\n LS {:?}",
                    expr,
                    got.node,
                    spine.node
                );
            }
        }
    }

    #[test]
    fn parse_query1_prime_followed_by_val_rev_stays_two_decls() {
        let source_text = concat!(
            "fun localQuery1Prime [t ::: Name] [fs ::: {Type}] [state ::: Type]\n",
            "    (q : sql_query [] [] [t = fs] [])\n",
            "    (f : $fs -> state -> state) (i : state) =\n",
            "    query q (fn r s => return (f r.t s)) i\n",
            "\n",
            "val rev = fn [a] =>\n",
            "    let\n",
            "        fun rev' acc (ls : list a) =\n",
            "            case ls of\n",
            "                [] => acc\n",
            "              | x :: rest => rev' (x :: acc) rest\n",
            "    in\n",
            "        rev' []\n",
            "    end\n",
        );
        let mut errors = ErrorReporter::new_silent();
        let Some(file) = parse_ur(
            "adjacent.ur",
            source_text,
            &mut errors,
            crate::db::ProjectDb::default(),
        ) else {
            panic!("parse_ur failed: {:?}", errors.errors);
        };
        assert_eq!(file.len(), 2, "expected two top-level declarations");
        match &file[1].node {
            crate::source::Decl::Val(pattern, _) => match &pattern.node {
                crate::source::Pat::Var(name) => assert_eq!(name, "rev"),
                other => panic!("expected rev variable pattern, got {:?}", other),
            },
            other => panic!("expected second declaration to be val rev, got {:?}", other),
        }
    }

    #[test]
    #[cfg(generated_parser)]
    fn parse_uppercase_field_postfix_on_value_is_field_access() {
        use crate::source::{Decl, Exp};
        let mut errors = ErrorReporter::new_silent();
        let file = parse_ur(
            "field_upper.ur",
            "val demo = r.C\n",
            &mut errors,
            crate::db::ProjectDb::default(),
        )
        .expect("parse");
        let Decl::Val(_, expression) = &file[0].node else {
            panic!("expected Val");
        };
        match &expression.node {
            Exp::Field(base, field_name) => {
                assert!(matches!(&base.node, Exp::Var(q, n, _) if q.is_empty() && n == "r"));
                assert!(matches!(&field_name.node, crate::source::Con::Name(name) if name == "C"));
            }
            other => panic!("expected field access, got {:?}", other),
        }
    }

    #[test]
    fn parse_monadic_bind_desugars_to_basis_bind_application() {
        let mut errors = ErrorReporter::new_silent();
        let Some(file) = parse_ur(
            "bind_desugar.ur",
            "fun demo q = ls <- q; return ls\n",
            &mut errors,
            crate::db::ProjectDb::default(),
        ) else {
            panic!("parse_ur failed: {:?}", errors.errors);
        };
        let crate::source::Decl::ValRec(bindings) = &file[0].node else {
            panic!("expected top-level fun to parse as val rec");
        };
        let (_, _, body) = bindings
            .first()
            .unwrap_or_else(|| panic!("expected one binding, got {:?}", bindings));
        let crate::source::Exp::Abs(argument_name, None, fun_body) = &body.node else {
            panic!(
                "expected top-level fun to remain a lambda around bind body, got {:?}",
                body.node
            );
        };
        assert_eq!(argument_name, "q");
        let crate::source::Exp::App(bind_apply, lambda) = &fun_body.node else {
            panic!(
                "expected monadic bind body to desugar to application, got {:?}",
                fun_body.node
            );
        };
        let crate::source::Exp::App(bind_head, bound_expression) = &bind_apply.node else {
            panic!(
                "expected bind application head to be curried application, got {:?}",
                bind_apply.node
            );
        };
        let crate::source::Exp::Var(module_path, function_name, crate::source::Inference::Infer) =
            &bind_head.node
        else {
            panic!("expected Basis.bind head, got {:?}", bind_head.node);
        };
        assert_eq!(module_path, &vec!["Basis".to_string()]);
        assert_eq!(function_name, "bind");
        let crate::source::Exp::Var(_, bound_name, _) = &bound_expression.node else {
            panic!(
                "expected first bind argument to stay as q, got {:?}",
                bound_expression.node
            );
        };
        assert_eq!(bound_name, "q");
        let crate::source::Exp::Abs(parameter_name, None, lambda_body) = &lambda.node else {
            panic!("expected bind continuation lambda, got {:?}", lambda.node);
        };
        assert_eq!(parameter_name, "ls");
        let crate::source::Exp::App(return_head, returned_value) = &lambda_body.node else {
            panic!(
                "expected continuation body to remain return application, got {:?}",
                lambda_body.node
            );
        };
        let crate::source::Exp::Var(return_module, return_name, crate::source::Inference::Infer) =
            &return_head.node
        else {
            panic!("expected return head, got {:?}", return_head.node);
        };
        assert_eq!(return_module, &Vec::<String>::new());
        assert_eq!(return_name, "return");
        let crate::source::Exp::Var(_, returned_name, _) = &returned_value.node else {
            panic!("expected returned variable, got {:?}", returned_value.node);
        };
        assert_eq!(returned_name, "ls");
    }

    #[test]
    fn preprocess_top_folder_wraps_tf_binder_in_brackets() {
        let src = r"(** Row folding *)

con folder = K ==> fn r :: {K} =>
                      tf :: ({K} -> Type)
                      -> (nm :: Name -> v :: K -> r :: {K} -> [[nm] ~ r] =>
                          tf r -> tf ([nm = v] ++ r))
                      -> tf [] -> tf r

";
        let pre = preprocess_ur_for_parse(src);
        assert!(
            pre.contains("[tf :: ({K} -> Type)] ->"),
            "bare kind binder `tf :: … ->` must rewrite to bracketed TCFun; got:\n{pre}"
        );
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/ur/top.ur");
        let Ok(full) = std::fs::read_to_string(path) else {
            return;
        };
        let pre_full = preprocess_ur_for_parse(&full);
        assert!(
            pre_full.contains("[tf :: ({K} -> Type)] ->"),
            "full top.ur must bracket folder's tf binder; got fragment: {}",
            pre_full
                .split("con folder")
                .nth(1)
                .and_then(|s| s.get(..200))
                .unwrap_or("<missing>")
        );
    }

    #[test]
    fn debug_top_ur_pos_263() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/lib/ur/top.ur");
        let src = std::fs::read_to_string(path).expect("top.ur");
        let pre = preprocess_ur_for_parse(&src);
        let pos = 263usize;
        let start = pos.saturating_sub(40);
        let end = (pos + 40).min(pre.len());
        tracing::debug!(pos, slice = ?pre.get(pos..pos + 1), "top.ur preprocess byte");
        tracing::debug!(pos, context = ?&pre[start..end], "top.ur preprocess context");
    }
}
