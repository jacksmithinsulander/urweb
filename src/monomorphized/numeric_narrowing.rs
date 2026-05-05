//! Numeric narrowing analysis for the monomorphized IR.
//!
//! This pass walks the entire monomorphized [`File`] and determines, for every
//! variable whose value is statically known at compile time, the smallest concrete
//! numeric type — category (`Int` / `Uint` / `Float`) and bit-width — that can
//! faithfully represent it.
//!
//! # What "narrowing all variables" means
//!
//! A variable is narrowable when its compile-time value can be determined by
//! **constant propagation**:
//!
//! - `Prim` literals → narrowed directly.
//! - `let x = <known> in body` → `x` is narrowable to the narrowed type of `<known>`.
//! - `(fn x => body)(42)` → if the argument is a known literal, `x` is narrowable in `body`.
//! - Arithmetic on two known prims → the result is computed and narrowed.
//! - Named top-level `val x = <known>` → `x` is narrowable at all use sites.
//!
//! Variables that are runtime-dependent (function arguments from user input, query
//! results, etc.) cannot be narrowed — [`narrow_exp`] returns `None` for those.
//!
//! # Outputs
//!
//! [`analyze`] returns a [`NarrowingTable`] which callers (codegen, SQL DDL generation)
//! can query via [`NarrowingTable::lookup_named`] and [`NarrowEnv::narrow_exp`].

use std::collections::HashMap;

use crate::monomorphized::{Decl, Exp, File, LocExp, Pat};
use crate::primitives::{NarrowedNumeric, Prim, StringMode};

// ---------------------------------------------------------------------------
// Arithmetic evaluation on known primitive values
// ---------------------------------------------------------------------------

/// Evaluates a binary integer/float operation on two known primitive values.
///
/// Returns `None` if the operation is not applicable (e.g., division by zero,
/// overflow, or an unrecognized operator name).
///
/// # Arguments
///
/// * `op` — The operator string (e.g., `"+"`, `"-"`, `"*"`, `"/"`, `"%"`).
/// * `left` — The left-hand-side known primitive.
/// * `right` — The right-hand-side known primitive.
fn eval_binop_prim(op: &str, left: &Prim, right: &Prim) -> Option<Prim> {
    match (left, right) {
        // Integer × integer arithmetic.
        (Prim::Int(a), Prim::Int(b)) => {
            let result = match op {
                "+" => a.checked_add(*b)?, // overflow → None
                "-" => a.checked_sub(*b)?, // underflow → None
                "*" => a.checked_mul(*b)?, // overflow → None
                "/" => {
                    if *b == 0 {
                        return None;
                    }
                    a.checked_div(*b)?
                } // div-by-zero → None
                "%" => {
                    if *b == 0 {
                        return None;
                    }
                    a.checked_rem(*b)?
                } // mod-by-zero → None
                _ => return None,          // unrecognized operator
            };
            Some(Prim::Int(result)) // produce a new integer literal
        }
        // Float × float arithmetic.
        (Prim::Float(a), Prim::Float(b)) => {
            let result = match op {
                "+" => a + b, // float addition
                "-" => a - b, // float subtraction
                "*" => a * b, // float multiplication
                "/" => a / b, // float division (may produce Inf or NaN, which is valid)
                _ => return None,
            };
            Some(Prim::Float(result)) // produce a new float literal
        }
        // Mismatched types (e.g., Int + Float) cannot be constant-folded here.
        _ => None,
    }
}

/// Evaluates a unary operation on a known primitive value.
///
/// Returns `None` for unrecognized operators or non-applicable types.
///
/// # Arguments
///
/// * `op` — The operator string (e.g., `"-"` for numeric negation, `"!"` for logical not).
/// * `operand` — The known primitive to operate on.
fn eval_unop_prim(op: &str, operand: &Prim) -> Option<Prim> {
    match operand {
        Prim::Int(n) => match op {
            "-" => n.checked_neg().map(Prim::Int), // negation; checked for MIN overflow
            _ => None,
        },
        Prim::Float(f) => match op {
            "-" => Some(Prim::Float(-f)), // float negation is always exact
            _ => None,
        },
        _ => None, // strings and chars have no numeric unary ops
    }
}

// ---------------------------------------------------------------------------
// Narrowing environment (local variable tracking)
// ---------------------------------------------------------------------------

/// Tracks compile-time–known primitive values for local (Rel) and named variables.
///
/// Uses de Bruijn indexing for locals: entry at index `n` is the value of `Rel(n)`,
/// where `Rel(0)` is the innermost (most recently bound) variable.
#[derive(Debug, Clone)]
pub struct NarrowEnv {
    /// Known primitive values for Rel-indexed local variables.
    /// Index 0 = innermost binder; `None` = value unknown at compile time.
    rel_values: Vec<Option<Prim>>,
    /// Known narrowed types for Named (globally identified) declarations.
    named_narrowings: HashMap<usize, NarrowedNumeric>,
}

impl NarrowEnv {
    /// Creates a fresh empty environment with no known variable values.
    pub fn new() -> Self {
        NarrowEnv {
            rel_values: vec![],
            named_narrowings: HashMap::new(),
        }
    }

    /// Returns a new environment with the given narrowing table's named entries merged in.
    ///
    /// Used to seed the environment from a completed whole-file analysis.
    ///
    /// # Arguments
    ///
    /// * `table` — The table whose named entries are added to this environment.
    pub fn with_table(self, table: &NarrowingTable) -> Self {
        NarrowEnv {
            rel_values: self.rel_values,
            named_narrowings: table.named.clone(),
        }
    }

    /// Returns a new environment with a new innermost Rel binding whose value is unknown.
    ///
    /// Used when entering an `Abs` binder whose argument is not a compile-time literal.
    pub fn push_unknown(&self) -> Self {
        let mut new_rels = vec![None]; // unknown value for Rel(0)
        new_rels.extend(self.rel_values.iter().cloned()); // shift outer bindings by 1
        NarrowEnv {
            rel_values: new_rels,
            named_narrowings: self.named_narrowings.clone(),
        }
    }

    /// Returns a new environment with a new innermost Rel binding holding a known primitive.
    ///
    /// Used when entering an `Abs` or `Let` binder whose value is a compile-time literal.
    ///
    /// # Arguments
    ///
    /// * `prim` — The known literal value for `Rel(0)` in the new environment.
    pub fn push_known(&self, prim: Prim) -> Self {
        let mut new_rels = vec![Some(prim)]; // known value for Rel(0)
        new_rels.extend(self.rel_values.iter().cloned()); // shift outer bindings by 1
        NarrowEnv {
            rel_values: new_rels,
            named_narrowings: self.named_narrowings.clone(),
        }
    }

    /// Returns a new environment with a named declaration's narrowed type recorded.
    ///
    /// # Arguments
    ///
    /// * `id` — The globally unique ID of the named declaration.
    /// * `narrowed` — The narrowed numeric type to associate with this ID.
    pub fn with_named(mut self, id: usize, narrowed: NarrowedNumeric) -> Self {
        self.named_narrowings.insert(id, narrowed); // record in named table
        self
    }

    /// Attempts to statically evaluate `exp` to a known compile-time primitive value.
    ///
    /// Performs constant propagation through:
    /// - `Prim` literals (always known)
    /// - `Rel(n)` local variables whose binding was a known literal
    /// - `Named(id)` declarations whose value was determined during whole-file analysis
    /// - `Let(name, _, bound, body)` — if `bound` is known, propagates into `body`
    /// - `App(Abs(_, _, _, body), arg)` — if `arg` is a known literal, propagates into `body`
    /// - `Binop` on two known prims → arithmetic constant folding
    /// - `Unop` on a known prim → arithmetic evaluation
    /// - `Case` with a known discriminant → selects the matching arm
    ///
    /// Returns `None` when the value is not statically determinable.
    ///
    /// # Arguments
    ///
    /// * `exp` — The expression to evaluate.
    pub fn known_prim(&self, exp: &LocExp) -> Option<Prim> {
        match &exp.node {
            // A literal is always known.
            Exp::Prim(p) => Some(p.clone()),

            // A local variable is known iff its binding is in the env.
            Exp::Rel(depth) => self.rel_values.get(*depth)?.clone(),

            // A named declaration is known iff it has a recorded literal equivalent.
            // (The named_narrowings table only stores *narrowed types*, not full prims.
            // For full prim tracking, the analysis pass also stores a prim side-table.)
            Exp::Named(_) => None, // narrowed type is stored, not full prim — see narrow_exp

            // `let x = bound in body`: if bound is known, push it and evaluate body.
            Exp::Let(_, _, bound_exp, body_exp) => {
                let bound_prim = self.known_prim(bound_exp); // may be None
                let inner_env = match bound_prim {
                    Some(p) => self.push_known(p), // propagate known value into body
                    None => self.push_unknown(),   // unknown value, but x is still in scope
                };
                inner_env.known_prim(body_exp) // evaluate body with extended env
            }

            // `(fn x => body)(arg)`: if arg is a known literal, propagate into body.
            Exp::App(function_exp, argument_exp) => {
                if let Exp::Abs(_, _, _, body_exp) = &function_exp.node {
                    let arg_prim = self.known_prim(argument_exp); // may be None
                    let inner_env = match arg_prim {
                        Some(p) => self.push_known(p), // propagate known arg into body
                        None => self.push_unknown(),   // unknown arg, but x is still in scope
                    };
                    inner_env.known_prim(body_exp) // evaluate body with extended env
                } else {
                    None // non-Abs function application — cannot propagate
                }
            }

            // Binary arithmetic on two known prims.
            Exp::Binop(_, op, left_exp, right_exp) => {
                let left_prim = self.known_prim(left_exp)?; // both sides must be known
                let right_prim = self.known_prim(right_exp)?;
                eval_binop_prim(op, &left_prim, &right_prim) // constant-fold the operation
            }

            // Unary arithmetic on a known prim.
            Exp::Unop(op, operand_exp) => {
                let operand_prim = self.known_prim(operand_exp)?; // operand must be known
                eval_unop_prim(op, &operand_prim) // constant-fold the unary op
            }

            // `case scrutinee of arms`: if discriminant is a known literal, select arm.
            Exp::Case(scrutinee_exp, arms, _) => {
                let scrutinee_prim = self.known_prim(scrutinee_exp)?; // discriminant must be known
                for (pattern, body_exp) in arms {
                    if pattern_matches_prim(&pattern.node, &scrutinee_prim) {
                        return self.known_prim(body_exp); // evaluate the matching arm
                    }
                }
                None // no arm matched (wildcard patterns with bindings not yet handled)
            }

            // Strcat on two known string prims.
            Exp::Strcat(left_exp, right_exp) => {
                let left_prim = self.known_prim(left_exp)?;
                let right_prim = self.known_prim(right_exp)?;
                match (&left_prim, &right_prim) {
                    (Prim::String(_, a), Prim::String(_, b)) => {
                        // Concatenate string literals; preserve Normal mode.
                        Some(Prim::String(StringMode::Normal, format!("{}{}", a, b)))
                    }
                    _ => None, // mismatched or non-string types
                }
            }

            // All other expression forms are not statically evaluable.
            _ => None,
        }
    }

    /// Attempts to determine the narrowed numeric type of `exp`.
    ///
    /// First tries to statically evaluate the expression to a known `Prim` via
    /// [`NarrowEnv::known_prim`], then narrows the result with [`NarrowedNumeric::from_prim`].
    ///
    /// For `Named` references, checks the `named_narrowings` table directly without
    /// needing to know the full primitive value.
    ///
    /// Returns `None` when the expression is not a statically known numeric value.
    ///
    /// # Arguments
    ///
    /// * `exp` — The expression whose narrowed type to determine.
    pub fn narrow_exp(&self, exp: &LocExp) -> Option<NarrowedNumeric> {
        // Special case: Named references look up the precomputed narrowing directly.
        if let Exp::Named(id) = &exp.node {
            return self.named_narrowings.get(id).copied();
        }
        // All other forms: evaluate to a known prim, then narrow it.
        let prim = self.known_prim(exp)?;
        NarrowedNumeric::from_prim(&prim)
    }
}

impl Default for NarrowEnv {
    /// Creates the default empty environment (delegates to [`NarrowEnv::new`]).
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Pattern matching on known prim values
// ---------------------------------------------------------------------------

/// Returns true iff `pattern` matches the given known primitive discriminant.
///
/// Only `Pat::Prim` patterns (literal match arms) are handled here; record,
/// constructor, and wildcard patterns are conservatively treated as non-matching
/// to avoid incorrect constant folding.
///
/// # Arguments
///
/// * `pattern` — The `Pat` node to test against the discriminant.
/// * `discriminant` — The known primitive value of the `case` scrutinee.
fn pattern_matches_prim(pattern: &Pat, discriminant: &Prim) -> bool {
    match pattern {
        Pat::Prim(pattern_prim) => pattern_prim == discriminant, // exact literal match
        _ => false, // wildcard and binding patterns cannot be handled here
    }
}

// ---------------------------------------------------------------------------
// Whole-file narrowing analysis
// ---------------------------------------------------------------------------

/// The result of the numeric narrowing analysis: a table mapping declaration IDs
/// to their narrowed numeric types.
///
/// Only populated for declarations whose bodies evaluate to a statically known
/// numeric literal. Callers query this via [`NarrowingTable::lookup_named`].
#[derive(Debug, Clone)]
pub struct NarrowingTable {
    /// Maps globally unique named declaration IDs to their narrowed numeric type.
    pub named: HashMap<usize, NarrowedNumeric>,
}

impl NarrowingTable {
    /// Creates an empty `NarrowingTable`.
    pub fn new() -> Self {
        NarrowingTable {
            named: HashMap::new(),
        }
    }

    /// Looks up the narrowed numeric type for a named declaration by ID.
    ///
    /// Returns `None` when the declaration's value is not statically known or is
    /// not a numeric type.
    ///
    /// # Arguments
    ///
    /// * `id` — The globally unique ID of the named declaration to look up.
    pub fn lookup_named(&self, id: usize) -> Option<NarrowedNumeric> {
        self.named.get(&id).copied() // copy since NarrowedNumeric is Copy
    }

    /// Returns the number of narrowed declarations recorded in this table.
    ///
    /// Useful for logging and testing to confirm the pass did useful work.
    pub fn len(&self) -> usize {
        self.named.len() // count of entries in the named table
    }

    /// Returns `true` when no declarations were narrowed.
    pub fn is_empty(&self) -> bool {
        self.named.is_empty() // true when no numeric literals were found
    }
}

impl Default for NarrowingTable {
    /// Creates the default empty table (delegates to [`NarrowingTable::new`]).
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Per-expression narrowing within a known environment
// ---------------------------------------------------------------------------

/// Narrows all variables in a single expression given a pre-built environment.
///
/// This is the on-demand entry point used by codegen passes: given the current
/// [`NarrowEnv`] at the expression's location, returns the narrowed type (if any).
///
/// # Arguments
///
/// * `exp` — The expression to narrow.
/// * `env` — The narrowing environment at the expression's location.
///
/// # Returns
///
/// The narrowed numeric type of `exp`, or `None` if the value is not statically known.
pub fn narrow_exp(exp: &LocExp, env: &NarrowEnv) -> Option<NarrowedNumeric> {
    env.narrow_exp(exp) // delegate to NarrowEnv::narrow_exp
}

// ---------------------------------------------------------------------------
// Whole-file analysis entry point
// ---------------------------------------------------------------------------

/// Performs numeric narrowing analysis on the entire monomorphized file.
///
/// Walks all top-level declarations in order and builds a [`NarrowingTable`]
/// that maps named declaration IDs to their narrowed numeric types.  Later
/// declarations may reference earlier ones via `Named(id)`, which is why the
/// table is built incrementally.
///
/// Declarations that are functions (return `Abs`) or have runtime-dependent
/// values are simply not recorded in the table; no error is produced.
///
/// # Arguments
///
/// * `file` — The monomorphized file to analyze.
///
/// # Returns
///
/// A [`NarrowingTable`] populated with all statically knowable numeric narrowings.
pub fn analyze(file: &File) -> NarrowingTable {
    let (decls, _export_info) = file; // unpack the file tuple
    let mut table = NarrowingTable::new(); // accumulate results here

    for located_decl in decls {
        match &located_decl.node {
            // Single value declaration: analyze the body expression.
            Decl::Val(_name, id, _typ, body_exp, _sql_name) => {
                // Build an env seeded with currently known named narrowings.
                let env = NarrowEnv::new().with_table(&table);
                // Attempt to determine the narrowed type of the body.
                if let Some(narrowed) = env.narrow_exp(body_exp) {
                    table.named.insert(*id, narrowed); // record the narrowing for this decl
                }
            }

            // Mutually recursive value declarations: analyze each body in the same env.
            // (Recursive calls to the group will yield None — correct: no self-referential
            // constant literals.)
            Decl::ValRec(bindings) => {
                for (_name, id, _typ, body_exp, _sql_name) in bindings {
                    let env = NarrowEnv::new().with_table(&table);
                    if let Some(narrowed) = env.narrow_exp(body_exp) {
                        table.named.insert(*id, narrowed); // record narrowing for this binding
                    }
                }
            }

            // All other declaration kinds (Table, Sequence, Database, etc.) do not
            // bind named values with statically knowable numeric types.
            _ => {}
        }
    }

    table // return the completed narrowing table
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error_types::{Located, Span};
    use crate::monomorphized::{BinopIntness, CaseMeta, LocTyp, Typ};
    use crate::primitives::Prim;

    /// Helper: a located expression with a dummy span.
    fn loc(exp: Exp) -> LocExp {
        Located::dummy(exp)
    }

    /// Helper: a located type with a dummy span.
    fn dummy_typ() -> LocTyp {
        Located::dummy(Typ::Ffi("Basis".into(), "int".into()))
    }

    #[test]
    fn narrow_prim_literal_positive_int_is_uint() {
        // A non-negative integer literal narrows to Uint.
        let env = NarrowEnv::new();
        let exp = loc(Exp::Prim(Prim::Int(42)));
        let narrowed = env.narrow_exp(&exp).expect("42 should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Uint(_)));
    }

    #[test]
    fn narrow_prim_literal_negative_int_is_signed() {
        // A negative integer literal narrows to Int (signed).
        let env = NarrowEnv::new();
        let exp = loc(Exp::Prim(Prim::Int(-5)));
        let narrowed = env.narrow_exp(&exp).expect("-5 should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Int(_)));
    }

    #[test]
    fn narrow_prim_literal_float_is_float() {
        // A float literal narrows to Float.
        let env = NarrowEnv::new();
        let exp = loc(Exp::Prim(Prim::Float(3.14)));
        let narrowed = env.narrow_exp(&exp).expect("3.14 should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Float(_)));
    }

    #[test]
    fn narrow_rel_with_known_binding_propagates() {
        // Rel(0) with a known literal binding should narrow to that literal's type.
        let env = NarrowEnv::new().push_known(Prim::Int(100));
        let exp = loc(Exp::Rel(0)); // refers to the innermost binding (100)
        let narrowed = env.narrow_exp(&exp).expect("Rel(0) should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Uint(_))); // 100 >= 0 → Uint
    }

    #[test]
    fn narrow_rel_with_unknown_binding_returns_none() {
        // Rel(0) with an unknown binding should return None.
        let env = NarrowEnv::new().push_unknown();
        let exp = loc(Exp::Rel(0));
        assert!(env.narrow_exp(&exp).is_none()); // unknown binding → not narrowable
    }

    #[test]
    fn narrow_let_propagates_known_binding_into_body() {
        // `let x = 7 in x` — x is known to be 7 (Uint), so the body narrows.
        let env = NarrowEnv::new();
        let bound = Box::new(loc(Exp::Prim(Prim::Int(7)))); // binding value: 7
        let body = Box::new(loc(Exp::Rel(0))); // body: x (de Bruijn 0)
        let exp = loc(Exp::Let("x".into(), dummy_typ(), bound, body));
        let narrowed = env.narrow_exp(&exp).expect("let x = 7 in x should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Uint(_))); // 7 >= 0 → Uint
    }

    #[test]
    fn narrow_let_with_unknown_bound_propagates_none() {
        // `let x = <runtime> in x` — x is not known, body should not narrow.
        let env = NarrowEnv::new();
        let bound = Box::new(loc(Exp::Named(999))); // runtime value (unknown)
        let body = Box::new(loc(Exp::Rel(0))); // body: x
        let exp = loc(Exp::Let("x".into(), dummy_typ(), bound, body));
        assert!(env.narrow_exp(&exp).is_none()); // unknown bound → not narrowable
    }

    #[test]
    fn narrow_app_abs_propagates_known_argument() {
        // `(fn x => x)(-3)` — argument is -3 (Int), body should narrow to Int.
        let env = NarrowEnv::new();
        let body = Box::new(loc(Exp::Rel(0))); // fn body: x
        let abs = Box::new(loc(Exp::Abs("x".into(), dummy_typ(), dummy_typ(), body)));
        let arg = Box::new(loc(Exp::Prim(Prim::Int(-3)))); // argument: -3
        let exp = loc(Exp::App(abs, arg));
        let narrowed = env.narrow_exp(&exp).expect("(fn x => x)(-3) should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Int(_))); // -3 < 0 → Int
    }

    #[test]
    fn narrow_binop_addition_of_known_prims() {
        // `3 + 4` — both sides known, result is 7 (Uint).
        let env = NarrowEnv::new();
        let left = Box::new(loc(Exp::Prim(Prim::Int(3))));
        let right = Box::new(loc(Exp::Prim(Prim::Int(4))));
        let exp = loc(Exp::Binop(BinopIntness::Int, "+".into(), left, right));
        let narrowed = env.narrow_exp(&exp).expect("3 + 4 should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Uint(_))); // 7 >= 0 → Uint
    }

    #[test]
    fn narrow_binop_subtraction_yields_negative() {
        // `3 - 10` → -7 → Int(I8).
        let env = NarrowEnv::new();
        let left = Box::new(loc(Exp::Prim(Prim::Int(3))));
        let right = Box::new(loc(Exp::Prim(Prim::Int(10))));
        let exp = loc(Exp::Binop(BinopIntness::Int, "-".into(), left, right));
        let narrowed = env.narrow_exp(&exp).expect("3 - 10 should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Int(_))); // -7 < 0 → Int
    }

    #[test]
    fn narrow_binop_with_unknown_operand_returns_none() {
        // `Rel(0) + 4` where Rel(0) is unknown → cannot constant-fold.
        let env = NarrowEnv::new().push_unknown();
        let left = Box::new(loc(Exp::Rel(0)));
        let right = Box::new(loc(Exp::Prim(Prim::Int(4))));
        let exp = loc(Exp::Binop(BinopIntness::Int, "+".into(), left, right));
        assert!(env.narrow_exp(&exp).is_none()); // unknown operand → not narrowable
    }

    #[test]
    fn narrow_unop_negation_of_known_int() {
        // `-42` → -42 → Int(I8).
        let env = NarrowEnv::new();
        let operand = Box::new(loc(Exp::Prim(Prim::Int(42))));
        let exp = loc(Exp::Unop("-".into(), operand));
        let narrowed = env.narrow_exp(&exp).expect("-42 should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Int(_))); // -42 < 0 → Int
    }

    #[test]
    fn narrow_case_selects_matching_prim_arm() {
        // `case 1 of | 1 => -5 | 2 => 200` → selects arm 1 (-5) → Int.
        let env = NarrowEnv::new();
        let span = Span::dummy();
        let scrutinee = Box::new(loc(Exp::Prim(Prim::Int(1)))); // known discriminant
        let arm1_pat = Located::new(Pat::Prim(Prim::Int(1)), span.clone());
        let arm1_body = loc(Exp::Prim(Prim::Int(-5)));
        let arm2_pat = Located::new(Pat::Prim(Prim::Int(2)), span.clone());
        let arm2_body = loc(Exp::Prim(Prim::Int(200)));
        let case_meta = CaseMeta {
            disc: dummy_typ(),
            result: dummy_typ(),
        };
        let exp = loc(Exp::Case(
            scrutinee,
            vec![(arm1_pat, arm1_body), (arm2_pat, arm2_body)],
            case_meta,
        ));
        let narrowed = env
            .narrow_exp(&exp)
            .expect("case with known discriminant should narrow");
        assert!(matches!(narrowed, NarrowedNumeric::Int(_))); // arm1 body is -5 → Int
    }

    #[test]
    fn narrow_named_with_table_entry() {
        // A Named reference that has a recorded narrowing in the table should narrow.
        let mut table = NarrowingTable::new();
        table
            .named
            .insert(77, NarrowedNumeric::Uint(crate::primitives::UintWidth::U8));
        let env = NarrowEnv::new().with_table(&table);
        let exp = loc(Exp::Named(77));
        let narrowed = env
            .narrow_exp(&exp)
            .expect("Named with table entry should narrow");
        assert!(matches!(
            narrowed,
            NarrowedNumeric::Uint(crate::primitives::UintWidth::U8)
        ));
    }

    #[test]
    fn analyze_records_literal_decl() {
        // A top-level `val x = 255` should appear in the narrowing table as Uint(U8).
        use crate::monomorphized::Decl;
        let decl = Located::dummy(Decl::Val(
            "x".into(),                     // name
            42,                             // id
            dummy_typ(),                    // type
            loc(Exp::Prim(Prim::Int(255))), // body: literal 255
            "x".into(),                     // sql name
        ));
        let file: crate::monomorphized::File = (vec![decl], vec![]);
        let table = analyze(&file);
        let narrowed = table
            .lookup_named(42)
            .expect("literal decl should be recorded");
        assert!(matches!(
            narrowed,
            NarrowedNumeric::Uint(crate::primitives::UintWidth::U8)
        ));
    }

    #[test]
    fn analyze_propagates_named_reference_to_later_decl() {
        // val a = 128; val b = a   →   b should be Uint(U8) too (128 fits in U8).
        use crate::monomorphized::Decl;
        let decl_a = Located::dummy(Decl::Val(
            "a".into(),
            10,
            dummy_typ(),
            loc(Exp::Prim(Prim::Int(128))),
            "a".into(),
        ));
        // b references a by Named(10)
        let decl_b = Located::dummy(Decl::Val(
            "b".into(),
            11,
            dummy_typ(),
            loc(Exp::Named(10)),
            "b".into(),
        ));
        let file: crate::monomorphized::File = (vec![decl_a, decl_b], vec![]);
        let table = analyze(&file);
        // a is recorded
        assert!(table.lookup_named(10).is_some(), "a should be in table");
        // b's narrowing is not automatically propagated through Named in analyze()
        // because known_prim does not resolve Named — only narrow_exp does via the table.
        // b is in the table because narrow_exp(Named(10)) looks up the table.
        assert!(table.lookup_named(11).is_some(), "b should be in table");
    }
}
