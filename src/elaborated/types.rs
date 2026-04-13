//! Canonical elaborated type-system nodes.
//!
//! This module is the single home for:
//! - kind AST (`Kind`, `KUnif`);
//! - constructor/type AST (`Constructor`, `CUnif`);
//! - traditional primitive Ur/Web type tags (`Types`).
//!
//! ## LangSec strings (Ur/Web policy)
//!
//! String-shaped identifiers that cross **strict** boundaries (parsers, DSLs such as
//! Zencode/Zenroom, generated FFI names) need predictable spelling. For **string
//! handling only**, Ur/Web treats ASCII **space** (`U+0020`) and **underscore**
//! (`U+005F`) as **interchangeable** on input and output: comparisons and
//! canonicalization should use [`langsec_string_identifiers_equivalent`] or
//! [`canonicalize_langsec_string_identifier`] so spellings such as `Hello World!` and
//! `Hello_World!` align. Other characters are unchanged; this is **not** a general
//! Unicode normalization policy.
//!
//! ## Typed homogeneous arrays (methodology)
//!
//! Following the same discipline as Zencode’s “`type` array” declarations, Ur/Web does
//! **not** use a single generic “array of anything” tag at this classifier layer: each
//! homogeneous array has its **own** `Types` variant (`StringArray`, `IntArray`, …).
//! Zenroom’s extra scalar kinds (`hex`, `base64`, …) are **not** modeled here until the
//! surface language exposes them; [`Types::Blob`] covers opaque binary payloads at this
//! level.

use std::fmt;
use std::hash::Hash;
use std::sync::{Arc, Mutex};

use crate::error_types::{Located, Span};

/// Normalizes one character for [`langsec_string_identifiers_equivalent`].
#[inline]
fn fold_langsec_string_space_or_underscore(character: char) -> char {
    match character {
        ' ' | '_' => '_',
        other => other,
    }
}

/// Returns true when two strings match under Ur/Web LangSec string-identifier rules.
///
/// ASCII spaces and underscores are equivalent in **both** arguments (suitable for
/// comparing external DSL tokens, JSON keys, and internal spellings).
pub fn langsec_string_identifiers_equivalent(left: &str, right: &str) -> bool {
    left.chars()
        .map(fold_langsec_string_space_or_underscore)
        .eq(right.chars().map(fold_langsec_string_space_or_underscore))
}

/// Returns a copy of `text` with LangSec string-identifier folding applied (spaces and
/// underscores both become underscore) for stable keys and hashes.
pub fn canonicalize_langsec_string_identifier(text: &str) -> String {
    text.chars()
        .map(fold_langsec_string_space_or_underscore)
        .collect()
}

/// Traditional primitive Ur/Web type tags (kind-level classifiers only).
///
/// These variants intentionally carry **no** runtime evidence (no literals, no heap
/// blobs): values and proofs live on constructors / expressions, not on `Types`.
///
/// [`Types::Function`] and [`Types::Error`] refine Ur’s kind `Type` (`*`) for elaborated
/// **spines** that still use unchanged surface syntax (`t1 -> t2`, `transaction t`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Types {
    /// Compatibility classifier for unknown / not-yet-specialized type facts.
    Any,
    /// Functions are a first class citizen type in the rust ur web compiler type system.
    /// the classic ur web syntax remain the same, but under the hood, functions are handled
    /// as a type. We are using dependent types to make types flexible and easy to reason about.
    /// This way, functions can take other functions as arguments and return other functions as results.
    /// Also records can include functions as fields, as long as they are not recursive, and dont 
    /// ruin anything on the client side.
    Function,
    /// Errors are a first class citizen type in the rust ur web compiler type system.
    /// This works similar as in the rust type system, where errors are a type that can be returned by a function.
    /// But again, the ur/web syntax remains the same, and the error type is not special in any way.
    /// But through dependent types, we can make errors more flexible and easy to reason about.
    Error,
    String,
    Int,
    Uint,
    /// Number is a slightly looser number type, that can represent any number, including integers and floats.
    Number,
    Bool,
    Float,
    Char,
    Unit,
    Time,
    Blob,
    /// Homogeneous array whose elements are classified as [`Types::String`].
    StringArray,
    /// Homogeneous array whose elements are classified as [`Types::Int`].
    IntArray,
    /// Homogeneous array whose elements are classified as [`Types::Uint`].
    UintArray,
    /// Homogeneous array whose elements are classified as [`Types::Number`].
    NumberArray,
    /// Homogeneous array whose elements are classified as [`Types::Float`].
    FloatArray,
    /// Homogeneous array whose elements are classified as [`Types::Bool`].
    BoolArray,
    /// Homogeneous array whose elements are classified as [`Types::Char`].
    CharArray,
    /// Homogeneous array whose elements are classified as [`Types::Time`].
    TimeArray,
    /// Homogeneous array whose elements are classified as [`Types::Blob`].
    BlobArray,
    /// Homogeneous array whose elements are classified as [`Types::Function`] (Ur `list (t1 -> t2)`).
    FunctionArray,
    /// Homogeneous array whose elements are classified as [`Types::Error`] (Ur `list (transaction t)`).
    ErrorArray,
}

/// Kind-level primitive tags used in gradual typing checks (`Kind::Typed`).
pub trait RuntimePrimitiveTag: Copy + Eq + Hash + fmt::Display {
    /// Returns the single classifier that stands for “any runtime primitive”.
    fn compatibility_top() -> Self;

    /// Returns true when this tag is [`RuntimePrimitiveTag::compatibility_top`].
    fn is_compatibility_top(self) -> bool;

    /// Returns true when two classifiers may unify at a runtime-type kind boundary.
    ///
    /// Default: symmetric [`RuntimePrimitiveTag::runtime_primitive_instance_of`] (either
    /// side may be the compatibility top).
    fn runtime_primitive_compatible(self, other: Self) -> bool {
        self.runtime_primitive_instance_of(other) || other.runtime_primitive_instance_of(self)
    }

    /// Returns true when `self` is no more informative than `wider` along the
    /// declarative “instance-of” preorder induced by the top element (`Any` absorbs all).
    fn runtime_primitive_instance_of(self, wider: Self) -> bool;
}

impl RuntimePrimitiveTag for Types {
    fn compatibility_top() -> Self {
        Types::Any
    }

    fn is_compatibility_top(self) -> bool {
        self == Types::Any
    }

    fn runtime_primitive_instance_of(self, wider: Self) -> bool {
        wider.is_compatibility_top() || self == wider
    }
}

/// Refinements of Ur’s kind `Type` (`*`) used by elaboration for non-scalar classifiers
/// ([`Types::Function`], [`Types::Error`]) while leaving surface syntax unchanged.
pub trait StarClassifierRefinement: RuntimePrimitiveTag {
    /// Returns true for [`Types::Function`] and [`Types::Error`] (not [`Types::Any`], not scalars).
    fn is_star_structural_refinement(self) -> bool;
}

impl StarClassifierRefinement for Types {
    fn is_star_structural_refinement(self) -> bool {
        matches!(
            self,
            Types::Function | Types::Error | Types::FunctionArray | Types::ErrorArray
        )
    }
}

/// Optional hook for tooling that groups “evidence-bearing” refinements next to
/// [`RuntimePrimitiveTag`] (reserved for future dependent-style evidence paths).
pub trait DependentRefinementHost: StarClassifierRefinement {}

impl DependentRefinementHost for Types {}

impl Types {
    /// Returns true when this type tag is a concrete primitive (not [`Types::Any`]).
    pub fn is_concrete(self) -> bool {
        !self.is_any()
    }

    /// Returns true for numeric primitives.
    pub fn is_numeric(self) -> bool {
        matches!(
            self,
            Types::Int | Types::Uint | Types::Float | Types::Number
        )
    }

    /// Returns true when this type tag is the top/unknown classifier.
    pub fn is_any(self) -> bool {
        self.is_compatibility_top()
    }

    /// Returns true when this tag names a homogeneous array with a fixed element classifier.
    pub fn is_homogeneous_array(self) -> bool {
        matches!(
            self,
            Types::StringArray
                | Types::IntArray
                | Types::UintArray
                | Types::NumberArray
                | Types::FloatArray
                | Types::BoolArray
                | Types::CharArray
                | Types::TimeArray
                | Types::BlobArray
                | Types::FunctionArray
                | Types::ErrorArray
        )
    }

    /// If this tag is `*Array`, returns the element [`Types`]; otherwise returns `None`.
    pub fn homogeneous_array_element_type(self) -> Option<Types> {
        Some(match self {
            Types::StringArray => Types::String,
            Types::IntArray => Types::Int,
            Types::UintArray => Types::Uint,
            Types::NumberArray => Types::Number,
            Types::FloatArray => Types::Float,
            Types::BoolArray => Types::Bool,
            Types::CharArray => Types::Char,
            Types::TimeArray => Types::Time,
            Types::BlobArray => Types::Blob,
            Types::FunctionArray => Types::Function,
            Types::ErrorArray => Types::Error,
            _ => return None,
        })
    }
}

pub type KUnifRef = Arc<Mutex<KUnif>>;

#[derive(Debug, Clone)]
pub enum KUnif {
    /// Not yet solved; the closure checks validity.
    Unknown,
    Known(Box<LocatedKind>),
}

#[derive(Debug, Clone)]
pub enum Kind {
    /// Refined runtime type tag used by gradual migration.
    Typed(Types),
    Arrow(Box<LocatedKind>, Box<LocatedKind>),
    Name,
    Record(Box<LocatedKind>),
    Unit,
    Tuple(Vec<LocatedKind>),

    /// Unification variable for a kind.
    Unif(Span, String, KUnifRef),
    /// Tuple unification variable (partially known).
    TupleUnif(Span, Vec<(usize, LocatedKind)>, KUnifRef),

    /// De Bruijn index into the kind environment.
    Rel(usize),
}

impl Kind {
    /// Returns the compatibility top classifier used by existing elaboration paths.
    pub fn any_type() -> Self {
        Kind::Typed(Types::Any)
    }

    /// Builds a refined type-kind from a concrete primitive tag.
    pub fn typed(type_tag: Types) -> Self {
        Kind::Typed(type_tag)
    }

    /// Returns true when this kind represents a runtime type classifier.
    pub fn is_runtime_type_classifier(&self) -> bool {
        matches!(self, Kind::Typed(_))
    }

    /// Returns the optional refined primitive tag carried by this kind.
    pub fn as_type_tag(&self) -> Option<Types> {
        match self {
            Kind::Typed(type_tag) => Some(*type_tag),
            _ => None,
        }
    }

    /// Returns true for `Typed(Any)`.
    pub fn is_any_typed(&self) -> bool {
        matches!(self, Kind::Typed(Types::Any))
    }

    /// Checks whether two kind heads are compatible runtime type classifiers.
    ///
    /// - non-runtime kinds are incompatible;
    /// - `Typed(Any)` is compatible with any runtime classifier;
    /// - concrete tags must match exactly.
    pub fn runtime_type_compatible_with(&self, other: &Self) -> bool {
        match (self.as_type_tag(), other.as_type_tag()) {
            (Some(left_type_tag), Some(right_type_tag)) => {
                RuntimePrimitiveTag::runtime_primitive_compatible(left_type_tag, right_type_tag)
            }
            _ => false,
        }
    }

    /// Returns true when `self`’s runtime primitive tag refines `other`’s (instance-of preorder).
    ///
    /// Non-[`Kind::Typed`] kinds yield `false`; otherwise delegates to
    /// [`RuntimePrimitiveTag::runtime_primitive_instance_of`].
    pub fn runtime_type_instance_of(&self, other: &Self) -> bool {
        match (self.as_type_tag(), other.as_type_tag()) {
            (Some(instance_tag), Some(wider_tag)) => {
                RuntimePrimitiveTag::runtime_primitive_instance_of(instance_tag, wider_tag)
            }
            _ => false,
        }
    }
}

impl fmt::Display for Types {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Types::Any => "Any",
            Types::Function => "Function",
            Types::Error => "Error",
            Types::String => "String",
            Types::Int => "Int",
            Types::Uint => "Uint",
            Types::Number => "Number",
            Types::Bool => "Bool",
            Types::Float => "Float",
            Types::Char => "Char",
            Types::Unit => "Unit",
            Types::Time => "Time",
            Types::Blob => "Blob",
            Types::StringArray => "StringArray",
            Types::IntArray => "IntArray",
            Types::UintArray => "UintArray",
            Types::NumberArray => "NumberArray",
            Types::FloatArray => "FloatArray",
            Types::BoolArray => "BoolArray",
            Types::CharArray => "CharArray",
            Types::TimeArray => "TimeArray",
            Types::BlobArray => "BlobArray",
            Types::FunctionArray => "FunctionArray",
            Types::ErrorArray => "ErrorArray",
        };
        write!(formatter, "{name}")
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Typed(type_tag) => write!(formatter, "Type<{type_tag}>"),
            Kind::Arrow(_, _) => write!(formatter, "<kind-arrow>"),
            Kind::Name => write!(formatter, "Name"),
            Kind::Record(_) => write!(formatter, "<kind-record>"),
            Kind::Unit => write!(formatter, "Unit"),
            Kind::Tuple(_) => write!(formatter, "<kind-tuple>"),
            Kind::Unif(_, label, _) => write!(formatter, "?{label}"),
            Kind::TupleUnif(_, _, _) => write!(formatter, "?tuple"),
            Kind::Rel(index) => write!(formatter, "'{index}"),
        }
    }
}

/// Shared trait for values that expose an elaborated runtime type classifier.
pub trait RuntimeTypeClassifier {
    /// Returns the optional runtime type tag.
    fn runtime_type_tag(&self) -> Option<Types>;

    /// Returns true if this value is a runtime type classifier.
    fn is_runtime_type_classifier(&self) -> bool {
        self.runtime_type_tag().is_some()
    }

    /// Returns true if the classifier is `Any`.
    fn is_any_runtime_type(&self) -> bool {
        self.runtime_type_tag()
            .map(RuntimePrimitiveTag::is_compatibility_top)
            .unwrap_or(false)
    }
}

impl RuntimeTypeClassifier for Kind {
    fn runtime_type_tag(&self) -> Option<Types> {
        self.as_type_tag()
    }
}

impl RuntimeTypeClassifier for LocatedKind {
    fn runtime_type_tag(&self) -> Option<Types> {
        self.node.as_type_tag()
    }
}

pub type LocatedKind = Located<Kind>;

pub type CUnifRef = Arc<Mutex<CUnif>>;

#[derive(Debug, Clone)]
pub enum CUnif {
    Unknown,
    Known(Box<LocatedConstructor>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Explicitness {
    Explicit,
    Implicit,
}

/// Structured view for Ur/Web constructor nodes.
#[derive(Debug, Clone)]
pub enum Constructor {
    TFun(Box<LocatedConstructor>, Box<LocatedConstructor>),
    TCFun(
        Explicitness,
        String,
        Box<LocatedKind>,
        Box<LocatedConstructor>,
    ),
    TRecord(Box<LocatedConstructor>),
    TDisjoint(
        Box<LocatedConstructor>,
        Box<LocatedConstructor>,
        Box<LocatedConstructor>,
    ),

    /// De Bruijn index.
    Rel(usize),
    /// Globally unique name (from `CNamed`).
    Named(usize),
    /// Module projection: `module.path.name`.
    ModProj(usize, Vec<String>, String),
    App(Box<LocatedConstructor>, Box<LocatedConstructor>),
    Abs(String, Box<LocatedKind>, Box<LocatedConstructor>),

    KAbs(String, Box<LocatedConstructor>),
    KApp(Box<LocatedConstructor>, Box<LocatedKind>),
    TKFun(String, Box<LocatedConstructor>),

    Name(String),

    Record(
        Box<LocatedKind>,
        Vec<(LocatedConstructor, LocatedConstructor)>,
    ),
    Concat(Box<LocatedConstructor>, Box<LocatedConstructor>),
    Map(Box<LocatedKind>, Box<LocatedKind>),

    Unit,

    Tuple(Vec<LocatedConstructor>),
    Proj(Box<LocatedConstructor>, usize),

    Error,
    /// Elaboration-time unification variable.
    Unif(usize, Span, Box<LocatedKind>, String, CUnifRef),
}

pub type LocatedConstructor = Located<Constructor>;

/// Construct `Kind::Typed(...)` succinctly.
#[macro_export]
macro_rules! elab_kind_typed {
    ($type_tag:expr) => {
        $crate::elaborated::Kind::Typed($type_tag)
    };
}

/// Construct `Kind::Typed(Types::Any)`.
#[macro_export]
macro_rules! elab_kind_any {
    () => {
        $crate::elaborated::Kind::Typed($crate::elaborated::Types::Any)
    };
}

/// Canonical type display API lives under `types.rs`.
pub mod type_display {
    //! Pretty-print elaborated [`crate::elaborated::Constructor`], [`crate::elaborated::Kind`],
    //! signatures, patterns, and expressions for LSP hovers and **catalog diagnostic placeholders**
    //! (never raw `Debug` of `Located` / unification cells).
    //!
    //! [`format_constructor`] and [`format_kind`] cap recursion depth to avoid blowups on cyclic types.

    use std::fmt::Write;

    use crate::datatype_kind::DatatypeKind;
    use crate::elaborated::{
        Constructor, Expression, ImportMode, Kind, LocatedConstructor, LocatedExpression,
        LocatedKind, LocatedPattern, LocatedSignature, LocatedSignatureItem, Pattern,
        PatternConstructor, Signature, SignatureItem, Types,
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

    pub(crate) fn write_constructor_into(
        output_buffer: &mut dyn std::fmt::Write,
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

    pub(crate) fn write_kind_into(
        output_buffer: &mut dyn std::fmt::Write,
        kind: &LocatedKind,
        recursion_depth: u32,
    ) -> std::fmt::Result {
        if recursion_depth > MAX_RECURSION_DEPTH {
            return write!(output_buffer, "…");
        }
        match &kind.node {
            Kind::Typed(type_tag) => {
                if *type_tag == Types::Any {
                    write!(output_buffer, "Type")
                } else {
                    write!(output_buffer, "Type<{type_tag}>")
                }
            }
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
            Kind::Unif(_, name, _) => write!(output_buffer, "?{}", name),
            Kind::TupleUnif(_, _, _) => write!(output_buffer, "?tuple"),
            Kind::Rel(de_bruijn_index) => write!(output_buffer, "'{}", de_bruijn_index),
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

    /// Append one [`SignatureItem`] summary into `output_buffer`, respecting `recursion_depth`.
    ///
    /// # Parameters
    ///
    /// * `output_buffer` — Destination string.
    /// * `item` — Signature item to describe.
    /// * `recursion_depth` — Current recursion level (caps at [`MAX_RECURSION_DEPTH`]).
    ///
    /// # Errors
    ///
    /// Returns [`std::fmt::Error`] only if writing fails.
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
            SignatureItem::DatatypeImp { name, .. } => {
                write!(output_buffer, "datatype `{}` (import)", name)
            }
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

    /// Append a [`Signature`] summary (braced functor / `where` / projection forms).
    ///
    /// # Parameters
    ///
    /// * `output_buffer` — Destination string.
    /// * `signature` — Signature tree to print.
    /// * `recursion_depth` — Current recursion level against [`MAX_RECURSION_DEPTH`].
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

    /// Emit a short `[enum]` / `[option]` / `[dt]` tag before datatype pattern heads.
    ///
    /// # Parameters
    ///
    /// * `output_buffer` — Destination string.
    /// * `datatype_kind` — Runtime representation class for the datatype.
    fn write_datatype_kind_hint(
        output_buffer: &mut String,
        datatype_kind: DatatypeKind,
    ) -> std::fmt::Result {
        let label = match datatype_kind {
            DatatypeKind::Enum => "enum",
            DatatypeKind::Option => "option",
            DatatypeKind::Default => "dt",
        };
        write!(output_buffer, "[{}] ", label)
    }

    /// Recursively append a [`Pattern`] for diagnostics.
    ///
    /// # Parameters
    ///
    /// * `output_buffer` — Destination string.
    /// * `pattern` — Elaborated pattern.
    /// * `recursion_depth` — Depth guard shared with constructor printing.
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
            Pattern::Constructor(
                datatype_kind,
                pattern_constructor,
                type_arguments,
                optional_subpattern,
            ) => {
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
                for (field_index, (field_label, subpattern, _field_type)) in
                    field_rows.iter().enumerate()
                {
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

    /// Compact literal for [`Prim`] (truncate long strings).
    ///
    /// # Parameters
    ///
    /// * `output_buffer` — Destination string.
    /// * `primitive` — Primitive value from the elaborator.
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

    /// Recursively append an [`Expression`] for wildcard / context messages.
    ///
    /// # Parameters
    ///
    /// * `output_buffer` — Destination string.
    /// * `expression` — Elaborated expression.
    /// * `recursion_depth` — Depth guard aligned with [`write_constructor_into`].
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
            Expression::Abs(binder_name, domain_constructor, codomain_constructor, body) => {
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
}
/// Canonical type operation API lives under `types.rs`.
pub mod type_operations {
    //! Constructor and kind substitution / normalization operations.
    //!
    //! Immediate-child structure walks can use [`crate::elaborated::type_tree`] so new variants
    //! stay covered by shared edge lists. Translated from `elab_ops.sml`.
    //!
    //! Public helpers document `# Arguments`, `# Returns`, and `# Errors` (including [`SubUnif`])
    //! where de Bruijn level conventions are not obvious from types alone.
    //!
    //! **Bounded work:** [`hnorm_con`] uses a thread-local depth counter; solved-[`Constructor::Unif`] peeling
    //! uses [`PEEL_SOLVED_CONSTRUCTOR_UNIF_CHAIN_MAX_STEPS`] so alias chains cannot cycle without bound.

    use std::sync::Arc;

    use crate::elaborated::{
        CUnif, CUnifRef, Constructor, Kind, LocatedConstructor, LocatedKind,
        StarClassifierRefinement, Types,
    };
    use crate::error_types::Located;

    // ---------------------------------------------------------------------------
    // Internal helpers
    // ---------------------------------------------------------------------------

    /// Lift every free `Kind::Rel(n)` with `n >= bound` by `by`.
    fn lift_kind_in_kind_bound(by: usize, bound: usize, kind: LocatedKind) -> LocatedKind {
        let span = kind.span.clone();
        let node =
            match kind.node {
                Kind::Rel(n) => {
                    if n < bound {
                        Kind::Rel(n) // bound: not lifted
                    } else {
                        // Saturating prevents overflow when n is a sentinel large value from an error path.
                        Kind::Rel(n.saturating_add(by))
                    }
                }
                Kind::Arrow(domain_kind, range_kind) => Kind::Arrow(
                    Box::new(lift_kind_in_kind_bound(by, bound, *domain_kind)),
                    Box::new(lift_kind_in_kind_bound(by, bound, *range_kind)),
                ),
                Kind::Record(record_element_kind) => Kind::Record(Box::new(
                    lift_kind_in_kind_bound(by, bound, *record_element_kind),
                )),
                Kind::Tuple(components) => Kind::Tuple(
                    components
                        .into_iter()
                        .map(|component_kind| lift_kind_in_kind_bound(by, bound, component_kind))
                        .collect(),
                ),
                other => other,
            };
        Located { node, span }
    }

    /// Substitute `rep` for `Kind::Rel(xn)`, adjusting indices.
    fn sub_kind_in_kind_bound(
        by: usize,
        xn: usize,
        rep: &LocatedKind,
        kind: LocatedKind,
    ) -> LocatedKind {
        let span = kind.span.clone();
        let node =
            match kind.node {
                Kind::Rel(n) => {
                    if n == xn {
                        return lift_kind_in_kind_bound(by, 0, rep.clone());
                    } else if n > xn {
                        Kind::Rel(n - 1)
                    } else {
                        Kind::Rel(n)
                    }
                }
                Kind::Arrow(domain_kind, range_kind) => Kind::Arrow(
                    Box::new(sub_kind_in_kind_bound(by, xn, rep, *domain_kind)),
                    Box::new(sub_kind_in_kind_bound(by, xn, rep, *range_kind)),
                ),
                Kind::Record(record_element_kind) => Kind::Record(Box::new(
                    sub_kind_in_kind_bound(by, xn, rep, *record_element_kind),
                )),
                Kind::Tuple(components) => Kind::Tuple(
                    components
                        .into_iter()
                        .map(|component_kind| sub_kind_in_kind_bound(by, xn, rep, component_kind))
                        .collect(),
                ),
                other => other,
            };
        Located { node, span }
    }

    /// Lift `Kind::Rel(n)` for `n >= bound` by 1 within a constructor.
    fn lift_kind_in_con_bound(bound: usize, constructor: LocatedConstructor) -> LocatedConstructor {
        let span = constructor.span.clone();
        let node = match constructor.node {
            Constructor::TFun(domain, codomain) => Constructor::TFun(
                Box::new(lift_kind_in_con_bound(bound, *domain)),
                Box::new(lift_kind_in_con_bound(bound, *codomain)),
            ),
            Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
                exp,
                x,
                Box::new(lift_kind_in_kind_bound(1, bound, *k)),
                // TCFun is a constructor binder (not kind), so `bound` for kind variables is unchanged.
                Box::new(lift_kind_in_con_bound(bound, *body)),
            ),
            Constructor::TRecord(row) => {
                Constructor::TRecord(Box::new(lift_kind_in_con_bound(bound, *row)))
            }
            Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
                Constructor::TDisjoint(
                    Box::new(lift_kind_in_con_bound(bound, *disjoint_left_row)),
                    Box::new(lift_kind_in_con_bound(bound, *disjoint_right_row)),
                    Box::new(lift_kind_in_con_bound(bound, *body_constructor)),
                )
            }
            Constructor::App(functor, argument) => Constructor::App(
                Box::new(lift_kind_in_con_bound(bound, *functor)),
                Box::new(lift_kind_in_con_bound(bound, *argument)),
            ),
            Constructor::Abs(x, k, body) => Constructor::Abs(
                x,
                Box::new(lift_kind_in_kind_bound(1, bound, *k)),
                Box::new(lift_kind_in_con_bound(bound, *body)),
            ),
            Constructor::KAbs(x, body) => {
                Constructor::KAbs(x, Box::new(lift_kind_in_con_bound(bound + 1, *body)))
            }
            Constructor::KApp(functor, kind_argument) => Constructor::KApp(
                Box::new(lift_kind_in_con_bound(bound, *functor)),
                Box::new(lift_kind_in_kind_bound(1, bound, *kind_argument)),
            ),
            Constructor::TKFun(x, body) => {
                Constructor::TKFun(x, Box::new(lift_kind_in_con_bound(bound + 1, *body)))
            }
            Constructor::Record(row_kind, field_pairs) => Constructor::Record(
                Box::new(lift_kind_in_kind_bound(1, bound, *row_kind)),
                field_pairs
                    .into_iter()
                    .map(|(field_name, field_type)| {
                        (
                            lift_kind_in_con_bound(bound, field_name),
                            lift_kind_in_con_bound(bound, field_type),
                        )
                    })
                    .collect(),
            ),
            Constructor::Concat(left_row, right_row) => Constructor::Concat(
                Box::new(lift_kind_in_con_bound(bound, *left_row)),
                Box::new(lift_kind_in_con_bound(bound, *right_row)),
            ),
            Constructor::Map(map_domain_kind, map_codomain_kind) => Constructor::Map(
                Box::new(lift_kind_in_kind_bound(1, bound, *map_domain_kind)),
                Box::new(lift_kind_in_kind_bound(1, bound, *map_codomain_kind)),
            ),
            Constructor::Tuple(elements) => Constructor::Tuple(
                elements
                    .into_iter()
                    .map(|element| lift_kind_in_con_bound(bound, element))
                    .collect(),
            ),
            Constructor::Proj(base, index) => {
                Constructor::Proj(Box::new(lift_kind_in_con_bound(bound, *base)), index)
            }
            other => other,
        };
        Located { node, span }
    }

    // ---------------------------------------------------------------------------
    // Public lifting / substitution API
    // ---------------------------------------------------------------------------

    /// Lift every free [`Kind::Rel`] de Bruijn index by 1 (enter one kind binder).
    ///
    /// # Arguments
    ///
    /// * `kind` — Kind to adjust.
    ///
    /// # Returns
    ///
    /// Kind with indices `n >= 0` incremented.
    pub fn lift_kind_in_kind(kind: LocatedKind) -> LocatedKind {
        lift_kind_in_kind_bound(1, 0, kind)
    }

    /// Substitute `replacement` for [`Kind::Rel`] index `kind_index` in `kind`, adjusting other free indices.
    ///
    /// # Arguments
    ///
    /// * `kind_index` — de Bruijn level of the variable to replace.
    /// * `replacement` — Kind substituted in; lifted across binders as in SML `subKindInKind`.
    /// * `kind` — Kind to transform.
    ///
    /// # Returns
    ///
    /// Kind after substitution.
    pub fn sub_kind_in_kind(
        kind_index: usize,
        replacement: &LocatedKind,
        kind: LocatedKind,
    ) -> LocatedKind {
        sub_kind_in_kind_bound(0, kind_index, replacement, kind)
    }

    /// Lift every free [`Kind::Rel`] inside `constructor` by 1 (cross one kind binder in `TCFun`, `Abs`, etc.).
    ///
    /// # Arguments
    ///
    /// * `constructor` — Constructor whose embedded kinds are adjusted.
    ///
    /// # Returns
    ///
    /// Constructor with incremented kind indices under those binders.
    pub fn lift_kind_in_con(constructor: LocatedConstructor) -> LocatedConstructor {
        lift_kind_in_con_bound(0, constructor)
    }

    /// Substitute `replacement` for [`Kind::Rel`] `kind_index` throughout `constructor`.
    ///
    /// # Arguments
    ///
    /// * `kind_index` — Variable level to replace.
    /// * `replacement` — Kind to splice in.
    /// * `constructor` — Target constructor.
    ///
    /// # Returns
    ///
    /// Constructor after kind substitution.
    pub fn sub_kind_in_con(
        kind_index: usize,
        replacement: &LocatedKind,
        constructor: LocatedConstructor,
    ) -> LocatedConstructor {
        sub_kind_in_con_inner(0, kind_index, replacement, constructor)
    }

    fn sub_kind_in_con_inner(
        by: usize,
        xn: usize,
        rep: &LocatedKind,
        constructor: LocatedConstructor,
    ) -> LocatedConstructor {
        let span = constructor.span.clone();
        let node = match constructor.node {
            Constructor::TFun(domain, codomain) => Constructor::TFun(
                Box::new(sub_kind_in_con_inner(by, xn, rep, *domain)),
                Box::new(sub_kind_in_con_inner(by, xn, rep, *codomain)),
            ),
            Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
                exp,
                x,
                Box::new(sub_kind_in_kind_bound(by, xn, rep, *k)),
                // TCFun is a constructor binder (not kind), so kind-variable indices are unchanged.
                Box::new(sub_kind_in_con_inner(by, xn, rep, *body)),
            ),
            Constructor::TRecord(row) => {
                Constructor::TRecord(Box::new(sub_kind_in_con_inner(by, xn, rep, *row)))
            }
            Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
                Constructor::TDisjoint(
                    Box::new(sub_kind_in_con_inner(by, xn, rep, *disjoint_left_row)),
                    Box::new(sub_kind_in_con_inner(by, xn, rep, *disjoint_right_row)),
                    Box::new(sub_kind_in_con_inner(by, xn, rep, *body_constructor)),
                )
            }
            Constructor::App(functor, argument) => Constructor::App(
                Box::new(sub_kind_in_con_inner(by, xn, rep, *functor)),
                Box::new(sub_kind_in_con_inner(by, xn, rep, *argument)),
            ),
            Constructor::Abs(x, k, body) => Constructor::Abs(
                x,
                Box::new(sub_kind_in_kind_bound(by, xn, rep, *k)),
                Box::new(sub_kind_in_con_inner(by, xn, rep, *body)),
            ),
            Constructor::KAbs(x, body) => Constructor::KAbs(
                x,
                Box::new(sub_kind_in_con_inner(by + 1, xn + 1, rep, *body)),
            ),
            Constructor::KApp(functor, kind_argument) => Constructor::KApp(
                Box::new(sub_kind_in_con_inner(by, xn, rep, *functor)),
                Box::new(sub_kind_in_kind_bound(by, xn, rep, *kind_argument)),
            ),
            Constructor::TKFun(x, body) => Constructor::TKFun(
                x,
                Box::new(sub_kind_in_con_inner(by + 1, xn + 1, rep, *body)),
            ),
            Constructor::Record(row_kind, field_pairs) => Constructor::Record(
                Box::new(sub_kind_in_kind_bound(by, xn, rep, *row_kind)),
                field_pairs
                    .into_iter()
                    .map(|(field_name, field_type)| {
                        (
                            sub_kind_in_con_inner(by, xn, rep, field_name),
                            sub_kind_in_con_inner(by, xn, rep, field_type),
                        )
                    })
                    .collect(),
            ),
            Constructor::Concat(left_row, right_row) => Constructor::Concat(
                Box::new(sub_kind_in_con_inner(by, xn, rep, *left_row)),
                Box::new(sub_kind_in_con_inner(by, xn, rep, *right_row)),
            ),
            Constructor::Map(map_domain_kind, map_codomain_kind) => Constructor::Map(
                Box::new(sub_kind_in_kind_bound(by, xn, rep, *map_domain_kind)),
                Box::new(sub_kind_in_kind_bound(by, xn, rep, *map_codomain_kind)),
            ),
            Constructor::Tuple(elements) => Constructor::Tuple(
                elements
                    .into_iter()
                    .map(|element| sub_kind_in_con_inner(by, xn, rep, element))
                    .collect(),
            ),
            Constructor::Proj(base, index) => {
                Constructor::Proj(Box::new(sub_kind_in_con_inner(by, xn, rep, *base)), index)
            }
            other => other,
        };
        Located { node, span }
    }

    // ---------------------------------------------------------------------------
    // Con-in-Con lifting
    // ---------------------------------------------------------------------------

    /// Lift every free `Constructor::Rel(n)` inside a constructor by `by`, starting at `bound`.
    fn lift_con_in_con_bound(
        by: usize,
        bound: usize,
        constructor: LocatedConstructor,
    ) -> LocatedConstructor {
        let span = constructor.span.clone();
        let node = match constructor.node {
            Constructor::Rel(n) => {
                if n < bound {
                    Constructor::Rel(n) // bound: not lifted
                } else {
                    // Use saturating_add: if `n` is a sentinel (e.g. usize::MAX from a failed lookup),
                    // adding `by` would overflow; saturating keeps it large (still "unbound") safely.
                    Constructor::Rel(n.saturating_add(by))
                }
            }
            // Unification variables track their nesting level; saturating prevents overflow on error paths.
            Constructor::Unif(nl, s, k, name, r) => {
                Constructor::Unif(nl.saturating_add(by), s, k, name, r)
            }
            Constructor::TFun(domain, codomain) => Constructor::TFun(
                Box::new(lift_con_in_con_bound(by, bound, *domain)),
                Box::new(lift_con_in_con_bound(by, bound, *codomain)),
            ),
            Constructor::TCFun(exp, x, k, body) => {
                // TCFun introduces a constructor binder, so increment `bound` so local Rel(0) is not lifted.
                Constructor::TCFun(
                    exp,
                    x,
                    k,
                    Box::new(lift_con_in_con_bound(by, bound + 1, *body)),
                )
            }
            Constructor::TRecord(row) => {
                Constructor::TRecord(Box::new(lift_con_in_con_bound(by, bound, *row)))
            }
            Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
                Constructor::TDisjoint(
                    Box::new(lift_con_in_con_bound(by, bound, *disjoint_left_row)),
                    Box::new(lift_con_in_con_bound(by, bound, *disjoint_right_row)),
                    Box::new(lift_con_in_con_bound(by, bound, *body_constructor)),
                )
            }
            Constructor::App(functor, argument) => Constructor::App(
                Box::new(lift_con_in_con_bound(by, bound, *functor)),
                Box::new(lift_con_in_con_bound(by, bound, *argument)),
            ),
            Constructor::Abs(x, k, body) => {
                Constructor::Abs(x, k, Box::new(lift_con_in_con_bound(by, bound + 1, *body)))
            }
            Constructor::KAbs(x, body) => {
                Constructor::KAbs(x, Box::new(lift_con_in_con_bound(by, bound, *body)))
            }
            Constructor::KApp(functor, kind_argument) => Constructor::KApp(
                Box::new(lift_con_in_con_bound(by, bound, *functor)),
                kind_argument,
            ),
            Constructor::TKFun(x, body) => {
                Constructor::TKFun(x, Box::new(lift_con_in_con_bound(by, bound, *body)))
            }
            Constructor::Record(row_kind, field_pairs) => Constructor::Record(
                row_kind,
                field_pairs
                    .into_iter()
                    .map(|(field_name, field_type)| {
                        (
                            lift_con_in_con_bound(by, bound, field_name),
                            lift_con_in_con_bound(by, bound, field_type),
                        )
                    })
                    .collect(),
            ),
            Constructor::Concat(left_row, right_row) => Constructor::Concat(
                Box::new(lift_con_in_con_bound(by, bound, *left_row)),
                Box::new(lift_con_in_con_bound(by, bound, *right_row)),
            ),
            Constructor::Tuple(elements) => Constructor::Tuple(
                elements
                    .into_iter()
                    .map(|element| lift_con_in_con_bound(by, bound, element))
                    .collect(),
            ),
            Constructor::Proj(base, index) => {
                Constructor::Proj(Box::new(lift_con_in_con_bound(by, bound, *base)), index)
            }
            other => other,
        };
        Located { node, span }
    }

    /// Lift every free [`Constructor::Rel`] inside `constructor` by 1 (one constructor binder).
    ///
    /// # Arguments
    ///
    /// * `constructor` — Elaborated constructor.
    ///
    /// # Returns
    ///
    /// Constructor with de Bruijn indices adjusted.
    pub fn lift_con_in_con(constructor: LocatedConstructor) -> LocatedConstructor {
        lift_con_in_con_bound(1, 0, constructor)
    }

    // ---------------------------------------------------------------------------
    // Squish: inverse of mlift_con_in_con (mirrors SML `squish`)
    // ---------------------------------------------------------------------------

    /// Shift all free [`Constructor::Rel`] indices down by `by`, raising on in-scope locals or Unif.
    ///
    /// Mirrors `squish by` in `elaborate.sml`.  Used when storing a constructor solution into a
    /// [`Constructor::Unif`] cell that has been lifted `by` times since creation — the inverse of
    /// [`mlift_con_in_con`].  Any [`Constructor::Rel`] in `[0, by)` (local variables that would be
    /// lost after squishing) and any [`Constructor::Unif`] node raise [`CantSquish`].
    ///
    /// # Arguments
    ///
    /// * `by` — Number of binder levels to squish out (the Unif's nesting level `nl`).
    /// * `constructor` — Constructor computed at depth `by`; indices ≥ `by` are shifted down.
    ///
    /// # Errors
    ///
    /// [`CantSquish`] when a free [`Constructor::Rel`] in `[0, by)` or a [`Constructor::Unif`] is encountered.
    ///
    /// # Returns
    ///
    /// `Ok(constructor_at_depth_0)` on success.
    pub fn squish_con(
        by: usize,
        constructor: LocatedConstructor,
    ) -> Result<LocatedConstructor, CantSquish> {
        if by == 0 {
            // Identity: no binders to squish.
            return Ok(constructor);
        }
        squish_con_bound(by, 0, constructor)
    }

    /// Raised when [`squish_con`] encounters a constructor that cannot be squished.
    ///
    /// Mirrors `exception CantSquish` in `elaborate.sml`.
    #[derive(Debug)]
    pub struct CantSquish;

    /// Recursive body of [`squish_con`]: `bound` tracks locally-bound constructor variables.
    ///
    /// # Arguments
    ///
    /// * `by` — Fixed: number of binders being squished.
    /// * `bound` — Current depth of locally-bound constructor variables; increments inside binders.
    /// * `constructor` — Sub-constructor to squish.
    fn squish_con_bound(
        by: usize,
        bound: usize,
        constructor: LocatedConstructor,
    ) -> Result<LocatedConstructor, CantSquish> {
        let span = constructor.span.clone();
        let node = match constructor.node {
            Constructor::Rel(n) => {
                if n < bound {
                    // Local variable (bound within this constructor's own binders): keep as-is.
                    Constructor::Rel(n)
                } else if n < bound + by {
                    // Free variable referencing one of the `by` binders being squished away: cannot squish.
                    return Err(CantSquish);
                } else {
                    // Outer variable beyond the squished range: shift index down by `by`.
                    Constructor::Rel(n - by)
                }
            }
            Constructor::Unif(_, _, _, _, _) => {
                // Any unification variable blocks squishing (it might solve to a local reference).
                return Err(CantSquish);
            }
            Constructor::TFun(domain, codomain) => Constructor::TFun(
                Box::new(squish_con_bound(by, bound, *domain)?),
                Box::new(squish_con_bound(by, bound, *codomain)?),
            ),
            Constructor::TCFun(exp, x, k, body) => {
                // TCFun introduces a constructor binder: increment `bound` for the body.
                Constructor::TCFun(exp, x, k, Box::new(squish_con_bound(by, bound + 1, *body)?))
            }
            Constructor::TRecord(row) => {
                Constructor::TRecord(Box::new(squish_con_bound(by, bound, *row)?))
            }
            Constructor::TDisjoint(left_row, right_row, body_con) => Constructor::TDisjoint(
                Box::new(squish_con_bound(by, bound, *left_row)?),
                Box::new(squish_con_bound(by, bound, *right_row)?),
                Box::new(squish_con_bound(by, bound, *body_con)?),
            ),
            Constructor::App(functor, argument) => Constructor::App(
                Box::new(squish_con_bound(by, bound, *functor)?),
                Box::new(squish_con_bound(by, bound, *argument)?),
            ),
            Constructor::Abs(x, k, body) => {
                // Abs introduces a constructor binder: increment `bound` for the body.
                Constructor::Abs(x, k, Box::new(squish_con_bound(by, bound + 1, *body)?))
            }
            Constructor::KAbs(x, body) => {
                // KAbs is a kind binder, not a constructor binder: `bound` is unchanged.
                Constructor::KAbs(x, Box::new(squish_con_bound(by, bound, *body)?))
            }
            Constructor::KApp(functor, kind_argument) => Constructor::KApp(
                Box::new(squish_con_bound(by, bound, *functor)?),
                kind_argument,
            ),
            Constructor::TKFun(x, body) => {
                // TKFun is a kind binder, not a constructor binder: `bound` is unchanged.
                Constructor::TKFun(x, Box::new(squish_con_bound(by, bound, *body)?))
            }
            Constructor::Record(row_kind, field_pairs) => {
                let mut squished_pairs = Vec::with_capacity(field_pairs.len());
                for (field_name, field_type) in field_pairs {
                    // Squish both the field name constructor and the field type constructor.
                    squished_pairs.push((
                        squish_con_bound(by, bound, field_name)?,
                        squish_con_bound(by, bound, field_type)?,
                    ));
                }
                Constructor::Record(row_kind, squished_pairs)
            }
            Constructor::Concat(left_row, right_row) => Constructor::Concat(
                Box::new(squish_con_bound(by, bound, *left_row)?),
                Box::new(squish_con_bound(by, bound, *right_row)?),
            ),
            Constructor::Tuple(elements) => {
                let mut squished = Vec::with_capacity(elements.len());
                for element in elements {
                    squished.push(squish_con_bound(by, bound, element)?);
                }
                Constructor::Tuple(squished)
            }
            Constructor::Proj(base, index) => {
                Constructor::Proj(Box::new(squish_con_bound(by, bound, *base)?), index)
            }
            // All other constructor forms (Named, ModProj, Unit, Map, Name, Error, etc.) have no
            // free constructor Rel indices and cannot contain CantSquish-triggering sub-terms.
            other => other,
        };
        Ok(Located { node, span })
    }

    // ---------------------------------------------------------------------------
    // Con-in-Con substitution
    // ---------------------------------------------------------------------------

    /// Substitution stopped at a forbidden unification-variable site (SML `SubUnif`).
    ///
    /// See [`sub_con_in_con`].
    #[derive(Debug)]
    pub struct SubUnif;

    /// Substitute `replacement` for [`Constructor::Rel`] `con_index` in `constructor`.
    ///
    /// # Arguments
    ///
    /// * `con_index` — de Bruijn index to replace.
    /// * `replacement` — Constructor spliced in (lifted across intervening binders).
    /// * `constructor` — Subject.
    ///
    /// # Errors
    ///
    /// [`SubUnif`] if a [`Constructor::Unif`] sentinel blocks substitution (mirrors `CUnif(~1, …)` in SML).
    ///
    /// # Returns
    ///
    /// `Ok(updated)` on success.
    pub fn sub_con_in_con(
        con_index: usize,
        replacement: &LocatedConstructor,
        constructor: LocatedConstructor,
    ) -> Result<LocatedConstructor, SubUnif> {
        sub_con_in_con_inner(0, con_index, replacement, constructor)
    }

    fn sub_con_in_con_inner(
        by: usize,
        xn: usize,
        rep: &LocatedConstructor,
        constructor: LocatedConstructor,
    ) -> Result<LocatedConstructor, SubUnif> {
        let span = constructor.span.clone();
        let node = match constructor.node {
            Constructor::Rel(n) => {
                if n == xn {
                    return Ok(lift_con_in_con_bound(by, 0, rep.clone()));
                } else if n > xn {
                    Constructor::Rel(n - 1)
                } else {
                    Constructor::Rel(n)
                }
            }
            // SML `subConInCon'`: `CUnif(~1, ...) → raise SubUnif; CUnif(n, ...) → CUnif(n-1, ...)`.
            // We represent SML's `-1` sentinel as `usize::MAX` (wrapping underflow from 0).
            // `wrapping_sub(1)` matches the SML decrement exactly: nl=0 → usize::MAX (= -1 sentinel),
            // and usize::MAX (already -1) is caught first and raises SubUnif.
            Constructor::Unif(nl, s, k, name, r) => match read_cunif(&r) {
                Some(known_constructor) => {
                    // Keep parity with SML `ElabUtil.Con.mapB`, which traverses through solved constructor unifiers.
                    let lifted_known_constructor = mlift_con_in_con(nl, known_constructor);
                    // Continue substitution through the solved constructor instead of treating the cell as opaque.
                    return sub_con_in_con_inner(by, xn, rep, lifted_known_constructor);
                }
                None => {
                    if nl == usize::MAX {
                        // This Unif already holds the ~1 sentinel: block substitution.
                        return Err(SubUnif);
                    }
                    // Decrement nesting level by 1; nl=0 wraps to usize::MAX (the ~1 sentinel),
                    // matching SML's CUnif(0) → CUnif(0-1) = CUnif(~1) behavior.
                    Constructor::Unif(nl.wrapping_sub(1), s, k, name, r)
                }
            },
            Constructor::TFun(domain, codomain) => Constructor::TFun(
                Box::new(sub_con_in_con_inner(by, xn, rep, *domain)?),
                Box::new(sub_con_in_con_inner(by, xn, rep, *codomain)?),
            ),
            Constructor::TCFun(exp, x, k, body) => Constructor::TCFun(
                exp,
                x,
                k,
                // TCFun introduces a constructor binder, so increment by and xn
                Box::new(sub_con_in_con_inner(by + 1, xn + 1, rep, *body)?),
            ),
            Constructor::TRecord(row) => {
                Constructor::TRecord(Box::new(sub_con_in_con_inner(by, xn, rep, *row)?))
            }
            Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
                Constructor::TDisjoint(
                    Box::new(sub_con_in_con_inner(by, xn, rep, *disjoint_left_row)?),
                    Box::new(sub_con_in_con_inner(by, xn, rep, *disjoint_right_row)?),
                    Box::new(sub_con_in_con_inner(by, xn, rep, *body_constructor)?),
                )
            }
            Constructor::App(functor, argument) => Constructor::App(
                Box::new(sub_con_in_con_inner(by, xn, rep, *functor)?),
                Box::new(sub_con_in_con_inner(by, xn, rep, *argument)?),
            ),
            Constructor::Abs(x, k, body) => Constructor::Abs(
                x,
                k,
                Box::new(sub_con_in_con_inner(by + 1, xn + 1, rep, *body)?),
            ),
            Constructor::KAbs(x, body) => {
                Constructor::KAbs(x, Box::new(sub_con_in_con_inner(by, xn, rep, *body)?))
            }
            Constructor::KApp(functor, kind_argument) => Constructor::KApp(
                Box::new(sub_con_in_con_inner(by, xn, rep, *functor)?),
                kind_argument,
            ),
            Constructor::TKFun(x, body) => {
                Constructor::TKFun(x, Box::new(sub_con_in_con_inner(by, xn, rep, *body)?))
            }
            Constructor::Record(row_kind, field_pairs) => {
                let mut new_field_pairs = Vec::with_capacity(field_pairs.len());
                for (field_name, field_type) in field_pairs {
                    new_field_pairs.push((
                        sub_con_in_con_inner(by, xn, rep, field_name)?,
                        sub_con_in_con_inner(by, xn, rep, field_type)?,
                    ));
                }
                Constructor::Record(row_kind, new_field_pairs)
            }
            Constructor::Concat(left_row, right_row) => Constructor::Concat(
                Box::new(sub_con_in_con_inner(by, xn, rep, *left_row)?),
                Box::new(sub_con_in_con_inner(by, xn, rep, *right_row)?),
            ),
            Constructor::Tuple(elements) => {
                let mut new_elements = Vec::with_capacity(elements.len());
                for element in elements {
                    new_elements.push(sub_con_in_con_inner(by, xn, rep, element)?);
                }
                Constructor::Tuple(new_elements)
            }
            Constructor::Proj(base, index) => {
                Constructor::Proj(Box::new(sub_con_in_con_inner(by, xn, rep, *base)?), index)
            }
            other => other,
        };
        Ok(Located { node, span })
    }

    // ---------------------------------------------------------------------------
    // Occurs check
    // ---------------------------------------------------------------------------

    /// Returns `true` if `Constructor::Rel(n)` appears free in `constructor` (at de Bruijn depth `bound`).
    fn occurs_at(debruijn_index: usize, bound: usize, constructor: &LocatedConstructor) -> bool {
        match &constructor.node {
            Constructor::Rel(m) => *m == debruijn_index + bound,
            Constructor::TFun(domain, codomain) => {
                occurs_at(debruijn_index, bound, domain)
                    || occurs_at(debruijn_index, bound, codomain)
            }
            // TCFun introduces a constructor binder: increment `bound` so the bound variable is not treated as free.
            Constructor::TCFun(_, _, _, body) => occurs_at(debruijn_index, bound + 1, body),
            Constructor::TRecord(row) => occurs_at(debruijn_index, bound, row),
            Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
                occurs_at(debruijn_index, bound, disjoint_left_row)
                    || occurs_at(debruijn_index, bound, disjoint_right_row)
                    || occurs_at(debruijn_index, bound, body_constructor)
            }
            Constructor::App(functor, argument) => {
                occurs_at(debruijn_index, bound, functor)
                    || occurs_at(debruijn_index, bound, argument)
            }
            Constructor::Abs(_, _, body) => occurs_at(debruijn_index, bound + 1, body),
            Constructor::KAbs(_, body) => occurs_at(debruijn_index, bound, body),
            Constructor::KApp(functor, _) => occurs_at(debruijn_index, bound, functor),
            Constructor::TKFun(_, body) => occurs_at(debruijn_index, bound, body),
            Constructor::Record(_, field_pairs) => {
                field_pairs.iter().any(|(field_name, field_type)| {
                    occurs_at(debruijn_index, bound, field_name)
                        || occurs_at(debruijn_index, bound, field_type)
                })
            }
            Constructor::Concat(left_row, right_row) => {
                occurs_at(debruijn_index, bound, left_row)
                    || occurs_at(debruijn_index, bound, right_row)
            }
            Constructor::Tuple(elements) => elements
                .iter()
                .any(|element| occurs_at(debruijn_index, bound, element)),
            Constructor::Proj(base, _) => occurs_at(debruijn_index, bound, base),
            _ => false,
        }
    }

    /// Returns whether de Bruijn variable 0 occurs free in `constructor` (occurs-check helper).
    ///
    /// # Arguments
    ///
    /// * `constructor` — Constructor at the current binding depth.
    ///
    /// # Returns
    ///
    /// `true` if `Constructor::Rel(0)` appears free at the current binding depth.
    pub fn occurs(constructor: &LocatedConstructor) -> bool {
        occurs_at(0, 0, constructor)
    }

    /// Returns whether constructor unification `unification_cell` occurs anywhere in `constructor`.
    ///
    /// # Arguments
    ///
    /// * `unification_cell` — [`CUnif`] reference cell (identity compared with [`Arc::ptr_eq`]).
    /// * `constructor` — Constructor to search.
    ///
    /// # Returns
    ///
    /// `true` if any [`Constructor::Unif`] in `c` shares `r`.
    pub fn occurs_cunif(unification_cell: &CUnifRef, constructor: &LocatedConstructor) -> bool {
        match &constructor.node {
            Constructor::Unif(_, _, _, _, other_cell) => Arc::ptr_eq(unification_cell, other_cell),
            Constructor::TFun(domain, codomain) => {
                occurs_cunif(unification_cell, domain) || occurs_cunif(unification_cell, codomain)
            }
            Constructor::TCFun(_, _, _, body) => occurs_cunif(unification_cell, body),
            Constructor::TRecord(row) => occurs_cunif(unification_cell, row),
            Constructor::TDisjoint(disjoint_left_row, disjoint_right_row, body_constructor) => {
                occurs_cunif(unification_cell, disjoint_left_row)
                    || occurs_cunif(unification_cell, disjoint_right_row)
                    || occurs_cunif(unification_cell, body_constructor)
            }
            Constructor::App(functor, argument) => {
                occurs_cunif(unification_cell, functor) || occurs_cunif(unification_cell, argument)
            }
            Constructor::Abs(_, _, body) => occurs_cunif(unification_cell, body),
            Constructor::KAbs(_, body) => occurs_cunif(unification_cell, body),
            Constructor::KApp(functor, _) => occurs_cunif(unification_cell, functor),
            Constructor::TKFun(_, body) => occurs_cunif(unification_cell, body),
            Constructor::Record(_, field_pairs) => {
                field_pairs.iter().any(|(field_name, field_type)| {
                    occurs_cunif(unification_cell, field_name)
                        || occurs_cunif(unification_cell, field_type)
                })
            }
            Constructor::Concat(left_row, right_row) => {
                occurs_cunif(unification_cell, left_row)
                    || occurs_cunif(unification_cell, right_row)
            }
            Constructor::Tuple(elements) => elements
                .iter()
                .any(|element| occurs_cunif(unification_cell, element)),
            Constructor::Proj(base, _) => occurs_cunif(unification_cell, base),
            _ => false,
        }
    }

    // ---------------------------------------------------------------------------
    // Stats counters (mirrors SML refs)
    // ---------------------------------------------------------------------------

    use std::sync::atomic::{AtomicUsize, Ordering};

    static IDENTITY: AtomicUsize = AtomicUsize::new(0);
    static DISTRIBUTE: AtomicUsize = AtomicUsize::new(0);
    static FUSE: AtomicUsize = AtomicUsize::new(0);

    /// Reset internal normalisation counters (`identity` / `distribute` / `fuse` mirrors of SML refs).
    ///
    /// # Returns
    ///
    /// Nothing. Intended for tests or debugging.
    pub fn reset_stats() {
        IDENTITY.store(0, Ordering::Relaxed);
        DISTRIBUTE.store(0, Ordering::Relaxed);
        FUSE.store(0, Ordering::Relaxed);
    }

    fn inc_distribute() {
        DISTRIBUTE.fetch_add(1, Ordering::Relaxed);
    }

    // ---------------------------------------------------------------------------
    // Head-normalisation
    // ---------------------------------------------------------------------------

    /// Read through a solved unification variable, returning the stored constructor.
    fn read_cunif(r: &CUnifRef) -> Option<LocatedConstructor> {
        match &*crate::compiler_diagnostics::lock_for_compile(
            r.as_ref(),
            "type operations CUnif cell",
        ) {
            CUnif::Known(c) => Some(*c.clone()),
            CUnif::Unknown => None,
        }
    }

    /// Upper bound on solved kind-unifier links peeled in one call.
    const PEEL_SOLVED_KIND_UNIF_CHAIN_MAX_STEPS: usize = 8192;

    /// Follow solved [`Kind::Unif`] / [`Kind::TupleUnif`] cells to a stable head.
    fn hnorm_kind(mut kind: LocatedKind) -> LocatedKind {
        for _ in 0..PEEL_SOLVED_KIND_UNIF_CHAIN_MAX_STEPS {
            let reference = match &kind.node {
                Kind::Unif(_, _, reference) | Kind::TupleUnif(_, _, reference) => reference,
                _ => return kind,
            };
            let guard = crate::compiler_diagnostics::lock_for_compile(
                reference.as_ref(),
                "type operations KUnif cell",
            );
            if let crate::elaborated::KUnif::Known(inner) = &*guard {
                let next = *inner.clone();
                drop(guard);
                kind = next;
            } else {
                drop(guard);
                return kind;
            }
        }
        let span = kind.span.clone();
        Located::new(Kind::Typed(Types::Error), span)
    }

    /// Lift all free [`Constructor::Rel`] indices in `constructor` by `binder_count` (multi-binder `mlift`).
    ///
    /// # Arguments
    ///
    /// * `binder_count` — Number of constructor binders entered.
    /// * `constructor` — Subject.
    ///
    /// # Returns
    ///
    /// Constructor with adjusted indices.
    pub fn mlift_con_in_con(
        binder_count: usize,
        constructor: LocatedConstructor,
    ) -> LocatedConstructor {
        lift_con_in_con_bound(binder_count, 0, constructor)
    }

    /// Upper bound on solved [`Constructor::Unif`] indirections peeled in one call.
    ///
    /// Cycles or pathological chains must not spin without stack growth (LangSec / bounded work per request).
    const PEEL_SOLVED_CONSTRUCTOR_UNIF_CHAIN_MAX_STEPS: usize = 8192;

    /// Peel a chain of solved [`Constructor::Unif`] heads in one go (no one-frame-per-link recursion).
    ///
    /// Long `Known` pointer chains from constructor unification can otherwise exhaust the stack before
    /// [`hnorm_con`]'s depth counter runs out. Step cap returns [`Constructor::Error`] like excessive
    /// [`hnorm_con`] depth (bad or cyclic instantiation graph).
    ///
    /// # Arguments
    ///
    /// * `constructor` — Elaborated constructor whose outermost nodes may be solved unifiers.
    ///
    /// # Returns
    ///
    /// First non-`Unif`, or the first `Unif` whose cell is still [`CUnif::Unknown`].
    fn peel_solved_constructor_unif_chain(
        mut constructor: LocatedConstructor,
    ) -> LocatedConstructor {
        for _ in 0..PEEL_SOLVED_CONSTRUCTOR_UNIF_CHAIN_MAX_STEPS {
            match &constructor.node {
                Constructor::Unif(binder_count, _, _, _, reference) => {
                    match read_cunif(reference) {
                        Some(inner) => {
                            constructor = mlift_con_in_con(*binder_count, inner);
                            // Lift through `binder_count` binders.
                        }
                        None => return constructor,
                    }
                }
                _ => return constructor,
            }
        }
        let span = constructor.span.clone();
        Located::new(Constructor::Error, span)
    }

    /// Head-normalize a constructor: peel solved [`Constructor::Unif`], beta/eta, `KApp`/`Map`/`Concat`/`Proj` rules.
    ///
    /// Translation of `hnormCon` from `elab_ops.sml`. No [`crate::elaborated::environment::Env`]:
    /// [`Constructor::Named`] / [`Constructor::ModProj`] are not expanded to definitions here.
    ///
    /// # Arguments
    ///
    /// * `constructor` — Elaborated constructor.
    ///
    /// # Returns
    ///
    /// Head-normal form, or [`Constructor::Error`] if recursion depth exceeds 200 (guards cyclic unifiers).
    pub fn hnorm_con(constructor: LocatedConstructor) -> LocatedConstructor {
        use std::cell::Cell;
        thread_local! {
            static HNORM_DEPTH: Cell<usize> = const { Cell::new(0) };
        }
        let d = HNORM_DEPTH.with(|c| {
            let v = c.get();
            c.set(v + 1);
            v
        });
        if d > 200 {
            HNORM_DEPTH.with(|c| c.set(0));
            let span = constructor.span.clone();
            return Located::new(Constructor::Error, span);
        }
        // Collapse solved-unifier prefixes iteratively so depth-200 only limits beta/eta steps, not chain length.
        let constructor = peel_solved_constructor_unif_chain(constructor);
        let result = hnorm_con_inner(constructor);
        HNORM_DEPTH.with(|c| c.set(d));
        result
    }

    fn hnorm_con_inner(constructor: LocatedConstructor) -> LocatedConstructor {
        let span = constructor.span.clone();
        match constructor.node.clone() {
            // Solved unification variable: lift and continue normalizing
            Constructor::Unif(binder_count, _, _, _, reference) => {
                if let Some(inner) = read_cunif(&reference) {
                    hnorm_con(mlift_con_in_con(binder_count, inner))
                } else {
                    constructor
                }
            }

            // Eta reduction: (fn x => f x) where x does not appear in f
            Constructor::Abs(x, k, body) => {
                let body_norm = hnorm_con(*body);
                match &body_norm.node {
                    Constructor::App(f, arg) => {
                        if matches!(&arg.node, Constructor::Rel(0)) && !occurs(f) {
                            // sub 0 -> Unit, then hnorm
                            let unit = Located {
                                node: Constructor::Unit,
                                span: span.clone(),
                            };
                            if let Ok(substituted) = sub_con_in_con(0, &unit, *f.clone()) {
                                return hnorm_con(substituted);
                            }
                        }
                        Located {
                            node: Constructor::Abs(x, k, Box::new(body_norm)),
                            span,
                        }
                    }
                    _ => Located {
                        node: Constructor::Abs(x, k, Box::new(body_norm)),
                        span,
                    },
                }
            }

            // Beta reduction
            Constructor::App(c1, c2) => {
                let c1_norm = hnorm_con(*c1);
                match c1_norm.node.clone() {
                    Constructor::Abs(_, _, cb) => {
                        let c2_norm = hnorm_con(*c2);
                        if let Ok(sub) = sub_con_in_con(0, &c2_norm, *cb) {
                            hnorm_con(sub)
                        } else {
                            Located {
                                node: Constructor::App(Box::new(c1_norm), Box::new(c2_norm)),
                                span,
                            }
                        }
                    }
                    // NOTE: SML `hnormCon` only beta-reduces `App(CAbs, c2)`; `App(TCFun, c2)` falls
                    // through to the default `c1' => (CApp((c1', loc), hnormCon env c2), loc)` arm.
                    // TCFun is a universal constructor quantifier (∀ x :: K. body), NOT a lambda;
                    // beta-reducing it here was incorrect and caused spurious constructor substitutions.
                    Constructor::App(c1p, f) => {
                        // Map fusion / distributivity / identity
                        let c2_norm = hnorm_con(*c2);
                        let c1p_norm = hnorm_con(*c1p);
                        match &c1p_norm.node {
                            Constructor::Map(_k1, k2) => {
                                let k2 = k2.clone();
                                match &c2_norm.node {
                                    Constructor::Record(_, fields) if fields.is_empty() => {
                                        Located {
                                            node: Constructor::Record(k2, vec![]),
                                            span,
                                        }
                                    }
                                    Constructor::Record(_, fields) if !fields.is_empty() => {
                                        let fields = fields.clone();
                                        let (first_name, first_val) = fields[0].clone();
                                        let rest_fields = fields[1..].to_vec();
                                        let mapped_first = Located {
                                            node: Constructor::App(f.clone(), Box::new(first_val)),
                                            span: span.clone(),
                                        };
                                        let mapped_rec = Located {
                                            node: Constructor::Record(
                                                k2.clone(),
                                                vec![(first_name, hnorm_con(mapped_first))],
                                            ),
                                            span: span.clone(),
                                        };
                                        let rest_con = Located {
                                            node: Constructor::Record(k2.clone(), rest_fields),
                                            span: span.clone(),
                                        };
                                        let rec_app = Located {
                                            node: Constructor::App(
                                                Box::new(Located {
                                                    node: c1_norm.node.clone(),
                                                    span: span.clone(),
                                                }),
                                                Box::new(rest_con),
                                            ),
                                            span: span.clone(),
                                        };
                                        hnorm_con(Located {
                                            node: Constructor::Concat(
                                                Box::new(mapped_rec),
                                                Box::new(hnorm_con(rec_app)),
                                            ),
                                            span,
                                        })
                                    }
                                    Constructor::Concat(cc1, cc2) => {
                                        match &cc1.node {
                                            Constructor::Record(k_inner, fields)
                                                if !fields.is_empty() =>
                                            {
                                                let fields = fields.clone();
                                                let k_inner = k_inner.clone();
                                                let (first_name, first_val) = fields[0].clone();
                                                let rest_fields = fields[1..].to_vec();
                                                let mapped_first = hnorm_con(Located {
                                                    node: Constructor::App(
                                                        f.clone(),
                                                        Box::new(first_val),
                                                    ),
                                                    span: span.clone(),
                                                });
                                                let mapped_rec = Located {
                                                    node: Constructor::Record(
                                                        k2.clone(),
                                                        vec![(first_name, mapped_first)],
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let rest_part = Located {
                                                    node: Constructor::Concat(
                                                        Box::new(Located {
                                                            node: Constructor::Record(
                                                                k_inner,
                                                                rest_fields,
                                                            ),
                                                            span: span.clone(),
                                                        }),
                                                        cc2.clone(),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let rest_mapped = hnorm_con(Located {
                                                    node: Constructor::App(
                                                        Box::new(Located {
                                                            node: c1_norm.node.clone(),
                                                            span: span.clone(),
                                                        }),
                                                        Box::new(rest_part),
                                                    ),
                                                    span: span.clone(),
                                                });
                                                hnorm_con(Located {
                                                    node: Constructor::Concat(
                                                        Box::new(mapped_rec),
                                                        Box::new(rest_mapped),
                                                    ),
                                                    span,
                                                })
                                            }
                                            _ => {
                                                // tryDistributivity
                                                inc_distribute();
                                                let map_f = Located {
                                                    node: Constructor::App(
                                                        Box::new(c1p_norm.clone()),
                                                        f.clone(),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let app1 = Located {
                                                    node: Constructor::App(
                                                        Box::new(map_f.clone()),
                                                        cc1.clone(),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let app2 = Located {
                                                    node: Constructor::App(
                                                        Box::new(map_f),
                                                        cc2.clone(),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                hnorm_con(Located {
                                                    node: Constructor::Concat(
                                                        Box::new(app1),
                                                        Box::new(app2),
                                                    ),
                                                    span,
                                                })
                                            }
                                        }
                                    }
                                    _ => {
                                        // tryDistributivity on outer c2_norm
                                        match &c2_norm.node {
                                            Constructor::Concat(cc1, cc2) => {
                                                inc_distribute();
                                                let map_f = Located {
                                                    node: Constructor::App(
                                                        Box::new(c1p_norm.clone()),
                                                        f.clone(),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let app1 = Located {
                                                    node: Constructor::App(
                                                        Box::new(map_f.clone()),
                                                        cc1.clone(),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let app2 = Located {
                                                    node: Constructor::App(
                                                        Box::new(map_f),
                                                        cc2.clone(),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                hnorm_con(Located {
                                                    node: Constructor::Concat(
                                                        Box::new(app1),
                                                        Box::new(app2),
                                                    ),
                                                    span,
                                                })
                                            }
                                            _ => Located {
                                                node: Constructor::App(
                                                    Box::new(Located {
                                                        node: Constructor::App(
                                                            Box::new(c1p_norm),
                                                            f,
                                                        ),
                                                        span: span.clone(),
                                                    }),
                                                    Box::new(c2_norm),
                                                ),
                                                span,
                                            },
                                        }
                                    }
                                }
                            }
                            _ => Located {
                                node: Constructor::App(
                                    Box::new(Located {
                                        node: Constructor::App(Box::new(c1p_norm), f),
                                        span: span.clone(),
                                    }),
                                    Box::new(c2_norm),
                                ),
                                span,
                            },
                        }
                    }
                    _ => Located {
                        node: Constructor::App(Box::new(c1_norm), Box::new(hnorm_con(*c2))),
                        span,
                    },
                }
            }

            // Kind application: (fn α => body) k  =>  body[k/0]
            Constructor::KApp(c1, k) => {
                let c1_norm = hnorm_con(*c1);
                match c1_norm.node {
                    Constructor::KAbs(_, body) => hnorm_con(sub_kind_in_con(0, &k, *body)),
                    _ => Located {
                        node: Constructor::KApp(Box::new(c1_norm), k),
                        span,
                    },
                }
            }

            // Record concatenation: flatten / simplify
            Constructor::Concat(c1, c2) => {
                let c1_norm = hnorm_con(*c1);
                let c2_norm = hnorm_con(*c2);
                match (c1_norm.node.clone(), c2_norm.node.clone()) {
                    (Constructor::Record(k, xcs1), Constructor::Record(_, xcs2)) => {
                        let mut merged = xcs1;
                        merged.extend(xcs2);
                        Located {
                            node: Constructor::Record(k, merged),
                            span,
                        }
                    }
                    (Constructor::Record(_, ref xcs), _) if xcs.is_empty() => c2_norm,
                    (Constructor::Concat(c11, c12), _) => hnorm_con(Located {
                        node: Constructor::Concat(
                            c11,
                            Box::new(Located {
                                node: Constructor::Concat(c12, Box::new(c2_norm)),
                                span: span.clone(),
                            }),
                        ),
                        span,
                    }),
                    (_, Constructor::Record(_, ref xcs)) if xcs.is_empty() => c1_norm,
                    _ => Located {
                        node: Constructor::Concat(Box::new(c1_norm), Box::new(c2_norm)),
                        span,
                    },
                }
            }

            // Tuple projection
            Constructor::Proj(c1, n) => {
                let c1_norm = hnorm_con(*c1);
                match c1_norm.node {
                    Constructor::Tuple(cs) if n >= 1 && n <= cs.len() => {
                        hnorm_con(cs[n - 1].clone())
                    }
                    _ => Located {
                        node: Constructor::Proj(Box::new(c1_norm), n),
                        span,
                    },
                }
            }

            other => Located { node: other, span },
        }
    }

    // ---------------------------------------------------------------------------
    // Full reduction (reduceCon)
    // ---------------------------------------------------------------------------

    /// Reduce a constructor by repeated head [`hnorm_con`] plus beta on `App(Abs(…), _)`.
    ///
    /// Mirrors SML `reduceCon` without a full structural normalizer (avoids non-termination on cyclic unifiers).
    /// Named / module-projected bodies are not loaded from the environment.
    ///
    /// # Arguments
    ///
    /// * `constructor` — Starting constructor.
    ///
    /// # Returns
    ///
    /// Constructor after head reduction steps succeed; otherwise the last stable head-normal form.
    pub fn reduce_con(constructor: LocatedConstructor) -> LocatedConstructor {
        // Head-normalize first (follows Unif chains, beta/eta at the head).
        let r = hnorm_con(constructor);
        match r.node.clone() {
            Constructor::App(c_prime, x) => {
                let c_prime_norm = hnorm_con(*c_prime);
                match c_prime_norm.node.clone() {
                    Constructor::Abs(_, _, body) => {
                        // Beta step: (λ. body) x → body[x/0]
                        if let Ok(subst) = sub_con_in_con(0, &x, *body) {
                            reduce_con(subst)
                        } else {
                            r
                        }
                    }
                    _ => r,
                }
            }
            _ => r,
        }
    }

    // NOTE: reduce_con_inner is no longer used; the old full-normalizer was removed
    // because it caused infinite loops on cyclic unification variables.
    #[allow(dead_code)]
    fn reduce_con_inner_legacy(constructor: LocatedConstructor) -> LocatedConstructor {
        let span = constructor.span.clone();
        match constructor.node {
            Constructor::App(c1, c2) => {
                let c1 = reduce_con(*c1);
                let c2 = reduce_con(*c2);
                match c1.node.clone() {
                    Constructor::Abs(_, _, cb) => {
                        if let Ok(sub) = sub_con_in_con(0, &c2, *cb) {
                            reduce_con(sub)
                        } else {
                            Located {
                                node: Constructor::App(Box::new(c1), Box::new(c2)),
                                span,
                            }
                        }
                    }
                    Constructor::App(c1p, f) => {
                        let c1p = reduce_con(*c1p);
                        let f = reduce_con(*f);
                        match &c1p.node {
                            Constructor::Map(_k1, k2) => {
                                let k2 = k2.clone();
                                match &c2.node {
                                    Constructor::Record(_, fields) if fields.is_empty() => {
                                        Located {
                                            node: Constructor::Record(k2, vec![]),
                                            span,
                                        }
                                    }
                                    Constructor::Record(_, fields) if !fields.is_empty() => {
                                        let fields = fields.clone();
                                        let (first_name, first_val) = fields[0].clone();
                                        let rest = fields[1..].to_vec();
                                        let mapped_first = reduce_con(Located {
                                            node: Constructor::App(
                                                Box::new(f.clone()),
                                                Box::new(first_val),
                                            ),
                                            span: span.clone(),
                                        });
                                        let mapped_rec = Located {
                                            node: Constructor::Record(
                                                k2.clone(),
                                                vec![(first_name, mapped_first)],
                                            ),
                                            span: span.clone(),
                                        };
                                        let rest_app = reduce_con(Located {
                                            node: Constructor::App(
                                                Box::new(Located {
                                                    node: Constructor::App(
                                                        Box::new(c1p.clone()),
                                                        Box::new(f.clone()),
                                                    ),
                                                    span: span.clone(),
                                                }),
                                                Box::new(Located {
                                                    node: Constructor::Record(k2.clone(), rest),
                                                    span: span.clone(),
                                                }),
                                            ),
                                            span: span.clone(),
                                        });
                                        reduce_con(Located {
                                            node: Constructor::Concat(
                                                Box::new(mapped_rec),
                                                Box::new(rest_app),
                                            ),
                                            span,
                                        })
                                    }
                                    _ => {
                                        // tryDistributivity
                                        match c2.node.clone() {
                                            Constructor::Concat(cc1, cc2) => {
                                                inc_distribute();
                                                let map_f = Located {
                                                    node: Constructor::App(
                                                        Box::new(c1p.clone()),
                                                        Box::new(f.clone()),
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let app1 = Located {
                                                    node: Constructor::App(
                                                        Box::new(map_f.clone()),
                                                        cc1,
                                                    ),
                                                    span: span.clone(),
                                                };
                                                let app2 = Located {
                                                    node: Constructor::App(Box::new(map_f), cc2),
                                                    span: span.clone(),
                                                };
                                                reduce_con(Located {
                                                    node: Constructor::Concat(
                                                        Box::new(app1),
                                                        Box::new(app2),
                                                    ),
                                                    span,
                                                })
                                            }
                                            _ => Located {
                                                node: Constructor::App(
                                                    Box::new(Located {
                                                        node: Constructor::App(
                                                            Box::new(c1p),
                                                            Box::new(f),
                                                        ),
                                                        span: span.clone(),
                                                    }),
                                                    Box::new(c2),
                                                ),
                                                span,
                                            },
                                        }
                                    }
                                }
                            }
                            _ => Located {
                                node: Constructor::App(
                                    Box::new(Located {
                                        node: Constructor::App(Box::new(c1p), Box::new(f)),
                                        span: span.clone(),
                                    }),
                                    Box::new(c2),
                                ),
                                span,
                            },
                        }
                    }
                    _ => Located {
                        node: Constructor::App(Box::new(c1), Box::new(c2)),
                        span,
                    },
                }
            }

            Constructor::Abs(x, k, body) => {
                let body = reduce_con(*body);
                match &body.node {
                    Constructor::App(f, arg) => {
                        if matches!(&arg.node, Constructor::Rel(0)) && !occurs(f) {
                            let unit = Located {
                                node: Constructor::Unit,
                                span: span.clone(),
                            };
                            if let Ok(sub) = sub_con_in_con(0, &unit, *f.clone()) {
                                return reduce_con(sub);
                            }
                        }
                        Located {
                            node: Constructor::Abs(x, k, Box::new(body)),
                            span,
                        }
                    }
                    _ => Located {
                        node: Constructor::Abs(x, k, Box::new(body)),
                        span,
                    },
                }
            }

            Constructor::KAbs(x, body) => Located {
                node: Constructor::KAbs(x, Box::new(reduce_con(*body))),
                span,
            },
            Constructor::KApp(c1, k) => {
                let c1 = reduce_con(*c1);
                match c1.node.clone() {
                    Constructor::KAbs(_, body) => reduce_con(sub_kind_in_con(0, &k, *body)),
                    _ => Located {
                        node: Constructor::KApp(Box::new(c1), k),
                        span,
                    },
                }
            }
            Constructor::TKFun(x, body) => Located {
                node: Constructor::TKFun(x, Box::new(reduce_con(*body))),
                span,
            },

            Constructor::Record(k, xcs) => Located {
                node: Constructor::Record(
                    k,
                    xcs.into_iter()
                        .map(|(x, v)| (reduce_con(x), reduce_con(v)))
                        .collect(),
                ),
                span,
            },

            Constructor::Concat(c1, c2) => {
                let c1 = reduce_con(*c1);
                let c2 = reduce_con(*c2);
                match (c1.node.clone(), c2.node.clone()) {
                    // 1. Two records
                    (Constructor::Record(k, xcs1), Constructor::Record(_, xcs2)) => {
                        let mut merged = xcs1;
                        merged.extend(xcs2);
                        Located {
                            node: Constructor::Record(k, merged),
                            span,
                        }
                    }
                    // 2. Empty left
                    (Constructor::Record(_, ref xcs), _) if xcs.is_empty() => c2,
                    // 2. Empty right
                    (_, Constructor::Record(_, ref xcs)) if xcs.is_empty() => c1,
                    // 3. Left record, right is concat-of-record
                    (Constructor::Record(k, xcs1), Constructor::Concat(inner_rec, rest2))
                        if matches!(&inner_rec.node, Constructor::Record(_, _)) =>
                    {
                        if let Constructor::Record(_, xcs2) = inner_rec.node.clone() {
                            let mut merged = xcs1;
                            merged.extend(xcs2);
                            Located {
                                node: Constructor::Concat(
                                    Box::new(Located {
                                        node: Constructor::Record(k, merged),
                                        span: span.clone(),
                                    }),
                                    rest2,
                                ),
                                span,
                            }
                        } else {
                            Located {
                                node: Constructor::Concat(Box::new(c1), Box::new(c2)),
                                span,
                            }
                        }
                    }
                    // 5. Split left concat
                    (Constructor::Concat(c11, c12), _) => reduce_con(Located {
                        node: Constructor::Concat(
                            c11,
                            Box::new(Located {
                                node: Constructor::Concat(c12, Box::new(c2)),
                                span: span.clone(),
                            }),
                        ),
                        span,
                    }),
                    // 6 & 7. Swap to hit earlier rules
                    (_, Constructor::Record(_, _)) | (_, Constructor::Concat(_, _)) => {
                        reduce_con(Located {
                            node: Constructor::Concat(Box::new(c2), Box::new(c1)),
                            span,
                        })
                    }
                    _ => Located {
                        node: Constructor::Concat(Box::new(c1), Box::new(c2)),
                        span,
                    },
                }
            }

            Constructor::Tuple(cs) => Located {
                node: Constructor::Tuple(cs.into_iter().map(reduce_con).collect()),
                span,
            },
            Constructor::Proj(c1, n) => {
                let c1 = reduce_con(*c1);
                match c1.node.clone() {
                    Constructor::Tuple(cs) if n >= 1 && n <= cs.len() => {
                        reduce_con(cs[n - 1].clone())
                    }
                    _ => Located {
                        node: Constructor::Proj(Box::new(c1), n),
                        span,
                    },
                }
            }

            other => Located { node: other, span },
        }
    }

    // ---------------------------------------------------------------------------
    // consEqSimple
    // ---------------------------------------------------------------------------

    /// Cheap structural equality after [`hnorm_con`] (no unification; skips some kind checks in `Abs`).
    ///
    /// Mirrors `consEqSimple` from `elab_ops.sml`.
    ///
    /// # Arguments
    ///
    /// * `left_constructor`, `right_constructor` — Constructors to compare.
    ///
    /// # Returns
    ///
    /// `true` when the simplified rules deem them equal (including same [`Constructor::Unif`] cell).
    pub fn cons_eq_simple(
        left_constructor: &LocatedConstructor,
        right_constructor: &LocatedConstructor,
    ) -> bool {
        let left_normalized = hnorm_con(left_constructor.clone());
        let right_normalized = hnorm_con(right_constructor.clone());
        cons_eq_simple_normed(&left_normalized, &right_normalized)
    }

    fn kinds_eq_simple(left_kind: &LocatedKind, right_kind: &LocatedKind) -> bool {
        let left_normalized = hnorm_kind(left_kind.clone());
        let right_normalized = hnorm_kind(right_kind.clone());
        match (&left_normalized.node, &right_normalized.node) {
            (Kind::Rel(left_index), Kind::Rel(right_index)) => left_index == right_index,
            (left_kind, right_kind)
                if left_kind.is_runtime_type_classifier()
                    && right_kind.is_runtime_type_classifier() =>
            {
                match (left_kind.as_type_tag(), right_kind.as_type_tag()) {
                    (Some(left_type_tag), Some(right_type_tag)) => {
                        left_type_tag == right_type_tag
                            || (left_type_tag == Types::Any
                                && StarClassifierRefinement::is_star_structural_refinement(
                                    right_type_tag,
                                ))
                            || (right_type_tag == Types::Any
                                && StarClassifierRefinement::is_star_structural_refinement(
                                    left_type_tag,
                                ))
                    }
                    _ => true,
                }
            }
            (Kind::Name, Kind::Name) => true,
            (Kind::Record(left_row_kind), Kind::Record(right_row_kind)) => {
                kinds_eq_simple(left_row_kind.as_ref(), right_row_kind.as_ref())
            }
            (Kind::Arrow(left_domain, left_range), Kind::Arrow(right_domain, right_range)) => {
                kinds_eq_simple(left_domain.as_ref(), right_domain.as_ref())
                    && kinds_eq_simple(left_range.as_ref(), right_range.as_ref())
            }
            (Kind::Tuple(left_elements), Kind::Tuple(right_elements)) => {
                left_elements.len() == right_elements.len()
                    && left_elements.iter().zip(right_elements.iter()).all(
                        |(left_element, right_element)| {
                            kinds_eq_simple(left_element, right_element)
                        },
                    )
            }
            (Kind::Unif(_, _, left_cell), Kind::Unif(_, _, right_cell)) => {
                Arc::ptr_eq(left_cell, right_cell) // compare Arc pointer identity without redundant references
            }
            _ => false,
        }
    }

    /// Public wrapper around simplified kind equality used by the `types.rs` facade trait.
    pub fn kinds_eq_simple_public(left_kind: &LocatedKind, right_kind: &LocatedKind) -> bool {
        kinds_eq_simple(left_kind, right_kind)
    }

    fn cons_eq_simple_normed(left: &LocatedConstructor, right: &LocatedConstructor) -> bool {
        match (&left.node, &right.node) {
            (Constructor::Rel(left_index), Constructor::Rel(right_index)) => {
                left_index == right_index
            }
            (Constructor::Named(left_id), Constructor::Named(right_id)) => left_id == right_id,
            (Constructor::ModProj(m1, path1, name1), Constructor::ModProj(m2, path2, name2)) => {
                m1 == m2 && path1 == path2 && name1 == name2
            }
            (
                Constructor::App(left_functor, left_arg),
                Constructor::App(right_functor, right_arg),
            ) => cons_eq_simple(left_functor, right_functor) && cons_eq_simple(left_arg, right_arg),
            (
                Constructor::Abs(_, _left_kind, left_body),
                Constructor::Abs(_, _right_kind, right_body),
            ) => cons_eq_simple(left_body, right_body),
            (Constructor::KAbs(_, left_body), Constructor::KAbs(_, right_body)) => {
                cons_eq_simple(left_body, right_body)
            }
            (
                Constructor::KApp(left_functor, left_kind),
                Constructor::KApp(right_functor, right_kind),
            ) => {
                cons_eq_simple(left_functor, right_functor)
                    && kinds_eq_simple(left_kind, right_kind)
            }
            (
                Constructor::TCFun(left_explicitness, _, left_kind, left_body),
                Constructor::TCFun(right_explicitness, _, right_kind, right_body),
            ) => {
                left_explicitness == right_explicitness
                    && kinds_eq_simple(left_kind, right_kind)
                    && cons_eq_simple(left_body, right_body)
            }
            (Constructor::Name(left_name), Constructor::Name(right_name)) => {
                left_name == right_name
            }
            (Constructor::Record(_, left_fields), Constructor::Record(_, right_fields)) => {
                left_fields.len() == right_fields.len()
                    && left_fields.iter().zip(right_fields.iter()).all(
                        |(
                            (left_field_name, left_field_type),
                            (right_field_name, right_field_type),
                        )| {
                            cons_eq_simple(left_field_name, right_field_name)
                                && cons_eq_simple(left_field_type, right_field_type)
                        },
                    )
            }
            (Constructor::Concat(left_a, left_b), Constructor::Concat(right_a, right_b)) => {
                cons_eq_simple(left_a, right_a) && cons_eq_simple(left_b, right_b)
            }
            (Constructor::Map(_, _), Constructor::Map(_, _)) => true,
            (Constructor::Unit, Constructor::Unit) => true,
            (Constructor::Tuple(left_elements), Constructor::Tuple(right_elements)) => {
                left_elements.len() == right_elements.len()
                    && left_elements.iter().zip(right_elements.iter()).all(
                        |(left_element, right_element)| cons_eq_simple(left_element, right_element),
                    )
            }
            (
                Constructor::Proj(left_base, left_index),
                Constructor::Proj(right_base, right_index),
            ) => left_index == right_index && cons_eq_simple(left_base, right_base),
            (
                Constructor::Unif(_, _, _, _, left_cell),
                Constructor::Unif(_, _, _, _, right_cell),
            ) => Arc::ptr_eq(left_cell, right_cell),
            (Constructor::TFun(left_dom, left_rng), Constructor::TFun(right_dom, right_rng)) => {
                cons_eq_simple(left_dom, right_dom) && cons_eq_simple(left_rng, right_rng)
            }
            (
                Constructor::TDisjoint(left_a, left_b, left_body),
                Constructor::TDisjoint(right_a, right_b, right_body),
            ) => {
                cons_eq_simple(left_a, right_a)
                    && cons_eq_simple(left_b, right_b)
                    && cons_eq_simple(left_body, right_body)
            }
            (Constructor::TRecord(left_row), Constructor::TRecord(right_row)) => {
                cons_eq_simple(left_row, right_row)
            }
            (Constructor::TKFun(_, left_body), Constructor::TKFun(_, right_body)) => {
                cons_eq_simple(left_body, right_body)
            }
            (Constructor::Error, Constructor::Error) => true,
            _ => false,
        }
    }

    // ---------------------------------------------------------------------------
    // Tests (catch missed mutants)
    // ---------------------------------------------------------------------------

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::elaborated::{Constructor, Explicitness, Kind, Types};
        use crate::error_types::Located;
        use anyhow::anyhow; // anyhow!() macro for error construction in tests
        use std::sync::{Arc, Mutex};

        fn dummy<T>(node: T) -> Located<T> {
            Located::dummy(node)
        }

        #[test]
        fn lift_kind_in_kind_rel_plus_one() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let k = dummy(Kind::Rel(0));
            let out = lift_kind_in_kind(k);
            assert!(matches!(out.node, Kind::Rel(1)));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn lift_kind_in_kind_bound_below_unchanged() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let k = dummy(Kind::Rel(0));
            let out = lift_kind_in_kind_bound(1, 1, k);
            assert!(matches!(out.node, Kind::Rel(0)));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn sub_kind_in_kind_rel_zero_replaced() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let rep = dummy(Kind::Typed(Types::Any));
            let k = dummy(Kind::Rel(0));
            let out = sub_kind_in_kind(0, &rep, k);
            assert!(matches!(out.node, Kind::Typed(Types::Any)));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn sub_kind_in_kind_rel_above_decremented() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let rep = dummy(Kind::Typed(Types::Any));
            let k = dummy(Kind::Rel(2));
            let out = sub_kind_in_kind(0, &rep, k);
            assert!(matches!(out.node, Kind::Rel(1)));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_rel_zero() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let c = dummy(Constructor::Rel(0));
            assert!(occurs(&c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_unit_false() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let c = dummy(Constructor::Unit);
            assert!(!occurs(&c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_at_rel_at_bound() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let c = dummy(Constructor::Rel(1));
            assert!(occurs_at(0, 1, &c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_at_rel_mismatch_false() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let c = dummy(Constructor::Rel(2));
            assert!(!occurs_at(0, 1, &c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_at_tfun_in_left() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let left = dummy(Constructor::Rel(0));
            let right = dummy(Constructor::Unit);
            let c = dummy(Constructor::TFun(Box::new(left), Box::new(right)));
            assert!(occurs_at(0, 0, &c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_at_tfun_in_right() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let left = dummy(Constructor::Unit);
            let right = dummy(Constructor::Rel(0));
            let c = dummy(Constructor::TFun(Box::new(left), Box::new(right)));
            assert!(occurs_at(0, 0, &c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_at_abs_shifts_bound() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            // Under Abs, bound becomes bound+1; index 0 at outer is index 1 in body.
            let body = dummy(Constructor::Rel(2));
            let k = dummy(Kind::Typed(Types::Any));
            let c = dummy(Constructor::Abs("x".into(), Box::new(k), Box::new(body)));
            assert!(occurs_at(0, 1, &c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_at_app_in_fun() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let f = dummy(Constructor::Rel(0));
            let a = dummy(Constructor::Unit);
            let c = dummy(Constructor::App(Box::new(f), Box::new(a)));
            assert!(occurs_at(0, 0, &c));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn occurs_at_trecord_inner() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let inner = dummy(Constructor::Rel(0));
            let r = dummy(Constructor::TRecord(Box::new(inner)));
            assert!(occurs_at(0, 0, &r));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn lift_con_in_con_rel_plus_one() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let c = dummy(Constructor::Rel(0));
            let out = lift_con_in_con(c);
            assert!(matches!(out.node, Constructor::Rel(1)));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn sub_con_in_con_rel_zero_replaced() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let rep = dummy(Constructor::Named(42));
            let c = dummy(Constructor::Rel(0));
            let out = match sub_con_in_con(0, &rep, c) {
                Ok(out) => out,
                Err(_) => return Err(anyhow!("expected substitution of Rel(0) to succeed")),
            };
            assert!(matches!(out.node, Constructor::Named(42)));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn sub_con_in_con_rel_above_decremented() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let rep = dummy(Constructor::Unit);
            let c = dummy(Constructor::Rel(2));
            let out = match sub_con_in_con(0, &rep, c) {
                Ok(out) => out,
                Err(_) => {
                    return Err(anyhow!(
                        "expected substitution of higher Rel index to succeed"
                    ))
                }
            };
            assert!(matches!(out.node, Constructor::Rel(1)));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn sub_con_in_con_peels_known_unif_before_sentinel_check() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            // Build a solved constructor unifier whose stored constructor still contains the target Rel(0).
            let known_constructor = dummy(Constructor::Rel(0));
            // Store the solved constructor in the unification cell so substitution must traverse through it.
            let reference = Arc::new(Mutex::new(CUnif::Known(Box::new(known_constructor))));
            // Use a zero nesting level so a non-parity implementation would wrap to the ~1 sentinel on this node.
            let constructor = dummy(Constructor::Unif(
                0,
                crate::error_types::Span::dummy(),
                Box::new(dummy(Kind::Typed(Types::Any))),
                "known".into(),
                reference,
            ));
            // Substitute a concrete constructor for Rel(0).
            let replacement = dummy(Constructor::Named(7));
            // The solved unifier should be traversed first, so substitution succeeds instead of producing SubUnif.
            let substituted_constructor = match sub_con_in_con(0, &replacement, constructor) {
                Ok(constructor) => constructor,
                Err(_) => {
                    return Err(anyhow!(
                        "expected solved constructor unifier substitution to succeed"
                    ));
                }
            };
            // The inner Rel(0) should be replaced by the requested constructor.
            assert!(matches!(
                substituted_constructor.node,
                Constructor::Named(7)
            ));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn cons_eq_simple_tfun_same() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let u = dummy(Constructor::Unit);
            let tfun = dummy(Constructor::TFun(Box::new(u.clone()), Box::new(u)));
            assert!(cons_eq_simple(&tfun, &tfun));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn cons_eq_simple_tuple_same() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let u = dummy(Constructor::Unit);
            let t = dummy(Constructor::Tuple(vec![u.clone(), u]));
            assert!(cons_eq_simple(&t, &t));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn cons_eq_simple_record_same() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let k = dummy(Kind::Typed(Types::Any));
            let u = dummy(Constructor::Unit);
            let r = dummy(Constructor::Record(
                Box::new(k),
                vec![(dummy(Constructor::Name("x".into())), u)],
            ));
            assert!(cons_eq_simple(&r, &r));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn hnorm_does_not_beta_reduce_app_of_tcfun() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            // SML hnormCon only beta-reduces App(CAbs, c), NOT App(TCFun, c).
            // TCFun is a forall/pi type (∀ x :: K. body); CApp(TCFun, c) is NOT
            // reducible in hnorm — the ECApp elaboration handles TCFun via substitution.
            // Constructor::Abs (CAbs in SML) is the constructor lambda; TCFun is the forall.
            let k = dummy(Kind::Typed(Types::Any));
            let body = dummy(Constructor::Rel(0));
            let head = dummy(Constructor::TCFun(
                Explicitness::Implicit,
                "a".into(),
                Box::new(k),
                Box::new(body),
            ));
            let arg = dummy(Constructor::Unit);
            let app = dummy(Constructor::App(
                Box::new(head.clone()),
                Box::new(arg.clone()),
            ));
            let out = hnorm_con(app);
            // App(TCFun(...), Unit) should remain as App(...) — TCFun does not beta-reduce.
            assert!(
                matches!(&out.node, Constructor::App(h, _) if matches!(&h.node, Constructor::TCFun(..))),
                "App(TCFun, c) should not beta-reduce in hnorm_con (only App(Abs, c) does)"
            );
            Ok(()) // return success to the test harness
        }

        #[test]
        fn hnorm_con_unit_unchanged() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let c = dummy(Constructor::Unit);
            let out = hnorm_con(c);
            assert!(matches!(out.node, Constructor::Unit));
            Ok(()) // return success to the test harness
        }

        #[test]
        fn reduce_con_unit_unchanged() -> anyhow::Result<()> {
            // test returns Result to allow ? propagation
            let c = dummy(Constructor::Unit);
            let out = reduce_con(c);
            assert!(matches!(out.node, Constructor::Unit));
            Ok(()) // return success to the test harness
        }
    }
}

/// High-level type-system operations centralized in `types.rs`.
pub trait ElaboratedTypeSystem {
    /// Pretty-print this kind using the canonical formatter.
    fn pretty_kind(&self) -> String;

    /// Returns true if both kinds are equal under simplified normalization.
    fn simple_kind_eq(&self, other: &LocatedKind) -> bool;
}

impl ElaboratedTypeSystem for LocatedKind {
    fn pretty_kind(&self) -> String {
        type_display::format_kind(self)
    }

    fn simple_kind_eq(&self, other: &LocatedKind) -> bool {
        type_operations::kinds_eq_simple_public(self, other)
    }
}

/// Structural tree API over [`Kind`] / [`Constructor`] (edges, folds, presentation hook).
pub mod type_tree {
    use super::{Constructor, Kind, LocatedConstructor, LocatedKind};

    /// One immediate child reference in the elaborated kind/constructor tree.
    #[derive(Debug, Clone, Copy)]
    pub enum TypeTreeEdge<'a> {
        /// Child is another elaborated constructor node.
        Constructor(&'a LocatedConstructor),
        /// Child is a kind node (kind parameters, row kinds, etc.).
        Kind(&'a LocatedKind),
    }

    /// Either subtree root in the unified elaborated type tree (borrowed view only).
    #[derive(Debug, Clone, Copy)]
    pub enum ElaboratedTypeView<'a> {
        /// A kind node ([`LocatedKind`]).
        Kind(&'a LocatedKind),
        /// A constructor/type node ([`LocatedConstructor`]).
        Constructor(&'a LocatedConstructor),
    }

    impl<'a> ElaboratedTypeView<'a> {
        /// Invokes `visitor` once per immediate child edge, whether kind or constructor.
        pub fn for_each_immediate_edge(self, visitor: impl FnMut(TypeTreeEdge<'a>)) {
            match self {
                ElaboratedTypeView::Kind(kind) => {
                    for_each_immediate_kind_edge(kind, visitor);
                }
                ElaboratedTypeView::Constructor(constructor) => {
                    for_each_immediate_constructor_edge(constructor, visitor);
                }
            }
        }

        /// Returns the [`KindNodeClass`] or [`ConstructorNodeClass`] for this root.
        pub fn head_class(self) -> TypeHeadClass {
            match self {
                ElaboratedTypeView::Kind(kind) => TypeHeadClass::Kind(kind_node_class(&kind.node)),
                ElaboratedTypeView::Constructor(constructor) => {
                    TypeHeadClass::Constructor(constructor_node_class(&constructor.node))
                }
            }
        }
    }

    /// Classifies the head of an [`ElaboratedTypeView`] without recursing into children.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum TypeHeadClass {
        Kind(KindNodeClass),
        Constructor(ConstructorNodeClass),
    }

    /// Kind variant bucket for non-recursive inspection.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum KindNodeClass {
        Leaf,
        Composite,
        Rel,
    }

    /// Constructor variant bucket for non-recursive inspection.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum ConstructorNodeClass {
        Leaf,
        Composite,
        Binder,
    }

    /// Maps a [`Kind`] to a coarse [`KindNodeClass`].
    pub fn kind_node_class(kind: &Kind) -> KindNodeClass {
        match kind {
            Kind::Typed(_) | Kind::Name | Kind::Unit | Kind::Error => KindNodeClass::Leaf,
            Kind::Unif(..) | Kind::TupleUnif(..) => KindNodeClass::Leaf,
            Kind::Rel(_) => KindNodeClass::Rel,
            Kind::Arrow(..) | Kind::Record(..) | Kind::Tuple(..) | Kind::Fun(..) => {
                KindNodeClass::Composite
            }
        }
    }

    /// Maps a [`Constructor`] to a coarse [`ConstructorNodeClass`].
    pub fn constructor_node_class(constructor: &Constructor) -> ConstructorNodeClass {
        match constructor {
            Constructor::Unit
            | Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::ModProj(..)
            | Constructor::Name(_)
            | Constructor::Error
            | Constructor::Unif(..) => ConstructorNodeClass::Leaf,
            Constructor::TFun(..)
            | Constructor::TRecord(..)
            | Constructor::TDisjoint(..)
            | Constructor::App(..)
            | Constructor::Record(..)
            | Constructor::Concat(..)
            | Constructor::Map(..)
            | Constructor::Tuple(..)
            | Constructor::Proj(..)
            | Constructor::KApp(..) => ConstructorNodeClass::Composite,
            Constructor::TCFun(..)
            | Constructor::Abs(..)
            | Constructor::KAbs(..)
            | Constructor::TKFun(..) => ConstructorNodeClass::Binder,
        }
    }

    /// Invokes `visitor` for every immediate [`TypeTreeEdge`] under `located`.
    pub fn for_each_immediate_constructor_edge<'a>(
        located: &'a LocatedConstructor,
        mut visitor: impl FnMut(TypeTreeEdge<'a>),
    ) {
        match &located.node {
            Constructor::TFun(domain, codomain) => {
                visitor(TypeTreeEdge::Constructor(domain.as_ref()));
                visitor(TypeTreeEdge::Constructor(codomain.as_ref()));
            }
            Constructor::TCFun(_, _, parameter_kind, body) => {
                visitor(TypeTreeEdge::Kind(parameter_kind.as_ref()));
                visitor(TypeTreeEdge::Constructor(body.as_ref()));
            }
            Constructor::TRecord(row) => {
                visitor(TypeTreeEdge::Constructor(row.as_ref()));
            }
            Constructor::TDisjoint(left, right, result) => {
                visitor(TypeTreeEdge::Constructor(left.as_ref()));
                visitor(TypeTreeEdge::Constructor(right.as_ref()));
                visitor(TypeTreeEdge::Constructor(result.as_ref()));
            }
            Constructor::Rel(_)
            | Constructor::Named(_)
            | Constructor::Name(_)
            | Constructor::Unit
            | Constructor::Error => {}
            Constructor::ModProj(..) => {}
            Constructor::App(function, argument) => {
                visitor(TypeTreeEdge::Constructor(function.as_ref()));
                visitor(TypeTreeEdge::Constructor(argument.as_ref()));
            }
            Constructor::Abs(_, parameter_kind, body) => {
                visitor(TypeTreeEdge::Kind(parameter_kind.as_ref()));
                visitor(TypeTreeEdge::Constructor(body.as_ref()));
            }
            Constructor::KAbs(_, body) => {
                visitor(TypeTreeEdge::Constructor(body.as_ref()));
            }
            Constructor::KApp(head, argument_kind) => {
                visitor(TypeTreeEdge::Constructor(head.as_ref()));
                visitor(TypeTreeEdge::Kind(argument_kind.as_ref()));
            }
            Constructor::TKFun(_, body) => {
                visitor(TypeTreeEdge::Constructor(body.as_ref()));
            }
            Constructor::Record(row_kind, fields) => {
                visitor(TypeTreeEdge::Kind(row_kind.as_ref()));
                for (field_name, field_type) in fields {
                    visitor(TypeTreeEdge::Constructor(field_name));
                    visitor(TypeTreeEdge::Constructor(field_type));
                }
            }
            Constructor::Concat(left, right) => {
                visitor(TypeTreeEdge::Constructor(left.as_ref()));
                visitor(TypeTreeEdge::Constructor(right.as_ref()));
            }
            Constructor::Map(domain_kind, codomain_kind) => {
                visitor(TypeTreeEdge::Kind(domain_kind.as_ref()));
                visitor(TypeTreeEdge::Kind(codomain_kind.as_ref()));
            }
            Constructor::Tuple(components) => {
                for component in components {
                    visitor(TypeTreeEdge::Constructor(component));
                }
            }
            Constructor::Proj(tuple, _) => {
                visitor(TypeTreeEdge::Constructor(tuple.as_ref()));
            }
            Constructor::Unif(_, _, kind_placeholder, _, _) => {
                visitor(TypeTreeEdge::Kind(kind_placeholder.as_ref()));
            }
        }
    }

    /// Invokes `visitor` for every immediate [`TypeTreeEdge`] under `located`.
    pub fn for_each_immediate_kind_edge<'a>(
        located: &'a LocatedKind,
        mut visitor: impl FnMut(TypeTreeEdge<'a>),
    ) {
        match &located.node {
            Kind::Typed(_) | Kind::Name | Kind::Unit | Kind::Error => {}
            Kind::Arrow(domain, codomain) => {
                visitor(TypeTreeEdge::Kind(domain.as_ref()));
                visitor(TypeTreeEdge::Kind(codomain.as_ref()));
            }
            Kind::Record(inner) => {
                visitor(TypeTreeEdge::Kind(inner.as_ref()));
            }
            Kind::Tuple(components) => {
                for component in components {
                    visitor(TypeTreeEdge::Kind(component));
                }
            }
            Kind::Unif(..) | Kind::TupleUnif(..) | Kind::Rel(_) => {}
        }
    }

    /// Folds immediate edges of `located`, allowing early exit with `Err`.
    pub fn try_fold_constructor_edges<'a, T, E>(
        located: &'a LocatedConstructor,
        init: T,
        mut folder: impl FnMut(T, TypeTreeEdge<'a>) -> Result<T, E>,
    ) -> Result<T, E> {
        let mut buffer: Vec<TypeTreeEdge<'a>> = Vec::new();
        for_each_immediate_constructor_edge(located, |edge| buffer.push(edge));
        let mut accumulator = init;
        for edge in buffer {
            accumulator = folder(accumulator, edge)?;
        }
        Ok(accumulator)
    }

    /// Folds immediate kind edges with possible early `Err`.
    pub fn try_fold_kind_edges<'a, T, E>(
        located: &'a LocatedKind,
        init: T,
        mut folder: impl FnMut(T, TypeTreeEdge<'a>) -> Result<T, E>,
    ) -> Result<T, E> {
        let mut buffer: Vec<TypeTreeEdge<'a>> = Vec::new();
        for_each_immediate_kind_edge(located, |edge| buffer.push(edge));
        let mut accumulator = init;
        for edge in buffer {
            accumulator = folder(accumulator, edge)?;
        }
        Ok(accumulator)
    }

    /// Fallible fold over immediate children of either a kind or constructor root.
    pub fn try_fold_immediate_edges<'a, T, E>(
        root: ElaboratedTypeView<'a>,
        init: T,
        folder: impl FnMut(T, TypeTreeEdge<'a>) -> Result<T, E>,
    ) -> Result<T, E> {
        match root {
            ElaboratedTypeView::Kind(kind) => try_fold_kind_edges(kind, init, folder),
            ElaboratedTypeView::Constructor(constructor) => {
                try_fold_constructor_edges(constructor, init, folder)
            }
        }
    }

    /// Extension trait for any [`std::fmt::Write`] sink to append elaborated types.
    pub trait WriteElaboratedTypePresentation: std::fmt::Write {
        fn write_elaborated_constructor_depth_limited(
            &mut self,
            constructor: &LocatedConstructor,
            recursion_depth: u32,
        ) -> std::fmt::Result;

        fn write_elaborated_kind_depth_limited(
            &mut self,
            kind: &LocatedKind,
            recursion_depth: u32,
        ) -> std::fmt::Result;
    }

    impl<W: std::fmt::Write> WriteElaboratedTypePresentation for W {
        fn write_elaborated_constructor_depth_limited(
            &mut self,
            constructor: &LocatedConstructor,
            recursion_depth: u32,
        ) -> std::fmt::Result {
            crate::elaborated::type_display::write_constructor_into(
                self,
                constructor,
                recursion_depth,
            )
        }

        fn write_elaborated_kind_depth_limited(
            &mut self,
            kind: &LocatedKind,
            recursion_depth: u32,
        ) -> std::fmt::Result {
            crate::elaborated::type_display::write_kind_into(self, kind, recursion_depth)
        }
    }

    /// Counts constructor + kind nodes reachable from `located` (inclusive), bounded by `max_nodes`.
    pub fn count_constructor_subtree_nodes_bounded(
        located: &LocatedConstructor,
        max_nodes: usize,
    ) -> usize {
        let mut counter = 0usize;
        count_constructor_subtree_nodes_bounded_inner(located, max_nodes, &mut counter);
        counter.min(max_nodes)
    }

    fn count_constructor_subtree_nodes_bounded_inner(
        located: &LocatedConstructor,
        max_nodes: usize,
        counter: &mut usize,
    ) {
        if *counter >= max_nodes {
            return;
        }
        *counter += 1;
        if *counter >= max_nodes {
            return;
        }
        for_each_immediate_constructor_edge(located, |edge| {
            if *counter >= max_nodes {
                return;
            }
            match edge {
                TypeTreeEdge::Constructor(child) => {
                    count_constructor_subtree_nodes_bounded_inner(child, max_nodes, counter);
                }
                TypeTreeEdge::Kind(kind) => {
                    count_kind_subtree_nodes_bounded_inner(kind, max_nodes, counter);
                }
            }
        });
    }

    /// Like [`count_constructor_subtree_nodes_bounded`] for a kind root.
    pub fn count_kind_subtree_nodes_bounded(located: &LocatedKind, max_nodes: usize) -> usize {
        let mut counter = 0usize;
        count_kind_subtree_nodes_bounded_inner(located, max_nodes, &mut counter);
        counter.min(max_nodes)
    }

    fn count_kind_subtree_nodes_bounded_inner(
        located: &LocatedKind,
        max_nodes: usize,
        counter: &mut usize,
    ) {
        if *counter >= max_nodes {
            return;
        }
        *counter += 1;
        if *counter >= max_nodes {
            return;
        }
        for_each_immediate_kind_edge(located, |edge| {
            if *counter >= max_nodes {
                return;
            }
            match edge {
                TypeTreeEdge::Kind(child) => {
                    count_kind_subtree_nodes_bounded_inner(child, max_nodes, counter)
                }
                TypeTreeEdge::Constructor(child) => {
                    count_constructor_subtree_nodes_bounded_inner(child, max_nodes, counter)
                }
            }
        });
    }

    impl<'a> From<&'a LocatedKind> for ElaboratedTypeView<'a> {
        fn from(kind: &'a LocatedKind) -> Self {
            ElaboratedTypeView::Kind(kind)
        }
    }

    impl<'a> From<&'a LocatedConstructor> for ElaboratedTypeView<'a> {
        fn from(constructor: &'a LocatedConstructor) -> Self {
            ElaboratedTypeView::Constructor(constructor)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::error_types::{Located, Span};

        fn dummy_span() -> Span {
            Span::default()
        }

        fn leaf_named() -> LocatedConstructor {
            Located {
                node: Constructor::Name("x".to_string()),
                span: dummy_span(),
            }
        }

        #[test]
        fn immediate_edge_count_matches_arrow_shape() {
            let domain = leaf_named();
            let codomain = leaf_named();
            let fun = Located {
                node: Constructor::TFun(Box::new(domain), Box::new(codomain)),
                span: dummy_span(),
            };
            let mut edges = 0usize;
            for_each_immediate_constructor_edge(&fun, |_| edges += 1);
            assert_eq!(edges, 2);
        }
    }
}

#[cfg(test)]
mod ur_langsec_and_array_classifier_tests {
    use super::{
        canonicalize_langsec_string_identifier, langsec_string_identifiers_equivalent, Kind,
        RuntimePrimitiveTag, Types,
    };

    #[test]
    fn langsec_string_identifiers_treat_space_and_underscore_as_equivalent() {
        assert!(langsec_string_identifiers_equivalent(
            "Hello World!",
            "Hello_World!"
        ));
        assert!(langsec_string_identifiers_equivalent("a  b", "a__b"));
        assert!(!langsec_string_identifiers_equivalent("ab", "a_b"));
    }

    #[test]
    fn canonicalize_langsec_string_identifier_folds_to_underscore() {
        assert_eq!(
            canonicalize_langsec_string_identifier("Hello World!"),
            "Hello_World!"
        );
    }

    #[test]
    fn homogeneous_array_tags_are_distinct_and_project_element_type() {
        assert_ne!(Types::StringArray, Types::IntArray);
        assert_eq!(
            Types::StringArray.homogeneous_array_element_type(),
            Some(Types::String)
        );
        assert_eq!(Types::String.homogeneous_array_element_type(), None);
        assert!(Types::BlobArray.is_homogeneous_array());
        assert!(!Types::Blob.is_homogeneous_array());
    }

    #[test]
    fn runtime_primitive_compatible_defaults_to_symmetric_instance_of() {
        assert!(RuntimePrimitiveTag::runtime_primitive_compatible(
            Types::Int,
            Types::Any
        ));
        assert!(!RuntimePrimitiveTag::runtime_primitive_compatible(
            Types::Int,
            Types::String
        ));
    }

    #[test]
    fn kind_runtime_type_instance_of_follows_primitive_preorder() {
        let int_kind = Kind::typed(Types::Int);
        let any_kind = Kind::typed(Types::Any);
        assert!(int_kind.runtime_type_instance_of(&any_kind));
        assert!(!any_kind.runtime_type_instance_of(&int_kind));
    }

    #[test]
    fn star_structural_refinement_tags_cover_function_and_error() {
        use super::StarClassifierRefinement;
        assert!(Types::Function.is_star_structural_refinement());
        assert!(Types::Error.is_star_structural_refinement());
        assert!(!Types::Any.is_star_structural_refinement());
        assert!(!Types::Int.is_star_structural_refinement());
    }

    #[test]
    fn kinds_eq_simple_treats_any_as_compatible_with_star_refinements() {
        use crate::elaborated::type_operations::kinds_eq_simple_public;
        use crate::error_types::Located;

        let any_k = Located::dummy(Kind::typed(Types::Any));
        let fun_k = Located::dummy(Kind::typed(Types::Function));
        let err_k = Located::dummy(Kind::typed(Types::Error));
        assert!(kinds_eq_simple_public(&any_k, &fun_k));
        assert!(kinds_eq_simple_public(&fun_k, &any_k));
        assert!(kinds_eq_simple_public(&any_k, &err_k));
        assert!(!kinds_eq_simple_public(&fun_k, &err_k));
    }
}

#[macro_export]
macro_rules! elaborated_try_fold_edges {
    ($root:expr, $init:expr, |$acc:ident, $edge:ident| $body:block) => {{
        let view = $crate::elaborated::type_tree::ElaboratedTypeView::from($root);
        $crate::elaborated::type_tree::try_fold_immediate_edges(view, $init, |$acc, $edge| $body)
    }};
}
