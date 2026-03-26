//! Pretty-print elaborated [`Constructor`] and [`Kind`] for LSP hover and diagnostics.
//! Human-readable surface roughly aligned with Ur/Web type syntax (not a full `elab_print` port).

use std::fmt::Write;

use crate::elaborated::{Constructor, Kind, LocatedConstructor, LocatedKind};

const MAX_DEPTH: u32 = 48;

/// Render a constructor type for display (hover, completion detail).
pub fn format_constructor(c: &LocatedConstructor) -> String {
    let mut out = String::new();
    let _ = write_con(&mut out, c, 0);
    out
}

/// Render a kind for display.
pub fn format_kind(k: &LocatedKind) -> String {
    let mut out = String::new();
    let _ = write_kind(&mut out, k, 0);
    out
}

fn write_con(out: &mut String, c: &LocatedConstructor, depth: u32) -> std::fmt::Result {
    if depth > MAX_DEPTH {
        return write!(out, "…");
    }
    match &c.node {
        Constructor::TFun(a, b) => {
            let paren = matches!(
                a.node,
                Constructor::TFun(_, _) | Constructor::TCFun(_, _, _, _)
            );
            if paren {
                write!(out, "(")?;
            }
            write_con(out, a, depth + 1)?;
            if paren {
                write!(out, ")")?;
            }
            write!(out, " -> ")?;
            write_con(out, b, depth + 1)
        }
        Constructor::TCFun(expl, x, k, t) => {
            match expl {
                crate::elaborated::Explicitness::Implicit => write!(out, "?")?,
                crate::elaborated::Explicitness::Explicit => {}
            }
            write!(out, "{} : ", x)?;
            write_kind(out, k, depth + 1)?;
            write!(out, " -> ")?;
            write_con(out, t, depth + 1)
        }
        Constructor::TRecord(r) => {
            write!(out, "{{ ")?;
            write_con(out, r, depth + 1)?;
            write!(out, " }}")
        }
        Constructor::TDisjoint(a, b, c) => {
            write_con(out, a, depth + 1)?;
            write!(out, " * ")?;
            write_con(out, b, depth + 1)?;
            write!(out, " -> ")?;
            write_con(out, c, depth + 1)
        }
        Constructor::Rel(i) => write!(out, "'{}", i),
        Constructor::Named(n) => write!(out, "#{}", n),
        Constructor::ModProj(mid, path, name) => {
            write!(out, "mod{}:", mid)?;
            for p in path {
                write!(out, "{}.", p)?;
            }
            write!(out, "{}", name)
        }
        Constructor::App(f, a) => {
            write_con(out, f, depth + 1)?;
            write!(out, " ")?;
            let paren = !matches!(
                a.node,
                Constructor::Name(_)
                    | Constructor::Unit
                    | Constructor::Rel(_)
                    | Constructor::Named(_)
            );
            if paren {
                write!(out, "(")?;
            }
            write_con(out, a, depth + 1)?;
            if paren {
                write!(out, ")")
            } else {
                Ok(())
            }
        }
        Constructor::Abs(x, k, t) => {
            write!(out, "{} : ", x)?;
            write_kind(out, k, depth + 1)?;
            write!(out, " -> ")?;
            write_con(out, t, depth + 1)
        }
        Constructor::KAbs(x, t) => {
            write!(out, "{}:: ", x)?;
            write_con(out, t, depth + 1)
        }
        Constructor::KApp(c, k) => {
            write_con(out, c, depth + 1)?;
            write!(out, "[")?;
            write_kind(out, k, depth + 1)?;
            write!(out, "]")
        }
        Constructor::TKFun(x, t) => {
            write!(out, "{} ~> ", x)?;
            write_con(out, t, depth + 1)
        }
        Constructor::Name(s) => write!(out, "{}", s),
        Constructor::Record(kind, fields) => {
            write!(out, "{{")?;
            write_kind(out, kind, depth + 1)?;
            for (f, t) in fields {
                write!(out, ", ")?;
                write_con(out, f, depth + 1)?;
                write!(out, " : ")?;
                write_con(out, t, depth + 1)?;
            }
            write!(out, "}}")
        }
        Constructor::Concat(a, b) => {
            write_con(out, a, depth + 1)?;
            write!(out, " ++ ")?;
            write_con(out, b, depth + 1)
        }
        Constructor::Map(k, v) => {
            write!(out, "map(")?;
            write_kind(out, k, depth + 1)?;
            write!(out, ", ")?;
            write_kind(out, v, depth + 1)?;
            write!(out, ")")
        }
        Constructor::Unit => write!(out, "()"),
        Constructor::Tuple(ts) => {
            write!(out, "(")?;
            for (i, t) in ts.iter().enumerate() {
                if i > 0 {
                    write!(out, " * ")?;
                }
                write_con(out, t, depth + 1)?;
            }
            write!(out, ")")
        }
        Constructor::Proj(t, i) => {
            write_con(out, t, depth + 1)?;
            write!(out, ".{}", i)
        }
        Constructor::Error => write!(out, "<error>"),
        Constructor::Unif(_, _, _, name, _) => write!(out, "?{}", name),
    }
}

fn write_kind(out: &mut String, k: &LocatedKind, depth: u32) -> std::fmt::Result {
    if depth > MAX_DEPTH {
        return write!(out, "…");
    }
    match &k.node {
        Kind::Type => write!(out, "Type"),
        Kind::Arrow(a, b) => {
            write_kind(out, a, depth + 1)?;
            write!(out, " -> ")?;
            write_kind(out, b, depth + 1)
        }
        Kind::Name => write!(out, "Name"),
        Kind::Record(r) => {
            write!(out, "{{ ")?;
            write_kind(out, r, depth + 1)?;
            write!(out, " }}")
        }
        Kind::Unit => write!(out, "()"),
        Kind::Tuple(ks) => {
            write!(out, "(")?;
            for (i, x) in ks.iter().enumerate() {
                if i > 0 {
                    write!(out, " * ")?;
                }
                write_kind(out, x, depth + 1)?;
            }
            write!(out, ")")
        }
        Kind::Error => write!(out, "<kind error>"),
        Kind::Unif(_, name, _) => write!(out, "?{}", name),
        Kind::TupleUnif(_, _, _) => write!(out, "?tuple"),
        Kind::Rel(i) => write!(out, "'{}", i),
        Kind::Fun(x, b) => {
            write!(out, "{} -> ", x)?;
            write_kind(out, b, depth + 1)
        }
    }
}
