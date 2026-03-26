//! Deterministic recognizer for the Ur/Web **operator and application spine**
//! (comparison → additive → multiplicative → juxtaposition).
//!
//! ## Language-theoretic security ([LangSec](https://langsec.org/))
//! LangSec treats valid inputs as a **formal language** and input handling as a
//! **recognizer** for that language: recognition should be feasible, match the
//! computational power of the language, and avoid ad hoc “shotgun” parsing where
//! structure is inferred in scattered places.
//!
//! For this tier of expressions, that means:
//! - **One algorithm** defines the language of operator/application combinations
//!   (no shift/reduce tables that leave the grammar ambiguous or conflicted).
//! - **Total behavior**: every position either progresses with a defined transition
//!   or fails with an [`ExprRecognizeError`] (no implicit disambiguation).
//! - **Strict compiler**: internal invariant breaches (e.g. empty juxtaposition list)
//!   become **parse failures** via [`crate::parse::lexical_analyzer::LexError`], not
//!   `assert!` / `expect!` in production paths — reject input, do not crash the process.
//! - **Composition**: atoms (`AtomExp` in the LALRPOP grammar — literals,
//!   records, XML, parenthesized `Exp`, etc.) are a **separate** recognizer,
//!   invoked via [`parse_cmp_app_spine`]'s `parse_primary` callback. That keeps
//!   the formal boundary clear: this module recognizes *how operators and
//!   juxtaposition combine*; primaries are delegated.
//!
//! The LALRPOP `ArithExp` tier is regression-locked against this recognizer (see
//! `parse::tests::langsec_spine_equiv` in `mod.rs`) for a spine subset **without**
//! postfix `.` / `[Con]` (those remain grammar-only via [`fold_postfixes`]). LALRPOP
//! still must not emit conflicted tables (`build.rs`).
//!
//! Optional postfix after `JuxtExp` (`PostfixExp = JuxtExp | JuxtExp PostfixStar`) is
//! a known LALR pain point (reduce-vs-shift on `.` / `[`); a single recognizer story
//! for application + postfix still lives in [`fold_juxtaposition_apps`] and
//! [`fold_postfixes`] even when the generator needs further grammar or engine work
//! to eliminate table conflicts.
//!
//! ## Precedence (tight → loose), aligned with `grammar.lalrpop` `ArithExp`
//! Juxtaposition (application) → `*`, `/`, `%` → `+`, `-`, `^` (desugared to
//! `Basis.strcat` apps, left-associative) → `::` (right-associative cons) →
//! comparisons `=`, `<>`, `<`, `>`, `<=`, `>=` (left-associative).

use crate::error_types::{Located, Span};
use crate::parse::lexical_analyzer::{LexError, Token};
use crate::source::{Con, Exp, Inference, LocCon, LocExp};

/// Explicit failure modes for the operator/application recognizer (LangSec: reject, don’t guess).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprRecognizeError {
    UnexpectedEof,
    UnexpectedToken { at_byte: usize, message: String },
    ExpectedPrimary { at_byte: usize },
    UnbalancedParen { at_byte: usize },
}

impl std::fmt::Display for ExprRecognizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExprRecognizeError::UnexpectedEof => write!(f, "unexpected end of input"),
            ExprRecognizeError::UnexpectedToken { at_byte, message } => {
                write!(f, "at byte {at_byte}: {message}")
            }
            ExprRecognizeError::ExpectedPrimary { at_byte } => {
                write!(f, "at byte {at_byte}: expected an expression primary")
            }
            ExprRecognizeError::UnbalancedParen { at_byte } => {
                write!(f, "at byte {at_byte}: unbalanced ')'")
            }
        }
    }
}

impl std::error::Error for ExprRecognizeError {}

/// Token slice with a moving cursor `(start, token, end)` byte offsets.
#[derive(Debug, Clone)]
pub struct TokenCursor<'a> {
    pub tokens: &'a [(usize, Token, usize)],
    pub pos: usize,
    pub line_starts: &'a [usize],
    pub file: &'a str,
}

impl<'a> TokenCursor<'a> {
    pub fn new(
        tokens: &'a [(usize, Token, usize)],
        line_starts: &'a [usize],
        file: &'a str,
    ) -> Self {
        TokenCursor {
            tokens,
            pos: 0,
            line_starts,
            file,
        }
    }

    pub fn peek(&self) -> Option<&(usize, Token, usize)> {
        self.tokens.get(self.pos)
    }

    pub fn bump(&mut self) -> Option<(usize, Token, usize)> {
        let t = self.tokens.get(self.pos).cloned()?;
        self.pos += 1;
        Some(t)
    }

    pub fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn last_consumed_end(&self) -> Option<usize> {
        if self.pos == 0 {
            return None;
        }
        self.tokens.get(self.pos - 1).map(|t| t.2)
    }
}

fn span_bytes(file: &str, line_starts: &[usize], lo: usize, hi: usize) -> Span {
    Span::from_offsets(file, lo, hi, line_starts)
}

/// Left-fold `AtomExp+` into nested `App` nodes (same semantics as [`parse_app`]).
/// Span for the whole juxtaposition is `(lo, hi)` byte offsets; inner `App` nodes use
/// [`Span::dummy`] until line-level spans are threaded through `LocExp`.
///
/// Returns [`Err`] if `atoms` is empty — the grammar should guarantee `JuxtAtomList`
/// is non-empty; violating that is a **hard parse error** (LangSec: no silent fix).
#[must_use = "empty juxtaposition must be handled as a parse error"]
pub fn fold_juxtaposition_apps(
    atoms: Vec<LocExp>,
    file: &str,
    lo: usize,
    hi: usize,
    line_starts: &[usize],
) -> Result<LocExp, LexError> {
    let mut it = atoms.into_iter();
    let mut lhs = match it.next() {
        Some(a) => a,
        None => {
            return Err(LexError::new(
                "internal: empty juxtaposition (grammar must supply AtomExp+)",
            ));
        }
    };
    let full = span_bytes(file, line_starts, lo, hi);
    for rhs in it {
        lhs = Located::new(Exp::App(Box::new(lhs), Box::new(rhs)), Span::dummy());
    }
    Ok(Located::new(lhs.node, full))
}

/// Postfix segment after juxtaposition (`[` `Con` `]`, `.` projections), applied left-to-right.
#[derive(Debug, Clone)]
pub enum ExpPostfixOp {
    CApp(LocCon),
    DotIdent(String),
    DotHash(String),
    DotUident(String),
    DotInt(i64),
    /// `tab.{field_var}` — SQL field access via constructor variable
    DotCon(LocCon),
    /// `tab.{{fields_var}}` — SQL multi-field access via constructor
    DotCons(LocCon),
}

fn apply_postfix(base: LocExp, op: ExpPostfixOp) -> LocExp {
    let fspan = base.span.clone();
    match op {
        ExpPostfixOp::CApp(c) => Located::new(Exp::CApp(Box::new(base), c), fspan),
        ExpPostfixOp::DotIdent(name) => {
            let exp = match base.node {
                Exp::Var(mut quals, last, inf)
                    if last.chars().next().map_or(false, |c| c.is_uppercase()) =>
                {
                    quals.push(last);
                    Exp::Var(quals, name, inf)
                }
                Exp::App(f2, xbox) => {
                    let Located {
                        node: xnode,
                        span: xspan,
                    } = *xbox;
                    match xnode {
                        Exp::Var(mut q, last, inf)
                            if q.is_empty()
                                && last.chars().next().map_or(false, |c| c.is_uppercase()) =>
                        {
                            q.push(last);
                            Exp::App(f2, Box::new(Located::new(Exp::Var(q, name, inf), xspan)))
                        }
                        xnode => {
                            let f_loc = Located::new(
                                Exp::App(f2, Box::new(Located::new(xnode, xspan))),
                                fspan.clone(),
                            );
                            Exp::Field(Box::new(f_loc), Located::dummy(Con::Name(name)))
                        }
                    }
                }
                fnode => Exp::Field(
                    Box::new(Located::new(fnode, fspan.clone())),
                    Located::dummy(Con::Name(name)),
                ),
            };
            Located::new(exp, fspan)
        }
        ExpPostfixOp::DotHash(name) => Located::new(
            Exp::Field(Box::new(base), Located::dummy(Con::Name(name))),
            fspan,
        ),
        ExpPostfixOp::DotInt(n) => Located::new(
            Exp::Field(Box::new(base), Located::dummy(Con::Name(n.to_string()))),
            fspan,
        ),
        ExpPostfixOp::DotCon(c) => Located::new(Exp::Field(Box::new(base), c), fspan),
        ExpPostfixOp::DotCons(c) => Located::new(Exp::CApp(Box::new(base), c), fspan),
        ExpPostfixOp::DotUident(name) => {
            let exp = match base.node {
                Exp::Var(mut quals, last, inf) => {
                    quals.push(last);
                    Exp::Var(quals, name, inf)
                }
                Exp::App(f2, xbox) => {
                    let Located {
                        node: xnode,
                        span: xspan,
                    } = *xbox;
                    match xnode {
                        Exp::Var(mut q, last, inf) if q.is_empty() => {
                            q.push(last);
                            Exp::App(f2, Box::new(Located::new(Exp::Var(q, name, inf), xspan)))
                        }
                        _ => Exp::Var(vec![], name, Inference::DontInfer),
                    }
                }
                _ => Exp::Var(vec![], name, Inference::DontInfer),
            };
            Located::new(exp, fspan)
        }
    }
}

/// Apply postfix operators after [`fold_juxtaposition_apps`]; outer span is `(lo, hi)`.
pub fn fold_postfixes(
    base: LocExp,
    ops: Vec<ExpPostfixOp>,
    file: &str,
    lo: usize,
    hi: usize,
    line_starts: &[usize],
) -> LocExp {
    let mut cur = base;
    for op in ops {
        cur = apply_postfix(cur, op);
    }
    Located::new(cur.node, Span::from_offsets(file, lo, hi, line_starts))
}

/// True if `t` can begin an `AtomExp` in the surface grammar (FIRST set).
pub fn token_starts_primary(t: &Token) -> bool {
    match t {
        Token::Int(_)
        | Token::Float(_)
        | Token::String(_)
        | Token::Char(_)
        | Token::Unit
        | Token::True
        | Token::False
        | Token::Lparen
        | Token::Lbrace
        | Token::At
        | Token::Under
        | Token::Underunderunder
        | Token::BeginTag(_)
        | Token::XmlBeginEnd => true,
        Token::Ident(_) | Token::UpperIdent(_) => true,
        Token::UrwebPut | Token::UrwebGet | Token::UrwebTbTransfer => true,
        _ => false,
    }
}

/// Parse `CmpExp` … `PostfixExp` spine: comparisons, then add, mul, juxtaposition.
/// `parse_primary` must consume exactly one primary (typically one `AtomExp` or
/// parenthesized full expression from an outer recognizer).
pub fn parse_cmp_app_spine<F>(
    cur: &mut TokenCursor<'_>,
    mut parse_primary: F,
) -> Result<LocExp, ExprRecognizeError>
where
    F: FnMut(&mut TokenCursor<'_>) -> Result<LocExp, ExprRecognizeError>,
{
    parse_cmp(cur, &mut parse_primary)
}

fn parse_cmp<F>(cur: &mut TokenCursor<'_>, primary: &mut F) -> Result<LocExp, ExprRecognizeError>
where
    F: FnMut(&mut TokenCursor<'_>) -> Result<LocExp, ExprRecognizeError>,
{
    let mut lhs = parse_cons(cur, primary)?;
    loop {
        let Some(&(l, ref tok, _r)) = cur.peek() else {
            break;
        };
        let op = match tok {
            Token::Eq => Some("=".to_string()),
            Token::Ne => Some("<>".to_string()),
            Token::Lt => Some("<".to_string()),
            Token::Gt => Some(">".to_string()),
            Token::Le => Some("<=".to_string()),
            Token::Ge => Some(">=".to_string()),
            _ => None,
        };
        let Some(op) = op else {
            break;
        };
        cur.bump();
        let rhs = parse_cons(cur, primary)?;
        let hi = cur.last_consumed_end().unwrap_or(l);
        let lo = l;
        lhs = Located::new(
            Exp::Infix(op, Box::new(lhs), Box::new(rhs)),
            span_bytes(cur.file, cur.line_starts, lo, hi),
        );
    }
    Ok(lhs)
}

/// `::` (cons), right-associative — looser than `+`/`-`/`^`, tighter than comparisons.
fn parse_cons<F>(cur: &mut TokenCursor<'_>, primary: &mut F) -> Result<LocExp, ExprRecognizeError>
where
    F: FnMut(&mut TokenCursor<'_>) -> Result<LocExp, ExprRecognizeError>,
{
    let lhs = parse_add(cur, primary)?;
    let Some(&(l, ref tok, _)) = cur.peek() else {
        return Ok(lhs);
    };
    if !matches!(tok, Token::Dcolon) {
        return Ok(lhs);
    }
    cur.bump();
    let rhs = parse_cons(cur, primary)?;
    let hi = cur.last_consumed_end().unwrap_or(l);
    Ok(Located::new(
        Exp::Infix("::".into(), Box::new(lhs), Box::new(rhs)),
        span_bytes(cur.file, cur.line_starts, l, hi),
    ))
}

fn parse_add<F>(cur: &mut TokenCursor<'_>, primary: &mut F) -> Result<LocExp, ExprRecognizeError>
where
    F: FnMut(&mut TokenCursor<'_>) -> Result<LocExp, ExprRecognizeError>,
{
    let mut lhs = parse_mul(cur, primary)?;
    loop {
        let Some(&(l, ref tok, _r)) = cur.peek() else {
            break;
        };
        match tok {
            Token::Plus => {
                cur.bump();
                let rhs = parse_mul(cur, primary)?;
                let hi = cur.last_consumed_end().unwrap_or(l);
                lhs = Located::new(
                    Exp::Infix("+".into(), Box::new(lhs), Box::new(rhs)),
                    span_bytes(cur.file, cur.line_starts, l, hi),
                );
            }
            Token::Minus => {
                cur.bump();
                let rhs = parse_mul(cur, primary)?;
                let hi = cur.last_consumed_end().unwrap_or(l);
                lhs = Located::new(
                    Exp::Infix("-".into(), Box::new(lhs), Box::new(rhs)),
                    span_bytes(cur.file, cur.line_starts, l, hi),
                );
            }
            Token::Caret => {
                cur.bump();
                let rhs = parse_mul(cur, primary)?;
                let hi = cur.last_consumed_end().unwrap_or(l);
                let pos = span_bytes(cur.file, cur.line_starts, l, hi);
                let strcat = Located::new(
                    Exp::Var(vec!["Basis".into()], "strcat".into(), Inference::DontInfer),
                    pos.clone(),
                );
                let app1 = Located::new(Exp::App(Box::new(strcat), Box::new(lhs)), pos.clone());
                lhs = Located::new(Exp::App(Box::new(app1), Box::new(rhs)), pos);
            }
            _ => break,
        }
    }
    Ok(lhs)
}

fn parse_mul<F>(cur: &mut TokenCursor<'_>, primary: &mut F) -> Result<LocExp, ExprRecognizeError>
where
    F: FnMut(&mut TokenCursor<'_>) -> Result<LocExp, ExprRecognizeError>,
{
    let mut lhs = parse_app(cur, primary)?;
    loop {
        let Some(&(l, ref tok, _r)) = cur.peek() else {
            break;
        };
        let op = match tok {
            Token::Star => Some("*".to_string()),
            Token::Divide => Some("/".to_string()),
            Token::Mod => Some("%".to_string()),
            _ => None,
        };
        let Some(op) = op else {
            break;
        };
        cur.bump();
        let rhs = parse_app(cur, primary)?;
        let hi = cur.last_consumed_end().unwrap_or(l);
        lhs = Located::new(
            Exp::Infix(op, Box::new(lhs), Box::new(rhs)),
            span_bytes(cur.file, cur.line_starts, l, hi),
        );
    }
    Ok(lhs)
}

/// Left-associative juxtaposition (function application), matching `AppExpInner`.
fn parse_app<F>(cur: &mut TokenCursor<'_>, primary: &mut F) -> Result<LocExp, ExprRecognizeError>
where
    F: FnMut(&mut TokenCursor<'_>) -> Result<LocExp, ExprRecognizeError>,
{
    let first_idx = cur.pos;
    let mut lhs = primary(cur)?;
    let lo = cur.tokens.get(first_idx).map(|t| t.0).unwrap_or(0);
    loop {
        let Some((_, ref tok, _)) = cur.peek() else {
            break;
        };
        if !token_starts_primary(tok) {
            break;
        }
        let rhs = primary(cur)?;
        let hi = cur.last_consumed_end().unwrap_or(lo);
        lhs = Located::new(
            Exp::App(Box::new(lhs), Box::new(rhs)),
            span_bytes(cur.file, cur.line_starts, lo, hi),
        );
    }
    Ok(lhs)
}

// --- Minimal primary parser for tests (LangSec: same recognizer, tiny atom language) ---

#[cfg(test)]
fn parse_test_primary(cur: &mut TokenCursor<'_>) -> Result<LocExp, ExprRecognizeError> {
    let Some((l, tok, r)) = cur.peek().cloned() else {
        return Err(ExprRecognizeError::UnexpectedEof);
    };
    match &tok {
        Token::Ident(name) | Token::UpperIdent(name) => {
            let name = name.clone();
            cur.bump();
            Ok(Located::new(
                Exp::Var(vec![], name, Inference::DontInfer),
                span_bytes(cur.file, cur.line_starts, l, r),
            ))
        }
        Token::Int(n) => {
            let n = *n;
            cur.bump();
            Ok(Located::new(
                Exp::Prim(crate::primitives::Prim::Int(n)),
                span_bytes(cur.file, cur.line_starts, l, r),
            ))
        }
        Token::Lparen => {
            cur.bump();
            let inner = parse_cmp_app_spine(cur, parse_test_primary)?;
            match cur.bump() {
                Some((_, Token::Rparen, r2)) => Ok(Located::new(
                    inner.node,
                    span_bytes(cur.file, cur.line_starts, l, r2),
                )),
                _ => Err(ExprRecognizeError::UnbalancedParen { at_byte: l }),
            }
        }
        _ => Err(ExprRecognizeError::ExpectedPrimary { at_byte: l }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::lexical_analyzer::{tokenize_xml_aware, Token};

    fn lex_all(src: &str) -> Vec<(usize, Token, usize)> {
        tokenize_xml_aware(src).expect("lex")
    }

    #[test]
    fn mul_binds_tighter_than_add() {
        let src = "a + b * c";
        let toks = lex_all(src);
        let mut cur = TokenCursor::new(&toks, &[], "");
        let e = parse_cmp_app_spine(&mut cur, parse_test_primary).expect("parse");
        match &e.node {
            Exp::Infix(op, l, r) if op == "+" => {
                assert!(matches!(r.node, Exp::Infix(ref o, _, _) if o == "*"));
                assert!(matches!(l.node, Exp::Var(_, ref x, _) if x == "a"));
            }
            other => panic!("expected + at root, got {:?}", other),
        }
    }

    #[test]
    fn app_left_associative() {
        let src = "f g h";
        let toks = lex_all(src);
        let mut cur = TokenCursor::new(&toks, &[], "");
        let e = parse_cmp_app_spine(&mut cur, parse_test_primary).expect("parse");
        match &e.node {
            Exp::App(f, x) => {
                assert!(matches!(f.node, Exp::App(_, _)));
                assert!(matches!(x.node, Exp::Var(_, ref n, _) if n == "h"));
            }
            other => panic!("expected App at root: {:?}", other),
        }
    }

    #[test]
    fn app_tighter_than_mul() {
        let src = "f x * y";
        let toks = lex_all(src);
        let mut cur = TokenCursor::new(&toks, &[], "");
        let e = parse_cmp_app_spine(&mut cur, parse_test_primary).expect("parse");
        match &e.node {
            Exp::Infix(op, l, r) if op == "*" => {
                assert!(matches!(l.node, Exp::App(_, _)));
                assert!(matches!(r.node, Exp::Var(_, ref n, _) if n == "y"));
            }
            other => panic!("expected * at root: {:?}", other),
        }
    }

    #[test]
    fn cons_is_right_associative() {
        let src = "a :: b :: c";
        let toks = lex_all(src);
        let mut cur = TokenCursor::new(&toks, &[], "");
        let e = parse_cmp_app_spine(&mut cur, parse_test_primary).expect("parse");
        match &e.node {
            Exp::Infix(op1, l, r) if op1 == "::" => {
                assert!(matches!(l.node, Exp::Var(_, ref n, _) if n == "a"));
                match &r.node {
                    Exp::Infix(op2, l2, r2) if op2 == "::" => {
                        assert!(matches!(l2.node, Exp::Var(_, ref n, _) if n == "b"));
                        assert!(matches!(r2.node, Exp::Var(_, ref n, _) if n == "c"));
                    }
                    other => panic!("expected nested :: {:?}", other),
                }
            }
            other => panic!("expected :: at root: {:?}", other),
        }
    }

    #[test]
    fn add_tighter_than_cons() {
        // Grammar: additive tighter than ::, so (a + b) :: c
        let src = "a + b :: c";
        let toks = lex_all(src);
        let mut cur = TokenCursor::new(&toks, &[], "");
        let e = parse_cmp_app_spine(&mut cur, parse_test_primary).expect("parse");
        match &e.node {
            Exp::Infix(op, l, r) if op == "::" => {
                assert!(matches!(
                    l.node,
                    Exp::Infix(ref o, _, _) if o == "+"
                ));
                assert!(matches!(r.node, Exp::Var(_, ref n, _) if n == "c"));
            }
            other => panic!("expected :: at root: {:?}", other),
        }
    }

    #[test]
    fn strcat_caret_desugars_like_grammar() {
        let src = "a ^ b";
        let toks = lex_all(src);
        let mut cur = TokenCursor::new(&toks, &[], "");
        let e = parse_cmp_app_spine(&mut cur, parse_test_primary).expect("parse");
        match &e.node {
            Exp::App(outer, y) => {
                assert!(matches!(y.node, Exp::Var(_, ref n, _) if n == "b"));
                match &outer.node {
                    Exp::App(f, x) => {
                        if let Exp::Var(q, n, _) = &f.node {
                            assert_eq!(q, &vec!["Basis".to_string()]);
                            assert_eq!(n, "strcat");
                        } else {
                            panic!("expected strcat head: {:?}", f.node);
                        }
                        assert!(matches!(x.node, Exp::Var(_, ref n, _) if n == "a"));
                    }
                    other => panic!("expected inner App: {:?}", other),
                }
            }
            other => panic!("expected App strcat: {:?}", other),
        }
    }
}
