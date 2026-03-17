//! Ur/Web lexer built with the `logos` crate.
//!
//! This covers all tokens found in `urweb.lex` / `urweb.mlton.lex.sml`.
//! The Token enum is intended to be driven by the LALRPOP grammar in
//! `grammar.lalrpop`.
//!
//! NOTE: The SML lexer has multiple lexer states (Regular / XML / String /
//! Comment).  The logos-based lexer here handles the Regular mode; XML-mode
//! tokens (`Notags`, `BeginTag`, `EndTag`) are produced by a separate
//! hand-written XML sub-lexer invoked by the parser (future work).

use logos::Logos;

// ---------------------------------------------------------------------------
// Error type returned when the lexer can't match a token
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LexError {
    pub message: String,
}

impl LexError {
    pub fn new(msg: impl Into<String>) -> Self {
        LexError {
            message: msg.into(),
        }
    }
}

// ---------------------------------------------------------------------------
// Token enum
// ---------------------------------------------------------------------------

#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(error = LexError)]
pub enum Token {
    // -----------------------------------------------------------------------
    // Literals — declared first so they take priority over identifiers
    // -----------------------------------------------------------------------
    /// Integer literal (decimal).
    #[regex(r"-?[0-9]+", |lex| lex.slice().parse::<i64>().ok(), priority = 4)]
    Int(i64),

    /// Floating-point literal.
    #[regex(r"-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?", |lex| lex.slice().parse::<f64>().ok(), priority = 5)]
    Float(f64),

    /// Double-quoted string literal.
    #[regex(r#""([^"\\]|\\.)*""#, |lex| {
        let s = lex.slice();
        Some(s[1..s.len()-1].to_string())
    }, priority = 3)]
    String(String),

    /// Character literal `#"x"`.
    #[regex(r#"#"([^"\\]|\\.)"#, |lex| {
        // slice is e.g. #"a" — extract the char after #"
        let s = lex.slice();
        s.chars().nth(2)
    }, priority = 3)]
    Char(char),

    // -----------------------------------------------------------------------
    // Whitespace and comments — skipped
    // -----------------------------------------------------------------------
    #[regex(r"[ \t\r\n]+", logos::skip)]
    Whitespace,

    // Note: nested ML comments (* ... (* ... *) ... *) require a custom
    // lexer pass; here we skip only the outermost level.
    #[regex(r"\(\*[^*]*\*+([^)*][^*]*\*+)*\)", logos::skip)]
    Comment,

    // -----------------------------------------------------------------------
    // Unit `()` — declared before individual parens
    // -----------------------------------------------------------------------
    #[token("()", priority = 3)]
    Unit,

    // -----------------------------------------------------------------------
    // Three-char operators (highest priority among symbols)
    // -----------------------------------------------------------------------
    #[token("---", priority = 4)]
    Minusminusminus,
    #[token("::::", priority = 4)]
    Dcolonwild,
    #[token("___", priority = 4)]
    Underunderunder,
    #[token("==>", priority = 4)]
    Dkarrow,
    #[token("...", priority = 4)]
    Dotdotdot,
    #[token("<>", priority = 3)]
    Ne,
    #[token("<-", priority = 3)]
    Larrow,
    #[token("->", priority = 3)]
    Arrow,
    #[token("=>", priority = 3)]
    Darrow,
    #[token("-->", priority = 4)]
    Karrow,
    #[token("++", priority = 3)]
    Plusplus,
    #[token("--", priority = 3)]
    Minusminus,
    #[token("::", priority = 3)]
    Dcolon,
    #[token(":::", priority = 4)]
    Tcolonwild,
    #[token("__", priority = 3)]
    Underunder,
    #[token("|>", priority = 3)]
    Fwdapp,
    #[token("<|", priority = 3)]
    Revapp,
    #[token("<=", priority = 3)]
    Le,
    #[token(">=", priority = 3)]
    Ge,

    // -----------------------------------------------------------------------
    // Single-char punctuation
    // -----------------------------------------------------------------------
    #[token("(")]
    Lparen,
    #[token(")")]
    Rparen,
    #[token("[")]
    Lbrack,
    #[token("]")]
    Rbrack,
    #[token("{")]
    Lbrace,
    #[token("}")]
    Rbrace,
    #[token("^")]
    Caret,
    #[token("=")]
    Eq,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(".")]
    Dot,
    #[token("$")]
    Dollar,
    #[token("#")]
    Hash,
    #[token("_")]
    Under,
    #[token("~")]
    Twiddle,
    #[token("|")]
    Bar,
    #[token("*")]
    Star,
    #[token(";")]
    Semi,
    #[token("!")]
    Bang,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("/")]
    Divide,
    #[token("%")]
    Mod,
    #[token("@")]
    At,

    // -----------------------------------------------------------------------
    // Keywords (priority = 2 keeps them above plain identifiers)
    // -----------------------------------------------------------------------
    #[token("and", priority = 2)]
    And,
    #[token("andalso", priority = 2)]
    Andalso,
    #[token("case", priority = 2)]
    Case,
    #[token("class", priority = 2)]
    Class,
    #[token("con", priority = 2)]
    Con,
    #[token("constraint", priority = 2)]
    Constraint,
    #[token("constraints", priority = 2)]
    Constraints,
    #[token("cookie", priority = 2)]
    Cookie,
    #[token("datatype", priority = 2)]
    Datatype,
    #[token("else", priority = 2)]
    Else,
    #[token("end", priority = 2)]
    End,
    #[token("export", priority = 2)]
    Export,
    #[token("false", priority = 2)]
    False,
    #[token("ffi", priority = 2)]
    Ffi,
    #[token("fn", priority = 2)]
    Fn,
    #[token("fun", priority = 2)]
    Fun,
    #[token("functor", priority = 2)]
    Functor,
    #[token("if", priority = 2)]
    If,
    #[token("in", priority = 2)]
    In,
    #[token("include", priority = 2)]
    Include,
    // "join" is not a reserved keyword; lexes as Ident
    #[token("let", priority = 2)]
    Let,
    #[token("map", priority = 2)]
    Map,
    #[token("of", priority = 2)]
    Of,
    #[token("open", priority = 2)]
    Open,
    #[token("orelse", priority = 2)]
    Orelse,
    #[token("policy", priority = 2)]
    Policy,
    #[token("rec", priority = 2)]
    Rec,
    #[token("sequence", priority = 2)]
    Sequence,
    #[token("sig", priority = 2)]
    Sig,
    #[token("signature", priority = 2)]
    Signature,
    #[token("struct", priority = 2)]
    Struct,
    #[token("structure", priority = 2)]
    Structure,
    #[token("style", priority = 2)]
    Style,
    #[token("table", priority = 2)]
    Table,
    #[token("task", priority = 2)]
    Task,
    #[token("then", priority = 2)]
    Then,
    #[token("true", priority = 2)]
    True,
    #[token("type", priority = 2)]
    Type,
    #[token("val", priority = 2)]
    Val,
    #[token("view", priority = 2)]
    View,
    #[token("where", priority = 2)]
    Where,

    // `Name` is the kind of field names; must be priority 3 to shadow UpperIdent.
    #[token("Name", priority = 3)]
    Name,

    // `Type` is the kind of types; must be priority 3 to shadow UpperIdent.
    #[token("Type", priority = 3)]
    KindType,

    // `Unit` is the kind of unit/constraints; must be priority 3 to shadow UpperIdent.
    #[token("Unit", priority = 3)]
    KindUnit,

    // -----------------------------------------------------------------------
    // Identifiers — priority 1 (lower than keywords)
    // -----------------------------------------------------------------------
    /// Upper-case identifier (module/constructor name).
    #[regex(r"[A-Z][a-zA-Z0-9_']*", |lex| lex.slice().to_string(), priority = 1)]
    UpperIdent(String),

    /// Lower-case / underscore-started identifier.
    #[regex(r"[a-z_][a-zA-Z0-9_']*", |lex| lex.slice().to_string(), priority = 1)]
    Ident(String),

    /// Backtick-quoted qualified path: `` `M.x` ``.
    #[regex(r"`[a-zA-Z][a-zA-Z0-9_.]*`", |lex| {
        let s = lex.slice();
        s[1..s.len()-1].to_string()
    }, priority = 3)]
    BacktickPath(String),

    // -----------------------------------------------------------------------
    // XML / HTML tokens (produced by a separate state; listed here for the
    // grammar to reference)
    // -----------------------------------------------------------------------
    /// Tag name in `<foo` — only produced when XML mode is active.
    BeginTag(String),

    /// `</foo>` — only produced when XML mode is active.
    EndTag(String),

    /// Self-closing `<foo/>` — only produced when XML mode is active.
    XmlBeginEnd,

    /// Text content between tags (no `<`, `{`, or `&`).
    Notags(String),

    // -----------------------------------------------------------------------
    // Tokens produced by conditional/meta lexer states (no regex here)
    // -----------------------------------------------------------------------
    Action,
    All,
    Cconstraint,
    Cif,
    Cthen,
    Celse,
    Cwhere,
    Csymbol(String),

    // -----------------------------------------------------------------------
    // End of file (injected by the lexer iterator)
    // -----------------------------------------------------------------------
    Eof,
}

// ---------------------------------------------------------------------------
// Lexer iterator — wraps logos and yields `(start, Token, end)` triples
// ---------------------------------------------------------------------------

pub type LexResult = Result<(usize, Token, usize), LexError>;

pub struct Lexer<'input> {
    inner: logos::Lexer<'input, Token>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            inner: Token::lexer(input),
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = LexResult;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.inner.next()? {
                Ok(Token::Whitespace) | Ok(Token::Comment) => continue,
                Ok(tok) => {
                    let span = self.inner.span();
                    return Some(Ok((span.start, tok, span.end)));
                }
                Err(_) => {
                    let span = self.inner.span();
                    return Some(Err(LexError::new(format!(
                        "Unexpected character at bytes {}..{}",
                        span.start, span.end
                    ))));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_all(input: &str) -> Vec<Token> {
        Token::lexer(input)
            .filter_map(|r| r.ok())
            .filter(|t| *t != Token::Whitespace && *t != Token::Comment)
            .collect()
    }

    #[test]
    fn keywords() {
        let toks = lex_all("fun val rec let in end");
        assert_eq!(toks[0], Token::Fun);
        assert_eq!(toks[1], Token::Val);
        assert_eq!(toks[2], Token::Rec);
        assert_eq!(toks[3], Token::Let);
        assert_eq!(toks[4], Token::In);
        assert_eq!(toks[5], Token::End);
    }

    #[test]
    fn integer_literal() {
        let toks = lex_all("42");
        assert_eq!(toks[0], Token::Int(42));
    }

    #[test]
    fn negative_integer() {
        let toks = lex_all("-7");
        assert_eq!(toks[0], Token::Int(-7));
    }

    #[test]
    fn float_literal() {
        let toks = lex_all("3.14");
        match &toks[0] {
            Token::Float(f) => assert!((f - 3.14).abs() < 1e-10),
            other => panic!("expected Float, got {:?}", other),
        }
    }

    #[test]
    fn string_literal() {
        let toks = lex_all(r#""hello""#);
        assert_eq!(toks[0], Token::String("hello".into()));
    }

    #[test]
    fn operators_multi() {
        let toks = lex_all("-> => ++ --");
        assert_eq!(toks[0], Token::Arrow);
        assert_eq!(toks[1], Token::Darrow);
        assert_eq!(toks[2], Token::Plusplus);
        assert_eq!(toks[3], Token::Minusminus);
    }

    #[test]
    fn three_char_ops() {
        let toks = lex_all("--- :::");
        assert_eq!(toks[0], Token::Minusminusminus);
        assert_eq!(toks[1], Token::Tcolonwild);
    }

    #[test]
    fn identifiers() {
        let toks = lex_all("Foo bar");
        assert_eq!(toks[0], Token::UpperIdent("Foo".into()));
        assert_eq!(toks[1], Token::Ident("bar".into()));
    }

    #[test]
    fn unit_token() {
        let toks = lex_all("()");
        assert_eq!(toks[0], Token::Unit);
    }

    #[test]
    fn paren_open_close() {
        let toks = lex_all("( x )");
        assert_eq!(toks[0], Token::Lparen);
        assert_eq!(toks[1], Token::Ident("x".into()));
        assert_eq!(toks[2], Token::Rparen);
    }

    #[test]
    fn keyword_not_ident() {
        // "fun" should be Fun, not Ident
        let toks = lex_all("fun");
        assert_eq!(toks.len(), 1);
        assert_eq!(toks[0], Token::Fun);
    }

    #[test]
    fn dotdotdot() {
        let toks = lex_all("...");
        assert_eq!(toks[0], Token::Dotdotdot);
    }

    #[test]
    fn backtick_path() {
        let toks = lex_all("`Basis.alert`");
        assert_eq!(toks[0], Token::BacktickPath("Basis.alert".into()));
    }

    /// Catches Lexer::next mutant (return None) - Lexer iterator must yield tokens.
    #[test]
    fn lexer_iterator_yields_tokens() {
        let mut lexer = Lexer::new("val x = 1");
        let first = lexer.next();
        assert!(
            first.is_some(),
            "Lexer::next must return Some for valid input"
        );
        let rest: Vec<_> = lexer.collect();
        assert!(!rest.is_empty(), "Lexer must yield multiple tokens");
    }
}
