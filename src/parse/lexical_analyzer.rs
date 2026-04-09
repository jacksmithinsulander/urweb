//! Ur/Web lexer built with the `logos` crate.
//!
//! This covers all tokens found in `urweb.lex` / `urweb.mlton.lex.sml`.
//! The Token enum is intended to be driven by the LALRPOP grammar in
//! `grammar.lalrpop`.
//!
//! **`#[regex(...)]` on tokens** is Logos’s way to specify lexer *classes*
//! (compiled to a DFA). It is not application-level parsing with the `regex`
//! crate: there is no `regex::Regex` here. Full parsing is LALRPOP → AST;
//! transitive `regex-syntax` / `regex` in the lockfile come from Logos/LALRPOP
//! codegen only.
//!
//! NOTE: The SML lexer has multiple lexer states (Regular / XML / String /
//! Comment).  The logos-based lexer here handles the Regular mode; XML-mode
//! tokens (`Notags`, `BeginTag`, `EndTag`) are produced by a separate
//! hand-written XML sub-lexer invoked by the parser (future work).
//!
//! **Power of Ten / LangSec:** comment skips, string scans, and per-token dispatch loops use
//! explicit iteration caps derived from the current source length so hostile or buggy input cannot
//! drive unbounded work in one lexer step.

use logos::Logos;

/// Process SML/Ur string escape sequences: `\n`, `\t`, `\r`, `\\`, `\"`, `\^X`, `\ddd`, `\uXXXX`.
fn process_string_escapes(s: &str) -> Option<String> {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    // Escapes can consume few input bytes but emit one char; keep slack for `\u`, gaps, and UTF-8.
    let escape_work_limit = s.len().saturating_mul(8).saturating_add(64);
    for _ in 0..escape_work_limit {
        let c = match chars.next() {
            Some(ch) => ch,
            None => return Some(out),
        };
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            'r' => out.push('\r'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
            'a' => out.push('\x07'),
            'b' => out.push('\x08'),
            'f' => out.push('\x0C'),
            'v' => out.push('\x0B'),
            '0' => out.push('\0'),
            '^' => {
                // \^X — control character
                let x = chars.next()?;
                if x.is_ascii() {
                    out.push(char::from_u32((x as u32).wrapping_sub(64) & 0x1F)?);
                }
            }
            'd' => {
                // \ddd — decimal escape (SML)
                let mut digits = String::new();
                for _ in 0..2 {
                    if let Some(&d) = chars.peek() {
                        if d.is_ascii_digit() {
                            if let Some(ch) = chars.next() {
                                digits.push(ch);
                            }
                        }
                    }
                }
                let n: u32 = format!("d{}", digits)
                    .trim_start_matches('d')
                    .parse()
                    .ok()?;
                out.push(char::from_u32(n)?);
            }
            'u' => {
                // \uXXXX — unicode hex (SML)
                let hex: String = (0..4).filter_map(|_| chars.next()).collect();
                let n = u32::from_str_radix(&hex, 16).ok()?;
                out.push(char::from_u32(n)?);
            }
            ' ' | '\n' | '\t' => {
                let gap_budget = s.len().saturating_add(1);
                for _ in 0..gap_budget {
                    let c2 = match chars.peek() {
                        Some(&x) => x,
                        None => break,
                    };
                    if c2 == '\\' {
                        chars.next();
                        break;
                    }
                    chars.next();
                }
            }
            other => {
                // Unrecognized — pass through
                out.push('\\');
                out.push(other);
            }
        }
    }
    None
}

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

impl std::fmt::Display for LexError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for LexError {}

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
        process_string_escapes(&s[1..s.len()-1])
    }, priority = 3)]
    String(String),

    /// Character literal `#"x"`.
    #[regex(r#"#"([^"\\]|\\.)"#, |lex| {
        // slice is e.g. #"a" — extract the char after #"
        let s = lex.slice();
        let inner = &s[2..s.len()-1]; // strip #" and "
        process_string_escapes(inner).and_then(|s| s.chars().next())
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
    /// Signature-only: inserted before `::` on abstract `con` / `class` lines (preprocess).
    #[token("sgn_abs", priority = 6)]
    SgnAbs,
    /// Signature-only: inserted by `preprocess_urs` after `::` kind on `con` / `class` lines
    /// (replaces `=` before the defining `Con`) so the grammar need not use ε before the RHS.
    #[token("sgn_def_con", priority = 6)]
    SgnDefCon,
    /// Optional leading `|` right after `case` … `of` (`urweb.grm` `barOpt`) — disjoint from `arm_sep`.
    #[token("case_bar", priority = 6)]
    CaseBar,
    /// Between `case` arms (not the optional leading bar).
    #[token("arm_sep", priority = 6)]
    ArmSep,
    /// Closes the `case` … `of` arm list before `;` / `)` / `}` (inserted by preprocess; disjoint
    /// from `arm_sep` so `CaseArmsMore` need not use a nullable tail with the same lookahead).
    #[token("case_end", priority = 6)]
    CaseEnd,
    /// In `datatype` … `=` constructor lists only (`rewrite_datatype_constructors`).
    #[token("dtype_of", priority = 6)]
    DtypeOf,
    /// Nullary datatype constructor marker (inserted before `dt_bar` / `dt_done` when no `dtype_of`).
    #[token("dt_con0", priority = 6)]
    DtCon0,
    #[token("dt_bar", priority = 6)]
    DtBar,
    /// Ends a `datatype` … `=` constructor list (before `and` / `;`).
    #[token("dt_done", priority = 6)]
    DtDone,
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

    /// ML `AT` paths: produced only by [`XmlAwareLexer`], not the Logos table.
    #[logos(skip)]
    AtTypesOnlyPath(String),
    /// ML `AT AT` paths: produced only by [`XmlAwareLexer`].
    #[logos(skip)]
    AtDontInferPath(String),

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
    /// Native KV / ledger surface (`compiler`-injected `UrwebNative` shims).
    #[token("urweb_put", priority = 2)]
    UrwebPut,
    #[token("urweb_get", priority = 2)]
    UrwebGet,
    #[token("urweb_tb_transfer", priority = 2)]
    UrwebTbTransfer,
    /// Signature `where` at paren depth 0 (`rewrite_sgn_where`).
    #[token("sgn_where", priority = 6)]
    Where,
    /// Signature `where` inside `(...)` (depth > 0) — disjoint from `sgn_where` for LR(1).
    #[token("sgn_subwhere", priority = 6)]
    SgnSubwhere,

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
    As,
    Cconstraint,
    Cif,
    Cthen,
    Celse,
    Cwhere,
    Count,
    Csymbol(String),
    CurrentTimestamp,
    Delete,
    From,
    Insert,
    Into,
    Is,
    Join,
    Left,
    Null,
    On,
    Set,
    Sql,
    SqlStar,
    Select,
    OrUpper,
    AndUpper,
    Update,
    Values,

    /// XML tag attribute name when the next non-whitespace byte is `=` (LangSec: disjoint from bare).
    XmlAttrNameEq(String),
    /// XML tag attribute name when not followed by `=` (boolean / bare attribute).
    XmlAttrNameBare(String),

    // -----------------------------------------------------------------------
    // Compound token: `_` followed by `::` (with optional whitespace).
    // Emitted by XmlAwareLexer to avoid LALR state-merge ambiguity.
    // -----------------------------------------------------------------------
    WildAnnot,

    // -----------------------------------------------------------------------
    // End of file (injected by the lexer iterator)
    // -----------------------------------------------------------------------
    Eof,
}

/// Human-oriented token descriptions for catalog parse details (not [`Debug`](std::fmt::Debug)).
impl std::fmt::Display for Token {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Shorten long string literals inside error lines.
        fn push_truncated_string(
            formatter: &mut std::fmt::Formatter<'_>,
            prefix: &str,
            text: &str,
            closing: &str,
        ) -> std::fmt::Result {
            const MAX_CHARS: usize = 32;
            let shortened: String = text.chars().take(MAX_CHARS).collect();
            let ellipsis = if text.chars().count() > MAX_CHARS {
                "…"
            } else {
                ""
            };
            write!(formatter, "{prefix}{shortened}{ellipsis}{closing}")
        }
        match self {
            Token::Int(value) => write!(formatter, "integer literal `{value}`"),
            Token::Float(value) => write!(formatter, "float literal `{value}`"),
            Token::String(text) => {
                write!(formatter, "string literal \"")?;
                push_truncated_string(formatter, "", text, "\"")?;
                Ok(())
            }
            Token::Char(character) => write!(formatter, "character literal `#\"{character}\"`"),
            Token::Whitespace => write!(formatter, "<whitespace>"),
            Token::Comment => write!(formatter, "<comment>"),
            Token::Unit => write!(formatter, "`()`"),
            Token::Minusminusminus => write!(formatter, "`---`"),
            Token::Dcolonwild => write!(formatter, "`::::`"),
            Token::Underunderunder => write!(formatter, "`___`"),
            Token::SgnAbs => write!(formatter, "`sgn_abs`"),
            Token::SgnDefCon => write!(formatter, "`sgn_def_con`"),
            Token::CaseBar => write!(formatter, "`case_bar`"),
            Token::ArmSep => write!(formatter, "`arm_sep`"),
            Token::CaseEnd => write!(formatter, "`case_end`"),
            Token::DtypeOf => write!(formatter, "`dtype_of`"),
            Token::DtCon0 => write!(formatter, "`dt_con0`"),
            Token::DtBar => write!(formatter, "`dt_bar`"),
            Token::DtDone => write!(formatter, "`dt_done`"),
            Token::Dkarrow => write!(formatter, "`==>`"),
            Token::Dotdotdot => write!(formatter, "`...`"),
            Token::Ne => write!(formatter, "`<>`"),
            Token::Larrow => write!(formatter, "`<-`"),
            Token::Arrow => write!(formatter, "`->`"),
            Token::Darrow => write!(formatter, "`=>`"),
            Token::Karrow => write!(formatter, "`-->`"),
            Token::Plusplus => write!(formatter, "`++`"),
            Token::Minusminus => write!(formatter, "`--`"),
            Token::Dcolon => write!(formatter, "`::`"),
            Token::Tcolonwild => write!(formatter, "`:::`"),
            Token::Underunder => write!(formatter, "`__`"),
            Token::Fwdapp => write!(formatter, "`|>`"),
            Token::Revapp => write!(formatter, "`<|`"),
            Token::Le => write!(formatter, "`<=`"),
            Token::Ge => write!(formatter, "`>=`"),
            Token::Lparen => write!(formatter, "`(`"),
            Token::Rparen => write!(formatter, "`)`"),
            Token::Lbrack => write!(formatter, "`[`"),
            Token::Rbrack => write!(formatter, "`]`"),
            Token::Lbrace => write!(formatter, "`{{`"),
            Token::Rbrace => write!(formatter, "`}}`"),
            Token::Caret => write!(formatter, "`^`"),
            Token::Eq => write!(formatter, "`=`"),
            Token::Lt => write!(formatter, "`<`"),
            Token::Gt => write!(formatter, "`>`"),
            Token::Comma => write!(formatter, "`,`"),
            Token::Colon => write!(formatter, "`:`"),
            Token::Dot => write!(formatter, "`.`"),
            Token::Dollar => write!(formatter, "`$`"),
            Token::Hash => write!(formatter, "`#`"),
            Token::Under => write!(formatter, "`_`"),
            Token::Twiddle => write!(formatter, "`~`"),
            Token::Bar => write!(formatter, "`|`"),
            Token::Star => write!(formatter, "`*`"),
            Token::Semi => write!(formatter, "`;`"),
            Token::Bang => write!(formatter, "`!`"),
            Token::Plus => write!(formatter, "`+`"),
            Token::Minus => write!(formatter, "`-`"),
            Token::Divide => write!(formatter, "`/`"),
            Token::Mod => write!(formatter, "`%`"),
            Token::At => write!(formatter, "`@`"),
            Token::AtTypesOnlyPath(s) => write!(formatter, "`@` path (types-only) `{s}`"),
            Token::AtDontInferPath(s) => write!(formatter, "`@@` path (no infer) `{s}`"),
            Token::And => write!(formatter, "`and`"),
            Token::Andalso => write!(formatter, "`andalso`"),
            Token::Case => write!(formatter, "`case`"),
            Token::Class => write!(formatter, "`class`"),
            Token::Con => write!(formatter, "`con`"),
            Token::Constraint => write!(formatter, "`constraint`"),
            Token::Constraints => write!(formatter, "`constraints`"),
            Token::Cookie => write!(formatter, "`cookie`"),
            Token::Datatype => write!(formatter, "`datatype`"),
            Token::Else => write!(formatter, "`else`"),
            Token::End => write!(formatter, "`end`"),
            Token::Export => write!(formatter, "`export`"),
            Token::False => write!(formatter, "`false`"),
            Token::Ffi => write!(formatter, "`ffi`"),
            Token::Fn => write!(formatter, "`fn`"),
            Token::Fun => write!(formatter, "`fun`"),
            Token::Functor => write!(formatter, "`functor`"),
            Token::If => write!(formatter, "`if`"),
            Token::In => write!(formatter, "`in`"),
            Token::Include => write!(formatter, "`include`"),
            Token::Let => write!(formatter, "`let`"),
            Token::Map => write!(formatter, "`map`"),
            Token::Of => write!(formatter, "`of`"),
            Token::Open => write!(formatter, "`open`"),
            Token::Orelse => write!(formatter, "`orelse`"),
            Token::Policy => write!(formatter, "`policy`"),
            Token::Rec => write!(formatter, "`rec`"),
            Token::Sequence => write!(formatter, "`sequence`"),
            Token::Sig => write!(formatter, "`sig`"),
            Token::Signature => write!(formatter, "`signature`"),
            Token::Struct => write!(formatter, "`struct`"),
            Token::Structure => write!(formatter, "`structure`"),
            Token::Style => write!(formatter, "`style`"),
            Token::Table => write!(formatter, "`table`"),
            Token::Task => write!(formatter, "`task`"),
            Token::Then => write!(formatter, "`then`"),
            Token::True => write!(formatter, "`true`"),
            Token::Type => write!(formatter, "`type`"),
            Token::Val => write!(formatter, "`val`"),
            Token::View => write!(formatter, "`view`"),
            Token::UrwebPut => write!(formatter, "`urweb_put`"),
            Token::UrwebGet => write!(formatter, "`urweb_get`"),
            Token::UrwebTbTransfer => write!(formatter, "`urweb_tb_transfer`"),
            Token::Where => write!(formatter, "`sgn_where`"),
            Token::SgnSubwhere => write!(formatter, "`sgn_subwhere`"),
            Token::Name => write!(formatter, "`Name`"),
            Token::KindType => write!(formatter, "`Type`"),
            Token::KindUnit => write!(formatter, "`Unit`"),
            Token::UpperIdent(name) => write!(formatter, "upper identifier `{name}`"),
            Token::Ident(name) => write!(formatter, "identifier `{name}`"),
            Token::BacktickPath(path) => write!(formatter, "backtick path `{path}`"),
            Token::BeginTag(name) => write!(formatter, "XML `<{name}`"),
            Token::EndTag(name) => write!(formatter, "XML `</{name}>`"),
            Token::XmlBeginEnd => write!(formatter, "XML self-closing `/>`"),
            Token::Notags(text) => {
                write!(formatter, "XML text \"")?;
                push_truncated_string(formatter, "", text, "\"")?;
                Ok(())
            }
            Token::Action => write!(formatter, "`ACTION`"),
            Token::All => write!(formatter, "`ALL`"),
            Token::As => write!(formatter, "`AS`"),
            Token::Cconstraint => write!(formatter, "`CONSTRAINT`"),
            Token::Cif => write!(formatter, "`IF`"),
            Token::Cthen => write!(formatter, "`THEN`"),
            Token::Celse => write!(formatter, "`ELSE`"),
            Token::Cwhere => write!(formatter, "`WHERE`"),
            Token::Count => write!(formatter, "`COUNT`"),
            Token::Csymbol(symbol) => write!(formatter, "cookie/policy symbol `{symbol}`"),
            Token::CurrentTimestamp => write!(formatter, "`CURRENT_TIMESTAMP`"),
            Token::Delete => write!(formatter, "`DELETE`"),
            Token::From => write!(formatter, "`FROM`"),
            Token::Insert => write!(formatter, "`INSERT`"),
            Token::Into => write!(formatter, "`INTO`"),
            Token::Is => write!(formatter, "`IS`"),
            Token::Join => write!(formatter, "`JOIN`"),
            Token::Left => write!(formatter, "`LEFT`"),
            Token::Null => write!(formatter, "`NULL`"),
            Token::On => write!(formatter, "`ON`"),
            Token::Set => write!(formatter, "`SET`"),
            Token::Sql => write!(formatter, "`SQL`"),
            Token::SqlStar => write!(formatter, "`sql_star`"),
            Token::Select => write!(formatter, "`SELECT`"),
            Token::OrUpper => write!(formatter, "`OR`"),
            Token::AndUpper => write!(formatter, "`AND`"),
            Token::Update => write!(formatter, "`UPDATE`"),
            Token::Values => write!(formatter, "`VALUES`"),
            Token::XmlAttrNameEq(name) => write!(formatter, "XML attribute `{name}` (=`...)"),
            Token::XmlAttrNameBare(name) => write!(formatter, "XML attribute `{name}` (boolean)"),
            Token::WildAnnot => write!(formatter, "`_ ::`"),
            Token::Eof => write!(formatter, "<end of input>"),
        }
    }
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
        let skip_cap = self.inner.source().len().saturating_add(1);
        for _ in 0..skip_cap {
            let step = self.inner.next()?;
            match step {
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
        Some(Err(LexError::new(
            "lexer exceeded whitespace/comment skip budget (internal)",
        )))
    }
}

// ---------------------------------------------------------------------------
// XML-aware multi-mode lexer
// ---------------------------------------------------------------------------
//
// This replaces the simple Logos-based Lexer for parsing `.ur` files,
// adding support for the XML/XMLTAG modes required by Ur/Web's XML syntax.
//
// Mode stack:
//   Regular  — normal Ur/Web code
//   Xml      — inside `<xml>...</xml>` content
//   XmlTag   — inside a tag's attribute list `<p class="foo">`
//
// Brace-level tracking: when `{` is seen in Xml or XmlTag mode the lexer
// pushes the current mode onto `brace_stack` and enters Regular mode.
// When `}` is encountered in Regular mode with a non-empty brace_stack,
// the brace depth is decremented; if it reaches zero the previous mode is
// restored.

#[derive(Clone, Debug, PartialEq)]
enum LexMode {
    Regular,
    Xml,
    XmlTag,
}

pub struct XmlAwareLexer<'a> {
    src: &'a [u8],
    pos: usize,
    mode: LexMode,
    /// Stack of (return_mode, brace_depth) pushed by `{` in XML/XmlTag modes.
    brace_stack: Vec<(LexMode, usize)>,
    /// String-mode return: set to Some(mode) when entering a string from XmlTag.
    string_return: Option<LexMode>,
    /// Buffered tokens produced in one scan step (for multi-token XML escapes).
    pending: std::collections::VecDeque<(usize, Token, usize)>,
    /// Nesting depth of `<xml>` tags seen inside Xml mode.
    /// 0 means the current `</xml>` closes the outer wrapper (switch back to Regular).
    xml_nesting: i32,
    /// True when the most-recent BeginTag in Xml mode was "xml" and we haven't
    /// yet seen the corresponding `>` or `/>` in XmlTag mode.
    pending_xml_open: bool,
}

impl<'a> XmlAwareLexer<'a> {
    pub fn new(src: &'a str) -> Self {
        XmlAwareLexer {
            src: src.as_bytes(),
            pos: 0,
            mode: LexMode::Regular,
            brace_stack: Vec::new(),
            string_return: None,
            pending: std::collections::VecDeque::new(),
            xml_nesting: 0,
            pending_xml_open: false,
        }
    }

    fn at(&self, offset: usize) -> Option<u8> {
        self.src.get(self.pos + offset).copied()
    }

    fn skip_ml_comment(&mut self) {
        // Already consumed `(*`; consume until matching `*)`, supporting nesting.
        let mut depth = 1usize;
        let scan_cap = self.src.len().saturating_mul(2).saturating_add(1);
        for _ in 0..scan_cap {
            if self.pos >= self.src.len() {
                return;
            }
            if self.pos + 1 < self.src.len()
                && self.src[self.pos] == b'('
                && self.src[self.pos + 1] == b'*'
            {
                depth += 1;
                self.pos += 2;
            } else if self.pos + 1 < self.src.len()
                && self.src[self.pos] == b'*'
                && self.src[self.pos + 1] == b')'
            {
                depth -= 1;
                self.pos += 2;
                if depth == 0 {
                    return;
                }
            } else {
                self.pos += 1;
            }
        }
        self.pos = self.src.len();
    }

    fn skip_xml_comment(&mut self) {
        // Already consumed `<!--`; consume until `-->`.
        let scan_cap = self.src.len().saturating_add(1);
        for _ in 0..scan_cap {
            if self.pos + 2 < self.src.len() {
                if &self.src[self.pos..self.pos + 3] == b"-->" {
                    self.pos += 3;
                    return;
                }
                self.pos += 1;
            } else {
                self.pos = self.src.len();
                return;
            }
        }
        self.pos = self.src.len();
    }

    fn scan_xml_id(&self, start: usize) -> usize {
        // xmlid = [A-Za-z][A-Za-z0-9_-]*
        let mut p = start;
        if p < self.src.len() && self.src[p].is_ascii_alphabetic() {
            p += 1;
            let tail_budget = self.src.len().saturating_sub(p).saturating_add(1);
            for _ in 0..tail_budget {
                if p >= self.src.len() {
                    break;
                }
                let b = self.src[p];
                if b.is_ascii_alphanumeric() || b == b'_' || b == b'-' {
                    p += 1;
                } else {
                    break;
                }
            }
        }
        p
    }

    fn scan_regular_string(&mut self, quote: u8, start: usize) -> LexResult {
        // Consume string body up to matching unescaped `quote`.
        let mut s = String::new();
        let body_cap = self.src.len().saturating_sub(start).saturating_add(1);
        for _ in 0..body_cap {
            if self.pos >= self.src.len() {
                return Err(LexError::new("Unterminated string literal"));
            }
            let b = self.src[self.pos];
            if b == b'\\' {
                self.pos += 1;
                if self.pos >= self.src.len() {
                    return Err(LexError::new("Unterminated escape in string"));
                }
                let esc = self.src[self.pos];
                self.pos += 1;
                match esc {
                    b'n' => s.push('\n'),
                    b't' => s.push('\t'),
                    b'r' => s.push('\r'),
                    b'\\' => s.push('\\'),
                    b'"' => s.push('"'),
                    b'\'' => s.push('\''),
                    b'a' => s.push('\x07'),
                    b'b' => s.push('\x08'),
                    b'f' => s.push('\x0C'),
                    b'v' => s.push('\x0B'),
                    b'0' => s.push('\0'),
                    _ => {
                        s.push('\\');
                        s.push(esc as char);
                    }
                }
            } else if b == quote {
                self.pos += 1;
                let end = self.pos;
                // If inside XmlTag, restore XmlTag mode after string
                if let Some(ret) = self.string_return.take() {
                    self.mode = ret;
                }
                return Ok((start, Token::String(s), end));
            } else {
                s.push(b as char);
                self.pos += 1;
            }
        }
        Err(LexError::new("Unterminated string literal (scan budget)"))
    }

    /// Keywords / pseudo-keywords that must not fuse with `@` into [`Token::AtTypesOnlyPath`].
    fn word_rejects_at_path_compound(word: &str) -> bool {
        matches!(
            word,
            "and"
                | "andalso"
                | "case"
                | "class"
                | "con"
                | "constraint"
                | "constraints"
                | "cookie"
                | "datatype"
                | "else"
                | "end"
                | "export"
                | "false"
                | "ffi"
                | "fn"
                | "fun"
                | "functor"
                | "if"
                | "in"
                | "include"
                | "let"
                | "map"
                | "of"
                | "open"
                | "orelse"
                | "policy"
                | "rec"
                | "sequence"
                | "sig"
                | "signature"
                | "struct"
                | "structure"
                | "style"
                | "table"
                | "task"
                | "then"
                | "true"
                | "type"
                | "val"
                | "view"
                | "urweb_put"
                | "urweb_get"
                | "urweb_tb_transfer"
                | "sgn_abs"
                | "sgn_def_con"
                | "case_bar"
                | "arm_sep"
                | "case_end"
                | "dtype_of"
                | "dt_con0"
                | "dt_bar"
                | "dt_done"
                | "sgn_where"
                | "sgn_subwhere"
                | "Name"
                | "Type"
                | "Unit"
        )
    }

    /// Consume Ur/Web identifier run (ASCII alnum, `_`, `'`).
    fn scan_ident_run(&self, mut index: usize) -> usize {
        let run_cap = self.src.len().saturating_sub(index).saturating_add(1);
        for _ in 0..run_cap {
            if index >= self.src.len() {
                break;
            }
            let byte = self.src[index];
            if byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'\'' {
                index += 1;
            } else {
                break;
            }
        }
        index
    }

    /// ML `eterm`: `AT path|cpath` and `AT AT path|cpath` as one token (matches upstream longest path).
    fn scan_at_inference_path(&mut self, start: usize) -> Option<LexResult> {
        let mut index = start + 1;
        if index >= self.src.len() {
            return None;
        }
        let mut dont_infer = false;
        if self.src[index] == b'@' {
            dont_infer = true;
            index += 1;
        }
        if index >= self.src.len() {
            return None;
        }
        if !matches!(
            self.src[index],
            b'a'..=b'z' | b'A'..=b'Z' | b'_'
        ) {
            return None;
        }
        let first_start = index;
        index = self.scan_ident_run(first_start);
        let first = std::str::from_utf8(&self.src[first_start..index]).unwrap_or("");
        if Self::word_rejects_at_path_compound(first) {
            return None;
        }
        let mut dotted = String::new();
        dotted.push_str(first);
        let dot_path_budget = self.src.len().saturating_sub(index).saturating_add(1);
        for _ in 0..dot_path_budget {
            if index >= self.src.len() || self.src[index] != b'.' {
                break;
            }
            let after_dot = index + 1;
            if after_dot >= self.src.len()
                || !matches!(
                    self.src[after_dot],
                    b'a'..=b'z' | b'A'..=b'Z' | b'_'
                )
            {
                break;
            }
            let seg_start = after_dot;
            let seg_end = self.scan_ident_run(seg_start);
            if seg_end == seg_start {
                break;
            }
            let seg = std::str::from_utf8(&self.src[seg_start..seg_end]).unwrap_or("");
            dotted.push('.');
            dotted.push_str(seg);
            index = seg_end;
        }
        self.pos = index;
        let token = if dont_infer {
            Token::AtDontInferPath(dotted)
        } else {
            Token::AtTypesOnlyPath(dotted)
        };
        Some(Ok((start, token, self.pos)))
    }

    fn next_regular(&mut self) -> Option<LexResult> {
        let stride_limit = self.src.len().saturating_add(1);
        'lex: for _ in 0..stride_limit {
            if self.pos >= self.src.len() {
                return None;
            }
            let start = self.pos;
            let b = self.src[self.pos];

            // Skip whitespace
            if b == b' ' || b == b'\t' || b == b'\r' || b == b'\n' {
                self.pos += 1;
                continue 'lex;
            }

            // ML comment `(*...*)` with nesting
            if b == b'(' && self.at(1) == Some(b'*') {
                self.pos += 2;
                self.skip_ml_comment();
                continue 'lex;
            }

            // String: "..." or '...' (the latter is also valid in Ur/Web)
            if b == b'"' || b == b'\'' {
                self.pos += 1;
                return Some(self.scan_regular_string(b, start));
            }

            // Char literal `#"x"`
            if b == b'#' && self.at(1) == Some(b'"') {
                self.pos += 2;
                if self.pos >= self.src.len() {
                    return Some(Err(LexError::new("Unterminated char literal")));
                }
                let ch = self.src[self.pos] as char;
                self.pos += 1;
                if self.pos < self.src.len() && self.src[self.pos] == b'"' {
                    self.pos += 1;
                }
                return Some(Ok((start, Token::Char(ch), self.pos)));
            }

            // `<` — may be XML start or comparison operator
            if b == b'<' {
                // Try `<xmlid/>` first (INITIAL XML self-closing)
                let id_start = self.pos + 1;
                let id_end = self.scan_xml_id(id_start);
                if id_end > id_start {
                    let rest = id_end;
                    // `<xmlid/>`?
                    if self.at(rest - self.pos) == Some(b'/')
                        && self.at(rest - self.pos + 1) == Some(b'>')
                    {
                        let _name = std::str::from_utf8(&self.src[id_start..id_end])
                            .unwrap_or("")
                            .to_string();
                        self.pos = id_end + 2; // skip `/>`
                        return Some(Ok((start, Token::XmlBeginEnd, self.pos)));
                    }
                    // `<xmlid>`?
                    if self.at(rest - self.pos) == Some(b'>') {
                        let name = std::str::from_utf8(&self.src[id_start..id_end])
                            .unwrap_or("")
                            .to_string();
                        self.pos = id_end + 1; // skip `>`
                                               // Enter XML mode; reset xml nesting counter
                        self.mode = LexMode::Xml;
                        self.xml_nesting = 0;
                        return Some(Ok((start, Token::BeginTag(name), self.pos)));
                    }
                }
                // Not XML: fall through to regular `<` handling
            }

            // Multi-char operators (longest first)
            let tok = self.try_multi_char_op();
            if let Some(t) = tok {
                return Some(Ok((start, t, self.pos)));
            }

            // `{` and `}` with brace-level tracking
            if b == b'{' {
                self.pos += 1;
                // If we're in a brace-stack context, increment depth
                if let Some((_, depth)) = self.brace_stack.last_mut() {
                    *depth += 1;
                }
                return Some(Ok((start, Token::Lbrace, self.pos)));
            }
            if b == b'}' {
                self.pos += 1;
                if let Some((ret_mode, depth)) = self.brace_stack.last_mut() {
                    if *depth == 1 {
                        let ret = ret_mode.clone();
                        self.brace_stack.pop();
                        self.mode = ret;
                    } else {
                        *depth -= 1;
                    }
                }
                return Some(Ok((start, Token::Rbrace, self.pos)));
            }

            // `(` with brace-level tracking (for XML-escaped `(` like in `tag (con)`)
            if b == b'(' {
                if self.at(1) == Some(b')') {
                    self.pos += 2;
                    return Some(Ok((start, Token::Unit, self.pos)));
                }
                self.pos += 1;
                if let Some((_, depth)) = self.brace_stack.last_mut() {
                    *depth += 1;
                }
                return Some(Ok((start, Token::Lparen, self.pos)));
            }
            if b == b')' {
                self.pos += 1;
                if let Some((ret_mode, depth)) = self.brace_stack.last_mut() {
                    if *depth == 1 {
                        let ret = ret_mode.clone();
                        self.brace_stack.pop();
                        self.mode = ret;
                    } else {
                        *depth -= 1;
                    }
                }
                return Some(Ok((start, Token::Rparen, self.pos)));
            }

            // Numeric literals
            if b.is_ascii_digit() || (b == b'-' && self.at(1).is_some_and(|c| c.is_ascii_digit())) {
                return Some(self.scan_number(start));
            }

            // Identifiers and keywords
            if b.is_ascii_alphabetic() || b == b'_' {
                return Some(self.scan_ident(start));
            }

            // `@` / `@@` + dotted path (`urweb.grm` `AT`/`AT AT` on `path`/`cpath`); otherwise bare `@`.
            if b == b'@' {
                if let Some(found) = self.scan_at_inference_path(start) {
                    return Some(found);
                }
                self.pos += 1;
                return Some(Ok((start, Token::At, self.pos)));
            }

            // Single-char punctuation
            self.pos += 1;
            let tok = match b {
                b'[' => Token::Lbrack,
                b']' => Token::Rbrack,
                b'^' => Token::Caret,
                b'=' => Token::Eq,
                b'>' => Token::Gt,
                b',' => Token::Comma,
                b':' => Token::Colon,
                b'.' => Token::Dot,
                b'$' => Token::Dollar,
                b'#' => Token::Hash,
                b'_' => Token::Under,
                b'~' => Token::Twiddle,
                b'|' => Token::Bar,
                b'*' => Token::Star,
                b';' => Token::Semi,
                b'!' => Token::Bang,
                b'+' => Token::Plus,
                b'-' => Token::Minus,
                b'/' => Token::Divide,
                b'%' => Token::Mod,
                b'<' => Token::Lt,
                b'`' => {
                    // Backtick path
                    let path_start = self.pos;
                    let tick_cap = self.src.len().saturating_sub(self.pos).saturating_add(1);
                    for _ in 0..tick_cap {
                        if self.pos >= self.src.len() {
                            break;
                        }
                        if self.src[self.pos] == b'`' {
                            break;
                        }
                        self.pos += 1;
                    }
                    let path = std::str::from_utf8(&self.src[path_start..self.pos])
                        .unwrap_or("")
                        .to_string();
                    if self.pos < self.src.len() {
                        self.pos += 1;
                    } // skip closing `
                    return Some(Ok((start, Token::BacktickPath(path), self.pos)));
                }
                other => {
                    return Some(Err(LexError::new(format!(
                        "Unexpected character '{}' (0x{:02x}) at offset {}",
                        other as char, other, start
                    ))));
                }
            };
            return Some(Ok((start, tok, self.pos)));
        }
        Some(Err(LexError::new(
            "XmlAwareLexer: exceeded per-token scan budget in Regular mode",
        )))
    }

    fn try_multi_char_op(&mut self) -> Option<Token> {
        let s = &self.src[self.pos..];
        let (tok, len) = match s {
            // 4-char
            [b':', b':', b':', b':', ..] => (Token::Dcolonwild, 4),
            [b'_', b'_', b'_', ..] => (Token::Underunderunder, 3),
            [b'=', b'=', b'>', ..] => (Token::Dkarrow, 3),
            [b'.', b'.', b'.', ..] => (Token::Dotdotdot, 3),
            [b'-', b'-', b'-', ..] => (Token::Minusminusminus, 3),
            [b'-', b'-', b'>', ..] => (Token::Karrow, 3),
            [b':', b':', b':', ..] => (Token::Tcolonwild, 3),
            // 2-char
            [b'<', b'>', ..] => (Token::Ne, 2),
            [b'<', b'-', ..] => (Token::Larrow, 2),
            [b'-', b'>', ..] => (Token::Arrow, 2),
            [b'=', b'>', ..] => (Token::Darrow, 2),
            [b'+', b'+', ..] => (Token::Plusplus, 2),
            [b'-', b'-', ..] => (Token::Minusminus, 2),
            [b':', b':', ..] => (Token::Dcolon, 2),
            [b'_', b'_', ..] => (Token::Underunder, 2),
            [b'|', b'>', ..] => (Token::Fwdapp, 2),
            [b'<', b'|', ..] => (Token::Revapp, 2),
            [b'<', b'=', ..] => (Token::Le, 2),
            [b'>', b'=', ..] => (Token::Ge, 2),
            _ => return None,
        };
        self.pos += len;
        Some(tok)
    }

    fn scan_number(&mut self, start: usize) -> LexResult {
        let neg = self.src[self.pos] == b'-';
        if neg {
            self.pos += 1;
        }
        let int_cap = self.src.len().saturating_sub(self.pos).saturating_add(1);
        for _ in 0..int_cap {
            if self.pos >= self.src.len() || !self.src[self.pos].is_ascii_digit() {
                break;
            }
            self.pos += 1;
        }
        // Float?
        if self.pos < self.src.len() && self.src[self.pos] == b'.' {
            let after_dot = self.pos + 1;
            if after_dot < self.src.len() && self.src[after_dot].is_ascii_digit() {
                self.pos += 1;
                let frac_cap = self.src.len().saturating_sub(self.pos).saturating_add(1);
                for _ in 0..frac_cap {
                    if self.pos >= self.src.len() || !self.src[self.pos].is_ascii_digit() {
                        break;
                    }
                    self.pos += 1;
                }
                let s = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("0");
                let v: f64 = s.parse().unwrap_or(0.0);
                return Ok((start, Token::Float(v), self.pos));
            }
        }
        let s = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("0");
        let v: i64 = s.parse().unwrap_or(0);
        Ok((start, Token::Int(v), self.pos))
    }

    fn scan_ident(&mut self, start: usize) -> LexResult {
        let ident_cap = self.src.len().saturating_sub(self.pos).saturating_add(1);
        for _ in 0..ident_cap {
            if self.pos >= self.src.len() {
                break;
            }
            let b = self.src[self.pos];
            if b.is_ascii_alphanumeric() || b == b'_' || b == b'\'' {
                self.pos += 1;
            } else {
                break;
            }
        }
        let word = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("_");
        // `_` (exactly) has special handling: WildAnnot when immediately followed by `::` (not `:::`),
        // Under when not followed by `::`. This ensures wildcard patterns and wildcard type-constructor
        // references both get the right token so grammar rules like `"_" => Con::Wild(...)` fire.
        if word == "_" {
            let mut peek = self.pos;
            let ws_cap = self.src.len().saturating_sub(peek).saturating_add(1);
            for _ in 0..ws_cap {
                if peek >= self.src.len() {
                    break;
                }
                if !matches!(self.src[peek], b' ' | b'\t' | b'\r' | b'\n') {
                    break;
                }
                peek += 1;
            }
            if peek + 1 < self.src.len()
                && self.src[peek] == b':'
                && self.src[peek + 1] == b':'
                && self.src.get(peek + 2).copied() != Some(b':')
            {
                // Consume the `::` and emit a WildAnnot token for `[_ :: K]` patterns.
                self.pos = peek + 2;
                return Ok((start, Token::WildAnnot, self.pos));
            }
            // No `::` follows: emit Under so grammar rules for wildcard (`Con::Wild`, `Pat::Var("_")`)
            // fire rather than treating `_` as an unbound identifier.
            return Ok((start, Token::Under, self.pos));
        }
        let tok = match word {
            "and" => Token::And,
            "andalso" => Token::Andalso,
            "case" => Token::Case,
            "class" => Token::Class,
            "con" => Token::Con,
            "constraint" => Token::Constraint,
            "constraints" => Token::Constraints,
            "cookie" => Token::Cookie,
            "datatype" => Token::Datatype,
            "else" => Token::Else,
            "end" => Token::End,
            "export" => Token::Export,
            "false" => Token::False,
            "ffi" => Token::Ffi,
            "fn" => Token::Fn,
            "fun" => Token::Fun,
            "functor" => Token::Functor,
            "if" => Token::If,
            "in" => Token::In,
            "include" => Token::Include,
            "let" => Token::Let,
            "map" => Token::Map,
            "of" => Token::Of,
            "open" => Token::Open,
            "orelse" => Token::Orelse,
            "policy" => Token::Policy,
            "rec" => Token::Rec,
            "sequence" => Token::Sequence,
            "sig" => Token::Sig,
            "signature" => Token::Signature,
            "struct" => Token::Struct,
            "structure" => Token::Structure,
            "style" => Token::Style,
            "table" => Token::Table,
            "task" => Token::Task,
            "then" => Token::Then,
            "true" => Token::True,
            "type" => Token::Type,
            "val" => Token::Val,
            "view" => Token::View,
            "urweb_put" => Token::UrwebPut,
            "urweb_get" => Token::UrwebGet,
            "urweb_tb_transfer" => Token::UrwebTbTransfer,
            "sgn_abs" => Token::SgnAbs,
            "sgn_def_con" => Token::SgnDefCon,
            "case_bar" => Token::CaseBar,
            "arm_sep" => Token::ArmSep,
            "case_end" => Token::CaseEnd,
            "dtype_of" => Token::DtypeOf,
            "dt_con0" => Token::DtCon0,
            "dt_bar" => Token::DtBar,
            "dt_done" => Token::DtDone,
            "sgn_where" => Token::Where,
            "sgn_subwhere" => Token::SgnSubwhere,
            "AND" => Token::AndUpper,
            "AS" => Token::As,
            "COUNT" => Token::Count,
            "CURRENT_TIMESTAMP" => Token::CurrentTimestamp,
            "DELETE" => Token::Delete,
            "FROM" => Token::From,
            "INSERT" => Token::Insert,
            "INTO" => Token::Into,
            "IS" => Token::Is,
            "JOIN" => Token::Join,
            "LEFT" => Token::Left,
            "NULL" => Token::Null,
            "ON" => Token::On,
            "OR" => Token::OrUpper,
            "SET" => Token::Set,
            "SELECT" => Token::Select,
            "SQL" => Token::Sql,
            "sql_star" => Token::SqlStar,
            "UPDATE" => Token::Update,
            "VALUES" => Token::Values,
            "WHERE" => Token::Cwhere,
            "Name" => Token::Name,
            "Type" => Token::KindType,
            "Unit" => Token::KindUnit,
            w if w.chars().next().is_some_and(|c| c.is_uppercase()) => {
                Token::UpperIdent(w.to_string())
            }
            w => Token::Ident(w.to_string()),
        };
        Ok((start, tok, self.pos))
    }

    /// Pull the next token while lexing an XML literal region (not tag attributes).
    fn next_xml(&mut self) -> Option<LexResult> {
        let stride_limit = self.src.len().saturating_add(1);
        'xml: for _ in 0..stride_limit {
            if self.pos >= self.src.len() {
                return None;
            }
            let start = self.pos;

            // ML comment `(*...*)` — skip
            if self.pos + 1 < self.src.len()
                && self.src[self.pos] == b'('
                && self.src[self.pos + 1] == b'*'
            {
                self.pos += 2;
                self.skip_ml_comment();
                continue 'xml;
            }

            // XML comment `<!--...-->` — skip
            if self.pos + 3 < self.src.len() && &self.src[self.pos..self.pos + 4] == b"<!--" {
                self.pos += 4;
                self.skip_xml_comment();
                continue 'xml;
            }

            let current_byte = self.src[self.pos];

            match current_byte {
                b'\n' => {
                    self.pos += 1;
                    return Some(Ok((start, Token::Notags("\n".to_string()), self.pos)));
                }
                b'<' => {
                    // `</id>` end tag vs `<id` begin tag vs bare `<`
                    if self.at(1) == Some(b'/') {
                        let id_start = self.pos + 2;
                        let id_end = self.scan_xml_id(id_start);
                        if id_end > id_start && self.at(id_end - self.pos) == Some(b'>') {
                            let name = std::str::from_utf8(&self.src[id_start..id_end])
                                .unwrap_or("")
                                .to_string();
                            self.pos = id_end + 1;
                            if name == "xml" {
                                if self.xml_nesting > 0 {
                                    self.xml_nesting -= 1;
                                } else {
                                    self.mode = LexMode::Regular;
                                }
                            }
                            return Some(Ok((start, Token::EndTag(name), self.pos)));
                        }
                    }
                    let id_start = self.pos + 1;
                    let id_end = self.scan_xml_id(id_start);
                    if id_end > id_start {
                        let name = std::str::from_utf8(&self.src[id_start..id_end])
                            .unwrap_or("")
                            .to_string();
                        self.pos = id_end;
                        self.mode = LexMode::XmlTag;
                        if name == "xml" {
                            self.pending_xml_open = true;
                        }
                        return Some(Ok((start, Token::BeginTag(name), self.pos)));
                    }
                    self.pos += 1;
                    return Some(Ok((start, Token::Notags("<".to_string()), self.pos)));
                }
                b'{' => {
                    self.pos += 1;
                    self.brace_stack.push((LexMode::Xml, 1));
                    self.mode = LexMode::Regular;
                    return Some(Ok((start, Token::Lbrace, self.pos)));
                }
                b'(' => {
                    self.pos += 1;
                    return Some(Ok((start, Token::Notags("(".to_string()), self.pos)));
                }
                _ => {
                    let text_start = self.pos;
                    let text_cap = self.src.len().saturating_sub(self.pos).saturating_add(1);
                    for _ in 0..text_cap {
                        if self.pos >= self.src.len() {
                            break;
                        }
                        let c = self.src[self.pos];
                        if c == b'<' || c == b'{' || c == b'\n' || c == b'(' {
                            break;
                        }
                        self.pos += 1;
                    }
                    if self.pos > text_start {
                        let text = std::str::from_utf8(&self.src[text_start..self.pos])
                            .unwrap_or("")
                            .to_string();
                        return Some(Ok((text_start, Token::Notags(text), self.pos)));
                    }
                    self.pos += 1;
                    return Some(Err(LexError::new(format!(
                        "Illegal XML character '{}' at offset {}",
                        current_byte as char, start
                    ))));
                }
            }
        }
        Some(Err(LexError::new(
            "XmlAwareLexer: exceeded per-token scan budget in Xml mode",
        )))
    }

    fn next_xmltag(&mut self) -> Option<LexResult> {
        let stride_limit = self.src.len().saturating_add(1);
        'xmltag: for _ in 0..stride_limit {
            if self.pos >= self.src.len() {
                return None;
            }
            let start = self.pos;
            let b = self.src[self.pos];

            // Skip whitespace
            if b == b' ' || b == b'\t' || b == b'\r' || b == b'\n' {
                self.pos += 1;
                continue 'xmltag;
            }

            // ML comment
            if b == b'(' && self.at(1) == Some(b'*') {
                self.pos += 2;
                self.skip_ml_comment();
                continue 'xmltag;
            }

            // `>` → Gt, switch back to Xml mode
            if b == b'>' {
                self.pos += 1;
                self.mode = LexMode::Xml;
                // If this `>` closes a `<xml ...>` tag, increment nesting depth
                if self.pending_xml_open {
                    self.xml_nesting += 1;
                    self.pending_xml_open = false;
                }
                return Some(Ok((start, Token::Gt, self.pos)));
            }

            // `/` → Divide (used for `/>` self-closing); clears pending_xml_open
            if b == b'/' {
                self.pos += 1;
                // Self-closing <xml/>: don't increment nesting
                self.pending_xml_open = false;
                return Some(Ok((start, Token::Divide, self.pos)));
            }

            // String literal → produce String token, return to XmlTag after
            if b == b'"' || b == b'\'' {
                self.pos += 1;
                self.string_return = Some(LexMode::XmlTag);
                return Some(self.scan_regular_string(b, start));
            }

            // `{` → push XmlTag return, switch to Regular
            if b == b'{' {
                self.pos += 1;
                self.brace_stack.push((LexMode::XmlTag, 1));
                self.mode = LexMode::Regular;
                return Some(Ok((start, Token::Lbrace, self.pos)));
            }

            // `(` → push XmlTag return, switch to Regular
            if b == b'(' {
                if self.at(1) == Some(b')') {
                    // `()` — unit
                    self.pos += 2;
                    self.brace_stack.push((LexMode::XmlTag, 1));
                    self.mode = LexMode::Regular;
                    return Some(Ok((start, Token::Unit, self.pos)));
                }
                self.pos += 1;
                self.brace_stack.push((LexMode::XmlTag, 1));
                self.mode = LexMode::Regular;
                return Some(Ok((start, Token::Lparen, self.pos)));
            }

            // `=` → Eq
            if b == b'=' {
                self.pos += 1;
                return Some(Ok((start, Token::Eq, self.pos)));
            }

            // Integer or float
            if b.is_ascii_digit() {
                return Some(self.scan_number(start));
            }

            // xmlid → Eq/bare-disjoint attribute name tokens (no optional `=` in the CFG).
            if b.is_ascii_alphabetic() || b == b'_' {
                let end = self.scan_xml_id(start);
                self.pos = end;
                let name = std::str::from_utf8(&self.src[start..end])
                    .unwrap_or("")
                    .to_string();
                let mut p = self.pos;
                let attr_ws_cap = self.src.len().saturating_sub(p).saturating_add(1);
                for _ in 0..attr_ws_cap {
                    if p >= self.src.len() {
                        break;
                    }
                    let bb = self.src[p];
                    if bb == b' ' || bb == b'\t' || bb == b'\r' || bb == b'\n' {
                        p += 1;
                    } else {
                        break;
                    }
                }
                let tok = if p < self.src.len() && self.src[p] == b'=' {
                    Token::XmlAttrNameEq(name)
                } else {
                    Token::XmlAttrNameBare(name)
                };
                return Some(Ok((start, tok, self.pos)));
            }

            // Other characters
            self.pos += 1;
            return Some(Err(LexError::new(format!(
                "Illegal XML tag character '{}' at offset {}",
                b as char, start
            ))));
        }
        Some(Err(LexError::new(
            "XmlAwareLexer: exceeded per-token scan budget in XmlTag mode",
        )))
    }
}

impl<'a> Iterator for XmlAwareLexer<'a> {
    type Item = LexResult;

    fn next(&mut self) -> Option<Self::Item> {
        // Drain any pending tokens first
        if let Some(tok) = self.pending.pop_front() {
            return Some(Ok(tok));
        }
        let result = match self.mode.clone() {
            LexMode::Regular => self.next_regular()?,
            LexMode::Xml => self.next_xml()?,
            LexMode::XmlTag => self.next_xmltag()?,
        };
        Some(result)
    }
}

/// Production token stream for LangSec spine tests: [`XmlAwareLexer`], whitespace/comments stripped.
/// Returns the first [`LexError`] if lexical analysis fails.
pub fn tokenize_xml_aware(src: &str) -> Result<Vec<(usize, Token, usize)>, LexError> {
    let mut out = Vec::new();
    for item in XmlAwareLexer::new(src) {
        match item {
            Ok((lo, tok, hi)) => {
                if matches!(tok, Token::Whitespace | Token::Comment) {
                    continue;
                }
                out.push((lo, tok, hi));
            }
            Err(e) => return Err(e),
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Context as _; // .with_context() on Result in tests
    use anyhow::Context as _;

    fn lex_all(input: &str) -> Vec<Token> {
        Token::lexer(input)
            .filter_map(|r| r.ok())
            .filter(|t| *t != Token::Whitespace && *t != Token::Comment)
            .collect()
    }

    #[test]
    fn token_display_uses_friendly_phrases_not_token_enum_debug() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let keyword = format!("{}", Token::Fun);
        assert!(
            keyword.contains('`') && keyword.contains("fun"),
            "expected backticked keyword: {keyword}"
        );
        assert!(
            !keyword.contains("Token::"),
            "Display must not look like Debug: {keyword}"
        );
        let id = format!("{}", Token::Ident("counter".into()));
        assert!(id.contains("counter"), "{id}");
        Ok(()) // return success to the test harness
    }

    #[test]
    fn xml_aware_lexer_fuses_at_inference_paths() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = tokenize_xml_aware("@@x @y @Foo.bar").with_context(|| "lex")?;
        assert_eq!(toks.len(), 3);
        assert_eq!(toks[0].1, Token::AtDontInferPath("x".into()));
        assert_eq!(toks[1].1, Token::AtTypesOnlyPath("y".into()));
        assert_eq!(toks[2].1, Token::AtTypesOnlyPath("Foo.bar".into()));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn xml_aware_lexer_at_before_keyword_does_not_fuse() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = tokenize_xml_aware("@fn @ x").with_context(|| "lex")?;
        assert!(
            matches!(&toks[0].1, Token::At),
            "expected bare `@` before keyword `fn`, got {:?}",
            toks[0].1
        );
        assert_eq!(toks[1].1, Token::Fn);
        assert_eq!(toks[2].1, Token::At);
        assert_eq!(toks[3].1, Token::Ident("x".into()));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn keywords() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("fun val rec let in end");
        assert_eq!(toks[0], Token::Fun);
        assert_eq!(toks[1], Token::Val);
        assert_eq!(toks[2], Token::Rec);
        assert_eq!(toks[3], Token::Let);
        assert_eq!(toks[4], Token::In);
        assert_eq!(toks[5], Token::End);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn integer_literal() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("42");
        assert_eq!(toks[0], Token::Int(42));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn negative_integer() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("-7");
        assert_eq!(toks[0], Token::Int(-7));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn float_literal() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("1.375");
        match &toks[0] {
            Token::Float(f) => assert!((f - 1.375).abs() < 1e-10),
            other => panic!("expected Float, got {:?}", other),
        }
        Ok(()) // return success to the test harness
    }

    #[test]
    fn string_literal() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all(r#""hello""#);
        assert_eq!(toks[0], Token::String("hello".into()));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn operators_multi() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("-> => ++ --");
        assert_eq!(toks[0], Token::Arrow);
        assert_eq!(toks[1], Token::Darrow);
        assert_eq!(toks[2], Token::Plusplus);
        assert_eq!(toks[3], Token::Minusminus);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn three_char_ops() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("--- :::");
        assert_eq!(toks[0], Token::Minusminusminus);
        assert_eq!(toks[1], Token::Tcolonwild);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn identifiers() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("Foo bar");
        assert_eq!(toks[0], Token::UpperIdent("Foo".into()));
        assert_eq!(toks[1], Token::Ident("bar".into()));
        Ok(()) // return success to the test harness
    }

    #[test]
    fn unit_token() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("()");
        assert_eq!(toks[0], Token::Unit);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn paren_open_close() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("( x )");
        assert_eq!(toks[0], Token::Lparen);
        assert_eq!(toks[1], Token::Ident("x".into()));
        assert_eq!(toks[2], Token::Rparen);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn keyword_not_ident() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        // "fun" should be Fun, not Ident
        let toks = lex_all("fun");
        assert_eq!(toks.len(), 1);
        assert_eq!(toks[0], Token::Fun);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn dotdotdot() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("...");
        assert_eq!(toks[0], Token::Dotdotdot);
        Ok(()) // return success to the test harness
    }

    #[test]
    fn backtick_path() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let toks = lex_all("`Basis.alert`");
        assert_eq!(toks[0], Token::BacktickPath("Basis.alert".into()));
        Ok(()) // return success to the test harness
    }

    /// Catches Lexer::next mutant (return None) - Lexer iterator must yield tokens.
    #[test]
    fn lexer_iterator_yields_tokens() -> anyhow::Result<()> {
        // test returns Result to allow ? propagation
        let mut lexer = Lexer::new("val x = 1");
        let first = lexer.next();
        assert!(
            first.is_some(),
            "Lexer::next must return Some for valid input"
        );
        let rest: Vec<_> = lexer.collect();
        assert!(!rest.is_empty(), "Lexer must yield multiple tokens");
        Ok(()) // return success to the test harness
    }
}
