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

/// Process SML/Ur string escape sequences: `\n`, `\t`, `\r`, `\\`, `\"`, `\^X`, `\ddd`, `\uXXXX`.
fn process_string_escapes(s: &str) -> Option<String> {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
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
                            digits.push(chars.next().unwrap());
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
                // SML whitespace gap: skip to matching backslash
                while let Some(&c2) = chars.peek() {
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
    Some(out)
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
    // Compound token: `_` followed by `::` (with optional whitespace).
    // Emitted by XmlAwareLexer to avoid LALR state-merge ambiguity.
    // -----------------------------------------------------------------------
    WildAnnot,

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

    fn peek(&self) -> Option<u8> {
        self.src.get(self.pos).copied()
    }

    fn peek2(&self) -> Option<u8> {
        self.src.get(self.pos + 1).copied()
    }

    fn at(&self, offset: usize) -> Option<u8> {
        self.src.get(self.pos + offset).copied()
    }

    fn advance(&mut self) -> u8 {
        let b = self.src[self.pos];
        self.pos += 1;
        b
    }

    fn skip_ml_comment(&mut self) {
        // Already consumed `(*`; consume until matching `*)`, supporting nesting.
        let mut depth = 1usize;
        while self.pos < self.src.len() {
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
    }

    fn skip_xml_comment(&mut self) {
        // Already consumed `<!--`; consume until `-->`.
        while self.pos + 2 < self.src.len() {
            if &self.src[self.pos..self.pos + 3] == b"-->" {
                self.pos += 3;
                return;
            }
            self.pos += 1;
        }
        self.pos = self.src.len();
    }

    fn scan_xml_id(&self, start: usize) -> usize {
        // xmlid = [A-Za-z][A-Za-z0-9_-]*
        let mut p = start;
        if p < self.src.len() && self.src[p].is_ascii_alphabetic() {
            p += 1;
            while p < self.src.len() {
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
        loop {
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
    }

    fn next_regular(&mut self) -> Option<LexResult> {
        loop {
            if self.pos >= self.src.len() {
                return None;
            }
            let start = self.pos;
            let b = self.src[self.pos];

            // Skip whitespace
            if b == b' ' || b == b'\t' || b == b'\r' || b == b'\n' {
                self.pos += 1;
                continue;
            }

            // ML comment `(*...*)` with nesting
            if b == b'(' && self.at(1) == Some(b'*') {
                self.pos += 2;
                self.skip_ml_comment();
                continue;
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
                        let name = std::str::from_utf8(&self.src[id_start..id_end])
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
            if b.is_ascii_digit() || (b == b'-' && self.at(1).map_or(false, |c| c.is_ascii_digit()))
            {
                return Some(self.scan_number(start));
            }

            // Identifiers and keywords
            if b.is_ascii_alphabetic() || b == b'_' {
                return Some(self.scan_ident(start));
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
                b'@' => Token::At,
                b'<' => Token::Lt,
                b'`' => {
                    // Backtick path
                    let path_start = self.pos;
                    while self.pos < self.src.len() && self.src[self.pos] != b'`' {
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
        let int_start = self.pos;
        while self.pos < self.src.len() && self.src[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        // Float?
        if self.pos < self.src.len() && self.src[self.pos] == b'.' {
            let after_dot = self.pos + 1;
            if after_dot < self.src.len() && self.src[after_dot].is_ascii_digit() {
                self.pos += 1;
                while self.pos < self.src.len() && self.src[self.pos].is_ascii_digit() {
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
        while self.pos < self.src.len() {
            let b = self.src[self.pos];
            if b.is_ascii_alphanumeric() || b == b'_' || b == b'\'' {
                self.pos += 1;
            } else {
                break;
            }
        }
        let word = std::str::from_utf8(&self.src[start..self.pos]).unwrap_or("_");
        // Emit WildAnnot when `_` (exactly) is immediately followed by `::` (not `:::`)
        if word == "_" {
            let mut peek = self.pos;
            while peek < self.src.len() && matches!(self.src[peek], b' ' | b'\t' | b'\r' | b'\n') {
                peek += 1;
            }
            if peek + 1 < self.src.len()
                && self.src[peek] == b':'
                && self.src[peek + 1] == b':'
                && self.src.get(peek + 2).copied() != Some(b':')
            {
                self.pos = peek + 2;
                return Ok((start, Token::WildAnnot, self.pos));
            }
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
            "where" => Token::Where,
            "Name" => Token::Name,
            "Type" => Token::KindType,
            "Unit" => Token::KindUnit,
            w if w.chars().next().map_or(false, |c| c.is_uppercase()) => {
                Token::UpperIdent(w.to_string())
            }
            w => Token::Ident(w.to_string()),
        };
        Ok((start, tok, self.pos))
    }

    fn next_xml(&mut self) -> Option<LexResult> {
        loop {
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
                continue;
            }

            // XML comment `<!--...-->` — skip
            if self.pos + 3 < self.src.len() && &self.src[self.pos..self.pos + 4] == b"<!--" {
                self.pos += 4;
                self.skip_xml_comment();
                continue;
            }

            let b = self.src[self.pos];

            // Newline → NOTAGS("\n")
            if b == b'\n' {
                self.pos += 1;
                return Some(Ok((start, Token::Notags("\n".to_string()), self.pos)));
            }

            // `</xmlid>` → EndTag
            if b == b'<' && self.at(1) == Some(b'/') {
                let id_start = self.pos + 2;
                let id_end = self.scan_xml_id(id_start);
                if id_end > id_start && self.at(id_end - self.pos) == Some(b'>') {
                    let name = std::str::from_utf8(&self.src[id_start..id_end])
                        .unwrap_or("")
                        .to_string();
                    self.pos = id_end + 1;
                    // If closing </xml> at depth 0, return to Regular mode
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

            // `<xmlid` → BeginTag, switch to XmlTag
            if b == b'<' {
                let id_start = self.pos + 1;
                let id_end = self.scan_xml_id(id_start);
                if id_end > id_start {
                    let name = std::str::from_utf8(&self.src[id_start..id_end])
                        .unwrap_or("")
                        .to_string();
                    self.pos = id_end;
                    self.mode = LexMode::XmlTag;
                    // Track nested <xml> tags so we know when </xml> exits to Regular
                    if name == "xml" {
                        self.pending_xml_open = true;
                    }
                    return Some(Ok((start, Token::BeginTag(name), self.pos)));
                }
                // bare `<` — treat as NOTAGS
                self.pos += 1;
                return Some(Ok((start, Token::Notags("<".to_string()), self.pos)));
            }

            // `{` → Lbrace, push XML return, switch to Regular
            if b == b'{' {
                self.pos += 1;
                self.brace_stack.push((LexMode::Xml, 1));
                self.mode = LexMode::Regular;
                return Some(Ok((start, Token::Lbrace, self.pos)));
            }

            // `(` — check if start of comment or just literal text
            if b == b'(' {
                self.pos += 1;
                return Some(Ok((start, Token::Notags("(".to_string()), self.pos)));
            }

            // Text content (everything except `<`, `{`, `\n`, `(`)
            let text_start = self.pos;
            while self.pos < self.src.len() {
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

            // Unexpected character
            self.pos += 1;
            return Some(Err(LexError::new(format!(
                "Illegal XML character '{}' at offset {}",
                b as char, start
            ))));
        }
    }

    fn next_xmltag(&mut self) -> Option<LexResult> {
        loop {
            if self.pos >= self.src.len() {
                return None;
            }
            let start = self.pos;
            let b = self.src[self.pos];

            // Skip whitespace
            if b == b' ' || b == b'\t' || b == b'\r' || b == b'\n' {
                self.pos += 1;
                continue;
            }

            // ML comment
            if b == b'(' && self.at(1) == Some(b'*') {
                self.pos += 2;
                self.skip_ml_comment();
                continue;
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

            // xmlid → Csymbol (attribute name)
            if b.is_ascii_alphabetic() || b == b'_' {
                let end = self.scan_xml_id(start);
                self.pos = end;
                let name = std::str::from_utf8(&self.src[start..end])
                    .unwrap_or("")
                    .to_string();
                return Some(Ok((start, Token::Csymbol(name), self.pos)));
            }

            // Other characters
            self.pos += 1;
            return Some(Err(LexError::new(format!(
                "Illegal XML tag character '{}' at offset {}",
                b as char, start
            ))));
        }
    }
}

impl<'a> Iterator for XmlAwareLexer<'a> {
    type Item = LexResult;

    fn next(&mut self) -> Option<Self::Item> {
        // Drain any pending tokens first
        if let Some(tok) = self.pending.pop_front() {
            return Some(Ok(tok));
        }
        loop {
            let result = match self.mode.clone() {
                LexMode::Regular => self.next_regular()?,
                LexMode::Xml => self.next_xml()?,
                LexMode::XmlTag => self.next_xmltag()?,
            };
            return Some(result);
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
