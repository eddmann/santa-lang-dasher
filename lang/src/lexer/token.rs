/// Position in source code (line and column, both 1-indexed)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    pub line: u32,
    pub column: u32,
}

impl Position {
    pub fn new(line: u32, column: u32) -> Self {
        Self { line, column }
    }
}

/// Span representing a range in source code
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

impl Span {
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }
}

/// Token type from LANG.txt Section 2
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Integer(i64),
    Decimal(f64),
    String(String),

    // Keywords
    Let,
    Mut,
    If,
    Else,
    Match,
    Return,
    Break,
    Nil,
    True,
    False,

    // Identifiers
    Identifier(String),

    // Operators
    Plus,           // +
    Minus,          // -
    Star,           // *
    Slash,          // /
    Percent,        // %
    EqualEqual,     // ==
    NotEqual,       // !=
    Less,           // <
    LessEqual,      // <=
    Greater,        // >
    GreaterEqual,   // >=
    AndAnd,         // &&
    OrOr,           // ||
    Bang,           // !
    Pipe,           // |>
    RightRight,     // >>
    DotDot,         // ..
    DotDotEqual,    // ..=
    Equal,          // =

    // Delimiters
    LeftParen,      // (
    RightParen,     // )
    LeftBracket,    // [
    RightBracket,   // ]
    LeftBrace,      // {
    RightBrace,     // }
    HashBrace,      // #{
    Comma,          // ,
    Colon,          // :
    Semicolon,      // ;
    VerticalBar,    // |
    Backtick,       // `

    // Special
    Underscore,     // _ (placeholder/wildcard)
    At,             // @ (attribute marker)

    // Comments (lexed but typically filtered during parsing)
    Comment(String),

    // End of input
    Eof,
}

/// Token with position information
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}
