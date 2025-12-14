/// Abstract Syntax Tree node types for santa-lang expressions
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // Literals
    Integer(i64),
    Decimal(f64),
    String(String),
    Boolean(bool),
    Nil,

    // Collections
    List(Vec<Expr>),
    Set(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    Range {
        start: Box<Expr>,
        end: Option<Box<Expr>>,
        inclusive: bool,
    },

    // Identifiers & Placeholders
    Identifier(String),
    Placeholder,
    RestIdentifier(String),

    // Operations
    Prefix {
        op: PrefixOp,
        right: Box<Expr>,
    },
    Infix {
        left: Box<Expr>,
        op: InfixOp,
        right: Box<Expr>,
    },
    Index {
        collection: Box<Expr>,
        index: Box<Expr>,
    },

    // Functions
    Function {
        params: Vec<Param>,
        body: Box<Expr>,
    },
    Call {
        function: Box<Expr>,
        args: Vec<Expr>,
    },
    InfixCall {
        function: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    // Control Flow
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    IfLet {
        pattern: Pattern,
        value: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },
    Match {
        subject: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Block(Vec<Stmt>),

    // Spread
    Spread(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PrefixOp {
    Not,     // !
    Negate,  // -
}

#[derive(Debug, Clone, PartialEq)]
pub enum InfixOp {
    // Arithmetic
    Add,      // +
    Subtract, // -
    Multiply, // *
    Divide,   // /
    Modulo,   // %

    // Comparison
    Equal,              // ==
    NotEqual,           // !=
    LessThan,           // <
    LessThanOrEqual,    // <=
    GreaterThan,        // >
    GreaterThanOrEqual, // >=

    // Logical
    And, // &&
    Or,  // ||

    // Special
    Pipeline,    // |>
    Composition, // >>
    Range,       // ..
    RangeInclusive, // ..=
    InfixCall,   // ` (backtick for infix function calls)
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    Wildcard,                // _
    Identifier(String),      // x
    RestIdentifier(String),  // ..rest
    Literal(Literal),        // 42, "hello", true
    List(Vec<Pattern>),      // [a, b, ..rest]
    Range {
        start: i64,
        end: Option<i64>,
        inclusive: bool,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Integer(i64),
    Decimal(f64),
    String(String),
    Boolean(bool),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let {
        mutable: bool,
        pattern: Pattern,
        value: Expr,
    },
    Return(Expr),
    Break(Expr),
    Expr(Expr),
}
