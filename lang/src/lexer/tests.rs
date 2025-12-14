use expect_test::{expect, Expect};

use super::*;
use token::{Token, TokenKind};

fn check_tokens(input: &str, expect: Expect) {
    let tokens = lex(input);
    let tokens_str = format!("{:#?}", tokens);
    expect.assert_eq(&tokens_str);
}

#[test]
fn lex_integer_literals() {
    check_tokens(
        "42",
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: Integer(
                            42,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 3,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 3,
                            },
                            end: Position {
                                line: 1,
                                column: 3,
                            },
                        },
                    },
                ],
            )"#]],
    );

    check_tokens(
        "-17",
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: Integer(
                            -17,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 4,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 4,
                            },
                            end: Position {
                                line: 1,
                                column: 4,
                            },
                        },
                    },
                ],
            )"#]],
    );

    check_tokens(
        "1_000_000",
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: Integer(
                            1000000,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 10,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 10,
                            },
                            end: Position {
                                line: 1,
                                column: 10,
                            },
                        },
                    },
                ],
            )"#]],
    );
}

#[test]
fn lex_multiple_integers() {
    check_tokens(
        "1 2 3",
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: Integer(
                            1,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 2,
                            },
                        },
                    },
                    Token {
                        kind: Integer(
                            2,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 3,
                            },
                            end: Position {
                                line: 1,
                                column: 4,
                            },
                        },
                    },
                    Token {
                        kind: Integer(
                            3,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 5,
                            },
                            end: Position {
                                line: 1,
                                column: 6,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 6,
                            },
                            end: Position {
                                line: 1,
                                column: 6,
                            },
                        },
                    },
                ],
            )"#]],
    );
}

#[test]
fn lex_decimal_literals() {
    check_tokens(
        "3.14",
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: Decimal(
                            3.14,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 5,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 5,
                            },
                            end: Position {
                                line: 1,
                                column: 5,
                            },
                        },
                    },
                ],
            )"#]],
    );

    check_tokens(
        "-0.5",
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: Decimal(
                            -0.5,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 5,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 5,
                            },
                            end: Position {
                                line: 1,
                                column: 5,
                            },
                        },
                    },
                ],
            )"#]],
    );

    check_tokens(
        "1_000.50",
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: Decimal(
                            1000.5,
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 9,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 9,
                            },
                            end: Position {
                                line: 1,
                                column: 9,
                            },
                        },
                    },
                ],
            )"#]],
    );
}

#[test]
fn lex_string_with_escapes() {
    check_tokens(
        r#""hello""#,
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: String(
                            "hello",
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 8,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 8,
                            },
                            end: Position {
                                line: 1,
                                column: 8,
                            },
                        },
                    },
                ],
            )"#]],
    );

    check_tokens(
        r#""Line 1\nLine 2""#,
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: String(
                            "Line 1\nLine 2",
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 17,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 17,
                            },
                            end: Position {
                                line: 1,
                                column: 17,
                            },
                        },
                    },
                ],
            )"#]],
    );

    check_tokens(
        r#""Tab\tseparated""#,
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: String(
                            "Tab\tseparated",
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 17,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 17,
                            },
                            end: Position {
                                line: 1,
                                column: 17,
                            },
                        },
                    },
                ],
            )"#]],
    );

    check_tokens(
        r#""Quote: \"text\"""#,
        expect![[r#"
            Ok(
                [
                    Token {
                        kind: String(
                            "Quote: \"text\"",
                        ),
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 1,
                            },
                            end: Position {
                                line: 1,
                                column: 18,
                            },
                        },
                    },
                    Token {
                        kind: Eof,
                        span: Span {
                            start: Position {
                                line: 1,
                                column: 18,
                            },
                            end: Position {
                                line: 1,
                                column: 18,
                            },
                        },
                    },
                ],
            )"#]],
    );
}

#[test]
fn lex_operators() {
    check_tokens("+ - * / %", expect![[r#"
        Ok(
            [
                Token {
                    kind: Plus,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 2,
                        },
                    },
                },
                Token {
                    kind: Minus,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 3,
                        },
                        end: Position {
                            line: 1,
                            column: 4,
                        },
                    },
                },
                Token {
                    kind: Star,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 5,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: Slash,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 7,
                        },
                        end: Position {
                            line: 1,
                            column: 8,
                        },
                    },
                },
                Token {
                    kind: Percent,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 9,
                        },
                        end: Position {
                            line: 1,
                            column: 10,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 10,
                        },
                        end: Position {
                            line: 1,
                            column: 10,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("== != < <= > >=", expect![[r#"
        Ok(
            [
                Token {
                    kind: EqualEqual,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 3,
                        },
                    },
                },
                Token {
                    kind: NotEqual,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 4,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: Less,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 7,
                        },
                        end: Position {
                            line: 1,
                            column: 8,
                        },
                    },
                },
                Token {
                    kind: LessEqual,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 9,
                        },
                        end: Position {
                            line: 1,
                            column: 11,
                        },
                    },
                },
                Token {
                    kind: Greater,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 12,
                        },
                        end: Position {
                            line: 1,
                            column: 13,
                        },
                    },
                },
                Token {
                    kind: GreaterEqual,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 14,
                        },
                        end: Position {
                            line: 1,
                            column: 16,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 16,
                        },
                        end: Position {
                            line: 1,
                            column: 16,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("&& || !", expect![[r#"
        Ok(
            [
                Token {
                    kind: AndAnd,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 3,
                        },
                    },
                },
                Token {
                    kind: OrOr,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 4,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: Bang,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 7,
                        },
                        end: Position {
                            line: 1,
                            column: 8,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 8,
                        },
                        end: Position {
                            line: 1,
                            column: 8,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("|> >> .. ..=", expect![[r#"
        Ok(
            [
                Token {
                    kind: Pipe,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 3,
                        },
                    },
                },
                Token {
                    kind: RightRight,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 4,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: DotDot,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 7,
                        },
                        end: Position {
                            line: 1,
                            column: 9,
                        },
                    },
                },
                Token {
                    kind: DotDotEqual,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 10,
                        },
                        end: Position {
                            line: 1,
                            column: 13,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 13,
                        },
                        end: Position {
                            line: 1,
                            column: 13,
                        },
                    },
                },
            ],
        )"#]]);
}

#[test]
fn lex_keywords_vs_identifiers() {
    check_tokens("let mut if else", expect![[r#"
        Ok(
            [
                Token {
                    kind: Let,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 4,
                        },
                    },
                },
                Token {
                    kind: Mut,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 5,
                        },
                        end: Position {
                            line: 1,
                            column: 8,
                        },
                    },
                },
                Token {
                    kind: If,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 9,
                        },
                        end: Position {
                            line: 1,
                            column: 11,
                        },
                    },
                },
                Token {
                    kind: Else,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 12,
                        },
                        end: Position {
                            line: 1,
                            column: 16,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 16,
                        },
                        end: Position {
                            line: 1,
                            column: 16,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("match return break", expect![[r#"
        Ok(
            [
                Token {
                    kind: Match,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: Return,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 7,
                        },
                        end: Position {
                            line: 1,
                            column: 13,
                        },
                    },
                },
                Token {
                    kind: Break,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 14,
                        },
                        end: Position {
                            line: 1,
                            column: 19,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 19,
                        },
                        end: Position {
                            line: 1,
                            column: 19,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("nil true false", expect![[r#"
        Ok(
            [
                Token {
                    kind: Nil,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 4,
                        },
                    },
                },
                Token {
                    kind: True,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 5,
                        },
                        end: Position {
                            line: 1,
                            column: 9,
                        },
                    },
                },
                Token {
                    kind: False,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 10,
                        },
                        end: Position {
                            line: 1,
                            column: 15,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 15,
                        },
                        end: Position {
                            line: 1,
                            column: 15,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("x counter is_valid?", expect![[r#"
        Ok(
            [
                Token {
                    kind: Identifier(
                        "x",
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 2,
                        },
                    },
                },
                Token {
                    kind: Identifier(
                        "counter",
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 3,
                        },
                        end: Position {
                            line: 1,
                            column: 10,
                        },
                    },
                },
                Token {
                    kind: Identifier(
                        "is_valid?",
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 11,
                        },
                        end: Position {
                            line: 1,
                            column: 20,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 20,
                        },
                        end: Position {
                            line: 1,
                            column: 20,
                        },
                    },
                },
            ],
        )"#]]);
}

#[test]
fn lex_comments() {
    check_tokens("42 // this is a comment", expect![[r#"
        Ok(
            [
                Token {
                    kind: Integer(
                        42,
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 3,
                        },
                    },
                },
                Token {
                    kind: Comment(
                        " this is a comment",
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 4,
                        },
                        end: Position {
                            line: 1,
                            column: 24,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 24,
                        },
                        end: Position {
                            line: 1,
                            column: 24,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("// full line comment\n42", expect![[r#"
        Ok(
            [
                Token {
                    kind: Comment(
                        " full line comment",
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 21,
                        },
                    },
                },
                Token {
                    kind: Integer(
                        42,
                    ),
                    span: Span {
                        start: Position {
                            line: 2,
                            column: 1,
                        },
                        end: Position {
                            line: 2,
                            column: 3,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 2,
                            column: 3,
                        },
                        end: Position {
                            line: 2,
                            column: 3,
                        },
                    },
                },
            ],
        )"#]]);
}

#[test]
fn lex_delimiters() {
    check_tokens("( ) [ ] { } #{", expect![[r#"
        Ok(
            [
                Token {
                    kind: LeftParen,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 2,
                        },
                    },
                },
                Token {
                    kind: RightParen,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 3,
                        },
                        end: Position {
                            line: 1,
                            column: 4,
                        },
                    },
                },
                Token {
                    kind: LeftBracket,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 5,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: RightBracket,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 7,
                        },
                        end: Position {
                            line: 1,
                            column: 8,
                        },
                    },
                },
                Token {
                    kind: LeftBrace,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 9,
                        },
                        end: Position {
                            line: 1,
                            column: 10,
                        },
                    },
                },
                Token {
                    kind: RightBrace,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 11,
                        },
                        end: Position {
                            line: 1,
                            column: 12,
                        },
                    },
                },
                Token {
                    kind: HashBrace,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 13,
                        },
                        end: Position {
                            line: 1,
                            column: 15,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 15,
                        },
                        end: Position {
                            line: 1,
                            column: 15,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens(", : ; | `", expect![[r#"
        Ok(
            [
                Token {
                    kind: Comma,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 2,
                        },
                    },
                },
                Token {
                    kind: Colon,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 3,
                        },
                        end: Position {
                            line: 1,
                            column: 4,
                        },
                    },
                },
                Token {
                    kind: Semicolon,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 5,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: VerticalBar,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 7,
                        },
                        end: Position {
                            line: 1,
                            column: 8,
                        },
                    },
                },
                Token {
                    kind: Backtick,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 9,
                        },
                        end: Position {
                            line: 1,
                            column: 10,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 10,
                        },
                        end: Position {
                            line: 1,
                            column: 10,
                        },
                    },
                },
            ],
        )"#]]);
}

#[test]
fn lex_range_operators() {
    check_tokens("1..5", expect![[r#"
        Ok(
            [
                Token {
                    kind: Integer(
                        1,
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 2,
                        },
                    },
                },
                Token {
                    kind: DotDot,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 2,
                        },
                        end: Position {
                            line: 1,
                            column: 4,
                        },
                    },
                },
                Token {
                    kind: Integer(
                        5,
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 4,
                        },
                        end: Position {
                            line: 1,
                            column: 5,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 5,
                        },
                        end: Position {
                            line: 1,
                            column: 5,
                        },
                    },
                },
            ],
        )"#]]);
    check_tokens("1..=5", expect![[r#"
        Ok(
            [
                Token {
                    kind: Integer(
                        1,
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 1,
                        },
                        end: Position {
                            line: 1,
                            column: 2,
                        },
                    },
                },
                Token {
                    kind: DotDotEqual,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 2,
                        },
                        end: Position {
                            line: 1,
                            column: 5,
                        },
                    },
                },
                Token {
                    kind: Integer(
                        5,
                    ),
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 5,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
                Token {
                    kind: Eof,
                    span: Span {
                        start: Position {
                            line: 1,
                            column: 6,
                        },
                        end: Position {
                            line: 1,
                            column: 6,
                        },
                    },
                },
            ],
        )"#]]);
}
