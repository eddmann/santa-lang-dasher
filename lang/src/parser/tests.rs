use super::*;
use crate::lexer::lex;
use expect_test::expect;

fn parse_expr(source: &str) -> Result<Expr, ParseError> {
    let tokens = lex(source).unwrap();
    parse(tokens)
}

#[test]
fn parse_integer_literal() {
    let expr = parse_expr("42").unwrap();
    expect![[r#"
        Integer(
            42,
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_multiple_integer_literals() {
    // Individual integers should parse
    assert_eq!(parse_expr("0").unwrap(), Expr::Integer(0));
    assert_eq!(parse_expr("123").unwrap(), Expr::Integer(123));
    assert_eq!(parse_expr("1_000_000").unwrap(), Expr::Integer(1_000_000));
}

#[test]
fn parse_decimal_literal() {
    let expr = parse_expr("3.14").unwrap();
    expect![[r#"
        Decimal(
            3.14,
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_string_literal() {
    let expr = parse_expr(r#""hello""#).unwrap();
    expect![[r#"
        String(
            "hello",
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_boolean_literals() {
    assert_eq!(parse_expr("true").unwrap(), Expr::Boolean(true));
    assert_eq!(parse_expr("false").unwrap(), Expr::Boolean(false));
}

#[test]
fn parse_nil_literal() {
    let expr = parse_expr("nil").unwrap();
    expect![[r#"
        Nil
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_identifier() {
    let expr = parse_expr("my_var").unwrap();
    expect![[r#"
        Identifier(
            "my_var",
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_binary_add() {
    let expr = parse_expr("1 + 2").unwrap();
    expect![[r#"
        Infix {
            left: Integer(
                1,
            ),
            op: Add,
            right: Integer(
                2,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_binary_multiply() {
    let expr = parse_expr("3 * 4").unwrap();
    expect![[r#"
        Infix {
            left: Integer(
                3,
            ),
            op: Multiply,
            right: Integer(
                4,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_operator_precedence() {
    // Multiplication has higher precedence than addition
    let expr = parse_expr("1 + 2 * 3").unwrap();
    expect![[r#"
        Infix {
            left: Integer(
                1,
            ),
            op: Add,
            right: Infix {
                left: Integer(
                    2,
                ),
                op: Multiply,
                right: Integer(
                    3,
                ),
            },
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_comparison_operators() {
    let expr = parse_expr("1 < 2").unwrap();
    expect![[r#"
        Infix {
            left: Integer(
                1,
            ),
            op: LessThan,
            right: Integer(
                2,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_list_literal_empty() {
    let expr = parse_expr("[]").unwrap();
    expect![[r#"
        List(
            [],
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_list_literal_with_elements() {
    let expr = parse_expr("[1, 2, 3]").unwrap();
    expect![[r#"
        List(
            [
                Integer(
                    1,
                ),
                Integer(
                    2,
                ),
                Integer(
                    3,
                ),
            ],
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_prefix_negate() {
    // The lexer treats -5 as a negative integer literal, not prefix negation
    // To test prefix negation, use a variable or non-literal
    let expr = parse_expr("-x").unwrap();
    expect![[r#"
        Prefix {
            op: Negate,
            right: Identifier(
                "x",
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_negative_integer_literal() {
    // Negative integers are lexed as single tokens
    let expr = parse_expr("-5").unwrap();
    expect![[r#"
        Integer(
            -5,
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_prefix_not() {
    let expr = parse_expr("!true").unwrap();
    expect![[r#"
        Prefix {
            op: Not,
            right: Boolean(
                true,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_function_expression() {
    // Test simple lambda |x| x + 1
    let expr = parse_expr("|x| x + 1").unwrap();
    expect![[r#"
        Function {
            params: [
                Param {
                    name: "x",
                },
            ],
            body: Infix {
                left: Identifier(
                    "x",
                ),
                op: Add,
                right: Integer(
                    1,
                ),
            },
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_function_no_params() {
    // Test no-parameter lambda || 42
    let expr = parse_expr("|| 42").unwrap();
    expect![[r#"
        Function {
            params: [],
            body: Integer(
                42,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_function_multiple_params() {
    // Test multiple parameters |a, b| a + b
    let expr = parse_expr("|a, b| a + b").unwrap();
    expect![[r#"
        Function {
            params: [
                Param {
                    name: "a",
                },
                Param {
                    name: "b",
                },
            ],
            body: Infix {
                left: Identifier(
                    "a",
                ),
                op: Add,
                right: Identifier(
                    "b",
                ),
            },
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_partial_application() {
    // Test partial application _ + 1
    // This should parse as a Placeholder in an expression
    let expr = parse_expr("_ + 1").unwrap();
    expect![[r#"
        Infix {
            left: Placeholder,
            op: Add,
            right: Integer(
                1,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_call_expression() {
    // Test function call f(1, 2)
    let expr = parse_expr("f(1, 2)").unwrap();
    expect![[r#"
        Call {
            function: Identifier(
                "f",
            ),
            args: [
                Integer(
                    1,
                ),
                Integer(
                    2,
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_index_expression() {
    // Test indexing arr[0]
    let expr = parse_expr("arr[0]").unwrap();
    expect![[r#"
        Index {
            collection: Identifier(
                "arr",
            ),
            index: Integer(
                0,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_set_literal() {
    // Test set #{1, 2, 3}
    let expr = parse_expr("#{1, 2, 3}").unwrap();
    expect![[r#"
        Set(
            [
                Integer(
                    1,
                ),
                Integer(
                    2,
                ),
                Integer(
                    3,
                ),
            ],
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_dict_literal() {
    // Test dict #{1: 2, 3: 4}
    let expr = parse_expr("#{1: 2, 3: 4}").unwrap();
    expect![[r#"
        Dict(
            [
                (
                    Integer(
                        1,
                    ),
                    Integer(
                        2,
                    ),
                ),
                (
                    Integer(
                        3,
                    ),
                    Integer(
                        4,
                    ),
                ),
            ],
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_range_exclusive() {
    // Test exclusive range 1..5
    let expr = parse_expr("1..5").unwrap();
    expect![[r#"
        Infix {
            left: Integer(
                1,
            ),
            op: Range,
            right: Integer(
                5,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_range_inclusive() {
    // Test inclusive range 1..=5
    let expr = parse_expr("1..=5").unwrap();
    expect![[r#"
        Infix {
            left: Integer(
                1,
            ),
            op: RangeInclusive,
            right: Integer(
                5,
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_pipeline() {
    // Test pipeline x |> f
    let expr = parse_expr("x |> f").unwrap();
    expect![[r#"
        Infix {
            left: Identifier(
                "x",
            ),
            op: Pipeline,
            right: Identifier(
                "f",
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_composition() {
    // Test composition f >> g
    let expr = parse_expr("f >> g").unwrap();
    expect![[r#"
        Infix {
            left: Identifier(
                "f",
            ),
            op: Composition,
            right: Identifier(
                "g",
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

// Trailing lambda syntax will be implemented in Phase 3
