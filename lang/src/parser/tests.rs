use super::*;
use crate::lexer::lex;
use expect_test::expect;

fn parse_expr(source: &str) -> Result<Expr, ParseError> {
    let tokens = lex(source).unwrap();
    parse(tokens)
}

fn parse_stmt(source: &str) -> Result<Stmt, ParseError> {
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    parser.parse_statement()
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

// ===== Phase 3: Statement Tests =====

#[test]
fn parse_let_binding() {
    // Test simple let binding: let x = 42;
    let stmt = parse_stmt("let x = 42").unwrap();
    expect![[r#"
        Let {
            mutable: false,
            pattern: Identifier(
                "x",
            ),
            value: Integer(
                42,
            ),
        }
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_mutable_binding() {
    // Test mutable let binding: let mut x = 42;
    let stmt = parse_stmt("let mut x = 42").unwrap();
    expect![[r#"
        Let {
            mutable: true,
            pattern: Identifier(
                "x",
            ),
            value: Integer(
                42,
            ),
        }
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_return_statement() {
    // Test return statement: return 42;
    let stmt = parse_stmt("return 42").unwrap();
    expect![[r#"
        Return(
            Integer(
                42,
            ),
        )
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_break_statement() {
    // Test break statement: break 42;
    let stmt = parse_stmt("break 42").unwrap();
    expect![[r#"
        Break(
            Integer(
                42,
            ),
        )
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_expression_statement() {
    // Test expression statement: 1 + 2;
    let stmt = parse_stmt("1 + 2").unwrap();
    expect![[r#"
        Expr(
            Infix {
                left: Integer(
                    1,
                ),
                op: Add,
                right: Integer(
                    2,
                ),
            },
        )
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_let_destructuring_list() {
    // Test list destructuring: let [a, b] = [1, 2];
    let stmt = parse_stmt("let [a, b] = [1, 2]").unwrap();
    expect![[r#"
        Let {
            mutable: false,
            pattern: List(
                [
                    Identifier(
                        "a",
                    ),
                    Identifier(
                        "b",
                    ),
                ],
            ),
            value: List(
                [
                    Integer(
                        1,
                    ),
                    Integer(
                        2,
                    ),
                ],
            ),
        }
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_let_destructuring_with_rest() {
    // Test list destructuring with rest: let [a, ..rest] = [1, 2, 3];
    let stmt = parse_stmt("let [a, ..rest] = [1, 2, 3]").unwrap();
    expect![[r#"
        Let {
            mutable: false,
            pattern: List(
                [
                    Identifier(
                        "a",
                    ),
                    RestIdentifier(
                        "rest",
                    ),
                ],
            ),
            value: List(
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
            ),
        }
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_let_wildcard_pattern() {
    // Test wildcard pattern: let _ = 42;
    let stmt = parse_stmt("let _ = 42").unwrap();
    expect![[r#"
        Let {
            mutable: false,
            pattern: Wildcard,
            value: Integer(
                42,
            ),
        }
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_match_expression() {
    // Test simple match expression
    let expr = parse_expr("match x { 1 { 10 } 2 { 20 } _ { 0 } }").unwrap();
    expect![[r#"
        Match {
            subject: Identifier(
                "x",
            ),
            arms: [
                MatchArm {
                    pattern: Literal(
                        Integer(
                            1,
                        ),
                    ),
                    guard: None,
                    body: Block(
                        [
                            Expr(
                                Integer(
                                    10,
                                ),
                            ),
                        ],
                    ),
                },
                MatchArm {
                    pattern: Literal(
                        Integer(
                            2,
                        ),
                    ),
                    guard: None,
                    body: Block(
                        [
                            Expr(
                                Integer(
                                    20,
                                ),
                            ),
                        ],
                    ),
                },
                MatchArm {
                    pattern: Wildcard,
                    guard: None,
                    body: Block(
                        [
                            Expr(
                                Integer(
                                    0,
                                ),
                            ),
                        ],
                    ),
                },
            ],
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_match_with_guards() {
    // Test match with guard clause
    let expr = parse_expr("match x { n if n > 0 { 1 } _ { 0 } }").unwrap();
    expect![[r#"
        Match {
            subject: Identifier(
                "x",
            ),
            arms: [
                MatchArm {
                    pattern: Identifier(
                        "n",
                    ),
                    guard: Some(
                        Infix {
                            left: Identifier(
                                "n",
                            ),
                            op: GreaterThan,
                            right: Integer(
                                0,
                            ),
                        },
                    ),
                    body: Block(
                        [
                            Expr(
                                Integer(
                                    1,
                                ),
                            ),
                        ],
                    ),
                },
                MatchArm {
                    pattern: Wildcard,
                    guard: None,
                    body: Block(
                        [
                            Expr(
                                Integer(
                                    0,
                                ),
                            ),
                        ],
                    ),
                },
            ],
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_aoc_input_section() {
    // Test input section: input: read("aoc://2022/1")
    let source = r#"input: read("aoc://2022/1")"#;
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();

    expect![[r#"
        Program {
            statements: [],
            sections: [
                Input(
                    Call {
                        function: Identifier(
                            "read",
                        ),
                        args: [
                            String(
                                "aoc://2022/1",
                            ),
                        ],
                    },
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&program);
}

#[test]
fn parse_aoc_part_sections() {
    // Test part_one and part_two sections
    let source = r#"
part_one: 42
part_two: { 1 + 1 }
"#;
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();

    expect![[r#"
        Program {
            statements: [],
            sections: [
                PartOne(
                    Integer(
                        42,
                    ),
                ),
                PartTwo(
                    Block(
                        [
                            Expr(
                                Infix {
                                    left: Integer(
                                        1,
                                    ),
                                    op: Add,
                                    right: Integer(
                                        1,
                                    ),
                                },
                            ),
                        ],
                    ),
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&program);
}

#[test]
fn parse_aoc_test_section() {
    // Test test section with input, part_one, and part_two
    let source = r#"
test: {
  input: "test data"
  part_one: 100
  part_two: 200
}
"#;
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();

    expect![[r#"
        Program {
            statements: [],
            sections: [
                Test {
                    input: String(
                        "test data",
                    ),
                    part_one: Some(
                        Integer(
                            100,
                        ),
                    ),
                    part_two: Some(
                        Integer(
                            200,
                        ),
                    ),
                },
            ],
        }
    "#]]
    .assert_debug_eq(&program);
}

#[test]
fn parse_complete_aoc_program() {
    // Test complete program with statements and sections
    let source = r#"
let x = 10;

input: "data"

part_one: x * 2
"#;
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();

    expect![[r#"
        Program {
            statements: [
                Let {
                    mutable: false,
                    pattern: Identifier(
                        "x",
                    ),
                    value: Integer(
                        10,
                    ),
                },
            ],
            sections: [
                Input(
                    String(
                        "data",
                    ),
                ),
                PartOne(
                    Infix {
                        left: Identifier(
                            "x",
                        ),
                        op: Multiply,
                        right: Integer(
                            2,
                        ),
                    },
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&program);
}

#[test]
fn parse_trailing_lambda() {
    // Test trailing lambda syntax: [1, 2, 3] map |x| x * 2
    // Should transform to: map([1, 2, 3], |x| x * 2)
    let expr = parse_expr("[1, 2, 3] map |x| x * 2").unwrap();
    expect![[r#"
        Call {
            function: Identifier(
                "map",
            ),
            args: [
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
                ),
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
                        op: Multiply,
                        right: Integer(
                            2,
                        ),
                    },
                },
            ],
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_empty_set_in_expression_position() {
    // {} in value position should be an empty set
    let stmt = parse_stmt("let x = {}").unwrap();
    expect![[r#"
        Let {
            mutable: false,
            pattern: Identifier(
                "x",
            ),
            value: Set(
                [],
            ),
        }
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_empty_block_in_statement_position() {
    // {} as function body should be an empty block
    let expr = parse_expr("|| { }").unwrap();
    expect![[r#"
        Function {
            params: [],
            body: Block(
                [],
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_dict_shorthand() {
    // Test dict shorthand: #{name, age} → #{"name": name, "age": age}
    let expr = parse_expr("#{name, age}").unwrap();
    expect![[r#"
        Dict(
            [
                (
                    String(
                        "name",
                    ),
                    Identifier(
                        "name",
                    ),
                ),
                (
                    String(
                        "age",
                    ),
                    Identifier(
                        "age",
                    ),
                ),
            ],
        )
    "#]]
    .assert_debug_eq(&expr);
}
