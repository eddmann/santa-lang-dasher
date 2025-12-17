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
    // This should be transformed into a function |__arg_0| __arg_0 + 1
    let expr = parse_expr("_ + 1").unwrap();
    expect![[r#"
        Function {
            params: [
                Param {
                    name: "__arg_0",
                },
            ],
            body: Infix {
                left: Identifier(
                    "__arg_0",
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
fn parse_partial_application_multiple_placeholders() {
    // Test partial application with multiple placeholders _ / _
    // This should be transformed into a function |__arg_0, __arg_1| __arg_0 / __arg_1
    let expr = parse_expr("_ / _").unwrap();
    expect![[r#"
        Function {
            params: [
                Param {
                    name: "__arg_0",
                },
                Param {
                    name: "__arg_1",
                },
            ],
            body: Infix {
                left: Identifier(
                    "__arg_0",
                ),
                op: Divide,
                right: Identifier(
                    "__arg_1",
                ),
            },
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_partial_application_right_operand() {
    // Test partial application with placeholder on right: 10 - _
    // This should be transformed into a function |__arg_0| 10 - __arg_0
    let expr = parse_expr("10 - _").unwrap();
    expect![[r#"
        Function {
            params: [
                Param {
                    name: "__arg_0",
                },
            ],
            body: Infix {
                left: Integer(
                    10,
                ),
                op: Subtract,
                right: Identifier(
                    "__arg_0",
                ),
            },
        }
    "#]]
    .assert_debug_eq(&expr);
}

// Operator function reference tests
#[test]
fn parse_operator_reference_add() {
    // Bare + should become |__op_0, __op_1| __op_0 + __op_1
    let expr = parse_expr("fold(0, +, [1, 2, 3])").unwrap();
    // The second argument should be a Function with two params
    if let Expr::Call { args, .. } = &expr {
        assert_eq!(args.len(), 3);
        match &args[1] {
            Expr::Function { params, body } => {
                assert_eq!(params.len(), 2);
                assert_eq!(params[0].name, "__op_0");
                assert_eq!(params[1].name, "__op_1");
                match body.as_ref() {
                    Expr::Infix { op, .. } => {
                        assert_eq!(*op, InfixOp::Add);
                    }
                    _ => panic!("Expected Infix body"),
                }
            }
            _ => panic!("Expected Function for operator reference, got {:?}", args[1]),
        }
    } else {
        panic!("Expected Call expression");
    }
}

#[test]
fn parse_operator_reference_multiply() {
    // Bare * should become |__op_0, __op_1| __op_0 * __op_1
    let expr = parse_expr("reduce(*, [1, 2, 3])").unwrap();
    if let Expr::Call { args, .. } = &expr {
        assert_eq!(args.len(), 2);
        match &args[0] {
            Expr::Function { params, body } => {
                assert_eq!(params.len(), 2);
                match body.as_ref() {
                    Expr::Infix { op, .. } => {
                        assert_eq!(*op, InfixOp::Multiply);
                    }
                    _ => panic!("Expected Infix body"),
                }
            }
            _ => panic!("Expected Function for operator reference"),
        }
    } else {
        panic!("Expected Call expression");
    }
}

#[test]
fn parse_operator_reference_subtract() {
    // Bare - should become |__op_0, __op_1| __op_0 - __op_1
    let expr = parse_expr("-").unwrap();
    match &expr {
        Expr::Function { params, body } => {
            assert_eq!(params.len(), 2);
            match body.as_ref() {
                Expr::Infix { op, .. } => {
                    assert_eq!(*op, InfixOp::Subtract);
                }
                _ => panic!("Expected Infix body"),
            }
        }
        _ => panic!("Expected Function for operator reference"),
    }
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
fn parse_call_expression_zero_args() {
    // Test function call with zero arguments f()
    let expr = parse_expr("f()").unwrap();
    expect![[r#"
        Call {
            function: Identifier(
                "f",
            ),
            args: [],
        }
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_time_nanos_call() {
    // Test parsing __time_nanos()
    let expr = parse_expr("__time_nanos()").unwrap();
    expect![[r#"
        Call {
            function: Identifier(
                "__time_nanos",
            ),
            args: [],
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
}

#[test]
fn parse_let_binding_with_lambda() {
    // Test let binding with lambda value
    let stmt = parse_stmt("let f = |x| x + 1").unwrap();
    expect![[r#"
        Let {
            mutable: false,
            pattern: Identifier(
                "f",
            ),
            value: Function {
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
            },
        }
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_memoize_call() {
    // Test memoize call: memoize |x| x
    let stmt = parse_stmt("let identity = memoize |x| x").unwrap();
    expect![[r#"
        Let {
            mutable: false,
            pattern: Identifier(
                "identity",
            ),
            value: Call {
                function: Identifier(
                    "memoize",
                ),
                args: [
                    Function {
                        params: [
                            Param {
                                name: "x",
                            },
                        ],
                        body: Identifier(
                            "x",
                        ),
                    },
                ],
            },
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
                    slow: false,
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

#[test]
fn parse_slow_test_attribute() {
    // Test @slow attribute on test sections
    let source = r#"
@slow
test: {
  input: "test data"
  part_one: 100
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
                    slow: true,
                    input: String(
                        "test data",
                    ),
                    part_one: Some(
                        Integer(
                            100,
                        ),
                    ),
                    part_two: None,
                },
            ],
        }
    "#]]
    .assert_debug_eq(&program);
}

// Phase 13: break statement tests

#[test]
fn parse_break_statement_simple() {
    // Test simple break statement: break acc
    let stmt = parse_stmt("break acc").unwrap();
    expect![[r#"
        Break(
            Identifier(
                "acc",
            ),
        )
    "#]]
    .assert_debug_eq(&stmt);
}

#[test]
fn parse_break_in_block() {
    // Test break inside a block: { break 42 }
    let expr = parse_expr("{ break 42 }").unwrap();
    expect![[r#"
        Block(
            [
                Break(
                    Integer(
                        42,
                    ),
                ),
            ],
        )
    "#]]
    .assert_debug_eq(&expr);
}

#[test]
fn parse_break_in_if_block() {
    // Test break in if-else: if cond { break x } else { y }
    let expr = parse_expr("if cond { break x } else { y }").unwrap();
    expect![[r#"
        If {
            condition: Identifier(
                "cond",
            ),
            then_branch: Block(
                [
                    Break(
                        Identifier(
                            "x",
                        ),
                    ),
                ],
            ),
            else_branch: Some(
                Block(
                    [
                        Expr(
                            Identifier(
                                "y",
                            ),
                        ),
                    ],
                ),
            ),
        }
    "#]]
    .assert_debug_eq(&expr);
}

