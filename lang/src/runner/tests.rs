use super::*;
use crate::lexer::lex;
use crate::parser::ast::Expr;
use crate::parser::Parser;

fn parse_program(source: &str) -> Program {
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    parser.parse_program().unwrap()
}

#[test]
fn validate_single_input_section() {
    let program = parse_program(r#"input: "test""#);
    let runner = Runner::new();
    assert!(runner.validate_program(&program).is_ok());
}

#[test]
fn validate_duplicate_input_error() {
    let program = parse_program(r#"
input: "test1"
input: "test2"
"#);
    let runner = Runner::new();
    assert_eq!(
        runner.validate_program(&program),
        Err(RunnerError::DuplicateInput)
    );
}

#[test]
fn validate_duplicate_part_one_error() {
    let program = parse_program(r#"
part_one: 1
part_one: 2
"#);
    let runner = Runner::new();
    assert_eq!(
        runner.validate_program(&program),
        Err(RunnerError::DuplicatePartOne)
    );
}

#[test]
fn validate_duplicate_part_two_error() {
    let program = parse_program(r#"
part_two: 1
part_two: 2
"#);
    let runner = Runner::new();
    assert_eq!(
        runner.validate_program(&program),
        Err(RunnerError::DuplicatePartTwo)
    );
}

#[test]
fn validate_multiple_test_sections_allowed() {
    let program = parse_program(r#"
test: {
  input: "test1"
  part_one: 1
}
test: {
  input: "test2"
  part_one: 2
}
"#);
    let runner = Runner::new();
    assert!(runner.validate_program(&program).is_ok());
}

#[test]
fn is_script_mode_no_parts() {
    let program = parse_program(r#"let x = 1 + 2"#);
    let runner = Runner::new();
    assert!(runner.is_script_mode(&program));
}

#[test]
fn is_script_mode_with_input_only() {
    let program = parse_program(r#"input: "data""#);
    let runner = Runner::new();
    assert!(runner.is_script_mode(&program));
}

#[test]
fn is_not_script_mode_with_part_one() {
    let program = parse_program(r#"
input: "data"
part_one: 42
"#);
    let runner = Runner::new();
    assert!(!runner.is_script_mode(&program));
}

#[test]
fn is_not_script_mode_with_part_two() {
    let program = parse_program(r#"
input: "data"
part_two: 42
"#);
    let runner = Runner::new();
    assert!(!runner.is_script_mode(&program));
}

#[test]
fn filter_tests_excludes_slow_by_default() {
    let program = parse_program(r#"
test: {
  input: "fast"
  part_one: 1
}
@slow
test: {
  input: "slow"
  part_one: 2
}
"#);
    let runner = Runner::new();
    let tests = runner.get_tests(&program);
    let filtered = runner.filter_tests(tests);
    assert_eq!(filtered.len(), 1);

    // Verify it's the fast test
    if let Section::Test { input, .. } = filtered[0] {
        assert!(matches!(input, Expr::String(s) if s == "fast"));
    } else {
        panic!("Expected Test section");
    }
}

#[test]
fn filter_tests_includes_slow_when_configured() {
    let program = parse_program(r#"
test: {
  input: "fast"
  part_one: 1
}
@slow
test: {
  input: "slow"
  part_one: 2
}
"#);
    let runner = Runner::with_config(RunnerConfig {
        include_slow: true,
    });
    let tests = runner.get_tests(&program);
    let filtered = runner.filter_tests(tests);
    assert_eq!(filtered.len(), 2);
}

// Phase 17: Solution execution tests

#[test]
fn generate_source_for_solution() {
    // Test source generation before testing full execution
    let program = parse_program(r#"
input: 42

part_one: input + 1
"#);
    let runner = Runner::new();
    let source = runner.test_generate_source(&program);

    // Expected source:
    // let input = 42;
    // let result_part_one = (input + 1);
    // puts("PART_ONE:", result_part_one);
    // 0
    println!("Generated source:\n{}", source);
    assert!(source.contains("let input = 42"));
    assert!(source.contains("input + 1"));
    assert!(source.contains("result_part_one"));
}

#[test]
fn generate_source_for_if_expression() {
    let program = parse_program(r#"
part_one: if input > 0 { input * 2 } else { input * -1 }

test: {
  input: 5
  part_one: 10
}
"#);
    let runner = Runner::new();
    let source = runner.test_generate_source(&program);
    println!("Generated source for if:\n{}", source);
    // Should contain valid if expression
    assert!(source.contains("if input > 0"));
}

#[test]
#[ignore] // Requires runtime library to be rebuilt: `cargo build --release`
fn execute_solution_with_input_binding() {
    let program = parse_program(r#"
input: 42

part_one: input + 1
"#);
    let runner = Runner::new();
    let result = runner.execute_solution(&program).unwrap();

    // input is 42, part_one is input + 1 = 43
    assert_eq!(result.part_one, Some(Value::from_integer(43)));
    assert_eq!(result.part_two, None);
}

// Phase 17: Test execution tests

#[test]
fn execute_test_simple_passing() {
    // A test section with input and expected part_one that should pass
    let program = parse_program(r#"
part_one: input + 1

test: {
  input: 10
  part_one: 11
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(11)));
}

#[test]
fn execute_test_simple_failing() {
    // A test section with wrong expected value
    let program = parse_program(r#"
part_one: input + 1

test: {
  input: 10
  part_one: 999
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(false));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(11)));
}

#[test]
fn execute_test_with_both_parts() {
    let program = parse_program(r#"
part_one: input * 2
part_two: input * 3

test: {
  input: 5
  part_one: 10
  part_two: 15
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_two_passed, Some(true));
}

#[test]
fn execute_multiple_tests() {
    let program = parse_program(r#"
part_one: input + 1

test: {
  input: 10
  part_one: 11
}
test: {
  input: 20
  part_one: 21
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 2);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[1].part_one_passed, Some(true));
}

// Phase 17: Timing tests

#[test]
fn solution_result_includes_timing() {
    let program = parse_program(r#"
part_one: 1 + 2
"#);
    let runner = Runner::new();
    let result = runner.execute_solution(&program).unwrap();

    // Timing should be present and non-negative
    assert!(result.part_one_time.is_some());
    let time = result.part_one_time.unwrap();
    assert!(time.as_nanos() >= 0);
}

#[test]
fn test_result_includes_timing() {
    let program = parse_program(r#"
part_one: input * 2

test: {
  input: 5
  part_one: 10
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    // Test results should include timing
    assert!(results[0].part_one_time.is_some());
}

#[test]
fn generate_source_for_match_with_function() {
    let program = parse_program(r#"
let sum_list = |list| match list {
  [] { 0 }
  [head, ..tail] { head + sum_list(tail) }
};

part_one: sum_list(input)

test: {
  input: [1, 2, 3]
  part_one: 6
}
"#);
    let runner = Runner::new();
    let source = runner.test_generate_source(&program);
    println!("Generated source for match:\n{}", source);

    // Check that the source contains a valid match expression
    assert!(source.contains("match list"));
    assert!(source.contains("sum_list"));
}

#[test]
fn generate_source_for_tail_recursive_sum() {
    let program = parse_program(r#"
let sum_list_tail = |acc, list| match list {
  [] { acc }
  [head, ..tail] { sum_list_tail(acc + head, tail) }
};

let sum_list = |list| sum_list_tail(0, list);

part_one: sum_list(input)

test: {
  input: [1, 2, 3]
  part_one: 6
}
"#);
    let runner = Runner::new();
    let source = runner.test_generate_source(&program);
    println!("Generated source for tail recursive sum:\n{}", source);

    // Check that both functions are present
    assert!(source.contains("sum_list_tail"));
    assert!(source.contains("sum_list"));
}

// Phase 10-11: Built-in function tests

#[test]
fn execute_test_sum_builtin() {
    // Test sum([1, 2, 3]) = 6
    let program = parse_program(r#"
part_one: sum([1, 2, 3, 4])

test: {
  input: nil
  part_one: 10
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(10)));
}

#[test]
fn execute_test_fold_builtin() {
    // Test fold(0, |acc, n| acc + n, [1, 2, 3]) = 6
    let program = parse_program(r#"
part_one: fold(0, |acc, n| acc + n, [1, 2, 3])

test: {
  input: nil
  part_one: 6
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(6)));
}

// Phase 13: break in reduce/fold/each for infinite sequences

#[test]
fn execute_test_break_in_fold_list() {
    // Test break with a list
    // Sum numbers [1, 2, 3, 4, 5] but break when acc > 6
    // 1 + 2 + 3 = 6, then 6 + 4 = 10 > 6, so break with 6
    let program = parse_program(r#"
part_one: fold(0, |acc, n| {
  let next = acc + n;
  if next > 6 { break acc }
  else { next }
}, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])

test: {
  input: nil
  part_one: 6
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(6)));
}

// Phase 14: memoize builtin
#[test]
fn execute_test_memoize_builtin() {
    // Test memoize with a simple identity closure
    // memoize should return a callable that caches results
    let program = parse_program(r#"
let identity = memoize |x| x;
part_one: identity(42)

test: {
  input: nil
  part_one: 42
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(42)));
}

// Phase 9: Basic mutable assignment test
#[test]
fn execute_test_basic_assignment() {
    // Simple test of mutable variable assignment within a closure
    let program = parse_program(r#"
let test_assign = || {
  let mut x = 0;
  x = x + 1;
  x
};

part_one: test_assign()

test: {
  input: nil
  part_one: 1
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(1)));
}

// Phase 9: Simple mutable capture - single call
#[test]
fn execute_test_simple_mutable_capture() {
    // Simple test: one call to a closure that captures a mutable variable
    let program = parse_program(r#"
let make_inc = || {
  let mut x = 0;
  || {
    x = x + 1;
    x
  }
};

let inc = make_inc();

part_one: inc()

test: {
  input: nil
  part_one: 1
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    println!("Simple capture actual: {:?}", results[0].part_one_actual);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(1)));
}

// Phase 9: Mutable capture - two calls
#[test]
fn execute_test_mutable_capture_two_calls() {
    // Two calls to a closure that captures a mutable variable
    let program = parse_program(r#"
let make_inc = || {
  let mut x = 0;
  || {
    x = x + 1;
    x
  }
};

let inc = make_inc();

part_one: inc() + inc()

test: {
  input: nil
  part_one: 3
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    println!("Two calls actual: {:?}", results[0].part_one_actual);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(3)));
}

// Phase 9: Mutable capture - immediate invocation
#[test]
fn execute_test_mutable_capture_immediate_invoke() {
    // Like the counter pattern, but simpler - using immediate invocation
    let program = parse_program(r#"
let inc = || {
  let mut x = 0;
  || {
    x = x + 1;
    x
  }
}();

part_one: inc() + inc()

test: {
  input: nil
  part_one: 3
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    println!("Immediate invoke actual: {:?}", results[0].part_one_actual);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(3)));
}

// Phase 9: Mutable captures - counter pattern from LANG.txt §8.3
#[test]
fn execute_test_mutable_closure_counter() {
    // This is the counter pattern from LANG.txt §8.3
    // A closure that returns another closure, with the inner closure
    // modifying a mutable variable from the outer scope
    // Note: We use 'cnt' instead of 'count' because 'count' is a protected builtin name
    let program = parse_program(r#"
let counter = || {
  let mut cnt = 0;
  || {
    cnt = cnt + 1;
    cnt
  }
}();

part_one: counter() + counter() + counter()

test: {
  input: nil
  part_one: 6
}
"#);
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    // counter() returns 1, then 2, then 3
    // 1 + 2 + 3 = 6
    assert_eq!(results.len(), 1);
    println!("Actual result: {:?}", results[0].part_one_actual);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(6)));
}

