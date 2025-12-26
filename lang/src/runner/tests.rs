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
    let program = parse_program(
        r#"
input: "test1"
input: "test2"
"#,
    );
    let runner = Runner::new();
    assert_eq!(
        runner.validate_program(&program),
        Err(RunnerError::DuplicateInput)
    );
}

#[test]
fn validate_duplicate_part_one_error() {
    let program = parse_program(
        r#"
part_one: 1
part_one: 2
"#,
    );
    let runner = Runner::new();
    assert_eq!(
        runner.validate_program(&program),
        Err(RunnerError::DuplicatePartOne)
    );
}

#[test]
fn validate_duplicate_part_two_error() {
    let program = parse_program(
        r#"
part_two: 1
part_two: 2
"#,
    );
    let runner = Runner::new();
    assert_eq!(
        runner.validate_program(&program),
        Err(RunnerError::DuplicatePartTwo)
    );
}

#[test]
fn validate_multiple_test_sections_allowed() {
    let program = parse_program(
        r#"
test: {
  input: "test1"
  part_one: 1
}
test: {
  input: "test2"
  part_one: 2
}
"#,
    );
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
    let program = parse_program(
        r#"
input: "data"
part_one: 42
"#,
    );
    let runner = Runner::new();
    assert!(!runner.is_script_mode(&program));
}

#[test]
fn is_not_script_mode_with_part_two() {
    let program = parse_program(
        r#"
input: "data"
part_two: 42
"#,
    );
    let runner = Runner::new();
    assert!(!runner.is_script_mode(&program));
}

#[test]
fn filter_tests_excludes_slow_by_default() {
    let program = parse_program(
        r#"
test: {
  input: "fast"
  part_one: 1
}
@slow
test: {
  input: "slow"
  part_one: 2
}
"#,
    );
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
    let program = parse_program(
        r#"
test: {
  input: "fast"
  part_one: 1
}
@slow
test: {
  input: "slow"
  part_one: 2
}
"#,
    );
    let runner = Runner::with_config(RunnerConfig {
        include_slow: true,
        script_dir: None,
    });
    let tests = runner.get_tests(&program);
    let filtered = runner.filter_tests(tests);
    assert_eq!(filtered.len(), 2);
}

// Phase 17: Solution execution tests

#[test]
fn generate_source_for_solution() {
    // Test source generation before testing full execution
    let program = parse_program(
        r#"
input: 42

part_one: input + 1
"#,
    );
    let runner = Runner::new();
    let source = runner.test_generate_source(&program);

    // Expected source now includes CLI arg handling and colored output:
    // - __get_args() for test mode detection
    // - __print_result() for colored output
    println!("Generated source:\n{}", source);
    assert!(source.contains("let input = 42"));
    assert!(source.contains("input + 1"));
    assert!(source.contains("__print_result"));
    assert!(source.contains("__get_args"));
}

#[test]
fn generate_source_for_if_expression() {
    let program = parse_program(
        r#"
part_one: if input > 0 { input * 2 } else { input * -1 }

test: {
  input: 5
  part_one: 10
}
"#,
    );
    let runner = Runner::new();
    let source = runner.test_generate_source(&program);
    println!("Generated source for if:\n{}", source);
    // Should contain valid if expression
    assert!(source.contains("if (input > 0)"));
}

#[test]
#[ignore] // Requires runtime library to be rebuilt: `cargo build --release`
fn execute_solution_with_input_binding() {
    let program = parse_program(
        r#"
input: 42

part_one: input + 1
"#,
    );
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
    let program = parse_program(
        r#"
part_one: input + 1

test: {
  input: 10
  part_one: 11
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(11)));
}

#[test]
fn execute_test_simple_failing() {
    // A test section with wrong expected value
    let program = parse_program(
        r#"
part_one: input + 1

test: {
  input: 10
  part_one: 999
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(false));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(11)));
}

#[test]
fn execute_test_with_both_parts() {
    let program = parse_program(
        r#"
part_one: input * 2
part_two: input * 3

test: {
  input: 5
  part_one: 10
  part_two: 15
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_two_passed, Some(true));
}

#[test]
fn execute_multiple_tests() {
    let program = parse_program(
        r#"
part_one: input + 1

test: {
  input: 10
  part_one: 11
}
test: {
  input: 20
  part_one: 21
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 2);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[1].part_one_passed, Some(true));
}

// Phase 17: Timing tests

#[test]
fn solution_result_includes_timing() {
    let program = parse_program(
        r#"
part_one: 1 + 2
"#,
    );
    let runner = Runner::new();
    let result = runner.execute_solution(&program).unwrap();

    // Timing should be present
    assert!(result.part_one_time.is_some());
}

#[test]
fn test_result_includes_timing() {
    let program = parse_program(
        r#"
part_one: input * 2

test: {
  input: 5
  part_one: 10
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    // Test results should include timing
    assert!(results[0].part_one_time.is_some());
}

#[test]
fn generate_source_for_match_with_function() {
    let program = parse_program(
        r#"
let sum_list = |list| match list {
  [] { 0 }
  [head, ..tail] { head + sum_list(tail) }
};

part_one: sum_list(input)

test: {
  input: [1, 2, 3]
  part_one: 6
}
"#,
    );
    let runner = Runner::new();
    let source = runner.test_generate_source(&program);
    println!("Generated source for match:\n{}", source);

    // Check that the source contains a valid match expression
    assert!(source.contains("match list"));
    assert!(source.contains("sum_list"));
}

#[test]
fn generate_source_for_tail_recursive_sum() {
    let program = parse_program(
        r#"
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
"#,
    );
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
    let program = parse_program(
        r#"
part_one: sum([1, 2, 3, 4])

test: {
  input: nil
  part_one: 10
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(10)));
}

#[test]
fn execute_test_fold_builtin() {
    // Test fold(0, |acc, n| acc + n, [1, 2, 3]) = 6
    let program = parse_program(
        r#"
part_one: fold(0, |acc, n| acc + n, [1, 2, 3])

test: {
  input: nil
  part_one: 6
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(6)));
}

#[test]
fn execute_test_fold_with_operator_reference() {
    // Test fold(0, +, [1, 2, 3]) = 6
    // The + is an operator reference that becomes |a, b| a + b
    let program = parse_program(
        r#"
part_one: fold(0, +, [1, 2, 3])

test: {
  input: nil
  part_one: 6
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(6)));
}

#[test]
fn execute_test_reduce_with_operator_reference() {
    // Test reduce(*, [1, 2, 3, 4]) = 24
    // The * is an operator reference that becomes |a, b| a * b
    let program = parse_program(
        r#"
part_one: reduce(*, [1, 2, 3, 4])

test: {
  input: nil
  part_one: 24
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(24)));
}

// Phase 13: break in reduce/fold/each for infinite sequences

#[test]
fn execute_test_break_in_fold_list() {
    // Test break with a list
    // Sum numbers [1, 2, 3, 4, 5] but break when acc > 6
    // 1 + 2 + 3 = 6, then 6 + 4 = 10 > 6, so break with 6
    let program = parse_program(
        r#"
part_one: fold(0, |acc, n| {
  let next = acc + n;
  if next > 6 { break acc }
  else { next }
}, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])

test: {
  input: nil
  part_one: 6
}
"#,
    );
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
    let program = parse_program(
        r#"
let identity = memoize |x| x;
part_one: identity(42)

test: {
  input: nil
  part_one: 42
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(42)));
}

#[test]
fn execute_test_memoize_self_recursion() {
    // Test memoized self-recursive function (fibonacci)
    // This is the pattern from LANG.txt §8.10:
    //   let fib = memoize |n| { if n > 1 { fib(n-1) + fib(n-2) } else { n } }
    // The closure references `fib` before it's assigned, so we need cell indirection.
    let program = parse_program(
        r#"
let fib = memoize |n| {
  if n > 1 { fib(n - 1) + fib(n - 2) } else { n }
};
part_one: fib(10)

test: {
  input: nil
  part_one: 55
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(55)));
}

#[test]
fn execute_test_non_tail_recursive_closure() {
    // Test non-tail recursive closure (factorial)
    // The recursive call is NOT in tail position: n * fact(n-1)
    // This should work correctly, not return nil
    let program = parse_program(
        r#"
let fact = |n| {
  if n <= 1 { 1 }
  else { n * fact(n - 1) }
};
part_one: fact(5)

test: {
  input: nil
  part_one: 120
}
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    assert_eq!(results.len(), 1);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(120)));
}

#[test]
fn test_self_referencing_detection() {
    // Verify that find_self_referencing_bindings detects direct self-recursive closures
    use crate::codegen::context::CodegenContext;
    use std::collections::HashSet;

    let source = r#"let fact = |n| { if n <= 1 { 1 } else { n * fact(n - 1) } };"#;
    let tokens = lex(source).unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();

    // Check detection
    let bound: HashSet<String> = HashSet::new();
    let self_refs = CodegenContext::find_self_referencing_bindings(&program.statements, &bound);

    // fact should be detected as self-referencing
    assert!(
        self_refs.contains("fact"),
        "fact should be detected as self-referencing, got: {:?}",
        self_refs
    );
}

#[test]
fn test_generated_source_for_self_recursive() {
    // Check what source is generated for the test
    let program = parse_program(
        r#"
let fact = |n| {
  if n <= 1 { 1 }
  else { n * fact(n - 1) }
};
part_one: fact(5)

test: {
  input: nil
  part_one: 120
}
"#,
    );
    let runner = Runner::new();

    // Generate the source that would be compiled
    let generated = runner.generate_test_source_for_debugging(
        &program.statements,
        &Expr::Nil,
        Some(&Expr::Call {
            function: Box::new(Expr::Identifier("fact".to_string())),
            args: vec![Expr::Integer(5)],
        }),
        None,
    );

    println!("Generated source:\n{}", generated);

    // Now check if the regenerated source still has fact as self-referencing
    use crate::codegen::context::CodegenContext;
    use std::collections::HashSet;

    let tokens = lex(&generated).unwrap();
    let mut parser = Parser::new(tokens);
    let reparsed = parser.parse_program().unwrap();

    let bound: HashSet<String> = HashSet::new();
    let self_refs = CodegenContext::find_self_referencing_bindings(&reparsed.statements, &bound);

    println!(
        "Self-referencing bindings in generated source: {:?}",
        self_refs
    );
    assert!(
        self_refs.contains("fact"),
        "fact should still be detected as self-referencing in generated source"
    );
}

#[test]
fn test_direct_compilation_non_recursive() {
    // First test: simple non-recursive closure
    use crate::codegen::pipeline::Compiler;
    use std::process::Command;

    let source = r#"
let double = |n| { n * 2 };
puts("RESULT:", double(5));
0
"#;

    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join("test_direct_non_recursive");

    println!("Starting compilation of non-recursive closure...");
    let compiler = Compiler::new();
    let result = compiler.compile_to_executable(source, &exe_path);
    println!("Compilation result: {:?}", result.is_ok());
    result.expect("Compilation failed");

    let output = Command::new(&exe_path).output().expect("Execution failed");

    std::fs::remove_file(&exe_path).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    println!("Output: {}", stdout);
    assert!(
        stdout.contains("RESULT: 10"),
        "Should output 10, got: {}",
        stdout
    );
}

#[test]
fn test_direct_compilation_simple_closure() {
    // Test simplest possible self-recursive closure
    use crate::codegen::pipeline::Compiler;
    use std::process::Command;

    // Simpler: identity function that references itself but doesn't call itself
    let source = r#"
let f = |n| n;
puts("RESULT:", f(5));
0
"#;

    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join("test_direct_simple_closure");

    println!("Starting compilation of simple closure...");
    let compiler = Compiler::new();
    let result = compiler.compile_to_executable(source, &exe_path);
    println!("Compilation result: {:?}", result.is_ok());
    result.expect("Compilation failed");

    let output = Command::new(&exe_path).output().expect("Execution failed");

    std::fs::remove_file(&exe_path).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    println!("Output: {}", stdout);
    assert!(
        stdout.contains("RESULT: 5"),
        "Should output 5, got: {}",
        stdout
    );
}

#[test]
fn test_direct_compilation_self_ref_no_call() {
    // Closure that references itself but doesn't call itself
    use crate::codegen::pipeline::Compiler;
    use std::process::Command;

    // This should trigger detection but just return 42
    let source = r#"
let f = |n| { let ignored = f; 42 };
puts("RESULT:", f(5));
0
"#;

    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join("test_direct_self_ref_no_call");

    println!("Starting compilation of self-ref-no-call closure...");
    let compiler = Compiler::new();
    let result = compiler.compile_to_executable(source, &exe_path);
    println!("Compilation result: {:?}", result.is_ok());
    result.expect("Compilation failed");

    let output = Command::new(&exe_path).output().expect("Execution failed");

    std::fs::remove_file(&exe_path).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    println!("Output: {}", stdout);
    assert!(
        stdout.contains("RESULT: 42"),
        "Should output 42, got: {}",
        stdout
    );
}

#[test]
fn test_direct_compilation_if_no_self_ref() {
    // Closure with if/else but no self-reference
    use crate::codegen::pipeline::Compiler;
    use std::process::Command;

    let source = r#"
let my_abs = |n| { if n < 0 { 0 - n } else { n } };
puts("RESULT:", my_abs(-5));
0
"#;

    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join("test_direct_if_no_self_ref");

    println!("Starting compilation of if-no-self-ref closure...");
    let compiler = Compiler::new();
    let result = compiler.compile_to_executable(source, &exe_path);
    println!("Compilation result: {:?}", result.is_ok());
    result.expect("Compilation failed");

    let output = Command::new(&exe_path).output().expect("Execution failed");

    std::fs::remove_file(&exe_path).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    println!("Output: {}", stdout);
    assert!(
        stdout.contains("RESULT: 5"),
        "Should output 5, got: {}",
        stdout
    );
}

#[test]
fn test_direct_compilation_tail_recursive() {
    // Test tail-recursive function (should use TCO)
    use crate::codegen::pipeline::Compiler;
    use std::process::Command;

    let source = r#"
let sum_helper = |n, acc| { if n <= 0 { acc } else { sum_helper(n - 1, acc + n) } };
puts("RESULT:", sum_helper(5, 0));
0
"#;

    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join("test_direct_tail_recursive");

    println!("Starting compilation of tail-recursive closure...");
    let compiler = Compiler::new();
    let result = compiler.compile_to_executable(source, &exe_path);
    println!("Compilation result: {:?}", result.is_ok());
    result.expect("Compilation failed");

    let output = Command::new(&exe_path).output().expect("Execution failed");

    std::fs::remove_file(&exe_path).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    println!("Output: {}", stdout);
    assert!(
        stdout.contains("RESULT: 15"),
        "Should output 15, got: {}",
        stdout
    );
}

#[test]
fn test_direct_compilation_self_recursive() {
    // Test compiling directly without going through runner transform
    use crate::codegen::pipeline::Compiler;
    use std::process::Command;

    let source = r#"
let fact = |n| { if n <= 1 { 1 } else { n * fact(n - 1) } };
puts("RESULT:", fact(5));
0
"#;

    // Compile
    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join("test_direct_self_recursive");

    println!("Starting compilation...");
    let compiler = Compiler::new();
    let result = compiler.compile_to_executable(source, &exe_path);
    println!("Compilation result: {:?}", result.is_ok());

    if let Err(ref e) = result {
        println!("Compilation error: {:?}", e);
    }
    result.expect("Compilation failed");

    println!("Compilation succeeded, running executable...");

    // Execute
    let output = Command::new(&exe_path).output().expect("Execution failed");

    std::fs::remove_file(&exe_path).ok();

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    println!("Stdout: {}", stdout);
    println!("Stderr: {}", stderr);
    println!("Status: {:?}", output.status);

    assert!(output.status.success(), "Program should succeed");
    assert!(
        stdout.contains("RESULT: 120"),
        "Should output 120, got: {}",
        stdout
    );
}

// Phase 9: Basic mutable assignment test
#[test]
fn execute_test_basic_assignment() {
    // Simple test of mutable variable assignment within a closure
    let program = parse_program(
        r#"
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
"#,
    );
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
    let program = parse_program(
        r#"
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
"#,
    );
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
    let program = parse_program(
        r#"
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
"#,
    );
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
    let program = parse_program(
        r#"
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
"#,
    );
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
    let program = parse_program(
        r#"
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
"#,
    );
    let runner = Runner::new();
    let results = runner.execute_tests(&program).unwrap();

    // counter() returns 1, then 2, then 3
    // 1 + 2 + 3 = 6
    assert_eq!(results.len(), 1);
    println!("Actual result: {:?}", results[0].part_one_actual);
    assert_eq!(results[0].part_one_passed, Some(true));
    assert_eq!(results[0].part_one_actual, Some(Value::from_integer(6)));
}

#[test]
fn test_generated_source_destructuring() {
    // Test that generated source for destructuring patterns is correct
    let program = parse_program(
        r#"
let lookup = #{"A": 0, "B": 1}

part_one: [[1, 2], [3, 4]] |> map(|[a, b]| a + b) |> sum

test: {
  input: nil
  part_one: 10
}
"#,
    );
    let runner = Runner::new();

    // Generate the source
    let generated = runner.generate_test_source_for_debugging(
        &program.statements,
        &Expr::Nil,
        Some(&Expr::Call {
            function: Box::new(Expr::Identifier("sum".to_string())),
            args: vec![Expr::Call {
                function: Box::new(Expr::Identifier("map".to_string())),
                args: vec![
                    Expr::List(vec![
                        Expr::List(vec![Expr::Integer(1), Expr::Integer(2)]),
                        Expr::List(vec![Expr::Integer(3), Expr::Integer(4)]),
                    ]),
                    Expr::Function {
                        params: vec![crate::parser::ast::Param {
                            pattern: crate::parser::ast::Pattern::List(vec![
                                crate::parser::ast::Pattern::Identifier("a".to_string()),
                                crate::parser::ast::Pattern::Identifier("b".to_string()),
                            ]),
                        }],
                        body: Box::new(Expr::Infix {
                            left: Box::new(Expr::Identifier("a".to_string())),
                            op: crate::parser::ast::InfixOp::Add,
                            right: Box::new(Expr::Identifier("b".to_string())),
                        }),
                    },
                ],
            }],
        }),
        None,
    );

    println!("Generated source for destructuring:\n{}", generated);

    // Check that it contains the destructuring pattern
    assert!(
        generated.contains("|[a, b]|"),
        "Should contain destructuring pattern |[a, b]|, got: {}",
        generated
    );
}

#[test]
fn test_day2_style_destructuring() {
    // Test Day 2 style pattern: destructuring in map with block body
    let program = parse_program(
        r#"
let lookup = #{
  "A": 0, "B": 1, "C": 2,
  "X": 0, "Y": 1, "Z": 2,
}

let parse_strategy = lines >> map(split(" "))

part_two: {
  parse_strategy(input)
    |> map(|[elf, ending]| {
      let move = (lookup[elf] + lookup[ending] + 2) % 3 + 1
      let outcome = lookup[ending] * 3
      move + outcome
    })
    |> sum
}

test: {
  input: "A Y
B X
C Z"
  part_two: 12
}
"#,
    );
    let runner = Runner::new();

    // Generate the test source
    let test = program
        .sections
        .iter()
        .find_map(|s| {
            if let crate::parser::ast::Section::Test { input, .. } = s {
                Some(input)
            } else {
                None
            }
        })
        .unwrap();

    let part_two = program.sections.iter().find_map(|s| {
        if let crate::parser::ast::Section::PartTwo(expr) = s {
            Some(expr)
        } else {
            None
        }
    });

    let generated =
        runner.generate_test_source_for_debugging(&program.statements, test, None, part_two);

    println!("Generated source for Day 2 style:\n{}", generated);

    // Now actually execute the tests
    let results = runner.execute_tests(&program).unwrap();
    println!(
        "Test results: part_two_passed={:?}, actual={:?}",
        results[0].part_two_passed, results[0].part_two_actual
    );

    assert_eq!(results[0].part_two_passed, Some(true));
    assert_eq!(results[0].part_two_actual, Some(Value::from_integer(12)));
}

#[test]
fn debug_day3_source_generation() {
    // Debug: see what source is generated for Day 3 style block with lambdas
    let program = parse_program(
        r#"
let priorities = zip("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ", 1..) |> dict;
let parse_groups = lines >> map(split(""));
let common_item = intersection >> list >> first;

part_one: {
  let compartments = |rucksack| {
    let length = size(rucksack) / 2;
    [rucksack[0..length], rucksack[length..]]
  };

  parse_groups(input)
    |> map(compartments >> common_item >> get(_, priorities))
    |> sum
}

test: {
  input: "vJrwpWtwJgWrhcsFMMfFFhFp
jqHRNqRjqzjGDLGLrsFMfFZSrLrFZsSL"
  part_one: 54
}
"#,
    );
    let runner = Runner::new();

    // Get the test input and part_one
    let test = program
        .sections
        .iter()
        .find_map(|s| {
            if let crate::parser::ast::Section::Test { input, .. } = s {
                Some(input)
            } else {
                None
            }
        })
        .unwrap();

    let part_one = program.sections.iter().find_map(|s| {
        if let crate::parser::ast::Section::PartOne(expr) = s {
            Some(expr)
        } else {
            None
        }
    });

    let generated =
        runner.generate_test_source_for_debugging(&program.statements, test, part_one, None);

    println!(
        "=== GENERATED SOURCE FOR DAY 3 ===\n{}\n=== END ===",
        generated
    );

    // Now actually run the test
    let results = runner.execute_tests(&program).unwrap();
    println!(
        "Test results: part_one_passed={:?}, actual={:?}",
        results[0].part_one_passed, results[0].part_one_actual
    );
}
