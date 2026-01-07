//! Integration tests for CLI output modes.
//!
//! These tests follow the CLI Output Format Specification (Section 16 of lang.txt).

use assert_cmd::Command;
use predicates::prelude::*;

// ============================================================================
// Basic CLI Tests (Text Mode)
// ============================================================================

#[test]
fn script() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg(format!("{}/fixtures/script.santa", env!("CARGO_MANIFEST_DIR")))
        .assert();
    assert.success().stdout("14\n");
}

#[test]
fn solution() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg(format!("{}/fixtures/solution.santa", env!("CARGO_MANIFEST_DIR")))
        .assert();
    assert
        .success()
        .stdout(predicate::str::contains("Part 1: \x1b[32m232\x1b[0m"))
        .stdout(predicate::str::contains("Part 2: \x1b[32m1783\x1b[0m"));
}

#[test]
fn test_solution() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg("-t")
        .arg(format!("{}/fixtures/solution.santa", env!("CARGO_MANIFEST_DIR")))
        .assert();
    assert
        .success()
        .stdout(predicate::str::contains("Testcase #1"))
        .stdout(predicate::str::contains("Part 1: -1 \x1b[32m✔\x1b[0m"))
        .stdout(predicate::str::contains("Part 2: 5 \x1b[32m✔\x1b[0m"));
}

#[test]
fn eval_simple_expression() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-e").arg("1 + 2").assert();
    assert.success().stdout("3\n");
}

#[test]
fn eval_complex_expression() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-e").arg("map(|x| x * 2, [1, 2, 3])").assert();
    assert.success().stdout("[2, 4, 6]\n");
}

#[test]
fn eval_aoc_solution() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-e").arg("part_one: { 42 }").assert();
    assert
        .success()
        .stdout(predicate::str::contains("Part 1: \x1b[32m42\x1b[0m"));
}

#[test]
fn stdin_simple_expression() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.write_stdin("1 + 2").assert();
    assert.success().stdout("3\n");
}

#[test]
fn stdin_aoc_solution() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.write_stdin("part_one: { 42 }").assert();
    assert
        .success()
        .stdout(predicate::str::contains("Part 1: \x1b[32m42\x1b[0m"));
}

#[test]
fn stdin_empty() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.write_stdin("").assert();
    assert.success();
}

// ============================================================================
// JSON Script Tests
// ============================================================================

#[test]
fn json_script_simple() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("json").arg("-e").arg("1 + 2").assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"script""#))
        .stdout(predicate::str::contains(r#""status":"complete""#))
        .stdout(predicate::str::contains(r#""value":"3""#));
}

#[test]
fn json_script_with_console() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("json").arg("-e").arg(r#"puts("hello"); 42"#).assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"script""#))
        .stdout(predicate::str::contains(r#""value":"42""#))
        .stdout(predicate::str::contains(r#""message":"hello""#));
}

// ============================================================================
// JSON Solution Tests
// ============================================================================

#[test]
fn json_solution() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg("-o")
        .arg("json")
        .arg(format!("{}/fixtures/solution.santa", env!("CARGO_MANIFEST_DIR")))
        .assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"solution""#))
        .stdout(predicate::str::contains(r#""part_one":"#))
        .stdout(predicate::str::contains(r#""part_two":"#))
        .stdout(predicate::str::contains(r#""status":"complete""#));
}

#[test]
fn json_solution_single_part() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("json").arg("-e").arg("part_one: { 42 }").assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"solution""#))
        .stdout(predicate::str::contains(r#""part_one":"#))
        .stdout(predicate::str::contains(r#""value":"42""#))
        // part_two should not be present when not defined
        .stdout(predicate::str::contains(r#""part_two""#).not());
}

// ============================================================================
// JSON Error Tests
// ============================================================================

#[test]
fn json_error_runtime() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("json").arg("-e").arg(r#"1 * "x""#).assert();
    assert
        .code(2)
        .stdout(predicate::str::contains(r#""type":"error""#))
        .stdout(predicate::str::contains(r#""message":"#));
}

#[test]
fn json_error_parse() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("json").arg("-e").arg("1 ^ 2").assert();
    assert
        .code(2)
        .stdout(predicate::str::contains(r#""type":"error""#))
        .stdout(predicate::str::contains(r#""message":"#));
}

// ============================================================================
// JSON Test Tests
// ============================================================================

#[test]
fn json_test_passing() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg("-o")
        .arg("json")
        .arg("-t")
        .arg(format!("{}/fixtures/solution.santa", env!("CARGO_MANIFEST_DIR")))
        .assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"test""#))
        .stdout(predicate::str::contains(r#""success":true"#))
        .stdout(predicate::str::contains(r#""passed":1"#))
        .stdout(predicate::str::contains(r#""failed":0"#));
}

#[test]
fn json_test_failing() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg("-o")
        .arg("json")
        .arg("-t")
        .arg("-e")
        .arg(
            r#"
            part_one: { 99 }
            test: {
                input: "x"
                part_one: 42
            }
            "#,
        )
        .assert();
    assert
        .code(3)
        .stdout(predicate::str::contains(r#""type":"test""#))
        .stdout(predicate::str::contains(r#""success":false"#))
        .stdout(predicate::str::contains(r#""passed":false"#))
        .stdout(predicate::str::contains(r#""expected":"42""#))
        .stdout(predicate::str::contains(r#""actual":"99""#));
}

#[test]
fn json_test_skipped() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg("-o")
        .arg("json")
        .arg("-t")
        .arg(format!(
            "{}/fixtures/solution_with_slow_test.santa",
            env!("CARGO_MANIFEST_DIR")
        ))
        .assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"test""#))
        .stdout(predicate::str::contains(r#""skipped":1"#))
        .stdout(predicate::str::contains(r#""status":"skipped""#));
}

#[test]
fn json_test_skipped_included_with_slow_flag() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg("-o")
        .arg("json")
        .arg("-t")
        .arg("-s")
        .arg(format!(
            "{}/fixtures/solution_with_slow_test.santa",
            env!("CARGO_MANIFEST_DIR")
        ))
        .assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"test""#))
        .stdout(predicate::str::contains(r#""skipped":0"#))
        .stdout(predicate::str::contains(r#""passed":2"#));
}

// ============================================================================
// JSONL Output Format Tests
// ============================================================================

#[test]
fn jsonl_script_simple() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("jsonl").arg("-e").arg("1 + 2").assert();
    // First line is initial state
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"script""#))
        .stdout(predicate::str::contains(r#""status":"pending""#))
        // Patches include running and complete
        .stdout(predicate::str::contains(r#""op":"replace""#))
        .stdout(predicate::str::contains(r#""/status""#))
        .stdout(predicate::str::contains(r#""running""#))
        .stdout(predicate::str::contains(r#""complete""#));
}

#[test]
fn jsonl_solution() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("jsonl").arg("-e").arg("part_one: { 42 }").assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"solution""#))
        .stdout(predicate::str::contains(r#""/part_one/status""#))
        .stdout(predicate::str::contains(r#""/part_one/value""#));
}

#[test]
fn jsonl_error() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("jsonl").arg("-e").arg(r#"1 * "x""#).assert();
    assert
        .code(2)
        .stdout(predicate::str::contains(r#""type":"script""#))
        .stdout(predicate::str::contains(r#""/error""#))
        .stdout(predicate::str::contains(r#""message""#));
}

#[test]
fn jsonl_test() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd
        .arg("-o")
        .arg("jsonl")
        .arg("-t")
        .arg(format!("{}/fixtures/solution.santa", env!("CARGO_MANIFEST_DIR")))
        .assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""type":"test""#))
        .stdout(predicate::str::contains(r#""/tests/0/status""#))
        .stdout(predicate::str::contains(r#""/summary/passed""#));
}

// ============================================================================
// JSON Version Output Tests
// ============================================================================

#[test]
fn json_version_output() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("json").arg("--version").assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""reindeer":"Dasher""#))
        .stdout(predicate::str::contains(r#""version":"#));
}

#[test]
fn jsonl_version_output() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("jsonl").arg("--version").assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""reindeer":"Dasher""#))
        .stdout(predicate::str::contains(r#""version":"#));
}

#[test]
fn json_version_output_flag_order_reversed() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("--version").arg("-o").arg("json").assert();
    assert
        .success()
        .stdout(predicate::str::contains(r#""reindeer":"Dasher""#))
        .stdout(predicate::str::contains(r#""version":"#));
}

// ============================================================================
// Output Mode Validation Tests
// ============================================================================

#[test]
fn invalid_output_mode() {
    let mut cmd = Command::cargo_bin("santa-cli").unwrap();
    let assert = cmd.arg("-o").arg("xml").arg("-e").arg("1").assert();
    assert.code(1).stderr(predicate::str::contains("Invalid output format"));
}
