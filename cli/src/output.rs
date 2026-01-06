//! CLI output formatting for JSON and JSONL modes.
//!
//! This module implements the CLI Output Format Specification (Section 16 of lang.txt).
//! It provides machine-readable output formats for integration with editors, CI systems,
//! and other tools.

use lang::error::SantaError;
use lang::runner::{SolutionResult, TestResult};
use serde::Serialize;
use std::io::{self, Write};

/// Output mode for CLI execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputMode {
    /// Human-readable output with ANSI colors (default)
    Text,
    /// Single JSON object after execution completes
    Json,
    /// Real-time streaming with JSON Lines
    Jsonl,
}

/// Console output entry from puts() calls.
#[derive(Debug, Clone, Serialize)]
pub struct ConsoleEntry {
    pub timestamp_ms: u64,
    pub message: String,
}

/// Error location with 1-indexed line and column.
#[derive(Debug, Clone, Serialize)]
pub struct ErrorLocation {
    pub line: u32,
    pub column: u32,
}

/// Stack frame for error traces.
#[derive(Debug, Clone, Serialize)]
pub struct StackFrame {
    pub function: String,
    pub line: u32,
    pub column: u32,
}

/// Part result for JSON output.
#[derive(Debug, Clone, Serialize)]
pub struct JsonPartResult {
    pub status: &'static str,
    pub value: String,
    pub duration_ms: u64,
}

/// Test part result for JSON output.
#[derive(Debug, Clone, Serialize)]
pub struct JsonTestPartResult {
    pub passed: bool,
    pub expected: String,
    pub actual: String,
}

/// Test case for JSON output.
#[derive(Debug, Clone, Serialize)]
pub struct JsonTestCase {
    pub index: u32,
    pub slow: bool,
    pub status: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub part_one: Option<JsonTestPartResult>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub part_two: Option<JsonTestPartResult>,
}

/// Test summary counts.
#[derive(Debug, Clone, Serialize)]
pub struct TestSummary {
    pub total: u32,
    pub passed: u32,
    pub failed: u32,
    pub skipped: u32,
}

/// JSON output for solution execution.
#[derive(Debug, Clone, Serialize)]
pub struct JsonSolutionOutput {
    #[serde(rename = "type")]
    pub output_type: &'static str,
    pub status: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub part_one: Option<JsonPartResult>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub part_two: Option<JsonPartResult>,
    pub console: Vec<ConsoleEntry>,
}

/// JSON output for script execution.
#[derive(Debug, Clone, Serialize)]
pub struct JsonScriptOutput {
    #[serde(rename = "type")]
    pub output_type: &'static str,
    pub status: &'static str,
    pub value: String,
    pub duration_ms: u64,
    pub console: Vec<ConsoleEntry>,
}

/// JSON output for test execution.
#[derive(Debug, Clone, Serialize)]
pub struct JsonTestOutput {
    #[serde(rename = "type")]
    pub output_type: &'static str,
    pub status: &'static str,
    pub success: bool,
    pub summary: TestSummary,
    pub tests: Vec<JsonTestCase>,
    pub console: Vec<ConsoleEntry>,
}

/// JSON output for errors.
#[derive(Debug, Clone, Serialize)]
pub struct JsonErrorOutput {
    #[serde(rename = "type")]
    pub output_type: &'static str,
    pub message: String,
    pub location: ErrorLocation,
    pub stack: Vec<StackFrame>,
}

/// Format a SantaError as JSON error output.
pub fn format_error_json(error: &SantaError) -> String {
    let (line, column) = match error {
        SantaError::LexError { position, .. } => (position.line, position.column),
        SantaError::ParseError { span, .. } => (span.start.line, span.start.column),
        SantaError::CompileError { span, .. } => span.map(|s| (s.start.line, s.start.column)).unwrap_or((1, 1)),
        SantaError::RuntimeError { stack_trace, .. } => {
            // Use first stack frame if available
            stack_trace
                .first()
                .and_then(|f| f.span.map(|s| (s.start.line, s.start.column)))
                .unwrap_or((1, 1))
        }
    };

    let stack: Vec<StackFrame> = match error {
        SantaError::RuntimeError { stack_trace, .. } => stack_trace
            .iter()
            .map(|f| {
                let (frame_line, frame_column) = f.span.map(|s| (s.start.line, s.start.column)).unwrap_or((1, 1));
                StackFrame {
                    function: f.function.clone(),
                    line: frame_line,
                    column: frame_column,
                }
            })
            .collect(),
        _ => Vec::new(), // Parse/compile errors have empty stack
    };

    let output = JsonErrorOutput {
        output_type: "error",
        message: error.message().to_string(),
        location: ErrorLocation { line, column },
        stack,
    };

    serde_json::to_string(&output).unwrap()
}

/// Format solution result as JSON.
pub fn format_solution_json(
    result: &SolutionResult,
    has_part_one: bool,
    has_part_two: bool,
    console: Vec<ConsoleEntry>,
) -> String {
    let output = JsonSolutionOutput {
        output_type: "solution",
        status: "complete",
        part_one: if has_part_one {
            result.part_one.as_ref().map(|v| JsonPartResult {
                status: "complete",
                value: lang::runtime::builtins::format_value(v),
                duration_ms: result.part_one_time.map(|d| d.as_millis() as u64).unwrap_or(0),
            })
        } else {
            None
        },
        part_two: if has_part_two {
            result.part_two.as_ref().map(|v| JsonPartResult {
                status: "complete",
                value: lang::runtime::builtins::format_value(v),
                duration_ms: result.part_two_time.map(|d| d.as_millis() as u64).unwrap_or(0),
            })
        } else {
            None
        },
        console,
    };

    serde_json::to_string(&output).unwrap()
}

/// Format script result as JSON.
pub fn format_script_json(value: &str, duration_ms: u64, console: Vec<ConsoleEntry>) -> String {
    let output = JsonScriptOutput {
        output_type: "script",
        status: "complete",
        value: value.to_string(),
        duration_ms,
        console,
    };

    serde_json::to_string(&output).unwrap()
}

/// Format test results as JSON.
pub fn format_test_json(
    test_results: &[TestResult],
    skipped_tests: &[(usize, bool)], // (index, slow) for skipped tests
    has_part_one: bool,
    has_part_two: bool,
    console: Vec<ConsoleEntry>,
) -> String {
    let mut passed = 0u32;
    let mut failed = 0u32;
    let skipped = skipped_tests.len() as u32;

    // Build test cases from both executed and skipped tests
    let mut all_tests: Vec<(usize, JsonTestCase)> = Vec::new();

    // Add executed test results
    for (i, tr) in test_results.iter().enumerate() {
        // Determine if test passed (all parts must pass)
        let part_one_passed = tr.part_one_passed.unwrap_or(true);
        let part_two_passed = tr.part_two_passed.unwrap_or(true);
        let all_passed = part_one_passed && part_two_passed;

        if all_passed {
            passed += 1;
        } else {
            failed += 1;
        }

        let test_case = JsonTestCase {
            index: (i + 1) as u32, // 1-indexed
            slow: tr.slow,
            status: "complete",
            part_one: if has_part_one && tr.part_one_passed.is_some() {
                Some(JsonTestPartResult {
                    passed: tr.part_one_passed.unwrap_or(false),
                    expected: tr
                        .part_one_expected
                        .as_ref()
                        .map(lang::runtime::builtins::format_value)
                        .unwrap_or_else(|| "nil".to_string()),
                    actual: tr
                        .part_one_actual
                        .as_ref()
                        .map(lang::runtime::builtins::format_value)
                        .unwrap_or_else(|| "nil".to_string()),
                })
            } else {
                None
            },
            part_two: if has_part_two && tr.part_two_passed.is_some() {
                Some(JsonTestPartResult {
                    passed: tr.part_two_passed.unwrap_or(false),
                    expected: tr
                        .part_two_expected
                        .as_ref()
                        .map(lang::runtime::builtins::format_value)
                        .unwrap_or_else(|| "nil".to_string()),
                    actual: tr
                        .part_two_actual
                        .as_ref()
                        .map(lang::runtime::builtins::format_value)
                        .unwrap_or_else(|| "nil".to_string()),
                })
            } else {
                None
            },
        };

        all_tests.push((i, test_case));
    }

    // Add skipped tests
    for (idx, slow) in skipped_tests {
        let test_case = JsonTestCase {
            index: (*idx + 1) as u32, // 1-indexed
            slow: *slow,
            status: "skipped",
            part_one: None,
            part_two: None,
        };
        all_tests.push((*idx, test_case));
    }

    // Sort by index to maintain original order
    all_tests.sort_by_key(|(idx, _)| *idx);
    let tests: Vec<JsonTestCase> = all_tests.into_iter().map(|(_, tc)| tc).collect();

    let total = tests.len() as u32;
    let success = failed == 0;

    let output = JsonTestOutput {
        output_type: "test",
        status: "complete",
        success,
        summary: TestSummary {
            total,
            passed,
            failed,
            skipped,
        },
        tests,
        console,
    };

    serde_json::to_string(&output).unwrap()
}

// ============================================================================
// JSONL Streaming Support
// ============================================================================

/// JSONL patch operation per RFC 6902.
#[derive(Debug, Clone, Serialize)]
pub struct JsonPatch {
    pub op: &'static str,
    pub path: String,
    pub value: serde_json::Value,
}

/// Initial state for JSONL solution streaming.
#[derive(Debug, Clone, Serialize)]
pub struct JsonlSolutionInitial {
    #[serde(rename = "type")]
    pub output_type: &'static str,
    pub status: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub part_one: Option<JsonlPartInitial>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub part_two: Option<JsonlPartInitial>,
    pub console: Vec<ConsoleEntry>,
}

/// Initial state for a part in JSONL streaming.
#[derive(Debug, Clone, Serialize)]
pub struct JsonlPartInitial {
    pub status: &'static str,
    pub value: Option<String>,
    pub duration_ms: Option<u64>,
}

/// Initial state for JSONL script streaming.
#[derive(Debug, Clone, Serialize)]
pub struct JsonlScriptInitial {
    #[serde(rename = "type")]
    pub output_type: &'static str,
    pub status: &'static str,
    pub value: Option<String>,
    pub duration_ms: Option<u64>,
    pub console: Vec<ConsoleEntry>,
}

/// Initial state for JSONL test streaming.
#[derive(Debug, Clone, Serialize)]
pub struct JsonlTestInitial {
    #[serde(rename = "type")]
    pub output_type: &'static str,
    pub status: &'static str,
    pub success: Option<bool>,
    pub summary: TestSummary,
    pub tests: Vec<JsonlTestCaseInitial>,
    pub console: Vec<ConsoleEntry>,
}

/// Initial test case state for JSONL streaming.
#[derive(Debug, Clone, Serialize)]
pub struct JsonlTestCaseInitial {
    pub index: u32,
    pub slow: bool,
    pub status: &'static str,
    pub part_one: Option<JsonTestPartResult>,
    pub part_two: Option<JsonTestPartResult>,
}

/// JSONL streaming writer.
pub struct JsonlWriter<W: Write> {
    writer: W,
}

impl<W: Write> JsonlWriter<W> {
    pub fn new(writer: W) -> Self {
        Self { writer }
    }

    /// Write initial state line.
    pub fn write_initial<T: Serialize>(&mut self, state: &T) -> io::Result<()> {
        let json = serde_json::to_string(state)?;
        writeln!(self.writer, "{}", json)?;
        self.writer.flush()
    }

    /// Write a patch array.
    pub fn write_patches(&mut self, patches: &[JsonPatch]) -> io::Result<()> {
        let json = serde_json::to_string(patches)?;
        writeln!(self.writer, "{}", json)?;
        self.writer.flush()
    }

    /// Create a replace patch.
    pub fn replace_patch(path: &str, value: impl Serialize) -> JsonPatch {
        JsonPatch {
            op: "replace",
            path: path.to_string(),
            value: serde_json::to_value(value).unwrap(),
        }
    }

    /// Create an add patch (for appending to arrays).
    pub fn add_patch(path: &str, value: impl Serialize) -> JsonPatch {
        JsonPatch {
            op: "add",
            path: path.to_string(),
            value: serde_json::to_value(value).unwrap(),
        }
    }
}

/// Determine if source is a solution (has part_one/part_two) or script.
pub fn is_solution_source(source: &str) -> (bool, bool) {
    // Simple heuristic: check if source contains part_one: or part_two:
    // This matches the runner's behavior
    let has_part_one = source.contains("part_one:");
    let has_part_two = source.contains("part_two:");
    (has_part_one, has_part_two)
}

/// Parse console entries from captured output.
/// Returns (console_entries, remaining_output).
pub fn parse_console_entries(output: &str) -> (Vec<ConsoleEntry>, String) {
    let mut console = Vec::new();
    let mut remaining = String::new();

    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("CONSOLE:") {
            if let Some((ts, msg)) = rest.split_once(':') {
                if let Ok(timestamp_ms) = ts.parse::<u64>() {
                    console.push(ConsoleEntry {
                        timestamp_ms,
                        message: msg.to_string(),
                    });
                    continue;
                }
            }
        }
        if !remaining.is_empty() {
            remaining.push('\n');
        }
        remaining.push_str(line);
    }

    (console, remaining)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_solution_source() {
        assert_eq!(is_solution_source("part_one: { 42 }"), (true, false));
        assert_eq!(is_solution_source("part_two: { 42 }"), (false, true));
        assert_eq!(is_solution_source("part_one: { 1 }\npart_two: { 2 }"), (true, true));
        assert_eq!(is_solution_source("1 + 2"), (false, false));
    }

    #[test]
    fn test_parse_console_entries_empty() {
        let (console, remaining) = parse_console_entries("");
        assert!(console.is_empty());
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_parse_console_entries_no_console() {
        let (console, remaining) = parse_console_entries("PART_ONE: 42\nPART_ONE_TIME: 100");
        assert!(console.is_empty());
        assert_eq!(remaining, "PART_ONE: 42\nPART_ONE_TIME: 100");
    }

    #[test]
    fn test_parse_console_entries_with_console() {
        let output = "CONSOLE:10:hello\nPART_ONE: 42\nCONSOLE:20:world";
        let (console, remaining) = parse_console_entries(output);
        assert_eq!(console.len(), 2);
        assert_eq!(console[0].timestamp_ms, 10);
        assert_eq!(console[0].message, "hello");
        assert_eq!(console[1].timestamp_ms, 20);
        assert_eq!(console[1].message, "world");
        assert_eq!(remaining, "PART_ONE: 42");
    }

    #[test]
    fn test_json_script_output_serialization() {
        let output = JsonScriptOutput {
            output_type: "script",
            status: "complete",
            value: "42".to_string(),
            duration_ms: 5,
            console: vec![],
        };
        let json = serde_json::to_string(&output).unwrap();
        assert!(json.contains(r#""type":"script""#));
        assert!(json.contains(r#""status":"complete""#));
        assert!(json.contains(r#""value":"42""#));
        assert!(json.contains(r#""duration_ms":5"#));
    }

    #[test]
    fn test_json_solution_output_omits_missing_parts() {
        let output = JsonSolutionOutput {
            output_type: "solution",
            status: "complete",
            part_one: Some(JsonPartResult {
                status: "complete",
                value: "42".to_string(),
                duration_ms: 5,
            }),
            part_two: None,
            console: vec![],
        };
        let json = serde_json::to_string(&output).unwrap();
        assert!(json.contains(r#""part_one":"#));
        assert!(!json.contains(r#""part_two""#));
    }

    #[test]
    fn test_json_error_output_serialization() {
        let output = JsonErrorOutput {
            output_type: "error",
            message: "Division by zero".to_string(),
            location: ErrorLocation { line: 15, column: 8 },
            stack: vec![StackFrame {
                function: "calculate".to_string(),
                line: 15,
                column: 8,
            }],
        };
        let json = serde_json::to_string(&output).unwrap();
        assert!(json.contains(r#""type":"error""#));
        assert!(json.contains(r#""message":"Division by zero""#));
        assert!(json.contains(r#""line":15"#));
        assert!(json.contains(r#""column":8"#));
    }

    #[test]
    fn test_json_test_output_serialization() {
        let output = JsonTestOutput {
            output_type: "test",
            status: "complete",
            success: true,
            summary: TestSummary {
                total: 2,
                passed: 1,
                failed: 0,
                skipped: 1,
            },
            tests: vec![
                JsonTestCase {
                    index: 1,
                    slow: false,
                    status: "complete",
                    part_one: Some(JsonTestPartResult {
                        passed: true,
                        expected: "6".to_string(),
                        actual: "6".to_string(),
                    }),
                    part_two: None,
                },
                JsonTestCase {
                    index: 2,
                    slow: true,
                    status: "skipped",
                    part_one: None,
                    part_two: None,
                },
            ],
            console: vec![],
        };
        let json = serde_json::to_string(&output).unwrap();
        assert!(json.contains(r#""type":"test""#));
        assert!(json.contains(r#""success":true"#));
        assert!(json.contains(r#""skipped":1"#));
        assert!(json.contains(r#""status":"skipped""#));
    }

    #[test]
    fn test_jsonl_writer() {
        let mut buffer = Vec::new();
        let mut writer = JsonlWriter::new(&mut buffer);

        let initial = JsonlScriptInitial {
            output_type: "script",
            status: "pending",
            value: None,
            duration_ms: None,
            console: vec![],
        };

        writer.write_initial(&initial).unwrap();

        let patches = vec![JsonlWriter::<Vec<u8>>::replace_patch("/status", "running")];

        writer.write_patches(&patches).unwrap();

        let output = String::from_utf8(buffer).unwrap();
        let lines: Vec<&str> = output.lines().collect();
        assert_eq!(lines.len(), 2);
        assert!(lines[0].contains(r#""status":"pending""#));
        assert!(lines[1].contains(r#""op":"replace""#));
        assert!(lines[1].contains(r#""/status""#));
    }
}
