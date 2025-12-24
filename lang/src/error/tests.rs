use super::*;
use crate::codegen::compiler::CompileError as CodegenCompileError;
use crate::codegen::pipeline::CompileError as PipelineCompileError;
use crate::lexer::LexError;
use crate::parser::ParseError;
use crate::runner::RunnerError;
use expect_test::expect;

fn pos(line: u32, column: u32) -> Position {
    Position::new(line, column)
}

fn span(start_line: u32, start_col: u32, end_line: u32, end_col: u32) -> Span {
    Span::new(pos(start_line, start_col), pos(end_line, end_col))
}

#[test]
fn lex_error_display() {
    let err = SantaError::lex("Unexpected character '?'", pos(1, 5));
    let display = format!("{}", err);
    expect![[r#"LexError at 1:5: Unexpected character '?'"#]].assert_eq(&display);
}

#[test]
fn parse_error_display() {
    let err = SantaError::parse("Expected ']' to close list", span(3, 10, 3, 12));
    let display = format!("{}", err);
    expect![[r#"ParseError at 3:10: Expected ']' to close list"#]].assert_eq(&display);
}

#[test]
fn compile_error_with_span_display() {
    let err = SantaError::compile("Undefined variable 'x'", span(5, 1, 5, 2));
    let display = format!("{}", err);
    expect![[r#"CompileError at 5:1: Undefined variable 'x'"#]].assert_eq(&display);
}

#[test]
fn compile_error_without_span_display() {
    let err = SantaError::compile_no_span("Failed to link runtime library");
    let display = format!("{}", err);
    expect![[r#"CompileError: Failed to link runtime library"#]].assert_eq(&display);
}

#[test]
fn runtime_error_display() {
    let err = SantaError::runtime("Division by zero");
    let display = format!("{}", err);
    expect![[r#"RuntimeError: Division by zero"#]].assert_eq(&display);
}

#[test]
fn runtime_error_with_stack_trace_display() {
    let stack_trace = vec![
        StackFrame {
            function: "divide".to_string(),
            span: Some(span(10, 5, 10, 15)),
        },
        StackFrame {
            function: "calculate".to_string(),
            span: Some(span(20, 3, 20, 20)),
        },
        StackFrame {
            function: "<main>".to_string(),
            span: None,
        },
    ];
    let err = SantaError::runtime_with_trace("Division by zero", stack_trace);
    let display = format!("{}", err);
    expect![[r#"RuntimeError: Division by zero
Stack trace:
  0: divide at 10:5
  1: calculate at 20:3
  2: <main>
"#]]
    .assert_eq(&display);
}

#[test]
fn error_kind() {
    assert_eq!(SantaError::lex("test", pos(1, 1)).kind(), "LexError");
    assert_eq!(
        SantaError::parse("test", span(1, 1, 1, 1)).kind(),
        "ParseError"
    );
    assert_eq!(
        SantaError::compile("test", span(1, 1, 1, 1)).kind(),
        "CompileError"
    );
    assert_eq!(SantaError::runtime("test").kind(), "RuntimeError");
}

#[test]
fn error_message() {
    let err = SantaError::lex("test message", pos(1, 1));
    assert_eq!(err.message(), "test message");
}

#[test]
fn error_position() {
    let lex_err = SantaError::lex("test", pos(5, 10));
    assert_eq!(lex_err.position(), Some(pos(5, 10)));

    let parse_err = SantaError::parse("test", span(3, 7, 3, 10));
    assert_eq!(parse_err.position(), Some(pos(3, 7)));

    let compile_err = SantaError::compile("test", span(2, 1, 2, 5));
    assert_eq!(compile_err.position(), Some(pos(2, 1)));

    let compile_err_no_span = SantaError::compile_no_span("test");
    assert_eq!(compile_err_no_span.position(), None);

    let runtime_err = SantaError::runtime("test");
    assert_eq!(runtime_err.position(), None);
}

// Tests for From conversions

#[test]
fn from_lex_error_unexpected_char() {
    let lex_err = LexError::UnexpectedCharacter {
        ch: '?',
        position: pos(3, 7),
    };
    let santa_err: SantaError = lex_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"LexError at 3:7: Unexpected character '?'"#]].assert_eq(&display);
}

#[test]
fn from_lex_error_unterminated_string() {
    let lex_err = LexError::UnterminatedString {
        position: pos(5, 10),
    };
    let santa_err: SantaError = lex_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"LexError at 5:10: Unterminated string literal"#]].assert_eq(&display);
}

#[test]
fn from_lex_error_invalid_number() {
    let lex_err = LexError::InvalidNumber {
        text: "1.2.3".to_string(),
        position: pos(1, 1),
    };
    let santa_err: SantaError = lex_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"LexError at 1:1: Invalid number: '1.2.3'"#]].assert_eq(&display);
}

#[test]
fn from_parse_error() {
    let parse_err = ParseError {
        message: "Expected ']' after list elements".to_string(),
        line: 10,
        column: 15,
    };
    let santa_err: SantaError = parse_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"ParseError at 10:15: Expected ']' after list elements"#]].assert_eq(&display);
}

#[test]
fn from_codegen_compile_error() {
    let compile_err = CodegenCompileError::UnsupportedExpression("Spread".to_string());
    let santa_err: SantaError = compile_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"CompileError: Unsupported expression: Spread"#]].assert_eq(&display);
}

#[test]
fn from_pipeline_compile_error() {
    let pipeline_err = PipelineCompileError::LinkError("libsanta_lang.a not found".to_string());
    let santa_err: SantaError = pipeline_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"CompileError: Link error: libsanta_lang.a not found"#]].assert_eq(&display);
}

#[test]
fn from_runner_error_duplicate_input() {
    let runner_err = RunnerError::DuplicateInput;
    let santa_err: SantaError = runner_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"RuntimeError: Expected a single 'input' section"#]].assert_eq(&display);
}

#[test]
fn from_runner_error_runtime() {
    let runner_err = RunnerError::RuntimeError("Failed to execute".to_string());
    let santa_err: SantaError = runner_err.into();
    let display = format!("{}", santa_err);
    expect![[r#"RuntimeError: Failed to execute"#]].assert_eq(&display);
}
