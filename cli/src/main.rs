//! Santa-lang CLI - LLVM Compiler (Dasher)
//!
//! Usage:
//!   santa-cli <SCRIPT>           Run solution file
//!   santa-cli -e <CODE>          Evaluate inline script
//!   santa-cli -t <SCRIPT>        Run tests (exclude @slow)
//!   santa-cli -t -s <SCRIPT>     Run tests (include @slow)
//!   santa-cli -c <SCRIPT>        Compile to executable (same name as script)
//!   santa-cli -o <FORMAT>        Output format: text (default), json, jsonl
//!   cat file | santa-cli         Read source from stdin

mod output;

use clap::Parser;
use output::{
    format_error_json, format_script_json, format_solution_json, format_test_json, is_solution_source,
    parse_console_entries, JsonlPartInitial, JsonlScriptInitial, JsonlSolutionInitial, JsonlTestCaseInitial,
    JsonlTestInitial, JsonlWriter, OutputMode, TestSummary,
};
use std::io::{self, Read};
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use santa_lang::codegen::pipeline::Compiler;
use santa_lang::lexer::lex;
use santa_lang::parser::Parser as SantaParser;
use santa_lang::runner::{Runner, RunnerConfig};

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn print_help() {
    println!(
        r#"santa-lang CLI - Dasher {}

USAGE:
    santa-cli <SCRIPT>              Run solution file
    santa-cli -e <CODE>             Evaluate inline script
    santa-cli -t <SCRIPT>           Run test suite
    santa-cli -t -s <SCRIPT>        Run tests including @slow
    santa-cli -c <SCRIPT>           Compile to native executable
    santa-cli -o <FORMAT>           Output format (text, json, jsonl)
    santa-cli -h                    Show this help
    cat file | santa-cli            Read from stdin

OPTIONS:
    -e, --eval <CODE>       Evaluate inline script
    -t, --test              Run the solution's test suite
    -s, --slow              Include @slow tests (use with -t)
    -c, --compile           Compile to native executable
    -o, --output <FORMAT>   Output format: text (default), json, jsonl
    -h, --help              Show this help message
    -v, --version           Display version information

ENVIRONMENT:
    SANTA_CLI_SESSION_TOKEN    AOC session token for aoc:// URLs"#,
        VERSION
    );
}

fn print_version() {
    println!("santa-lang Dasher {}", VERSION);
}

/// Santa-lang LLVM Compiler (Dasher)
#[derive(Parser, Debug)]
#[command(name = "santa-cli")]
#[command(version, about = "Santa-lang LLVM Compiler", long_about = None)]
#[command(disable_version_flag = true, disable_help_flag = true)]
struct Args {
    /// Print version
    #[arg(short = 'v', long = "version")]
    version: bool,

    /// Show help message
    #[arg(short = 'h', long = "help")]
    help: bool,

    /// The script file to run (optional if using -e or stdin)
    script: Option<PathBuf>,

    /// Evaluate inline script
    #[arg(short = 'e', long = "eval")]
    eval: Option<String>,

    /// Run tests instead of the solution
    #[arg(short = 't', long = "test")]
    test_mode: bool,

    /// Include @slow tests (only with -t)
    #[arg(short = 's', long = "slow")]
    include_slow: bool,

    /// Compile to executable (output in same directory as script)
    #[arg(short = 'c', long = "compile")]
    compile: bool,

    /// Output format: text (default), json, jsonl
    #[arg(short = 'o', long = "output", value_name = "FORMAT")]
    output: Option<String>,
}

/// Source of the script being executed
enum Source {
    /// From a file path
    File { path: PathBuf, content: String },
    /// From -e flag or stdin (no file path)
    Inline { content: String },
}

/// Parse the output mode from CLI args.
fn parse_output_mode(args: &Args) -> Result<OutputMode, String> {
    match args.output.as_deref() {
        None | Some("text") => Ok(OutputMode::Text),
        Some("json") => Ok(OutputMode::Json),
        Some("jsonl") => Ok(OutputMode::Jsonl),
        Some(other) => Err(format!("Invalid output format: '{}'. Use: text, json, jsonl", other)),
    }
}

fn main() -> ExitCode {
    let args = Args::parse();

    // Handle --help flag
    if args.help {
        print_help();
        return ExitCode::SUCCESS;
    }

    // Handle --version flag
    if args.version {
        print_version();
        return ExitCode::SUCCESS;
    }

    // Parse output mode early
    let output_mode = match parse_output_mode(&args) {
        Ok(mode) => mode,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(1);
        }
    };

    // Determine source: -e flag > file argument > stdin
    let source = match get_source(&args) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(1);
        }
    };

    // Emit mode: compile to executable and exit (don't run)
    if args.compile {
        return compile_to_executable(&source);
    }

    // Set console capture env var for JSON/JSONL modes
    if output_mode != OutputMode::Text {
        std::env::set_var("DASHER_CONSOLE_CAPTURE", "1");
    }

    // Dispatch based on output mode
    match output_mode {
        OutputMode::Text => run_text_mode(&args, &source),
        OutputMode::Json => run_json_mode(&args, &source),
        OutputMode::Jsonl => run_jsonl_mode(&args, &source),
    }
}

/// Run in text mode (default, human-readable output).
fn run_text_mode(args: &Args, source: &Source) -> ExitCode {
    // Parse the source
    let (program, source_content) = match parse_source(source) {
        Ok(p) => p,
        Err(code) => return code,
    };

    // Create runner with configuration
    let config = RunnerConfig {
        include_slow: args.include_slow,
        script_path: source.path().map(|p| p.to_path_buf()),
    };
    let runner = Runner::with_config(config);

    // Validate the program
    if let Err(e) = runner.validate_program(&program) {
        eprintln!("Program validation error: {:?}", e);
        return ExitCode::from(2);
    }

    if args.test_mode {
        run_tests(&runner, &program)
    } else if runner.is_script_mode(&program) {
        run_script(source, source_content)
    } else {
        run_solution(&runner, &program)
    }
}

fn get_source(args: &Args) -> Result<Source, String> {
    // Priority: -e flag > file argument > stdin
    if let Some(ref eval_script) = args.eval {
        return Ok(Source::Inline {
            content: eval_script.clone(),
        });
    }

    if let Some(ref script_path) = args.script {
        let path = script_path
            .canonicalize()
            .map_err(|e| format!("Error resolving script path {:?}: {}", script_path, e))?;
        let content =
            std::fs::read_to_string(&path).map_err(|e| format!("Error reading file {:?}: {}", script_path, e))?;
        return Ok(Source::File { path, content });
    }

    // Try stdin if not a TTY
    if !atty::is(atty::Stream::Stdin) {
        let mut content = String::new();
        std::io::stdin()
            .read_to_string(&mut content)
            .map_err(|e| format!("Error reading from stdin: {}", e))?;
        return Ok(Source::Inline { content });
    }

    Err("No input provided. Use: santa-cli <SCRIPT>, santa-cli -e <CODE>, or pipe to stdin".to_string())
}

impl Source {
    fn content(&self) -> &str {
        match self {
            Source::File { content, .. } => content,
            Source::Inline { content } => content,
        }
    }

    fn path(&self) -> Option<&PathBuf> {
        match self {
            Source::File { path, .. } => Some(path),
            Source::Inline { .. } => None,
        }
    }
}

fn parse_source(source: &Source) -> Result<(santa_lang::parser::ast::Program, &str), ExitCode> {
    let content = source.content();

    let tokens = match lex(content) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Lexer error: {:?}", e);
            return Err(ExitCode::from(2));
        }
    };

    let mut parser = SantaParser::new(tokens);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Parse error: {:?}", e);
            return Err(ExitCode::from(2));
        }
    };

    Ok((program, content))
}

fn compile_to_executable(source: &Source) -> ExitCode {
    let path = match source.path() {
        Some(p) => p,
        None => {
            eprintln!("Error: --compile requires a file path");
            return ExitCode::from(1);
        }
    };

    let content = source.content();

    // Parse first to check if it's a solution file
    let tokens = match lex(content) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Lexer error: {:?}", e);
            return ExitCode::from(2);
        }
    };

    let mut parser = SantaParser::new(tokens);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Parse error: {:?}", e);
            return ExitCode::from(2);
        }
    };

    // Output path: same directory as script, same name without extension
    let emit_path = path.with_extension("");

    // Check if it's a solution file (has part_one/part_two sections)
    let runner = Runner::new();
    let final_source = if runner.is_script_mode(&program) {
        content.to_string()
    } else {
        // Solution mode: use Runner to generate executable source
        // If input is an AOC read, resolve it and bake into the binary
        let resolved_input = runner
            .get_aoc_url_from_input(&program)
            .and_then(|url| santa_lang::runtime::builtins::resolve_aoc_input(&url, path));
        runner.generate_source_with_resolved_input(&program, resolved_input.as_deref())
    };

    let compiler = Compiler::new();
    if let Err(e) = compiler.compile_to_executable(&final_source, &emit_path) {
        eprintln!("Compilation error: {:?}", e);
        return ExitCode::from(2);
    }
    println!("Compiled to: {}", emit_path.display());
    ExitCode::SUCCESS
}

fn run_script(source: &Source, content: &str) -> ExitCode {
    use std::process::Command;

    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join(format!("santa_script_{}", std::process::id()));

    let compiler = Compiler::new();
    if let Err(e) = compiler.compile_to_executable(content, &exe_path) {
        eprintln!("Compilation error: {:?}", e);
        return ExitCode::from(2);
    }

    let mut cmd = Command::new(&exe_path);
    // Set script path env var for AOC input resolution (if we have a file path)
    if let Some(path) = source.path() {
        cmd.env("DASHER_SCRIPT_PATH", path);
    }
    let status = cmd.status().expect("Failed to run compiled program");

    std::fs::remove_file(&exe_path).ok();

    if status.success() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(status.code().unwrap_or(1) as u8)
    }
}

fn run_solution(runner: &Runner, program: &santa_lang::parser::ast::Program) -> ExitCode {
    match runner.execute_solution(program) {
        Ok(result) => {
            if let Some(ref part_one) = result.part_one {
                let time_ms = result.part_one_time.map(|d| d.as_millis()).unwrap_or(0);
                println!(
                    "Part 1: \x1b[32m{}\x1b[0m \x1b[90m{}ms\x1b[0m",
                    santa_lang::runtime::builtins::format_value(part_one),
                    time_ms
                );
            }
            if let Some(ref part_two) = result.part_two {
                let time_ms = result.part_two_time.map(|d| d.as_millis()).unwrap_or(0);
                println!(
                    "Part 2: \x1b[32m{}\x1b[0m \x1b[90m{}ms\x1b[0m",
                    santa_lang::runtime::builtins::format_value(part_two),
                    time_ms
                );
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("Execution error: {:?}", e);
            ExitCode::from(2)
        }
    }
}

fn run_tests(runner: &Runner, program: &santa_lang::parser::ast::Program) -> ExitCode {
    match runner.execute_tests(program) {
        Ok(results) => {
            let mut exit_code = 0;

            for (i, result) in results.iter().enumerate() {
                let test_num = i + 1;

                // Print blank line between tests (not before first)
                if i > 0 {
                    println!();
                }

                // Print testcase header with optional slow marker
                if result.slow {
                    println!("\x1b[4mTestcase #{}\x1b[0m \x1b[33m(slow)\x1b[0m", test_num);
                } else {
                    println!("\x1b[4mTestcase #{}\x1b[0m", test_num);
                }

                // Check if no expectations
                if result.part_one_passed.is_none() && result.part_two_passed.is_none() {
                    println!("No expectations");
                    continue;
                }

                // Check part_one
                if let Some(passed) = result.part_one_passed {
                    let actual = result
                        .part_one_actual
                        .as_ref()
                        .map(santa_lang::runtime::builtins::format_value)
                        .unwrap_or_else(|| "nil".to_string());
                    if passed {
                        println!("Part 1: {} \x1b[32m✔\x1b[0m", actual);
                    } else {
                        let expected = result
                            .part_one_expected
                            .as_ref()
                            .map(santa_lang::runtime::builtins::format_value)
                            .unwrap_or_else(|| "nil".to_string());
                        println!("Part 1: {} \x1b[31m✘ (Expected: {})\x1b[0m", actual, expected);
                        exit_code = 3;
                    }
                }

                // Check part_two
                if let Some(passed) = result.part_two_passed {
                    let actual = result
                        .part_two_actual
                        .as_ref()
                        .map(santa_lang::runtime::builtins::format_value)
                        .unwrap_or_else(|| "nil".to_string());
                    if passed {
                        println!("Part 2: {} \x1b[32m✔\x1b[0m", actual);
                    } else {
                        let expected = result
                            .part_two_expected
                            .as_ref()
                            .map(santa_lang::runtime::builtins::format_value)
                            .unwrap_or_else(|| "nil".to_string());
                        println!("Part 2: {} \x1b[31m✘ (Expected: {})\x1b[0m", actual, expected);
                        exit_code = 3;
                    }
                }
            }

            if exit_code != 0 {
                ExitCode::from(exit_code)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            eprintln!("Test execution error: {:?}", e);
            ExitCode::from(2)
        }
    }
}

// ============================================================================
// JSON Mode
// ============================================================================

/// Run in JSON mode (batch output).
fn run_json_mode(args: &Args, source: &Source) -> ExitCode {
    let content = source.content();

    // Determine if it's a solution or script
    let (has_part_one, has_part_two) = is_solution_source(content);

    // Parse the source
    let (program, _source_content) = match parse_source_json(source) {
        Ok(p) => p,
        Err((exit_code, json)) => {
            println!("{}", json);
            return exit_code;
        }
    };

    // Create runner with configuration
    let config = RunnerConfig {
        include_slow: args.include_slow,
        script_path: source.path().map(|p| p.to_path_buf()),
    };
    let runner = Runner::with_config(config);

    // Validate the program
    if let Err(e) = runner.validate_program(&program) {
        let error = santa_lang::error::SantaError::from(e);
        println!("{}", format_error_json(&error));
        return ExitCode::from(2);
    }

    if args.test_mode {
        run_json_tests(&runner, &program, has_part_one, has_part_two)
    } else if runner.is_script_mode(&program) {
        run_json_script(source, content)
    } else {
        run_json_solution(&runner, &program, has_part_one, has_part_two)
    }
}

/// Parse source for JSON mode, returning JSON error on failure.
fn parse_source_json(source: &Source) -> Result<(santa_lang::parser::ast::Program, &str), (ExitCode, String)> {
    let content = source.content();

    let tokens = match lex(content) {
        Ok(t) => t,
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            return Err((ExitCode::from(2), format_error_json(&error)));
        }
    };

    let mut parser = SantaParser::new(tokens);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            return Err((ExitCode::from(2), format_error_json(&error)));
        }
    };

    Ok((program, content))
}

/// Run script in JSON mode.
fn run_json_script(source: &Source, content: &str) -> ExitCode {
    use std::process::Command;

    let start_time = Instant::now();
    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join(format!("santa_script_{}", std::process::id()));

    // Wrap script to print result for JSON output capture
    // Original script returns result as exit code, but we need it on stdout
    // Use a lambda to properly handle multi-statement scripts
    let wrapped_content = format!(
        "let __script_fn__ = || {{ {} }};\nlet __json_result__ = __script_fn__();\n__puts_repr(\"SCRIPT_RESULT:\", __json_result__);\n0",
        content.trim_end().trim_end_matches(';')
    );

    let compiler = Compiler::new();
    if let Err(e) = compiler.compile_to_executable(&wrapped_content, &exe_path) {
        let error = santa_lang::error::SantaError::from(e);
        println!("{}", format_error_json(&error));
        return ExitCode::from(2);
    }

    let mut cmd = Command::new(&exe_path);
    if let Some(path) = source.path() {
        cmd.env("DASHER_SCRIPT_PATH", path);
    }
    // Ensure console capture is enabled for subprocess
    cmd.env("DASHER_CONSOLE_CAPTURE", "1");

    let output = match cmd.output() {
        Ok(o) => o,
        Err(e) => {
            let error = santa_lang::error::SantaError::runtime(format!("Failed to run: {}", e));
            println!("{}", format_error_json(&error));
            std::fs::remove_file(&exe_path).ok();
            return ExitCode::from(2);
        }
    };

    std::fs::remove_file(&exe_path).ok();

    let duration_ms = start_time.elapsed().as_millis() as u64;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let (console, remaining) = parse_console_entries(&stdout);

    // Extract script result from SCRIPT_RESULT: prefix line
    let value = remaining
        .lines()
        .find(|line| line.starts_with("SCRIPT_RESULT: "))
        .map(|line| line.strip_prefix("SCRIPT_RESULT: ").unwrap_or(line).to_string())
        .unwrap_or_default();

    // Check stderr for error message - scripts use exit code for result value, not error
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !stderr.is_empty() {
        // Actual error occurred
        let error = santa_lang::error::SantaError::runtime(stderr.trim().to_string());
        println!("{}", format_error_json(&error));
        return ExitCode::from(2);
    }

    // Script succeeded - exit code is the result value (not an error indicator)
    println!("{}", format_script_json(&value, duration_ms, console));
    ExitCode::SUCCESS
}

/// Run solution in JSON mode.
fn run_json_solution(
    runner: &Runner,
    program: &santa_lang::parser::ast::Program,
    has_part_one: bool,
    has_part_two: bool,
) -> ExitCode {
    match runner.execute_solution(program) {
        Ok(result) => {
            // No console capture needed for runner (uses subprocess internally)
            let console = Vec::new();
            println!("{}", format_solution_json(&result, has_part_one, has_part_two, console));
            ExitCode::SUCCESS
        }
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            println!("{}", format_error_json(&error));
            ExitCode::from(2)
        }
    }
}

/// Run tests in JSON mode.
fn run_json_tests(
    runner: &Runner,
    program: &santa_lang::parser::ast::Program,
    has_part_one: bool,
    has_part_two: bool,
) -> ExitCode {
    // Get all tests and filter
    let all_tests = runner.get_tests(program);
    let filtered_tests = runner.filter_tests(all_tests.clone());

    // Determine skipped tests - compare by position in the all_tests list
    let mut skipped_tests = Vec::new();
    for (i, test) in all_tests.iter().enumerate() {
        let is_slow = matches!(test, santa_lang::parser::ast::Section::Test { slow: true, .. });
        // Check if this test (by index) is in the filtered list
        let is_in_filtered = filtered_tests.iter().any(|t| {
            // Compare if they point to the same section
            std::ptr::eq(*t as *const _, *test as *const _)
        });
        if !is_in_filtered {
            skipped_tests.push((i, is_slow));
        }
    }

    match runner.execute_tests(program) {
        Ok(results) => {
            let has_failures = results
                .iter()
                .any(|r| r.part_one_passed == Some(false) || r.part_two_passed == Some(false));
            let console = Vec::new();
            println!(
                "{}",
                format_test_json(&results, &skipped_tests, has_part_one, has_part_two, console)
            );
            if has_failures {
                ExitCode::from(3)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            println!("{}", format_error_json(&error));
            ExitCode::from(2)
        }
    }
}

// ============================================================================
// JSONL Mode
// ============================================================================

/// Run in JSONL mode (streaming output).
fn run_jsonl_mode(args: &Args, source: &Source) -> ExitCode {
    let content = source.content();
    let (has_part_one, has_part_two) = is_solution_source(content);

    // Parse the source
    let (program, _source_content) = match parse_source_jsonl(source) {
        Ok(p) => p,
        Err(exit_code) => return exit_code,
    };

    // Create runner with configuration
    let config = RunnerConfig {
        include_slow: args.include_slow,
        script_path: source.path().map(|p| p.to_path_buf()),
    };
    let runner = Runner::with_config(config);

    // Validate the program
    if let Err(e) = runner.validate_program(&program) {
        let error = santa_lang::error::SantaError::from(e);
        output_jsonl_error(&error);
        return ExitCode::from(2);
    }

    if args.test_mode {
        run_jsonl_tests(&runner, &program, has_part_one, has_part_two)
    } else if runner.is_script_mode(&program) {
        run_jsonl_script(source, content)
    } else {
        run_jsonl_solution(&runner, &program, has_part_one, has_part_two)
    }
}

/// Parse source for JSONL mode, outputting error state on failure.
fn parse_source_jsonl(source: &Source) -> Result<(santa_lang::parser::ast::Program, &str), ExitCode> {
    let content = source.content();

    let tokens = match lex(content) {
        Ok(t) => t,
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            output_jsonl_error(&error);
            return Err(ExitCode::from(2));
        }
    };

    let mut parser = SantaParser::new(tokens);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            output_jsonl_error(&error);
            return Err(ExitCode::from(2));
        }
    };

    Ok((program, content))
}

/// Output error in JSONL format (initial state + error patch).
fn output_jsonl_error(error: &santa_lang::error::SantaError) {
    let mut writer = JsonlWriter::new(io::stdout());

    // Initial state with error
    let initial = JsonlScriptInitial {
        output_type: "script",
        status: "error",
        value: None,
        duration_ms: None,
        console: vec![],
    };
    writer.write_initial(&initial).ok();

    // Error patch
    let error_json = serde_json::json!({
        "message": error.message(),
        "location": {
            "line": error.position().map(|p| p.line).unwrap_or(1),
            "column": error.position().map(|p| p.column).unwrap_or(1)
        },
        "stack": []
    });
    let patches = vec![JsonlWriter::<io::Stdout>::add_patch("/error", error_json)];
    writer.write_patches(&patches).ok();
}

/// Run script in JSONL mode.
fn run_jsonl_script(source: &Source, content: &str) -> ExitCode {
    use std::process::Command;

    let mut writer = JsonlWriter::new(io::stdout());

    // Write initial state
    let initial = JsonlScriptInitial {
        output_type: "script",
        status: "pending",
        value: None,
        duration_ms: None,
        console: vec![],
    };
    writer.write_initial(&initial).ok();

    // Status: running
    let patches = vec![JsonlWriter::<io::Stdout>::replace_patch("/status", "running")];
    writer.write_patches(&patches).ok();

    let start_time = Instant::now();
    let temp_dir = std::env::temp_dir();
    let exe_path = temp_dir.join(format!("santa_script_{}", std::process::id()));

    // Wrap script to print result for JSONL output capture
    // Use a lambda to properly handle multi-statement scripts
    let wrapped_content = format!(
        "let __script_fn__ = || {{ {} }};\nlet __json_result__ = __script_fn__();\n__puts_repr(\"SCRIPT_RESULT:\", __json_result__);\n0",
        content.trim_end().trim_end_matches(';')
    );

    let compiler = Compiler::new();
    if let Err(e) = compiler.compile_to_executable(&wrapped_content, &exe_path) {
        let error = santa_lang::error::SantaError::from(e);
        let error_json = serde_json::json!({
            "message": error.message(),
            "location": {"line": 1, "column": 1},
            "stack": []
        });
        let patches = vec![
            JsonlWriter::<io::Stdout>::replace_patch("/status", "error"),
            JsonlWriter::<io::Stdout>::add_patch("/error", error_json),
        ];
        writer.write_patches(&patches).ok();
        return ExitCode::from(2);
    }

    let mut cmd = Command::new(&exe_path);
    if let Some(path) = source.path() {
        cmd.env("DASHER_SCRIPT_PATH", path);
    }
    cmd.env("DASHER_CONSOLE_CAPTURE", "1");

    let output = match cmd.output() {
        Ok(o) => o,
        Err(e) => {
            std::fs::remove_file(&exe_path).ok();
            let error_json = serde_json::json!({
                "message": format!("Failed to run: {}", e),
                "location": {"line": 1, "column": 1},
                "stack": []
            });
            let patches = vec![
                JsonlWriter::<io::Stdout>::replace_patch("/status", "error"),
                JsonlWriter::<io::Stdout>::add_patch("/error", error_json),
            ];
            writer.write_patches(&patches).ok();
            return ExitCode::from(2);
        }
    };

    std::fs::remove_file(&exe_path).ok();

    let duration_ms = start_time.elapsed().as_millis() as u64;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let (console, remaining) = parse_console_entries(&stdout);

    // Extract script result from SCRIPT_RESULT: prefix line
    let value = remaining
        .lines()
        .find(|line| line.starts_with("SCRIPT_RESULT: "))
        .map(|line| line.strip_prefix("SCRIPT_RESULT: ").unwrap_or(line).to_string())
        .unwrap_or_default();

    // Output console entries
    for entry in &console {
        let patches = vec![JsonlWriter::<io::Stdout>::add_patch("/console/-", entry)];
        writer.write_patches(&patches).ok();
    }

    // Check stderr for error message - scripts use exit code for result value, not error
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !stderr.is_empty() {
        // Actual error occurred
        let error_json = serde_json::json!({
            "message": stderr.trim(),
            "location": {"line": 1, "column": 1},
            "stack": []
        });
        let patches = vec![
            JsonlWriter::<io::Stdout>::replace_patch("/status", "error"),
            JsonlWriter::<io::Stdout>::add_patch("/error", error_json),
        ];
        writer.write_patches(&patches).ok();
        return ExitCode::from(2);
    }

    // Script succeeded - exit code is the result value (not an error indicator)
    let patches = vec![
        JsonlWriter::<io::Stdout>::replace_patch("/status", "complete"),
        JsonlWriter::<io::Stdout>::replace_patch("/value", &value),
        JsonlWriter::<io::Stdout>::replace_patch("/duration_ms", duration_ms),
    ];
    writer.write_patches(&patches).ok();
    ExitCode::SUCCESS
}

/// Run solution in JSONL mode.
fn run_jsonl_solution(
    runner: &Runner,
    program: &santa_lang::parser::ast::Program,
    has_part_one: bool,
    has_part_two: bool,
) -> ExitCode {
    let mut writer = JsonlWriter::new(io::stdout());

    // Write initial state
    let initial = JsonlSolutionInitial {
        output_type: "solution",
        status: "pending",
        part_one: if has_part_one {
            Some(JsonlPartInitial {
                status: "pending",
                value: None,
                duration_ms: None,
            })
        } else {
            None
        },
        part_two: if has_part_two {
            Some(JsonlPartInitial {
                status: "pending",
                value: None,
                duration_ms: None,
            })
        } else {
            None
        },
        console: vec![],
    };
    writer.write_initial(&initial).ok();

    // Status: running
    let patches = vec![JsonlWriter::<io::Stdout>::replace_patch("/status", "running")];
    writer.write_patches(&patches).ok();

    match runner.execute_solution(program) {
        Ok(result) => {
            // Output part_one result
            if has_part_one {
                let patches = vec![JsonlWriter::<io::Stdout>::replace_patch("/part_one/status", "running")];
                writer.write_patches(&patches).ok();

                if let Some(ref value) = result.part_one {
                    let patches = vec![
                        JsonlWriter::<io::Stdout>::replace_patch("/part_one/status", "complete"),
                        JsonlWriter::<io::Stdout>::replace_patch(
                            "/part_one/value",
                            santa_lang::runtime::builtins::format_value(value),
                        ),
                        JsonlWriter::<io::Stdout>::replace_patch(
                            "/part_one/duration_ms",
                            result.part_one_time.map(|d| d.as_millis() as u64).unwrap_or(0),
                        ),
                    ];
                    writer.write_patches(&patches).ok();
                }
            }

            // Output part_two result
            if has_part_two {
                let patches = vec![JsonlWriter::<io::Stdout>::replace_patch("/part_two/status", "running")];
                writer.write_patches(&patches).ok();

                if let Some(ref value) = result.part_two {
                    let patches = vec![
                        JsonlWriter::<io::Stdout>::replace_patch("/part_two/status", "complete"),
                        JsonlWriter::<io::Stdout>::replace_patch(
                            "/part_two/value",
                            santa_lang::runtime::builtins::format_value(value),
                        ),
                        JsonlWriter::<io::Stdout>::replace_patch(
                            "/part_two/duration_ms",
                            result.part_two_time.map(|d| d.as_millis() as u64).unwrap_or(0),
                        ),
                    ];
                    writer.write_patches(&patches).ok();
                }
            }

            // Final status
            let patches = vec![JsonlWriter::<io::Stdout>::replace_patch("/status", "complete")];
            writer.write_patches(&patches).ok();

            ExitCode::SUCCESS
        }
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            let error_json = serde_json::json!({
                "message": error.message(),
                "location": {"line": 1, "column": 1},
                "stack": []
            });
            let patches = vec![
                JsonlWriter::<io::Stdout>::replace_patch("/status", "error"),
                JsonlWriter::<io::Stdout>::add_patch("/error", error_json),
            ];
            writer.write_patches(&patches).ok();
            ExitCode::from(2)
        }
    }
}

/// Run tests in JSONL mode.
fn run_jsonl_tests(
    runner: &Runner,
    program: &santa_lang::parser::ast::Program,
    has_part_one: bool,
    has_part_two: bool,
) -> ExitCode {
    let mut writer = JsonlWriter::new(io::stdout());

    // Get all tests and filter
    let all_tests = runner.get_tests(program);
    let filtered_tests = runner.filter_tests(all_tests.clone());
    let total = all_tests.len() as u32;
    let skipped = (all_tests.len() - filtered_tests.len()) as u32;

    // Build initial test case states
    let tests: Vec<JsonlTestCaseInitial> = all_tests
        .iter()
        .enumerate()
        .map(|(i, test)| {
            let is_slow = matches!(test, santa_lang::parser::ast::Section::Test { slow: true, .. });
            let is_in_filtered = filtered_tests.iter().any(|t| {
                std::ptr::eq(*t as *const _, *test as *const _)
            });
            JsonlTestCaseInitial {
                index: (i + 1) as u32,
                slow: is_slow,
                status: if is_in_filtered { "pending" } else { "skipped" },
                part_one: None,
                part_two: None,
            }
        })
        .collect();

    // Write initial state
    let initial = JsonlTestInitial {
        output_type: "test",
        status: "pending",
        success: None,
        summary: TestSummary {
            total,
            passed: 0,
            failed: 0,
            skipped,
        },
        tests,
        console: vec![],
    };
    writer.write_initial(&initial).ok();

    // Status: running
    let patches = vec![JsonlWriter::<io::Stdout>::replace_patch("/status", "running")];
    writer.write_patches(&patches).ok();

    match runner.execute_tests(program) {
        Ok(results) => {
            let mut passed = 0u32;
            let mut failed = 0u32;

            for (i, result) in results.iter().enumerate() {
                // Status: running this test
                let patches = vec![JsonlWriter::<io::Stdout>::replace_patch(
                    &format!("/tests/{}/status", i),
                    "running",
                )];
                writer.write_patches(&patches).ok();

                let part_one_passed = result.part_one_passed.unwrap_or(true);
                let part_two_passed = result.part_two_passed.unwrap_or(true);
                let test_passed = part_one_passed && part_two_passed;

                if test_passed {
                    passed += 1;
                } else {
                    failed += 1;
                }

                // Output part results
                let mut patches = vec![JsonlWriter::<io::Stdout>::replace_patch(
                    &format!("/tests/{}/status", i),
                    "complete",
                )];

                if has_part_one && result.part_one_passed.is_some() {
                    let part_result = serde_json::json!({
                        "passed": result.part_one_passed.unwrap_or(false),
                        "expected": result.part_one_expected.as_ref().map(santa_lang::runtime::builtins::format_value).unwrap_or_else(|| "nil".to_string()),
                        "actual": result.part_one_actual.as_ref().map(santa_lang::runtime::builtins::format_value).unwrap_or_else(|| "nil".to_string())
                    });
                    patches.push(JsonlWriter::<io::Stdout>::replace_patch(
                        &format!("/tests/{}/part_one", i),
                        part_result,
                    ));
                }

                if has_part_two && result.part_two_passed.is_some() {
                    let part_result = serde_json::json!({
                        "passed": result.part_two_passed.unwrap_or(false),
                        "expected": result.part_two_expected.as_ref().map(santa_lang::runtime::builtins::format_value).unwrap_or_else(|| "nil".to_string()),
                        "actual": result.part_two_actual.as_ref().map(santa_lang::runtime::builtins::format_value).unwrap_or_else(|| "nil".to_string())
                    });
                    patches.push(JsonlWriter::<io::Stdout>::replace_patch(
                        &format!("/tests/{}/part_two", i),
                        part_result,
                    ));
                }

                writer.write_patches(&patches).ok();
            }

            // Final status
            let patches = vec![
                JsonlWriter::<io::Stdout>::replace_patch("/status", "complete"),
                JsonlWriter::<io::Stdout>::replace_patch("/success", failed == 0),
                JsonlWriter::<io::Stdout>::replace_patch("/summary/passed", passed),
                JsonlWriter::<io::Stdout>::replace_patch("/summary/failed", failed),
            ];
            writer.write_patches(&patches).ok();

            if failed > 0 {
                ExitCode::from(3)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            let error = santa_lang::error::SantaError::from(e);
            let error_json = serde_json::json!({
                "message": error.message(),
                "location": {"line": 1, "column": 1},
                "stack": []
            });
            let patches = vec![
                JsonlWriter::<io::Stdout>::replace_patch("/status", "error"),
                JsonlWriter::<io::Stdout>::add_patch("/error", error_json),
            ];
            writer.write_patches(&patches).ok();
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_args_run_mode() {
        let args = Args::try_parse_from(["santa-cli", "test.santa"]).unwrap();
        assert!(!args.test_mode);
        assert!(!args.include_slow);
        assert_eq!(args.script, Some(PathBuf::from("test.santa")));
    }

    #[test]
    fn parse_args_test_mode() {
        let args = Args::try_parse_from(["santa-cli", "-t", "test.santa"]).unwrap();
        assert!(args.test_mode);
        assert!(!args.include_slow);
    }

    #[test]
    fn parse_args_test_mode_with_slow() {
        let args = Args::try_parse_from(["santa-cli", "-t", "-s", "test.santa"]).unwrap();
        assert!(args.test_mode);
        assert!(args.include_slow);
    }

    #[test]
    fn parse_args_long_flags() {
        let args = Args::try_parse_from(["santa-cli", "--test", "--slow", "test.santa"]).unwrap();
        assert!(args.test_mode);
        assert!(args.include_slow);
    }

    #[test]
    fn parse_args_compile_mode() {
        let args = Args::try_parse_from(["santa-cli", "-c", "test.santa"]).unwrap();
        assert!(args.compile);
        assert_eq!(args.script, Some(PathBuf::from("test.santa")));
    }

    #[test]
    fn parse_args_compile_mode_long() {
        let args = Args::try_parse_from(["santa-cli", "--compile", "path/to/script.santa"]).unwrap();
        assert!(args.compile);
        assert_eq!(args.script, Some(PathBuf::from("path/to/script.santa")));
    }

    #[test]
    fn parse_args_eval_mode() {
        let args = Args::try_parse_from(["santa-cli", "-e", "1 + 2"]).unwrap();
        assert_eq!(args.eval, Some("1 + 2".to_string()));
        assert!(args.script.is_none());
    }

    #[test]
    fn parse_args_eval_mode_long() {
        let args = Args::try_parse_from(["santa-cli", "--eval", "puts(42)"]).unwrap();
        assert_eq!(args.eval, Some("puts(42)".to_string()));
    }

    #[test]
    fn parse_args_output_json() {
        let args = Args::try_parse_from(["santa-cli", "-o", "json", "-e", "1 + 2"]).unwrap();
        assert_eq!(args.output, Some("json".to_string()));
    }

    #[test]
    fn parse_args_output_jsonl() {
        let args = Args::try_parse_from(["santa-cli", "-o", "jsonl", "-e", "1 + 2"]).unwrap();
        assert_eq!(args.output, Some("jsonl".to_string()));
    }

    #[test]
    fn parse_args_output_text() {
        let args = Args::try_parse_from(["santa-cli", "-o", "text", "-e", "1 + 2"]).unwrap();
        assert_eq!(args.output, Some("text".to_string()));
    }

    #[test]
    fn parse_args_output_long() {
        let args = Args::try_parse_from(["santa-cli", "--output", "json", "-e", "1 + 2"]).unwrap();
        assert_eq!(args.output, Some("json".to_string()));
    }

    #[test]
    fn parse_output_mode_default() {
        let args = Args::try_parse_from(["santa-cli", "-e", "1"]).unwrap();
        assert_eq!(parse_output_mode(&args), Ok(OutputMode::Text));
    }

    #[test]
    fn parse_output_mode_text() {
        let args = Args::try_parse_from(["santa-cli", "-o", "text", "-e", "1"]).unwrap();
        assert_eq!(parse_output_mode(&args), Ok(OutputMode::Text));
    }

    #[test]
    fn parse_output_mode_json() {
        let args = Args::try_parse_from(["santa-cli", "-o", "json", "-e", "1"]).unwrap();
        assert_eq!(parse_output_mode(&args), Ok(OutputMode::Json));
    }

    #[test]
    fn parse_output_mode_jsonl() {
        let args = Args::try_parse_from(["santa-cli", "-o", "jsonl", "-e", "1"]).unwrap();
        assert_eq!(parse_output_mode(&args), Ok(OutputMode::Jsonl));
    }

    #[test]
    fn parse_output_mode_invalid() {
        let args = Args::try_parse_from(["santa-cli", "-o", "xml", "-e", "1"]).unwrap();
        assert!(parse_output_mode(&args).is_err());
    }
}
