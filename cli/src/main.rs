//! Santa-lang CLI - LLVM Compiler (Dasher)
//!
//! Usage:
//!   santa-cli <SCRIPT>           Run solution file
//!   santa-cli -e <CODE>          Evaluate inline script
//!   santa-cli -t <SCRIPT>        Run tests (exclude @slow)
//!   santa-cli -t -s <SCRIPT>     Run tests (include @slow)
//!   santa-cli -c <SCRIPT>        Compile to executable (same name as script)
//!   cat file | santa-cli         Read source from stdin

use clap::Parser;
use std::io::Read;
use std::path::PathBuf;
use std::process::ExitCode;

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
    santa-cli -h                    Show this help
    cat file | santa-cli            Read from stdin

OPTIONS:
    -e, --eval <CODE>    Evaluate inline script
    -t, --test           Run the solution's test suite
    -s, --slow           Include @slow tests (use with -t)
    -c, --compile        Compile to native executable
    -h, --help           Show this help message
    -v, --version        Display version information

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
}

/// Source of the script being executed
enum Source {
    /// From a file path
    File { path: PathBuf, content: String },
    /// From -e flag or stdin (no file path)
    Inline { content: String },
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

    // Parse the source
    let (program, source_content) = match parse_source(&source) {
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
        run_script(&source, source_content)
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
}
