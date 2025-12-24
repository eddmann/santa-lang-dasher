//! Dasher CLI - Santa-lang LLVM Compiler
//!
//! Usage:
//!   dasher <SCRIPT>           Run solution file
//!   dasher -t <SCRIPT>        Run tests (exclude @slow)
//!   dasher -t -s <SCRIPT>     Run tests (include @slow)
//!   dasher -e <SCRIPT>        Compile to executable (same name as script)

use clap::Parser;
use std::path::PathBuf;
use std::process::ExitCode;

use santa_lang::lexer::lex;
use santa_lang::parser::Parser as SantaParser;
use santa_lang::runner::{Runner, RunnerConfig};

/// Dasher - Santa-lang LLVM Compiler
#[derive(Parser, Debug)]
#[command(name = "dasher")]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The script file to run
    script: PathBuf,

    /// Run tests instead of the solution
    #[arg(short = 't', long = "test")]
    test_mode: bool,

    /// Include @slow tests (only with -t)
    #[arg(short = 's', long = "slow")]
    include_slow: bool,

    /// Emit executable (compile only, output in same directory as script)
    #[arg(short = 'e', long = "emit")]
    emit: bool,
}

fn main() -> ExitCode {
    let args = Args::parse();

    // Read the script file
    let source = match std::fs::read_to_string(&args.script) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading file {:?}: {}", args.script, e);
            return ExitCode::from(1);
        }
    };

    // Emit mode: compile to executable and exit (don't run)
    if args.emit {
        use santa_lang::codegen::pipeline::Compiler;

        // Output path: same directory as script, same name without extension
        let emit_path = args.script.with_extension("");

        // Parse first to check if it's a solution file
        let tokens = match lex(&source) {
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

        // Check if it's a solution file (has part_one/part_two sections)
        let runner = Runner::new();
        let final_source = if runner.is_script_mode(&program) {
            // Script mode: compile source directly
            source.clone()
        } else {
            // Solution mode: use Runner to generate executable source
            runner.generate_source(&program)
        };

        let compiler = Compiler::new();
        if let Err(e) = compiler.compile_to_executable(&final_source, &emit_path) {
            eprintln!("Compilation error: {:?}", e);
            return ExitCode::from(2);
        }
        println!("Compiled to: {}", emit_path.display());
        return ExitCode::SUCCESS;
    }

    // Lex and parse
    let tokens = match lex(&source) {
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

    // Create runner with configuration
    let config = RunnerConfig {
        include_slow: args.include_slow,
    };
    let runner = Runner::with_config(config);

    // Validate the program
    if let Err(e) = runner.validate_program(&program) {
        eprintln!("Program validation error: {:?}", e);
        return ExitCode::from(2);
    }

    if args.test_mode {
        // Test mode: run tests
        match runner.execute_tests(&program) {
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
                        let actual = result.part_one_actual.as_ref()
                            .map(santa_lang::runtime::builtins::format_value)
                            .unwrap_or_else(|| "nil".to_string());
                        if passed {
                            println!("Part 1: {} \x1b[32m✔\x1b[0m", actual);
                        } else {
                            let expected = result.part_one_expected.as_ref()
                                .map(santa_lang::runtime::builtins::format_value)
                                .unwrap_or_else(|| "nil".to_string());
                            println!(
                                "Part 1: {} \x1b[31m✘ (Expected: {})\x1b[0m",
                                actual, expected
                            );
                            exit_code = 3;
                        }
                    }

                    // Check part_two
                    if let Some(passed) = result.part_two_passed {
                        let actual = result.part_two_actual.as_ref()
                            .map(santa_lang::runtime::builtins::format_value)
                            .unwrap_or_else(|| "nil".to_string());
                        if passed {
                            println!("Part 2: {} \x1b[32m✔\x1b[0m", actual);
                        } else {
                            let expected = result.part_two_expected.as_ref()
                                .map(santa_lang::runtime::builtins::format_value)
                                .unwrap_or_else(|| "nil".to_string());
                            println!(
                                "Part 2: {} \x1b[31m✘ (Expected: {})\x1b[0m",
                                actual, expected
                            );
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
    } else {
        // Solution mode: execute the solution
        if runner.is_script_mode(&program) {
            // Script mode: compile and run directly, showing all output
            use santa_lang::codegen::pipeline::Compiler;
            use std::process::Command;

            let temp_dir = std::env::temp_dir();
            let exe_path = temp_dir.join(format!("santa_script_{}", std::process::id()));

            let compiler = Compiler::new();
            if let Err(e) = compiler.compile_to_executable(&source, &exe_path) {
                eprintln!("Compilation error: {:?}", e);
                return ExitCode::from(2);
            }

            let status = Command::new(&exe_path)
                .status()
                .expect("Failed to run compiled program");

            std::fs::remove_file(&exe_path).ok();

            if status.success() {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(status.code().unwrap_or(1) as u8)
            }
        } else {
            match runner.execute_solution(&program) {
                Ok(result) => {
                    if let Some(ref part_one) = result.part_one {
                        let time_ms = result.part_one_time
                            .map(|d| d.as_millis())
                            .unwrap_or(0);
                        println!(
                            "Part 1: \x1b[32m{}\x1b[0m \x1b[90m{}ms\x1b[0m",
                            santa_lang::runtime::builtins::format_value(part_one),
                            time_ms
                        );
                    }
                    if let Some(ref part_two) = result.part_two {
                        let time_ms = result.part_two_time
                            .map(|d| d.as_millis())
                            .unwrap_or(0);
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
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_args_run_mode() {
        let args = Args::try_parse_from(["dasher", "test.santa"]).unwrap();
        assert!(!args.test_mode);
        assert!(!args.include_slow);
        assert_eq!(args.script, PathBuf::from("test.santa"));
    }

    #[test]
    fn parse_args_test_mode() {
        let args = Args::try_parse_from(["dasher", "-t", "test.santa"]).unwrap();
        assert!(args.test_mode);
        assert!(!args.include_slow);
    }

    #[test]
    fn parse_args_test_mode_with_slow() {
        let args = Args::try_parse_from(["dasher", "-t", "-s", "test.santa"]).unwrap();
        assert!(args.test_mode);
        assert!(args.include_slow);
    }

    #[test]
    fn parse_args_long_flags() {
        let args = Args::try_parse_from(["dasher", "--test", "--slow", "test.santa"]).unwrap();
        assert!(args.test_mode);
        assert!(args.include_slow);
    }

    #[test]
    fn parse_args_emit_mode() {
        let args = Args::try_parse_from(["dasher", "-e", "test.santa"]).unwrap();
        assert!(args.emit);
        assert_eq!(args.script, PathBuf::from("test.santa"));
    }

    #[test]
    fn parse_args_emit_mode_long() {
        let args = Args::try_parse_from(["dasher", "--emit", "path/to/script.santa"]).unwrap();
        assert!(args.emit);
        assert_eq!(args.script, PathBuf::from("path/to/script.santa"));
    }
}
