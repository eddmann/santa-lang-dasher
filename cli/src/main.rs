//! Dasher CLI - Santa-lang LLVM Compiler
//!
//! Usage:
//!   dasher <SCRIPT>           Run solution file
//!   dasher -t <SCRIPT>        Run tests (exclude @slow)
//!   dasher -t -s <SCRIPT>     Run tests (include @slow)

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
                let mut all_passed = true;
                for (i, result) in results.iter().enumerate() {
                    let test_num = i + 1;

                    // Check part_one
                    if let Some(passed) = result.part_one_passed {
                        if passed {
                            println!("Test {}: part_one ✓", test_num);
                        } else {
                            let actual = result.part_one_actual.as_ref()
                                .map(santa_lang::runtime::builtins::format_value)
                                .unwrap_or_else(|| "nil".to_string());
                            println!("Test {}: part_one ✗ (got {})", test_num, actual);
                            all_passed = false;
                        }
                    }

                    // Check part_two
                    if let Some(passed) = result.part_two_passed {
                        if passed {
                            println!("Test {}: part_two ✓", test_num);
                        } else {
                            let actual = result.part_two_actual.as_ref()
                                .map(santa_lang::runtime::builtins::format_value)
                                .unwrap_or_else(|| "nil".to_string());
                            println!("Test {}: part_two ✗ (got {})", test_num, actual);
                            all_passed = false;
                        }
                    }
                }

                if all_passed {
                    println!("\nAll tests passed!");
                    ExitCode::SUCCESS
                } else {
                    println!("\nSome tests failed.");
                    ExitCode::from(3)
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
            println!("Running solution...");

            match runner.execute_solution(&program) {
                Ok(result) => {
                    if let Some(part_one) = result.part_one {
                        println!("Part 1: {}", santa_lang::runtime::builtins::format_value(&part_one));
                    }
                    if let Some(part_two) = result.part_two {
                        println!("Part 2: {}", santa_lang::runtime::builtins::format_value(&part_two));
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
}
