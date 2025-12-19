//! AOC Runner module for executing santa-lang programs.
//!
//! The runner handles:
//! - Solution execution (input, part_one, part_two sections)
//! - Test execution with expected value comparison
//! - Script mode (no part sections)
//!
//! This is an AOT runner - it compiles programs to native code and executes them.

#[cfg(test)]
mod tests;

use crate::parser::ast::{Program, Section, Expr};
use crate::runtime::value::Value;
use crate::codegen::pipeline::Compiler;
use std::process::Command;
use std::time::Duration;

/// Error types for the runner
#[derive(Debug, Clone, PartialEq)]
pub enum RunnerError {
    /// Multiple input sections defined
    DuplicateInput,
    /// Multiple part_one sections defined
    DuplicatePartOne,
    /// Multiple part_two sections defined
    DuplicatePartTwo,
    /// Runtime error during execution
    RuntimeError(String),
}

/// Result of running a solution
#[derive(Debug, Clone)]
pub struct SolutionResult {
    pub part_one: Option<Value>,
    pub part_two: Option<Value>,
    pub part_one_time: Option<Duration>,
    pub part_two_time: Option<Duration>,
}

/// Result of running a single test
#[derive(Debug, Clone)]
pub struct TestResult {
    pub part_one_passed: Option<bool>,
    pub part_two_passed: Option<bool>,
    pub part_one_actual: Option<Value>,
    pub part_two_actual: Option<Value>,
    pub part_one_time: Option<Duration>,
    pub part_two_time: Option<Duration>,
    pub slow: bool,
}

/// Configuration for the runner
#[derive(Debug, Clone, Default)]
pub struct RunnerConfig {
    /// Include @slow tests in test execution
    pub include_slow: bool,
}

/// The AOC runner
pub struct Runner {
    config: RunnerConfig,
}

impl Runner {
    /// Create a new runner with default configuration
    pub fn new() -> Self {
        Self {
            config: RunnerConfig::default(),
        }
    }

    /// Create a new runner with the given configuration
    pub fn with_config(config: RunnerConfig) -> Self {
        Self { config }
    }

    /// Validate a program for duplicate sections
    pub fn validate_program(&self, program: &Program) -> Result<(), RunnerError> {
        let mut has_input = false;
        let mut has_part_one = false;
        let mut has_part_two = false;

        for section in &program.sections {
            match section {
                Section::Input(_) => {
                    if has_input {
                        return Err(RunnerError::DuplicateInput);
                    }
                    has_input = true;
                }
                Section::PartOne(_) => {
                    if has_part_one {
                        return Err(RunnerError::DuplicatePartOne);
                    }
                    has_part_one = true;
                }
                Section::PartTwo(_) => {
                    if has_part_two {
                        return Err(RunnerError::DuplicatePartTwo);
                    }
                    has_part_two = true;
                }
                Section::Test { .. } => {
                    // Multiple test sections are allowed
                }
            }
        }

        Ok(())
    }

    /// Check if the program is in script mode (no part sections)
    pub fn is_script_mode(&self, program: &Program) -> bool {
        !program.sections.iter().any(|s| {
            matches!(s, Section::PartOne(_) | Section::PartTwo(_))
        })
    }

    /// Get all test sections from a program
    pub fn get_tests<'a>(&self, program: &'a Program) -> Vec<&'a Section> {
        program
            .sections
            .iter()
            .filter(|s| matches!(s, Section::Test { .. }))
            .collect()
    }

    /// Filter tests based on configuration (exclude @slow unless configured)
    pub fn filter_tests<'a>(&self, tests: Vec<&'a Section>) -> Vec<&'a Section> {
        tests
            .into_iter()
            .filter(|s| {
                if let Section::Test { slow, .. } = s {
                    self.config.include_slow || !slow
                } else {
                    true
                }
            })
            .collect()
    }

    /// Execute all test sections in a program
    ///
    /// Each test section has its own input binding and expected values.
    /// Returns a TestResult for each test.
    pub fn execute_tests(&self, program: &Program) -> Result<Vec<TestResult>, RunnerError> {
        // First, validate the program
        self.validate_program(program)?;

        // Get part_one and part_two expressions from main sections
        let part_one_expr = self.get_part_one_section(program);
        let part_two_expr = self.get_part_two_section(program);

        // Get tests and filter based on config
        let tests = self.get_tests(program);
        let filtered = self.filter_tests(tests);

        let mut results = Vec::new();

        for test in filtered {
            if let Section::Test { input, part_one: expected_one, part_two: expected_two, slow } = test {
                let result = self.execute_single_test(
                    &program.statements,
                    input,
                    part_one_expr,
                    part_two_expr,
                    expected_one.as_ref(),
                    expected_two.as_ref(),
                    *slow,
                )?;
                results.push(result);
            }
        }

        Ok(results)
    }

    /// Execute a single test section
    #[allow(clippy::too_many_arguments)]
    fn execute_single_test(
        &self,
        statements: &[crate::parser::ast::Stmt],
        test_input: &Expr,
        part_one_expr: Option<&Expr>,
        part_two_expr: Option<&Expr>,
        expected_one: Option<&Expr>,
        expected_two: Option<&Expr>,
        slow: bool,
    ) -> Result<TestResult, RunnerError> {
        // Generate source for this test: bind input from test section, evaluate parts
        let source = self.generate_test_source(
            statements,
            test_input,
            part_one_expr,
            part_two_expr,
        );

        // Compile and execute
        let solution_result = self.compile_and_execute(&source)?;

        // Compare results with expected values
        let part_one_passed = match (solution_result.part_one.as_ref(), expected_one) {
            (Some(actual), Some(expected)) => {
                let expected_val = self.eval_expected_value(expected)?;
                Some(self.values_equal(actual, &expected_val))
            }
            (None, None) => None,
            (Some(_), None) => None,  // Has actual but no expected - not tested
            (None, Some(_)) => Some(false),  // Expected but didn't produce - failure
        };

        let part_two_passed = match (solution_result.part_two.as_ref(), expected_two) {
            (Some(actual), Some(expected)) => {
                let expected_val = self.eval_expected_value(expected)?;
                Some(self.values_equal(actual, &expected_val))
            }
            (None, None) => None,
            (Some(_), None) => None,
            (None, Some(_)) => Some(false),
        };

        Ok(TestResult {
            part_one_passed,
            part_two_passed,
            part_one_actual: solution_result.part_one,
            part_two_actual: solution_result.part_two,
            part_one_time: solution_result.part_one_time,
            part_two_time: solution_result.part_two_time,
            slow,
        })
    }

    /// Generate source code for a single test with timing
    fn generate_test_source(
        &self,
        statements: &[crate::parser::ast::Stmt],
        test_input: &Expr,
        part_one_expr: Option<&Expr>,
        part_two_expr: Option<&Expr>,
    ) -> String {
        let mut source = String::new();

        // Add top-level statements
        for stmt in statements {
            source.push_str(&self.stmt_to_source(stmt));
            // Let statements need semicolons
            if matches!(stmt, crate::parser::ast::Stmt::Let { .. }) {
                source.push(';');
            }
            source.push('\n');
        }

        // Bind input from test section
        source.push_str("let input = ");
        source.push_str(&self.expr_to_source(test_input));
        source.push_str(";\n");

        // Evaluate and print part_one if present with timing
        if let Some(part_one) = part_one_expr {
            source.push_str("let start_one = __time_nanos();\n");
            source.push_str("let result_part_one = ");
            source.push_str(&self.expr_to_source(part_one));
            source.push_str(";\n");
            source.push_str("let end_one = __time_nanos();\n");
            source.push_str("puts(\"PART_ONE:\", result_part_one);\n");
            source.push_str("puts(\"PART_ONE_TIME:\", end_one - start_one);\n");
        }

        // Evaluate and print part_two if present with timing
        if let Some(part_two) = part_two_expr {
            source.push_str("let start_two = __time_nanos();\n");
            source.push_str("let result_part_two = ");
            source.push_str(&self.expr_to_source(part_two));
            source.push_str(";\n");
            source.push_str("let end_two = __time_nanos();\n");
            source.push_str("puts(\"PART_TWO:\", result_part_two);\n");
            source.push_str("puts(\"PART_TWO_TIME:\", end_two - start_two);\n");
        }

        source.push_str("0\n");
        source
    }

    /// Public wrapper for generate_test_source for debugging
    #[allow(dead_code)]
    pub fn generate_test_source_for_debugging(
        &self,
        statements: &[crate::parser::ast::Stmt],
        test_input: &Expr,
        part_one_expr: Option<&Expr>,
        part_two_expr: Option<&Expr>,
    ) -> String {
        self.generate_test_source(statements, test_input, part_one_expr, part_two_expr)
    }

    /// Evaluate an expected value expression to a Value
    ///
    /// For simple literals, we can evaluate them directly.
    /// For more complex expressions, we'd need to compile and execute.
    fn eval_expected_value(&self, expr: &Expr) -> Result<Value, RunnerError> {
        match expr {
            Expr::Integer(n) => Ok(Value::from_integer(*n)),
            Expr::Decimal(d) => Ok(Value::from_decimal(*d)),
            Expr::String(s) => Ok(Value::from_string(s)),
            Expr::Boolean(b) => Ok(Value::from_bool(*b)),
            Expr::Nil => Ok(Value::nil()),
            _ => {
                // For complex expressions, compile and execute them
                let source = format!("puts(\"RESULT:\", {}); 0", self.expr_to_source(expr));
                let temp_dir = std::env::temp_dir();
                let unique_id = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_nanos())
                    .unwrap_or(0);
                let exe_path = temp_dir.join(format!("santa_eval_exec_{}", unique_id));

                let compiler = Compiler::new();
                compiler.compile_to_executable(&source, &exe_path)
                    .map_err(|e| RunnerError::RuntimeError(format!("Eval failed: {:?}", e)))?;

                let output = Command::new(&exe_path)
                    .output()
                    .map_err(|e| RunnerError::RuntimeError(format!("Eval execution failed: {}", e)))?;

                std::fs::remove_file(&exe_path).ok();

                let stdout = String::from_utf8_lossy(&output.stdout);
                for line in stdout.lines() {
                    if let Some(value_str) = line.strip_prefix("RESULT: ") {
                        return self.parse_value(value_str);
                    }
                }

                Err(RunnerError::RuntimeError("Could not evaluate expected value".to_string()))
            }
        }
    }

    /// Compare two values for equality
    fn values_equal(&self, a: &Value, b: &Value) -> bool {
        // Use the runtime's equality check
        use crate::runtime::operations::rt_eq;
        let result = rt_eq(*a, *b);
        result.as_bool().unwrap_or(false)
    }

    /// Execute a solution program (AOT compilation)
    ///
    /// This compiles the program sections to native code, runs the executable,
    /// and captures the results.
    pub fn execute_solution(&self, program: &Program) -> Result<SolutionResult, RunnerError> {
        // First, validate the program
        self.validate_program(program)?;

        // Extract sections
        let input_expr = self.get_input_section(program);
        let part_one_expr = self.get_part_one_section(program);
        let part_two_expr = self.get_part_two_section(program);

        // Generate source code for execution
        let source = self.generate_executable_source(
            &program.statements,
            input_expr,
            part_one_expr,
            part_two_expr,
        );

        // Compile and execute
        self.compile_and_execute(&source)
    }

    /// Get the input section expression if present
    fn get_input_section<'a>(&self, program: &'a Program) -> Option<&'a Expr> {
        program.sections.iter().find_map(|s| {
            if let Section::Input(expr) = s {
                Some(expr)
            } else {
                None
            }
        })
    }

    /// Get the part_one section expression if present
    fn get_part_one_section<'a>(&self, program: &'a Program) -> Option<&'a Expr> {
        program.sections.iter().find_map(|s| {
            if let Section::PartOne(expr) = s {
                Some(expr)
            } else {
                None
            }
        })
    }

    /// Get the part_two section expression if present
    fn get_part_two_section<'a>(&self, program: &'a Program) -> Option<&'a Expr> {
        program.sections.iter().find_map(|s| {
            if let Section::PartTwo(expr) = s {
                Some(expr)
            } else {
                None
            }
        })
    }

    /// Generate source code that evaluates sections and prints results with timing
    fn generate_executable_source(
        &self,
        statements: &[crate::parser::ast::Stmt],
        input_expr: Option<&Expr>,
        part_one_expr: Option<&Expr>,
        part_two_expr: Option<&Expr>,
    ) -> String {
        let mut source = String::new();

        // Add top-level statements
        for stmt in statements {
            source.push_str(&self.stmt_to_source(stmt));
            // Let statements need semicolons
            if matches!(stmt, crate::parser::ast::Stmt::Let { .. }) {
                source.push(';');
            }
            source.push('\n');
        }

        // Add input binding if present
        if let Some(input) = input_expr {
            source.push_str("let input = ");
            source.push_str(&self.expr_to_source(input));
            source.push_str(";\n");
        }

        // Evaluate and print part_one if present with timing
        if let Some(part_one) = part_one_expr {
            source.push_str("let start_one = __time_nanos();\n");
            source.push_str("let result_part_one = ");
            source.push_str(&self.expr_to_source(part_one));
            source.push_str(";\n");
            source.push_str("let end_one = __time_nanos();\n");
            source.push_str("puts(\"PART_ONE:\", result_part_one);\n");
            source.push_str("puts(\"PART_ONE_TIME:\", end_one - start_one);\n");
        }

        // Evaluate and print part_two if present with timing
        if let Some(part_two) = part_two_expr {
            source.push_str("let start_two = __time_nanos();\n");
            source.push_str("let result_part_two = ");
            source.push_str(&self.expr_to_source(part_two));
            source.push_str(";\n");
            source.push_str("let end_two = __time_nanos();\n");
            source.push_str("puts(\"PART_TWO:\", result_part_two);\n");
            source.push_str("puts(\"PART_TWO_TIME:\", end_two - start_two);\n");
        }

        // Return 0 at end
        source.push_str("0\n");
        source
    }

    /// Convert a statement back to source code
    fn stmt_to_source(&self, stmt: &crate::parser::ast::Stmt) -> String {
        match stmt {
            crate::parser::ast::Stmt::Expr(expr) => self.expr_to_source(expr),
            crate::parser::ast::Stmt::Let { mutable, pattern, value } => {
                let mut s = String::from("let ");
                if *mutable {
                    s.push_str("mut ");
                }
                s.push_str(&self.pattern_to_source(pattern));
                s.push_str(" = ");
                s.push_str(&self.expr_to_source(value));
                s
            }
            crate::parser::ast::Stmt::Return(expr) => {
                format!("return {}", self.expr_to_source(expr))
            }
            crate::parser::ast::Stmt::Break(expr) => {
                format!("break {}", self.expr_to_source(expr))
            }
        }
    }

    /// Convert an expression back to source code
    fn expr_to_source(&self, expr: &Expr) -> String {
        match expr {
            Expr::Integer(n) => n.to_string(),
            Expr::Decimal(d) => d.to_string(),
            Expr::String(s) => {
                // Escape special characters in string literals
                let escaped = s
                    .replace('\\', "\\\\")
                    .replace('"', "\\\"")
                    .replace('\n', "\\n")
                    .replace('\r', "\\r")
                    .replace('\t', "\\t");
                format!("\"{}\"", escaped)
            }
            Expr::Boolean(b) => b.to_string(),
            Expr::Nil => "nil".to_string(),
            Expr::Identifier(name) => name.clone(),
            Expr::Placeholder => "_".to_string(),
            Expr::Infix { left, op, right } => {
                // Always wrap in parentheses to preserve the original grouping
                // This ensures expressions like (a + b) % 3 aren't converted to a + b % 3
                format!(
                    "({} {} {})",
                    self.expr_to_source(left),
                    self.infix_op_to_source(op),
                    self.expr_to_source(right)
                )
            }
            Expr::Prefix { op, right } => {
                format!(
                    "{}{}",
                    self.prefix_op_to_source(op),
                    self.expr_to_source(right)
                )
            }
            Expr::Block(stmts) => {
                if stmts.is_empty() {
                    "{ }".to_string()
                } else if stmts.len() == 1 {
                    // Single statement block - no semicolon needed (returns value)
                    format!("{{ {} }}", self.stmt_to_source(&stmts[0]))
                } else {
                    // Multiple statements - semicolons between, but NOT after last
                    // The last statement returns its value
                    let mut s = String::from("{\n");
                    for (i, stmt) in stmts.iter().enumerate() {
                        s.push_str(&self.stmt_to_source(stmt));
                        if i < stmts.len() - 1 {
                            s.push_str(";\n");
                        } else {
                            s.push('\n');
                        }
                    }
                    s.push('}');
                    s
                }
            }
            Expr::List(elements) => {
                let elems: Vec<String> = elements.iter().map(|e| self.expr_to_source(e)).collect();
                format!("[{}]", elems.join(", "))
            }
            Expr::Call { function, args } => {
                let args_str: Vec<String> = args.iter().map(|e| self.expr_to_source(e)).collect();
                format!("{}({})", self.expr_to_source(function), args_str.join(", "))
            }
            Expr::If { condition, then_branch, else_branch } => {
                // For if expressions, we need to serialize blocks without trailing semicolons
                let then_str = self.block_or_expr_to_source(then_branch);
                let mut s = format!("if {} {}", self.expr_to_source(condition), then_str);
                if let Some(else_br) = else_branch {
                    let else_str = if matches!(else_br.as_ref(), Expr::If { .. }) {
                        // else if chains
                        self.expr_to_source(else_br)
                    } else {
                        self.block_or_expr_to_source(else_br)
                    };
                    s.push_str(&format!(" else {}", else_str));
                }
                s
            }
            Expr::Function { params, body } => {
                let params_str: Vec<String> = params
                    .iter()
                    .map(|p| self.pattern_to_source(&p.pattern))
                    .collect();
                format!("|{}| {}", params_str.join(", "), self.expr_to_source(body))
            }
            Expr::Range { start, end, inclusive } => {
                let start_str = self.expr_to_source(start);
                match end {
                    Some(end_expr) => {
                        if *inclusive {
                            format!("{}..={}", start_str, self.expr_to_source(end_expr))
                        } else {
                            format!("{}..{}", start_str, self.expr_to_source(end_expr))
                        }
                    }
                    None => format!("{}..", start_str),
                }
            }
            Expr::Set(elements) => {
                let elems: Vec<String> = elements.iter().map(|e| self.expr_to_source(e)).collect();
                format!("#{{{}}}", elems.join(", "))
            }
            Expr::Dict(entries) => {
                let entries_str: Vec<String> = entries
                    .iter()
                    .map(|(k, v)| format!("{}: {}", self.expr_to_source(k), self.expr_to_source(v)))
                    .collect();
                format!("#{{{}}}", entries_str.join(", "))
            }
            Expr::Index { collection, index } => {
                format!("{}[{}]", self.expr_to_source(collection), self.expr_to_source(index))
            }
            Expr::Match { subject, arms } => {
                let mut s = format!("match {} {{", self.expr_to_source(subject));
                for arm in arms {
                    // The arm body is already a Block expression from the parser,
                    // so use block_or_expr_to_source to avoid double-wrapping
                    let guard_str = if let Some(ref guard) = arm.guard {
                        format!(" if {}", self.expr_to_source(guard))
                    } else {
                        String::new()
                    };
                    s.push_str(&format!(
                        " {}{} ",
                        self.pattern_to_source(&arm.pattern),
                        guard_str
                    ));
                    s.push_str(&self.block_or_expr_to_source(&arm.body));
                }
                s.push_str(" }");
                s
            }
            Expr::Assignment { name, value } => {
                format!("{} = {}", name, self.expr_to_source(value))
            }
            Expr::Spread(inner) => {
                format!("..{}", self.expr_to_source(inner))
            }
            Expr::InfixCall { function, left, right } => {
                format!(
                    "{} `{}` {}",
                    self.expr_to_source(left),
                    function,
                    self.expr_to_source(right)
                )
            }
            _ => format!("/* unsupported expr: {:?} */", expr),
        }
    }

    /// Convert a block or expression to source for use in if/else bodies
    /// This serializes blocks without trailing semicolons (expression blocks return their last value)
    fn block_or_expr_to_source(&self, expr: &Expr) -> String {
        match expr {
            Expr::Block(stmts) => {
                if stmts.is_empty() {
                    "{ }".to_string()
                } else if stmts.len() == 1 {
                    // Single statement block - no semicolon needed
                    format!("{{ {} }}", self.stmt_to_source(&stmts[0]))
                } else {
                    // Multiple statements - semicolons between, but not after last
                    let mut s = String::from("{ ");
                    for (i, stmt) in stmts.iter().enumerate() {
                        s.push_str(&self.stmt_to_source(stmt));
                        if i < stmts.len() - 1 {
                            s.push_str("; ");
                        }
                    }
                    s.push_str(" }");
                    s
                }
            }
            _ => format!("{{ {} }}", self.expr_to_source(expr)),
        }
    }

    /// Convert infix operator to source
    fn infix_op_to_source(&self, op: &crate::parser::ast::InfixOp) -> &'static str {
        use crate::parser::ast::InfixOp;
        match op {
            InfixOp::Add => "+",
            InfixOp::Subtract => "-",
            InfixOp::Multiply => "*",
            InfixOp::Divide => "/",
            InfixOp::Modulo => "%",
            InfixOp::Equal => "==",
            InfixOp::NotEqual => "!=",
            InfixOp::LessThan => "<",
            InfixOp::LessThanOrEqual => "<=",
            InfixOp::GreaterThan => ">",
            InfixOp::GreaterThanOrEqual => ">=",
            InfixOp::And => "&&",
            InfixOp::Or => "||",
            InfixOp::Pipeline => "|>",
            InfixOp::Composition => ">>",
            InfixOp::Range => "..",
            InfixOp::RangeInclusive => "..=",
            InfixOp::InfixCall => "`",  // Note: this won't produce valid source for function calls
        }
    }

    /// Convert prefix operator to source
    fn prefix_op_to_source(&self, op: &crate::parser::ast::PrefixOp) -> &'static str {
        use crate::parser::ast::PrefixOp;
        match op {
            PrefixOp::Not => "!",
            PrefixOp::Negate => "-",
        }
    }

    /// Convert pattern to source
    fn pattern_to_source(&self, pattern: &crate::parser::ast::Pattern) -> String {
        use crate::parser::ast::Pattern;
        match pattern {
            Pattern::Wildcard => "_".to_string(),
            Pattern::Identifier(name) => name.clone(),
            Pattern::RestIdentifier(name) => format!("..{}", name),
            Pattern::Literal(lit) => self.literal_to_source(lit),
            Pattern::List(patterns) => {
                let pats: Vec<String> = patterns.iter().map(|p| self.pattern_to_source(p)).collect();
                format!("[{}]", pats.join(", "))
            }
            Pattern::Range { start, end, inclusive } => {
                if let Some(e) = end {
                    if *inclusive {
                        format!("{}..={}", start, e)
                    } else {
                        format!("{}..{}", start, e)
                    }
                } else {
                    format!("{}..", start)
                }
            }
        }
    }

    /// Convert literal to source
    fn literal_to_source(&self, lit: &crate::parser::ast::Literal) -> String {
        use crate::parser::ast::Literal;
        match lit {
            Literal::Integer(n) => n.to_string(),
            Literal::Decimal(d) => d.to_string(),
            Literal::String(s) => format!("\"{}\"", s),
            Literal::Boolean(b) => b.to_string(),
            Literal::Nil => "nil".to_string(),
        }
    }

    /// Compile and execute source, parsing output into SolutionResult
    fn compile_and_execute(&self, source: &str) -> Result<SolutionResult, RunnerError> {
        // Create temp directory for executable with unique filename
        let temp_dir = std::env::temp_dir();
        let unique_id = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let exe_path = temp_dir.join(format!("santa_runner_exec_{}", unique_id));

        // Compile
        let compiler = Compiler::new();
        compiler.compile_to_executable(source, &exe_path)
            .map_err(|e| RunnerError::RuntimeError(format!("Compilation failed: {:?}", e)))?;

        // Execute and capture output
        let output = Command::new(&exe_path)
            .output()
            .map_err(|e| RunnerError::RuntimeError(format!("Execution failed: {}", e)))?;

        // Clean up executable
        std::fs::remove_file(&exe_path).ok();

        // Parse output
        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_output(&stdout)
    }

    /// Parse execution output to extract part_one and part_two values with timing
    fn parse_output(&self, output: &str) -> Result<SolutionResult, RunnerError> {
        let mut part_one = None;
        let mut part_two = None;
        let mut part_one_time = None;
        let mut part_two_time = None;

        for line in output.lines() {
            if let Some(value_str) = line.strip_prefix("PART_ONE: ") {
                part_one = Some(self.parse_value(value_str)?);
            } else if let Some(value_str) = line.strip_prefix("PART_TWO: ") {
                part_two = Some(self.parse_value(value_str)?);
            } else if let Some(time_str) = line.strip_prefix("PART_ONE_TIME: ") {
                if let Ok(nanos) = time_str.trim().parse::<u64>() {
                    part_one_time = Some(Duration::from_nanos(nanos));
                }
            } else if let Some(time_str) = line.strip_prefix("PART_TWO_TIME: ") {
                if let Ok(nanos) = time_str.trim().parse::<u64>() {
                    part_two_time = Some(Duration::from_nanos(nanos));
                }
            }
        }

        Ok(SolutionResult { part_one, part_two, part_one_time, part_two_time })
    }

    /// Parse a string representation of a value
    fn parse_value(&self, s: &str) -> Result<Value, RunnerError> {
        let s = s.trim();
        if let Ok(n) = s.parse::<i64>() {
            Ok(Value::from_integer(n))
        } else if let Ok(d) = s.parse::<f64>() {
            Ok(Value::from_decimal(d))
        } else if s == "true" {
            Ok(Value::from_bool(true))
        } else if s == "false" {
            Ok(Value::from_bool(false))
        } else if s == "nil" {
            Ok(Value::nil())
        } else if s.starts_with('"') && s.ends_with('"') {
            // String value - strip quotes
            let inner = &s[1..s.len()-1];
            Ok(Value::from_string(inner))
        } else {
            // Treat as string if no other type matches
            Ok(Value::from_string(s))
        }
    }

    /// Test helper: generate source code for a program (for debugging)
    #[cfg(test)]
    pub fn test_generate_source(&self, program: &Program) -> String {
        let input_expr = self.get_input_section(program);
        let part_one_expr = self.get_part_one_section(program);
        let part_two_expr = self.get_part_two_section(program);

        self.generate_executable_source(
            &program.statements,
            input_expr,
            part_one_expr,
            part_two_expr,
        )
    }
}

impl Default for Runner {
    fn default() -> Self {
        Self::new()
    }
}
