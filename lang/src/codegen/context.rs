use crate::types::Type;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::values::PointerValue;
use inkwell::OptimizationLevel;
use std::collections::{HashMap, HashSet};
use std::path::Path;

/// Tracks state for tail-call optimization within a function
#[derive(Clone)]
pub struct TcoState<'ctx> {
    /// The name this function is bound to (for detecting self-recursive calls)
    pub self_name: Option<String>,
    /// The entry block to jump to for tail calls
    pub entry_block: BasicBlock<'ctx>,
    /// Parameter allocas (in order) for updating before tail call jump
    pub param_allocas: Vec<PointerValue<'ctx>>,
}

pub struct CodegenContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub current_block: Option<BasicBlock<'ctx>>,
    /// Maps variable names to their stack allocations
    pub variables: HashMap<String, PointerValue<'ctx>>,
    /// TCO state for the current function being compiled (if any)
    pub tco_state: Option<TcoState<'ctx>>,
    /// LLVM optimization level (O0, O1, O2, O3)
    opt_level: OptimizationLevel,
    /// Variables that are stored in mutable cells (for closure capture of mutable vars)
    /// When a variable is in this set, reads go through rt_cell_get and writes through rt_cell_set
    pub cell_variables: HashSet<String>,
    /// Type environment from type inference pass
    /// Maps variable names to their inferred types for optimized code generation
    pub type_env: HashMap<String, Type>,
}

impl<'ctx> CodegenContext<'ctx> {
    /// Create a new codegen context with default O2 optimization (Aggressive)
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        // Default to O2 (Aggressive) for good performance vs compile time tradeoff
        Self::with_optimization(context, module_name, OptimizationLevel::Aggressive)
    }

    /// Create a new codegen context with a specific optimization level
    pub fn with_optimization(
        context: &'ctx Context,
        module_name: &str,
        opt_level: OptimizationLevel,
    ) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();

        Self {
            context,
            module,
            builder,
            current_block: None,
            variables: HashMap::new(),
            tco_state: None,
            opt_level,
            cell_variables: HashSet::new(),
            type_env: HashMap::new(),
        }
    }

    /// Set the type environment from the type inference pass
    pub fn set_type_env(&mut self, type_env: HashMap<String, Type>) {
        self.type_env = type_env;
    }

    /// Pre-analyze top-level statements for self-referencing bindings
    ///
    /// This must be called before compiling statements at the top level
    /// (outside of a block) to properly handle patterns like:
    ///   let fib = memoize |n| { fib(n-1) + fib(n-2) }
    pub fn pre_analyze_statements(&mut self, stmts: &[crate::parser::ast::Stmt]) {
        use crate::parser::ast::{Pattern, Stmt};
        use std::collections::HashSet;

        // Collect all mutable variables
        let mut mutable_vars: HashSet<String> = HashSet::new();
        for stmt in stmts {
            if let Stmt::Let {
                mutable: true,
                pattern: Pattern::Identifier(name),
                ..
            } = stmt
            {
                mutable_vars.insert(name.clone());
            }
        }

        // Find mutable variables that are captured by nested closures
        let bound_vars: HashSet<String> = self.variables.keys().cloned().collect();
        for stmt in stmts {
            match stmt {
                Stmt::Let { value, .. } => {
                    let captures =
                        self.find_mutable_captures_in_expr(value, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
                Stmt::Expr(expr) | Stmt::Return(expr) | Stmt::Break(expr) => {
                    let captures =
                        self.find_mutable_captures_in_expr(expr, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
            }
        }

        // Find self-referencing bindings (e.g., let fib = memoize |n| { fib(...) })
        let self_refs = Self::find_self_referencing_bindings(stmts, &bound_vars);
        self.cell_variables.extend(self_refs);
    }

    /// Get the configured optimization level
    pub fn optimization_level(&self) -> OptimizationLevel {
        self.opt_level
    }

    /// Create a test function and position builder at its entry block
    /// This is useful for testing expression compilation
    pub fn create_test_function(&mut self) -> inkwell::values::FunctionValue<'ctx> {
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[], false);
        let function = self.module.add_function("test_fn", fn_type, None);
        let entry_block = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry_block);
        self.current_block = Some(entry_block);
        function
    }

    /// Get the LLVM IR as a string (for debugging)
    pub fn get_ir(&self) -> String {
        self.module.print_to_string().to_string()
    }

    /// Write the module to an object file
    pub fn write_object_file(&self, path: &Path) -> Result<(), String> {
        // Initialize native target
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|e| format!("Failed to initialize native target: {}", e))?;

        // Get native target triple
        let triple = TargetMachine::get_default_triple();

        // Get the target
        let target = Target::from_triple(&triple)
            .map_err(|e| format!("Failed to get target from triple: {}", e))?;

        // Create target machine with the configured optimization level
        let target_machine = target
            .create_target_machine(
                &triple,
                "generic",      // CPU
                "",             // Features
                self.opt_level, // Use configured optimization level
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or_else(|| "Failed to create target machine".to_string())?;

        // Write to object file
        target_machine
            .write_to_file(&self.module, FileType::Object, path)
            .map_err(|e| format!("Failed to write object file: {}", e))
    }

    /// Write the module to an assembly file (for debugging)
    pub fn write_assembly_file(&self, path: &Path) -> Result<(), String> {
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|e| format!("Failed to initialize native target: {}", e))?;

        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple)
            .map_err(|e| format!("Failed to get target from triple: {}", e))?;

        let target_machine = target
            .create_target_machine(
                &triple,
                "generic",
                "",
                self.opt_level, // Use configured optimization level
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or_else(|| "Failed to create target machine".to_string())?;

        target_machine
            .write_to_file(&self.module, FileType::Assembly, path)
            .map_err(|e| format!("Failed to write assembly file: {}", e))
    }
}
