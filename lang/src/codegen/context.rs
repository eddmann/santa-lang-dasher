use crate::types::Type;
use inkwell::OptimizationLevel;
use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine};
use inkwell::values::PointerValue;
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
    /// Variables that were forward-declared (for mutual recursion).
    /// Used to distinguish from shadowed variables when compiling let bindings.
    pub forward_declared_variables: HashSet<String>,
    /// Variables that are mutable in the current scope (declared with `let mut`)
    pub mutable_variables: HashSet<String>,
    /// Depth of nested function compilation (0 = top-level)
    pub function_depth: usize,
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
    pub fn with_optimization(context: &'ctx Context, module_name: &str, opt_level: OptimizationLevel) -> Self {
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
            forward_declared_variables: HashSet::new(),
            mutable_variables: HashSet::new(),
            function_depth: 0,
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
                    let captures = self.find_mutable_captures_in_expr(value, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
                Stmt::Expr(expr) | Stmt::Return(expr) | Stmt::Break(expr) => {
                    let captures = self.find_mutable_captures_in_expr(expr, &mutable_vars, &bound_vars);
                    self.cell_variables.extend(captures);
                }
            }
        }

        // Find self-referencing bindings (e.g., let fib = memoize |n| { fib(...) })
        let self_refs = Self::find_self_referencing_bindings(stmts, &bound_vars);
        self.cell_variables.extend(self_refs);

        // Find forward references (mutual recursion between top-level functions)
        let forward_refs = Self::find_forward_references(stmts, &bound_vars);
        self.cell_variables.extend(forward_refs);
    }

    /// Forward-declare a top-level binding
    ///
    /// Creates an alloca for the variable and initializes it properly:
    /// - For cell variables: creates a cell containing nil
    /// - For regular variables: stores nil directly
    pub fn forward_declare_binding(&mut self, name: &str) {
        let i64_type = self.context.i64_type();
        let nil_value = i64_type.const_int(0b010, false);

        let alloca = self.builder.build_alloca(i64_type, name).unwrap();

        if self.cell_variables.contains(name) {
            // Create a cell containing nil
            let rt_cell_new = self.get_or_declare_runtime_fn("rt_cell_new");
            let cell = self
                .builder
                .build_call(rt_cell_new, &[nil_value.into()], &format!("{}_cell", name))
                .unwrap();
            self.builder
                .build_store(alloca, cell.try_as_basic_value().left().unwrap())
                .unwrap();
        } else {
            // Store nil directly
            self.builder.build_store(alloca, nil_value).unwrap();
        }

        self.variables.insert(name.to_string(), alloca);
        self.forward_declared_variables.insert(name.to_string());
    }

    /// Get or declare a runtime function by name
    fn get_or_declare_runtime_fn(&self, fn_name: &str) -> inkwell::values::FunctionValue<'ctx> {
        if let Some(func) = self.module.get_function(fn_name) {
            return func;
        }
        // All our runtime functions take i64 and return i64
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into()], false);
        let func = self.module.add_function(fn_name, fn_type, None);

        // Add nounwind attribute - tells LLVM this function doesn't throw exceptions
        let nounwind_kind = Attribute::get_named_enum_kind_id("nounwind");
        let nounwind_attr = self.context.create_enum_attribute(nounwind_kind, 0);
        func.add_attribute(AttributeLoc::Function, nounwind_attr);

        func
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
        let target = Target::from_triple(&triple).map_err(|e| format!("Failed to get target from triple: {}", e))?;

        // Create target machine with the configured optimization level
        // Use native CPU and features for best performance on the host machine
        let cpu = TargetMachine::get_host_cpu_name();
        let features = TargetMachine::get_host_cpu_features();
        let target_machine = target
            .create_target_machine(
                &triple,
                cpu.to_str().unwrap_or("generic"),
                features.to_str().unwrap_or(""),
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
        let target = Target::from_triple(&triple).map_err(|e| format!("Failed to get target from triple: {}", e))?;

        // Use native CPU and features for best performance on the host machine
        let cpu = TargetMachine::get_host_cpu_name();
        let features = TargetMachine::get_host_cpu_features();
        let target_machine = target
            .create_target_machine(
                &triple,
                cpu.to_str().unwrap_or("generic"),
                features.to_str().unwrap_or(""),
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
