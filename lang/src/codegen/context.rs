use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::builder::Builder;
use inkwell::basic_block::BasicBlock;
use inkwell::values::PointerValue;
use std::collections::HashMap;

pub struct CodegenContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub current_block: Option<BasicBlock<'ctx>>,
    /// Maps variable names to their stack allocations
    pub variables: HashMap<String, PointerValue<'ctx>>,
}

impl<'ctx> CodegenContext<'ctx> {
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();

        Self {
            context,
            module,
            builder,
            current_block: None,
            variables: HashMap::new(),
        }
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
}
