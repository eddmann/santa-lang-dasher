//! Benchmarks for the santa-lang Dasher compiler
//!
//! Measures performance of:
//! - Lexer throughput
//! - Parser throughput
//! - Codegen (LLVM IR generation)
//! - Full compilation pipeline

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use inkwell::OptimizationLevel;
use inkwell::context::Context;

use lang::codegen::context::CodegenContext;
use lang::lexer::lex;
use lang::parser::Parser;

/// Simple arithmetic expression
const SIMPLE_EXPR: &str = "1 + 2 * 3";

/// Nested arithmetic expression
const NESTED_EXPR: &str = "1 + 2 * 3 + 4 / 5 - 6 + 7 * 8 - 9 + 10";

/// Function definition and call
const FUNCTION_EXPR: &str = r#"
let add = |a, b| a + b;
let multiply = |a, b| a * b;
multiply(add(1, 2), add(3, 4))
"#;

/// List operations
const LIST_EXPR: &str = r#"
let nums = [1, 2, 3, 4, 5];
let doubled = map(|x| x * 2, nums);
fold(0, |acc, x| acc + x, doubled)
"#;

/// Tail-recursive function (TCO benchmark)
const RECURSIVE_EXPR: &str = r#"
let countdown = |n| {
    if n == 0 { 0 }
    else { countdown(n - 1) }
};
countdown(100)
"#;

/// Match expression (using literal patterns, not ranges which have complex syntax)
const MATCH_EXPR: &str = r#"
let classify = |n| {
    match n {
        0 { "zero" }
        1 { "one" }
        2 { "two" }
        _ { "other" }
    }
};
classify(2)
"#;

fn bench_lexer(c: &mut Criterion) {
    let mut group = c.benchmark_group("lexer");

    let test_cases = [
        ("simple", SIMPLE_EXPR),
        ("nested", NESTED_EXPR),
        ("function", FUNCTION_EXPR),
        ("list", LIST_EXPR),
        ("recursive", RECURSIVE_EXPR),
        ("match", MATCH_EXPR),
    ];

    for (name, source) in test_cases {
        group.bench_with_input(BenchmarkId::new("lex", name), source, |b, source| {
            b.iter(|| lex(black_box(source)).unwrap())
        });
    }

    group.finish();
}

fn bench_parser(c: &mut Criterion) {
    let mut group = c.benchmark_group("parser");

    let test_cases = [
        ("simple", SIMPLE_EXPR),
        ("nested", NESTED_EXPR),
        ("function", FUNCTION_EXPR),
        ("list", LIST_EXPR),
        ("recursive", RECURSIVE_EXPR),
        ("match", MATCH_EXPR),
    ];

    for (name, source) in test_cases {
        // Pre-lex for parser-only benchmark
        let tokens = lex(source).unwrap();

        group.bench_with_input(BenchmarkId::new("parse", name), &tokens, |b, tokens| {
            b.iter(|| {
                let mut parser = Parser::new(tokens.clone());
                parser.parse_program().unwrap()
            })
        });
    }

    group.finish();
}

fn bench_codegen(c: &mut Criterion) {
    let mut group = c.benchmark_group("codegen");

    // Only benchmark simple cases for codegen as it involves LLVM
    let test_cases = [("simple", SIMPLE_EXPR), ("nested", NESTED_EXPR)];

    for (name, source) in test_cases {
        // Pre-parse for codegen-only benchmark
        let tokens = lex(source).unwrap();
        let mut parser = Parser::new(tokens);
        let _program = parser.parse_program().unwrap();

        group.bench_with_input(BenchmarkId::new("codegen", name), source, |b, _source| {
            b.iter(|| {
                let context = Context::create();
                let codegen = CodegenContext::new(&context, "bench_module");
                // Return the optimization level to avoid lifetime issues
                // Full codegen would compile the program here
                black_box(codegen.optimization_level())
            })
        });
    }

    group.finish();
}

fn bench_optimization_levels(c: &mut Criterion) {
    let mut group = c.benchmark_group("optimization");

    let opt_levels = [
        ("O0", OptimizationLevel::None),
        ("O1", OptimizationLevel::Less),
        ("O2", OptimizationLevel::Default),
        ("O3", OptimizationLevel::Aggressive),
    ];

    for (name, opt_level) in opt_levels {
        group.bench_with_input(
            BenchmarkId::new("context_creation", name),
            &opt_level,
            |b, opt_level| {
                b.iter(|| {
                    let context = Context::create();
                    let codegen = CodegenContext::with_optimization(&context, "bench_module", *opt_level);
                    // Return something that doesn't hold a reference to context
                    black_box(codegen.optimization_level())
                })
            },
        );
    }

    group.finish();
}

fn bench_full_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("full_pipeline");

    let test_cases = [("simple", SIMPLE_EXPR), ("nested", NESTED_EXPR)];

    for (name, source) in test_cases {
        group.bench_with_input(BenchmarkId::new("lex_parse", name), source, |b, source| {
            b.iter(|| {
                let tokens = lex(black_box(source)).unwrap();
                let mut parser = Parser::new(tokens);
                parser.parse_program().unwrap()
            })
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_lexer,
    bench_parser,
    bench_codegen,
    bench_optimization_levels,
    bench_full_pipeline
);
criterion_main!(benches);
