//! Build script to embed the runtime library in the lang crate.
//!
//! This script compresses the runtime library and makes it available
//! for embedding via include_bytes!().

use std::env;
use std::fs;
use std::io::{Read, Write};
use std::path::PathBuf;

fn main() {
    // Tell Cargo to re-run if the runtime library changes
    println!("cargo:rerun-if-changed=../runtime/src/");
    println!("cargo:rerun-if-changed=../runtime/Cargo.toml");

    // Find the runtime library
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let project_root = PathBuf::from(&manifest_dir).parent().unwrap().to_path_buf();

    // Try release first, then debug
    let runtime_lib = project_root.join("target/release/libsanta_lang_runtime.a");
    let runtime_lib = if runtime_lib.exists() {
        runtime_lib
    } else {
        let debug_lib = project_root.join("target/debug/libsanta_lang_runtime.a");
        if debug_lib.exists() {
            debug_lib
        } else {
            // Runtime not built yet - this is fine during initial build
            // The pipeline will fall back to finding it externally
            println!("cargo:warning=Runtime library not found, embedding disabled");
            return;
        }
    };

    // Read and compress the runtime library
    let mut file = fs::File::open(&runtime_lib).expect("Failed to open runtime library");
    let mut data = Vec::new();
    file.read_to_end(&mut data).expect("Failed to read runtime library");

    // Compress using flate2/gzip
    let mut encoder = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::best());
    encoder.write_all(&data).expect("Failed to compress runtime library");
    let compressed = encoder.finish().expect("Failed to finish compression");

    println!(
        "cargo:warning=Runtime library: {} -> {} bytes (compressed)",
        data.len(),
        compressed.len()
    );

    // Write to OUT_DIR
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = PathBuf::from(&out_dir).join("runtime_embedded.gz");
    fs::write(&dest_path, &compressed).expect("Failed to write compressed runtime");

    // Export the path for include_bytes!
    println!("cargo:rustc-env=RUNTIME_EMBEDDED_PATH={}", dest_path.display());
}
