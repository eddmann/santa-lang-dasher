//! Build script to embed the runtime library in the lang crate.
//!
//! This script compresses the runtime library and makes it available
//! for embedding via include_bytes!().

use std::env;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};

fn newest_staticlib_in_deps(dir: &Path) -> Option<PathBuf> {
    let mut newest: Option<(std::time::SystemTime, PathBuf)> = None;
    let entries = std::fs::read_dir(dir).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        let file_name = path.file_name()?.to_string_lossy();
        if !file_name.starts_with("libsanta_lang_runtime-") || !file_name.ends_with(".a") {
            continue;
        }
        let modified = entry.metadata().and_then(|m| m.modified()).ok()?;
        match &newest {
            Some((best_time, _)) if *best_time >= modified => {}
            _ => newest = Some((modified, path)),
        }
    }
    newest.map(|(_, path)| path)
}

fn main() {
    // Tell Cargo to re-run if the runtime library changes
    println!("cargo:rerun-if-changed=../runtime/src/");
    println!("cargo:rerun-if-changed=../runtime/Cargo.toml");

    // Find the runtime library
    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let project_root = PathBuf::from(&manifest_dir).parent().unwrap().to_path_buf();
    println!(
        "cargo:rerun-if-changed={}",
        project_root.join("target/release/libsanta_lang_runtime.a").display()
    );
    println!(
        "cargo:rerun-if-changed={}",
        project_root.join("target/debug/libsanta_lang_runtime.a").display()
    );

    let profile = env::var("PROFILE").unwrap_or_else(|_| "debug".to_string());
    let profile_dir = project_root.join("target").join(&profile);

    // Prefer profile-matched staticlib, then a deps-built staticlib for the same profile
    let runtime_lib = profile_dir.join("libsanta_lang_runtime.a");
    let runtime_lib = if runtime_lib.exists() {
        runtime_lib
    } else if let Some(dep_lib) = newest_staticlib_in_deps(&profile_dir.join("deps")) {
        dep_lib
    } else {
        // Runtime not built yet - this is fine during initial build
        // The pipeline will fall back to finding it externally
        println!(
            "cargo:warning=Runtime library not found for profile '{}', embedding disabled",
            profile
        );
        return;
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
