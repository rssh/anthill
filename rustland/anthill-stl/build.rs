use std::collections::HashMap;
use std::path::PathBuf;

use anthill_core::codegen::{CodegenConfig, generate_rust_with_config, collect_trait_sorts};
use anthill_core::parse;

fn main() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let stdlib_dir = manifest_dir.join("../../stdlib/anthill");
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());

    let config = CodegenConfig {
        flatten_top_namespace: true,
        emit_fn_bodies: true,
        carrier_bindings: HashMap::from([
            ("Term".into(), "anthill_core::kb::term::TermId".into()),
            ("FactId".into(), "anthill_core::kb::RuleId".into()),
        ]),
        namespace_map: HashMap::from([
            ("anthill".into(), "crate".into()),
        ]),
        derives: vec!["Clone".into(), "Debug".into()],
        default_pub: true,
    };

    // Source → generated output mapping
    let files = [
        ("prelude/stream.anthill", "stream.rs"),
        ("prelude/logical_stream.anthill", "logical_stream.rs"),
        ("prelude/meta.anthill", "meta.rs"),
        ("reflect/reflect.anthill", "reflect.rs"),
        ("persistence/store.anthill", "store.rs"),
        ("persistence/filesystem.anthill", "filesystem.rs"),
        ("persistence/sql.anthill", "sql.rs"),
    ];

    // Parse all files
    let mut parsed_files = Vec::new();
    for (src, _) in &files {
        let source_path = stdlib_dir.join(src);
        let source = std::fs::read_to_string(&source_path)
            .unwrap_or_else(|e| panic!("read {}: {}", source_path.display(), e));
        let parsed = parse::parse(&source)
            .unwrap_or_else(|e| panic!("parse {}: {:?}", source_path.display(), e));
        parsed_files.push(parsed);
    }

    // Collect trait sorts across all files for cross-file impl Trait wrapping
    let refs: Vec<_> = parsed_files.iter().collect();
    let global_traits = collect_trait_sorts(&refs);

    // Generate each file
    for (i, (_, dst)) in files.iter().enumerate() {
        let code = generate_rust_with_config(&parsed_files[i], &global_traits, &config)
            .unwrap_or_else(|e| panic!("codegen {}: {:?}", dst, e));
        let out_path = out_dir.join(dst);
        std::fs::write(&out_path, &code)
            .unwrap_or_else(|e| panic!("write {}: {}", out_path.display(), e));
    }

    // Rerun if source changes
    println!("cargo:rerun-if-changed=../../stdlib/anthill");
}
