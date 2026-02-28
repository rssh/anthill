use std::path::PathBuf;

use anthill_core::parse;
use anthill_core::codegen::{collect_trait_sorts, generate_rust_with_context};

fn main() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let out_dir = manifest_dir.join("generated");
    std::fs::create_dir_all(&out_dir).expect("create generated/ dir");

    let files = [
        ("reflect", "../../stdlib/anthill/reflect/reflect.anthill"),
        ("store", "../../stdlib/anthill/persistence/store.anthill"),
        ("filesystem", "../../stdlib/anthill/persistence/filesystem.anthill"),
        ("sql", "../../stdlib/anthill/persistence/sql.anthill"),
        ("stream", "../../stdlib/anthill/prelude/stream.anthill"),
        ("logical_stream", "../../stdlib/anthill/prelude/logical_stream.anthill"),
    ];

    // Parse all files first
    let parsed: Vec<(&str, anthill_core::parse::ir::ParsedFile)> = files.iter()
        .map(|(name, rel_path)| {
            let path = manifest_dir.join(rel_path);
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            let p = parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {name}: {e:?}"));
            (*name, p)
        })
        .collect();

    // Collect cross-file trait sorts
    let refs: Vec<&anthill_core::parse::ir::ParsedFile> = parsed.iter().map(|(_, p)| p).collect();
    let trait_sorts = collect_trait_sorts(&refs);

    // Generate with context
    for (name, p) in &parsed {
        let rust = generate_rust_with_context(p, &trait_sorts)
            .unwrap_or_else(|e| panic!("codegen {name}: {e:?}"));
        let out_path = out_dir.join(format!("{name}.rs"));
        std::fs::write(&out_path, &rust)
            .unwrap_or_else(|e| panic!("write {}: {e}", out_path.display()));
        println!("wrote {}", out_path.display());
    }
}
