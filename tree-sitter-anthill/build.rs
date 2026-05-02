use std::path::Path;
use std::process::Command;

fn main() {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let src_dir = manifest_dir.join("src");
    let bindings_dir = manifest_dir.join("bindings/rust");

    println!("cargo:rerun-if-changed=grammar.js");

    // Generate parser if src/parser.c is missing or stale relative to grammar.js
    let parser_c = src_dir.join("parser.c");
    let grammar_js = manifest_dir.join("grammar.js");
    let needs_regen = !parser_c.exists()
        || match (
            std::fs::metadata(&grammar_js).and_then(|m| m.modified()),
            std::fs::metadata(&parser_c).and_then(|m| m.modified()),
        ) {
            (Ok(g), Ok(p)) => g > p,
            _ => false,
        };

    if needs_regen {
        eprintln!("tree-sitter-anthill: (re)generating parser from grammar.js...");
        let status = Command::new("npx")
            .arg("tree-sitter")
            .arg("generate")
            .current_dir(manifest_dir)
            .status()
            .expect("failed to run `npx tree-sitter generate` — is tree-sitter-cli installed?");
        assert!(status.success(), "tree-sitter generate failed");
    }

    // Generate Rust bindings if missing
    if !bindings_dir.join("lib.rs").exists() {
        eprintln!("tree-sitter-anthill: generating Rust bindings...");
        let status = Command::new("npx")
            .arg("tree-sitter")
            .arg("init")
            .current_dir(manifest_dir)
            .status()
            .expect("failed to run `npx tree-sitter init` — is tree-sitter-cli installed?");
        assert!(status.success(), "tree-sitter init failed");
    }

    // Compile the C parser
    let mut c_config = cc::Build::new();
    c_config.std("c11").include(&src_dir);

    #[cfg(target_env = "msvc")]
    c_config.flag("-utf-8");

    let parser_path = src_dir.join("parser.c");
    c_config.file(&parser_path);
    println!("cargo:rerun-if-changed={}", parser_path.display());

    let scanner_path = src_dir.join("scanner.c");
    if scanner_path.exists() {
        c_config.file(&scanner_path);
        println!("cargo:rerun-if-changed={}", scanner_path.display());
    }

    c_config.compile("tree-sitter-anthill");
}
