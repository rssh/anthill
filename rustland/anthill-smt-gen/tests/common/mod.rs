//! Shared test helpers — load a KB from an inline source plus the
//! cached stdlib. Mirrors anthill-cpp-gen's `tests/common/mod.rs`.

use std::path::PathBuf;
use std::sync::LazyLock;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

pub fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir).expect("read dir") {
            let entry = entry.expect("read dir entry");
            let path = entry.path();
            if path.is_dir() {
                files.extend(collect_anthill_files(&path));
            } else if path.extension().is_some_and(|e| e == "anthill") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

pub fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill")
}

static STDLIB_PARSED: LazyLock<Vec<ParsedFile>> = LazyLock::new(|| {
    let files = collect_anthill_files(&stdlib_dir());
    files.iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect()
});

#[allow(dead_code)]
pub fn load_kb_with(source: &str) -> KnowledgeBase {
    let user = parse::parse(source).expect("parse user source");
    let mut refs: Vec<&ParsedFile> = STDLIB_PARSED.iter().collect();
    refs.push(&user);

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}
