//! Shared test helpers — load a KB from an inline source plus the
//! cached stdlib. Mirrors anthill-cpp-gen's `tests/common/mod.rs`.

use std::path::PathBuf;
use std::sync::LazyLock;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

/// WI-747: the walk is the shared `anthill_core::fs_util`; the panic-on-fault
/// policy (a broken stdlib fixture is a test bug) stays here.
pub fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
    anthill_core::fs_util::collect_files(dir, &["anthill"]).expect("collect .anthill files")
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

/// Load the cached stdlib + `source` into a fresh KB, PANICKING on a load error.
///
/// WI-966 dissolved a name trap here rather than renaming around it. This crate
/// used to spell the DISCARDING loader `load_kb_with` while
/// `anthill-core/tests/common::load_kb_with` PANICS — same name, opposite
/// guarantee, same workspace — with a strict `load_kb_strict` alongside that
/// only `wi680_ite_lowering_test` reached for. The discard was justified in
/// writing as "load-bearing for the fixtures that deliberately carry an
/// unresolvable shape". MEASURED by flipping it: all 100 tests in this crate
/// pass strict, so no such fixture exists. There is now one loader, and the name
/// means panic-on-error in all three test crates.
///
/// A fixture that must load dirty needs a NAMED lenient entry point (see
/// `anthill-cpp-gen/tests/common::load_kb_with_lenient`), never a bare discard:
/// WI-887 recorded this very harness hiding a live load error in
/// `wi680_ite_lowering_test`, whose assertions about emitted SMT went on passing
/// through a fallback path while claiming to pin the imported one.
#[allow(dead_code)]
pub fn load_kb_with(source: &str) -> KnowledgeBase {
    let user = parse::parse(source).expect("parse user source");
    let mut refs: Vec<&ParsedFile> = STDLIB_PARSED.iter().collect();
    refs.push(&user);

    let mut kb = KnowledgeBase::new();
    if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {
        panic!(
            "load must be clean for a test that depends on name resolution; got: {:?}",
            errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }
    kb
}

#[allow(dead_code)]
pub fn z3_available() -> bool {
    std::process::Command::new("z3").arg("--version").output()
        .map(|o| o.status.success()).unwrap_or(false)
}

/// Write `smt` to `${TMPDIR}/anthill_${slug}.smt2`, invoke z3 on it,
/// and return trimmed stdout. The temp file is intentionally left in
/// place for failure-mode debugging.
#[allow(dead_code)]
pub fn run_z3(slug: &str, smt: &str) -> String {
    let path = std::env::temp_dir().join(format!("anthill_{slug}.smt2"));
    std::fs::write(&path, smt).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
    let out = std::process::Command::new("z3").arg(&path).output()
        .unwrap_or_else(|e| panic!("z3 spawn for {slug}: {e}"));
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}
