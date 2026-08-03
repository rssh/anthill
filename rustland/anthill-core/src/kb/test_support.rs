//! The stdlib-loading fixture shared by this crate's `#[cfg(test)]` modules.
//!
//! WI-959 lifted it here after finding the same sequence hand-rolled in three
//! `kb/` modules (`typing.rs` twice, `region.rs`, `op_requirements.rs`), each
//! with its own walk and its own error policy.
//!
//! It cannot live in `anthill-core/tests/common/`: that is a separate crate and
//! sees only `pub` items, while the tests needing this fixture drive
//! crate-private ones (`typing::join_types`, `typing::meet_types`,
//! `typing::is_function_spec`, `region`'s flow derivation). That is the whole
//! reason a second copy of `tests/common::load_kb_with` has to exist at all.

use crate::kb::load::{self, NullResolver};
use crate::kb::KnowledgeBase;
use crate::parse::{self, ir::ParsedFile};
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

/// `stdlib/anthill` — the language's own library.
static STDLIB_PARSED: LazyLock<Vec<ParsedFile>> = LazyLock::new(|| {
    parse_dir(&PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill"))
});

/// `rustland/anthill-stl/anthill` — the Rust host bindings.
static STL_PARSED: LazyLock<Vec<ParsedFile>> = LazyLock::new(|| {
    parse_dir(&PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../anthill-stl/anthill"))
});

/// The stdlib, plus an optional fixture source loaded alongside it.
pub(crate) fn load_stdlib(extra: Option<&str>) -> KnowledgeBase {
    load_libraries(&[&STDLIB_PARSED], extra)
}

/// [`load_stdlib`] plus the `anthill-stl` host bindings.
pub(crate) fn load_stdlib_and_stl(extra: Option<&str>) -> KnowledgeBase {
    load_libraries(&[&STDLIB_PARSED, &STL_PARSED], extra)
}

/// Parse every `.anthill` file under `dir`, once per test binary.
///
/// The library text is immutable and `load_all` borrows it (`&[&ParsedFile]`), so
/// every fixture can share one parse — the same `LazyLock` shape
/// `anthill-smt-gen/tests/common` uses. The KB itself is still built fresh per
/// caller, which is where most of the time goes: MEASURED over the 29 tests in
/// this crate's fixture-bearing modules, sharing the parse moved 22.0s of user
/// CPU to 19.1s (~13%). Worth having, but do not expect the parse to dominate.
fn parse_dir(dir: &Path) -> Vec<ParsedFile> {
    // WI-747: the walk is the shared `crate::fs_util`, which fails LOUD on an
    // unreadable/missing dir. A hand-rolled `if dir.is_dir()` copy returns an
    // EMPTY list instead, and a caller's headline test would then report e.g.
    // "the stdlib declares no anthill.prelude.Function" — blaming the constant
    // for a bad path, the exact misdiagnosis it exists to prevent.
    let files = crate::fs_util::collect_files(dir, &["anthill"])
        .unwrap_or_else(|e| panic!("collect .anthill files: {e}"));
    // Each `expect` NAMES the file: a bare `unwrap` here reports an Io or
    // parse error with no path, which is the same mute-diagnostic problem the
    // walk above was just fixed for.
    files
        .iter()
        .map(|p| {
            let text =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&text).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect()
}

/// `libs` plus `extra`, loaded into one fresh KB.
///
/// Every failure is RAISED — there is no lenient variant, because WI-959
/// measured that nothing here needs one. `region.rs`'s copy discarded the load
/// error under a comment claiming its fixture legitimately fails to typecheck;
/// the fixture was simply broken (it spelled the unit value `unit`, which the
/// grammar does not define — see `stdlib/anthill/prelude/unit.anthill`), and
/// once fixed it loads clean like the other two. A fixture that must carry a
/// genuinely unloadable shape needs its own named entry point, as
/// `anthill-smt-gen`'s `load_kb_with`/`load_kb_strict` pair does — never a
/// silent `let _ =` at a call site.
fn load_libraries(libs: &[&Vec<ParsedFile>], extra: Option<&str>) -> KnowledgeBase {
    let extra_parsed = extra.map(|src| parse::parse(src).expect("parse fixture"));
    let mut refs: Vec<&ParsedFile> = libs.iter().flat_map(|lib| lib.iter()).collect();
    refs.extend(extra_parsed.iter());

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    // The subject is "library + fixture", NOT "stdlib". `extra` loads in the same
    // batch and is by far the likelier culprit, so labelling this a stdlib error
    // blames the wrong file — the misdiagnosis the walk above is loud to avoid,
    // reintroduced one line down. Each error names its own origin already: WI-745
    // renders a library error as `path:line:col` and the path-less `extra` as a
    // bare `line:col`, so the label must not pre-empt them.
    if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {
        panic!(
            "load errors (library + fixture): {:?}",
            errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }
    kb
}
