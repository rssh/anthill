//! Shared test fixtures for `anthill-todo` integration tests.

use std::fs;
use std::path::{Path, PathBuf};

/// Concatenate every `.anthill` file in `inner` into one string —
/// integration tests assert on persisted-fact substrings without
/// caring which file (workitems.anthill vs facts.anthill) the
/// FileStore routed the write to.
pub fn read_combined(inner: &Path) -> String {
    let mut combined = String::new();
    for entry in fs::read_dir(inner).expect("read_dir") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|s| s.to_str()) == Some("anthill") {
            combined.push_str(&fs::read_to_string(&path).expect("read"));
        }
    }
    combined
}

/// Inside a flat WorkItem-fact dump, find the fact block whose
/// `id: "<id>"` matches, then check whether `dep` appears anywhere
/// in that block. Used to assert depends_on contents without parsing
/// the term. Crude but adequate for tests with a handful of facts.
pub fn workitem_block_contains(haystack: &str, id: &str, dep: &str) -> bool {
    let id_marker = format!("id: \"{id}\"");
    let Some(start) = haystack.find(&id_marker) else { return false };
    let after = &haystack[start..];
    let block_end = after[1..]
        .find("fact WorkItem")
        .map(|i| i + 1)
        .unwrap_or(after.len());
    after[..block_end].contains(&format!("\"{dep}\""))
}

pub fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent().unwrap()
        .parent().unwrap()
        .to_path_buf()
}

/// Build a fresh project under `tmp` with the bundle-asset
/// domain.anthill / rules.anthill copied in (so the bundle's
/// `import anthill.stage0.{...}` resolves at scan time) and a
/// caller-supplied workitems.anthill body.
///
/// Since WI-505 these copied domain/rules are redundant — the bundle
/// supplies them and the CLI skips a project's own copies — but keeping
/// them here exercises that skip path, and existing assertions that scan
/// every project file (`read_combined`) stay unchanged. The copy-source is
/// the canonical bundle asset under `rustland/anthill-todo/anthill/`, not the
/// live tracker dir (WI-684).
pub fn setup_project(tmp: &tempfile::TempDir, workitems: &str) -> PathBuf {
    let proj = tmp.path().to_path_buf();
    let inner = proj.join("anthill-todo");
    fs::create_dir(&inner).expect("mkdir anthill-todo");

    let src_root = workspace_root().join("rustland/anthill-todo/anthill");
    for f in ["domain.anthill", "rules.anthill"] {
        fs::copy(src_root.join(f), inner.join(f)).expect("copy project file");
    }
    fs::write(inner.join("workitems.anthill"), workitems).expect("write workitems");
    proj
}

/// Build a fresh project under `tmp` carrying NO domain.anthill /
/// rules.anthill — only a workitems.anthill body. The standard
/// anthill.stage0 domain and workflow rules come from the binary bundle
/// (WI-505), so such a project must load and run all the same.
pub fn setup_domainless_project(tmp: &tempfile::TempDir, workitems: &str) -> PathBuf {
    let proj = tmp.path().to_path_buf();
    let inner = proj.join("anthill-todo");
    fs::create_dir(&inner).expect("mkdir anthill-todo");
    fs::write(inner.join("workitems.anthill"), workitems).expect("write workitems");
    proj
}
