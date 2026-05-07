//! Shared test fixtures for `anthill-todo` integration tests.

use std::fs;
use std::path::PathBuf;

pub fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent().unwrap()
        .parent().unwrap()
        .to_path_buf()
}

/// Build a fresh project under `tmp` with the workspace's own
/// domain.anthill / rules.anthill copied in (so the bundle's
/// `import anthill.stage0.{...}` resolves at scan time) and a
/// caller-supplied workitems.anthill body.
pub fn setup_project(tmp: &tempfile::TempDir, workitems: &str) -> PathBuf {
    let proj = tmp.path().to_path_buf();
    let inner = proj.join("anthill-todo");
    fs::create_dir(&inner).expect("mkdir anthill-todo");

    let src_root = workspace_root().join("anthill-todo");
    for f in ["domain.anthill", "rules.anthill"] {
        fs::copy(src_root.join(f), inner.join(f)).expect("copy project file");
    }
    fs::write(inner.join("workitems.anthill"), workitems).expect("write workitems");
    proj
}
