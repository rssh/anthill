//! Generate the embedded-stdlib source list at build time.
//!
//! The list used to be hand-maintained in `src/stdlib_embedded.rs` and DRIFTED
//! out of sync with `stdlib/anthill/` — new files (e.g. `prelude/cell`,
//! `prelude/time`, `kernel`, `logic/*`) were silently missing, so the CLI
//! shipped a stale stdlib that couldn't resolve `Cell` / recent additions.
//! Walking the directories here keeps the embedded set CURRENT automatically:
//! every `.anthill` under `stdlib/anthill/` and `anthill-stl/anthill/` is
//! embedded (via `include_str!` of an absolute path in the generated array),
//! the same complete set the test loader (`collect_anthill_files`) loads.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    // Loud over silent: a missing/unreadable root must FAIL the build, not yield
    // an empty stdlib (which would re-create the stale-stdlib failure this fixes).
    let rd = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("anthill-cli build.rs: cannot read stdlib dir {}: {e}", dir.display()));
    for entry in rd {
        let entry = entry.expect("read_dir entry");
        // `file_type()` does NOT follow symlinks — so a symlink (incl. one to an
        // ancestor dir) is neither `is_dir` nor an `.anthill` file and is simply
        // skipped, avoiding unbounded recursion / double-embedding.
        let ft = entry.file_type().expect("file_type");
        let p = entry.path();
        if ft.is_dir() {
            collect(&p, out);
        } else if ft.is_file() && p.extension().is_some_and(|e| e == "anthill") {
            out.push(p);
        }
    }
}

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    // (root dir, label prefix) — mirrors the two source trees the hand-list
    // covered: the language stdlib and the rustland host bindings.
    let roots = [
        (manifest.join("../../stdlib/anthill"), "anthill"),
        (manifest.join("../anthill-stl/anthill"), "rustland/anthill-stl"),
    ];

    let mut entries: Vec<(String, String)> = Vec::new(); // (label, absolute path)
    for (dir, prefix) in &roots {
        let dir = dir.canonicalize().unwrap_or_else(|e| {
            panic!("anthill-cli build.rs: stdlib root {} not found: {e}", dir.display())
        });
        let mut files = Vec::new();
        collect(&dir, &mut files);
        // A root that contributes zero files means the layout moved — fail loudly
        // rather than ship a half/empty embedded stdlib.
        assert!(!files.is_empty(), "anthill-cli build.rs: no .anthill files under {}", dir.display());
        for f in files {
            let rel = f.strip_prefix(&dir).unwrap_or(&f).with_extension("");
            let label = format!("{}/{}", prefix, rel.to_string_lossy().replace('\\', "/"));
            entries.push((label, f.to_string_lossy().into_owned()));
        }
        // Re-run when a file is added/removed under a root (content changes are
        // already tracked via the generated `include_str!` dependencies).
        println!("cargo:rerun-if-changed={}", dir.display());
    }
    entries.sort();

    let mut src = String::from("&[\n");
    for (label, path) in &entries {
        writeln!(src, "    ({label:?}, include_str!({path:?})),").unwrap();
    }
    src.push(']');

    let dest = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("stdlib_sources.rs");
    std::fs::write(&dest, src).unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
