//! Anti-drift guard for the embedded stdlib list (`anthill::stdlib::SOURCES`).
//!
//! The list is explicit and ORDERED (load order matters — see the module doc in
//! `src/stdlib.rs`), so it cannot be a plain directory walk. This test supplies
//! the completeness half the walk used to give: it reconciles `SOURCES` against
//! the on-disk source trees and FAILS LOUDLY if a `.anthill` file was added or
//! removed without being placed in the list. The failure message names the
//! offending files so the fix is to slot each into `SOURCES` at the right
//! dependency position (not to alphabetize the whole list).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// Collect every `.anthill` file under `dir`, returning labels of the form
/// `<prefix>/<stem-relative-to-root>` (matching how `SOURCES` labels its
/// entries). `dir` is the directory currently being walked; the relative stem
/// is always taken against `root` so nested segments (e.g. `prelude/`) survive
/// the recursion.
fn walk_labels(root: &Path, dir: &Path, prefix: &str, out: &mut BTreeSet<String>) {
    let rd = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read stdlib dir {}: {e}", dir.display()));
    for entry in rd {
        let entry = entry.expect("read_dir entry");
        let ft = entry.file_type().expect("file_type");
        let p = entry.path();
        if ft.is_dir() {
            walk_labels(root, &p, prefix, out);
        } else if ft.is_file() && p.extension().is_some_and(|e| e == "anthill") {
            let rel = p.strip_prefix(root).unwrap().with_extension("");
            out.insert(format!("{prefix}/{}", rel.to_string_lossy().replace('\\', "/")));
        }
    }
}

#[test]
fn embedded_sources_match_on_disk_trees() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let roots = [
        (manifest.join("../../stdlib/anthill"), "anthill"),
        (manifest.join("anthill"), "rustland/anthill-stl"),
    ];

    let mut on_disk: BTreeSet<String> = BTreeSet::new();
    for (dir, prefix) in &roots {
        let dir = dir
            .canonicalize()
            .unwrap_or_else(|e| panic!("stdlib root {} not found: {e}", dir.display()));
        walk_labels(&dir, &dir, prefix, &mut on_disk);
    }

    let embedded: BTreeSet<String> =
        anthill::stdlib::SOURCES.iter().map(|(label, _)| label.to_string()).collect();

    let missing: Vec<&String> = on_disk.difference(&embedded).collect();
    let extra: Vec<&String> = embedded.difference(&on_disk).collect();

    assert!(
        missing.is_empty() && extra.is_empty(),
        "embedded stdlib list drifted from the on-disk source trees.\n  \
         on disk but NOT in SOURCES (add each at its dependency position in src/stdlib.rs): {missing:?}\n  \
         in SOURCES but NOT on disk (remove from src/stdlib.rs): {extra:?}",
    );
}

/// WI-934 — `stdlib/anthill/persistence/` carries the store algebra and the backends
/// that realize it, and nothing else.
///
/// A shape no host realizes is an example, not a standard library
/// (`docs/proposals/038-builtin-sorts.md`, "What the stdlib carries"), which is why the
/// SQL sketch now lives in `examples/sql-store/`. That is a CURATION decision: such a
/// file loads perfectly, declares nothing and provides nothing, so no load-time check
/// can refuse it and an explicit assertion is the only available form.
///
/// Stated over the DIRECTORY rather than as "no label containing `sql`", because the
/// name is the weakest thing to key on: re-adding the same sketch as
/// `persistence/database.anthill` would walk straight past a name filter. An exact set
/// also fails on the addition of an unrealized `persistence/redis.anthill`, which the
/// rule equally forbids — a new REALIZED backend is expected to update this list, and
/// that edit is where the rule gets read.
///
/// `embedded_sources_match_on_disk_trees` cannot carry this: it reconciles two sets, so
/// it is satisfied by any consistent pair — restoring the file AND re-listing it in
/// `SOURCES` passes it. `sql_store_example_test::the_sql_store_shape_left_the_stdlib`
/// (anthill-core) makes the complementary claim against a loaded KB; this one is
/// crate-local, so `cargo test -p anthill-stl` alone catches the drift.
#[test]
fn the_stdlib_persistence_dir_carries_only_the_algebra_and_its_realized_backends() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../stdlib/anthill/persistence")
        .canonicalize()
        .expect("stdlib persistence dir");

    let mut found: Vec<String> = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("read persistence dir") {
        let p = entry.expect("dir entry").path();
        if p.extension().is_some_and(|e| e == "anthill") {
            found.push(p.file_name().unwrap().to_string_lossy().into_owned());
        }
    }
    found.sort();

    assert_eq!(
        found,
        ["filesystem.anthill", "store.anthill"],
        "stdlib/anthill/persistence/ carries the abstract store algebra and the backends \
         a host realizes — nothing else. A shape no host realizes is an example \
         (examples/sql-store/, WI-934); see docs/proposals/038-builtin-sorts.md.",
    );

    // …and the bundle every anthill binary carries agrees with the tree.
    let labels: Vec<&str> = anthill::stdlib::SOURCES.iter().map(|(l, _)| *l).collect();
    assert!(
        labels.contains(&"anthill/persistence/store"),
        "the store algebra must ship in the embedded bundle; labels were {labels:?}",
    );
}
