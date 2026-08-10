//! Every file in a crate's `tests/include/` must be registered in exactly one
//! aggregator — the invariant `rustland/CLAUDE.md` states, enforced instead of
//! merely documented.
//!
//! WHY A TEST AND NOT A CONVENTION. Only *direct children* of `tests/` are cargo
//! test targets, so a file under `tests/include/` is compiled only if some
//! aggregator carries a `#[path = "include/<name>.rs"] mod <name>;` for it.
//! Forget that line and the file is never compiled and never run — and NOTHING
//! reports it. No cargo warning, no rustc warning, no failing test: the suite
//! goes green with every assertion in that file silently absent. That is the
//! silent-skip failure mode the repo's principles single out, and it gets easier
//! to hit as the directory grows (391 files across three crates at the time of
//! writing, spread over nine aggregators).
//!
//! The three drifts it catches, each silent otherwise:
//!   * UNREGISTERED — a file no aggregator names. Never compiled, never run.
//!     This is the accident: add a test, forget the `#[path]` line.
//!   * DANGLING     — a registration whose file was renamed or deleted. This one
//!                    is already a compile error, so it is the cheap half; the
//!                    check just names it plainly instead of leaving a `#[path]`
//!                    resolution failure.
//!   * DOUBLE       — a file two aggregators both name. It compiles and runs
//!                    twice, in two binaries, doubling its cost and racing with
//!                    itself over any shared on-disk fixture.
//!
//! RESIDUAL EXPOSURE, stated rather than hidden: this guard lives in `include/`
//! too, so deleting *its own* registration disables it silently. That is a
//! deliberate edit visible in a diff, not the accident above — and the
//! alternative, a top-level file that cannot be unregistered, costs a whole test
//! binary, which is the cost this layout exists to avoid.
//!
//! CONTROL. Delete any `#[path = "include/…"]` line from any aggregator in the
//! three listed crates and this test fails naming that file; every other test in
//! the workspace stays green — which is exactly the blindness being closed.
//! Deleting the file along with its registration passes, correctly: the
//! invariant is files-match-registrations, not a count.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Crates using the `tests/include/` + aggregator layout. The codegen crates
/// (`anthill-cpp-gen`, `anthill-rust-gen`, `anthill-smt-gen`) reach the same goal
/// through `autotests = false` + explicit `[[test]]` blocks, where an unlisted
/// file is a Cargo-level omission rather than a `#[path]` one — a different
/// mechanism, deliberately out of scope here.
const AGGREGATED_CRATES: &[&str] = &["anthill-core", "anthill-cli", "anthill-todo"];

/// `CARGO_MANIFEST_DIR` is `<workspace>/anthill-core`; its parent is the root.
fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("anthill-core has a parent directory")
        .to_path_buf()
}

fn rs_file_names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("read {}: {e}", dir.display()))
        .map(|e| {
            e.expect("dir entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .filter(|n| n.ends_with(".rs"))
        .collect();
    names.sort();
    names
}

/// Map `<name>.rs` -> the aggregator file names that declare it.
fn registrations(tests_dir: &Path) -> BTreeMap<String, Vec<String>> {
    let mut regs: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for aggregator in rs_file_names(tests_dir) {
        let path = tests_dir.join(&aggregator);
        let src =
            fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        for line in src.lines() {
            // `#[path = "include/foo_test.rs"]`
            let Some(rest) = line.trim().strip_prefix("#[path = \"include/") else {
                continue;
            };
            let Some(name) = rest.split('"').next() else {
                continue;
            };
            regs.entry(name.to_string())
                .or_default()
                .push(aggregator.clone());
        }
    }
    regs
}

#[test]
fn every_include_file_is_registered_in_exactly_one_aggregator() {
    let root = workspace_root();
    let mut problems: Vec<String> = Vec::new();

    for krate in AGGREGATED_CRATES {
        let tests_dir = root.join(krate).join("tests");
        let include_dir = tests_dir.join("include");

        // A missing or empty include/ would make this guard silently vacuous for
        // that crate — the very shape it exists to reject. Fail loudly instead.
        assert!(
            include_dir.is_dir(),
            "{krate} is listed in AGGREGATED_CRATES but {} does not exist. If the \
             crate stopped using this layout, remove it from the list; do not leave \
             an entry pointing at nothing.",
            include_dir.display()
        );
        let files = rs_file_names(&include_dir);
        assert!(
            !files.is_empty(),
            "{} holds no .rs files — a vacuous check for {krate}. See the note above.",
            include_dir.display()
        );

        let regs = registrations(&tests_dir);

        for name in &files {
            match regs.get(name) {
                None => problems.push(format!(
                    "{krate}/tests/include/{name} is registered by NO aggregator, so it is \
                     never compiled and never run. Add \
                     `#[path = \"include/{name}\"] mod {};` to one aggregator in \
                     {krate}/tests/.",
                    name.trim_end_matches(".rs")
                )),
                // Two aggregators naming it is the common shape, but ONE
                // aggregator naming it twice is the same defect, so report the
                // registration count and the DISTINCT aggregators separately —
                // "2 aggregators (resolve_tests.rs, resolve_tests.rs)" is a lie
                // about where to look.
                Some(aggs) if aggs.len() > 1 => {
                    let mut distinct: Vec<&String> = aggs.iter().collect();
                    distinct.dedup();
                    problems.push(format!(
                        "{krate}/tests/include/{name} is registered {} times, in {} ({}), so it \
                         compiles and runs once per registration. Keep exactly one.",
                        aggs.len(),
                        if distinct.len() == 1 {
                            "one aggregator"
                        } else {
                            "several aggregators"
                        },
                        distinct
                            .iter()
                            .map(|s| s.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                }
                Some(_) => {}
            }
        }

        for (name, aggs) in &regs {
            if !files.contains(name) {
                problems.push(format!(
                    "{krate}/tests/{} registers include/{name}, which does not exist.",
                    aggs.join(" and ")
                ));
            }
        }
    }

    assert!(
        problems.is_empty(),
        "tests/include/ registration drift ({} problem(s)):\n  {}",
        problems.len(),
        problems.join("\n  ")
    );
}
