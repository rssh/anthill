//! Filesystem helpers shared across the workspace — one recursive `.anthill`
//! (or arbitrary-extension) directory walk, so the CLIs, the persistence
//! backend, and every test suite agree on which files constitute a project.
//!
//! WI-747: this replaced EIGHT copies of "recursively collect files from a
//! directory" that had drifted into THREE incompatible error policies (panic,
//! empty-Vec, and a reported error). The home is `anthill-core` and not the
//! CLIs' shared `anthill-stl` for a dependency-graph reason: anthill-core is the
//! only crate every consumer can reach. anthill-stl depends on anthill-core, not
//! the reverse, so a helper there would be invisible to anthill-core's own test
//! copies and to anthill-smt-gen / anthill-cpp-gen (which depend on anthill-core
//! but not anthill-stl) — forcing a second copy and defeating the point.
//!
//! ERROR SHAPE — fail-fast `Result`, not a `&mut Vec<String>` out-param. WI-744
//! gave the two CLI copies an out-param so a scan could report every unreadable
//! directory rather than just the first. This unifies on the fail-fast shape the
//! persistence backend already used, because: (a) every caller discards the
//! collected files the instant a fault appears, so scanning past the first is
//! dead work whose only effect is printing N lines instead of 1; (b) a `Result`
//! is `#[must_use]` — a caller cannot silently drop it and thereby restore the
//! warn-and-continue bug WI-744 exists to kill, which an out-param invites. The
//! per-binary policy wrappers still accumulate one fault per *named input path*
//! into their own `Vec<String>` (a missing path, a non-`.anthill` file), and a
//! directory-read error simply joins them there — so multi-path reporting, the
//! reason the out-param was defensible, is unaffected.

use std::fs;
use std::path::{Path, PathBuf};

/// Does `path`'s extension (compared without the leading dot) appear in
/// `extensions`? A path with no extension answers `false`.
pub fn has_extension(path: &Path, extensions: &[&str]) -> bool {
    path.extension()
        .and_then(|e| e.to_str())
        .is_some_and(|e| extensions.contains(&e))
}

/// Recursively append every file under `dir` whose extension is in `extensions`
/// to `out`. Fail-fast: the first unreadable directory — or unreadable entry
/// within one — returns `Err` with a message ready to print, and the partial
/// `out` is meant to be discarded by the caller.
///
/// NOT `entries.flatten()`: `ReadDir` yields `io::Result<DirEntry>`, and flatten
/// maps an `Err` to zero items — so a file that fails mid-walk (the directory
/// mutating under us, an NFS/FUSE hiccup) would drop out of the result with no
/// diagnostic, the exact silent skip this error channel exists to close.
pub fn collect_files_recursive(
    dir: &Path,
    extensions: &[&str],
    out: &mut Vec<PathBuf>,
) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("cannot read directory {}: {e}", dir.display()))?;
    for entry in entries {
        let entry = entry
            .map_err(|e| format!("cannot read an entry of directory {}: {e}", dir.display()))?;
        let path = entry.path();
        // KNOWN GAP: `is_dir()` answers false on a stat failure, so an unstattable
        // subdirectory is neither recursed into nor reported. Left as-is
        // deliberately: `fs::metadata` would report it, but it follows symlinks,
        // so a DANGLING symlink to anything irrelevant would become a hard error
        // — over-claiming files that were never ours.
        if path.is_dir() {
            collect_files_recursive(&path, extensions, out)?;
        } else if has_extension(&path, extensions) {
            out.push(path);
        }
    }
    Ok(())
}

/// Collect every file under `dir` with a matching extension into a fresh,
/// sorted `Vec`. Convenience for call sites scanning a *single* directory (the
/// test suites, the persistence backend); the CLIs' wrappers, which merge
/// several named input paths, call [`collect_files_recursive`] per path and sort
/// once at the end instead.
pub fn collect_files(dir: &Path, extensions: &[&str]) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    collect_files_recursive(dir, extensions, &mut files)?;
    files.sort();
    Ok(files)
}
