//! Bake the build-time version provenance into the crate as `rustc-env`
//! variables: the git short SHA of HEAD and the build date (ISO-8601 UTC).
//! `lib.rs` reads them with `env!`. Both are repo-wide (the same for every
//! consuming binary) — the per-binary name/semver come from the consumer's
//! own Cargo metadata via the `version_string!` macro.

use std::process::Command;

use chrono::{DateTime, Utc};

/// Run a git command, returning its trimmed stdout when it succeeds.
fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git").args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    let s = String::from_utf8(out.stdout).ok()?.trim().to_string();
    (!s.is_empty()).then_some(s)
}

fn main() {
    // Git short SHA of HEAD. "unknown" when built outside a git checkout
    // (e.g. from a packaged source tarball) so the stamp is always populated.
    let sha = git(&["rev-parse", "--short", "HEAD"]).unwrap_or_else(|| "unknown".to_string());
    println!("cargo:rustc-env=ANTHILL_VERSION_GIT_SHA={sha}");

    // Build date, ISO-8601 UTC. Honour SOURCE_DATE_EPOCH for reproducible
    // builds; otherwise stamp the current wall-clock time.
    let date: DateTime<Utc> = std::env::var("SOURCE_DATE_EPOCH")
        .ok()
        .and_then(|s| s.parse::<i64>().ok())
        .and_then(|epoch| DateTime::from_timestamp(epoch, 0))
        .unwrap_or_else(Utc::now);
    println!(
        "cargo:rustc-env=ANTHILL_VERSION_BUILD_DATE={}",
        date.format("%Y-%m-%dT%H:%M:%SZ")
    );
    println!("cargo:rerun-if-env-changed=SOURCE_DATE_EPOCH");

    // Re-run when HEAD moves so the embedded SHA tracks `git rev-parse HEAD`
    // — otherwise the cached build-script output (and stale SHA) survives a
    // commit. Track HEAD, the ref it points at (loose), and packed-refs (in
    // case the ref has been packed and the loose file is absent). Resolve
    // each via `git rev-parse --git-path`, which accounts for linked
    // worktrees (HEAD is per-worktree; refs/packed-refs live in the common
    // git dir) — a manual `<git-dir>/<name>` join would mis-track there.
    if let Some(head_path) = git(&["rev-parse", "--git-path", "HEAD"]) {
        println!("cargo:rerun-if-changed={head_path}");
        if let Ok(contents) = std::fs::read_to_string(&head_path) {
            if let Some(refname) = contents.strip_prefix("ref:").map(str::trim) {
                if let Some(ref_path) = git(&["rev-parse", "--git-path", refname]) {
                    println!("cargo:rerun-if-changed={ref_path}");
                }
            }
        }
    }
    if let Some(packed) = git(&["rev-parse", "--git-path", "packed-refs"]) {
        println!("cargo:rerun-if-changed={packed}");
    }
}
