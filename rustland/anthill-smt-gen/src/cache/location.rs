//! Cache root resolution and on-disk layout.
//!
//! Override chain: `--cache-dir` arg → `ANTHILL_CACHE_DIR` env →
//! `dirs::cache_dir()/anthill/`. (TOML config support deferred until a
//! workspace-config crate exists.) Within the root, entries live at:
//!
//!   `<root>/projects/<sha256(repo_root)>/proofs/<solver>/v<format>/`
//!
//! The repo-root segment isolates each anthill project's cache, so a
//! shared `~/.cache/anthill/` can host many repos without collisions.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::key::CACHE_FORMAT_VERSION;

/// Solver identity for the cache subtree. Per-solver subtrees keep
/// each solver's value-format independent: a Z3 schema bump leaves the
/// dReal subtree untouched.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Solver {
    Z3,
    DReal,
    Cvc5,
}

impl Solver {
    pub fn as_dir(self) -> &'static str {
        match self {
            Solver::Z3 => "z3",
            Solver::DReal => "dreal",
            Solver::Cvc5 => "cvc5",
        }
    }
}

pub fn resolve_cache_root(override_path: Option<&Path>) -> PathBuf {
    if let Some(p) = override_path {
        return p.to_path_buf();
    }
    if let Ok(env) = std::env::var("ANTHILL_CACHE_DIR") {
        if !env.is_empty() {
            return PathBuf::from(env);
        }
    }
    dirs::cache_dir()
        .map(|d| d.join("anthill"))
        .unwrap_or_else(|| PathBuf::from(".anthill-cache"))
}

/// Per-project per-solver subdirectory. Callers should hoist the
/// result out of any per-obligation loop — this canonicalises
/// `repo_root` (a syscall).
pub fn proof_subdir(cache_root: &Path, repo_root: &Path, solver: Solver) -> PathBuf {
    let repo_canon = repo_root.canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let mut h = Sha256::new();
    h.update(repo_canon.to_string_lossy().as_bytes());
    let repo_hash = hex::encode(h.finalize());

    cache_root
        .join("projects")
        .join(repo_hash)
        .join("proofs")
        .join(solver.as_dir())
        .join(format!("v{CACHE_FORMAT_VERSION}"))
}

/// On-disk path for a cache entry. Two-level hex fanout caps any
/// directory at <16K entries even on busy projects.
pub fn entry_path(subdir: &Path, key_hex: &str) -> PathBuf {
    debug_assert!(key_hex.len() >= 4, "cache key too short");
    let level1 = &key_hex[0..2];
    let level2 = &key_hex[2..4];
    let rest = &key_hex[4..];
    subdir
        .join(level1)
        .join(level2)
        .join(format!("{rest}.json"))
}
