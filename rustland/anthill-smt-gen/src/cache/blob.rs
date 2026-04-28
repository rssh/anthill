//! Content-addressed blob storage for proof-witness payloads
//! (proposal 030 phase α.5).
//!
//! Blobs are sha256-keyed text files: SMT-LIB documents, sat models,
//! SLD-derivation trees. Identical content collides deterministically
//! across discharges — the same SMT document produced by two proofs
//! shares one blob on disk. Layout:
//!
//!   `<cache_root>/projects/<sha256(repo_root)>/blobs/v<format>/<aa>/<bb>/<rest>`
//!
//! Sibling to `proof_subdir` (verdict cache) so a project's blobs are
//! isolated from other projects'. Two-level hex fanout caps any
//! directory at <16K entries.
//!
//! Witness construction passes content into `store_blob` and embeds
//! the returned hash in `ProofWitness::SmtDischarge.document_hash` /
//! `SmtVerdict::Sat.model_hash`. The phase-β kernel check fetches
//! payloads via `load_blob` to re-verify discharges.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use super::key::CACHE_FORMAT_VERSION;

/// Per-project blob subdirectory. Mirrors `proof_subdir`'s isolation
/// strategy — each anthill project has its own blob namespace, so
/// cleanup or GC of one project doesn't disturb another.
pub fn blob_subdir(cache_root: &Path, repo_root: &Path) -> PathBuf {
    let repo_canon = repo_root.canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let mut h = Sha256::new();
    h.update(repo_canon.to_string_lossy().as_bytes());
    let repo_hash = hex::encode(h.finalize());

    cache_root
        .join("projects")
        .join(repo_hash)
        .join("blobs")
        .join(format!("v{CACHE_FORMAT_VERSION}"))
}

/// Full on-disk path for a blob, given its content hash.
pub fn blob_path(blob_dir: &Path, content_hash: &str) -> PathBuf {
    debug_assert!(content_hash.len() >= 4, "blob hash too short");
    let l1 = &content_hash[0..2];
    let l2 = &content_hash[2..4];
    let rest = &content_hash[4..];
    blob_dir.join(l1).join(l2).join(rest)
}

/// Hash content as a sha256 hex digest. Pure — no disk access.
/// Used by callers that want a content hash even when the blob isn't
/// stored (e.g. `--no-cache` mode).
pub fn hash_content(content: &str) -> String {
    let mut h = Sha256::new();
    h.update(content.as_bytes());
    hex::encode(h.finalize())
}

/// Write `content` to its content-addressed path; return the hash.
/// Idempotent — if the blob already exists, returns the hash without
/// rewriting (saves a syscall + preserves any prior atime metadata).
/// Atomic via tmp + rename, like `store::store`.
pub fn store_blob(blob_dir: &Path, content: &str) -> io::Result<String> {
    let hash = hash_content(content);
    let path = blob_path(blob_dir, &hash);
    if path.exists() {
        return Ok(hash);
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let tmp = path.with_extension("tmp");
    fs::write(&tmp, content)?;
    fs::rename(&tmp, &path)?;
    Ok(hash)
}

/// Read a blob's content by its hash. `None` for missing / unreadable
/// files; callers treat that as "payload not available" rather than
/// surfacing the I/O error — phase-β check reports verification
/// failures uniformly through the witness layer.
pub fn load_blob(blob_dir: &Path, content_hash: &str) -> Option<String> {
    let path = blob_path(blob_dir, content_hash);
    fs::read_to_string(path).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn store_then_load_roundtrips() {
        let tmp = TempDir::new().unwrap();
        let dir = tmp.path();
        let content = "(set-logic LRA)\n(check-sat)\n";
        let hash = store_blob(dir, content).unwrap();
        assert_eq!(hash.len(), 64);
        assert_eq!(hash, hash_content(content));
        let got = load_blob(dir, &hash).unwrap();
        assert_eq!(got, content);
    }

    #[test]
    fn idempotent_store_returns_same_hash() {
        let tmp = TempDir::new().unwrap();
        let h1 = store_blob(tmp.path(), "same").unwrap();
        let h2 = store_blob(tmp.path(), "same").unwrap();
        assert_eq!(h1, h2);
    }

    #[test]
    fn load_missing_is_none() {
        let tmp = TempDir::new().unwrap();
        assert!(load_blob(tmp.path(), &"de".repeat(32)).is_none());
    }

    #[test]
    fn different_content_different_hash() {
        assert_ne!(hash_content("a"), hash_content("b"));
    }
}
