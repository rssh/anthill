//! JSON-per-entry on-disk cache store.
//!
//! Atomic writes via sibling `.tmp` + rename — partial writes never
//! produce corrupt cache hits. No `fsync` per write: the rename gives
//! crash-atomicity for individual entries, and a lost cache entry just
//! means re-running a proof.

use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use super::location::entry_path;

/// On-disk cache record. Fields are `pub` because this is a serde DTO;
/// `#[non_exhaustive]` keeps adding fields non-breaking for downstream.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct CacheEntry {
    /// The cache key (sha256 hex). Self-describing for forensic
    /// inspection — entries are read out-of-band by `--show-cache`.
    pub key: String,
    pub verdict: String,
    pub solver_secs: f64,
    pub z3_version: String,
    pub written_at: String,
    #[serde(default)]
    pub raw_output: String,
    /// Captured Z3 model text for `sat` verdicts when
    /// `produce_models` was on. Empty otherwise.
    #[serde(default)]
    pub model_text: String,
    /// Best-effort `(name, value)` pairs extracted from the model.
    #[serde(default)]
    pub variable_assignments: Vec<(String, String)>,
    /// Names from `(get-unsat-core)` for `unsat` verdicts when
    /// `produce_unsat_cores` was on.
    #[serde(default)]
    pub unsat_core: Vec<String>,
    /// Content hash of the SMT-LIB document that produced this
    /// entry (proposal 030 phase α.5 — `ProofWitness::SmtDischarge.
    /// document_hash`). Empty for legacy entries written before
    /// α.5; readers fall back to recomputing if needed.
    #[serde(default)]
    pub document_hash: String,
    /// Content hash of the sat model text (when applicable). Empty
    /// for unsat / unknown verdicts and legacy entries. Used as
    /// `SmtVerdict::Sat.model_hash` in the witness.
    #[serde(default)]
    pub model_hash: String,
}

impl CacheEntry {
    pub fn new(
        key: String,
        verdict: String,
        solver_secs: f64,
        z3_version: String,
        written_at: String,
        raw_output: String,
    ) -> Self {
        Self {
            key, verdict, solver_secs, z3_version, written_at, raw_output,
            model_text: String::new(),
            variable_assignments: Vec::new(),
            unsat_core: Vec::new(),
            document_hash: String::new(),
            model_hash: String::new(),
        }
    }
}

/// Look up an entry by key. Missing files / corrupt JSON / path-key
/// mismatches all surface as `None`.
pub fn lookup(subdir: &Path, key: &str) -> Option<CacheEntry> {
    let path = entry_path(subdir, key);
    let bytes = fs::read(&path).ok()?;
    let entry: CacheEntry = serde_json::from_slice(&bytes).ok()?;
    if entry.key != key { return None; }
    Some(entry)
}

/// Atomically write an entry. Creates parent directories as needed.
pub fn store(subdir: &Path, entry: &CacheEntry) -> io::Result<PathBuf> {
    let path = entry_path(subdir, &entry.key);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let tmp = path.with_extension("json.tmp");
    {
        let mut f = fs::File::create(&tmp)?;
        let bytes = serde_json::to_vec_pretty(entry)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        f.write_all(&bytes)?;
    }
    fs::rename(&tmp, &path)?;
    Ok(path)
}

pub fn invalidate(subdir: &Path, key: &str) {
    let path = entry_path(subdir, key);
    let _ = fs::remove_file(path);
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn fixture() -> CacheEntry {
        CacheEntry::new(
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".into(),
            "proved".into(),
            0.42,
            "Z3 version 4.13.0".into(),
            "2026-04-27T12:00:00Z".into(),
            "unsat\n".into(),
        )
    }

    #[test]
    fn store_then_lookup_roundtrips() {
        let tmp = TempDir::new().unwrap();
        let entry = fixture();
        store(tmp.path(), &entry).unwrap();
        let got = lookup(tmp.path(), &entry.key).unwrap();
        assert_eq!(got.key, entry.key);
        assert_eq!(got.verdict, entry.verdict);
        assert_eq!(got.raw_output, entry.raw_output);
    }

    #[test]
    fn lookup_missing_is_none() {
        let tmp = TempDir::new().unwrap();
        assert!(lookup(tmp.path(), "deadbeef".repeat(8).as_str()).is_none());
    }

    #[test]
    fn corrupt_file_treated_as_miss() {
        let tmp = TempDir::new().unwrap();
        let key = "deadbeef".repeat(8);
        let p = entry_path(tmp.path(), &key);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, b"not json").unwrap();
        assert!(lookup(tmp.path(), &key).is_none());
    }
}
