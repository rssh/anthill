//! Witness sidecar persistence (proposal 030, WI-124).
//!
//! Bridges the gap between `anthill prove` (produces witnesses,
//! today discards them after CLI printing) and `anthill check`
//! (verifies witnesses, today only sees the loader's placeholders).
//! One sidecar JSON per project per rule QN, content-addressed by
//! the underlying SMT-LIB document via the existing blob store.
//!
//! Layout:
//!   `<cache_root>/projects/<sha256(repo_root)>/witnesses/v<format>/<sanitised-qn>.json`
//!
//! Lives alongside `proofs/` and `blobs/` under the same per-project
//! root so cleanup of one project doesn't disturb another.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::key::CACHE_FORMAT_VERSION;

/// Per-project witness sidecar directory.
pub fn witness_subdir(cache_root: &Path, repo_root: &Path) -> PathBuf {
    let repo_canon = repo_root.canonicalize()
        .unwrap_or_else(|_| repo_root.to_path_buf());
    let mut h = Sha256::new();
    h.update(repo_canon.to_string_lossy().as_bytes());
    let repo_hash = hex::encode(h.finalize());

    cache_root
        .join("projects")
        .join(repo_hash)
        .join("witnesses")
        .join(format!("v{CACHE_FORMAT_VERSION}"))
}

/// Sanitise a rule QN into a filesystem-safe filename.
pub fn witness_path(witness_dir: &Path, rule_qn: &str) -> PathBuf {
    let safe: String = rule_qn.chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '.' || c == '_' { c } else { '_' })
        .collect();
    witness_dir.join(format!("{safe}.json"))
}

/// Serializable witness sidecar. Mirrors the `SmtDischarge` shape
/// for v0; `MetaCompose` (induction / ranking compositions) is
/// captured by recording the meta-tactic name + sub-witnesses
/// flattened out so the JSON is human-readable. Other constructors
/// fall through `WitnessShape::Other`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessSidecar {
    pub rule_qn: String,
    pub verdict_label: String,
    pub witness: WitnessShape,
    pub state_hash: String,
    pub written_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum WitnessShape {
    SmtDischarge {
        backend: String,
        logic: String,
        document_hash: String,
        verdict: SmtVerdictDto,
        #[serde(default)]
        core: Option<String>,
    },
    SldDerivation {
        tree_hash: String,
    },
    MetaCompose {
        tactic_name: String,
        sub: Vec<WitnessShape>,
    },
    ScopeAxiom {
        scope_kind: String,
        scope_qn: String,
        aspect: String,
    },
    Specialization {
        parametric: String,
        substitution: Vec<(String, String)>,
        instances: Vec<String>,
    },
    TrustedAxiom {
        reason: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum SmtVerdictDto {
    Unsat,
    Sat { model_hash: String },
    Unknown { reason: String },
}

/// Atomic write — sibling .tmp + rename, like store_entry. Creates
/// parent directories as needed.
pub fn store_witness(witness_dir: &Path, sidecar: &WitnessSidecar) -> io::Result<PathBuf> {
    let path = witness_path(witness_dir, &sidecar.rule_qn);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    let tmp = path.with_extension("json.tmp");
    let bytes = serde_json::to_vec_pretty(sidecar)
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    fs::write(&tmp, &bytes)?;
    fs::rename(&tmp, &path)?;
    Ok(path)
}

/// Read a sidecar by rule QN. Missing files / corrupt JSON / qn-
/// mismatch surface as `None`. Phase β's `check` falls back to the
/// in-source placeholder witness when no sidecar exists.
pub fn load_witness(witness_dir: &Path, rule_qn: &str) -> Option<WitnessSidecar> {
    let path = witness_path(witness_dir, rule_qn);
    let bytes = fs::read(&path).ok()?;
    let sidecar: WitnessSidecar = serde_json::from_slice(&bytes).ok()?;
    if sidecar.rule_qn != rule_qn { return None; }
    Some(sidecar)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn fixture() -> WitnessSidecar {
        WitnessSidecar {
            rule_qn: "test.foo.bar".into(),
            verdict_label: "Proved".into(),
            witness: WitnessShape::SmtDischarge {
                backend: "z3".into(),
                logic: "LRA".into(),
                document_hash: "ab".repeat(32),
                verdict: SmtVerdictDto::Unsat,
                core: None,
            },
            state_hash: "cd".repeat(32),
            written_at: "@1234567890".into(),
        }
    }

    #[test]
    fn store_then_load_roundtrips() {
        let tmp = TempDir::new().unwrap();
        let s = fixture();
        store_witness(tmp.path(), &s).unwrap();
        let got = load_witness(tmp.path(), &s.rule_qn).unwrap();
        assert_eq!(got.rule_qn, s.rule_qn);
        assert_eq!(got.verdict_label, s.verdict_label);
    }

    #[test]
    fn load_missing_is_none() {
        let tmp = TempDir::new().unwrap();
        assert!(load_witness(tmp.path(), "nope").is_none());
    }

    #[test]
    fn qn_mismatch_treated_as_miss() {
        let tmp = TempDir::new().unwrap();
        let s = fixture();
        let path = witness_path(tmp.path(), "different.qn");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        let bytes = serde_json::to_vec_pretty(&s).unwrap();
        std::fs::write(&path, &bytes).unwrap();
        assert!(load_witness(tmp.path(), "different.qn").is_none());
    }
}
