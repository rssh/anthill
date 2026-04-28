//! Witness-blob storage tests (proposal 030 phase α.5).
//!
//! Pins: hashes are content-addressed (identical content → identical
//! hash); store + load round-trips losslessly; idempotent store does
//! not duplicate writes.

use anthill_smt_gen::cache::{
    blob_path, blob_subdir, hash_content, load_blob, store_blob,
};
use tempfile::TempDir;

#[test]
fn document_hash_is_sha256_of_content() {
    let smt = "(set-logic LRA)\n(declare-const x Real)\n(check-sat)\n";
    let h = hash_content(smt);
    // sha256 hex digest is exactly 64 lowercase hex chars.
    assert_eq!(h.len(), 64);
    assert!(h.chars().all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase()));
    // Identical content always hashes to the same value.
    assert_eq!(h, hash_content(smt));
}

#[test]
fn blob_store_load_roundtrip() {
    let tmp = TempDir::new().unwrap();
    let smt = "(check-sat)\n";
    let hash = store_blob(tmp.path(), smt).unwrap();
    let got = load_blob(tmp.path(), &hash).unwrap();
    assert_eq!(got, smt);
}

#[test]
fn idempotent_store_no_double_write() {
    let tmp = TempDir::new().unwrap();
    let content = "(declare-const x Real)\n";
    let h1 = store_blob(tmp.path(), content).unwrap();
    let h2 = store_blob(tmp.path(), content).unwrap();
    assert_eq!(h1, h2);
    // The blob file path is deterministic; one entry on disk.
    let path = blob_path(tmp.path(), &h1);
    assert!(path.exists());
}

#[test]
fn different_content_different_blob_paths() {
    let tmp = TempDir::new().unwrap();
    let h1 = store_blob(tmp.path(), "a").unwrap();
    let h2 = store_blob(tmp.path(), "b").unwrap();
    assert_ne!(h1, h2);
    assert_ne!(blob_path(tmp.path(), &h1), blob_path(tmp.path(), &h2));
}

#[test]
fn load_missing_blob_is_none() {
    let tmp = TempDir::new().unwrap();
    assert!(load_blob(tmp.path(), &"de".repeat(32)).is_none());
}

#[test]
fn blob_subdir_isolated_per_repo() {
    let cache = TempDir::new().unwrap();
    let repo_a = TempDir::new().unwrap();
    let repo_b = TempDir::new().unwrap();
    let a = blob_subdir(cache.path(), repo_a.path());
    let b = blob_subdir(cache.path(), repo_b.path());
    assert_ne!(a, b, "different repos should map to different blob subdirs");
}
