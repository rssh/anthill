//! Proof cache: content-addressed XDG-located persistent store of
//! verdicts for prior solver invocations.
//!
//! See `key.rs` for the key construction (cache invalidation guarantee),
//! `store.rs` for the on-disk JSON format, and `location.rs` for the
//! directory layout / XDG resolution.

pub mod blob;
pub mod key;
pub mod location;
pub mod store;
pub mod witness;

pub use blob::{blob_path, blob_subdir, hash_content, load_blob, store_blob};
pub use key::{build_key, state_hash, KeyInputs, CACHE_FORMAT_VERSION, STATE_HASH_FORMAT_VERSION};
pub use location::{entry_path, proof_subdir, resolve_cache_root, Solver};
pub use store::{invalidate, lookup, store as store_entry, CacheEntry};
pub use witness::{
    load_witness, store_witness, witness_path, witness_subdir,
    SmtVerdictDto, WitnessShape, WitnessSidecar,
};
