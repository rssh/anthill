//! Proof cache: content-addressed XDG-located persistent store of
//! verdicts for prior solver invocations.
//!
//! See `key.rs` for the key construction (cache invalidation guarantee),
//! `store.rs` for the on-disk JSON format, and `location.rs` for the
//! directory layout / XDG resolution.

pub mod key;
pub mod location;
pub mod store;

pub use key::{build_key, KeyInputs, CACHE_FORMAT_VERSION};
pub use location::{entry_path, proof_subdir, resolve_cache_root, Solver};
pub use store::{invalidate, lookup, store as store_entry, CacheEntry};
