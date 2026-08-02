// No `pub mod sql` — see the file map in `build.rs` (WI-934).
pub mod filesystem;

use crate::reflect::Error;

include!(concat!(env!("OUT_DIR"), "/store.rs"));
