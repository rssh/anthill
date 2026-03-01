pub mod filesystem;
pub mod sql;

use crate::reflect::Error;

include!(concat!(env!("OUT_DIR"), "/store.rs"));
