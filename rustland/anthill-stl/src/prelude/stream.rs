//! Host realization of `anthill.prelude.Stream`.
//!
//! WI-553: the `Stream` trait is GENERATED from
//! `stdlib/anthill/prelude/stream.anthill` (object-safe — `boxed_trait_objects`
//! boxes the `Self`/recursive-tail returns, the generic fold methods are
//! `Self: Sized`-bound) and `include!`d below, so the spec is the single source
//! of truth. This module only supplies the one import the generated signatures
//! reference (`Pair`); the spec's body/rule imports are suppressed
//! (`suppress_imports`) since the signature-only output never uses them.
//! `SearchStreamAdapter` (`reflect/bridge.rs`) is the host implementation.
#![allow(unused_imports)]

use crate::prelude::Pair;

include!(concat!(env!("OUT_DIR"), "/stream.rs"));
