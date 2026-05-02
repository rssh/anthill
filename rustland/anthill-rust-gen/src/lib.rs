//! Generate Rust code from anthill specifications.
//!
//! v1 implements the `rust+anthill` realization profile only — a hybrid
//! bundle whose output is a Rust crate that embeds the anthill spec
//! verbatim and dispatches it through the WI-051 interpreter at runtime.
//! Sibling to the future full-Rust-codegen profile (proposal 029, the
//! `rust_std` LanguageMapping) which is not implemented here.
//!
//! Entry point: [`bundle::generate_bundle`].

pub mod bundle;

pub use bundle::{generate_bundle, BundleError, BundleOptions};
