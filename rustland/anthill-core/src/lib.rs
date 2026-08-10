//! Anthill kernel: terms, parser, knowledge base, resolution, codegen.
//!
//! READ THESE DOCS WITH `--document-private-items`:
//!
//! ```text
//! cargo doc -p anthill-core --no-deps --document-private-items --open
//! ```
//!
//! This is a workspace-internal crate — every consumer is a path dependency
//! (`anthill-cli`, `anthill-stl`, the `*-gen` crates), and the doc comments are
//! written for whoever is changing the code, not for an outside caller. They
//! therefore link freely into private items: the invariant a `pub` method must
//! uphold usually lives in the private helper that enforces it, and a doc that
//! could not name it would be documenting the wrong half.
//!
//! `private_intra_doc_links` is allowed for exactly that reason. It fires when a
//! public item's doc links somewhere a downstream reader could not follow — a
//! real defect in a PUBLISHED library, and not a situation this crate has. All
//! such links resolve under the command above. Should anthill-core ever ship as
//! a library, this allow is the thing to remove first.
//!
//! The allow covers ONLY visibility. A link naming an item that does not exist
//! is still a defect and still warns (`broken_intra_doc_links` stays on), as do
//! malformed markup and `<placeholder>` notation left outside backticks, which
//! rustdoc silently eats from the rendered page.
//!
//! CHECK THE PRIVATE-ITEMS VIEW, NOT THE PUBLIC ONE. Plain `cargo doc` inspects
//! only public items, so it cannot see a broken link inside a private one — and
//! most of this crate is private. A clean plain run is therefore no evidence;
//! the command at the top is the one whose warnings count.
#![allow(rustdoc::private_intra_doc_links)]

pub mod codegen;
pub mod eval;
pub mod fs_util;
pub mod intern;
pub mod kb;
pub mod parse;
pub mod persistence;
pub mod span;
