//! WI-251 — the legacy `OccurrenceStore` arena and `OccurrenceId` /
//! `ExprOccurrenceId` handles were deleted in favor of the value-typed
//! `NodeOccurrence` tree (see `node_occurrence.rs`). Spans are looked
//! up via `kb.term_spans` / `kb.functor_spans` side-tables populated
//! during load. This module now only houses `PassId`, the
//! identifier for synthesizing passes that produce `Synthesized`
//! origins on a NodeOccurrence — kept here for stable import paths.
//!
//! See: docs/design/occurrence-as-value-type.md

use crate::intern::Symbol;

/// Identifier for a compiler pass that can synthesize occurrences.
/// Newtype over Symbol — typed wrapper preventing accidental Symbol
/// mixing; same 4-byte cost. Passes register once at KB construction
/// (or first use) via `kb.register_pass("anthill.kb.passes.<name>")
/// -> PassId`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PassId(Symbol);

impl PassId {
    pub fn symbol(self) -> Symbol {
        self.0
    }

    pub(crate) fn from_symbol(sym: Symbol) -> Self {
        PassId(sym)
    }
}
