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

/// The `PassId` tagging a MACRO-BUILT occurrence — the sibling of
/// [`simp_pass`](crate::kb::simp_rewrite::simp_pass), which tags a template-SUBSTITUTED
/// one. `make_apply`'s doc has named the split since WI-722: it is what distinguishes a
/// node a macro constructed from one the `[simp]` engine substituted.
///
/// WI-20260820-5R2XT gave that distinction its first READER
/// ([`NodeOccurrence::surface_call_name`](crate::kb::node_occurrence::NodeOccurrence::surface_call_name)),
/// and moved the name here so it has ONE owner: it was spelled out at each of the two
/// splice builtins, and a reader comparing against a third copy would have been a silent
/// no-match rather than a compile error.
pub(crate) const MACRO_EXPAND_PASS_NAME: &str = "anthill.kb.passes.macro_expand";

pub(crate) fn macro_expand_pass(kb: &mut crate::kb::KnowledgeBase) -> PassId {
    kb.register_pass(MACRO_EXPAND_PASS_NAME)
}
