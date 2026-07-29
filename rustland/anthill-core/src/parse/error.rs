/// Parse errors with source spans.

use crate::span::{LineIndex, Span};

#[derive(Clone, Debug)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl ParseError {
    pub fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

impl ParseError {
    /// `line:col: message` — the PATHLESS rendering, for a source that has no
    /// file (a synthesized one). The one place a parse error's body is spelled;
    /// everything else here goes through it.
    ///
    /// Takes the index rather than the text, so a caller with several errors
    /// cannot accidentally re-index per error: that was O(N × len), measured at
    /// 50 s for 2100 diagnostics over 2.7 MB. The convenience one-shot that used
    /// to sit here (`format_with_source`) is deleted for the same reason
    /// `Display` was — a shape that must not be used in a loop should not be the
    /// easy one to reach for. Batch printers want [`ParseError::all_located`].
    pub fn format_at(&self, loc: &LineIndex) -> String {
        format!("{}: {}", loc.format_start(self.span), self.message)
    }

    /// Render EVERY error from one source, located in `path` — the entry point
    /// for a printer, which always has a whole `Vec<ParseError>` in hand.
    ///
    /// Exists because the per-error path resolves a position by walking the
    /// source, and doing that once per error is O(N × len): measured at ~50 s in
    /// the debug CLI for 2100 diagnostics on a 2.7 MB file, against ~1 s once the
    /// index is built once here. Rendering a batch through this — rather than
    /// resolving each error against the raw source — is the difference.
    /// Returns an ITERATOR so a printer writes each line as it renders it, the
    /// way the per-error loops this replaced did.
    pub fn all_located<'a>(
        errors: &'a [ParseError],
        path: &'a std::path::Path,
        source: &'a str,
    ) -> impl Iterator<Item = String> + 'a {
        let loc = LineIndex::new(source);
        errors.iter().map(move |e| e.format_located_at(path, &loc))
    }

    /// WI-852: render with the file this error came from — `path:line:col:
    /// message`, character-for-character the rendering a `LoadError` at the same
    /// position gets. Both halves are shared: the file prefix by
    /// [`crate::span::render_located`], the position by
    /// [`LineIndex::format_start`], which `LoadError`'s message arms also use.
    ///
    /// WHY A RENDERING AND NOT A CARRIER. WI-745 gave `LoadError` a `Located`
    /// wrapper storing `(path, source, inner)`, and WI-852's ticket asked for
    /// the same here unless there was a reason. The reason is that the two
    /// families travel differently. A `LoadError` is raised deep in the loader
    /// with no `&ParsedFile` in hand and reaches `load_all`'s caller merged with
    /// N other files' errors, so its file identity has to RIDE with it. A
    /// `ParseError` is returned by `parse()` straight to the caller that just
    /// read the text, and is rendered in that same expression: a carrier would
    /// be constructed and consumed on one line. The single exception —
    /// `PersistenceError`, which used to hold `ParseError`s across a boundary —
    /// renders at its raise site instead, so nothing in the tree now stores an
    /// unrendered `ParseError`. What the wrapper is actually FOR, one owner of
    /// the prefix rule, is what `render_located` provides.
    ///
    /// The cost is that this is a call-site obligation rather than a type
    /// invariant, which is why the sourceless `Display` was DELETED rather than
    /// documented: with no `Display` and no `Error` impl, a printer that forgets
    /// does not compile, so the obligation is enforced after all.
    ///
    /// A `ParseError`'s span is not optional, so this always renders as
    /// span-bearing. The two spanless-by-construction producers (`parse()`'s
    /// grammar-load and no-tree arms, which pass `Span::default()`) report a
    /// tree-sitter ABI failure rather than a position in the text, and would say
    /// `1:1`; they are build regressions, not conditions an author can reach.
    pub fn format_located_at(&self, path: &std::path::Path, loc: &LineIndex) -> String {
        crate::span::render_located(Some(path), self.format_at(loc), true)
    }

}
