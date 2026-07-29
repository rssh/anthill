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
    /// Format with line:col against an already-built index. The one place a
    /// parse error's `line:col: message` body is spelled; everything else here
    /// goes through it.
    fn format_at(&self, loc: &LineIndex) -> String {
        format!("{}: {}", loc.format_start(self.span), self.message)
    }

    /// Format with line:col using source text. The pathless rendering — for a
    /// source that HAS no file (a synthesized one); a caller holding a path
    /// wants [`ParseError::all_located`], or
    /// [`ParseError::format_located_at`] for a single error.
    ///
    /// Builds a [`LineIndex`] for this ONE error, which is why there is no
    /// path-bearing one-shot beside it: a printer holds a whole `Vec` and must
    /// index the source once — see [`ParseError::all_located`].
    pub fn format_with_source(&self, source: &str) -> String {
        self.format_at(&LineIndex::new(source))
    }

    /// Render EVERY error from one source, located in `path` — the entry point
    /// for a printer, which always has a whole `Vec<ParseError>` in hand.
    ///
    /// Exists because the per-error path resolves a position by walking the
    /// source, and doing that once per error is O(N × len): measured at ~50 s in
    /// the debug CLI for 2100 diagnostics on a 2.7 MB file, against ~1 s once the
    /// index is built once here. Rendering a batch through this — rather than
    /// resolving each error against the raw source — is the difference.
    pub fn all_located(
        errors: &[ParseError],
        path: &std::path::Path,
        source: &str,
    ) -> Vec<String> {
        let loc = LineIndex::new(source);
        errors.iter().map(|e| e.format_located_at(path, &loc)).collect()
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
