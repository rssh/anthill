/// Parse errors with source spans.

use crate::span::Span;

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
    /// Format with line:col using source text. The pathless rendering — for a
    /// source that HAS no file (a synthesized one); a caller holding a path
    /// wants [`ParseError::format_located`].
    pub fn format_with_source(&self, source: &str) -> String {
        format!("{}: {}", Span::format_start(source, self.span), self.message)
    }

    /// WI-852: render with the file this error came from — `path:line:col:
    /// message`, the rendering a `LoadError` at the same position gets. What
    /// makes them agree is the shared PREFIX owner,
    /// [`crate::span::render_located`]; the `line:col` half is each family's own
    /// (see that function's note), so this is one owner for the file prefix, not
    /// for the whole line.
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
    pub fn format_located(&self, path: &std::path::Path, source: &str) -> String {
        crate::span::render_located(Some(path), self.format_with_source(source), true)
    }
}
