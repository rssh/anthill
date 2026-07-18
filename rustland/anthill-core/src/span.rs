/// Source location tracking (byte offsets into the source text).

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn from_ts_node(node: &tree_sitter::Node) -> Self {
        Self {
            start: node.start_byte() as u32,
            end: node.end_byte() as u32,
        }
    }

    pub fn merge(a: Span, b: Span) -> Span {
        Span {
            start: a.start.min(b.start),
            end: a.end.max(b.end),
        }
    }

    /// Convert byte offset to (line, col), both 1-based.
    pub fn line_col(source: &str, byte_offset: u32) -> (usize, usize) {
        let offset = byte_offset as usize;
        let mut line = 1;
        let mut col = 1;
        for (i, ch) in source.char_indices() {
            if i >= offset {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        (line, col)
    }

    /// Format as "line:col" for error reporting.
    pub fn format_start(source: &str, span: Span) -> String {
        let (line, col) = Span::line_col(source, span.start);
        format!("{}:{}", line, col)
    }
}

// ── Source identification ──────────────────────────────────────

/// Opaque handle to a loaded source text. Sequential, not hash-consed.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SourceId(u32);

impl SourceId {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn from_raw(raw: u32) -> Self {
        SourceId(raw)
    }

    pub fn raw(self) -> u32 {
        self.0
    }
}

/// A span with file identity — for cross-file use in the legacy occurrence side-table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub source: SourceId,
    pub span: Span,
}

impl SourceSpan {
    pub fn new(source: SourceId, start: u32, end: u32) -> Self {
        Self { source, span: Span::new(start, end) }
    }

    pub fn from_span(source: SourceId, span: Span) -> Self {
        Self { source, span }
    }

    pub fn start(&self) -> u32 {
        self.span.start
    }

    pub fn end(&self) -> u32 {
        self.span.end
    }
}

/// A registered source: its display name plus (WI-745) the on-disk path and full
/// text, so a `SourceId` carried by a span can be rendered as `path:line:col`.
struct SourceEntry {
    name: String,
    /// The file's source text. Empty for sources registered by name only
    /// (`register`), in which case span rendering degrades to `1:1`.
    source: std::sync::Arc<str>,
    /// The on-disk path, if known. `None` for embedded / synthetic sources.
    path: Option<std::sync::Arc<std::path::Path>>,
}

/// Registry mapping SourceId → file name + (WI-745) path + source text.
pub struct SourceRegistry {
    entries: Vec<SourceEntry>,
}

impl SourceRegistry {
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    /// Register a source by name only (no text/path). Span rendering against
    /// this source degrades to `1:1`.
    pub fn register(&mut self, name: String) -> SourceId {
        let id = SourceId(self.entries.len() as u32);
        self.entries.push(SourceEntry {
            name,
            source: std::sync::Arc::from(""),
            path: None,
        });
        id
    }

    /// WI-745: register a source WITH its on-disk path and full text, so a load
    /// error carrying the returned `SourceId` renders `path:line:col: message`.
    pub fn register_file(
        &mut self,
        name: String,
        source: std::sync::Arc<str>,
        path: Option<std::sync::Arc<std::path::Path>>,
    ) -> SourceId {
        let id = SourceId(self.entries.len() as u32);
        self.entries.push(SourceEntry { name, source, path });
        id
    }

    pub fn name(&self, id: SourceId) -> &str {
        &self.entries[id.index()].name
    }

    /// WI-745: the `(path, source text)` provenance of a source, for rendering a
    /// span as `path:line:col`. Returns `None` if the id is out of range or the
    /// source carries no text (registered by name only).
    pub fn provenance(
        &self,
        id: SourceId,
    ) -> Option<(Option<std::sync::Arc<std::path::Path>>, std::sync::Arc<str>)> {
        let e = self.entries.get(id.index())?;
        if e.source.is_empty() {
            return None;
        }
        Some((e.path.clone(), e.source.clone()))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}
