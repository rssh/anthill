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

/// A span with file identity — for cross-file use in the OccurrenceStore.
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

/// Registry mapping SourceId → file path/name.
pub struct SourceRegistry {
    names: Vec<String>,
}

impl SourceRegistry {
    pub fn new() -> Self {
        Self { names: Vec::new() }
    }

    pub fn register(&mut self, name: String) -> SourceId {
        let id = SourceId(self.names.len() as u32);
        self.names.push(name);
        id
    }

    pub fn name(&self, id: SourceId) -> &str {
        &self.names[id.index()]
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}
