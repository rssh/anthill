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
}
