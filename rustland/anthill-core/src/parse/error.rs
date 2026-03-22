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
    /// Format with line:col using source text.
    pub fn format_with_source(&self, source: &str) -> String {
        let (line, col) = Span::line_col(source, self.span.start);
        format!("{}:{}: {}", line, col, self.message)
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "parse error at {}..{}: {}",
            self.span.start, self.span.end, self.message
        )
    }
}

impl std::error::Error for ParseError {}
