/// Parser — tree-sitter CST → typed parse IR.
///
/// Entry point: `parse(source) -> Result<ParsedFile, Vec<ParseError>>`

pub mod ir;
pub mod error;
pub mod pratt;
mod convert;

use ir::ParsedFile;
use error::ParseError;

/// Parse an `.anthill` source string into a typed parse IR.
pub fn parse(source: &str) -> Result<ParsedFile, Vec<ParseError>> {
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_anthill::LANGUAGE.into())
        .map_err(|e| vec![ParseError::new(format!("failed to load grammar: {e}"), crate::span::Span::default())])?;

    let tree = parser
        .parse(source, None)
        .ok_or_else(|| vec![ParseError::new("tree-sitter parse returned None", crate::span::Span::default())])?;

    // Surface tree-sitter ERROR / MISSING nodes early. tree-sitter recovers
    // from malformed input by inserting these and continuing; the converter
    // walks past anything it doesn't recognise, so a broken construct would
    // otherwise be silently dropped. Fail fast instead (CLAUDE.md: "avoid
    // fallbacks, know about errors early").
    let mut errors = collect_syntax_errors(tree.root_node(), source);

    let mut converter = convert::Converter::new(source);
    converter.convert_file(tree.root_node());
    errors.append(&mut converter.errors);

    if errors.is_empty() {
        Ok(ParsedFile {
            items: converter.items,
            symbols: converter.symbols,
            terms: converter.terms,
        })
    } else {
        errors.sort_by_key(|e| e.span.start);
        Err(errors)
    }
}

/// Walk the CST collecting tree-sitter ERROR / MISSING nodes.
///
/// Clean subtrees are pruned via `has_error()`, so the walk only descends
/// where an error actually lives, and reports each error / missing node once
/// (it does not descend into an ERROR subtree's children). Results are
/// source-ordered by start byte.
fn collect_syntax_errors(root: tree_sitter::Node, source: &str) -> Vec<ParseError> {
    let mut errors = Vec::new();
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        // No error anywhere in this subtree (and not itself missing) — prune.
        if !node.has_error() && !node.is_missing() {
            continue;
        }
        if node.is_missing() {
            errors.push(ParseError::new(
                format!("missing `{}`", node.kind()),
                crate::span::Span::from_ts_node(&node),
            ));
            continue;
        }
        if node.is_error() {
            let text = &source[node.start_byte()..node.end_byte()];
            let snippet: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
            let snippet = if snippet.chars().count() > 40 {
                let truncated: String = snippet.chars().take(40).collect();
                format!("{truncated}…")
            } else {
                snippet
            };
            errors.push(ParseError::new(
                format!("syntax error near `{snippet}`"),
                crate::span::Span::from_ts_node(&node),
            ));
            continue;
        }
        // Interior node that merely *contains* an error — descend.
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            stack.push(child);
        }
    }
    errors.sort_by_key(|e| e.span.start);
    errors
}
