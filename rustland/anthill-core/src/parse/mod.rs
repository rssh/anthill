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
            // WI-745: keep the source so a load error's byte span can render as
            // `line:col`. The path is unknown here — the caller stamps it via
            // `ParsedFile::with_path`.
            source: std::sync::Arc::from(source),
            path: None,
        })
    } else {
        errors.sort_by_key(|e| e.span.start);
        Err(errors)
    }
}

/// Walk the CST collecting tree-sitter ERROR / MISSING nodes, plus the
/// zero-width nodes tree-sitter inserts for an absent token (WI-778) — which
/// carry NEITHER flag and so would otherwise pass for clean syntax.
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
        // MISSING, or (WI-778) a node tree-sitter inserted for an absent token,
        // which exposes neither ERROR nor MISSING on the VISIBLE tree, only
        // `has_error()`.
        //
        // WHY WIDTH AND NOT THE FLAG. The MISSING flag is not absent, it is
        // HIDDEN: `identifier: $ => reserved('none', $._identifier_token)`
        // (grammar.js) keeps `identifier` a real non-terminal, so recovery marks
        // the INVISIBLE `_identifier_token` MISSING while the visible wrapper
        // inherits only `error_cost` — and `Node::children()` skips invisible
        // nodes, so `is_missing()` is unreachable from here. `tree-sitter parse`
        // on `entity e(: Int64)` shows it: `name: (identifier [2,13] - [2,13])`,
        // zero-width, no MISSING marker. Width is therefore the observable the
        // flag only proxies for.
        //
        // It subsumes the flag rather than merely coinciding with it: a MISSING
        // leaf is built zero-width BY CONSTRUCTION (`ts_subtree_new_missing_leaf`
        // uses `length_zero()`), so ONE predicate covers both — nothing was
        // consumed here, so something is absent. The one way that could break is
        // `ts_subtree_edit`, which can resize a subtree while carrying `is_missing`
        // forward; that needs an INCREMENTAL reparse, and `parse()` above always
        // passes `None` as the old tree. Restore the `is_missing()` arm if that
        // ever changes.
        //
        // Before this arm existed the unflagged half fell through to the descend
        // below, iterated its zero (or equally zero-width) children, and
        // vanished — `entity e(: Int64)`, `entity e(a: )` and `operation f(:
        // Int64) -> Int64` all parsed CLEAN, with the converter's
        // `intern(text(n))` interning the EMPTY STRING as a real field name. The
        // ticket blamed the `has_error()` prune above; measured, `has_error()` is
        // TRUE on such a node and every ancestor, so the walk always reached it
        // and the prune keeps its full pruning power. Reported at the OUTERMOST
        // zero-width node, which names the absent part the way the author would
        // (`simple_type` for a missing type, `identifier` for a missing name);
        // descending would only re-derive the same hole one level deeper.
        //
        // Ordered AFTER `is_error` so a zero-width ERROR — garbage PRESENT, not a
        // hole — keeps its own diagnosis rather than being recast as "missing".
        // No such node was observed in practice; this is ordering discipline, not
        // a fix for a measured case.
        //
        // Owning this at the WALK is what makes the ~31 `intern(self.text(n))`
        // sites in `parse/convert.rs` inherit it: the ticket named THREE
        // producers — only TWO of them in this class — and measurement found TEN
        // silent spellings. Same PATHOLOGY as WI-440 and WI-766, but they closed
        // it in OPPOSITE directions: WI-766 made `(Int64,)` an ERROR, WI-440 made
        // `@ {}` LEGAL. Both are grammar-level and each closes one production;
        // this is the general net under them. See the header of
        // `tests/include/wi778_zero_width_token_test.rs`.
        if node.byte_range().is_empty() {
            errors.push(ParseError::new(
                format!("missing `{}`", node.kind()),
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
