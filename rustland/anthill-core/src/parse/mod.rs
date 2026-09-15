mod convert;
pub mod desugar_target;
pub mod error;
/// Parser — tree-sitter CST → typed parse IR.
///
/// Entry point: `parse(source) -> Result<ParsedFile, Vec<ParseError>>`
pub mod ir;
pub mod pratt;

use error::ParseError;
use ir::ParsedFile;

/// Parse an `.anthill` source string into a typed parse IR.
pub fn parse(source: &str) -> Result<ParsedFile, Vec<ParseError>> {
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_anthill::LANGUAGE.into())
        .map_err(|e| {
            vec![ParseError::new(
                format!("failed to load grammar: {e}"),
                crate::span::Span::default(),
            )]
        })?;

    let tree = parser.parse(source, None).ok_or_else(|| {
        vec![ParseError::new(
            "tree-sitter parse returned None",
            crate::span::Span::default(),
        )]
    })?;

    // Surface tree-sitter ERROR / MISSING nodes early. tree-sitter recovers
    // from malformed input by inserting these and continuing; the converter
    // walks past anything it doesn't recognise, so a broken construct would
    // otherwise be silently dropped. Fail fast instead (CLAUDE.md: "avoid
    // fallbacks, know about errors early").
    let mut errors = collect_syntax_errors(tree.root_node(), source);
    errors.extend(arrow_effect_list_errors(tree.root_node(), source));

    let mut converter = convert::Converter::new(source);
    converter.convert_file(tree.root_node());
    errors.append(&mut converter.errors);

    if errors.is_empty() {
        Ok(ParsedFile {
            items: converter.items,
            imports: converter.imports,
            symbols: converter.symbols,
            terms: converter.terms,
            // WI-745: keep the source so a load error's byte span can render as
            // `line:col`. The path is unknown here — the caller stamps it via
            // `ParsedFile::with_path`.
            source: std::sync::Arc::from(source),
            path: None,
        })
    } else {
        let hints = legacy_meta_block_hints(tree.root_node(), source, &errors);
        // An `@ [..]` the arrow-effect refusal already named at the same place needs no
        // second message saying the same thing.
        let hints: Vec<_> = hints
            .into_iter()
            .filter(|h| {
                !errors
                    .iter()
                    .any(|e| e.span.start == h.span.start && e.message.contains("single token `@[`"))
            })
            .collect();
        errors.extend(hints);
        errors.sort_by_key(|e| e.span.start);
        Err(errors)
    }
}

/// WI-20260915-G9EA9 — name the new spelling when a failed parse holds an old one.
///
/// A meta block opens with the one token `@[`. The retired spellings no longer parse
/// as blocks, and what they parse as instead varies with the position: a syntax error
/// at the term BEFORE the bracket (`rule r(?x) :- a(?x) [simp]`), a bare-literal rule
/// head in a `rule { … }` block (`q(?a) [simp]` reads `[simp]` as the next entry), a
/// namespace-wide ERROR (`end [M]`), or recovery that folds the bracket into a
/// type-parameter list. None of those messages says what to write, so each old-shaped
/// bracket lying on an error's line or inside its span gets one more error, at the
/// bracket, that does. Only a failed parse is scanned.
///
/// CANDIDATES COME FROM THE TEXT, EXCLUSIONS FROM THE TREE. Error recovery gives a
/// retired bracket no stable place in the CST (a rule body, a loose ERROR leaf, a
/// `sort_type_param_list`, an `application` with an ERROR inside — all measured), so a
/// `[` is found in the source; the tree then rules out what is not a block: a bracket
/// inside a comment, string or description block, and a bracket an error-free
/// `application` owns (`sort Xs = List [Int64]` beside an unrelated error is a type
/// application). The token before the bracket decides the shape: `@` (`@ [..]`),
/// `meta` (the retired operation clause), or a term's end AFTER whitespace (`[Key…]`).
/// A keyword before it (`in [a, b]`, `then [x]`) makes it a list, and the whitespace
/// separates a retired block from a type application written tight on a broken line
/// (`Eq[T]`): all 298 blocks the migration found had it.
fn legacy_meta_block_hints(
    root: tree_sitter::Node,
    source: &str,
    errors: &[ParseError],
) -> Vec<ParseError> {
    let bytes = source.as_bytes();
    let lines = crate::span::LineIndex::new(source);

    // Opaque tokens, in source order (a pre-order walk visits them that way).
    let mut opaque: Vec<(usize, usize)> = Vec::new();
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        match node.kind() {
            "line_comment" | "block_comment" | "string_literal" | "description_block" => {
                opaque.push((node.start_byte(), node.end_byte()));
            }
            _ => {
                let mut cursor = node.walk();
                let children: Vec<_> = node.children(&mut cursor).collect();
                stack.extend(children.into_iter().rev());
            }
        }
    }
    let in_opaque = |at: usize| {
        let i = opaque.partition_point(|&(s, _)| s <= at);
        i > 0 && at < opaque[i - 1].1
    };
    let error_regions: Vec<(usize, usize, usize)> = errors
        .iter()
        .map(|e| {
            let (s, t) = (e.span.start as usize, e.span.end as usize);
            (s, t.max(s + 1), lines.line_col(e.span.start).0)
        })
        .collect();
    let near_error = |at: usize| {
        let line = lines.line_col(at as u32).0;
        error_regions.iter().any(|&(s, t, l)| (s <= at && at < t) || l == line)
    };
    // A legal type application's bracket, which recovery left intact.
    let owned_by_clean_application = |at: usize| {
        root.descendant_for_byte_range(at, at + 1)
            .and_then(|leaf| leaf.parent())
            .is_some_and(|p| p.kind() == "application" && !p.has_error())
    };
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';

    let mut hints = Vec::new();
    for at in 0..bytes.len() {
        if bytes[at] != b'[' || (at > 0 && bytes[at - 1] == b'@') || in_opaque(at) {
            continue;
        }
        let Some(end) = legacy_block_end(bytes, at) else {
            continue;
        };
        if !near_error(at) || owned_by_clean_application(at) {
            continue;
        }
        let mut prev = at;
        while prev > 0 && bytes[prev - 1].is_ascii_whitespace() {
            prev -= 1;
        }
        if prev == 0 {
            continue;
        }
        let spaced = prev < at;
        let before = bytes[prev - 1];
        let mut word_start = prev;
        while word_start > 0 && is_ident(bytes[word_start - 1]) {
            word_start -= 1;
        }
        let word = &source[word_start..prev];
        let block = &source[at..end];
        let (span_start, message) = if before == b'@' && spaced {
            (
                prev - 1,
                format!(
                    "`@ {block}`: a meta block opens with the single token `@[` — remove the \
                     space"
                ),
            )
        } else if word == "meta" {
            (
                word_start,
                format!(
                    "the operation `meta {block}` clause was removed: write the block after \
                     the declaration, as `@{block}`"
                ),
            )
        } else if spaced
            && (matches!(before, b')' | b']' | b'}' | b'?' | b'"') || is_ident(before))
            && !LIST_KEYWORDS.contains(&word)
        {
            (
                at,
                format!("`{block}` is a meta block in the retired spelling: write `@{block}`"),
            )
        } else {
            continue;
        };
        hints.push(ParseError::new(
            message,
            crate::span::Span::new(span_start as u32, end as u32),
        ));
    }
    hints
}

/// Words after which a `[` opens a list literal or a type, never a block.
const LIST_KEYWORDS: &[&str] = &[
    "in", "then", "else", "case", "of", "do", "return", "and", "or", "not", "mod", "div",
    "let", "match", "with", "where", "forall", "exists", "requires", "ensures", "effects",
    "using", "by", "conclude", "import", "provides", "fact", "rule", "sort", "entity",
    "operation", "const", "constraint", "namespace",
];

/// The end (exclusive) of a `[Key, Key: value, …]` bracket starting at `at`, or `None`
/// when the text there does not have a meta block's shape. A key is a dotted name; a
/// value runs to the next top-level `,` or `]` on the same line, with string literals
/// skipped whole so their punctuation does not count.
fn legacy_block_end(bytes: &[u8], at: usize) -> Option<usize> {
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut i = at + 1;
    loop {
        while i < bytes.len() && bytes[i] == b' ' {
            i += 1;
        }
        // key: Name(.Name)*
        loop {
            if i >= bytes.len() || !(bytes[i].is_ascii_alphabetic() || bytes[i] == b'_') {
                return None;
            }
            while i < bytes.len() && is_ident(bytes[i]) {
                i += 1;
            }
            if bytes.get(i) == Some(&b'.') {
                i += 1;
            } else {
                break;
            }
        }
        while i < bytes.len() && bytes[i] == b' ' {
            i += 1;
        }
        if bytes.get(i) == Some(&b':') {
            let mut depth = 0usize;
            i += 1;
            while i < bytes.len() {
                match bytes[i] {
                    b'\n' => return None,
                    b'"' => {
                        i += 1;
                        while i < bytes.len() && bytes[i] != b'"' {
                            if bytes[i] == b'\\' {
                                i += 1;
                            }
                            if bytes.get(i) == Some(&b'\n') {
                                return None;
                            }
                            i += 1;
                        }
                    }
                    b'(' | b'[' | b'{' => depth += 1,
                    b')' | b'}' => depth = depth.checked_sub(1)?,
                    b']' if depth > 0 => depth -= 1,
                    b',' | b']' if depth == 0 => break,
                    _ => {}
                }
                i += 1;
            }
        }
        match bytes.get(i) {
            Some(b',') => i += 1,
            Some(b']') => return Some(i + 1),
            _ => return None,
        }
    }
}

/// WI-20260915-G9EA9 — `@ [..]` after an arrow TERM parses clean, and must not.
///
/// In a term, `@` is the arrow-effect infix, so `?a -> ?b @ [simp]` reads as an arrow
/// whose effect is the list `[simp]`: no syntax error, the tag silently gone. No effect
/// is a list (`_effect_set` is a name or `{…}`), so an `@` operand that is a collection
/// literal is refused here, on every parse, naming the one-token block.
fn arrow_effect_list_errors(root: tree_sitter::Node, source: &str) -> Vec<ParseError> {
    let mut errors = Vec::new();
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        let mut cursor = node.walk();
        let children: Vec<_> = node.children(&mut cursor).collect();
        if node.kind() == "infix_term" {
            for pair in children.windows(2) {
                if pair[0].kind() == "@" && pair[1].kind() == "collection_literal" {
                    let text = &source[pair[1].start_byte()..pair[1].end_byte()];
                    errors.push(ParseError::new(
                        format!(
                            "`@ {text}`: an effect after `@` is a name or `{{…}}`, never a \
                             list — a meta block opens with the single token `@[`"
                        ),
                        crate::span::Span::new(pair[0].start_byte() as u32, pair[1].end_byte() as u32),
                    ));
                }
            }
        }
        stack.extend(children);
    }
    errors
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
        // Ord AFTER `is_error` so a zero-width ERROR — garbage PRESENT, not a
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
