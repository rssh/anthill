//! WI-778 — an absent token that tree-sitter recovered as a ZERO-WIDTH node is a
//! LOUD, LOCATED parse error, not a silent accept.
//!
//! MEASURED before the fix — each of these parsed CLEAN, zero diagnostics, and the
//! converter's `intern(text(n))` interned the EMPTY STRING as a real field name (the
//! label is genuine, not dropped: under the tuple instance of the same bug it reached
//! a type mismatch rendered as `got (: Int64)`):
//!
//! ```anthill
//! entity e(: Int64)                  -- no field name
//! entity e(a: )                      -- no field type
//! operation f(: Int64) -> Int64      -- no parameter name
//! ```
//!
//! THE TICKET'S DIAGNOSIS WAS WRONG, and the correction is what made this a
//! four-line fix instead of a walker-by-walker sweep. It read: `has_error()` is
//! false, so `collect_syntax_errors`' `!has_error() && !is_missing()` prune never
//! descends. Measured, `has_error()` is TRUE — on the zero-width node itself and on
//! every ancestor up to the root — so the walk descends all the way in. The error was
//! dropped at the BOTTOM: the node exposes neither ERROR nor MISSING on the VISIBLE
//! tree, so it fell into the "interior node that merely contains an error — descend"
//! arm, iterated its zero (or equally zero-width) children, and vanished. The prune is
//! innocent and keeps its full pruning power; the fix is one arm, and costs no extra
//! walking.
//!
//! The flag is HIDDEN, not absent — recovery marks the invisible `_identifier_token`
//! that `identifier` wraps, and `Node::children()` skips invisible nodes. That is why
//! the guard keys on zero WIDTH, which the flag only proxies for; see the long comment
//! at the arm in `parse/mod.rs` for the full mechanism and its one caveat.
//!
//! Owned at the WALK rather than at the ~31 `intern(self.text(n))` sites in
//! `parse/convert.rs`, so every walker inherits it — including ones this ticket never
//! enumerated. That is not a hypothetical. The ticket listed THREE producers (entity
//! constructor, operation params, arrow params), but only TWO are in this class:
//! measured, an arrow param's hole (`(: Int64) -> Int64`, `(a: ) -> Int64`) builds a
//! real ERROR node and was ALREADY loud via WI-766 — no zero-width node at all. Those
//! two in-class producers account for FOUR of the TEN silent spellings; the other SIX
//! reach through `sort_type_param`, `operation_type_param`, `sort_binding`, an entity
//! `name`, a variadic capture's name and a `const`'s type. Enumerating the ticket's
//! walkers would have fixed four of ten.
//!
//! Same PATHOLOGY as WI-440 and WI-766 — a hole error-recovered into a zero-width node
//! — but note the two closed it in OPPOSITE directions, and do not restate this as
//! "both stayed loud": WI-766 made `(Int64,)` / `(a: Int64,)` an ERROR (asserted below),
//! whereas WI-440 made `@ {}` LEGAL, accepting the empty effect row so nothing recovers
//! into a phantom `simple_type` (asserted CLEAN below). Both are grammar-level and each
//! closes ONE production; this closes the class underneath them.

use crate::common::parses_clean;
use anthill_core::parse;

/// Messages paired with their start offset — the acceptance criterion is a LOCATED
/// error, and a message assertion alone would pass on a span pointing anywhere.
fn errs_at(src: &str) -> Vec<(String, u32)> {
    match parse::parse(src) {
        Ok(_) => panic!("expected a parse error, but the source parsed clean:\n{src}"),
        Err(errs) => errs.iter().map(|e| (e.message.clone(), e.span.start)).collect(),
    }
}

/// Assert the sole diagnostic is `msg`, positioned exactly at the hole — which opens
/// immediately after `before`. `is_err` alone would pass on any syntax error, and this
/// whole ticket is about a class that produced NO error at all; an unpinned span would
/// likewise pass on a diagnostic pointing at the wrong construct entirely.
fn assert_missing(src: &str, msg: &str, before: &str) {
    let errs = errs_at(src);
    let at = src.find(before).unwrap_or_else(|| panic!("`{before}` not in source"));
    let want = (at + before.len()) as u32;
    assert_eq!(
        errs,
        vec![(msg.to_string(), want)],
        "expected exactly `{msg}` at byte {want} (just past `{before}`) for:\n{src}"
    );
}

// ── The three the ticket measured ──────────────────────────────────────────

#[test]
fn entity_field_without_a_name_is_loud() {
    // The hole sits at the `:`, where the absent identifier would have been.
    assert_missing(
        "namespace t\n  sort S\n    entity e(: Int64)\n  end\nend\n",
        "missing `identifier`",
        "entity e(",
    );
}

#[test]
fn entity_field_without_a_type_is_loud() {
    // Reported at the OUTERMOST zero-width node, so the message names the part the
    // author omitted (a TYPE) rather than the `identifier` leaf one level deeper.
    assert_missing(
        "namespace t\n  sort S\n    entity e(a: )\n  end\nend\n",
        "missing `simple_type`",
        "a:",
    );
}

#[test]
fn operation_param_without_a_name_is_loud() {
    assert_missing(
        "namespace t\n  operation f(: Int64) -> Int64\nend\n",
        "missing `identifier`",
        "f(",
    );
}

// ── The same hole through the OTHER walkers, none of which the ticket named ──

#[test]
fn operation_param_without_a_type_is_loud() {
    assert_missing(
        "namespace t\n  operation f(a: ) -> Int64\nend\n",
        "missing `simple_type`",
        "a:",
    );
}

#[test]
fn empty_type_param_and_binding_lists_are_loud() {
    // Three distinct productions, one inherited guard.
    assert_missing(
        "namespace t\n  sort S[]\n    entity e(a: Int64)\n  end\nend\n",
        "missing `sort_type_param`",
        "S[",
    );
    assert_missing(
        "namespace t\n  operation f[](a: Int64) -> Int64\nend\n",
        "missing `operation_type_param`",
        "f[",
    );
    assert_missing(
        "namespace t\n  operation f(a: List[]) -> Int64\nend\n",
        "missing `sort_binding`",
        "List[",
    );
}

#[test]
fn entity_without_a_name_is_loud() {
    assert_missing(
        "namespace t\n  sort S\n    entity (a: Int64)\n  end\nend\n",
        "missing `name`",
        "entity",
    );
}

#[test]
fn variadic_capture_without_a_name_is_loud() {
    // WI-727's `...args: R` with the name omitted. The `...` is a FUSED token, so the
    // hole opens between it and the `:`.
    assert_missing(
        "namespace t\n  operation f(...: R) -> Int64\nend\n",
        "missing `identifier`",
        "...",
    );
}

#[test]
fn const_without_a_type_is_loud() {
    assert_missing(
        "namespace t\n  const c: = 1\nend\n",
        "missing `simple_type`",
        "c:",
    );
}

// ── Controls ───────────────────────────────────────────────────────────────

#[test]
fn well_formed_declarations_still_parse() {
    // The guard fires on a zero-width node reached by the ERROR walk. A clean file
    // never enters that walk at all, but assert it rather than assume it: an
    // over-firing guard here would refuse every valid program in the language.
    parses_clean("namespace t\n  sort S\n    entity e(a: Int64, b: String)\n  end\nend\n");
    parses_clean("namespace t\n  operation f(a: Int64, b: String) -> Int64\nend\n");
    parses_clean("namespace t\n  sort S[T]\n    entity e(a: T)\n  end\nend\n");
    parses_clean("namespace t\n  operation f[T](a: List[T = Int64]) -> Int64\nend\n");
    parses_clean("namespace t\n  const c: Int64 = 1\nend\n");
    // Well-formed twin of `variadic_capture_without_a_name_is_loud`: that test pins the
    // malformed `...:` as loud, which stays green even if `...rest: R` stopped parsing.
    parses_clean("namespace t\n  operation f(...rest: R) -> Int64\nend\n");
}

#[test]
fn the_grammar_level_fixes_of_this_class_stay_loud() {
    // WI-766 closed its own production in the grammar. This guard sits UNDER it and must
    // not be read as having replaced it — if a grammar change ever reopened it, these
    // would go silent again rather than fall through to here.
    //
    // Each negative is paired with its WELL-FORMED twin, because `is_err` alone is a
    // weak assertion: it passes on ANY syntax error, including one from an unrelated
    // part of the source. Without the twin, a grammar change that broke tuple types
    // WHOLESALE would keep this test green while deleting the feature.
    for (bad, good) in [
        (
            "namespace t\n  operation f(x: (Int64,)) -> Int64\nend\n",
            "namespace t\n  operation f(x: (Int64, String)) -> Int64\nend\n",
        ),
        (
            "namespace t\n  operation f(x: (a: Int64,)) -> Int64\nend\n",
            "namespace t\n  operation f(x: (a: Int64, b: String)) -> Int64\nend\n",
        ),
    ] {
        assert!(parse::parse(bad).is_err(), "expected a parse error for:\n{bad}");
        parses_clean(good);
    }
}

#[test]
fn wi440_empty_effect_row_is_legal_not_loud() {
    // WI-440 is the same pathology fixed in the OPPOSITE direction, and it is asserted
    // here so nobody "restores symmetry" by asserting it errors.
    //
    // The trap this replaces: an earlier version of this file asserted
    // `operation f(a: Int64) -> Int64 @ {}` is_err, reading that as WI-440 staying loud.
    // It IS an error — but VACUOUSLY, for an unrelated reason. `@ ...` is ungrammatical
    // after an operation's return type at all, so `@ {Error}` and `@ Error` fail there
    // identically while `effects {}` is clean. The assertion held no WI-440 content and
    // would have passed no matter what happened to WI-440's fix.
    //
    // `@ {}` belongs to an ARROW TYPE, and there WI-440 made it PARSE — that was the
    // fix: accept the explicit closed-empty row, so nothing error-recovers into a
    // zero-width `simple_type` with the annotation silently dropped
    // (`_effect_set`, `commaSep` not `commaSep1`, tree-sitter-anthill/grammar.js).
    parses_clean("namespace t\n  operation f(g: (x: Int64) -> Int64 @ {}) -> Int64\nend\n");
    parses_clean("namespace t\n  operation f(g: (x: Int64) -> Int64 @ {Error}) -> Int64\nend\n");
}

#[test]
fn a_genuinely_missing_token_is_still_loud() {
    // Pins the behaviour of the `is_missing()` arm this ticket DELETED. That arm is now
    // subsumed by the zero-width predicate on the premise that a MISSING node is itself
    // always zero-width; if that premise ever fails, the diagnostic would be dropped
    // silently rather than fail loudly, so it gets its own test rather than riding on
    // the unflagged-node cases above (which never exercise a real MISSING node).
    // Pinned just past `namespace t` — the hole opens BEFORE the trailing newline.
    assert_missing("namespace t\n", "missing `end`", "namespace t");
}
