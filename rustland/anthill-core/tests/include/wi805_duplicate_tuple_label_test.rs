//! WI-805 — a named tuple's component labels must be DISTINCT, enforced where the
//! tuple is MINTED.
//!
//! MEASURED before the guard, on a clean load:
//!
//! ```anthill
//! operation take(t: (b: Int64, a: Int64)) -> Int64 = t.a
//! operation drive() -> Int64 = take((a: 1, b: 2, a: 3))
//! ```
//!
//! loaded with zero errors and `drive()` returned `Int(1)`. The `a: 3` column was
//! reachable by neither its name (`t.a` takes the first `a`) nor its position (the
//! relation is name-keyed) — a component nothing can read, whose declared type was
//! never checked against anything. `-> (a: Int64, a: Int64) = (a: 1, a: 2)` was
//! accepted the same way, from the TYPE side.
//!
//! WI-803 had already made the two readers agree (both resolve a name to its FIRST
//! match), which turned the differently-typed spelling into a visible mismatch. That
//! is necessary but not sufficient, and the distinction is the point of this file:
//! AGREEING on which component to read does not make the unread one readable. The
//! spec refuses exactly this shape for a projection's result keys (`x.(a, a)`) and
//! for a call's named arguments; the construct that can actually MINT such a tuple
//! was the one place the rule was missing.
//!
//! The guard is therefore at the mint — `check_tuple_label_unique`
//! (parse/convert.rs), one owner shared by the literal and the tuple type — so the
//! refusal is a PARSE-stage located error and the tuple is never built. Tests read
//! `parse` directly for that reason, as WI-639's sibling projection tests do.

use crate::common::{interp_for, parse_errs, parses_clean, try_load_kb_with};

fn load_errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

// ── the literal ────────────────────────────────────────────────

/// The headline, in its SAME-TYPED spelling — the one WI-803's reader/relation
/// agreement leaves silent, because with both `a`s `Int64` there is no mismatch to
/// surface. Nothing before this guard refused it, and `drive()` returned `Int(1)`
/// from a tuple whose third component no reader could reach.
#[test]
fn same_typed_duplicate_literal_label_is_refused() {
    let src = r#"
namespace test.wi805.lit
  import anthill.prelude.Int64
  operation take(t: (b: Int64, a: Int64)) -> Int64 = t.a
  operation drive() -> Int64 = take((a: 1, b: 2, a: 3))
end
"#;
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate tuple literal component label `a`")),
        "the duplicate literal label must be refused, naming `a`; got: {errs:?}",
    );
}

/// The diagnostic is LOCATED AT THE OFFENDING COMPONENT, not at the whole tuple —
/// the check runs over `(label, key node)` pairs in `push_tuple_literal` for that
/// reason. Pinned by span, since a check reported at the tuple node would point at
/// the opening paren and still satisfy every `contains` assertion above.
#[test]
fn the_duplicate_is_located_at_the_second_occurrence() {
    let src = "namespace test.wi805.loc\n  import anthill.prelude.Int64\n  \
               operation bad() -> Int64 = (a: 1, b: 2, a: 3)._1\nend\n";
    let errs = match anthill_core::parse::parse(src) {
        Ok(_) => panic!("a duplicate-label tuple literal must not parse"),
        Err(errs) => errs,
    };
    let dup = errs
        .iter()
        .find(|e| e.message.contains("duplicate tuple literal component label"))
        .unwrap_or_else(|| panic!("no duplicate-label error; got: {errs:?}"));
    // The SECOND `a`, not the first and not the tuple's `(`.
    let second_a = src.rfind("a: 3").expect("fixture spells the second `a`") as u32;
    assert_eq!(
        (dup.span.start, dup.span.end),
        (second_a, second_a + 1),
        "the error must point at the second `a` (offset {second_a}); got {:?} — `{}`",
        dup.span,
        &src[dup.span.start as usize..dup.span.end as usize],
    );
}

// ── the type ───────────────────────────────────────────────────

/// The TYPE side is a separate mint and needs its own guard: a duplicate here made
/// the second component undeclarable-against rather than unreadable. Before the
/// guard this loaded with a MISLEADING error — `expected String, got Int64` on the
/// return — because `t.a` read the first `a` while the author had written the
/// second one's type as the operation's result.
#[test]
fn duplicate_tuple_type_component_label_is_refused() {
    let src = r#"
namespace test.wi805.ty
  import anthill.prelude.{Int64, String}
  operation take(t: (a: Int64, a: String)) -> String = t.a
end
"#;
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate tuple type component label `a`")),
        "the duplicate type label must be refused, naming `a`; got: {errs:?}",
    );
}

/// A RETURN tuple type — the spelling that loaded with ZERO errors, both halves
/// duplicated. Drives the type and the literal guards together.
#[test]
fn duplicate_return_tuple_type_and_literal_are_both_refused() {
    let src = r#"
namespace test.wi805.ret
  import anthill.prelude.Int64
  operation mk() -> (a: Int64, a: Int64) = (a: 1, a: 2)
end
"#;
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("duplicate tuple type component label `a`")),
        "the return TYPE's duplicate must be refused; got: {errs:?}",
    );
    assert!(
        errs.iter().any(|e| e.contains("duplicate tuple literal component label `a`")),
        "the literal's duplicate must be refused too — two mints, two guards; \
         got: {errs:?}",
    );
}

// ── the third producer: variadic capture ───────────────────────

/// A `...rest: R` capture folds a call's LEFTOVER NAMED ARGUMENTS into a named tuple
/// (WI-727), so it keys a tuple on labels the author wrote — and the parse guard
/// cannot see them, because they are written as call arguments and only become a
/// tuple in the typer.
///
/// Found by the WI-805 `/code-review` altitude pass, which refused to accept
/// "literal + type = every producer" and enumerated the callers of
/// `named_tuple_value` instead. Measured live before the guard: this program loaded
/// CLEAN and `drive()` returned `Int(2)`, having built `(a: Int64, a: String)` — the
/// very type the parse guard forbids writing — with the `a: String` column
/// unreachable and its type never checked.
///
/// `named_arg_coverage_errors`' "binds a parameter already given" does NOT cover
/// this: a captured leftover matches no declared parameter, which is what routed it
/// into the capture in the first place.
#[test]
fn duplicate_captured_named_argument_is_refused() {
    let src = r#"
namespace test.wi805.cap
  import anthill.prelude.{Int64, String}
  operation cap[R](x: Int64, ...rest: R) -> R = rest
  operation drive() -> Int64 = cap(1, a: 2, a: "ess").a
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("captured twice into the `...` record")
            && e.contains('a')),
        "a label captured twice must be refused at load, naming it; got: {errs:?}",
    );
}

/// The same duplicate reaching the RUNTIME reader, which is what makes it the WI-805
/// defect rather than a tidiness rule. Before the guard this loaded clean and raised
/// `MatchFailed` at eval — `match_tuple_pattern` received two IDENTICAL labels over a
/// two-component tuple and its WI-445 double-cover check refused to bind one
/// component to both binders.
///
/// That refusal was the double-cover guard's only end-to-end witness in the corpus.
/// Closing this producer removes it again, which is recorded at the guard itself
/// (eval/pattern.rs) rather than left implicit: the guard still answers for labels
/// that collide as distinct QUALIFIED names sharing a last segment, a mode no
/// source-level distinctness rule can see.
#[test]
fn duplicate_captured_label_no_longer_reaches_the_matcher() {
    let src = r#"
namespace test.wi805.cap2
  import anthill.prelude.Int64
  operation cap[R](x: Int64, ...rest: R) -> R = rest
  operation drive() -> Int64 =
    let (p, q) = cap(1, a: 2, a: 3)
    q
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("captured twice into the `...` record")),
        "the duplicate is refused at the capture, before it can reach the matcher; \
         got: {errs:?}",
    );
}

/// CONTROL: a capture with DISTINCT labels still works, end to end. Without this the
/// test above passes just as well against a guard that refuses every capture.
#[test]
fn distinct_captured_labels_still_capture_and_read() {
    let src = r#"
namespace test.wi805.cap3
  import anthill.prelude.Int64
  operation cap[R](x: Int64, ...rest: R) -> R = rest
  operation drive() -> Int64 = cap(1, a: 2, b: 3).b
end
"#;
    assert!(load_errs(src).is_empty(), "a distinct-label capture must load: {:?}", load_errs(src));
    let mut interp = interp_for(src);
    match interp.call("test.wi805.cap3.drive", &[]).expect("drive") {
        anthill_core::eval::Value::Int(3) => {}
        other => panic!("`.b` must read the captured `b` column (3); got {other:?}"),
    }
}

// ── what the rule must NOT catch ───────────────────────────────

/// POSITIONAL components must stay legal at any arity. Their `_N` labels are minted
/// from each component's own index (`intern_positional_label`), so they cannot
/// collide — but the check runs over WRITTEN labels only, and this is the control
/// that says so. A check placed after the positional desugar would still pass here;
/// what would break is the mixed case below.
#[test]
fn positional_tuples_are_untouched() {
    parses_clean(
        "namespace test.wi805.pos\n  import anthill.prelude.{Int64, String}\n  \
         operation mk() -> (Int64, String, Int64) = (1, \"two\", 3)\nend\n",
    );
}

/// A `_`-prefixed USER label is an ordinary name (WI-790) and compares as one: two
/// of them collide, one does not. `_1` at the FIRST position is the canonical
/// synthetic name for that slot, so this fixture writes `_1` second, where it is a
/// user label — and pairs it with a distinct `_b` to show the rule keys on the name
/// rather than on `_`-prefixedness (which is the projection rule, deliberately
/// broader — see `validate_projection_labels`).
#[test]
fn distinct_underscore_user_labels_are_legal_and_duplicates_still_are_not() {
    parses_clean(
        "namespace test.wi805.usr\n  import anthill.prelude.Int64\n  \
         operation mk() -> (_b: Int64, _1: Int64) = (_b: 1, _1: 2)\nend\n",
    );
    let errs = parse_errs(
        "namespace test.wi805.usr2\n  import anthill.prelude.Int64\n  \
         operation mk() -> Int64 = (_b: 1, _b: 2)._b\nend\n",
    );
    assert!(
        errs.iter().any(|e| e.contains("duplicate tuple literal component label `_b`")),
        "a repeated USER `_`-label is a duplicate like any other; got: {errs:?}",
    );
}

/// DIFFERENT tuples in one expression are independent — the check is per-tuple, not
/// per-file. A nested tuple reusing an outer label is fine, and the label set does
/// not leak across siblings.
#[test]
fn labels_do_not_collide_across_distinct_tuples() {
    parses_clean(
        "namespace test.wi805.nest\n  import anthill.prelude.Int64\n  \
         operation mk() -> (a: Int64, b: (a: Int64, c: Int64)) \
         = (a: 1, b: (a: 2, c: 3))\nend\n",
    );
}

/// An ARROW PARAMETER LIST is not a tuple TYPE and is deliberately NOT covered.
/// The two share one grammar production (WI-766) but not one reading, and
/// `convert_arrow_type` walks its params itself rather than calling
/// `convert_tuple_type` — the same seam that lets `(A) -> B` be a parameter list
/// while `(A)` is not a type.
///
/// The exemption is not an oversight: a parameter list is applied POSITIONALLY, so
/// a repeated binder name leaves NO parameter unreachable, and the one channel that
/// does read those names — a named argument — already refuses a duplicate at the
/// call (`named_arg_coverage_errors`, "binds a parameter already given"). Nothing
/// here is silently wrong, which is what this file is about. Recorded rather than
/// widened, so that a later decision to reject duplicate binder names is taken on
/// its own terms.
#[test]
fn an_arrow_parameter_list_is_not_covered() {
    parses_clean(
        "namespace test.wi805.arrow\n  import anthill.prelude.Int64\n  \
         operation useit(f: (a: Int64, a: Int64) -> Int64) -> Int64 = f(1, 2)\nend\n",
    );
}
