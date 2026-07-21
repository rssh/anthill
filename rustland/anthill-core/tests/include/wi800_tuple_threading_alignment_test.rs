//! WI-800 — the tuple-literal expected-type THREADING and the tuple CONFORMANCE
//! relation share one correspondence.
//!
//! WI-462 pushes a tuple literal's expected component types down into its
//! components, so a component whose inferred type is a free var (`h` from
//! `cons(h, t)` over a bare `xs : List`) is pinned by the declared one before
//! conformance — which only subtype-checks and would not bind it. That threading
//! had its OWN correspondence: an order-blind lookup for the first expected
//! component with the same SHORT name. Every relation over two named tuples uses
//! `align_named_tuple_slots` instead — a name-keyed, order-PRESERVING cursor scan
//! (WI-788, WI-804). Two walks, one call apart, that answer differently.
//!
//! They disagree in both directions, and neither is a soundness bug — threading is
//! a hint, and a hint the relation refuses cannot make a program conform:
//!
//!   * THE HINT LANDED WHERE THE RELATION REFUSES. For a permuted literal, the
//!     lookup still found each name and threaded, so the type reported back was
//!     one the literal was never given — see `permuted_*` below.
//!   * THE HINT LANDED ON A DIFFERENT COMPONENT than the relation aligns, whenever
//!     a first-match and a resume-after-the-previous-match disagree about which
//!     component a name picks. `duplicate_label_*` drives that case directly.
//!
//! The fix is that the threading calls the relation's own walk, in the same
//! argument order (`actual`, `expected`) and the same `DATA` mode. What that
//! buys beyond agreement is width: the drop is name-keyed from ANYWHERE (WI-804),
//! so a component needing the hint can sit AFTER a dropped one — `width_*` below
//! pins that, and a raw index-for-index zip fails it.

use crate::common::{interp_for, try_load_kb_with};

fn load_errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// `split` over a bare `xs : List`, so `h` is a free `?_` that only the threading
/// can pin — WI-462's fixture, with the literal's components spelled as `lit`.
fn split_case(ns: &str, ret: &str, lit: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{List, Option, Int64, String}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.List.{{cons, nil}}
  operation split(xs: List) -> Option[T = {ret}] =
    match xs
      case nil() -> none
      case cons(h, t) -> some({lit})
end
"#
    )
}

const DECLARED: &str = "(head: xs.T, rest: List[T = xs.T])";

// ── the hint agrees with the relation about WHETHER to thread ───

/// A PERMUTED literal now CONFORMS (WI-803 made `<:` fully name-keyed), and the
/// threading has to agree with that too — it shares the relation's walk, so a
/// component's hint follows it to whatever slot it actually occupies.
///
/// INVERTED BY WI-803, which is the outcome this test was built to detect either
/// way. Under WI-788 the literal was refused and the point was that the "got" side
/// must not report a type the literal never had (`head: xs.T`, threaded in by name
/// at a slot the relation was about to refuse). The shared walk is what makes both
/// verdicts come out right without a second alignment rule: it threaded nothing
/// when the relation refused, and it threads correctly now that the relation
/// accepts. A threading that had kept its own order-blind by-name lookup would
/// have produced the right answer here for the wrong reason, and the wrong one
/// before.
#[test]
fn permuted_literal_is_threaded_at_its_own_slot() {
    let src = split_case("test.wi800.permuted", DECLARED, "(rest: t, head: h)");
    let errs = load_errs(&src);
    assert!(
        errs.is_empty(),
        "a permuted tuple literal conforms and its components' hints thread to the \
         slots they occupy; got: {errs:?}",
    );
}

/// The CONTROL for the test above: the same fixture IN ORDER conforms, so what the
/// permuted case pins is the permutation and not a broken fixture.
///
/// It is the same program as `wi462_tuple_literal_threading_test`'s
/// `named_tuple_literal_threads`, DELIBERATELY: a control has to differ from the
/// case it controls in exactly one respect, which means sharing this file's builder
/// rather than citing a fixture spelled out elsewhere. If the two ever disagree,
/// WI-462's is the one that states the requirement.
#[test]
fn in_order_literal_still_threads() {
    let src = split_case("test.wi800.inorder", DECLARED, "(head: h, rest: t)");
    assert!(load_errs(&src).is_empty(), "the in-order literal must load: {:?}", load_errs(&src));
}

// ── the hint agrees with the relation about WHICH component ─────

/// WIDTH, with the dropped component sitting BEFORE the one that needs the hint.
/// `(mid: Int64, head: ?_, rest: List)` conforms to `(head: xs.T, rest: …)` by
/// name-keyed width (WI-804), and `head` still gets its expected type — the scan
/// resumes from where the previous match left off rather than requiring slot `i`
/// to answer for component `i`. An index-for-index zip compares `mid` against
/// `head`, gives up, and this program stops loading.
#[test]
fn width_threads_past_a_dropped_component() {
    let src = split_case("test.wi800.widthdrop", DECLARED, "(mid: 1, head: h, rest: t)");
    assert!(
        load_errs(&src).is_empty(),
        "a component after a width-dropped one must still be threaded: {:?}",
        load_errs(&src),
    );
}

/// The same, with the drop BETWEEN the two threaded components.
#[test]
fn width_threads_around_a_dropped_component() {
    let src = split_case("test.wi800.widthmid", DECLARED, "(head: h, mid: 1, rest: t)");
    assert!(
        load_errs(&src).is_empty(),
        "a middle drop must not stop the threading: {:?}",
        load_errs(&src),
    );
}

/// A DUPLICATE label is where a first-match lookup and the cursor scan pick
/// different components: expected `a` resumes AFTER `b`'s match, so it takes the
/// SECOND `a`. The relation is built on that choice, so the hint must be too.
///
/// This program used to be ACCEPTED while computing a value its type denies:
/// `t.a` reads the FIRST `a` (`field_access` is by name) while the relation, whose
/// cursor resumed AFTER the `b` match, typed the SECOND. An operation declared
/// `-> String` returned `Int(1)` on a clean load.
///
/// INVERTED BY WI-803, and by the half of it that was not the headline. Making
/// `TupleAlign::DATA` order-free meant choosing where each name lookup STARTS, and
/// starting from 0 — first match — is `field_access`' own rule. So the relation
/// and the reader now pick the same component, the type mismatch is visible, and
/// the program is refused.
///
/// This does NOT close WI-805, and the test does not claim to. WI-805's fix is to
/// refuse a duplicate label where the tuple is BUILT, which makes the disagreement
/// unreachable rather than merely aligned; a duplicate-label tuple whose two `a`s
/// have the SAME type still loads today. What is fixed here is the divergence:
/// two walks over one tuple no longer answer differently.
#[test]
fn duplicate_label_conforms_on_the_first_occurrence_like_field_access() {
    let src = r#"
namespace test.wi800.dup
  import anthill.prelude.{Int64, String}
  operation take(t: (b: Int64, a: String)) -> String = t.a
  operation drive() -> String = take((a: 1, b: 2, a: "ess"))
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("mismatch")),
        "the alignment takes the FIRST `a` (Int64), which is the one `t.a` reads, so \
         the `-> String` claim is refused instead of silently yielding Int(1); got: {errs:?}",
    );
}
