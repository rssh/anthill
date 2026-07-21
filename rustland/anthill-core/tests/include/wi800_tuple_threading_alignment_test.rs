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

/// A PERMUTED literal is refused (WI-788), and the diagnostic reports the type the
/// literal actually has: `head` is the free `?_` nothing determined. It used to be
/// reported as `xs.T` — the expected component type, threaded in by name at a slot
/// the relation was about to refuse, so the "got" side named a type the literal was
/// never given.
#[test]
fn permuted_literal_is_not_threaded() {
    let src = split_case("test.wi800.permuted", DECLARED, "(rest: t, head: h)");
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("mismatch")),
        "a permuted tuple literal must still be refused; got: {errs:?}",
    );
    // Only the GOT side — `head: xs.T` is what the message SHOULD say on the
    // expected side, and asserting over the whole string would pin nothing.
    let got: Vec<&str> = errs.iter().filter_map(|e| e.split_once(", got ")).map(|(_, g)| g).collect();
    assert!(!got.is_empty(), "expected a mismatch message with a got-side; got: {errs:?}");
    assert!(
        !got.iter().any(|g| g.contains("head: xs.T")),
        "the refused literal must not be reported as having the EXPECTED component \
         type threaded into it; got: {errs:?}",
    );
    // The positive half, so the assertion above cannot pass on a message that
    // simply stopped naming components: the literal is reported in SOURCE order,
    // `rest` before `head`. Deliberately NOT asserting how the unbound `head`
    // renders (`?_` today) — that is the type printer's business, and pinning it
    // here would fail this test for a change that has nothing to do with
    // threading.
    assert!(
        got.iter().any(|g| {
            g.find("rest").is_some_and(|r| g.find("head").is_some_and(|h| r < h))
        }),
        "the got-side must be the literal's own type, in SOURCE order (rest before \
         head); got: {errs:?}",
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
/// This program is accepted, and the value it computes is NOT the one its type
/// says — `t.a` reads the FIRST `a` (`field_access` is by name) while the relation
/// typed the second. That is a live defect of the WI-788 family, filed as WI-805,
/// and is NOT what this ticket fixes: it is in the relation and the by-name
/// reader, not in the threading, which is why this test pins the alignment's
/// CHOICE (via the load verdict) and records the wrong answer rather than
/// asserting it is right.
///
/// MEASURED: this test passes with the old by-name threading too — it does not
/// discriminate this ticket's change (the `permuted_*` and `width_*` tests do).
/// It is here because the disagreement it drives is what makes sharing the walk
/// more than tidiness, and because the defect it records needs a live witness.
#[test]
fn duplicate_label_alignment_resumes_after_the_previous_match() {
    let src = r#"
namespace test.wi800.dup
  import anthill.prelude.{Int64, String}
  operation take(t: (b: Int64, a: String)) -> String = t.a
  operation drive() -> String = take((a: 1, b: 2, a: "ess"))
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "the alignment takes the SECOND `a` (String), so this conforms; a first-match \
         walk would take the first (Int64) and refuse it: {:?}",
        load_errs(src),
    );
    let mut interp = interp_for(src);
    match interp.call("test.wi800.dup.drive", &[]) {
        Ok(anthill_core::eval::Value::Int(1)) => {}
        other => panic!(
            "RECORDED, not endorsed: `t.a` reads the first `a` while the relation typed \
             the second, so an operation declared `-> String` yields Int(1). Filed as \
             WI-805; when that lands this program is REFUSED at load and this test should \
             assert the refusal. Got: {other:?}",
        ),
    }
}
