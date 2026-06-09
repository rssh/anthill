//! WI-376: expression-carried type projections `s.T` / `s.Sort`.
//!
//! A producer's projection signature `peek(l: List) -> l.T` threads the receiver's
//! element through call sites: the projection is ELIMINATED by projecting the
//! ARGUMENT's inferred type (`List[Int64].T = Int64`) — the synthesis-time discharge of
//! WI-379 bidirectional inference, resolved in `check_apply_iter` where the arguments
//! are already synthesized. `s.Sort` projects the whole parameterized sort of the
//! receiver. A member the receiver's concrete sort does NOT declare is a loud error
//! (never a silent fresh var); a bare / abstract receiver stays polymorphic, so one
//! signature serves both the concrete and the abstract receiver.
//!
//! Design: `docs/design/expansion-during-unification.md` §4 case 2,
//! `docs/design/type-parameter-scoping.md` §1, `docs/proposals/042` §"Type
//! projections". The receiver is a single value reference (`Ref(s)`); compound
//! receivers (`a.b.T`) and cross-parameter projections are the documented follow-on.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// `peek(l: List) -> l.T` threads the element: calling it on a `List[Int64]` yields
/// `Int64`, so returning the call where `Int64` is declared CONFORMS.
#[test]
fn projection_threads_element_concrete() {
    let ok = r#"
namespace test.wi376.elem_ok
  import anthill.prelude.{List, Int64}
  operation peek(l: List) -> l.T
  operation caller(xs: List[T = Int64]) -> Int64 = peek(xs)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "peek(xs) is List[Int64].T = Int64; returning it as Int64 must conform",
    );
}

/// The threaded element is REAL: returning `peek(xs)` (which is `Int64`) where `String`
/// is declared must be rejected — the projection did not invent a fresh element.
#[test]
fn projection_wrong_element_is_rejected() {
    let wrong = r#"
namespace test.wi376.elem_wrong
  import anthill.prelude.{List, Int64, String}
  operation peek(l: List) -> l.T
  operation caller(xs: List[T = Int64]) -> String = peek(xs)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "peek(xs) is Int64, not String — the wrong declared return must be rejected",
    );
}

/// `echo(l: List) -> l.Sort` projects the WHOLE parameterized sort of the receiver,
/// so `echo(xs)` on a `List[Int64]` is `List[Int64]` (every parameter captured).
#[test]
fn projection_sort_captures_whole_type() {
    let ok = r#"
namespace test.wi376.sort_ok
  import anthill.prelude.{List, Int64}
  operation echo(l: List) -> l.Sort
  operation caller(xs: List[T = Int64]) -> List[T = Int64] = echo(xs)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "echo(xs) is l.Sort = List[Int64]; returning it as List[Int64] must conform",
    );

    let wrong = r#"
namespace test.wi376.sort_wrong
  import anthill.prelude.{List, Int64, String}
  operation echo(l: List) -> l.Sort
  operation caller(xs: List[T = Int64]) -> List[T = String] = echo(xs)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "echo(xs) is List[Int64], not List[String] — must be rejected",
    );
}

/// A member the receiver's concrete sort does NOT declare is a loud error, never a
/// silent fresh var: `List` declares `T`, not `Nonesuch`, so `l.Nonesuch` is rejected.
#[test]
fn projection_missing_member_is_loud() {
    let src = r#"
namespace test.wi376.missing
  import anthill.prelude.{List, Int64}
  operation bad(l: List) -> l.Nonesuch
  operation caller(xs: List[T = Int64]) -> Int64 = bad(xs)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("Nonesuch") || e.contains("no member")),
        "projecting a member List does not declare must be a loud error; got: {errs:?}",
    );
}

/// The headline acceptance: a producer `to_stream(l: List) -> Stream[T = l.T, E = {}]`
/// and a consumer `gather(s: Stream) -> List[T = s.T]` THREAD the element through
/// composition — `gather(to_stream(xs))` on a `List[Int64]` is `List[Int64]`, with no
/// fresh `?_` element. (The written `E = {}` carries the observation effect; the
/// element rides the projection.)
#[test]
fn projection_threads_through_composition() {
    let ok = r#"
namespace test.wi376.compose_ok
  import anthill.prelude.{List, Stream, Int64}
  operation to_stream(l: List) -> Stream[T = l.T, E = {}]
  operation gather(s: Stream) -> List[T = s.T]
  operation walk(xs: List[T = Int64]) -> List[T = Int64] = gather(to_stream(xs))
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "gather(to_stream(xs)) must thread Int64 through the projection composition",
    );

    let wrong = r#"
namespace test.wi376.compose_wrong
  import anthill.prelude.{List, Stream, Int64, String}
  operation to_stream(l: List) -> Stream[T = l.T, E = {}]
  operation gather(s: Stream) -> List[T = s.T]
  operation walk(xs: List[T = Int64]) -> List[T = String] = gather(to_stream(xs))
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "the composed element is Int64, not String — wrong declared return must be rejected",
    );
}

/// WI-400 (abstract-stays-poly, co-delivered) UPDATED the bare-receiver case: a projection
/// off a bare / abstract receiver no longer ERRORS at formation — `peek(l: List) -> l.T` is
/// well-formed, forming the rigid NEUTRAL `l.T` (`T` IS a declared type-parameter of `List`,
/// just unbound on a bare `List`). The neutral "stays polymorphic" but is NOT a fresh var
/// that absorbs any demand: returning it where a concrete `Int64` is declared is REJECTED by
/// the ζ arm (a neutral never equals a concrete type), so the old soundness guarantee — one
/// `peek(l)` cannot satisfy both `Int64` and `String` — is preserved by the neutral, not by
/// erroring at formation. (Was `projection_bare_receiver_is_rejected`, asserting the
/// pre-WI-400 loud "abstract-receiver not yet supported" error.)
#[test]
fn projection_bare_receiver_stays_poly() {
    // The bare-receiver signature is well-formed on its own (l.T is a valid neutral).
    let ok = r#"
namespace test.wi376.bare_poly
  import anthill.prelude.List
  operation peek(l: List) -> l.T
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "peek(l: List) -> l.T must be well-formed (l.T a rigid neutral, abstract-stays-poly); \
         got: {:?}",
        load_errors(&[ok]),
    );

    // Soundness preserved: the neutral does NOT satisfy a concrete Int64 demand.
    let wrong = r#"
namespace test.wi376.bare_concrete
  import anthill.prelude.{List, Int64}
  operation peek(l: List) -> l.T
  operation relay(l: List) -> Int64 = peek(l)
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("l.T")),
        "the bare-receiver neutral l.T must NOT satisfy a concrete Int64 demand (ζ refuses a \
         neutral vs concrete); got: {errs:?}",
    );
}

/// Regression (WI-261 / proposal 041): `Modify[result.a]` is a per-result-component
/// effect — `result` is an OpResult value head but `a` is LOWERCASE, so it is a value
/// place (a `denoted`), NOT a type projection. Calling such an op must not raise a
/// spurious "receiver 'result' is not an argument-bound parameter" (the bug a naive
/// value-head classifier without the capitalization rule introduces).
#[test]
fn modify_result_field_not_misclassified_as_projection() {
    let src = r#"
namespace test.wi376.result_effect
  import anthill.prelude.{Cell, Int64, Modify}
  operation make_pair() -> (a: Cell[V = Int64], b: Cell[V = Int64])
    effects {Modify[result.a], Modify[result.b]}
  operation run() -> (a: Cell[V = Int64], b: Cell[V = Int64])
    effects {Modify[result.a], Modify[result.b]}
    = make_pair()
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.iter().any(|e| e.contains("argument-bound") || e.contains("projection")),
        "Modify[result.a] is a value place, not a type projection; calling the op must \
         not raise a projection error; got: {errs:?}",
    );
}

// ── WI-396: expression-carried projection in EFFECT-row position (`effects s.E`) ──
//
// The element projection `s.T` carries the receiver's element; `s.E` is its effect
// sibling — it threads the receiver Stream's effect ROW (the observation effect,
// `effects E = ?` on stream.anthill). The same classifier + eliminator the type
// position uses now serves the effect position: `effects s.E` lowers to an
// `ExprCarried`, and at the call it projects the `E` member off the argument's
// inferred type. `List` has NO effect member to project, so `l.E` is a loud
// missing-member error (design §5: the written row is the route there, not a
// projection) — never a silent pure default, which `E` must never become.

/// `drain(s: Stream) -> List[T = s.T] effects s.E` threads BOTH the element and the
/// effect: on a `Stream[T = Int64, E = {Branch}]` it is `List[Int64]` with effect
/// `{Branch}`, so a caller that declares `effects {Branch}` conforms.
#[test]
fn effect_projection_threads_concrete() {
    let ok = r#"
namespace test.wi396.eff_ok
  import anthill.prelude.{List, Stream, Int64, Branch}
  operation drain(s: Stream) -> List[T = s.T] effects s.E
  operation run(es: Stream[T = Int64, E = {Branch}]) -> List[T = Int64] effects {Branch} = drain(es)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "drain(es) projects s.E = {{Branch}}; a caller declaring effects {{Branch}} must conform",
    );
}

/// The threaded effect is REAL: the projected `s.E = {Branch}` is a genuine effect,
/// so a caller that declares PURE (no effects) must be rejected — the projection did
/// not silently default `E` to pure.
#[test]
fn effect_projection_wrong_effect_is_rejected() {
    let wrong = r#"
namespace test.wi396.eff_wrong
  import anthill.prelude.{List, Stream, Int64, Branch}
  operation drain(s: Stream) -> List[T = s.T] effects s.E
  operation run(es: Stream[T = Int64, E = {Branch}]) -> List[T = Int64] = drain(es)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "drain(es) threads effect {{Branch}}; a pure caller must be rejected, not silently accepted",
    );
}

/// `l.E` on a `List` is a loud missing-member error: `List` declares no effect member
/// `E`, so the projection cannot resolve (design §5 — the written row is the route to
/// carry `E`, not a projection). Never a silent fresh / pure default.
#[test]
fn effect_projection_missing_member_is_loud() {
    let src = r#"
namespace test.wi396.eff_missing
  import anthill.prelude.{List, Int64}
  operation bad(l: List) -> Int64 effects l.E
  operation caller(xs: List[T = Int64]) -> Int64 = bad(xs)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("no member 'E'") || e.contains("has no member")),
        "List has no effect member 'E'; projecting l.E must be a loud error; got: {errs:?}",
    );
}

/// The projection also works INSIDE a written effect row: `effects {s.E}` threads the
/// receiver's effect row the same way the bare `effects s.E` does.
#[test]
fn effect_projection_in_written_row() {
    let ok = r#"
namespace test.wi396.eff_row
  import anthill.prelude.{List, Stream, Int64, Branch}
  operation drain(s: Stream) -> List[T = s.T] effects {s.E}
  operation run(es: Stream[T = Int64, E = {Branch}]) -> List[T = Int64] effects {Branch} = drain(es)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "effects {{s.E}} (projection inside a written row) must thread {{Branch}} like bare effects s.E",
    );
}

/// A projection nested in a denoted-bearing type — `Stream[T = l.T, E = {Modify[c]}]`
/// rides a `Value::Node` carrier — is rejected loudly rather than leaking the
/// un-eliminated `l.T` into the inferred type (the Node-carrier rewrite is a follow-on).
#[test]
fn projection_in_denoted_node_is_rejected() {
    let src = r#"
namespace test.wi376.node
  import anthill.prelude.{List, Stream, Int64, Cell, Modify}
  operation src(l: List, c: Cell[V = Int64]) -> Stream[T = l.T, E = {Modify[c]}]
  operation use_src(xs: List[T = Int64], c: Cell[V = Int64]) -> Int64 = src(xs, c)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("denoted-bearing") || e.contains("not yet supported")),
        "a projection inside a denoted-bearing type must be a loud error, not a leak; got: {errs:?}",
    );
}
