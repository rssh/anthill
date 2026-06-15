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

// ── WI-460: a projection NESTED in a denoted-bearing `Value::Node` carrier ──
//
// The headline shape is `find`'s callback param `(x: s.T) -> Bool @ {EffP, -Modify[x]}`:
// the `-Modify[x]` binder makes the arrow a `Value::Node`, and `s.T` rides inside it.
// WI-460 rewrites the projection THROUGH the Node carrier (descend the occurrence tree,
// eliminate each `ExprCarried` child against the receiver's argument type, rebuild the
// carrier with the denoted children preserved) instead of bailing with the old
// "not yet supported" error. The threading stays REAL — a wrong declared element is
// still rejected — and the descent reaches a `parameterized` carrier (`Stream[T = l.T,
// E = {Modify[c]}]`) too.

/// The `find`-pred shape: `s.T` nested in a denoted-bearing arrow `(x: s.T) -> Bool @
/// {EffP, -Modify[x]}`, with a projection-only return `Option[T = s.T]`. The projection
/// threads through the Node carrier, so calling it on a `Stream[T = Int64]` and declaring
/// the result `Option[T = Int64]` conforms — no more formation bail.
#[test]
fn projection_in_denoted_arrow_threads() {
    let ok = r#"
namespace test.wi460.arrow_ok
  import anthill.prelude.{Stream, Int64, Bool, Option, Cell, Modify}
  operation find2[EffP](s: Stream, pred: (x: s.T) -> Bool @ {EffP, -Modify[x]})
    -> Option[T = s.T] effects {s.E, EffP}
  operation use_find(es: Stream[T = Int64, E = {}], p: (x: Int64) -> Bool @ {})
    -> Option[T = Int64] = find2(es, p)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "s.T nested in the denoted pred arrow (-Modify[x]) must thread through the Node \
         carrier so find2(es, p) is Option[Int64]; got: {:?}",
        load_errors(&[ok]),
    );
}

/// The threaded element is REAL: `find2(es, p)` on a `Stream[T = Int64]` is
/// `Option[T = Int64]`, so declaring the result `Option[T = String]` is rejected — the
/// projection inside the denoted arrow did not invent a fresh element.
#[test]
fn projection_in_denoted_arrow_wrong_element_rejected() {
    let wrong = r#"
namespace test.wi460.arrow_wrong
  import anthill.prelude.{Stream, Int64, String, Bool, Option, Cell, Modify}
  operation find2[EffP](s: Stream, pred: (x: s.T) -> Bool @ {EffP, -Modify[x]})
    -> Option[T = s.T] effects {s.E, EffP}
  operation use_find(es: Stream[T = Int64, E = {}], p: (x: Int64) -> Bool @ {})
    -> Option[T = String] = find2(es, p)
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("Int64") && e.contains("String")),
        "the threaded element is Int64, not String — the wrong declared return must be \
         rejected; got: {errs:?}",
    );
}

/// The descent also reaches a `parameterized` carrier: `Stream[T = l.T, E = {Modify[c]}]`
/// rides a `Value::Node` (the `Modify[c]` denoted binding). WI-460 eliminates `l.T` →
/// `Int64` THROUGH that carrier — so the old formation bail ("not yet supported") is gone
/// and no un-eliminated `l.T` leaks. (The residual `Modify[c]` effect-row equality across
/// the call is an orthogonal, pre-existing denoted-row limitation — independent of the
/// projection, it fails even with no projection at all — so this asserts only that the
/// projection no longer bails and threads to the concrete element.)
#[test]
fn projection_in_denoted_parameterized_no_longer_bails() {
    let src = r#"
namespace test.wi460.param
  import anthill.prelude.{List, Stream, Int64, Cell, Modify}
  operation src(l: List, c: Cell[V = Int64]) -> Stream[T = l.T, E = {Modify[c]}]
  operation use_src(xs: List[T = Int64], c: Cell[V = Int64]) -> Int64 = src(xs, c)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.iter().any(|e| e.contains("not yet supported") || e.contains("denoted-bearing")),
        "the projection l.T must no longer bail at formation inside the denoted carrier; \
         got: {errs:?}",
    );
    // The projection was eliminated (the GOT type threads the concrete `T = Int64`); a
    // leaked `l.T` would print in the residual mismatch.
    assert!(
        !errs.iter().any(|e| e.contains("l.T")),
        "no un-eliminated `l.T` must leak into the inferred type; got: {errs:?}",
    );
}

/// EVAL: a non-recursive op carrying the denoted-arrow projection param runs end-to-end —
/// the callback `(x: xs.T) -> Bool @ {EffP, -Modify[x]}` is applied to the list head, so
/// WI-460's rewrite is exercised at run time, not only at type-check.
#[test]
fn projection_in_denoted_arrow_evals() {
    let src = r#"
namespace test.wi460.eval
  import anthill.prelude.{List, Int64, Bool, Cell, Modify}
  import anthill.prelude.List.{cons, nil}
  operation check_first[EffP](xs: List, pred: (x: xs.T) -> Bool @ {EffP, -Modify[x]})
    -> Bool effects EffP =
    match xs
      case nil() -> false
      case cons(h, t) -> pred(h)
  operation is_big(n: Int64) -> Bool = n > 2
  operation big_first() -> Int64 = if check_first([3, 1, 2], is_big) then 1 else 0
  operation small_first() -> Int64 = if check_first([1, 3, 2], is_big) then 1 else 0
end
"#;
    assert!(load_errors(&[src]).is_empty(), "eval fixture must typecheck; got: {:?}", load_errors(&[src]));
    let mut interp = crate::common::interp_for(src);
    let run = |interp: &mut anthill_core::eval::Interpreter, op: &str| -> i64 {
        match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
            anthill_core::eval::Value::Int(i) => i,
            other => panic!("call {op}: expected Int, got {other:?}"),
        }
    };
    assert_eq!(run(&mut interp, "test.wi460.eval.big_first"), 1, "head 3 is_big → true");
    assert_eq!(run(&mut interp, "test.wi460.eval.small_first"), 0, "head 1 not is_big → false");
}

// ── WI-376 (final): cross-sort provider DIVERGENT member name (the retained acceptance) ──
//
// A carrier may PROVIDE a spec that declares a member under a DIFFERENT carrier-side name:
// `List provides Iterable[List[T], T]` maps Iterable's `Element` to `List`'s `T`. A
// projection written in the SPEC's vocabulary (`c.Element`) must therefore ground on a
// concrete carrier (`List[T = Int64].Element = Int64`) by following the `provides` binding,
// not by looking for a literal `Element` member on `List`. Combined with WI-400's
// abstract-stays-poly (an abstract carrier `c : C requires Iterable` keeps `c.Element` a
// neutral), this is the concrete/abstract receiver split via the spec interface. (The
// concrete-carrier OWN-name case `l.T` and the abstract requires-side case are the earlier
// WI-376 / WI-400 tests; this file's `projection_threads_*` cover the former.)

/// A projection of a spec member off a CONCRETE carrier grounds through the carrier's
/// `provides` binding: `elemOf(l: List) -> l.Element` on a `List[T = Int64]` is `Int64`
/// (Iterable's `Element` ↦ `List`'s `T = Int64`), so returning it as `Int64` conforms.
#[test]
fn divergent_provider_member_grounds_concrete() {
    let ok = r#"
namespace test.wi376.divergent_ok
  import anthill.prelude.{List, Int64}
  operation elemOf(l: List) -> l.Element
  operation caller(xs: List[T = Int64]) -> Int64 = elemOf(xs)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "l.Element grounds via `List provides Iterable[List[T], T]` to List's T = Int64; \
         returning it as Int64 must conform; got: {:?}",
        load_errors(&[ok]),
    );
}

/// The divergent grounding is REAL: `l.Element` is `Int64` (the carrier's element), so
/// returning it where `String` is declared is rejected — not a fresh var absorbing demand.
#[test]
fn divergent_provider_member_wrong_return_rejected() {
    let wrong = r#"
namespace test.wi376.divergent_wrong
  import anthill.prelude.{List, Int64, String}
  operation elemOf(l: List) -> l.Element
  operation caller(xs: List[T = Int64]) -> String = elemOf(xs)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "l.Element is Int64 (List's element via Iterable), not String — must be rejected",
    );
}

/// The concrete/abstract split via the spec interface: an ABSTRACT carrier `c : C` whose
/// declared interface is `requires Iterable[C = C, Element = Element, E = E]` keeps
/// `w.coll.Element` a rigid NEUTRAL (abstract-stays-poly, WI-400), so a body that returns it
/// as the same `w.coll.Element` type-checks — the same `Element` member that grounds on a
/// concrete carrier above stays polymorphic here.
#[test]
fn abstract_carrier_spec_member_stays_poly() {
    let ok = r#"
namespace test.wi376.abstract_iter
  import anthill.prelude.Iterable
  sort Walker
    sort C = ?
    sort Element = ?
    effects E = ?
    requires Iterable[C = C, Element = Element, E = E]
    entity walker(coll: C)
  end
  operation firstElem(w: Walker, e: w.coll.Element) -> w.coll.Element = e
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "an abstract carrier's w.coll.Element (interface from `requires Iterable`) stays a \
         neutral, so `firstElem(...) = e` type-checks; got: {:?}",
        load_errors(&[ok]),
    );
}
