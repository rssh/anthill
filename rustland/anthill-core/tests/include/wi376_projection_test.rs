//! WI-376: expression-carried type projections `s.T` / `s.Sort`.
//!
//! A producer's projection signature `peek(l: List) -> l.T` threads the receiver's
//! element through call sites: the projection is ELIMINATED by projecting the
//! ARGUMENT's inferred type (`List[Int].T = Int`) — the synthesis-time discharge of
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

/// `peek(l: List) -> l.T` threads the element: calling it on a `List[Int]` yields
/// `Int`, so returning the call where `Int` is declared CONFORMS.
#[test]
fn projection_threads_element_concrete() {
    let ok = r#"
namespace test.wi376.elem_ok
  import anthill.prelude.{List, Int}
  operation peek(l: List) -> l.T
  operation caller(xs: List[T = Int]) -> Int = peek(xs)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "peek(xs) is List[Int].T = Int; returning it as Int must conform",
    );
}

/// The threaded element is REAL: returning `peek(xs)` (which is `Int`) where `String`
/// is declared must be rejected — the projection did not invent a fresh element.
#[test]
fn projection_wrong_element_is_rejected() {
    let wrong = r#"
namespace test.wi376.elem_wrong
  import anthill.prelude.{List, Int, String}
  operation peek(l: List) -> l.T
  operation caller(xs: List[T = Int]) -> String = peek(xs)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "peek(xs) is Int, not String — the wrong declared return must be rejected",
    );
}

/// `echo(l: List) -> l.Sort` projects the WHOLE parameterized sort of the receiver,
/// so `echo(xs)` on a `List[Int]` is `List[Int]` (every parameter captured).
#[test]
fn projection_sort_captures_whole_type() {
    let ok = r#"
namespace test.wi376.sort_ok
  import anthill.prelude.{List, Int}
  operation echo(l: List) -> l.Sort
  operation caller(xs: List[T = Int]) -> List[T = Int] = echo(xs)
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "echo(xs) is l.Sort = List[Int]; returning it as List[Int] must conform",
    );

    let wrong = r#"
namespace test.wi376.sort_wrong
  import anthill.prelude.{List, Int, String}
  operation echo(l: List) -> l.Sort
  operation caller(xs: List[T = Int]) -> List[T = String] = echo(xs)
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "echo(xs) is List[Int], not List[String] — must be rejected",
    );
}

/// A member the receiver's concrete sort does NOT declare is a loud error, never a
/// silent fresh var: `List` declares `T`, not `Nonesuch`, so `l.Nonesuch` is rejected.
#[test]
fn projection_missing_member_is_loud() {
    let src = r#"
namespace test.wi376.missing
  import anthill.prelude.{List, Int}
  operation bad(l: List) -> l.Nonesuch
  operation caller(xs: List[T = Int]) -> Int = bad(xs)
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
/// composition — `gather(to_stream(xs))` on a `List[Int]` is `List[Int]`, with no
/// fresh `?_` element. (The written `E = {}` carries the observation effect; the
/// element rides the projection.)
#[test]
fn projection_threads_through_composition() {
    let ok = r#"
namespace test.wi376.compose_ok
  import anthill.prelude.{List, Stream, Int}
  operation to_stream(l: List) -> Stream[T = l.T, E = {}]
  operation gather(s: Stream) -> List[T = s.T]
  operation walk(xs: List[T = Int]) -> List[T = Int] = gather(to_stream(xs))
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "gather(to_stream(xs)) must thread Int through the projection composition",
    );

    let wrong = r#"
namespace test.wi376.compose_wrong
  import anthill.prelude.{List, Stream, Int, String}
  operation to_stream(l: List) -> Stream[T = l.T, E = {}]
  operation gather(s: Stream) -> List[T = s.T]
  operation walk(xs: List[T = Int]) -> List[T = String] = gather(to_stream(xs))
end
"#;
    assert!(
        !load_errors(&[wrong]).is_empty(),
        "the composed element is Int, not String — wrong declared return must be rejected",
    );
}

/// A BARE / abstract receiver is a loud error, NOT a silent fresh var: projecting
/// `l.T` off a bare `List` (element unbound) would have to mint an unconstrained var
/// that could unsoundly satisfy any demand (the same `peek(l)` usable as both `Int`
/// and `String`). The sound "stays polymorphic" projection — read the receiver's
/// DECLARED-INTERFACE member so the result is rigid — is the abstract-receiver
/// follow-on; until then it is rejected.
#[test]
fn projection_bare_receiver_is_rejected() {
    let src = r#"
namespace test.wi376.bare
  import anthill.prelude.{List, Int}
  operation peek(l: List) -> l.T
  operation relay(l: List) -> Int = peek(l)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("not concretely known") || e.contains("abstract-receiver")),
        "projecting off a bare (element-unbound) receiver must be a loud error; got: {errs:?}",
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
  import anthill.prelude.{Cell, Int, Modify}
  operation make_pair() -> (a: Cell[V = Int], b: Cell[V = Int])
    effects {Modify[result.a], Modify[result.b]}
  operation run() -> (a: Cell[V = Int], b: Cell[V = Int])
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

/// A projection nested in a denoted-bearing type — `Stream[T = l.T, E = {Modify[c]}]`
/// rides a `Value::Node` carrier — is rejected loudly rather than leaking the
/// un-eliminated `l.T` into the inferred type (the Node-carrier rewrite is a follow-on).
#[test]
fn projection_in_denoted_node_is_rejected() {
    let src = r#"
namespace test.wi376.node
  import anthill.prelude.{List, Stream, Int, Cell, Modify}
  operation src(l: List, c: Cell[V = Int]) -> Stream[T = l.T, E = {Modify[c]}]
  operation use_src(xs: List[T = Int], c: Cell[V = Int]) -> Int = src(xs, c)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("denoted-bearing") || e.contains("not yet supported")),
        "a projection inside a denoted-bearing type must be a loud error, not a leak; got: {errs:?}",
    );
}
