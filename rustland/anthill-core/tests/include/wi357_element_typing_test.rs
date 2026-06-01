//! WI-357 — thread the element type through a destructured `Pair` over a
//! **dispatched** Stream spec-op result, so `head`/`splitFirst` consuming a
//! `List[Int]` *as a Stream* types statically as `Option[Int]` rather than an
//! unbound `?_`.
//!
//! Proposal library/002: a `List` *is* a `Stream` (`iterator(l) = l`), and
//! consumers walk it through the shared `Stream` interface — `splitFirst` /
//! `head`. When the spec op `Stream.splitFirst(s: Stream) -> Option[T = Pair[A
//! = T, B = Stream]]` dispatches to `List`'s impl, the carrier's element
//! (`List[Int]` ⇒ `Int`) must flow to the spec's element `T` and out through
//! the return, so a destructured `pair(h, _)` binds `h : Int`.
//!
//! The DIRECT `List.splitFirst` call already threads correctly (anchor test
//! below). The gap WI-357 closes is the DISPATCHED path: a `List[Int]` consumed
//! through the `Stream` spec leaves `h` as `?_`, and a typed extraction fails
//! to load with `type mismatch in match.rule: expected Int, got ?_`.
//!
//! Runtime decomposition is already correct (see `eval_test`'s
//! `wi343_list_splitfirst_*`); this pins the STATIC element typing.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra source → load errors (empty Vec on clean load).
fn try_load(extra: &str) -> Vec<load::LoadError> {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

fn errors_text(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

// ── Anchor: the DIRECT List.splitFirst call already threads the element ──────

/// `List.splitFirst` (the concrete carrier op) over a `List[Int]` already binds
/// `h : Int` — the `List[T = Int]` argument unifies with the concrete op's own
/// element parameter. This is the baseline that already works; WI-357 is about
/// the dispatched path below behaving the same.
#[test]
fn direct_list_splitfirst_threads_element_type() {
    let src = r#"
namespace test.wi357.direct
  import anthill.prelude.{List, Int}
  import anthill.prelude.List.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  operation get_head(xs: List[T = Int]) -> Int =
    match splitFirst(xs)
      case some(pair(h, _)) -> h
      case none() -> 0
end
"#;
    let errs = try_load(src);
    assert!(
        errs.is_empty(),
        "direct List.splitFirst on a List[Int] should thread Int to `pair(h, _)`; \
         got load errors:\n{}",
        errors_text(&errs),
    );
}

// ── WI-357: the DISPATCHED Stream.splitFirst path ───────────────────────────

/// Consume a `List[Int]` through the `Stream` spec op `splitFirst`. The op
/// dispatches to `List`'s impl (List provides Stream, WI-350); the element type
/// `Int` must thread through the dispatched result so `pair(h, _)` binds
/// `h : Int` and the `-> h` branch conforms to the `Int` return.
#[test]
fn dispatched_stream_splitfirst_threads_element_type() {
    let src = r#"
namespace test.wi357.dispatched
  import anthill.prelude.{List, Int}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  operation get_head(xs: List[T = Int]) -> Int =
    match splitFirst(xs)
      case some(pair(h, _)) -> h
      case none() -> 0
end
"#;
    let errs = try_load(src);
    assert!(
        errs.is_empty(),
        "dispatched Stream.splitFirst on a List[Int] must thread the element type \
         Int through the dispatched result to `pair(h, _)`; got load errors:\n{}",
        errors_text(&errs),
    );
}

/// Soundness anchor for the dispatched path: with the element threaded as
/// `Int`, returning the head in a `-> String` context must STILL be rejected —
/// ruling out "the element became an unconstrained `?_` that conforms to
/// anything" as the reason the positive test passes.
#[test]
fn dispatched_stream_splitfirst_wrong_return_type_is_rejected() {
    let src = r#"
namespace test.wi357.dispatched_wrong
  import anthill.prelude.{List, Int, String}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  operation get_head(xs: List[T = Int]) -> String =
    match splitFirst(xs)
      case some(pair(h, _)) -> h
      case none() -> "x"
end
"#;
    let errs = try_load(src);
    assert!(
        !errs.is_empty(),
        "unsound: the head of a List[Int] consumed as a Stream is Int, so returning \
         it in a `-> String` operation must be rejected; loaded clean instead",
    );
}

/// The `head` spec op (`Stream.head(s) -> Option[T = T]`) over a `List[Int]`
/// must likewise yield `Option[Int]`, so `case some(h) -> h` binds `h : Int`.
#[test]
fn dispatched_stream_head_threads_element_type() {
    let src = r#"
namespace test.wi357.head
  import anthill.prelude.{List, Int}
  import anthill.prelude.Stream.{head}
  import anthill.prelude.Option.{some, none}

  operation get_head(xs: List[T = Int]) -> Int =
    match head(xs)
      case some(h) -> h
      case none() -> 0
end
"#;
    let errs = try_load(src);
    assert!(
        errs.is_empty(),
        "dispatched Stream.head on a List[Int] must yield Option[Int] so `some(h)` \
         binds h : Int; got load errors:\n{}",
        errors_text(&errs),
    );
}
