//! WI-474 (WI-447 bare-form prereq, Gap E): a Stream spec op DISPATCHED on a
//! non-Stream provider (e.g. List) must thread the element through the `s.T`
//! PROJECTION in the abstract op's return. With the BARE-form spec
//! `splitFirst(s: Stream) -> Option[Pair[A = s.T, B = Stream[T = s.T]]]` called on
//! `xs : List[Int64]`, the `s.T` projection (`Stream.T` off the receiver — a
//! CROSS-SORT member, since `T` is declared on `Stream` but `xs` is a `List`) must
//! eliminate to the carrier's element `Int64` via the `List provides Stream[T]`
//! binding. When filed, the dispatched path left `?_` (`type mismatch in
//! match.rule: expected Int64, got ?_`) while the DIRECT `List.splitFirst` call
//! (whose `xs.T` is a same-sort projection) already threaded.
//!
//! The mechanism is satisfied by delivered work — WI-461 (the production dual: a
//! bare self-receiver returning the receiver as a PROVIDED sort threads the
//! projection through provider-admissibility) plus the WI-376/399 projection
//! eliminator, which together resolve a cross-sort `s.T` against the receiver's
//! `provides` binding. The stdlib `Stream`/`List` are still in the explicit
//! `[Elem, Eff]` form (the bare-form revert is WI-447), so these tests are the
//! SELF-CONTAINED bare-`s.T` analogue of `wi357`'s dispatched tests — they pin the
//! behaviour WI-447 will rely on. The `s.E` effect-projection dual is the sibling
//! WI-475; these fixtures thread only the element `s.T`.

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

/// A `match.rule` mismatch whose RESOLVED types confirm the threaded element: the
/// soundness tests return the element (threaded to `Int64`) in a `-> String` op, so
/// the error must read `expected String, got Int64` — pinning that `s.T` eliminated
/// to the real `Int64` (not an unconstrained `?_` that would conform to `String`),
/// and that the failure is the return mismatch, not an unrelated parse/import error.
fn rejected_int64_vs_string(errs: &[String]) -> bool {
    errs.iter().any(|e| {
        e.contains("match.rule") && e.contains("expected String") && e.contains("got Int64")
    })
}

// ── splitFirst-style: a Pair-shaped primitive spec op, dispatched ────────────

/// The headline: a BARE-form primitive spec op
/// `splitFirstX(s: Strm) -> Option[Pair[A = s.T, B = Strm[T = s.T]]]`, dispatched on
/// a `Lst[Int64]` (which `provides Strm[T]` and supplies its own `splitFirstX`),
/// threads the cross-sort `s.T` to `Int64` so `pair(h, _)` binds `h : Int64`.
#[test]
fn dispatched_spec_splitfirst_threads_element_bare_form() {
    let src = r#"
namespace test.wi474.strm
  import anthill.prelude.{Option, Pair}
  export Strm
  sort Strm
    sort T = ?
    operation splitFirstX(s: Strm) -> Option[T = Pair[A = s.T, B = Strm[T = s.T]]]
  end
end
namespace test.wi474.lst
  import anthill.prelude.{Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import test.wi474.strm.{Strm}
  export Lst
  sort Lst
    sort T = ?
    provides Strm[T = T]
    entity lnil
    entity lcons(hd: T, tl: Lst)
    operation splitFirstX(xs: Lst) -> Option[T = Pair[A = xs.T, B = Lst[T = xs.T]]] =
      match xs
        case lnil() -> none
        case lcons(h, t) -> some(pair(h, t))
  end
end
namespace test.wi474.use
  import anthill.prelude.{Int64, Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import test.wi474.lst.{Lst}
  import test.wi474.strm.Strm.{splitFirstX}
  operation get_head(xs: Lst[T = Int64]) -> Int64 =
    match splitFirstX(xs)
      case some(pair(h, _)) -> h
      case none() -> 0
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "dispatched bare-form Strm.splitFirstX on a Lst[Int64] must thread the cross-sort \
         s.T to Int64 so `pair(h, _)` binds h : Int64; got: {errs:?}",
    );
}

/// Soundness: with `s.T` threaded to `Int64`, returning the head in a `-> String`
/// context must be REJECTED — ruling out "the element became an unconstrained `?_`
/// that conforms to anything" as the reason the positive test passes.
#[test]
fn dispatched_spec_splitfirst_wrong_return_rejected() {
    let src = r#"
namespace test.wi474w.strm
  import anthill.prelude.{Option, Pair}
  export Strm
  sort Strm
    sort T = ?
    operation splitFirstX(s: Strm) -> Option[T = Pair[A = s.T, B = Strm[T = s.T]]]
  end
end
namespace test.wi474w.lst
  import anthill.prelude.{Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import test.wi474w.strm.{Strm}
  export Lst
  sort Lst
    sort T = ?
    provides Strm[T = T]
    entity lnil
    entity lcons(hd: T, tl: Lst)
    operation splitFirstX(xs: Lst) -> Option[T = Pair[A = xs.T, B = Lst[T = xs.T]]] =
      match xs
        case lnil() -> none
        case lcons(h, t) -> some(pair(h, t))
  end
end
namespace test.wi474w.use
  import anthill.prelude.{Int64, String, Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import test.wi474w.lst.{Lst}
  import test.wi474w.strm.Strm.{splitFirstX}
  operation get_head(xs: Lst[T = Int64]) -> String =
    match splitFirstX(xs)
      case some(pair(h, _)) -> h
      case none() -> "x"
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        rejected_int64_vs_string(&errs),
        "unsound: the head of a Lst[Int64] dispatched through the bare-form spec is Int64, so \
         returning it in a `-> String` op must be rejected; got: {errs:?}",
    );
}

// ── head-style: a default-body spec op whose return IS `Option[s.T]` ─────────

/// The `head`-shaped case, where the carrier supplies NO own impl — the spec op
/// `firstE(s: Strm) -> Option[s.T]` (a default body over the primitive
/// `splitFirstX`) is the ONLY candidate, so the dispatched call MUST use the spec's
/// own `Option[s.T]` return. The cross-sort `s.T` (`Strm.T` off `xs : Lst`) still
/// eliminates to `Int64` via the provides binding.
#[test]
fn dispatched_spec_head_threads_element_bare_form() {
    let src = r#"
namespace test.wi474h.strm
  import anthill.prelude.{Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  export Strm
  sort Strm
    sort T = ?
    operation splitFirstX(s: Strm) -> Option[T = Pair[A = s.T, B = Strm[T = s.T]]]
    operation firstE(s: Strm) -> Option[T = s.T] =
      match splitFirstX(s)
        case some(pair(h, _)) -> some(h)
        case none() -> none
  end
end
namespace test.wi474h.lst
  import anthill.prelude.{Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import test.wi474h.strm.{Strm}
  export Lst
  sort Lst
    sort T = ?
    provides Strm[T = T]
    entity lnil
    entity lcons(hd: T, tl: Lst)
    operation splitFirstX(xs: Lst) -> Option[T = Pair[A = xs.T, B = Lst[T = xs.T]]] =
      match xs
        case lnil() -> none
        case lcons(h, t) -> some(pair(h, t))
  end
end
namespace test.wi474h.use
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}
  import test.wi474h.lst.{Lst}
  import test.wi474h.strm.Strm.{firstE}
  operation get_head(xs: Lst[T = Int64]) -> Int64 =
    match firstE(xs)
      case some(h) -> h
      case none() -> 0
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "dispatched bare-form Strm.firstE (Option[s.T]) on a Lst[Int64] must thread the \
         cross-sort s.T to Int64 so `some(h)` binds h : Int64; got: {errs:?}",
    );
}

/// Soundness for the head-shaped case: returning the `Option[s.T]` element in a
/// `-> String` context is rejected (the element is the real `Int64`, not `?_`).
#[test]
fn dispatched_spec_head_wrong_return_rejected() {
    let src = r#"
namespace test.wi474hw.strm
  import anthill.prelude.{Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  export Strm
  sort Strm
    sort T = ?
    operation splitFirstX(s: Strm) -> Option[T = Pair[A = s.T, B = Strm[T = s.T]]]
    operation firstE(s: Strm) -> Option[T = s.T] =
      match splitFirstX(s)
        case some(pair(h, _)) -> some(h)
        case none() -> none
  end
end
namespace test.wi474hw.lst
  import anthill.prelude.{Option, Pair}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}
  import test.wi474hw.strm.{Strm}
  export Lst
  sort Lst
    sort T = ?
    provides Strm[T = T]
    entity lnil
    entity lcons(hd: T, tl: Lst)
    operation splitFirstX(xs: Lst) -> Option[T = Pair[A = xs.T, B = Lst[T = xs.T]]] =
      match xs
        case lnil() -> none
        case lcons(h, t) -> some(pair(h, t))
  end
end
namespace test.wi474hw.use
  import anthill.prelude.{Int64, String, Option}
  import anthill.prelude.Option.{some, none}
  import test.wi474hw.lst.{Lst}
  import test.wi474hw.strm.Strm.{firstE}
  operation get_head(xs: Lst[T = Int64]) -> String =
    match firstE(xs)
      case some(h) -> h
      case none() -> "x"
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        rejected_int64_vs_string(&errs),
        "unsound: the head element threaded through the bare-form spec is Int64, so returning \
         it in a `-> String` op must be rejected; got: {errs:?}",
    );
}
