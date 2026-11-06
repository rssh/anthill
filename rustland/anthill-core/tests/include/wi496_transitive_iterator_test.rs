//! WI-496 — TRANSITIVE dispatch of a body-less carrier-param spec op.
//!
//! `Iterable.iterator(c: C)` is body-less. A `List` no longer declares its own
//! `operation iterator(l: List) = l` (dropped here): its Iterable-ness now rides
//! transitively through `List provides Stream` + `Stream provides Iterable`, and
//! `Stream.iterator(s) = s` is the genuine identity impl. So an EXPLICIT
//! `iterator(xs)` on a concrete `List`:
//!
//!   * type-checks — the typer recognises the carrier (`List`) provides the spec
//!     only through a provides-chain and threads the return type from the transitive
//!     provision view (`Stream[T = xs.T, E = {}]`);
//!   * is decided at load (WI-20261105-C6GK8, proposal 073 §1): the dispatch composes
//!     the chain and the call runs `Stream.iterator` within `List`'s `Stream` dictionary.
//!     WI-496 left it as the spec op for eval's value-directed dispatch (WI-492), for a
//!     `DispatchNoMatch` on `Stream`'s `requires EffectsRuntime` the dispatch no longer
//!     gives, and leaves it so now only where the dispatch finds nothing;
//!     `wi_c6gk8_known_type_call_test`'s chain rows fail with that deferral back;
//!   * evaluates — the list itself, as a stream.
//!
//! Contrast WI-495's `IntBag` (a DIRECT `provides Iterable` carrier) and WI-218's
//! `IntBar` (a WITNESS `fact Bar[T = Int64]`), which dispatch concretely to their own impl
//! as they always did.

use anthill_core::kb::term_view::TermView;

use crate::common::unrendered_load_errors_of as load_errs;

const SRC: &str = r#"
namespace wi496.transitive
  import anthill.prelude.{List, Int64, Stream}
  import anthill.prelude.List.{nil, cons, length}
  import anthill.prelude.Iterable.{iterator}
  import anthill.prelude.Stream.{takeN}

  operation mk() -> List[T = Int64] =
    cons(head: 1, tail: cons(head: 2, tail: cons(head: 3, tail: nil)))

  -- explicit iterator(xs) on a List — resolves transitively to Stream.iterator
  -- (List provides Stream provides Iterable). The produced value is a bare
  -- Stream (maybe-infinite), so the unsound `Stream.count` is gone (Phase C /
  -- WI-589); a BOUNDED drain `takeN(_, 1000)` then `length` counts a small finite
  -- list soundly (the bound ≥ its length yields every element).
  operation walk(xs: List[T = Int64]) -> Int64 = length(takeN(iterator(xs), 1000))
end
"#;

#[test]
fn transitive_iterator_typechecks() {
    let errs = load_errs(SRC);
    assert!(
        errs.is_empty(),
        "explicit iterator(xs) on a List must type-check transitively; got:\n{}",
        errs.iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n"),
    );
}

#[test]
fn transitive_iterator_evaluates() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi496.transitive.mk", &[]).expect("build list");
    let got = interp
        .call("wi496.transitive.walk", &[xs])
        .unwrap_or_else(|e| panic!("call walk: {e:?}"));
    assert_eq!(
        got.literal_int64(interp.kb()),
        Some(3),
        "iterator(xs) over a 3-element list, counted"
    );
}

/// `iterator(xs)` in `walk` is decided at load: `Stream.iterator`, within `List`'s `Stream`
/// dictionary (WI-20261105-C6GK8). FAILS with WI-496's deferral restored (no stamp); the two
/// rows above pass either way, value-direction computing the same 3.
#[test]
fn transitive_iterator_is_decided_at_load() {
    use anthill_core::kb::node_occurrence::{visit_classifications, ApplyDispatch};
    let kb = crate::common::load_kb_with(SRC);
    let walk = kb.try_resolve_symbol("wi496.transitive.walk").expect("walk resolves");
    let body = kb.op_body_node(walk).expect("walk has a body");
    let mut decided = Vec::new();
    visit_classifications(body, &mut |occ, _| {
        if let ApplyDispatch::Pin(t) | ApplyDispatch::NeedsDict(t) = occ.apply_dispatch() {
            decided.push(kb.qualified_name_of(t).to_string());
        }
    });
    assert!(
        decided.iter().any(|t| t == "anthill.prelude.Stream.iterator"),
        "`iterator(xs)` is stamped with `Stream.iterator`; stamps: {decided:?}"
    );
}
