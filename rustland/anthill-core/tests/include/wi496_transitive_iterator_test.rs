//! WI-496 — TRANSITIVE dispatch of a body-less carrier-param spec op.
//!
//! `Iterable.iterator(c: C)` is body-less. A `List` no longer declares its own
//! `operation iterator(l: List) = l` (dropped here): its Iterable-ness now rides
//! transitively through `List provides Stream` + `Stream provides Iterable`, and
//! `Stream.iterator(s) = s` is the genuine identity impl. So an EXPLICIT
//! `iterator(xs)` on a concrete `List`:
//!
//!   * type-checks — the typer recognises the carrier (`List`) provides the spec
//!     only through a provides-chain, threads the return type from the transitive
//!     provision view (`Stream[T = xs.T, E = {}]`), and leaves the call as the
//!     spec op for eval (it cannot dispatch concretely — `List` ≤ `Stream` would
//!     drag in `Stream`'s `requires EffectsRuntime`, which an identity iterator
//!     never threads);
//!   * evaluates — eval's value-directed dispatch (WI-492) routes the `List` value
//!     to `Stream.iterator`, returning the list itself as a stream.
//!
//! Contrast WI-495's `IntBag` (a DIRECT `provides Iterable` carrier) and WI-218's
//! `IntBar` (a WITNESS `fact Bar[T = Int64]`): both still dispatch concretely to
//! their own impl — only the provides-chain carrier defers.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

fn load_errs(extra: &str) -> Vec<LoadError> {
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
        errs.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n"),
    );
}

#[test]
fn transitive_iterator_evaluates() {
    let mut interp = crate::common::interp_for(SRC);
    let xs = interp.call("wi496.transitive.mk", &[]).expect("build list");
    let got = interp
        .call("wi496.transitive.walk", &[xs])
        .unwrap_or_else(|e| panic!("call walk: {e:?}"));
    assert_eq!(got.as_int(), Some(3), "iterator(xs) over a 3-element list, counted");
}
