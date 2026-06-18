//! WI-507 — a BARE-call carrier-only mutating spec op (`clear(c)`, where the
//! carrier `C` is the sole param) must dispatch and evaluate like the dot form
//! `c.clear()`.
//!
//! The bug: a generic op constrained by `requires MutableCollection[C, …]`
//! whose body bare-calls the carrier-only `clear(c)` typechecked but died at
//! eval with the dispatching-requirement dict never threaded into its frame
//! (`DeferToRequirement: requirement param `__req_mutablecollection` not bound
//! in caller frame`). The sibling `insert(c, x)` — same `requires`, but a
//! carrier PLUS a value arg — worked: its value arg pins the spec's `Element`
//! param, so the compile-stage dispatching-dict resolution found the carrier's
//! `provides` fact. The carrier-only call pins only `C`, leaving `Element` as
//! the enclosing sort's own unpinned `Ref(Sort.Element)`, which clashed with
//! the value the `provides` fact would assign (it ties `Element` to `C` via a
//! shared impl param) — so no dict was built.
//!
//! Fix (kb/typing.rs, `match_candidate_against_goal`): a type-param wildcard on
//! the per-call side matches an already-bound impl param without constraining
//! it — the concrete carrier already pins the shared param, and the sibling is
//! whatever that pinning implies. The all-wildcard call already resolved (its
//! carrier is a wildcard too, so the param never pins); this extends the same
//! leniency to the carrier-concrete / sibling-abstract mix.

use anthill_core::eval::Value;
use crate::common::{interp_for, register_modify_handler};

const SRC: &str = r#"
namespace test.wi507
  import anthill.prelude.{Int64, Bool, Unit, MutableStack, MutableCollection}
  import anthill.prelude.MutableCollection.{insert, clear}
  import anthill.prelude.Iterable.{size}

  operation fresh() -> MutableStack[T = Int64] effects Modify[result] = MutableStack.new()
  operation pushN(s: MutableStack[T = Int64], x: Int64) -> Unit effects Modify[s] = MutableStack.push(s, x)
  operation depth(s: MutableStack[T = Int64]) -> Int64 = size(s)

  -- CONCRETE carrier, bare carrier-only call (resolves to MutableStack.clear).
  operation wipeBare(s: MutableStack[T = Int64]) -> Unit effects Modify[s] = clear(s)

  -- ABSTRACT carrier: generic over any MutableCollection. `c : C` is bound by
  -- the requires clause, so the spec-op calls dispatch through the threaded
  -- requirement dict (the WI-415..423 path). `wipeBareIt` is the carrier-only
  -- case under test; `addIt` (carrier + value arg) is the sibling that always
  -- worked.
  sort Wiper
    sort C = ?
    sort Element = ?
    effects E = ?
    requires MutableCollection[C = C, Element = Element, E = E]
    operation wipeBareIt(c: C) -> Unit effects Modify[c] = clear(c)
    operation addIt(c: C, x: Element) -> Bool effects Modify[c] = insert(c, x)
  end

  -- top-level drivers (no requires) that thread one handle through the abstract
  -- Wiper ops on a concrete MutableStack.
  operation driveBare() -> Int64 effects Modify[result] =
    let s = fresh()
    let _ = pushN(s, 10)
    let _ = pushN(s, 20)
    let _ = Wiper.wipeBareIt(s)
    depth(s)

  operation driveInsert() -> Int64 effects Modify[result] =
    let s = fresh()
    let _ = Wiper.addIt(s, 10)
    let _ = Wiper.addIt(s, 20)
    depth(s)
end
"#;

/// Concrete carrier: bare `clear(s)` empties in place (resolves to the carrier's
/// own concrete override — the form WI-364's lifecycle test originally avoided).
#[test]
fn wi507_concrete_bare_clear_empties() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);

    let s = interp.call("test.wi507.fresh", &[]).expect("fresh");
    for x in [10, 20, 30] {
        interp.call("test.wi507.pushN", &[s.clone(), Value::Int(x)]).expect("push");
    }
    interp.call("test.wi507.wipeBare", &[s.clone()]).expect("bare clear (concrete)");
    assert_eq!(
        interp.call("test.wi507.depth", &[s]).unwrap().as_int(),
        Some(0),
        "concrete bare clear empties the same handle",
    );
}

/// The regression: the abstract, requires-threaded carrier-only `clear(c)`.
#[test]
fn wi507_abstract_carrier_only_clear_empties() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);
    let r = interp.call("test.wi507.driveBare", &[]).expect("driveBare");
    assert_eq!(r.as_int(), Some(0), "abstract carrier-only bare clear empties");
}

/// Guard: the sibling carrier+value `insert(c, x)` keeps working (it never broke,
/// but the fix touches the shared dispatch matcher).
#[test]
fn wi507_abstract_insert_still_works() {
    let mut interp = interp_for(SRC);
    register_modify_handler(&mut interp);
    let r = interp.call("test.wi507.driveInsert", &[]).expect("driveInsert");
    assert_eq!(r.as_int(), Some(2), "abstract insert adds two");
}
