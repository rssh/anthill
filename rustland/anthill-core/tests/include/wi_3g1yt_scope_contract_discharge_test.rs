//! WI-20260921-3G1YT — ROUTE 4: A SPEC-TYPED VALUE IN SCOPE DISCHARGES THE OBLIGATION,
//! AND AN UNRELATED ONE DOES NOT.
//!
//! The ticket deleted the two BODY WALKS that used to decide whether a call's declared
//! `requires` was owed (`op_body_reads_sort_requirement_slot` /
//! `op_body_reads_op_requirement_slot`, with `SlotToRead` and the `if !reads { continue; }`
//! gate). A declared `requires` is owed BECAUSE IT IS DECLARED; what replaces the excuse
//! is a DISCHARGE read from the caller's own scope — `scope_contract_covers_dep`.
//!
//! THE POPULATION THAT MADE THE WALKS LOOK NECESSARY is the first row here: 29 stdlib
//! bodies "declare a chain and never read it", the stdlib's generic consumers among them.
//! Not one needed the excuse — they are OWED AND HELD, because the caller holds a value
//! whose type carries the contract.
//!
//! AND THE ROW THAT BOUNDS IT was written by a review pass over this very change, against
//! a fixture the suite did not have: an UNRELATED value in scope must not decide a call
//! the call itself pinned. It is the sharpest statement of what route 4 is allowed to
//! mean, and it FAILED when it was written — see its own site.

use crate::common::try_load_kb_with;

fn loads(src: &str) -> bool {
    try_load_kb_with(src).is_ok()
}

fn refusal(src: &str, why: &str) -> String {
    match try_load_kb_with(src) {
        Err(errs) => errs.join("\n"),
        Ok(_) => panic!("{why}: expected a LOAD refusal, but the program loaded clean\n{src}"),
    }
}

/// ROUTE 4 PROPER — the ticket's headline shape. `c` is typed at the SPEC, so
/// `FiniteCollection`'s own `requires Iterable[…]` is carried BY `c`'s type; the call
/// `size(c)` owes that chain and holds it.
///
/// MEASURED AS THE ROW THIS LEG CARRIES: backing out the chain leg of
/// `scope_contract_covers_dep` (its `direct_requires_chain` walk) refuses exactly this
/// shape and nothing else in the probe set — the provision leg beside it carries a
/// disjoint population (`wi599`, `wi508`).
#[test]
fn a_spec_typed_parameter_carries_its_spec_s_requires_chain() {
    const SRC: &str = r#"
namespace wi3g1yt.route4
  import anthill.prelude.{List, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  operation total(c: FiniteCollection) -> Int64 effects c.E = size(c)
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation drive() -> Int64 = total(rows())
end
"#;
    assert!(
        loads(SRC),
        "a parameter typed at a spec holds that spec's chain, so `size(c)` is discharged"
    );
}

/// **AN UNRELATED VALUE IN SCOPE MUST NOT DECIDE A CALL THE CALL ITSELF PINNED**, and
/// this row exists because the first cut of route 4's provision leg got it wrong.
///
/// FOUND BY `/code-review` OVER THIS TICKET'S OWN DIFF, and it FAILED when written. The
/// leg replaced the dep's CARRIER with the holder's type unconditionally, so a
/// `Holder.probe(mystery())` needing `Iterable[C = Mystery]` — which nothing provides —
/// resolved `Iterable[C = List[T = Int64]]` instead and LOADED. The dictionary it would
/// have needed does not exist, so the program dies at eval: the silent-wrong-dispatch
/// class this whole file guards, re-created by the guard itself.
///
/// THE TWO HALVES DIFFER IN ONE PARAMETER, which is what makes this a measurement rather
/// than an assertion: `drive` takes an `xs: List[T = Int64]` it never mentions in the
/// body. With it the program used to load; without it the identical call was refused.
/// A value the call does not mention must not change the call's verdict.
#[test]
fn an_unrelated_value_in_scope_does_not_discharge_a_pinned_dep() {
    const WITH_LIST: &str = r#"
namespace wi3g1yt.hole
  import anthill.prelude.{Int64, List, Iterable}
  sort Mystery
    entity mystery
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Iterable[C = HT, Element = Int64, E = {}] = 1
  end
  sort Driver
    operation drive(xs: List[T = Int64]) -> Int64 = Holder.probe(mystery())
  end
end
"#;
    let text = refusal(WITH_LIST, "a pinned `Iterable[C = Mystery]` nothing provides");
    assert!(
        text.contains("Iterable"),
        "the refusal must name the requirement nothing supplies; got {text:?}"
    );

    // THE CONTROL, and it is the same program minus the unused parameter. It was ALREADY
    // refused while the arm above loaded — which is how the defect was isolated to the
    // parameter rather than to the call.
    let without_list = WITH_LIST.replace(
        "operation drive(xs: List[T = Int64]) -> Int64",
        "operation drive(n: Int64) -> Int64",
    );
    assert_ne!(without_list, WITH_LIST, "the fixture edit must have applied");
    refusal(&without_list, "the same call with nothing else in scope");
}

/// A CARRIER'S OWN `requires` IS NOT CARRIED BY HOLDING ONE OF ITS VALUES, which is the
/// bound that separates route 4 from "anything parameterised in scope will do".
///
/// `SortedSet` declares `requires O: WeakOrd[T]` and NOTHING provides `SortedSet` — it IS
/// the carrier, so there is no provision row to hold the slot and the dictionary is a
/// STATIC INPUT its caller owes. Holding a `SortedSet` therefore carries no ordering.
/// Before WI-456 this program loaded clean and died
/// `Internal(… __req_weakord not bound … frame binds [])`; route 4 must not re-admit it.
///
/// MEASURED: with the obtainability gate removed, this row and both `wi456_no_scope_route`
/// refusals go green-to-red together.
#[test]
fn a_carriers_own_requires_is_not_held_by_a_value_of_it() {
    const SRC: &str = r#"
namespace wi3g1yt.carrier
  import anthill.prelude.{SortedSet, Int64}
  sort PolyA
    operation insertA[T, O](s: SortedSet[T = T, O = O], x: T) -> SortedSet[T = T, O = O] =
      SortedSet.insert(s, x)
  end
end
"#;
    let text = refusal(SRC, "a `SortedSet` member called while holding no ordering");
    assert!(
        text.contains("WeakOrd"),
        "the refusal must name the ordering nothing supplies; got {text:?}"
    );
}
