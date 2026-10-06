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
//! The consumers did not need the excuse — they are OWED AND HELD, because the caller holds
//! a value whose type carries the contract. Two that were held only by a value the call
//! never mentions, `MappedStream.map` and `FilteredStream.filter`, were repaired by deleting
//! the clause no body read (WI-20261005-2KV4Y).
//!
//! WI-20261005-KSSA4 REMOVED THE VALUE HALF OF THE ROUTE. A value typed at a spec over a
//! parameter is not a value of a sort that provides it, so no value holds a spec's chain:
//! the consumers are written `c: FiniteCollection.C`, which requires the spec of the
//! parameter's sort, and the chain is in the dictionary the caller supplies for that
//! requirement. What the cover still answers for is a declared `require[…]` bracket.
//!
//! AND THE ROW THAT BOUNDS IT was written by a review pass over this very change, against
//! a fixture the suite did not have: an UNRELATED value in scope must not decide a call
//! the call itself pinned. It is the sharpest statement of what route 4 is allowed to
//! mean, and it FAILED when it was written — see its own site.

use crate::common::try_load_kb_with;
use anthill_core::kb::term_view::TermView;

fn loads(src: &str) -> bool {
    try_load_kb_with(src).is_ok()
}

fn refusal(src: &str, why: &str) -> String {
    match try_load_kb_with(src) {
        Err(errs) => errs.join("\n"),
        Ok(_) => panic!("{why}: expected a LOAD refusal, but the program loaded clean\n{src}"),
    }
}

/// THE TICKET'S HEADLINE SHAPE, IN THE SPELLING THAT SAYS IT. `c: FiniteCollection.C` is a
/// value of a sort that provides `FiniteCollection`, and the operation requires the spec of
/// that sort; `FiniteCollection`'s own `requires Iterable[…]` is part of the dictionary the
/// caller supplies, so `size(c)` reads its chain from the operation's own requirement.
///
/// IT WAS WRITTEN `total(c: FiniteCollection)` — a parameter typed at the spec, read as
/// "a value that holds the spec's chain" — and that reading is gone (WI-20261005-KSSA4): a
/// `List` provides `FiniteCollection` and is not one. The row below refuses that spelling.
#[test]
fn a_requirement_on_the_parameters_sort_supplies_the_specs_chain() {
    const SRC: &str = r#"
namespace wi3g1yt.route4
  import anthill.prelude.{List, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  operation total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E = size(c)
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation drive() -> Int64 = total(rows())
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    let v = interp
        .call("wi3g1yt.route4.drive", &[])
        .unwrap_or_else(|e| panic!("drive: {e:?}"));
    assert_eq!(
        v.literal_int64(interp.kb()),
        Some(4),
        "`total` is handed `List`'s `FiniteCollection` dictionary, chain and all",
    );
}

/// THE SPEC-TYPED SPELLING OF THE SAME PROGRAM IS REFUSED, where it used to be the route's
/// headline. A value typed at a spec over a parameter is not a value of a sort that
/// provides it, so the `List` is refused at `total`'s parameter and `c` at `size`'s — each
/// naming the spelling that says what was meant.
#[test]
fn a_parameter_typed_at_the_spec_holds_nothing() {
    const SRC: &str = r#"
namespace wi3g1yt.route4spec
  import anthill.prelude.{List, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  operation total(c: FiniteCollection) -> Int64 effects c.E = size(c)
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation drive() -> Int64 = total(rows())
end
"#;
    let errs = refusal(SRC, "a `List` is not a `FiniteCollection`");
    assert!(
        errs.contains("expected FiniteCollection, got List[T = Int64]")
            && errs.contains("Type this position `anthill.prelude.FiniteCollection.C`"),
        "the argument is refused at the spec-typed parameter; got:\n{errs}",
    );
    assert!(
        errs.contains("expected anthill.prelude.FiniteCollection.C, got FiniteCollection")
            && errs.contains("a value typed at it is not a value of a sort that provides it"),
        "and the spec-typed `c` is refused where the carrier is expected; got:\n{errs}",
    );
}

/// **AN UNRELATED VALUE IN SCOPE MUST NOT DECIDE A CALL THE CALL ITSELF PINNED**, and
/// this row exists because the first cut of route 4 had a second leg that got it wrong
/// (the leg is gone since WI-20261005-2KV4Y, which refuses the unpinned twin of this row).
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
/// MEASURED: with the rule that it is a SPEC which holds a chain removed
/// (`sort_is_a_provided_spec`, once one arm of an "obtainability gate"), this row and both
/// `wi456_no_scope_route` refusals went green-to-red together. Since WI-20260923-WN9P8 the
/// program is refused first as a FORWARD of `insertA`'s own `O`, which the frame holds no
/// dictionary for (`project_forwarded_slot`, before route 4 is asked). So that rule alone
/// no longer reddens this row: it reddens with the rule and that forward rule backed out
/// together, measured, and so do wi456's three no-route rows.
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
