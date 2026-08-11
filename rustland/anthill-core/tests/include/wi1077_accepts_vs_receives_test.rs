//! WI-1077 — "accepts" vs "receives on", DECIDED: the carrier parameter stays INFERRED, and
//! the rule is written down rather than replaced.
//!
//! `spec_carrier_param` (WI-1076) reads a spec's carrier as *the first declared type parameter
//! that some declared operation TAKES AS A PARAMETER*. "Takes" is wider than "receives on",
//! which is what would decide if the language could say it. Three options were on the table —
//! (a) mark the parameter (`sort C = ? carrier`), (b) declare spec-hood (`spec Iterable … end`)
//! and derive the carrier, (c) leave it inferred and document the rule. **(c)** is the
//! decision (user, 2026-08-11), so neither (a) nor (b)'s new surface is coming and the residue
//! below is the LANGUAGE's answer, not a defect awaiting one.
//!
//! ## What (c) commits to, and why it needs tests rather than only prose
//!
//! A documented rule with nothing driving it is the failure this repo names most often. The
//! residue has two faces and this file drives both — one of which had NO coverage at all,
//! because the corpus does not contain the shape:
//!
//! | face | row |
//! |---|---|
//! | a spec that RECEIVES on its own sort and also ACCEPTS its element | [`a_spec_that_accepts_its_own_element_files_the_provision_at_the_element`] — new; nothing measured it before |
//! | a carrier-parameterized spec declaring its element FIRST and accepting it | `wi1076_…::an_accepted_element_declared_first_still_wins_over_the_carrier_param` — kept, re-worded from "KNOWN RESIDUE" to the shipped rule |
//!
//! ## The repair to prefer is the DECLARATION, not a wider predicate
//!
//! WI-1076's seventh mis-filed provision was fixed that way and it is the model: `LogicalStream
//! .pure` read `pure(x: T) -> LogicalStream`, reusing the SORT's element for a value it merely
//! lifts, and as `pure[A](x: A) -> LogicalStream[A, {}]` the question stops being asked. Where
//! the reuse is ACCIDENTAL, change the signature. What (c) accepts is the INTENDED reuse —
//! `Set.insert(s: Set, x: T)`, `Map.put(m: Map, key: K, value: V)` — where the operation really
//! does take the sort's own element.
//!
//! ## CONTROL, and it is what makes these rows measurements rather than restatements
//!
//! Every row here passes with the ticket "backed out", because (c) ships today's behaviour —
//! that is the point of choosing it. What each row guards against is DRIFT: a future widening
//! of `spec_carrier_param` (say, to "receives on" via `spec_is_self_representing`) changes
//! these verdicts, and WI-1076 measured that such a widening REFUSES A PROGRAM THAT LOADS —
//! `a_spec_with_both_a_carrier_param_and_a_self_receiver_keeps_its_binding` is the row it
//! breaks. So each row states the verdict it holds AND names what would move it; a green run
//! here plus that row is what says the documented rule and the implemented one still agree.
//!
//! REFERENCE: WI-1076 (the predicate, and both rejected alternatives with their measurements),
//! WI-1069 (what a `provides` clause's bindings mean), WI-424
//! (`provision_binds_param_to_carrier`, the sound but provision-relative gate that cannot be
//! used here), proposal 058 §3.6, `docs/kernel-language.md` §5.1.

use anthill_core::kb::KnowledgeBase;

use crate::wi1076_self_representing_spec_carrier_test::carrier_rows;
use crate::wi860_default_provider_relations_test::relation_rows;

/// A SPEC THAT ACCEPTS ITS OWN ELEMENT — the face of the residue nothing measured, because no
/// stdlib provision has this shape and a user can write it today.
///
/// `Bag` receives on itself (`insert(s: Bag, x: T)`, `size(s: Bag)`) AND takes its own element
/// `T`. `T` is the first declared type parameter some operation takes as a parameter, so `T`
/// answers as the carrier and `sort IntBag provides Bag[T = Int64]` files at **`Int64`** — the
/// element — rather than at `IntBag`, the provider. Under (c) that is the rule, not a bug:
/// "takes as a parameter" is what is asked, and `insert` genuinely takes it.
///
/// CONTRAST IN THE SAME PROGRAM, which is what keeps this from being a restatement of the
/// implementation: `Feeder` differs only in NOT taking its element (`next(f: Feeder) -> T`
/// returns it instead), and its provision files at the PROVIDER. One character of difference
/// in what an operation's parameter list mentions moves the carrier — that is the rule stated
/// as a measurement.
///
/// CONTROL: both halves pass with the ticket backed out (they are today's behaviour, which is
/// what (c) adopts). They move together only under a change to `spec_carrier_param`; a
/// widening to "receives on" flips the `Bag` half to the provider and, per WI-1076's
/// measurement, refuses `a_spec_with_both_a_carrier_param_and_a_self_receiver_keeps_its_binding`.
#[test]
fn a_spec_that_accepts_its_own_element_files_the_provision_at_the_element() {
    let src = r#"namespace test.wi1077.accepts
  import anthill.prelude.{Int64, Bool}

  sort Bag
    sort T = ?
    operation insert(s: Bag, x: T) -> Bag
    operation size(s: Bag) -> Int64
  end

  sort Feeder
    sort T = ?
    operation next(f: Feeder) -> T
  end

  sort IntBag
    import anthill.prelude.{Int64, Bool}
    entity intBag(n: Int64)
    provides Bag[T = Int64]
    operation insert(s: IntBag, x: Int64) -> IntBag = s
    operation size(s: IntBag) -> Int64 = 0
  end

  sort IntFeeder
    import anthill.prelude.Int64
    entity intFeeder(n: Int64)
    provides Feeder[T = Int64]
    operation next(f: IntFeeder) -> Int64 = 1
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        carrier_rows(&mut kb, "Bag"),
        vec!["IntBag | Bag | Int64".to_string()],
        "`insert(s: Bag, x: T)` TAKES the element, and `spec_carrier_param` cannot tell that \
         from receiving on a carrier — so `T` answers and the provision files at `Int64`. \
         WI-1077 option (c): this is the documented rule",
    );
    assert_eq!(
        carrier_rows(&mut kb, "Feeder"),
        vec!["IntFeeder | Feeder | IntFeeder".to_string()],
        "`Feeder` differs ONLY in not taking its element — `next` returns it — so it has no \
         carrier parameter and its provision records the PROVIDER. The pair is the rule",
    );
}

/// THE RULE'S OTHER HALF, and the one that says the residue is bounded: a spec none of whose
/// operations takes any of its type parameters records the PROVIDER, and that is what the
/// stdlib actually relies on. `Relation provides LogicalStream` is the live case — it is why
/// WI-1076 existed — so it is asserted here against the real stdlib rather than a fixture.
///
/// CONTROL: passes with the ticket backed out (WI-1076 delivered it). It is here because
/// WI-1077's acceptance names it: whatever (c) documents must not have moved the case the
/// predicate was fixed FOR.
#[test]
fn a_spec_taking_none_of_its_parameters_still_records_the_provider() {
    let mut kb = crate::common::load_kb_with("");
    assert!(
        relation_rows(&mut kb, "self_provides", 2).contains(&"Relation | LogicalStream".to_string()),
        "`LogicalStream`'s operations take none of its type parameters, so `Relation` \
         provides it AS ITSELF — the case WI-1076 repaired and (c) must preserve",
    );
}
