//! WI-1102 — an unsatisfiable `requires` at a CONCRETE carrier is a LOAD DIAGNOSTIC
//! naming the sort and the missing provision, not an internal evaluator error.
//!
//! 058 §3.10's use-site discharge: "'provides nothing at all' stops being an accepting
//! state". WI-1098 delivered the other half of that section (derive `Eq` for a lawful
//! composite, so the common case has a provision to find) and narrowed the population
//! without changing the message. Three classes remained, and all three loaded clean and
//! then answered, from inside `List.contains`:
//!
//!   Err(Internal("DeferToRequirement: requirement param `__req_eq` not bound in caller
//!    frame (running `anthill.prelude.List.contains`, requires-chain owner
//!    `anthill.prelude.List.contains`; frame binds [])"))
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Backing out the WI-1102 park in `build_op_scoped_dicts` (its `unprovided_provision`
//! arm) fails the three headline rows here — `a_parametric_field_carrier_is_refused`,
//! `a_witness_only_provision_is_refused_at_the_carrier`, `a_noneq_composite_is_refused`
//! — and the op-scoped arm of `both_spellings_of_one_requirement_agree`. Each reverts to
//! the `Internal` above.
//!
//! Backing out the SORT-half park (`build_dispatching_dict_from_chain`'s `else if`)
//! fails the sort-level arm of `both_spellings_of_one_requirement_agree` here and of
//! `wi855_ambiguous_requirement_test::a_body_that_reads_an_unsuppliable_slot_agrees_on_
//! both_spellings`, and those are the rows that exist to catch it: WI-855 legislates that
//! the two spellings give ONE verdict, and an op-half-only fix splits them.
//!
//! Backing out `carrier_has_provision_row` (i.e. asserting "provides no" from a failed
//! goal instead of looking the row up) fails
//! `a_failing_conditional_provision_is_not_reported_as_a_missing_one` here and the wi855
//! row above. This is what the first cut did, and /code-review found it: a conditional
//! provision whose side condition fails ends `NoMatch` at the top goal exactly as a
//! missing one does.
//!
//! Backing out the BUILTIN gate in `OpSlotParkSite::for_call` fails
//! `control_a_builtin_comparison_at_a_no_instance_carrier_still_loads` here, and outside
//! this file `wi642_rule_body_requires_test::builtin_comparison_op_on_concrete_no_
//! instance_loads` plus every test that loads a stdlib-only KB and reaches
//! `SortedSet.insertSorted` — `fact Ord[T = Int64]` lives in the RUST BINDINGS, so
//! `gt(c, 0)` in that body is a fully-pinned `Ord[Int64]` with no provider. Measured
//! before the gate existed.
//!
//! Backing out the ENCLOSING-OP gate (the same function's `enclosing_op.is_some()`)
//! fails `control_a_rule_body_goal_is_not_refused` here and refuses the stdlib itself:
//! `platform.needs_rebuild`'s `gt(?t_in, ?t_out)` compares two `Timestamp`s and
//! `Ord[Timestamp]` has no provider anywhere.
//!
//! Backing out the READ gate (`op_body_reads_op_requirement_slot`, i.e. refusing every
//! parked entry) fails `control_a_body_that_never_reads_the_slot_still_runs` here and
//! `wi855_ambiguous_requirement_test::other_unresolvable_causes_still_enter_unsupplied`.
//! That gate is WI-822 LEG 2's line — "has an unpinnable chain" and "needs it" are
//! different questions — held one channel over.
//!
//! PASSES EITHER WAY BY DESIGN — controls, not this ticket's evidence:
//! `control_a_derived_provision_still_loads_and_answers` (WI-1098's derivation, which
//! must keep the refusal off every lawful composite) and
//! `control_the_provision_written_on_the_carrier_loads_and_answers` (class (2) with its
//! one repair applied). They are here because the refusal must NOT fire there, which is
//! a claim about this change even though neither test needed it.
//!
//! ── the /code-review follow-ups, each its own back-out ─────────────────────────
//!
//! Backing out the SELF-REPRESENTING gate in `spec_carrier_param_or_sole` fails
//! `a_self_representing_spec_does_not_file_its_element_as_the_carrier`, and only that.
//!
//! Backing out `carrier_has_provision_row`'s use of that same ladder (reverting it to
//! `witness_dispatch_carrier`, which stops at rung 1) fails
//! `a_witness_row_is_found_for_a_carrier_param_less_spec`, and only that.
//!
//! Backing out the row-exists WORDING fails
//! `the_row_exists_sentence_does_not_claim_a_condition_it_never_checked`, and only that.
//!
//! MEASURED one at a time, each over the whole file: 12 pass, 1 fails. The three are
//! independent, which is the claim — a shared ladder that only one reader consults is
//! the defect all three descend from.
//!
//! NOT DRIVEN HERE, and pinned elsewhere rather than duplicated: the FULLY-PINNED gate,
//! whose control is an abstract carrier that must still enter unsupplied — `wi822
//! unbound_requirement_message_names_the_running_frame` and `wi855
//! other_unresolvable_causes_still_enter_unsupplied` are both exactly that program and
//! both still expect the eval-time raise.

use anthill_core::eval::value::Value;

// ── the three measured classes ──────────────────────────────────────────────

/// (1) PARAMETRIC FIELD — WI-1098's documented derivation gap. The classifier resolves a
/// field's type to its BASE sort, so it sees `Pair`, not `Pair[A = Float]`, and derives
/// nothing rather than claim a `Float` lawful.
const PARAMETRIC_FIELD: &str = r#"
namespace wi1102.paramfield
  import anthill.prelude.{Bool, Int64, Float, List, Pair}
  import anthill.prelude.List.{cons, nil, contains}
  import anthill.prelude.Pair.{pair}
  sort Hold
    entity hold(p: Pair[A = Float, B = Int64])
  end
  sort Driver
    operation has(n: Int64) -> Int64 =
      if contains(cons(head: hold(p: pair(fst: 1.0, snd: 2)), tail: nil),
                  hold(p: pair(fst: 1.0, snd: 2)))
      then 1 else 0
  end
end
"#;

/// (2) DISPATCHED `eq`, provision filed under the WITNESS. `eq(pebble(1), pebble(2))`
/// dispatches fine — the provision files under `PebbleEq` (WI-1069: provider and carrier
/// are two questions) — so `Pebble` itself has no row to build a dictionary from.
const WITNESS_PROVISION: &str = r#"
namespace wi1102.witness
  import anthill.prelude.{Bool, Int64, List, PartialEq}
  import anthill.prelude.List.{cons, nil, contains}
  sort Pebble
    entity pebble(n: Int64)
  end
  sort PebbleEq
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end
  sort Driver
    operation has(n: Int64) -> Int64 =
      if contains(cons(head: pebble(n: 1), tail: nil), pebble(n: 2)) then 1 else 0
  end
end
"#;

/// (3) GENUINELY NonEq — a `Float` field, so `requires Eq[T]` is UNSATISFIABLE and no
/// provision line can fix it.
const NON_EQ: &str = r#"
namespace wi1102.noneq
  import anthill.prelude.{Bool, Int64, Float, List}
  import anthill.prelude.List.{cons, nil, contains}
  sort Pt
    entity pt(x: Float)
  end
  sort Driver
    operation has(n: Int64) -> Int64 =
      if contains(cons(head: pt(x: 1.0), tail: nil), pt(x: 1.0)) then 1 else 0
  end
end
"#;

// ── helpers ─────────────────────────────────────────────────────────────────

/// The load errors, or a panic naming the program that was supposed to be refused.
fn refusal(src: &str, what: &str) -> String {
    match crate::common::try_load_kb_with(src) {
        Err(errs) => errs.join("\n"),
        Ok(_) => panic!("{what}: expected a LOAD refusal, but the program loaded clean"),
    }
}

/// Every claim the ticket makes about the message, in one place: it must name the CALL,
/// the CARRIER SORT, and the missing PROVISION — the three things the `Internal` named
/// none of.
fn assert_names_carrier_and_provision(text: &str, callee: &str, carrier: &str, spec: &str) {
    assert!(
        text.contains(callee),
        "the refusal must name the call it is about (`{callee}`); got:\n{text}"
    );
    assert!(
        text.contains(&format!("`{carrier}` provides no `{spec}`")),
        "the refusal must name the CARRIER SORT and the provision it lacks \
         (`{carrier}` / `{spec}`) — that is the whole content the `Internal` lacked; \
         got:\n{text}"
    );
    assert!(
        text.contains(&format!("provides {spec}[T = {carrier}]")),
        "…and must spell the repair as a line the author can paste; got:\n{text}"
    );
}

fn eval_int(src: &str, op: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int, got {other:?}"),
    }
}

// ── AXIS 1: the three classes are refused AT LOAD ───────────────────────────

/// Class (1). The carrier named is `Hold` — the composite whose parametric field the
/// derivation cannot see through — not `Pair` and not `Float`.
#[test]
fn a_parametric_field_carrier_is_refused() {
    let text = refusal(PARAMETRIC_FIELD, "the parametric-field carrier");
    assert_names_carrier_and_provision(
        &text,
        "anthill.prelude.List.contains",
        "wi1102.paramfield.Hold",
        "anthill.prelude.Eq",
    );
}

/// Class (2). The refusal names `Pebble` — the CARRIER — and not `PebbleEq`, which is
/// where the provision actually sits and is exactly the confusion the author must be
/// pointed out of.
#[test]
fn a_witness_only_provision_is_refused_at_the_carrier() {
    let text = refusal(WITNESS_PROVISION, "the witness-only provision");
    assert_names_carrier_and_provision(
        &text,
        "anthill.prelude.List.contains",
        "wi1102.witness.Pebble",
        "anthill.prelude.Eq",
    );
    assert!(
        !text.contains("PebbleEq"),
        "the witness sort is not the carrier and naming it would send the author to \
         the declaration that is already there; got:\n{text}"
    );
}

/// Class (3). Refused for the same reason and with the same sentence — see
/// `UnprovidedProvision`'s doc for why the message stops short of "and cannot": the
/// derived `NonEq[Pt]` that would prove impossibility is asserted by `eq_derive::run`,
/// which stands after this diagnostic is rendered.
#[test]
fn a_noneq_composite_is_refused() {
    let text = refusal(NON_EQ, "the NonEq composite");
    assert_names_carrier_and_provision(
        &text,
        "anthill.prelude.List.contains",
        "wi1102.noneq.Pt",
        "anthill.prelude.Eq",
    );
}

/// THE AGREEMENT, on both spellings of one program — WI-855's rule
/// (`a_body_that_reads_an_unsuppliable_slot_agrees_on_both_spellings`) moved to the load
/// side, where it now belongs. The op-scoped `requires` on the callee and the
/// sort-level one on its parent are the same claim written twice; a fix that parked only
/// the op half would refuse one spelling at load and let the other die at eval.
///
/// The two halves are filled from DIFFERENT channels (`op_dicts` vs the parent-bundle
/// dictionary) and read by different predicates, so this is not one code path exercised
/// twice.
#[test]
fn both_spellings_of_one_requirement_agree() {
    const OP_SCOPED: &str = r#"
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
"#;
    const SORT_LEVEL: &str = r#"
  sort Reader
    sort HT = ?
    requires Desc[T = HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
"#;
    for (which, reader) in [("opscoped", OP_SCOPED), ("sortlevel", SORT_LEVEL)] {
        let ns = format!("wi1102.agree.{which}");
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Mystery
    entity mystery
  end
{reader}
  sort Driver
    operation drive(n: Int64) -> Int64 = Reader.probe(mystery())
  end
end
"#
        );
        let text = refusal(&src, &format!("the {which} spelling"));
        assert_names_carrier_and_provision(
            &text,
            &format!("{ns}.Reader.probe"),
            &format!("{ns}.Mystery"),
            &format!("{ns}.Desc"),
        );
    }
}

// ── AXIS 2: the gates — each is a population the refusal must NOT reach ──────

/// THE READ GATE. `Silent.probe` carries `requires Desc[T = HT]` and answers a constant,
/// so entering it without the slot costs nothing. WI-822 LEG 2 measured this class as 29
/// stdlib bodies; refusing here would take all of them.
///
/// This is the WI-855 fixture verbatim, driven for the opposite verdict: it must still
/// LOAD and still ANSWER 5.
#[test]
fn control_a_body_that_never_reads_the_slot_still_runs() {
    const SRC: &str = r#"
namespace wi1102.silent
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Mystery
    entity mystery
  end
  sort Silent
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = 5
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Silent.probe(mystery())
  end
end
"#;
    assert_eq!(
        eval_int(SRC, "wi1102.silent.Driver.drive"),
        5,
        "a body that never reads the slot must still enter unsupplied and run — the \
         `Desc` chain resolves to no provider at `Mystery`, exactly as in the three \
         refused programs above, and the ONLY difference is that this body ignores it"
    );
}

/// THE BUILTIN GATE. `PartialOrd.gt` is registered as a resolver builtin and resolves
/// STRUCTURALLY; the default body carrying `requires Ord[T]` is never entered, so no
/// `provides` line would change the outcome and its absence is not a defect to report.
/// Same claim, same shape, as `wi642 builtin_comparison_op_on_concrete_no_instance_
/// loads` — restated here on an OPERATION body, so the gate is driven where the
/// rule-body gate cannot cover for it.
///
/// `Blob` and NOT `Int64`, deliberately: these fixtures load the Rust host bindings,
/// where `fact Ord[T = Int64]` lives, so an `Int64` row would be outside the refusal
/// population for a second reason and would pass with the gate removed — a control that
/// measures nothing. `Blob` provides no `Ord` anywhere.
///
/// THE NEIGHBOUR IS THE OTHER HALF. `Desc.describe` is the same call shape at the same
/// carrier with the ONE difference that decides — its spec op is not a builtin — and it
/// IS refused. Without it, "the program loads" could equally mean the fixture never
/// reached the check.
#[test]
fn control_a_builtin_comparison_at_a_no_instance_carrier_still_loads() {
    const BUILTIN: &str = r#"
namespace wi1102.builtincmp
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialOrd.{gt}
  sort Blob
    entity blob(v: Int64)
  end
  sort Driver
    operation later(a: Blob, b: Blob) -> Bool = gt(a, b)
  end
end
"#;
    assert!(
        crate::common::try_load_kb_with(BUILTIN).is_ok(),
        "`PartialOrd.gt` resolves structurally — refusing its unfillable `Ord[Blob]` \
         slot would take `wi642 builtin_comparison_op_on_concrete_no_instance_loads` \
         and the stdlib's own `needs_rebuild` with it"
    );

    // THE NEIGHBOUR: identical but for the spec op, which is not a builtin.
    const NOT_BUILTIN: &str = r#"
namespace wi1102.builtincmp.nb
  import anthill.prelude.{Int64, Bool}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Blob
    entity blob(v: Int64)
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  sort Driver
    operation later(a: Blob) -> Int64 = Reader.probe(a)
  end
end
"#;
    let text = refusal(NOT_BUILTIN, "the non-builtin neighbour");
    assert!(
        text.contains("`wi1102.builtincmp.nb.Blob` provides no `wi1102.builtincmp.nb.Desc`"),
        "the neighbour must be REFUSED — it is what says the fixture above is inside \
         the population and exempted, rather than never reaching the check; got:\n{text}"
    );
}

/// THE ENCLOSING-OP GATE. A rule-body goal reaches eval through the SLD bridge, which
/// resolves real provider dictionaries from the CONCRETE argument values at fire time
/// and suspends when it cannot — so a carrier that provides nothing is the ORDINARY case
/// there. This is stdlib `platform.needs_rebuild`'s shape (`gt` on two `Timestamp`s),
/// on a NON-builtin spec op so it is the rule-body gate under test and not the builtin
/// one.
#[test]
fn control_a_rule_body_goal_is_not_refused() {
    const SRC: &str = r#"
namespace wi1102.rulebody
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialEq.{eq}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Mystery
    entity mystery
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  rule described(?x, ?n) :- eq(Holder.probe(?x), ?n)
end
"#;
    assert!(
        crate::common::try_load_kb_with(SRC).is_ok(),
        "a rule body resolves its dictionary from the concrete query value at fire \
         time; refusing it at load takes the stdlib's own `needs_rebuild` with it"
    );
}

/// A CONDITIONAL provision that fails is NOT "the carrier provides nothing", and the
/// message must not say it is (found by /code-review on the first cut, which said it).
///
/// `Quiet` provides `Desc[T = Box[B = E]]` conditional on `Desc[T = E]`, so `Box` HAS a
/// `Desc` provider; the goal `Desc[Box[B = Mystery]]` fails only because `Mystery` has
/// none. Both cases end `NoMatch` at the top goal, which is exactly why inferring the
/// sentence from the failure was wrong — the row has to be LOOKED UP.
///
/// The program is still refused: the requirement genuinely cannot be supplied and the
/// body reads it. What changes is where the author is sent. Told "declare `provides
/// Desc[…]` on `Box`" they would write a second row for a carrier that already has one.
///
/// FAILS IF `carrier_has_provision_row` IS BACKED OUT — the message reverts to "`Box`
/// provides no `Desc`", which the first assertion here rejects by name.
#[test]
fn a_failing_conditional_provision_is_not_reported_as_a_missing_one() {
    const SRC: &str = r#"
namespace wi1102.cond
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Mystery
    entity mystery
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort Quiet
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Box[B = E]]
    operation describe(b: Box[B = E]) -> Int64 = 5
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Reader.probe(box(inner: mystery()))
  end
end
"#;
    let text = refusal(SRC, "the failing conditional provision");
    assert!(
        !text.contains("`wi1102.cond.Box` provides no `wi1102.cond.Desc`"),
        "`Box` DOES provide `Desc` — conditionally, via `Quiet` — so saying it provides \
         none is false, and the `provides` line it prescribes would be a second row for \
         a carrier that already has one; got:\n{text}"
    );
    assert!(
        text.contains("wi1102.cond.Box")
            && text.contains("does provide")
            && text.contains("conditional"),
        "the refusal must still name `Box` and say the CONDITION is what failed, so the \
         author looks at the type argument; got:\n{text}"
    );

    // THE NEIGHBOUR, one line different: the same program at an argument that DOES
    // provide `Desc`. It must load and answer — the conditional row is real, and this
    // is what says the refusal above is about the argument rather than about `Box`.
    const SATISFIED: &str = r#"
namespace wi1102.cond.ok
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 3
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort Quiet
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Box[B = E]]
    operation describe(b: Box[B = E]) -> Int64 = 5
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Reader.probe(box(inner: leaf()))
  end
end
"#;
    assert_eq!(
        eval_int(SATISFIED, "wi1102.cond.ok.Driver.drive"),
        5,
        "with the condition satisfied the conditional provision resolves and the body \
         runs — so the refusal above is about `Mystery`, not about `Box`"
    );
}

// ── AXIS 3: the positives the refusal must not swallow ───────────────────────

/// CONTROL (WI-1098). A `provides`-less composite whose fields are all lawfully `Eq`
/// gets a DERIVED provision, so the goal resolves and nothing is refused. This is the
/// acceptance clause "the refusal must not fire where a provision was derived", and it
/// is driven to an ANSWER rather than to a clean load — a program that loads and cannot
/// run would satisfy the weaker claim.
#[test]
fn control_a_derived_provision_still_loads_and_answers() {
    const SRC: &str = r#"
namespace wi1102.derived
  import anthill.prelude.{Bool, Int64, List}
  import anthill.prelude.List.{cons, nil, contains}
  sort Colour
    entity red
    entity green
    entity blue
  end
  sort Driver
    operation hasRed(n: Int64) -> Int64 =
      if contains(cons(head: red, tail: cons(head: green, tail: nil)), red) then 1 else 0
    operation hasBlue(n: Int64) -> Int64 =
      if contains(cons(head: red, tail: cons(head: green, tail: nil)), blue) then 1 else 0
  end
end
"#;
    assert_eq!(eval_int(SRC, "wi1102.derived.Driver.hasRed"), 1);
    assert_eq!(
        eval_int(SRC, "wi1102.derived.Driver.hasBlue"),
        0,
        "the negative twin: a refusal-free load that answered TRUE everywhere would \
         pass the positive half alone"
    );
}

/// CONTROL, and the tightest one here: class (2) with its ONE repair applied — the
/// `provides` line moved onto the carrier, which is precisely what the refusal tells the
/// author to write. Everything else is byte-identical to `WITNESS_PROVISION`, so this
/// says the diagnostic's advice is correct and not merely well-formed.
#[test]
fn control_the_provision_written_on_the_carrier_loads_and_answers() {
    const SRC: &str = r#"
namespace wi1102.repaired
  import anthill.prelude.{Bool, Int64, List, PartialEq, Eq}
  import anthill.prelude.List.{cons, nil, contains}
  sort Pebble
    entity pebble(n: Int64)
    provides PartialEq[T = Pebble]
    provides Eq[T = Pebble]
  end
  sort Driver
    operation has(n: Int64) -> Int64 =
      if contains(cons(head: pebble(n: 1), tail: nil), pebble(n: 2)) then 1 else 0
    operation hasIt(n: Int64) -> Int64 =
      if contains(cons(head: pebble(n: 1), tail: nil), pebble(n: 1)) then 1 else 0
  end
end
"#;
    assert_eq!(
        eval_int(SRC, "wi1102.repaired.Driver.hasIt"),
        1,
        "with the provision on the CARRIER the dictionary builds and `contains` answers"
    );
    assert_eq!(eval_int(SRC, "wi1102.repaired.Driver.has"), 0);
}

// ── /code-review follow-ups on the carrier-parameter ladder ─────────────────
//
// Three findings on the shipped WI-1102, all about the SECOND rung of "which type
// parameter holds the carrier" (`spec_carrier_param_or_sole`). Fixed inline rather than
// filed, per the repo's follow-up rule.

/// RUNG 2 MUST NOT FIRE FOR A SELF-REPRESENTING SPEC.
///
/// `spec_carrier_param` answers `None` for two different reasons, and only one of them
/// licenses "the sole type parameter is the carrier". A spec with no receiving surface
/// (`Eq`, `NonEq`, `Monad`) has a sole parameter that IS the carrier. A SELF-REPRESENTING
/// one — an operation receiving on the sort itself, `Container.head(c: Container)` — does
/// not: its parameter is the ELEMENT. Reading it as the carrier is WI-1076's measured
/// defect, which filed seven stdlib provisions at the type VARIABLE `T`; here it would
/// send the author to declare `provides Container[T = Mystery]` on `Mystery`, the
/// element, when the provision belongs on whatever sort IS a container of it.
///
/// Every self-representing spec in the stdlib carries a second type parameter, so this
/// needs a written one-parameter spec to reach — which is also why the shipped code was
/// green: the corpus cannot get here (WI-979's shape).
///
/// CONTROL — FAILS with the `spec_is_self_representing` gate removed from
/// `spec_carrier_param_or_sole`: the refusal then names `Mystery` as the sort that
/// provides no `Container`, which the assertion below rejects by name.
#[test]
fn a_self_representing_spec_does_not_file_its_element_as_the_carrier() {
    const SRC: &str = r#"
namespace wi1102.selfrep
  import anthill.prelude.{Int64}
  sort Container
    sort T = ?
    -- RECEIVES ON THE SORT: self-representing. `T` is the element type.
    operation head(c: Container) -> T
    -- ... and a non-receiving member, so a requirement holder's body can READ the slot.
    operation tag() -> Int64
  end
  sort Mystery
    entity mystery
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Container[T = HT] = Container.tag()
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Reader.probe(mystery())
  end
end
"#;
    let text = match crate::common::try_load_kb_with(SRC) {
        Err(errs) => errs.join("\n"),
        Ok(_) => String::new(),
    };
    assert!(
        !text.contains("`wi1102.selfrep.Mystery` provides no `wi1102.selfrep.Container`"),
        "`Mystery` is `Container`'s ELEMENT, not its carrier — a self-representing spec \
         binds no carrier in its parameters, so no sort can be named here and none must \
         be; got:\n{text}"
    );
    assert!(
        !text.contains("provides Container[T = wi1102.selfrep.Mystery] on"),
        "…and no repair line may prescribe the element as the provider; got:\n{text}"
    );
}

/// THE TWO HALVES OF THE DIAGNOSTIC MUST DECODE THE CARRIER THE SAME WAY.
///
/// `unprovided_provision` picks the carrier off the ladder; `carrier_has_provision_row`
/// then asks whether that sort already has a row, and its answer picks WHICH of the two
/// sentences is rendered. It used to ask through `witness_dispatch_carrier`, which stops
/// at rung 1 — right for its other callers (WI-1076), wrong here, because rung 1 answers
/// `None` for exactly the carrier-param-less family rung 2 exists to serve. Every WITNESS
/// row for such a spec then decoded to the PROVIDER, so `has_a_row` could never be true
/// and a carrier whose provision lives on another sort was told it had none.
///
/// `Lawful` has a sole parameter and no operation receiving on anything, so rung 2 names
/// `T`. `Quiet` provides `Lawful[T = Box[B = E]]` conditionally, so `Box` HAS a row; the
/// goal fails only because `Mystery` has none. This is `a_failing_conditional_provision_
/// is_not_reported_as_a_missing_one` one family over — that fixture's `Desc` has a
/// carrier PARAM (`describe(x: T)`), so it never left rung 1.
///
/// CONTROL — FAILS with `carrier_has_provision_row` reverted to
/// `witness_dispatch_carrier(...).unwrap_or(provider)`: the message becomes "`Box`
/// provides no `Lawful`", rejected by name below.
#[test]
fn a_witness_row_is_found_for_a_carrier_param_less_spec() {
    const SRC: &str = r#"
namespace wi1102.witnessrow
  import anthill.prelude.{Int64}
  sort Lawful
    sort T = ?
    -- Receives on NOTHING (the `NonEq.nonEqRefl` shape): no carrier PARAM, and not
    -- self-representing either — so the sole parameter `T` IS the carrier.
    operation mark() -> Int64
  end
  sort Mystery
    entity mystery
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort Quiet
    sort E = ?
    requires Lawful[T = E]
    fact Lawful[T = Box[B = E]]
    operation mark() -> Int64 = 5
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Lawful[T = HT] = Lawful.mark()
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Reader.probe(box(inner: mystery()))
  end
end
"#;
    let text = refusal(SRC, "the witness row at a carrier-param-less spec");
    assert!(
        !text.contains("`wi1102.witnessrow.Box` provides no `wi1102.witnessrow.Lawful`"),
        "`Box` DOES provide `Lawful` — via the witness `Quiet` — so the sentence that \
         sends the author to write a row on `Box` is the wrong one; got:\n{text}"
    );
    assert!(
        text.contains("wi1102.witnessrow.Box") && text.contains("does provide"),
        "the refusal must still name `Box` and select the row-exists sentence; \
         got:\n{text}"
    );
}

/// THE ROW-EXISTS SENTENCE MUST NOT NAME A MECHANISM THE LOOKUP NEVER CHECKED.
///
/// `carrier_has_provision_row` proves only that SOME row keyed by this base exists —
/// deliberately, per its doc. It used to select a sentence asserting the row is
/// CONDITIONAL and that "the missing provision belongs on that argument's sort, not on
/// `{carrier}`". An UNCONDITIONAL row at a different instantiation makes the lookup true
/// too, and there the ruled-out repair — a second row on the carrier — is the correct
/// one.
///
/// `Box` provides `Desc` at `B = Int64` only, unconditionally; the call needs it at
/// `B = Mystery`.
///
/// CONTROL — FAILS against the shipped wording, which tells this author the gap is on
/// `Mystery`'s sort and explicitly not on `Box`. Both repairs are now named, because
/// which one applies is precisely what this lookup does not know.
#[test]
fn the_row_exists_sentence_does_not_claim_a_condition_it_never_checked() {
    const SRC: &str = r#"
namespace wi1102.uncond
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Mystery
    entity mystery
  end
  sort Box
    sort B = ?
    entity box(inner: B)
    fact Desc[T = Box[B = Int64]]
    operation describe(x: Box[B = Int64]) -> Int64 = 5
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Reader.probe(box(inner: mystery()))
  end
end
"#;
    let text = refusal(SRC, "the unconditional row at another instantiation");
    assert!(
        !text.contains("belongs on that argument's sort, not on"),
        "the lookup proved only that a row EXISTS; `Box`'s row here is unconditional and \
         at another instantiation, so ruling out a second row on `Box` rules out the \
         correct repair; got:\n{text}"
    );
    assert!(
        text.contains("no row of it answers at these bindings"),
        "the sentence must say what was actually established; got:\n{text}"
    );
}
