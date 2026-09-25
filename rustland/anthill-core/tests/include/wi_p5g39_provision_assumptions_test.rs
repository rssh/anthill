//! WI-20260925-P5G39 — A PROVISION'S CONTRACT IS CHECKED UNDER THE PROVISION'S OWN
//! CONDITIONS, WITH THE CARRIER'S PARAMETERS RIGID (058 §3.10: a condition is discharged as an
//! ASSUMPTION, `Candidate::Assumption`).
//!
//! `check_provider_requires` asks, for `C provides Spec :- G…`, whether each of `Spec`'s
//! own `requires` holds at `C`. It used to ask with NO context — `C`'s parameters open and
//! none of `G…` in scope — which for a conditional provision is false by construction
//! ("is every `Pair` an `Eq`?"), and a second, hand-rolled route (`self_provides_required`
//! + `conditions_entail`) then re-derived the entailment beside the resolver. It is now
//! one question to the resolver: the clause's conditions and the sort-level chain as
//! ASSUMPTIONS, closed under the `requires` chain, and a σ whose `param_rigids` makes the
//! carrier's parameters skolems.
//!
//! MEASURED on the bare stdlib (a probe at the spec-half `Unavailable` push in
//! `resolve_inner`): 10 unresolved spec-half slots before, all from this check; 0 after.
//!
//! ## What fails when the change is backed out
//!
//! * `an_open_element_does_not_match_a_structured_provider_head` — the old check ACCEPTED
//!   the too-weak `WeakOrd[Cell]` (it reported only the unrelated `Eq` refusal).
//! * `a_requirement_reaching_the_carrier_nested_holds_under_the_conditions` — the old
//!   check REFUSED a correct program ("does not provide `Small`").
//! * `an_unconditioned_clause_is_checked_beside_a_conditioned_one` — found by
//!   `/code-review` in the first cut of this ticket, which checked such a provision only
//!   under the conditioned clause and LOADED it (the old check refused it, by accident of
//!   its empty scope).
//!
//! * `a_provision_certified_by_a_generic_witness_elsewhere_is_refused` — the old check
//!   ACCEPTED `Hi[Cell]` because `Cell` provides `Lo` at `A = Int64` only, and its
//!   self-provision arm asked no more than "is there a `Lo` provision of `Cell`".
//! * `a_dispatch_holds_through_an_unconditioned_clause_beside_duplicate_conditioned_ones`
//!   — the old DISPATCH dropped the outright clause and refused the call.
//!
//! * `a_ground_requirement_is_assumed_and_its_use_is_refused` — the old check REFUSED
//!   `provides Hi[T = Cell] :- Lo[T = Cell]`, whose requirement is its own condition.
//!
//! The rest pin a second `/code-review` pass over this ticket's own first cut, and fail
//! there rather than on the old check: `the_refusal_names_the_written_condition_…` (the
//! first cut named the innermost goal; the old check named the written one, as now),
//! `a_written_condition_fact_with_no_spec_head_is_reported` (the first cut panicked; the
//! old check skipped it and loaded), `a_derived_floor_is_told_to_write_its_own_clause`
//! (wording).
//!
//! `a_named_slot_on_a_parametric_carrier_resolves_through_the_carrier_at_its_own_params`
//! loaded before this ticket (through the hand-rolled route) and fails if the carrier's
//! self-application (`goal_at_own_params`) is backed out of the new one. The two
//! `CONTROL` rows pass either way BY DESIGN: they pin verdicts the rewrite must not move.

/// A local ordering tower whose `Eq` is conditioned on `eq_cond`, beside a carrier that
/// provides the spec `Lawful` at a STRUCTURED head only.
fn cell_tower(extra: &str, eq_cond: &str, ord_cond: &str) -> String {
    format!(
        "\nnamespace p5g39.cell\n  \
         import anthill.prelude.{{Bool, Int64, PartialEq, Eq, PartialOrd, Ord, WeakOrd}}\n\
  sort Lawful\n    sort T = ?\n  end\n{extra}\
  enum Cell\n    sort E = ?\n    entity cell(v: E)\n    \
    provides PartialEq[Cell] :- PartialEq[E] where\n      \
      operation eq(a: Cell, b: Cell) -> Bool =\n        \
        match a\n          case cell(x) ->\n            match b\n              case cell(y) -> PartialEq.eq(x, y)\n    \
    end\n    \
    provides Eq[Cell] :- {eq_cond}\n    \
    provides PartialOrd[Cell] :- PartialOrd[E]\n    \
    provides WeakOrd[Cell] :- WeakOrd[E] where\n      \
      operation compare(a: Cell, b: Cell) -> Int64 =\n        \
        match a\n          case cell(x) ->\n            match b\n              case cell(y) -> WeakOrd.compare(x, y)\n    \
    end\n    \
    provides Ord[Cell] :- {ord_cond}\n  end\nend\n"
    )
}

const WRAP: &str = "  enum Wrap\n    sort A = ?\n    entity wrap(a: A)\n    \
    provides Lawful[T = Wrap[A = A]]\n  end\n";

use anthill_core::eval::Value;

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// AN OPEN ELEMENT IS NOT A STRUCTURED TYPE. `WeakOrd[Cell] :- WeakOrd[E]` needs
/// `Eq[Cell]`, whose own condition is `Lawful[E]` — and `WeakOrd[E]` does not entail
/// `Lawful[E]`, so the provision over-claims. The old check resolved `Eq[Cell]` with no
/// σ, and the sub-goal `Lawful[T = Cell.E]` HEAD-MATCHED `Wrap`'s `Lawful[T = Wrap[A =
/// A]]` — the open `E` read as a wildcard that "is" `Wrap[A]` — so `Eq[Cell]` resolved,
/// the provision was accepted, and a `WeakOrd` was claimed where the `Eq` it requires
/// does not hold. The stdlib's own instance of the same mismatch was `Eq[T = Pair.A]`
/// choosing `SortedSet`.
///
/// DISCRIMINATES: backed out, the only error is the `Eq`→`PartialEq` one below and this
/// row's assertion fails.
#[test]
fn an_open_element_does_not_match_a_structured_provider_head() {
    let errs = load_errs(&cell_tower(WRAP, "Lawful[E]", "Ord[E]"));
    assert!(
        errs.iter().any(|e| e.contains(
            "'p5g39.cell.Cell' provides 'anthill.prelude.WeakOrd', which requires \
             'anthill.prelude.Eq'"
        ) && e.contains("DOES provide")
            && e.contains("`p5g39.cell.Lawful[T = p5g39.cell.Cell.E]`")),
        "a rigid `Cell.E` must not match `Wrap`'s structured head, so `WeakOrd[Cell]`'s \
         unentailed `Lawful` condition must be named; got {errs:?}",
    );
    // The fixture's OTHER defect, reported either way — `Eq[Cell] :- Lawful[E]` cannot
    // certify the `PartialEq[Cell]` that `Eq` requires. Asserted so the row above is read
    // as an ADDITIONAL refusal, not a replacement.
    assert!(
        errs.iter().any(|e| e.contains(
            "'p5g39.cell.Cell' provides 'anthill.prelude.Eq', which requires \
             'anthill.prelude.PartialEq'"
        )),
        "got {errs:?}",
    );
}

/// THE TICKET'S CONTROL: conditions that really are too weak stay refused. `Ord[Cell] :-
/// PartialOrd[E]` is claimed beside `WeakOrd[Cell] :- WeakOrd[E]`, and `Ord` requires
/// `WeakOrd`, which a `PartialOrd` element does not give. `:- Ord[E]` is the same carrier
/// with a condition that does, and loads.
///
/// PASSES EITHER WAY by design — the old hand-rolled route refused the same shape with
/// the same words.
#[test]
fn control_a_too_weak_condition_is_still_refused() {
    let errs = load_errs(&cell_tower("", "Eq[E]", "PartialOrd[E]"));
    assert!(
        errs.iter().any(|e| e.contains(
            "'p5g39.cell.Cell' provides 'anthill.prelude.Ord', which requires \
             'anthill.prelude.WeakOrd'"
        ) && e.contains("`anthill.prelude.WeakOrd[T = p5g39.cell.Cell.E]`")),
        "`PartialOrd[E]` does not entail the `WeakOrd[E]` the carrier's own `WeakOrd` \
         provision is conditioned on; got {errs:?}",
    );
    if let Err(errs) = crate::common::try_load_kb_with(&cell_tower("", "Eq[E]", "Ord[E]")) {
        panic!("`Ord[E]` entails `WeakOrd[E]`, so this must load; got {errs:?}");
    }
}

/// A requirement that reaches the carrier NESTED — `Big requires Small[T = Seq[E = T]]`,
/// so `Box provides Big` owes `Small[Seq[Box]]` — holds when `Seq`'s condition leads back
/// to `Box`'s own, and `Box`'s own is among `Big`'s conditions.
fn nested(big_cond: &str) -> String {
    format!(
        "\nnamespace p5g39.nested\n\
  sort Small\n    sort T = ?\n  end\n\
  sort Cond\n    sort T = ?\n  end\n\
  sort Big\n    sort T = ?\n    requires Small[T = Seq[E = T]]\n  end\n\
  enum Seq\n    sort E = ?\n    entity seq(e: E)\n    provides Small[T = Seq] :- Small[E]\n  end\n\
  enum Box\n    sort B = ?\n    entity bx(b: B)\n    \
    provides Small[T = Box] :- Cond[B]\n    \
    provides Big[T = Box]{big_cond}\n  end\nend\n"
    )
}

/// DISCRIMINATES: the old check resolved `Small[Seq[Box]]` with an empty scope, so
/// `Box`'s `Cond[B]` could not hold, and its fallback accepted only a requirement whose
/// every binding IS the carrier — `Seq[E = Box]` is not. It refused this program with
/// "'Box' does not provide 'Small'", which is false.
#[test]
fn a_requirement_reaching_the_carrier_nested_holds_under_the_conditions() {
    if let Err(errs) = crate::common::try_load_kb_with(&nested(" :- Cond[B]")) {
        panic!(
            "`Big[Box]`'s condition `Cond[B]` is exactly `Small[Box]`'s, so \
             `Small[Seq[Box]]` holds wherever `Big[Box]` does; got {errs:?}"
        );
    }
}

/// CONTROL for the row above: the same program with `Big[Box]` UNCONDITIONED is refused,
/// so that row's clean load is the check examining the nested requirement and finding it
/// entailed — not the check skipping it. Passes either way by design.
///
/// Only the VERDICT is pinned. The refusal's tail — "'Box' does not provide 'Small'" —
/// predates this ticket and is imprecise here: `Box` does provide `Small`, and what fails
/// is its condition `Cond[B]`, reached beneath `Seq`. `ProvisionConditionsTooWeak` names
/// such a condition only under the carrier's OWN provision of the required spec.
#[test]
fn control_the_nested_requirement_is_refused_without_the_condition() {
    let errs = load_errs(&nested(""));
    assert!(
        errs.iter().any(|e| e.contains(
            "'p5g39.nested.Box' provides 'p5g39.nested.Big', which requires \
             'p5g39.nested.Small'"
        )),
        "an unconditioned `Big[Box]` claims `Small[Seq[Box]]` where `Cond[B]` may not \
         hold; got {errs:?}",
    );
}

/// A CLAUSE WITH NO CONDITION MAKES THE PROVISION HOLD OUTRIGHT, beside any conditioned
/// clause of the same spec — the dispatch reads the pair so (`alternative_condition_goals`)
/// — so the contract is also checked assuming nothing. Checked only under `Cond[B]`, this
/// program loaded: adding a conditioned clause beside the refused unconditioned one turned
/// the refusal into a load.
#[test]
fn an_unconditioned_clause_is_checked_beside_a_conditioned_one() {
    let errs = load_errs(&nested("\n    provides Big[T = Box] :- Cond[B]"));
    assert!(
        errs.iter().any(|e| e.contains(
            "'p5g39.nested.Box' provides 'p5g39.nested.Big', which requires \
             'p5g39.nested.Small'"
        )),
        "the unconditioned `Big[Box]` still claims `Small[Seq[Box]]` where `Cond[B]` may \
         not hold; got {errs:?}",
    );
}

/// A NAMED SLOT IS A PARAMETER, and the check reads the carrier at its own. `Tagged`
/// declares `requires O: WeakOrd[T]` and gets derived `PartialEq` / `Eq` provisions whose
/// heads spell it BARE (`PartialEq[T = Tagged]`). Resolved with a σ at the bare spelling,
/// the provision match records no `O`, and `O` reads as a head that forgot `O = O` —
/// refused, so this program did not load (MEASURED, before `goal_at_own_params`). Read at
/// `Tagged[T = Tagged.T, O = Tagged.O]`, the slot's sub-goal is answered by the sort-level
/// assumption.
///
/// Backed out (the self-application), this row fails; it loaded before the ticket too,
/// through the deleted route.
#[test]
fn a_named_slot_on_a_parametric_carrier_resolves_through_the_carrier_at_its_own_params() {
    let src = "\nnamespace p5g39.tagged\n  \
         import anthill.prelude.{WeakOrd}\n  \
         enum Tagged\n    sort T = ?\n    requires O: WeakOrd[T]\n    \
         entity tagged(v: T)\n  end\nend\n";
    let kb = crate::common::try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!(
            "the derived `Eq[Tagged]` holds under `Tagged`'s own `O: WeakOrd[T]`; \
             got {errs:?}"
        )
    });
    // The clean load is evidence only if there was something to check: the derived rows
    // whose `PartialEq` requirement reads the named slot must exist.
    let tagged = kb
        .try_resolve_symbol("p5g39.tagged.Tagged")
        .expect("Tagged must exist");
    for spec in ["anthill.prelude.Eq", "anthill.prelude.PartialEq"] {
        let spec_sym = kb.try_resolve_symbol(spec).expect("the spec must exist");
        assert!(
            kb.provides_clause_count(tagged, spec_sym) >= 1,
            "`Tagged` must provide `{spec}` (derived), or this row checks nothing",
        );
    }
}

/// Specs with no members, so a fixture exercises the provision check and nothing else.
const SPECS: &str = "  sort Lawful\n    sort T = ?\n  end\n  \
    sort Lo\n    sort T = ?\n  end\n  \
    sort Hi\n    sort T = ?\n    requires Lo[T = T]\n  end\n";

/// A GROUND REQUIREMENT IS AN ASSUMPTION TOO — of the provision's own, and of the
/// carrier's. `provides Hi[T = Cell] :- Lo[T = Cell]` claims `Hi` exactly where
/// `Lo[Cell]` holds, and `Hi requires Lo[T = T]` is then discharged by that condition.
/// DISCRIMINATES against the old check, which refused it ("does not provide `Lo`").
///
/// `sort Cell requires Lo[T = Cell]` beside an unconditioned `provides Hi[T = Cell]` is
/// the same claim, because a sort-level `requires` conditions every provision of the
/// carrier. A second /code-review pass read it as circular; refusing ground assumptions
/// refused the explicit form above as well, and every sort with an unprovided ground
/// `requires` through its derived `Eq` (MEASURED — the `wi1112` fixtures). It is VACUOUS
/// rather than unsound, and the row pins where it is caught: a USE of the provision is
/// refused at the call, because nothing supplies `Lo[Cell]`.
#[test]
fn a_ground_requirement_is_assumed_and_its_use_is_refused() {
    let conditioned = format!(
        "\nnamespace p5g39.cond\n{SPECS}  enum Cell\n    sort A = ?\n    \
         entity cell(a: A)\n    provides Hi[T = Cell] :- Lo[T = Cell]\n  end\nend\n"
    );
    if let Err(errs) = crate::common::try_load_kb_with(&conditioned) {
        panic!("`Hi[Cell]` holds where its condition `Lo[Cell]` does; got {errs:?}");
    }
    let sort_level = |use_it: &str| {
        format!(
            "\nnamespace p5g39.self\n  import anthill.prelude.{{Int64}}\n{SPECS}  \
             sort Show\n    sort T = ?\n    requires Hi[T = T]\n    \
             operation show(x: T) -> Int64\n  end\n  \
             enum Cell\n    sort A = ?\n    entity cell(a: A)\n    \
             requires Lo[T = Cell]\n    provides Hi[T = Cell]\n    provides Show[T = Cell]\n    \
             operation show(x: Cell) -> Int64 = 1\n  end\n  \
             sort Caller\n    sort T = ?\n    requires Show[T = T]\n    \
             operation useIt(x: T) -> Int64 = Show.show(x)\n  end\n{use_it}end\n"
        )
    };
    if let Err(errs) = crate::common::try_load_kb_with(&sort_level("")) {
        panic!("an unused vacuous provision is not refused at its declaration; got {errs:?}");
    }
    let errs = load_errs(&sort_level(
        "  operation go() -> Int64 = Caller.useIt(cell(a: 1))\n",
    ));
    assert!(
        errs.iter().any(|e| e.contains("cannot be supplied for call to `p5g39.self.Caller.useIt`")
            && e.contains("no impl provides p5g39.self.Lo")),
        "the USE is refused, naming the requirement nothing supplies; got {errs:?}",
    );
}

/// THE CARRIER THAT FAILED IS THE ONE THE RESOLVER CHOSE. `Cell` provides `Lo` only at
/// `A = Int64`, so `Lo[Cell]` at `Cell`'s own parameters is answered by the generic
/// witness `Gen`, whose condition fails. That is not `Cell` providing `Lo` under too weak
/// a condition — `Cell`'s row does not apply at all — so the refusal must not say it
/// "DOES provide" it and send the author to a `provides Lo[…] :- …` clause that is
/// `Gen`'s.
///
/// DISCRIMINATES against the old check too, which ACCEPTED this: its self-provision arm
/// asked only whether `Cell` had SOME `Lo` provision, and claimed `Hi` for every `Cell`.
#[test]
fn a_provision_certified_by_a_generic_witness_elsewhere_is_refused() {
    let src = format!(
        "\nnamespace p5g39.gen\n  import anthill.prelude.{{Int64}}\n{SPECS}  \
         sort Gen\n    sort X = ?\n    provides Lo[T = X] :- Lawful[X]\n  end\n  \
         enum Cell\n    sort A = ?\n    entity cell(a: A)\n    \
         provides Lo[T = Cell[A = Int64]]\n    provides Hi[T = Cell]\n  end\nend\n"
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains(
            "'p5g39.gen.Cell' provides 'p5g39.gen.Hi', which requires 'p5g39.gen.Lo'"
        )),
        "`Hi[Cell]` claims `Lo` at every `A`; got {errs:?}",
    );
    assert!(
        !errs.iter().any(|e| e.contains("DOES provide")),
        "the failed condition is `Gen`'s, not a condition of `Cell`'s; got {errs:?}",
    );
}

/// THE REFUSAL NAMES THE CONDITION AS WRITTEN. `Cell`'s `Lo` is conditioned on
/// `Lawful[T = Seq[E = A]]`, which holds only through `Seq`'s own `Lawful[E]`. The
/// resolver's innermost failure is `Lawful[T = Cell.A]`, which `Cell` never wrote; the
/// first cut of this ticket named that one.
#[test]
fn the_refusal_names_the_written_condition_not_the_innermost_goal() {
    let src = format!(
        "\nnamespace p5g39.deep\n{SPECS}  \
         enum Seq\n    sort E = ?\n    entity seq(e: E)\n    \
         provides Lawful[T = Seq] :- Lawful[E]\n  end\n  \
         enum Cell\n    sort A = ?\n    entity cell(a: A)\n    \
         provides Lo[T = Cell] :- Lawful[T = Seq[E = A]]\n    provides Hi[T = Cell]\n  end\nend\n"
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("DOES provide")
            && e.contains("`p5g39.deep.Lawful[T = p5g39.deep.Seq[E = p5g39.deep.Cell.A]]`")),
        "the refusal must name `Cell`'s own condition; got {errs:?}",
    );
}

/// A `ProvidesConditionInfo` fact can be WRITTEN, and its condition need not be a spec.
/// The loader refuses that at a `provides … :-` clause, but the decoder of the written
/// fact checks only the `provided` head — the first cut of this ticket reached an
/// `unreachable!` on it and crashed the load.
#[test]
fn a_written_condition_fact_with_no_spec_head_is_reported() {
    let src = format!(
        "\nnamespace p5g39.fact\n  import anthill.reflect.{{ProvidesConditionInfo}}\n{SPECS}  \
         enum Box\n    sort B = ?\n    entity bx(b: B)\n    \
         provides Lo[T = Box]\n    provides Hi[T = Box]\n  end\n  \
         fact ProvidesConditionInfo(sort_ref: Box, provided: Hi, condition: 42, clause: 7)\nend\n"
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("has no readable spec head")),
        "the unreadable condition must be reported, not crash or be skipped; got {errs:?}",
    );
}

/// A DERIVED FLOOR IS TOLD TO WRITE ITS OWN CLAUSE. `provides Ord[Foo]` is unconditional,
/// so the `WeakOrd[Foo]` derived from it is too, and it requires the `Eq[Foo]` that holds
/// only under `Eq[A]`. Conditioning `provides Ord` — what the first cut advised — makes it
/// derive nothing, and the author is then refused for the missing floor instead.
#[test]
fn a_derived_floor_is_told_to_write_its_own_clause() {
    let src = "\nnamespace p5g39.derived\n  \
         import anthill.prelude.{Int64, Bool, PartialEq, Eq, PartialOrd, Ord, WeakOrd}\n  \
         enum Foo\n    sort A = ?\n    entity foo(a: A)\n    \
         provides Eq[Foo] :- Eq[A]\n    provides Ord[Foo] where\n      \
         operation compare(x: Foo, y: Foo) -> Int64 = 0\n    end\n  end\nend\n";
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains(
            "'p5g39.derived.Foo' provides 'anthill.prelude.WeakOrd', which requires \
             'anthill.prelude.Eq'"
        ) && e.contains("DERIVED, unconditionally")
            && e.contains("write `provides anthill.prelude.WeakOrd[…] :- …`")),
        "the refusal must say the floor is derived and to write its own clause; \
         got {errs:?}",
    );
}

/// THE DISPATCH READS THE SAME CLAUSES THE CHECK DOES. `provides Big[T = Box]` beside two
/// clauses conditioned on the SAME `Cond[B]` holds outright. The dispatch used to ask
/// `conditioned groups < clause count` — and two identical conditioned clauses are one
/// entry in the count and two groups — so it dropped the outright clause, demanded
/// `Cond[Int64]`, and refused this call (MEASURED). It now asks the clause record, as the
/// check does.
#[test]
fn a_dispatch_holds_through_an_unconditioned_clause_beside_duplicate_conditioned_ones() {
    let src = "\nnamespace p5g39.alt\n  import anthill.prelude.{Int64}\n  \
         sort Cond\n    sort T = ?\n  end\n  \
         sort Big\n    sort T = ?\n    operation big(x: T) -> Int64\n  end\n  \
         enum Box\n    sort B = ?\n    entity bx(b: B)\n    \
         provides Big[T = Box]\n    provides Big[T = Box] :- Cond[B]\n    \
         provides Big[T = Box] :- Cond[B]\n    \
         operation big(x: Box) -> Int64 = 7\n  end\n  \
         sort Caller\n    sort T = ?\n    requires Big[T = T]\n    \
         operation useIt(x: T) -> Int64 = Big.big(x)\n  end\n  \
         operation go() -> Int64 = Caller.useIt(bx(b: 1))\nend\n";
    let mut interp = crate::common::interp_for(src);
    match interp.call("p5g39.alt.go", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 7, "`Big[Box]` holds outright and dispatches"),
        other => panic!("the call must dispatch through the outright clause; got {other:?}"),
    }
}
