//! WI-865 — A RECORDED-ABSENT DICTIONARY SLOT CARRIES ITS FAILURE KIND.
//!
//! WI-857 made an unresolvable SPEC-HALF slot carry an empty bundle over the
//! `anthill.reflect.NoProvider` marker, refused at any use. The variant is built for
//! `NoMatch`, `Ambiguous` and `Cyclic` ALIKE — deliberately, so the PLACEMENT rule has
//! no cases to get wrong — but the marker then carried nothing to runtime, so the
//! refusal could only say *"nothing provides that spec at those bindings, or more than
//! one does, or this frame was entered from a host entry point"* and could never say
//! WHICH, nor name the bindings it claimed. That was an ATTRIBUTION REGRESSION against
//! WI-843, which goes to specific trouble to FORWARD a sub-goal tie verbatim rather
//! than restamp it: the same tie was a precise coherence diagnostic at a call's own
//! goal and an anonymous one inside a spec half.
//!
//! WHAT IS MEASURED HERE is ONE program shape under seven provider blocks — 0
//! providers, 1, 2, 1 conditional on itself, and three where the failure is a LEVEL
//! BELOW the slot (one of them on the SAME spec) — so the only thing that varies
//! between the rows is the thing the message is supposed to be keyed on. The one-provider row is the POSITIVE CONTROL: it RUNS,
//! which is what says the `Base.b` read really goes through the spec-half slot in all
//! of them (a fixture whose slot is never read would report nothing whatever the
//! block).
//!
//! CONTROLS — FIVE AXES, FIVE BACK-OUTS, EACH MEASURED (not predicted). One recipe
//! credited with all five would say nothing about which part carries the fix:
//!
//! 1. **The wording** — `marker_refusal` returns the old hedged sentence
//!    unconditionally. MEASURED: 6 fail, `one_provider_still_runs` passes.
//! 2. **The discriminant is READ off the failure** — `unavailable_why_of` returns
//!    `NoProvider` for every outcome. MEASURED: 3 fail (`…tie…`, `…cyclic…`,
//!    `no_two_failing_rows…`); `…no_provider…`, `…host_entry…` and wi869's
//!    `reading_a_sibling_provisions_evidence_is_loud` pass, because none of them
//!    routes through that function.
//! 3. **The WI-869 slot is recorded as its own thing** — `resolve_inner`'s
//!    `NotThisDispatch` placement becomes `NoProvider`. MEASURED: only
//!    `reading_a_sibling_provisions_evidence_is_loud` fails; every test here passes,
//!    since no fixture here has a conditional provision.
//! 4. **The reason names the FAILING level, not the slot** — render each arm against
//!    the slot's spec. MEASURED: exactly the two `…below_the_slot…` tests fail; the
//!    others pass, because in them the failure IS at the slot. That axis was the first
//!    cut's defect, found by /code-review and measured before being fixed.
//! 5. **"Below the slot" is a carried BIT, not a spec comparison** — gate the context
//!    clause on `goal != slot spec` instead of on `AbsenceRecord::Slot::below`.
//!    MEASURED: only `a_failure_below_the_slot_on_the_same_spec…` fails (46 of 47 in
//!    wi865/857/869/1045 pass). That axis was the SECOND cut's defect, same shape one
//!    coordinate over, again found by /code-review and measured before being fixed.
//!    The THIRD cut then had the clause right and the sentence beside it still wrong
//!    — "at the bindings this dictionary was built for" is a claim about the slot's
//!    level — so `below` gates the bindings wording too, and the `Cyclic` arm drops
//!    the clause entirely (a cycle is always `below`, and "look one level down" is
//!    the wrong advice at the one message with no other level). Both halves are
//!    pinned by the `!contains` assertions in the two tests concerned; without them
//!    those tests passed through both defects.
//!
//! `one_provider_still_runs` passes under ALL FIVE, by design — it is the control that
//! the read is live, not evidence for the change.

use anthill_core::eval::value::Value;

/// One program; `{PROVIDERS}` is the only hole every row varies.
///
/// `Holder.via`'s `x` is ABSTRACT (`T`), so `Base.b(x)` cannot dispatch on a value and
/// must read `__req_top` and project slot 0 — the spec half of `Top`'s dictionary,
/// which is exactly the slot `resolve_inner` records an absence into. `WTop provides
/// Base[T = Int64]` is a red herring for the LOAD-time base-level existence check
/// (`check_provider_requires`), which asks only whether some sort named in the
/// provision provides `Base` at all; it is no candidate for the goal the dictionary
/// actually has, `Base[T = Wrap[E = Int64]]`.
const TEMPLATE: &str = r#"
namespace wi865.tie
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Option.{none}

  sort Base
    sort T = ?
    operation b(x: T) -> Int64
  end

  enum Wrap
    import anthill.prelude.{Int64}
    sort E = ?
    entity wrap(v: E)
  end

{PROVIDERS}

  sort Top
    sort T = ?
    requires Base[T = T]
    operation t(x: T) -> Int64
  end

  sort WTop
    sort E = ?
    provides Top[T = Wrap[E = E]]
    provides Base[T = Int64]
    operation b(x: Int64) -> Int64 = 0
    operation t(x: Wrap[E = E]) -> Int64 = 7
  end

  sort Holder
    sort T = ?
    requires Top[T]
    operation via(x: T) -> Int64 = Base.b(x)
  end

  sort Driver
    operation go(n: Int64) -> Int64 = Holder.via(wrap(v: 5))
  end
end
"#;

fn provider(name: &str, answer: i64) -> String {
    format!(
        "  sort {name}\n    sort E = ?\n    provides Base[T = Wrap[E = E]]\n    \
         operation b(x: Wrap[E = E]) -> Int64 = {answer}\n  end\n"
    )
}

fn src_block(block: &str) -> String {
    TEMPLATE.replace("{PROVIDERS}", block)
}

fn src(providers: &[(&str, i64)]) -> String {
    src_block(
        &providers
            .iter()
            .map(|(n, a)| provider(n, *a))
            .collect::<Vec<_>>()
            .join("\n"),
    )
}

/// `Driver.go` on a FRESH interpreter — a trapped call poisons later calls on a shared
/// one — returning the rendered failure.
fn go_err(src: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call("wi865.tie.Driver.go", &[Value::Int(0)]) {
        Err(e) => format!("{e}"),
        Ok(v) => panic!("the spec-half slot pins no provider, so the read must fail; got {v:?}"),
    }
}

// ── the three rows ──────────────────────────────────────────────────────────

/// THE POSITIVE CONTROL. One provider, so the slot IS pinned and the body runs —
/// which is what says the two failing rows below fail at the slot they claim to, and
/// not because the fixture never reads one.
///
/// PASSES EITHER WAY BY DESIGN: nothing here touches the absence channel.
#[test]
fn one_provider_still_runs() {
    let mut interp = crate::common::interp_for(&src(&[("BaseA", 1)]));
    match interp.call("wi865.tie.Driver.go", &[Value::Int(0)]) {
        Ok(Value::Int(1)) => {}
        other => panic!(
            "with a unique provider the spec-half slot is filled and `Base.b` \
             dispatches through it; got {other:?}"
        ),
    }
}

/// THE TICKET'S ACCEPTANCE: two providers inside a spec half report as a TIE, naming
/// both candidates — not as "no provider".
///
/// The candidates are WI-843's own `InstanceTie::candidates`, forwarded from the level
/// that tied rather than restamped, which is the same discipline `resolve_at_goal`
/// applies to a tie at a call's own goal.
///
/// AND IT WITNESSES THE MARKER FAMILY. Since this ticket a marker's name carries the
/// record it was minted from (`anthill.reflect.NoProvider[…]`), so `is_absence_marker`
/// recognizes it by PREFIX. If that prefix test had been left as the old exact-name
/// compare, this marker would not be recognized at all and the call would SILENTLY
/// fall through to the spec's own `Base.b` — no failure to assert on.
#[test]
fn a_spec_half_tie_names_both_tied_candidates() {
    let err = go_err(&src(&[("BaseA", 1), ("BaseB", 2)]));
    assert!(
        err.contains("MORE THAN ONE provider matched `wi865.tie.Base`"),
        "a tie must be reported AS a tie: {err}",
    );
    assert!(
        err.contains("`wi865.tie.BaseA`") && err.contains("`wi865.tie.BaseB`"),
        "…naming the providers that tied — the half WI-843 carries and WI-857 dropped: \
         {err}",
    );
    assert!(
        !err.contains("nothing provides"),
        "and it must NOT also say the opposite — the hedge is what this ticket \
         retires: {err}",
    );
    // §4.5 step 0 keeps a call-site key out of a sub-resolution, so no bracket exists
    // to advertise here (WI-843 drove both spellings to a refusal). Advertising one
    // would print advice that does not load.
    assert!(
        !err.contains("[Base ="),
        "no call-site bracket reaches a dictionary sub-slot, so none may be \
         suggested: {err}",
    );
}

/// The other end of the same axis: NO provider names the SPEC it is missing, which the
/// payload-free marker could not do either — the old sentence said "that spec" and
/// named nothing.
#[test]
fn a_spec_half_with_no_provider_names_the_spec_it_is_missing() {
    let err = go_err(&src(&[]));
    assert!(
        err.contains("nothing provides `wi865.tie.Base`"),
        "a no-match must name the requirement that has none: {err}",
    );
    assert!(
        !err.contains("MORE THAN ONE"),
        "…and must not hedge toward the tie it is not: {err}",
    );
}

/// THE POINT OF THE WHOLE CHANGE, asserted as one claim: the failures are PAIRWISE
/// DISTINGUISHABLE. Before this ticket all three rows produced the identical sentence,
/// so an author reading any of them was told to consider all the causes and given no
/// way to tell which held.
///
/// Asserted on the whole rendered sentences rather than on needles, because that is
/// the claim — not "each contains its own phrase" (the per-row tests say that) but
/// "no two of them are the same message".
#[test]
fn no_two_failing_rows_share_one_message() {
    let none = go_err(&src(&[]));
    let tie = go_err(&src(&[("BaseA", 1), ("BaseB", 2)]));
    let cyclic = go_err(&src_block(SELF_CONDITIONAL));
    assert_ne!(
        none, tie,
        "a tie and a miss are two facts and must read as two",
    );
    assert_ne!(none, cyclic, "so are a cycle and a miss");
    assert_ne!(tie, cyclic, "so are a cycle and a tie");
    // All still key on the shared head every reader of this refusal matches on.
    for text in [&none, &tie, &cyclic] {
        assert!(
            text.contains("pins no provider"),
            "the shared head is load-bearing wording, not a leftover: {text}",
        );
    }
}

/// THE THIRD RESOLVER ARM, driven so no arm of the record ships unmeasured. The
/// single candidate's provision is conditional ON ITSELF, so the search re-enters the
/// goal already on its stack and `resolve` answers `Cyclic` — a THIRD thing the one
/// payload-free marker reported as "nothing provides that spec, or more than one
/// does", which is false in both halves here: exactly one provision matches, and its
/// condition is the problem.
const SELF_CONDITIONAL: &str = "  sort SelfCond\n    sort E = ?\n    \
     provides Base[T = Wrap[E = E]] :- Base[T = Wrap[E = E]]\n    \
     operation b(x: Wrap[E = E]) -> Int64 = 3\n  end\n";

#[test]
fn a_cyclic_spec_half_slot_says_cyclic() {
    let err = go_err(&src_block(SELF_CONDITIONAL));
    assert!(
        err.contains("cyclic") && err.contains("`wi865.tie.Base`"),
        "a cycle must be reported as a cycle, naming the spec it loops on: {err}",
    );
    assert!(
        !err.contains("nothing provides") && !err.contains("MORE THAN ONE"),
        "…and neither of the two facts that are false here: {err}",
    );
    // A cycle is ALWAYS reached through a condition, so it is always `below` — but
    // the thing that failed is this goal RE-ENTERED, and "look one level down" is
    // exactly the wrong advice at the one message where there is no other level.
    assert!(
        !err.contains("while filling"),
        "`cyclic` already says the goal came back to itself; pointing at the level it \
         came from is noise in the clause whose job is to point elsewhere: {err}",
    );
}

// ── the failure is not always AT the slot ───────────────────────────────────

/// A NESTED failure: `Base` has exactly ONE provider, and what fails is that
/// provider's own `requires Mid[…]`, which ties.
///
/// `resolve_inner` returns a PROVIDER-half sub-goal's failure verbatim (`return err`)
/// — deliberately, so the goal a refusal names is the unmet condition — so the `err`
/// arriving at the outer spec-half slot may describe a goal SEVERAL LEVELS DOWN. A
/// reason rendered against the SLOT's spec is then a definite falsehood, and worse
/// than the hedge it replaced: it would say "more than one provider matched `Base` —
/// `MidA`, `MidB`", when neither provides `Base` and retracting either does nothing
/// for it.
///
/// So the reason carries the FAILING LEVEL's own spec — `InstanceTie::spec` for a tie,
/// the failing goal's for a miss or a cycle — exactly as WI-843 forwards a sub-goal
/// tie rather than restamping it. Found by /code-review of this ticket's first cut,
/// which restamped.
///
/// CONTROL (axis 4 in the module header, MEASURED): render each reason against the
/// slot's spec instead of the failure's, and exactly these two tests fail while every
/// other test in this file passes — none of the others has a failure below its slot.
/// `Base`'s only provider, whose OWN `requires Mid[…]` is what the search fails on.
const ONLY_BASE: &str = r#"
  sort Mid
    sort T = ?
    operation m(x: T) -> Int64
  end

  sort OnlyBase
    sort E = ?
    requires Mid[T = Wrap[E = E]]
    provides Base[T = Wrap[E = E]]
    operation b(x: Wrap[E = E]) -> Int64 = Mid.m(x)
  end
"#;

/// …plus two providers of `Mid`, so the nested failure is a TIE rather than a miss.
const MID_PAIR: &str = r#"
  sort MidA
    sort E = ?
    provides Mid[T = Wrap[E = E]]
    operation m(x: Wrap[E = E]) -> Int64 = 1
  end

  sort MidB
    sort E = ?
    provides Mid[T = Wrap[E = E]]
    operation m(x: Wrap[E = E]) -> Int64 = 2
  end
"#;

#[test]
fn a_tie_below_the_slot_names_the_spec_that_actually_tied() {
    let err = go_err(&src_block(&format!("{ONLY_BASE}\n{MID_PAIR}")));
    assert!(
        err.contains("`wi865.tie.Mid`"),
        "the tie is over `Mid`'s providers, so `Mid` is the spec named: {err}",
    );
    assert!(
        err.contains("`wi865.tie.MidA`") && err.contains("`wi865.tie.MidB`"),
        "…with the providers that tied: {err}",
    );
    assert!(
        !err.contains("provider matched `wi865.tie.Base`"),
        "`MidA`/`MidB` do not provide `Base` — saying so is the defect this test \
         exists for: {err}",
    );
    // The slot is still named, as CONTEXT: it is where the absence sits, and a reader
    // needs both coordinates to find the program text.
    assert!(
        err.contains("`wi865.tie.Base`"),
        "…and the slot the absence occupies is still named: {err}",
    );
}

/// The same shape one axis over: ONE provider for `Base`, whose own `requires Mid[…]`
/// has NO provider at all. The pre-WI-865 hedge named no spec and was merely vague;
/// naming the slot's spec here would be affirmatively wrong — `OnlyBase` DOES provide
/// `Base` at these bindings, and it is `Mid` that has no provider.
#[test]
fn a_miss_below_the_slot_names_the_spec_that_is_actually_missing() {
    // `MID_PAIR` omitted: `OnlyBase requires Mid[…]` and nothing provides it.
    let err = go_err(&src_block(ONLY_BASE));
    assert!(
        err.contains("nothing provides `wi865.tie.Mid`"),
        "the missing provision is `Mid`'s, not `Base`'s: {err}",
    );
    assert!(
        !err.contains("nothing provides `wi865.tie.Base`"),
        "`OnlyBase` provides `Base` at these bindings; sending the author to declare \
         one is the defect: {err}",
    );
}

/// …AND THE SPEC IS NOT THE COORDINATE THAT SEPARATES THE TWO LEVELS. `SelfDeep`
/// provides `Base` at the slot's own bindings and requires `Base` at OTHER ones, so
/// the failure is a level below the slot on the SAME SPEC.
///
/// The first repair for the nested case suppressed the "reached while filling …"
/// clause whenever the failing spec equalled the slot's — which reads as "the failure
/// is at this level" and is false exactly here, reproducing the original falsehood:
/// `SelfDeep` DOES provide `Base` at the bindings the dictionary was built for, and
/// what has no provider is `Base[T = Bool]`. The bindings are what tell the two goals
/// apart and the record deliberately does not carry them, so the record carries
/// instead the one bit that answers the question directly — whether the failure was
/// FORWARDED out of a sub-goal (`AbsenceRecord::Slot::below`).
///
/// Found by /code-review of the second cut, with this fixture. CONTROL (axis 5,
/// MEASURED): gate the clause on spec identity instead of on `below` and only this
/// test fails.
const SELF_DEEP: &str = r#"
  sort SelfDeep
    sort E = ?
    requires Base[T = Bool]
    provides Base[T = Wrap[E = E]]
    operation b(x: Wrap[E = E]) -> Int64 = 4
  end
"#;

#[test]
fn a_failure_below_the_slot_on_the_same_spec_is_still_marked_as_below() {
    let err = go_err(&src_block(SELF_DEEP));
    assert!(
        err.contains("while filling"),
        "the failure is a LEVEL DOWN, and only that clause says so — `SelfDeep` does \
         provide `Base` at the slot's own bindings: {err}",
    );
    // THE NEGATIVE HALF, which is what actually pins the defect: `below` must also
    // decide WHOSE BINDINGS the sentence asserts. Saying the missing provision is for
    // "the bindings this dictionary was built for" is false here for the same reason
    // the suppressed clause was — those bindings are `Wrap[E = Int64]`, which
    // `SelfDeep` provides. Found by /code-review of the third cut, where the clause
    // fired but this half of the sentence had not moved.
    assert!(
        !err.contains("the bindings this dictionary was built for"),
        "the failing goal's bindings are a level down, so the sentence must not claim \
         they are this dictionary's: {err}",
    );
}

// ── the host-entry stand-in ─────────────────────────────────────────────────

/// A marker is reachable in a frame slot a SECOND way — eval's host-entry stand-in
/// (`Interpreter::stand_in_requirement`), whose sub-slots carry no evidence because
/// the host supplied no dictionary at all. Nothing is wrong with the PROGRAM there,
/// and the remedy is `call_with_requirements`; the old sentence offered that beside
/// "declare a provider" and let the reader pick.
///
/// Driven by entering `Holder.via` DIRECTLY from the host — the same body, the same
/// slot 0 projection, a different producer of what sits in it. Note the fixture here
/// is the one-provider row, whose `Driver.go` route RUNS (`one_provider_still_runs`):
/// so the failure below is attributable to the entry point and to nothing else.
#[test]
fn a_host_entry_stand_in_slot_blames_the_entry_and_not_the_program() {
    let mut interp = crate::common::interp_for(&src(&[("BaseA", 1)]));
    let err = match interp.call("wi865.tie.Holder.via", &[Value::Int(5)]) {
        Err(e) => format!("{e}"),
        Ok(v) => panic!("a host entry supplies no dictionary, so the read must fail; got {v:?}"),
    };
    assert!(
        err.contains("pins no provider") && err.contains("host entry point"),
        "a stand-in slot must say the FRAME was entered without a dictionary: {err}",
    );
    assert!(
        err.contains("call_with_requirements"),
        "…and name the entry point that supplies one: {err}",
    );
    assert!(
        !err.contains("nothing provides") && !err.contains("MORE THAN ONE"),
        "…and must not send the author to fix a program that is not at fault: {err}",
    );
}
