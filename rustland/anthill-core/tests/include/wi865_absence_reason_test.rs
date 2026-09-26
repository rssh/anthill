//! WI-865 — A SPEC HALF THAT CANNOT BE FILLED IS REPORTED WITH ITS FAILURE KIND.
//!
//! WI-857 made an unresolvable SPEC-HALF slot carry an empty bundle over the
//! `anthill.reflect.NoProvider` marker, refused at any use, and WI-865 made that marker
//! carry WHY — a miss, a tie naming its candidates, a cycle, and whether the failure sat
//! at the slot or a level below it — because a payload-free marker reported all of them
//! with one hedged sentence, an ATTRIBUTION REGRESSION against WI-843, which forwards a
//! sub-goal tie verbatim rather than restamping it.
//!
//! WI-20260925-4ZZKZ MOVED THE REFUSAL TO LOAD. Every program below declares
//! `WTop provides Top[T = Wrap[E = E]]` beside `Top requires Base[T = T]`, and the
//! provider block decides whether `Base[T = Wrap[E]]` holds. It loaded through
//! `check_provider_requires`' base-level fallback (`WTop provides Base` at `Int64`, a red
//! herring, answered "some sort named here provides `Base`"), so the absence reached
//! run time. The check now resolves the goal at `WTop`'s own parameters, and the
//! resolver no longer records a spec half absent — so the SAME distinctions are now the
//! load refusal's (`LoadError::UnsatisfiedProviderRequires::failure`), and this file
//! pins them there: the one program under seven provider blocks, so the only thing that
//! varies between rows is the thing the message is keyed on.
//!
//! CONTROLS:
//!
//! 1. **The move** — restore the base-level fallback in `check_provider_requires`: every
//!    failing row fails on `refusal`'s "loaded clean" (MEASURED: all seven).
//! 2. **The kind rides into the refusal** — render every `RequirementFailure` as
//!    `NoProvider`: the tie, cycle and three below-the-slot rows fail, and
//!    `no_two_failing_rows_share_one_message` with them; the no-provider row passes
//!    (MEASURED: exactly those six).
//! 3. **The failing LEVEL is named, not the slot** — the three `…below…` rows exist for
//!    exactly the falsehood WI-865 measured twice: "more than one provider matched
//!    `Base`" when `MidA`/`MidB` provide `Mid`, and "declare a provider" for a `Base`
//!    that `OnlyBase` / `SelfDeep` DO provide at these bindings.
//!
//! `one_provider_still_runs` passes under all of them, by design — it is the control
//! that the program is otherwise sound and the slot is live.

use anthill_core::eval::value::Value;

/// One program; `{PROVIDERS}` is the only hole every row varies.
///
/// `Holder.via`'s `x` is ABSTRACT (`T`), so `Base.b(x)` cannot dispatch on a value and
/// must read `__req_top` and project slot 0 — the spec half of `Top`'s dictionary. It
/// is what makes the one-provider control LIVE: the slot is read, and it answers `1`.
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

/// The load's refusal of `WTop`'s provision — the one the provider block decides.
fn refusal(src: &str) -> String {
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("`WTop provides Top` cannot hold here, yet this loaded clean"));
    errs.into_iter()
        .find(|e| e.contains("'wi865.tie.WTop' provides 'wi865.tie.Top'"))
        .unwrap_or_else(|| panic!("the refusal must be about `WTop`'s `Top` provision"))
}

// ── the rows ────────────────────────────────────────────────────────────────

/// THE POSITIVE CONTROL. One provider, so the provision holds and the body runs, reading
/// the spec-half slot the failing rows below are refused over.
///
/// PASSES EITHER WAY BY DESIGN.
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

/// Two providers of `Base[T = Wrap[E]]` are a TIE, reported as one and naming both —
/// not as "does not provide", which is false twice over.
#[test]
fn a_spec_half_tie_names_both_tied_candidates() {
    let err = refusal(&src(&[("BaseA", 1), ("BaseB", 2)]));
    assert!(
        err.contains("MORE THAN ONE provider matches `wi865.tie.Base["),
        "a tie must be reported AS a tie: {err}",
    );
    assert!(
        err.contains("`wi865.tie.BaseA`") && err.contains("`wi865.tie.BaseB`"),
        "…naming the providers that tied: {err}",
    );
    assert!(
        !err.contains("does not provide"),
        "…and not also the opposite: {err}",
    );
}

/// No provider names the goal it is missing — at `Wrap[E]`, which is not the carrier, so
/// the sentence must not tell `WTop` to provide `Base`.
#[test]
fn a_spec_half_with_no_provider_names_the_spec_it_is_missing() {
    let err = refusal(&src(&[]));
    assert!(
        err.contains(
            "which requires 'wi865.tie.Base', but nothing provides \
             `wi865.tie.Base[T = wi865.tie.Wrap[E = wi865.tie.WTop.E]]`"
        ),
        "a miss names the goal that has no provider: {err}",
    );
    assert!(!err.contains("MORE THAN ONE"), "…and is no tie: {err}");
}

/// THE POINT, asserted as one claim: the failures are PAIRWISE DISTINGUISHABLE — on the
/// whole sentences, because that is the claim, not "each contains its own phrase".
#[test]
fn no_two_failing_rows_share_one_message() {
    let none = refusal(&src(&[]));
    let tie = refusal(&src(&[("BaseA", 1), ("BaseB", 2)]));
    let cyclic = refusal(&src_block(SELF_CONDITIONAL));
    assert_ne!(none, tie, "a tie and a miss are two facts and must read as two");
    assert_ne!(none, cyclic, "so are a cycle and a miss");
    assert_ne!(tie, cyclic, "so are a cycle and a tie");
}

/// THE CYCLE, driven so no failure kind ships unmeasured. The single candidate's
/// provision is conditional ON ITSELF, so resolving it re-enters the goal — exactly one
/// provision matches, and its condition is the problem.
const SELF_CONDITIONAL: &str = "  sort SelfCond\n    sort E = ?\n    \
     provides Base[T = Wrap[E = E]] :- Base[T = Wrap[E = E]]\n    \
     operation b(x: Wrap[E = E]) -> Int64 = 3\n  end\n";

#[test]
fn a_cyclic_spec_half_says_cyclic() {
    let err = refusal(&src_block(SELF_CONDITIONAL));
    assert!(
        err.contains("cyclic") && err.contains("wi865.tie.Base["),
        "a cycle must be reported as a cycle, naming the goal it loops on: {err}",
    );
    assert!(
        !err.contains("does not provide") && !err.contains("MORE THAN ONE"),
        "…and neither of the two facts that are false here: {err}",
    );
}

// ── the failure is not always AT the requirement ────────────────────────────

/// A NESTED failure: `Base` has exactly ONE provider, and what fails is that provider's
/// own `requires Mid[…]`. The resolver forwards the failure verbatim, so it describes a
/// goal a level below the requirement — and naming the REQUIREMENT's spec with the
/// failure's facts ("more than one provider matched `Base` — `MidA`, `MidB`") is the
/// falsehood WI-865 found and fixed at the marker. It is kept fixed at the refusal.
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
fn a_tie_below_the_requirement_names_the_spec_that_actually_tied() {
    let err = refusal(&src_block(&format!("{ONLY_BASE}\n{MID_PAIR}")));
    assert!(
        err.contains("`wi865.tie.Mid[") && err.contains("beneath it"),
        "the tie is over `Mid`'s providers, a level below: {err}",
    );
    assert!(
        err.contains("wi865.tie.MidA") && err.contains("wi865.tie.MidB"),
        "…with the providers that tied: {err}",
    );
    assert!(
        !err.contains("MORE THAN ONE provider matches `wi865.tie.Base"),
        "`MidA`/`MidB` do not provide `Base`: {err}",
    );
}

/// The same shape one axis over: `OnlyBase`'s own `requires Mid[…]` has NO provider.
#[test]
fn a_miss_below_the_requirement_names_the_spec_that_is_actually_missing() {
    let err = refusal(&src_block(ONLY_BASE));
    assert!(
        err.contains("`wi865.tie.Mid[") && err.contains("no impl provides wi865.tie.Mid"),
        "the missing provision is `Mid`'s, not `Base`'s: {err}",
    );
    assert!(
        !err.contains("does not provide 'wi865.tie.Base'"),
        "`OnlyBase` provides `Base` at these bindings: {err}",
    );
}

/// …AND THE SPEC IS NOT WHAT SEPARATES THE TWO LEVELS. `SelfDeep` provides `Base` at the
/// requirement's own bindings and requires `Base` at OTHER ones, so the failure is a
/// level below on the SAME spec; it is the failing GOAL, bindings included, that says so.
const SELF_DEEP: &str = r#"
  sort SelfDeep
    sort E = ?
    requires Base[T = Bool]
    provides Base[T = Wrap[E = E]]
    operation b(x: Wrap[E = E]) -> Int64 = 4
  end
"#;

#[test]
fn a_failure_below_on_the_same_spec_names_the_goal_that_failed() {
    let err = refusal(&src_block(SELF_DEEP));
    assert!(
        err.contains("`wi865.tie.Base[T = anthill.prelude.Bool]` beneath it"),
        "the failing goal is `Base[T = Bool]`, a level down: {err}",
    );
    assert!(
        !err.contains("does not provide 'wi865.tie.Base'"),
        "`SelfDeep` does provide `Base` at the requirement's own bindings: {err}",
    );
}

// ── the host-entry stand-in ─────────────────────────────────────────────────

/// A marker is still reachable in a frame slot at RUN time — eval's host-entry stand-in
/// (`Interpreter::stand_in_requirement`), whose sub-slots carry no evidence because the
/// host supplied no dictionary at all. Nothing is wrong with the PROGRAM there, and the
/// remedy is `call_with_requirements`; the old sentence offered that beside "declare a
/// provider" and let the reader pick.
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
