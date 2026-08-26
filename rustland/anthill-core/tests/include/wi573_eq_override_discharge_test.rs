//! WI-573 → WI-755 (WI-502 consumers): a guarded-effect guard whose predicate is
//! the spec op `eq`/`neq` is decided by the carrier's OWN equality — dispatched
//! where it can be, suspended where it cannot — never by a structural comparison
//! the override contradicts.
//!
//! WI-067/WI-592 discharge an `eq`-guard (`{ Boom :- eq(c, Red) }`) by refuting it
//! through the resolver. While `eq` was the purely STRUCTURAL `BuiltinTag::Eq`,
//! that was sound only for a NATIVE-Eq carrier (`provides Eq`, no override), whose
//! equality structural equality IS: refuting `eq(Green, Red)` structurally
//! (Green ≠ Red) and DROPPING the effect is unsound on a carrier whose own `eq`
//! would hold. WI-573 therefore sat a PRE-GATE in the typer that suspended any
//! `eq`-family conjunct whose operands could reach an overriding carrier — the
//! sound floor (its option (b)), keeping the effect without ever consulting the
//! override.
//!
//! WI-616 made `eq`/`neq` SEMANTIC (`BuiltinTag::SemEq`/`SemNeq` →
//! `resolve.rs::sem_eq_values`), which is exactly the discipline the pre-gate was
//! waiting for — and the pre-gate then SHADOWED it, short-circuiting before
//! `refute_guard` → `prove_from_gamma` → resolver. **WI-755 retired the gate for
//! everything the resolver can see** (WI-573's deferred option (a)), so those rows
//! now measure the RESOLVER:
//!
//!   * head-carrier override + deep-ground operands ⇒ DISPATCH `<carrier>.eq`;
//!   * BURIED override (an overriding carrier reachable inside the operand) ⇒
//!     Delay — the nested rows below;
//!   * non-ground operand ⇒ Delay;
//!   * no override anywhere ⇒ the structural verdict, unchanged since WI-592.
//!
//! Every Delay reaches `prove_from_gamma` under `definite_only`, which yields no
//! solution ⇒ unproved ⇒ unrefuted ⇒ the effect is KEPT. So WI-573's floor is
//! intact; it is now the resolver's, and the cases the gate could only suspend are
//! decided.
//!
//! **EXCEPT ONE**, which WI-755 kept a narrowed gate for and **WI-1125 removed
//! outright**: the resolver's dispatch index keys `PartialEq.eq` suppliers only, so a
//! carrier supplying a `neq` and no `eq` was invisible to it and was decided
//! STRUCTURALLY, against that very override. WI-755 held the `neq`-only half as
//! `guard_conjunct_reaches_undispatchable_neq`; WI-1125 made such a carrier a LOAD
//! ERROR instead (`neq` is derived — `neq <=> not(eq)`, §8.3 — so it is not an
//! override point at all) and deleted the gate. Where an `eq` exists it always was
//! the authority, and still is: the resolver's dispatch of that `eq` IS the carrier's
//! own equality. See the section below and `wi1125_neq_not_an_override_test`.
//!
//! WHICH ROWS MEASURE WI-755. Restore WI-573's BLANKET gate — block whenever a
//! reachable carrier supplies an own `eq` OR an own `neq`, with no index check;
//! that is the retired `guard_conjunct_overrides_structural_eq`, whose ~140 lines
//! of helpers went with it and are recoverable from this ticket's commit. WI-755
//! MEASURED that against this file's then-12 rows and
//! `wi756_proof_path_eq_override_test`'s 26 and found THREE failures; TWO of them
//! survive here, and each names a distinct thing WI-755 buys —
//!
//!   * `custom_eq_override_dispatches_and_drops` — the override refutes and the old
//!     gate suspends instead, so `Boom` is kept and the program stops loading;
//!   * `wi756…::custom_eq_rule_body_refutation_rejects_too` — the same gate on the
//!     precondition polarity.
//!
//! The THIRD was `carrier_supplying_both_members_dispatches_its_eq`, the one place
//! the blanket and narrowed floors differed in the DROP direction. WI-1125 retired it
//! with the shape it measured: a carrier spelling both members is now refused at
//! load, so there is no own `neq` left for any gate to key on, and
//! `custom_eq_override_dispatches_and_drops` carries the eq-dispatch claim alone.
//! THREE→TWO is therefore a DEDUCTION from deleting that row, not a re-measurement:
//! restoring the blanket gate would mean rewriting the ~140 lines WI-755 deleted, and
//! this ticket did not. What WI-1125 did measure, against the shape it owns, is
//! recorded in `wi1125_neq_not_an_override_test`'s header — two back-outs, 7 and 1.
//!
//! Every other row passes EITHER WAY, and each for its own stated reason: the two
//! nested rows and the symbolic row because gate-suspend and resolver-delay produce
//! the same KEEP (what changes is WHO decided — the nested pair now pins the
//! resolver's buried-override reach rather than the typer's scan, and the symbolic
//! row pins its open-world force-delay); the two native rows because the gate never
//! fired on a carrier with no override.
//!
//! Contrast `wi592_constructor_arg_discharge_test`, whose `Color` carrier is
//! STRUCTURAL (`provides Eq`, no `operation eq`) — there the structural verdict IS
//! the carrier's equality and the effect discharges. The discriminating difference
//! here is the added `operation eq` member.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Identical harness to `wi067_guard_discharge_test::load_result`.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

/// The undeclared-effect diagnostic is `…effects: …got undeclared effect: Boom`
/// (typing.rs). Match BOTH fragments — not just `"Boom"` (which the sort name
/// alone would satisfy from any unrelated failure that happens to mention it).
fn is_undeclared_boom(errs: &[String]) -> bool {
    errs.iter()
        .any(|e| e.contains("undeclared effect") && e.contains("Boom"))
}

/// `Color` with a CUSTOM `eq` that always holds (`= true`): under this carrier's
/// equality `eq(Green, Red)` is TRUE, so the guard `eq(c, Red)` HOLDS and `Boom`
/// must be kept. The structural builtin would (wrongly) refute it.
const CUSTOM_EQ_TRUE_PRELUDE: &str = r#"
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Effect}
  -- WI-20260825-KD9SW: a WRITTEN guard functor is brought into scope by import; a
  -- guard naming nothing is VACUOUSLY discharged, so the row would pass for the wrong reason.
  import anthill.prelude.PartialEq.{eq}

  sort Boom
    entity Bang
  end
  -- WI-20260823-VM3YB: registers the label. Load-bearing.
  fact Effect[T = Boom]

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
  end

  operation risky(c: Color) -> Int64
    effects { Boom :- eq(c, Red) }
"#;

/// `Color` with NO override (`provides Eq` only) — the structural builtin IS this
/// carrier's equality, so the WI-592 discharge applies unchanged.
const STRUCTURAL_EQ_PRELUDE: &str = r#"
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Effect}
  -- WI-20260825-KD9SW: a WRITTEN guard functor is brought into scope by import; a
  -- guard naming nothing is VACUOUSLY discharged, so the row would pass for the wrong reason.
  import anthill.prelude.PartialEq.{eq}

  sort Boom
    entity Bang
  end
  -- WI-20260823-VM3YB: registers the label. Load-bearing.
  fact Effect[T = Boom]

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end

  operation risky(c: Color) -> Int64
    effects { Boom :- eq(c, Red) }
"#;

#[test]
fn custom_eq_override_keeps_effect() {
    // THE soundness row. `risky(Green)` with a custom `eq = true`: the carrier's
    // own equality makes `eq(Green, Red)` hold, so the guard holds and `Boom`
    // must be KEPT. Before WI-573 the structural builtin refuted `eq(Green, Red)`
    // (Green ≠ Red structurally) and unsoundly DROPPED `Boom` — this caller then
    // loaded with no `effects`. It must fail (undeclared `Boom`).
    //
    // WI-755 changed WHO keeps it, not WHETHER: the retired pre-gate suspended on
    // the mere presence of the override; the resolver now DISPATCHES `Color.eq`
    // (head carrier, deep-ground operands) and gets `true`, so `neq(Green, Red)`
    // is definitely FALSE and the guard is unrefutable. Both readings keep, so
    // this row does not distinguish WI-755 — it bounds it from the other side:
    // dispatch must not turn a HOLDING guard into a drop. Its `eq = false` twin,
    // `custom_eq_override_dispatches_and_drops`, is the discriminating one.
    let src = format!(
        r#"
namespace anthill.test.wi573keep
{CUSTOM_EQ_TRUE_PRELUDE}
  operation caller() -> Int64 =
    risky(Green)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "`Color.eq(Green, Red)` is TRUE, so the guard HOLDS and must not be refuted \
         structurally; `Boom` is kept, so omitting `effects Boom` must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the kept `Boom` to surface as undeclared; got: {errs:#?}"
    );
}

#[test]
fn native_eq_carrier_still_discharges() {
    // REGRESSION GUARD: a carrier with NO override is decided structurally, and
    // soundly — structural equality IS its instance. `risky(Green)` against guard
    // `eq(c, Red)` refutes (Green ≠ Red) → `Boom` DROPS → loads OK. This is the
    // WI-592 drop case; neither the retired gate nor the resolver's override
    // machinery may touch it (else every native-Eq discharge regresses to "kept").
    // It is also the pin that `provides Eq` alone must NOT synthesize a
    // carrier-parented `eq` member — the whole no-regression property rides on
    // this carrier having no override to find.
    let src = format!(
        r#"
namespace anthill.test.wi573native
{STRUCTURAL_EQ_PRELUDE}
  operation caller() -> Int64 =
    risky(Green)
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "a native-Eq carrier (no override) must still discharge `eq(Green, Red)` \
         and drop `Boom`; got: {:#?}",
        res.err()
    );
}

#[test]
fn custom_eq_override_kept_effect_is_declarable() {
    // The kept effect is a REAL effect, not a phantom diagnostic: declaring
    // `effects Boom` on the caller makes the same custom-override program load.
    // (Pairs with `custom_eq_override_keeps_effect` — same source, effect now
    // declared — to show the keep is a normal undeclared-effect, dischargeable by
    // declaration.)
    let src = format!(
        r#"
namespace anthill.test.wi573declared
{CUSTOM_EQ_TRUE_PRELUDE}
  operation caller() -> Int64
    effects {{ Boom }}
  =
    risky(Green)
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "declaring `effects {{ Boom }}` must satisfy the kept guarded effect; \
         got: {:#?}",
        res.err()
    );
}

/// The `eq = false` carrier: nothing is equal to anything, so `eq(Green, Red)` is
/// FALSE under this carrier's own equality even though the operands are the same
/// two constructors `CUSTOM_EQ_TRUE_PRELUDE` calls EQUAL. The two preludes differ
/// in one token and disagree on every verdict — which is what makes the pair
/// evidence that the override is being CONSULTED, not merely detected.
///
/// Its `provides Eq` is not lawful (`eq_refl` fails — a constant-`false` equality
/// is not reflexive) and nothing here relies on it being: every row over this
/// carrier compares DISTINCT constructors, which is a verdict a lawful instance is
/// free to give. Reflexive operands would take `sem_eq_values`' reflexivity
/// shortcut, which answers before any dispatch precisely because a lawful `Eq` must
/// agree with it — that is WI-616's contract, not something these rows measure.
const CUSTOM_EQ_FALSE_COLOR: &str = r#"
  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = false
  end
"#;

#[test]
fn custom_eq_override_dispatches_and_drops() {
    // THE WI-755 ROW — the ONE row in this file that fails if the retired pre-gate
    // comes back. With a custom `eq = false` the carrier's own equality makes
    // `eq(Green, Red)` FALSE, so its negation `neq(Green, Red)` is PROVED and the
    // guard is constructively refuted: `Boom` DROPS and `caller` loads with no
    // `effects` clause.
    //
    // What each half of the machinery contributes, since neither alone gets here:
    // the resolver dispatches because `Green`/`Red` key the load-time eq-dispatch
    // index and both operands are deep-ground (`sem_eq_values` outcome 4 →
    // `sem_eq_dispatch` → the eval bridge, `Color.eq` having a runnable body); the
    // typer reaches the resolver at all only because WI-755 removed the pre-gate
    // that short-circuited every eq-family conjunct over an overriding carrier.
    //
    // Under WI-573 this asserted the opposite (`Boom` KEPT) and its comment said
    // to move it here when option (a) landed. Sound then, incomplete: over-keeping
    // an effect never misses one, but it also never discharges one the carrier's
    // own equality refutes.
    let src = format!(
        r#"
namespace anthill.test.wi573suspend
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Effect}}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq}}
  import anthill.prelude.PartialEq.{{eq}}

  sort Boom
    entity Bang
  end
  -- WI-20260823-VM3YB: registers the label. Load-bearing.
  fact Effect[T = Boom]
{CUSTOM_EQ_FALSE_COLOR}
  operation risky(c: Color) -> Int64
    effects {{ Boom :- eq(c, Red) }}

  operation caller() -> Int64 =
    risky(Green)
end
"#
    );
    let res = load_result(&src);
    assert!(
        res.is_ok(),
        "`Color.eq(Green, Red)` is FALSE, so the guard `eq(c, Red)` is \
         constructively refuted and `Boom` must DROP — the caller declares no \
         effects and must load; got: {:#?}",
        res.err()
    );
}

#[test]
fn symbolic_operand_suspends_rather_than_dispatching() {
    // The NON-GROUND row. The same `eq = false` carrier — so a dispatch that
    // ignored groundness would refute the guard and DROP `Boom`, exactly as the
    // row above — but the caller forwards its OWN parameter, so σ leaves the guard
    // as `eq(var_ref(c), Red)` over an open-world binder. It must stay UNDECIDED:
    // `Boom` is kept and the caller must declare it.
    //
    // WHAT HOLDS IT, measured rather than assumed — the two candidates are not
    // interchangeable. Backing out `sem_eq_values`' `value_deep_ground` check
    // changes NOTHING here: the goal never reaches the builtin. Backing out the
    // resolver's open-world force-delay (`value_has_open_world_ref`, `step_init`)
    // makes this row FAIL — `SemEq` then decides `neq(var_ref(c), Red)` by
    // dispatching `Color.eq` on a reflect-term as if it were a constant, and `Boom`
    // drops. So this row pins the force-delay alone; the groundness check is
    // pinned, if anywhere, elsewhere. Not a control for the override — the
    // structural carrier flounders here too — but it is the control for WI-755 not
    // having bought its dispatch by deciding from an open world.
    let src = format!(
        r#"
namespace anthill.test.wi573symbolic
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq, Effect}}
  import anthill.prelude.{{Int64, Bool, Eq, PartialEq}}
  import anthill.prelude.PartialEq.{{eq}}

  sort Boom
    entity Bang
  end
  -- WI-20260823-VM3YB: registers the label. Load-bearing.
  fact Effect[T = Boom]
{CUSTOM_EQ_FALSE_COLOR}
  operation risky(c: Color) -> Int64
    effects {{ Boom :- eq(c, Red) }}

  operation caller(c: Color) -> Int64 =
    risky(c)
end
"#
    );
    let errs = load_result(&src).expect_err(
        "a symbolic guard operand leaves `eq(c, Red)` undecided, so `Boom` is kept \
         conservatively; omitting `effects Boom` must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the undecided (kept) `Boom` to surface as undeclared; \
         got: {errs:#?}"
    );
}

// ── The `neq`-only carrier: WI-755's residual floor, and its removal ─────────
// Found by review of WI-755, then measured. WI-573's gate detected an own `eq` OR
// an own `neq`; the resolver's replacement sees only `eq`, because
// `build_eq_dispatch_index` keys `PartialEq.eq` suppliers alone. So a carrier
// declaring `operation neq` and no `eq` keyed nothing and was decided STRUCTURALLY
// — against its own inequality. WI-755 kept a narrowed typer gate for exactly that
// shape (`guard_conjunct_reaches_undispatchable_neq`) and this file carried three
// `*_keeps_effect` rows plus `carrier_supplying_both_members_dispatches_its_eq` to
// bound it.
//
// **WI-1125 deleted the gate and all four rows**, by removing the SHAPE instead of
// guarding it: a carrier supplying its own `neq` — through any of the three supply
// routes — is now a load error (`LoadError::CarrierSuppliesNeq`), because
// `neq(a,b) <=> not(eq(a,b))` (§8.3) makes `neq` derived and no evaluator ever
// consulted it. The gate was the wrong shape of fix for a second reason this file
// could not see: it sat on the REFUTATION route alone, while the three other
// `prove_from_gamma` consumers and the interpreter answered such a carrier
// structurally with no floor at all.
//
// The rows live in `wi1125_neq_not_an_override_test` now — one per supply route,
// one per consumer, plus the both-members and contradictory-members arms. What
// stays HERE is the behaviour they bounded: `custom_eq_override_dispatches_and_drops`
// is the eq-only carrier whose guard is genuinely refuted and whose `Boom` drops,
// which is what `carrier_supplying_both_members_dispatches_its_eq` existed to
// protect from a gate keyed on the mere presence of an own `neq`. No such gate can
// exist now — there is no own `neq` for one to key on.

// ── Nested carriers: the BURIED override ─────────────────────────────────────
// A structural comparison recurses into every positional and named child, so a
// custom equality on a nested ELEMENT or FIELD carrier makes its verdict unsound
// just as a top-level one does — while the head carrier (`Option`, `Wrap`) has no
// override to dispatch, so there is nothing to decide WITH either. Both rows must
// therefore SUSPEND, and the effect is kept.
//
// WI-755 moved which code answers that. The retired typer gate scanned the
// operand's carried type (`value_type_term` → `carrier_own_op`) over the same
// children the structural compare touches; the resolver now answers it as
// `sem_eq_values` outcome 5 — no dispatch target at either head, but
// `value_reaches_eq_override` finds one INSIDE, so it delays rather than
// mis-decide, and `definite_only` turns that delay into "unrefuted". Same verdict,
// different scanner: these two rows pass either way and are the regression guard
// on the resolver's scan reaching as deep as the typer's did. Their controls are
// the `*_native_*` rows — without them "keeps" could equally mean "a container
// operand never decides", which would measure nothing.
//
// `Color` again has a custom `eq = true`; the container/wrapper itself uses
// structural `Eq`.

#[test]
fn nested_element_override_keeps_effect() {
    // `Option[Color]` element carrier overrides `eq`. `eq(some(Green), some(Red))`
    // recurses into the `Color` elements; structurally `Green != Red`, so a
    // structural verdict would refute and drop `Boom`, but under `Color.eq = true`
    // the options are element-wise "equal" — and `Option` declares no `eq` to
    // dispatch, so the compare cannot decide either way. It suspends and `Boom` is
    // kept. The top-level carrier has no override, so a head-only scan misses this
    // — the reach must descend into the element.
    let src = r#"
namespace anthill.test.wi573nestedelem
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Option, Effect}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.PartialEq.{eq}

  sort Boom
    entity Bang
  end
  -- WI-20260823-VM3YB: registers the label. Load-bearing.
  fact Effect[T = Boom]

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
  end

  operation risky(o: Option[T = Color]) -> Int64
    effects { Boom :- eq(o, some(Red)) }

  operation caller() -> Int64 =
    risky(some(Green))
end
"#;
    let errs = load_result(src).expect_err(
        "a custom `eq` on the ELEMENT carrier of `Option[Color]` must suspend the \
         structural refutation; `Boom` is kept, so omitting it must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the kept `Boom` (nested element override) to surface as \
         undeclared; got: {errs:#?}"
    );
}

#[test]
fn nested_field_override_keeps_effect() {
    // `Wrap` has a `Color` FIELD (a NAMED child). `eq(W(c: Green), W(c: Red))`
    // recurses into the `c` field, where `Color.eq = true` contradicts the
    // structural verdict while `Wrap` itself declares no `eq` to dispatch — so the
    // compare suspends and `Boom` is kept. Exercises the named-child arm of the
    // reach, distinct from the positional element case.
    let src = r#"
namespace anthill.test.wi573nestedfield
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Effect}
  import anthill.prelude.PartialEq.{eq}

  sort Boom
    entity Bang
  end
  -- WI-20260823-VM3YB: registers the label. Load-bearing.
  fact Effect[T = Boom]

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = true
  end

  sort Wrap
    entity W(c: Color)
    provides PartialEq[T = Wrap]
    provides Eq[T = Wrap]
  end

  operation risky(w: Wrap) -> Int64
    effects { Boom :- eq(w, W(c: Red)) }

  operation caller() -> Int64 =
    risky(W(c: Green))
end
"#;
    let errs = load_result(src).expect_err(
        "a custom `eq` on a FIELD carrier of `Wrap` must suspend the structural \
         refutation; `Boom` is kept, so omitting it must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the kept `Boom` (nested field override) to surface as \
         undeclared; got: {errs:#?}"
    );
}

#[test]
fn nested_native_element_still_discharges() {
    // REGRESSION GUARD for the buried-override reach, and the CONTROL for
    // `nested_element_override_keeps_effect`: a NESTED-native container (no
    // override anywhere in `Option[Color]` — `Color` here has only structural
    // `provides Eq`) must still discharge. `eq(some(Green), some(Red))` refutes
    // structurally (Green != Red) → `Boom` DROPS → loads OK. The reach must not
    // over-block native nested structures (else every container `eq`-guard
    // regresses to "kept", and the suspension above would mean nothing).
    let src = r#"
namespace anthill.test.wi573nestednative
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Option, Effect}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.PartialEq.{eq}

  sort Boom
    entity Bang
  end
  -- WI-20260823-VM3YB: registers the label. Load-bearing.
  fact Effect[T = Boom]

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
  end

  operation risky(o: Option[T = Color]) -> Int64
    effects { Boom :- eq(o, some(Red)) }

  operation caller() -> Int64 =
    risky(some(Green))
end
"#;
    let res = load_result(src);
    assert!(
        res.is_ok(),
        "a wholly native `Option[Color]` (no override anywhere) must still \
         discharge `eq(some(Green), some(Red))` and drop `Boom`; got: {:#?}",
        res.err()
    );
}
