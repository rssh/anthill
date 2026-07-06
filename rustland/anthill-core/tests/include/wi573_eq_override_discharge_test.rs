//! WI-573 (WI-502 consumer): a guarded-effect guard whose predicate is the
//! spec op `eq`/`neq` must NOT be refuted by the structural `Eq`/`Neq` builtin
//! when the argument's carrier defines its OWN equality override.
//!
//! WI-067/WI-592 discharge an `eq`-guard (`{ Boom :- eq(c, Red) }`) by refuting
//! it through the resolver's structural `Eq` builtin (`BuiltinTag::Eq`): for a
//! NATIVE-Eq carrier (`provides Eq`, no override) that is sound — structural
//! equality *is* the carrier's equality. But a carrier that overrides `eq` with
//! its OWN impl has a different equality, and the structural builtin never
//! dispatches that impl. So refuting `eq(Green, Red)` structurally (Green ≠ Red)
//! and DROPPING the effect is unsound when the carrier's `eq` would hold.
//!
//! WI-573 detects the override from the operand's carried type
//! (`value_type_term` → `carrier_override_op`) and SUSPENDS the conjunct — the
//! effect is conservatively kept. Actually dispatching the override (runtime
//! monomorphization, so the guard could still discharge under the carrier's own
//! equality) is the deferred half (the ticket's option (a)); this delivers the
//! sound floor (option (b): keep when an override exists).
//!
//! Contrast `wi592_constructor_arg_discharge_test`, whose `Color` carrier is
//! STRUCTURAL (`provides Eq`, no `operation eq`) — there the builtin is sound and
//! the effect discharges. The discriminating difference here is the added
//! `operation eq` member.

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
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
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
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}

  sort Boom
    entity Bang
  end

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
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}

  sort Boom
    entity Bang
  end

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
    // THE soundness fix. `risky(Green)` with a custom `eq = true`: the carrier's
    // own equality makes `eq(Green, Red)` hold, so the guard holds and `Boom`
    // must be KEPT. Before WI-573 the structural builtin refuted `eq(Green, Red)`
    // (Green ≠ Red structurally) and unsoundly DROPPED `Boom` — this caller then
    // loaded with no `effects`. It must now fail (undeclared `Boom`).
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
        "a carrier with a CUSTOM `eq` override must NOT have its `eq`-guard refuted \
         by the structural builtin; `Boom` is kept, so omitting `effects Boom` must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the kept (suspended) `Boom` to surface as undeclared; got: {errs:#?}"
    );
}

#[test]
fn native_eq_carrier_still_discharges() {
    // REGRESSION GUARD: a carrier with NO override is decided soundly by the
    // structural builtin, exactly as before WI-573. `risky(Green)` against guard
    // `eq(c, Red)` refutes (Green ≠ Red) → `Boom` DROPS → loads OK. This is the
    // WI-592 drop case; the override gate must not touch it (else every native-Eq
    // discharge would regress to "kept").
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

#[test]
fn custom_eq_override_suspends_rather_than_dispatches() {
    // Characterizes the CONSERVATIVE suspend (option (b), the delivered floor) vs
    // dispatch (option (a), deferred). With a custom `eq = false` (nothing is
    // equal), the carrier's own equality makes `eq(Green, Red)` FALSE, so under
    // full runtime monomorphization the guard would be refuted and `Boom` could
    // DROP. WI-573 does NOT evaluate the override — it only DETECTS one and
    // suspends — so `Boom` is conservatively KEPT here too (sound: over-keeping
    // an effect never misses one). If this ever starts dropping, the dispatch
    // half (option (a)) has landed and this test should move to assert the drop.
    let src = r#"
namespace anthill.test.wi573suspend
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}

  sort Boom
    entity Bang
  end

  sort Color
    entity Red
    entity Green
    provides PartialEq[T = Color]
    provides Eq[T = Color]
    operation eq(a: Color, b: Color) -> Bool = false
  end

  operation risky(c: Color) -> Int64
    effects { Boom :- eq(c, Red) }

  operation caller() -> Int64 =
    risky(Green)
end
"#;
    let errs = load_result(src).expect_err(
        "WI-573 suspends (keeps) on a detected override without evaluating it, so \
         even a custom `eq = false` keeps `Boom`; omitting `effects Boom` must fail",
    );
    assert!(
        is_undeclared_boom(&errs),
        "expected the conservatively-suspended `Boom` to surface as undeclared; \
         got: {errs:#?}"
    );
}

// ── Nested carriers ──────────────────────────────────────────────────────────
// The structural `Eq`/`Neq` builtin compares values by structural RECURSION, so
// a custom equality on a nested ELEMENT or FIELD carrier (not just the top-level
// one) makes the structural verdict unsound too. The override scan therefore
// mirrors `views_structurally_equal` and descends into positional + named
// children. `Color` again has a custom `eq = true`; the container/wrapper itself
// uses structural `Eq`.

#[test]
fn nested_element_override_keeps_effect() {
    // `Option[Color]` element carrier overrides `eq`. `eq(some(Green), some(Red))`
    // recurses into the `Color` elements; structurally `Green != Red`, so the
    // builtin would refute and drop `Boom`, but under `Color.eq = true` the
    // options are element-wise "equal" → the guard holds → `Boom` must be kept.
    // The top-level carrier is `Option` (no override), so a top-level-only gate
    // misses this — the scan must reach the element.
    let src = r#"
namespace anthill.test.wi573nestedelem
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Option}
  import anthill.prelude.Option.{some, none}

  sort Boom
    entity Bang
  end

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
    // recurses into the `c` field; under `Color.eq = true` the wraps are "equal"
    // → guard holds → `Boom` kept. Exercises the named-child arm of the scan
    // (`named_keys`/`named_arg`), distinct from the positional element case.
    let src = r#"
namespace anthill.test.wi573nestedfield
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}

  sort Boom
    entity Bang
  end

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
    // REGRESSION GUARD for the deep scan: a NESTED-native container (no override
    // anywhere in `Option[Color]` — `Color` here has only structural `provides
    // Eq`) must still discharge. `eq(some(Green), some(Red))` refutes structurally
    // (Green != Red) → `Boom` DROPS → loads OK. The deep scan must not over-block
    // native nested structures (else every container `eq`-guard would regress to
    // "kept").
    let src = r#"
namespace anthill.test.wi573nestednative
  import anthill.prelude.{Int64, Bool, Eq, PartialEq, Option}
  import anthill.prelude.Option.{some, none}

  sort Boom
    entity Bang
  end

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
