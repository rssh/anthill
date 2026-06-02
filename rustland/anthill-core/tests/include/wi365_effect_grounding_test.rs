//! WI-365 — effect grounding through a *dispatched* spec op (the EFFECT dual of
//! WI-357's element threading).
//!
//! Background (the design decision behind WI-301's closure). A provider fact
//! never carries the carrier's effect — effects are not type arguments. A pure
//! carrier (`List`) leaves the spec's effect row unbound and the typer grounds
//! it to `{}`. The open question this file pins is the NON-pure case: a carrier
//! whose spec-op override is genuinely effectful (`effects Modify[b]`). That
//! effect lives on the OPERATION, not the fact, and the typer must DERIVE it at
//! the consumption boundary — exactly as it derives `{}` for the pure case.
//!
//! Today it does not. The concrete-carrier effect-close (`kb/typing.rs`,
//! "Close the spec op's OWN polymorphic effect row at this concrete carrier")
//! only handles the pure provider: it *drops* the still-unresolved effect row
//! var. Its own comment says "the only expressible case today is a pure
//! provider (`List`)". So a dispatched `Box.peek` over the non-pure `MutBox`
//! never derives `Modify[b]`: the effect row leaks as the unresolved var `?_`
//! and the call also raises `MissingRequiresForSpecOp` (the uncovered effect
//! param) — but NO diagnostic names `Modify`, so the mutating call is not
//! pinned to its real effect (the exact shape WI-365 §"CALL-SIDE" describes).
//!
//! ANCHOR (`direct_*`, active): the DIRECT call to the carrier's own `peek`
//! already surfaces `Modify` and rejects a pure consumer — proving the effect
//! checker works and the carrier really is non-pure, so the trip-wire below is
//! not vacuous.
//!
//! TRIP-WIRE (`dispatched_*`, `#[ignore]`): the DISPATCHED `Box.peek` call must
//! likewise surface `Modify` and reject the pure consumer. Today no error names
//! `Modify` (the row var is dropped / leaks as `?_`). This is the acceptance
//! gate for WI-365 — un-`#[ignore]` it when the def-side effect dual of WI-357
//! lands and the dispatched spec op grounds its effect row to the carrier's
//! real effect.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra sources → load-error strings (empty Vec on clean load).
fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// Spec `Box.peek` carries a polymorphic effect row (`effects Effect`); the
/// concrete carrier `MutBox` provides `Box` and overrides `peek` with a
/// genuinely non-pure body (`effects Modify[b]`). The provider fact omits the
/// effect — by design — so the effect must be derived from `MutBox.peek`.
const CARRIER: &str = r#"
namespace test.wi365.carrier
  import anthill.prelude.{Int, Modify, EffectsRuntime}
  export Box, MutBox

  sort Box
    effects Effect = ?
    operation peek(b: Box) -> Int effects Effect
  end

  sort MutBox
    entity mb(fd: Int)
    fact Box
    operation peek(b: MutBox) -> Int effects Modify[b] =
      match b
        case mb(x) -> x
  end
end
"#;

// ── Anchor: the DIRECT carrier-op call already surfaces the Modify effect ────

/// `MutBox.peek` (the concrete carrier op) is `effects Modify[b]`. A consumer
/// that calls it directly and declares NO effects (closed/pure) must be
/// rejected with an undeclared-effect diagnostic naming `Modify`. This already
/// works — it is the baseline the dispatched path must match.
#[test]
fn direct_carrier_peek_surfaces_modify_effect() {
    let consumer = r#"
namespace test.wi365.direct
  import anthill.prelude.{Int}
  import test.wi365.carrier.{MutBox}
  import test.wi365.carrier.MutBox.{peek}

  operation read_it(b: MutBox) -> Int = peek(b)
end
"#;
    let errs = load_errors(&[CARRIER, consumer]);
    assert!(
        errs.iter().any(|e| e.contains("Modify")),
        "a pure consumer calling MutBox.peek directly (effects Modify[b]) must be \
         rejected with an undeclared-effect diagnostic naming Modify; got: {errs:?}",
    );
}

// ── WI-365 trip-wire: the DISPATCHED spec-op call must surface it too ────────

/// Consume a `MutBox` THROUGH the `Box` spec op `peek`. The op
/// dispatches to `MutBox.peek` (MutBox provides Box), whose effect is
/// `Modify[b]`; a sound typer derives that effect at the call site and rejects
/// the pure `read_it`, exactly as the direct anchor above is rejected.
///
/// FAILS TODAY: the dispatched `peek`'s effect row is not grounded to the
/// carrier — it leaks as `?_` (plus a `MissingRequiresForSpecOp`), so no error
/// names `Modify`. Acceptance gate for WI-365 — un-`#[ignore]` when the
/// dispatched spec op grounds its effect row to the carrier's real effect.
#[test]
#[ignore = "WI-365: dispatched spec-op effect grounding not implemented; non-pure carrier effect leaks as ?_ and is never derived to Modify"]
fn dispatched_spec_peek_surfaces_modify_effect() {
    let consumer = r#"
namespace test.wi365.dispatched
  import anthill.prelude.{Int}
  import test.wi365.carrier.{MutBox}
  import test.wi365.carrier.Box.{peek}

  operation read_it(b: MutBox) -> Int = peek(b)
end
"#;
    let errs = load_errors(&[CARRIER, consumer]);
    assert!(
        errs.iter().any(|e| e.contains("Modify")),
        "a pure consumer calling MutBox.peek THROUGH the Box spec op must be \
         rejected with an undeclared-effect diagnostic naming Modify — the \
         dispatched effect must ground to the carrier's Modify[b], not {{}}; \
         got: {errs:?}",
    );
}
