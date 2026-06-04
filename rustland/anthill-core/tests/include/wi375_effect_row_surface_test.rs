//! WI-375 — WRITTEN effect-rows in a type-argument value slot
//! (`Stream[E = {}]` / `Stream[E = {Modify[p]}]`).
//!
//! Surface completion of the proposal-045 effect-ROW model: an effect row can
//! now be STATED structurally in a type argument, exactly as the element `T`
//! is. The grammar `effect_row` node lowers (convert.rs → load.rs) to the KB
//! `effects_rows(EffectExpression)` Type (the WI-320 bridge), so a producer's
//! return type can carry the observation effect `E` in the type.
//!
//! This makes the effectful-carrier case SOUND (design doc §5,
//! `docs/design/expansion-during-unification.md`): the effect is IN the type,
//! so a pure consumer of an effectful stream is correctly rejected, while a
//! pure stream (`E = {}`) typechecks pure. The row threads into a bare-`Stream`
//! consumer param through the existing `unify_parameterized_with_sort_ref`
//! half-rule (the parameterized return ↔ bare param case) and the effect check
//! (`check_operation_bodies`) rejects an undeclared effect in a pure context.
//!
//! No WI-374 dependency: the producer RETURNS a *parameterized* `Stream[E=…]`,
//! so the (parameterized, sort_ref) arm already threads it — WI-374's
//! bare-vs-bare expansion is only needed when the producer erases the row
//! (bare `-> Stream`).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra sources → load-error strings (empty Vec on clean load).
fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
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

/// An abstract `Producer` whose two stream-producing ops WRITE their result's
/// observation effect in the type: `pure_stream` is `E = {}` (pure), and
/// `eff_stream` is `E = {Modify[p]}` (observing it mutates `p`). Both carry the
/// element `T = Int`. These are exactly the two WI-375 surface forms.
const CARRIER: &str = r#"
namespace test.wi375.carrier
  import anthill.prelude.{Int, Stream, Modify, EffectsRuntime}
  export Producer

  sort Producer
    -- A pure stream: nothing is incurred to observe it.
    operation pure_stream(p: Producer) -> Stream[T = Int, E = {}]
    -- An effectful stream: observing it incurs Modify[p].
    operation eff_stream(p: Producer) -> Stream[T = Int, E = {Modify[p]}]
  end
end
"#;

// ── Acceptance #1: the written effect-row forms load ────────────────────────

/// `Stream[E = {}]` and `Stream[E = {Modify[p]}]` parse, lower to
/// `effects_rows(EffectExpression)`, and load with zero errors. This is the
/// surface-syntax acceptance: the braced row in a type-argument value slot is
/// accepted (it was a parse error before WI-375 — "parse error tested" in the
/// WI-320 bridge).
#[test]
fn written_effect_row_forms_load_clean() {
    let errs = load_errors(&[CARRIER]);
    assert!(
        errs.is_empty(),
        "the WI-375 producer (Stream[E = {{}}] and Stream[E = {{Modify[p]}}]) must \
         load with no errors — the braced effect-row in a type-argument slot is \
         the proposal-045 surface form; got: {errs:?}",
    );
}

// ── Acceptance #2a: a PURE written stream typechecks pure ───────────────────

/// Observing the `E = {}` stream incurs no effect, so a pure consumer
/// (`good`, no effects clause) typechecks. The written empty row binds the
/// bare-`Stream` consumer param's `E` to `{}`, and `isEmpty`'s `effects E`
/// closes to `{}`.
#[test]
fn pure_written_stream_accepted_in_pure_context() {
    let consumer = r#"
namespace test.wi375.pure
  import anthill.prelude.{Bool}
  import anthill.prelude.Stream.{isEmpty}
  import test.wi375.carrier.{Producer}
  import test.wi375.carrier.Producer.{pure_stream}

  operation good(p: Producer) -> Bool = isEmpty(pure_stream(p))
end
"#;
    let errs = load_errors(&[CARRIER, consumer]);
    assert!(
        errs.is_empty(),
        "a pure consumer observing a written-pure stream (Stream[E = {{}}]) must \
         typecheck — the empty row binds isEmpty's E to {{}}; got: {errs:?}",
    );
}

// ── Acceptance #2b: an EFFECTFUL written stream is rejected in a pure op ─────

/// Observing the `E = {Modify[p]}` stream incurs `Modify[p]`. A pure consumer
/// (`bad`, no effects clause) must be rejected with an undeclared-effect
/// diagnostic naming `Modify` — the written row threads through `isEmpty`'s
/// bare-`Stream` param (binding `E := {Modify[p]}`) and the effect check
/// rejects it in the pure context. This is the soundness payoff: the effect is
/// IN the type, so the effectful carrier cannot pass as pure.
#[test]
fn effectful_written_stream_rejected_in_pure_context() {
    let consumer = r#"
namespace test.wi375.effectful
  import anthill.prelude.{Bool}
  import anthill.prelude.Stream.{isEmpty}
  import test.wi375.carrier.{Producer}
  import test.wi375.carrier.Producer.{eff_stream}

  operation bad(p: Producer) -> Bool = isEmpty(eff_stream(p))
end
"#;
    let errs = load_errors(&[CARRIER, consumer]);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect") && e.contains("Modify")),
        "a pure consumer observing a written-effectful stream (Stream[E = \
         {{Modify[p]}}]) must be rejected with an undeclared-effect diagnostic \
         naming Modify — the written row binds isEmpty's E to {{Modify[p]}}; \
         got: {errs:?}",
    );
}
