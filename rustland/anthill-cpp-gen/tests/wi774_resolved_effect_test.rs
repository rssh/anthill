//! WI-774: `supported_effects` (the WI-576 capability-gate diagnostic) RESOLVES
//! its `EffectMapping` / `LanguageMapping` candidates instead of head-matching
//! them. This retires the last WI-770 `assert!`-abort in cpp-gen: a bodied
//! realization rule is now EVALUATED (its guard honored) rather than aborting the
//! read.
//!
//! Two consequences the WI called out, both fixed here:
//!   1. A bodied `EffectMapping` no longer turns the gate's rejection DIAGNOSTIC
//!      into a panic — the abort used to fire inside `describe_supported_effects`
//!      while RENDERING the capability-gate error (exit 101, no span).
//!   2. Resolution HONORS the guard when gathering candidates, so a guarded
//!      `EffectMapping` joins the supported-effect set only when its body succeeds
//!      — where the head-match path listed it unconditionally (guard skipped).
//!
//! The Resolve policy itself is pinned generically by `kb::extent`'s unit tests
//! (`read_facts_resolved_honors_a_passing_bodied_rule_guard` and siblings); this
//! file exercises it end-to-end through the public capability gate.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_with;

/// The exact WI-774 bug: a bodied `EffectMapping` rule must not turn the
/// capability-gate DIAGNOSTIC into a panic. `supported_effects` gathers its
/// candidates while rendering the rejection; pre-WI-774 it head-matched the bodied
/// rule and `assert!`-aborted mid-message. Now it resolves (guard honored), so the
/// rejection renders cleanly, naming the offending effect and the supported set.
#[test]
fn bodied_effect_mapping_does_not_abort_the_gate_diagnostic() {
    let source = r#"
        namespace test.wi774.diag
          import anthill.prelude.{Unit, String, Bool}
          import anthill.prelude.Console.{ConsoleOutput}
          import anthill.prelude.Option.{some, none}
          import anthill.realization.{EffectMapping, ReceiverForm}

          sort Logger
            operation shout(msg: String) -> Unit
              effects ConsoleOutput
          end

          entity Toggle(on: Bool)
          fact Toggle(on: true)

          -- A GUARDED EffectMapping overlay under the very functor the diagnostic
          -- enumerates. Pre-WI-774 this poisoned `supported_effects` with an
          -- `assert!`-abort while the gate error was being rendered; now it
          -- RESOLVES (the guard holds), so the diagnostic renders instead.
          rule EffectMapping(effect: "Widen", receiver: MutRef, lang: some("cpp"), key: some("wi774"))
            :- Toggle(on: true)
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_traits_struct(&mut kb, "test.wi774.diag.Logger")
        .expect_err("ConsoleOutput is unrealizable in cpp — the gate must reject");
    let msg = err.to_string();
    // The diagnostic RENDERED (no panic) and still names the offending effect and
    // the resolved supported set (Error, Modify from the plain cpp base facts).
    assert!(msg.contains("ConsoleOutput"), "names the offending effect: {msg}");
    assert!(
        msg.contains("Error") && msg.contains("Modify"),
        "lists the resolved supported set: {msg}"
    );
}

/// Resolution HONORS the guard in the candidate gather: a guarded cpp-base
/// `EffectMapping` (`key: none`) contributes its effect to the supported set only
/// when its body succeeds. A head-match (the retired WI-770 path) would have listed
/// it regardless of the guard — the silent-wrong-answer this replaces.
#[test]
fn a_guarded_effect_mapping_joins_the_supported_set_only_when_its_guard_holds() {
    let with_guard = supported_effects_diagnostic(true);
    assert!(with_guard.contains("Widen"), "guard holds → Widen is supported: {with_guard}");

    let without_guard = supported_effects_diagnostic(false);
    assert!(
        !without_guard.contains("Widen"),
        "guard fails → Widen is NOT supported (resolution skips it): {without_guard}"
    );
    // Either way the plain base facts read, so a missing Widen is the guard, not a
    // broken read.
    assert!(without_guard.contains("Modify"), "plain base facts still resolve: {without_guard}");
}

/// Render the capability-gate rejection diagnostic (which lists the resolved
/// supported-effect set) for a `Logger.shout` op requiring the unrealizable
/// `ConsoleOutput`, with a guarded cpp-base `EffectMapping` for `Widen` whose guard
/// holds iff `guard_holds`.
fn supported_effects_diagnostic(guard_holds: bool) -> String {
    let toggle = if guard_holds {
        "fact Toggle(on: true)"
    } else {
        "fact Toggle(on: false)"
    };
    let source = format!(
        r#"
        namespace test.wi774.guard
          import anthill.prelude.{{Unit, String, Bool}}
          import anthill.prelude.Console.{{ConsoleOutput}}
          import anthill.prelude.Option.{{some, none}}
          import anthill.realization.{{EffectMapping, ReceiverForm}}

          sort Logger
            operation shout(msg: String) -> Unit
              effects ConsoleOutput
          end

          entity Toggle(on: Bool)
          {toggle}

          -- A guarded cpp language-base EffectMapping. When the guard holds it
          -- resolves through both the candidate gather AND `realizes_effect`'s base
          -- arm, so `Widen` lands in the supported set; when it fails, it is absent.
          rule EffectMapping(effect: "Widen", receiver: MutRef, lang: some("cpp"), key: none)
            :- Toggle(on: true)
        end
    "#
    );
    let mut kb = load_kb_with(&source);
    emit_traits_struct(&mut kb, "test.wi774.guard.Logger")
        .expect_err("ConsoleOutput unrealizable → gate rejects, rendering the supported set")
        .to_string()
}
