//! WI-576: the codegen capability gate and the uniform effect-realization
//! accessor it reads.
//!
//! An operation's residual required effect row must be a SUBSET of the target
//! profile's supported-effect set — the effects that profile's `effect_map`
//! realizes. An effect with no realization is UNREALIZABLE there and must fail
//! loudly (repo principle: loud error over silent skip), never be folded away
//! into "emit the signature unchanged".
//!
//! Handlers are unimplemented (WI-329), so residual == declared; once
//! `handle_K` discharge lands it narrows the row before the gate sees it.

use super::common;

use anthill_cpp_gen::{emit_namespace_header_with_profile, emit_traits_struct, realizes_effect};
use common::load_kb_with;

/// cpp's supported set is exactly `{Error, Modify}` (`cpp_std.anthill`'s flat
/// keyed `EffectMapping` facts). `ConsoleOutput` is a real, resolvable effect
/// sort with no cpp realization — so it must be REJECTED, naming the effect,
/// the profile, and what the profile does support.
#[test]
fn unrealizable_effect_rejected() {
    let source = r#"
        namespace test.wi576.gate
          import anthill.prelude.{Unit, String}
          import anthill.prelude.Console.{ConsoleOutput}
          sort Logger
            operation shout(msg: String) -> Unit
              effects ConsoleOutput
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_traits_struct(&mut kb, "test.wi576.gate.Logger")
        .expect_err("an effect the cpp profile cannot realize must fail codegen");

    let msg = err.to_string();
    assert!(msg.contains("ConsoleOutput"), "must name the offending effect: {msg}");
    assert!(msg.contains("shout"), "must name the offending operation: {msg}");
    assert!(msg.contains("cpp"), "must name the target profile: {msg}");
    // The supported set comes from the KB, not a hardcoded list.
    assert!(
        msg.contains("Error") && msg.contains("Modify"),
        "must report the profile's supported effects: {msg}"
    );
}

/// The same rejection with a compilation profile actually threaded in — the
/// path the CLI takes, where `Generated.profile` reaches `CodegenContext`. The
/// diagnostic must name THAT profile, not a hardcoded one.
#[test]
fn unrealizable_effect_names_the_active_profile() {
    let source = r#"
        namespace test.wi576.profiled
          import anthill.prelude.{Unit, String}
          import anthill.prelude.Console.{ConsoleOutput}
          sort Logger
            operation shout(msg: String) -> Unit
              effects ConsoleOutput
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_namespace_header_with_profile(
        &mut kb,
        "test.wi576.profiled",
        Some("cpp20-stl".to_string()),
    )
    .expect_err("an effect no profile realizes must fail codegen");

    let msg = err.to_string();
    assert!(msg.contains("ConsoleOutput"), "must name the offending effect: {msg}");
    assert!(msg.contains("cpp20-stl"), "must name the ACTIVE profile: {msg}");
}

/// The positive half of the acceptance: both effects cpp DOES realize —
/// `Error` (`ResultWrap`) and a `denoted`-bearing `Modify[self]` (`MutRef`,
/// carried as a `Value::Node`) — lower without complaint, and `Error` still
/// drives the `tl::expected` return wrap.
#[test]
fn realized_effects_lower_fine() {
    let source = r#"
        namespace test.wi576.ok
          import anthill.prelude.{Int64, Unit, Modify, Error}
          import anthill.realization.{Implementation, CarrierBinding}

          sort Robot
            operation bump(self: Robot, n: Int64) -> Unit
              effects Modify[self]
            operation risky(n: Int64) -> Int64
              effects Error
          end

          fact Implementation(
            target:        "test.wi576.ok.Robot",
            artifact:      "robot.hpp",
            language:      "cpp",
            profile:       some("cpp17-stl"),
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Robot",
                                           host_type: "::vendor::Robot *")],
            namespace_map: [],
            binding:       none
          )
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.wi576.ok.Robot")
        .expect("effects the profile realizes must lower");

    assert!(cpp.contains("bump"), "Modify-effect op should be emitted:\n{cpp}");
    assert!(
        cpp.contains("tl::expected<int64_t, std::string> risky"),
        "Error effect should still drive the ResultWrap return:\n{cpp}"
    );
}

/// An effect-polymorphic operation (`effects {EffP}` over a declared type
/// param) states no CONCRETE requirement at its declaration — the row is
/// whatever a call site instantiates — so the gate must pass it through rather
/// than reject it as unrealizable.
///
/// A LOCAL fixture, not `anthill.prelude.Monad`: keying the regression to a
/// stdlib declaration means a change there could silently stop covering this
/// branch instead of failing. `Monad` is exercised separately below as the
/// real-world instance.
#[test]
fn effect_row_parameter_is_not_gated() {
    let source = r#"
        namespace test.wi576.poly
          import anthill.prelude.{Int64}
          sort Runner
            operation run[EffP](n: Int64) -> Int64 effects {EffP}
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.wi576.poly.Runner")
        .expect("an effect-polymorphic op must not trip the capability gate");
    assert!(cpp.contains("run"), "the op should still be emitted:\n{cpp}");
}

/// The stdlib instance of the same shape — `Monad.flatMap[A, B, EffP](…)
/// effects {EffP}`. This is what broke when the gate first treated an
/// unreadable label and a row parameter alike.
#[test]
fn stdlib_monad_effect_row_parameter_is_not_gated() {
    let mut kb = load_kb_with("namespace test.wi576.monad\nend\n");
    emit_traits_struct(&mut kb, "anthill.prelude.Monad")
        .expect("Monad's effect-polymorphic ops must not trip the capability gate");
}

/// The accessor over cpp's FLAT keyed `EffectMapping` facts (WI-089(b)).
#[test]
fn realizes_effect_reads_flat_keyed_facts() {
    let mut kb = load_kb_with("namespace test.wi576.flat\nend\n");

    assert_eq!(realizes_effect(&mut kb, "cpp", None, "Error").as_deref(), Some("ResultWrap"));
    assert_eq!(realizes_effect(&mut kb, "cpp", None, "Modify").as_deref(), Some("MutRef"));
    // Outside the supported set — the answer the gate turns into an error.
    assert_eq!(realizes_effect(&mut kb, "cpp", None, "ConsoleOutput"), None);
    // An unknown profile still sees the language base (`key: none`).
    assert_eq!(
        realizes_effect(&mut kb, "cpp", Some("cpp20-stl"), "Error").as_deref(),
        Some("ResultWrap")
    );
}

/// The SAME accessor over the NESTED representation — `effect_map` inside a
/// `LanguageMapping` fact, which is what rust/scala kept after the WI-089 pivot
/// moved cpp to flat facts. This is the "never assume a representation" half of
/// WI-576: a `lang`-generic accessor that only read the flat form would answer
/// `None` here and report effects these profiles DO realize as unsupported.
#[test]
fn realizes_effect_reads_nested_language_mapping() {
    let mut kb = load_kb_with("namespace test.wi576.nested\nend\n");

    // scala_std: Modify is by-value (immutable update), Error is Either.
    assert_eq!(realizes_effect(&mut kb, "scala", Some("std"), "Modify").as_deref(), Some("ByValue"));
    assert_eq!(
        realizes_effect(&mut kb, "scala", Some("std"), "Error").as_deref(),
        Some("ResultWrap")
    );
    // rust_std: Modify is `&mut self` — same effect, different host realization,
    // read through one accessor.
    assert_eq!(realizes_effect(&mut kb, "rust", Some("std"), "Modify").as_deref(), Some("MutRef"));

    // scala_caps declares Console; scala_std does not. The profile selects.
    assert_eq!(realizes_effect(&mut kb, "scala", Some("std"), "Console"), None);

    // The gap WI-576's description names: no scala profile realizes `Async`.
    assert_eq!(realizes_effect(&mut kb, "scala", Some("std"), "Async"), None);
}

/// Pins the accessor's CONTRACT for the nested representation: the profile is
/// REQUIRED there. Only the flat form has a language base (`key: none`) —
/// every stdlib `LanguageMapping` declares a profile (`std` / `caps` /
/// `anthill`) and none declares `profile: none` — so asking without one
/// resolves nothing even for an effect the language obviously realizes.
///
/// Asserted rather than "fixed" with a sole-mapping-wins fallback, which would
/// guess at the caller's profile. cpp is deliberately shown as the contrast:
/// its facts DO carry a base, so the same call succeeds.
#[test]
fn realizes_effect_without_a_profile_resolves_no_nested_entry() {
    let mut kb = load_kb_with("namespace test.wi576.nobase\nend\n");

    assert_eq!(
        realizes_effect(&mut kb, "rust", None, "Modify"),
        None,
        "no rust LanguageMapping declares profile: none, so there is no base to hit"
    );
    assert_eq!(realizes_effect(&mut kb, "scala", None, "Modify"), None);
    // Contrast: cpp's flat facts carry `key: none`, so the base resolves.
    assert_eq!(realizes_effect(&mut kb, "cpp", None, "Modify").as_deref(), Some("MutRef"));
}

/// A cpp `EffectMapping` must not be answered from another language's entries,
/// and vice versa — the two representations are merged into one hit list, so
/// the language filter has to survive that merge.
#[test]
fn realizes_effect_does_not_leak_across_languages() {
    let mut kb = load_kb_with("namespace test.wi576.iso\nend\n");

    // scala_std maps Modify to ByValue; cpp must still answer MutRef.
    assert_eq!(realizes_effect(&mut kb, "cpp", None, "Modify").as_deref(), Some("MutRef"));
    // No `LanguageMapping(language: "cpp")` and no flat rust facts exist, so a
    // language with neither representation present resolves nothing.
    assert_eq!(realizes_effect(&mut kb, "python", None, "Modify"), None);
}
