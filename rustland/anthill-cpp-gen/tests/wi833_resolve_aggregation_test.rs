//! WI-833: cpp-gen's type-lowering realization readers (`TypeMapping`,
//! `IncludeMapping`, `NamingConvention`) GRADUATE from `Refuse` to `Resolve`
//! (`read_facts_resolved`). A bodied mapping rule is now EVALUATED — its guard
//! honored — instead of the read refusing every bodied candidate (the WI-810
//! behavior this supersedes for these three functors). The key-priority
//! aggregation stays caller-side (`select_keyed_unique`), upgraded to:
//!   * DEDUP identical resolved rows (Resolve enumerates one mapping once per
//!     derivation — a duplicate is one mapping, not a conflict), and
//!   * reject a genuine per-key AMBIGUITY (two competing mappings under one key)
//!     loudly through `CppCodegenError`.
//!
//! This file covers the WI's matrix — passing/failing guards, duplicate answers,
//! overlay priority, and ambiguity — across all three readers, through their
//! public entry points. The Resolve mechanism itself (guard honored, floundered
//! solutions dropped) is pinned generically by `kb::extent`'s unit tests
//! (`read_facts_resolved_honors_a_passing_bodied_rule_guard` and siblings).

use super::common;

use anthill_cpp_gen::{
    cpp_base_host_type, cpp_host_type, emit_namespace_header, emit_traits_struct,
};
use common::load_kb_with;

// ── TypeMapping ──────────────────────────────────────────────────────

/// Resolve the cpp base host type for a fresh anthill type `ty` from `body`
/// (spliced into a namespace importing the realization vocabulary). `Money` is
/// not a stdlib type, so `body` controls every mapping for it.
fn money_base(body: &str, ty: &str) -> Result<Option<String>, String> {
    let source = format!(
        r#"
        namespace test.wi833.tm
          import anthill.realization.{{TypeMapping}}
          import anthill.prelude.{{Bool, String}}
          import anthill.prelude.Option.{{some, none}}
          {body}
        end
    "#
    );
    let mut kb = load_kb_with(&source);
    cpp_base_host_type(&mut kb, ty).map_err(|e| e.message)
}

#[test]
fn type_mapping_passing_guard_applies() {
    // A guarded base overlay whose guard HOLDS contributes its host type.
    let host = money_base(
        r#"
          entity FastMath(on: Bool)
          fact FastMath(on: true)
          rule TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money",
                           host_type: "float", lift: none, lower: none)
            :- FastMath(on: true)
        "#,
        "Money",
    )
    .expect("a guarded TypeMapping resolves, never refuses");
    assert_eq!(
        host.as_deref(),
        Some("float"),
        "passing guard → the mapping applies"
    );
}

#[test]
fn type_mapping_failing_guard_contributes_nothing() {
    // The same rule with a FAILING guard resolves no row — `Money` has no base.
    let host = money_base(
        r#"
          entity FastMath(on: Bool)
          fact FastMath(on: false)
          rule TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money",
                           host_type: "float", lift: none, lower: none)
            :- FastMath(on: true)
        "#,
        "Money",
    )
    .expect("a guarded TypeMapping resolves, never refuses");
    assert_eq!(host, None, "failing guard → no mapping resolves");
}

#[test]
fn type_mapping_duplicate_answers_are_deduped_not_ambiguous() {
    // A rule whose guard succeeds via MULTIPLE derivations enumerates the SAME
    // mapping row several times. Deduplicated to one — NOT rejected as ambiguous
    // (identical rows are one mapping). This is the duplicate-vs-conflict line.
    let host = money_base(
        r#"
          entity Cond(tag: String)
          fact Cond(tag: "a")
          fact Cond(tag: "b")
          -- `Cond(tag: ?t)` succeeds twice, so this resolves Money -> float twice.
          rule TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money",
                           host_type: "float", lift: none, lower: none)
            :- Cond(tag: ?t)
        "#,
        "Money",
    )
    .expect("identical resolved rows dedup, never ambiguous");
    assert_eq!(
        host.as_deref(),
        Some("float"),
        "duplicate answers collapse to one mapping"
    );
}

#[test]
fn type_mapping_competing_answers_at_one_key_are_ambiguous() {
    // Two DISTINCT host types under the SAME key (`none`) — no deterministic pick
    // exists, so selection rejects it loudly (never the old silent first-wins).
    let err = money_base(
        r#"
          fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money",
                           host_type: "float", lift: none, lower: none)
          fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money",
                           host_type: "double", lift: none, lower: none)
        "#,
        "Money",
    )
    .expect_err("two competing base mappings for one key are ambiguous");
    assert!(err.contains("ambiguous"), "names the ambiguity: {err}");
    assert!(err.contains("Money"), "names the anthill type: {err}");
    assert!(
        err.contains("float") && err.contains("double"),
        "lists the competing host types: {err}"
    );
}

#[test]
fn type_mapping_guarded_overlay_shadows_base_only_when_its_guard_holds() {
    // Overlay priority THROUGH a guard: a profile-keyed overlay whose guard holds
    // shadows the base under the active profile; when the guard fails the query
    // falls through to the base. Combines WI-089(a) priority with WI-833 guards.
    let ladder = |fast_math: bool| {
        let toggle = if fast_math {
            "fact FastMath(on: true)"
        } else {
            "fact FastMath(on: false)"
        };
        let source = format!(
            r#"
            namespace test.wi833.overlay
              import anthill.realization.{{TypeMapping}}
              import anthill.prelude.{{Bool}}
              import anthill.prelude.Option.{{some, none}}

              entity FastMath(on: Bool)
              {toggle}

              fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money",
                               host_type: "Base", lift: none, lower: none)
              rule TypeMapping(lang: some("cpp"), key: some("cpp20-stl"), anthill_type: "Money",
                               host_type: "Overlay", lift: none, lower: none)
                :- FastMath(on: true)
            end
        "#
        );
        let mut kb = load_kb_with(&source);
        // Under the cpp20-stl profile, no binding (declared-signature position).
        cpp_host_type(&mut kb, "Money", Some("cpp20-stl"), None)
            .expect("guarded overlay resolves")
            .expect("Money has at least a base")
    };

    assert_eq!(
        ladder(true),
        "Overlay",
        "guard holds → the profile overlay shadows the base"
    );
    assert_eq!(
        ladder(false),
        "Base",
        "guard fails → selection falls through to the base"
    );
}

// ── IncludeMapping ───────────────────────────────────────────────────

/// Emit `test.wi833.inc`'s header from `body`. `Widget(size: Int64)` lowers to
/// `int64_t size;`, so the include scan sees `int64_t` and fires every probe
/// keyed on that spelling — the stdlib `<cstdint>` plus any `body` adds.
fn emit_inc_header(body: &str) -> Result<String, String> {
    let source = format!(
        r#"
        namespace test.wi833.inc
          import anthill.prelude.{{Int64, Bool, String}}
          import anthill.realization.IncludeMapping

          entity Widget(size: Int64)
          {body}
        end
    "#
    );
    let mut kb = load_kb_with(&source);
    emit_namespace_header(&mut kb, "test.wi833.inc").map_err(|e| e.message)
}

#[test]
fn include_mapping_guard_gates_a_probe() {
    // A guarded extra include on `int64_t`. Present iff its guard holds; the
    // stdlib `<cstdint>` (a plain fact) is always there — so a missing extra is
    // the guard, not a broken read.
    let with_guard = emit_inc_header(
        r##"
          entity FastMath(on: Bool)
          fact FastMath(on: true)
          rule IncludeMapping(lang: "cpp", host_type: "int64_t", include: "#include <extra_int>")
            :- FastMath(on: true)
        "##,
    )
    .expect("guarded IncludeMapping resolves, never refuses");
    assert!(
        with_guard.contains("#include <cstdint>"),
        "plain base fact still reads:\n{with_guard}"
    );
    assert!(
        with_guard.contains("#include <extra_int>"),
        "guard holds → extra include:\n{with_guard}"
    );

    let without_guard = emit_inc_header(
        r##"
          entity FastMath(on: Bool)
          fact FastMath(on: false)
          rule IncludeMapping(lang: "cpp", host_type: "int64_t", include: "#include <extra_int>")
            :- FastMath(on: true)
        "##,
    )
    .expect("guarded IncludeMapping resolves, never refuses");
    assert!(
        without_guard.contains("#include <cstdint>"),
        "plain base fact still reads:\n{without_guard}"
    );
    assert!(
        !without_guard.contains("#include <extra_int>"),
        "guard fails → no extra include:\n{without_guard}"
    );
}

#[test]
fn include_mapping_duplicate_probes_render_once() {
    // A rule whose guard succeeds via MULTIPLE derivations resolves the SAME
    // probe several times. The probe set dedups, so the directive renders ONCE —
    // `Includes::needed` keys on the probe index, so un-deduped duplicates would
    // emit the same `#include` twice.
    let header = emit_inc_header(
        r##"
          entity Cond(tag: String)
          fact Cond(tag: "a")
          fact Cond(tag: "b")
          rule IncludeMapping(lang: "cpp", host_type: "int64_t", include: "#include <extra_int>")
            :- Cond(tag: ?t)
        "##,
    )
    .expect("guarded IncludeMapping resolves");
    assert_eq!(
        header.matches("#include <extra_int>").count(),
        1,
        "duplicate resolved probes render exactly one directive:\n{header}"
    );
}

// ── NamingConvention ─────────────────────────────────────────────────

/// Emit `test.wi833.naming.Sensor`'s traits struct from `body`. A carrier
/// binding lets `self: Sensor` lower, so emission reaches carrier-dispatch body
/// synthesis — which reads the cpp `NamingConvention` (`cpp_method_name`). The
/// stdlib always ships one cpp convention (snake_case -> camelCase).
fn emit_sensor_traits(body: &str) -> Result<String, String> {
    let source = format!(
        r#"
        namespace test.wi833.naming
          import anthill.prelude.{{Unit, String, Option, Bool}}
          import anthill.realization.{{Implementation, CarrierBinding, NamingConvention}}

          sort Sensor
            operation ping(self: Sensor) -> Unit
          end

          fact Implementation(
            target:        "test.wi833.naming.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor", host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       none)
          {body}
        end
    "#
    );
    let mut kb = load_kb_with(&source);
    emit_traits_struct(&mut kb, "test.wi833.naming.Sensor").map_err(|e| e.message)
}

#[test]
fn naming_convention_duplicate_of_the_stdlib_is_deduped() {
    // A guarded rule that re-derives the stdlib's own (snake_case, camelCase)
    // convention — via a two-solution guard — is a DUPLICATE of the stdlib fact,
    // not a competitor. Deduped, so emission succeeds and `ping` stays `ping`
    // (identity under camelCase). Pre-WI-833 this bodied rule was refused loudly.
    let traits = emit_sensor_traits(
        r#"
          entity Cond(tag: String)
          fact Cond(tag: "a")
          fact Cond(tag: "b")
          rule NamingConvention(language: "cpp", method_case: "camelCase", source_case: "snake_case")
            :- Cond(tag: ?t)
        "#,
    )
    .expect("a duplicate NamingConvention dedups, emission succeeds");
    assert!(
        traits.contains("self->ping()"),
        "convention read, dispatch emitted:\n{traits}"
    );
}

#[test]
fn naming_convention_failing_guard_leaves_the_stdlib_convention() {
    // A competing PascalCase convention behind a FAILING guard contributes
    // nothing — only the stdlib snake_case -> camelCase remains, so emission
    // succeeds. Proves the guard is evaluated (the rule is excluded, not fused
    // in as a second convention).
    let traits = emit_sensor_traits(
        r#"
          entity Toggle(on: Bool)
          fact Toggle(on: false)
          rule NamingConvention(language: "cpp", method_case: "PascalCase", source_case: "snake_case")
            :- Toggle(on: true)
        "#,
    )
    .expect("a failing-guard convention is excluded, emission succeeds");
    assert!(
        traits.contains("self->ping()"),
        "stdlib convention applies:\n{traits}"
    );
}

#[test]
fn naming_convention_competing_conventions_are_ambiguous() {
    // A PascalCase convention behind a HOLDING guard resolves alongside the
    // stdlib camelCase one — two distinct conventions, no deterministic pick, so
    // `cpp_method_name` rejects it loudly (the `realizes_effect` <=1 discipline).
    let err = emit_sensor_traits(
        r#"
          entity Toggle(on: Bool)
          fact Toggle(on: true)
          rule NamingConvention(language: "cpp", method_case: "PascalCase", source_case: "snake_case")
            :- Toggle(on: true)
        "#,
    )
    .expect_err("two competing cpp NamingConventions are ambiguous");
    assert!(err.contains("ambiguous"), "names the ambiguity: {err}");
    assert!(err.contains("NamingConvention"), "names the functor: {err}");
    assert!(
        err.contains("PascalCase") && err.contains("camelCase"),
        "lists the competing conventions: {err}"
    );
}
