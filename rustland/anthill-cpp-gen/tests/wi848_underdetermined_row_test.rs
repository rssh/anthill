//! WI-848: what happens when a realization fact/rule leaves a REQUIRED field
//! under-determined — a fact that omits it, or a bodied rule head that leaves it
//! unconstrained.
//!
//! The loader var-fills such a field with a fresh variable, so `read_facts_resolved`
//! reifies it as a `Value::Term` wrapping a `Term::Var` — NOT a value-level
//! `Value::Var` (measured; pinned generically at the seam by
//! `kb::extent::read_facts_resolved_surfaces_an_underdetermined_field_as_a_term_var`).
//! `row_named_term` therefore receives it through its `Value::Term` arm, and the
//! loud `Value::Var` arm it once carried — whose doc claimed the trigger was exactly
//! this omitted-required-field case — is UNREACHABLE and was removed (folded into a
//! single defensive non-term arm).
//!
//! Downstream, each of the three type-lowering readers treats the resulting
//! non-literal var-term per its own aggregation, which this file pins:
//!   * IncludeMapping (a probe SET): the string readers read a var-term as absent,
//!     so the row contributes NO probe — a correct program, clean emit.
//!   * TypeMapping (keyed, per-key unique): the under-determined row is skipped, so
//!     the type resolves to no base — `Ok(None)`, not an error.
//!   * NamingConvention (single-valued): the under-determined `method_case` reads as
//!     `None`, a pair DISTINCT from the stdlib's snake→camel, so the single-valued
//!     selector reports it AMBIGUOUS (loud) — the difference is the reader's
//!     `unique_or_ambiguous` discipline, not `row_named_term`.

use super::common;

use anthill_cpp_gen::{cpp_base_host_type, emit_namespace_header, emit_traits_struct};
use common::load_kb_with;

// ── IncludeMapping: a probe set — an under-determined row adds no probe ──

/// Emit `test.wi848.inc`'s header. `Widget(size: Int64)` lowers to `int64_t`, so
/// the stdlib `int64_t → <cstdint>` probe always fires — a fixed witness that the
/// include read RAN, so a missing extra probe is the under-determined row, not a
/// broken read.
fn emit_inc(body: &str) -> Result<String, String> {
    let source = format!(
        r#"
        namespace test.wi848.inc
          import anthill.prelude.{{Int64, Bool, String}}
          import anthill.realization.IncludeMapping

          entity Widget(size: Int64)
          {body}
        end
    "#
    );
    let mut kb = load_kb_with(&source);
    emit_namespace_header(&mut kb, "test.wi848.inc").map_err(|e| e.message)
}

#[test]
fn include_mapping_fact_omitting_required_include_contributes_no_probe() {
    // A fact omitting the required `include`. The loader var-fills it; the resolved
    // row's `include` is a term-var, read as absent — so the row contributes NO
    // probe. Proven by comparing against a baseline with no such fact: adding the
    // malformed fact leaves the header BYTE-IDENTICAL (a garbage probe would show as
    // an extra `#include` line, failing the equality). Emission also succeeds — the
    // under-determined field reaches the `Value::Term` arm, never the removed
    // defensive error. (The stdlib `int64_t → <cstdint>` probe present in the
    // baseline witnesses that the include read genuinely ran.)
    let baseline = emit_inc("").expect("baseline emits cleanly");
    let with_malformed = emit_inc(r#"fact IncludeMapping(lang: "cpp", host_type: "int64_t")"#)
        .expect("an IncludeMapping missing `include` contributes no mapping, not an error");
    assert!(
        baseline.contains("#include <cstdint>"),
        "stdlib probe present in baseline:\n{baseline}"
    );
    assert_eq!(
        with_malformed, baseline,
        "a fact missing the required `include` adds no probe — header identical to baseline"
    );
}

#[test]
fn include_mapping_rule_head_leaving_include_unconstrained_contributes_no_probe() {
    // The bodied-rule spelling: a rule head that leaves `include` an unconstrained
    // var. Same outcome, isolated against a baseline that carries the SAME guard
    // entities but no IncludeMapping rule — so the rule is the only variable, and the
    // header is unchanged (its `include` term-var reads as absent → no probe).
    let guard = "entity Toggle(on: Bool)\n          fact Toggle(on: true)";
    let baseline = emit_inc(guard).expect("baseline emits cleanly");
    let with_malformed = emit_inc(&format!(
        "{guard}\n          rule IncludeMapping(lang: \"cpp\", host_type: \"int64_t\", include: ?i)\
         \n            :- Toggle(on: true)"
    ))
    .expect("an unconstrained-head IncludeMapping contributes no mapping, not an error");
    assert!(
        baseline.contains("#include <cstdint>"),
        "stdlib probe present in baseline:\n{baseline}"
    );
    assert_eq!(
        with_malformed, baseline,
        "a rule head leaving `include` unconstrained adds no probe — header identical to baseline"
    );
}

// ── TypeMapping: keyed — an under-determined base maps nothing ──────────

#[test]
fn type_mapping_fact_omitting_required_host_type_maps_nothing() {
    // `Money` gets a base TypeMapping that omits the required `host_type`. The
    // resolved row's `host_type` is a term-var, read as absent, so no base resolves.
    // `cpp_base_host_type` returns `Ok(None)`, never a loud error — `Money` simply
    // has no cpp base.
    let source = r#"
        namespace test.wi848.tm
          import anthill.realization.TypeMapping
          import anthill.prelude.{Bool, String}
          import anthill.prelude.Option.{some, none}

          fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "Money", lift: none, lower: none)
        end
    "#;
    let mut kb = load_kb_with(source);
    let host = cpp_base_host_type(&mut kb, "Money")
        .expect("a TypeMapping missing `host_type` contributes no mapping, not an error");
    assert_eq!(host, None, "an under-determined host_type maps nothing");
}

// ── NamingConvention: single-valued — under-determined competes, loudly ─

/// Emit `test.wi848.naming.Sensor`'s traits struct. A carrier binding lets
/// `self: Sensor` lower, so emission reaches carrier-dispatch body synthesis, which
/// reads the cpp `NamingConvention`. The stdlib always ships one (snake→camel).
fn emit_sensor_traits(body: &str) -> Result<String, String> {
    let source = format!(
        r#"
        namespace test.wi848.naming
          import anthill.prelude.{{Unit, String, Option, Bool}}
          import anthill.realization.{{Implementation, CarrierBinding, NamingConvention}}
          import anthill.prelude.Option.{{none}}

          sort Sensor
            operation ping(self: Sensor) -> Unit
          end

          fact Implementation(
            target:        "test.wi848.naming.Sensor",
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
    emit_traits_struct(&mut kb, "test.wi848.naming.Sensor").map_err(|e| e.message)
}

#[test]
fn naming_convention_omitting_required_method_case_is_ambiguous_not_silent() {
    // A cpp NamingConvention omitting the required `method_case`. Its resolved row's
    // `method_case` is a term-var, read as `None` — a `(snake_case, None)` pair
    // DISTINCT from the stdlib's `(snake_case, camelCase)`. The convention is
    // single-valued, so `unique_or_ambiguous` rejects the two competing pairs
    // LOUDLY rather than silently picking one (or emitting a wrong `ping` spelling).
    // Unlike the probe-set / keyed readers above, this reader does not skip an
    // under-determined row — the difference is its aggregation, not `row_named_term`.
    let err =
        emit_sensor_traits(r#"fact NamingConvention(language: "cpp", source_case: "snake_case")"#)
            .expect_err(
                "an under-determined cpp convention competes with the stdlib's — ambiguous",
            );
    assert!(err.contains("ambiguous"), "names the ambiguity: {err}");
    assert!(err.contains("NamingConvention"), "names the functor: {err}");
}
