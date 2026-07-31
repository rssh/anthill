//! WI-889 — a host-supplied `const` reaches the backends through a `const_map` clause,
//! the const-level peer of `operation_map` (WI-876). Before this, the three `Float`
//! IEEE specials (`infinity`/`negativeInfinity`/`nan`) were keyed by HARDCODED
//! qualified name in every backend — `eval/builtins.rs`'s `register_if_present` in the
//! rust runtime and `render_as_float_special` in cpp-gen, the last of WI-886's four
//! hand-written per-carrier tables.
//!
//! What this suite pins:
//!   * the stdlib `Float` `const_map` lands as `anthill.realization.ConstMapping` facts,
//!     the flat queryable form (mirror of `a_binding_blocks_operation_map_lands_as_facts`);
//!   * the WI-876 KIND CHECK's guarantee survives the widened vocabulary — a `const_map`
//!     target must be a `const`, so a mapping cannot attach a host value to an operation
//!     or an entity constructor, just as `operation_map` cannot attach to a non-operation;
//!   * the three specials still EVALUATE (rust), now through the data channel;
//!   * both runtime failure modes stay LOUD (unknown key; a non-nullary value source).
//!
//! The cpp side (the same three realized from the cpp `const_map`) is pinned by
//! `anthill-cpp-gen`'s `wi533_const_test` — anthill-core loads only the rust bindings.
//!
//! Reference: `stdlib/anthill/realization/realization.anthill` (`ConstMapping`),
//! `rustland/anthill-stl/anthill/float.anthill`, `docs/kernel-language.md` §10.2.

use anthill_core::eval::Value;

/// A carrier declaring one of EACH kind a qualified `<ns>.<Sort>.<member>` name can
/// resolve to — a `const`, an operation, and an entity constructor — so a `const_map`
/// entry can be aimed at each and the kind check exercised. `answer` is the only valid
/// target; `squish` and `widget` are the traps.
fn const_mapping_program(ns: &str, entry: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         sort Widget\n    import anthill.prelude.{{Int64}}\n    \
         entity widget(v: Int64)\n    \
         operation squish(a: Widget, b: Widget) -> Int64\n    \
         const answer: Int64\n  end\n  \
         provides Widget language rust\n    artifact \"nowhere.rs\"\n    \
         const_map {{ {entry} }}\n  end\nend\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// Build the interpreter for a program the way `registration_err` does in the wi876
/// suite: load (clean), then run the eval-side `register_standard_builtins`, which is
/// where `register_const_mappings` lives. Returns the registration error string.
fn registration_err(src: &str) -> String {
    let kb = crate::common::load_kb_with(src);
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    match anthill_core::eval::builtins::register_standard_builtins(&mut interp) {
        Ok(()) => panic!("expected a registration error, but registration succeeded"),
        Err(e) => format!("{e:?}"),
    }
}

/// The stdlib `Float` `const_map` reaches the KB as `ConstMapping` facts — the same
/// flat, queryable shape `operation_map` uses, so the runtime's registry reads facts
/// rather than a hardcoded list. The rust host keys the three IEEE specials to their
/// `HOST_FNS` value sources.
#[test]
fn stdlib_float_const_map_lands_as_facts() {
    let kb = crate::common::load_kb_with("\nnamespace wi889.facts\n  sort S\n  end\nend\n");
    let host_fn = |const_qn: &str| -> String {
        kb.host_const_mappings()
            .iter()
            .find(|m| m.const_qn == const_qn && m.lang == "rust")
            .unwrap_or_else(|| panic!("no rust const mapping for {const_qn}"))
            .host_fn
            .clone()
    };
    assert_eq!(host_fn("anthill.prelude.Float.infinity"), "float_infinity");
    assert_eq!(host_fn("anthill.prelude.Float.negativeInfinity"), "float_negative_infinity");
    assert_eq!(host_fn("anthill.prelude.Float.nan"), "float_nan");
}

/// RESOLVING IS NOT ENOUGH — a `const_map` target must be a `const`. An operation is a
/// qualified `<ns>.<Sort>.<operation>` name, so it resolves; the MIRROR of WI-876's
/// operation-side kind check refuses it, keeping the guarantee that a host value source
/// cannot be attached to an operation (whose channel is `operation_map`).
#[test]
fn a_const_map_over_an_operation_is_refused_at_load() {
    let errs = load_errs(&const_mapping_program("wi889.op", "squish: \"float_infinity\""));
    let joined = errs.join("\n");
    assert!(joined.contains("wi889.op.Widget.squish"), "names the target: {joined}");
    assert!(joined.contains("not a `const`"), "says what is wrong: {joined}");
}

/// The same guard against an ENTITY CONSTRUCTOR — also a resolving qualified name, and
/// the exact shape WI-876 MEASURED for `operation_map` (a comparison registered against
/// the constructor). Aimed at a const's clause it is the same defect one vocabulary over.
#[test]
fn a_const_map_over_an_entity_constructor_is_refused_at_load() {
    let errs = load_errs(&const_mapping_program("wi889.ctor", "widget: \"float_infinity\""));
    let joined = errs.join("\n");
    assert!(joined.contains("not a `const`"), "says what is wrong: {joined}");
}

/// A `const_map` for a const the carrier never DECLARED is refused at LOAD — by the
/// loader, which can see it, so `anthill load`/`check` say so. The clause says what
/// BACKS a const; it does not bring one into existence.
#[test]
fn a_const_map_for_an_undeclared_const_is_refused_at_load() {
    let errs = load_errs(&const_mapping_program("wi889.badc", "missing: \"float_infinity\""));
    let joined = errs.join("\n");
    assert!(joined.contains("wi889.badc.Widget.missing"), "names the const: {joined}");
    assert!(joined.contains("declares no const"), "says what is wrong: {joined}");
}

/// `const_map` under `language anthill` is refused rather than IGNORED — the grammar
/// admits the clause in every binding block, and an anthill implementation is a const
/// BODY, not a host binding. Refusing avoids the loads-clean/registers-nothing shape.
#[test]
fn a_const_map_under_language_anthill_is_refused() {
    let errs = load_errs(
        "\nnamespace wi889.anthlang\n  \
         sort Widget\n    import anthill.prelude.{Int64}\n    \
         const answer: Int64\n  end\n  \
         provides Widget language anthill\n    \
         const_map { answer: \"float_infinity\" }\n  end\nend\n",
    );
    assert!(
        errs.join("\n").contains("not meaningful"),
        "should refuse the clause: {errs:?}",
    );
}

/// An UNQUOTED host value is refused at the producer, so every emitted fact is
/// well-shaped and its readers need no "malformed?" arm — the same guard `operation_map`
/// draws (WI-876), for the same measured reason (an unquoted key produced a non-string
/// `host_fn` the reader dropped, and the mapping VANISHED silently).
#[test]
fn an_unquoted_const_map_value_is_refused_at_load() {
    let errs = load_errs(&const_mapping_program("wi889.unquoted", "answer: not_a_string"));
    let joined = errs.join("\n");
    assert!(joined.contains("answer"), "names the entry: {joined}");
    assert!(joined.contains("STRING"), "says what is wrong: {joined}");
}

/// The headline: the three `Float` IEEE specials still evaluate — now reached as DATA
/// through the `const_map` channel, exactly as `pi`/`e`/`tau` reach eval through
/// `operation_map`. This is `wi532`'s driver, re-asserted against the new mechanism.
#[test]
fn the_float_ieee_specials_evaluate_through_the_const_map_channel() {
    let mut i = crate::common::interp_for(
        "\nnamespace wi889.eval\n  \
         import anthill.prelude.Float.{infinity, negativeInfinity, nan}\n  \
         operation posInf() -> Float = infinity\n  \
         operation negInf() -> Float = negativeInfinity\n  \
         operation theNan() -> Float = nan\nend\n",
    );
    match i.call("wi889.eval.posInf", &[]).expect("posInf") {
        Value::Float(v) => assert!(v.is_infinite() && v > 0.0, "got {v}"),
        other => panic!("expected +∞, got {other:?}"),
    }
    match i.call("wi889.eval.negInf", &[]).expect("negInf") {
        Value::Float(v) => assert!(v.is_infinite() && v < 0.0, "got {v}"),
        other => panic!("expected -∞, got {other:?}"),
    }
    match i.call("wi889.eval.theNan", &[]).expect("theNan") {
        Value::Float(v) => assert!(v.is_nan(), "got {v}"),
        other => panic!("expected NaN, got {other:?}"),
    }
}

/// A `const_map` naming a host value the RUNTIME does not have stays the runtime's to
/// answer — loud there, naming the key, rather than a silently unregistered const that
/// would later misreport as a value-unavailable const. The peer of wi876's
/// `an_unknown_host_function_is_loud_at_registration`.
#[test]
fn an_unknown_const_host_value_is_loud_at_registration() {
    let err = registration_err(&const_mapping_program("wi889.badfn", "answer: \"no_such_host_value\""));
    assert!(err.contains("no_such_host_value"), "names the key: {err}");
    assert!(err.contains("wi889.badfn.Widget.answer"), "names the const: {err}");
}

/// A const's value source must be NULLARY — `force_const` invokes it with no args. A
/// `host_fn` that takes arguments cannot be one; caught at registration, the earliest
/// point that knows the host function's arity. (`ordered_compare` is a real key of
/// arity 2.)
#[test]
fn a_non_nullary_host_value_for_a_const_is_loud_at_registration() {
    let err = registration_err(&const_mapping_program("wi889.arity", "answer: \"ordered_compare\""));
    assert!(err.contains("wi889.arity.Widget.answer"), "names the const: {err}");
    assert!(err.contains("NULLARY"), "says what is wrong: {err}");
}
