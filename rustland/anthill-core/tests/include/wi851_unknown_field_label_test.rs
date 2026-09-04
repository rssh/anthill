//! WI-851 — an entity constructor's named-argument list is CLOSED: a label that names
//! no declared field is refused.
//!
//! MEASURED before the fix: every constructor position below LOADED CLEAN. The extra
//! field was not inert — `canonicalize_record_named_args` (`kb/resolve.rs`) sorts an
//! unknown label LAST (`unwrap_or(usize::MAX)`) and it rides into the hash-consed term
//! as a real named arg, while `check_constructor_iter` iterates the DECLARED fields and
//! looks each one up among the supplied args, so the extra one is never visited and its
//! value's type is never checked. `mk(a: 1, bogus: 2)` and `mk(a: 1)` are therefore
//! DIFFERENT terms, and a query written the other way silently fails to match.
//!
//! ONE check closes all of it, in `Loader::convert_term`'s constructor arm beside the
//! POSITIONAL over-arity check that was already there. Deliberately NOT one check per
//! producer — that is the WI-805 / WI-839 mistake, and the operation-body cases
//! (`op_body_constructor`, `nested_constructor_in_operation_body`) were the ones a
//! producer list would have missed: they reach the same loader arm, which is why no
//! second site in the typer is needed.
//!
//! This is the member the WI-805 (tuple labels) / WI-808 (entity field names) / WI-809
//! (named-argument lists) family was missing. Those made every label list DISTINCT;
//! this makes an entity's label list CLOSED.

use crate::common::try_load_kb_with;

/// Every refusal must name BOTH the entity and the offending label. Asserting the
/// MESSAGE, not just "some error": a count-only assertion would pass on an
/// implementation that rejected these programs for an unrelated reason — and for the
/// rule-body and constraint cases the wrong implementation is a tempting one (reading
/// the unknown label as an unbound variable).
fn assert_refused(src: &str, entity: &str, label: &str, why: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: {why}"),
        Err(errs) => errs,
    };
    let needle = format!("'{entity}' has no field '{label}'");
    assert!(
        errs.iter().any(|e| e.contains(&needle)),
        "{why}; expected a diagnostic containing {needle:?}, got: {errs:?}",
    );
}

const BOX: &str = r#"
  sort Box
    entity mk(a: Int64)
    entity outer(inner: Int64)
  end
"#;

fn with_box(item: &str) -> String {
    format!("namespace test.wi851\n  import anthill.prelude.{{Int64}}\n{BOX}{item}\nend\n")
}

#[test]
fn fact_head() {
    assert_refused(
        &with_box("  fact mk(a: 1, bogus: 2)"),
        "mk",
        "bogus",
        "a fact head's unknown field label",
    );
}

/// The positional path reaches the same check: the desugar assigns declared fields to
/// the positionals, so what is left over is still the user's undeclared label.
#[test]
fn fact_head_positional_plus_unknown_label() {
    assert_refused(
        &with_box("  fact mk(1, bogus: 2)"),
        "mk",
        "bogus",
        "a positional fact with an extra named label",
    );
}

#[test]
fn op_body_constructor() {
    assert_refused(
        &with_box("  sort D\n    operation go() -> Box = mk(a: 1, bogus: 2)\n  end"),
        "mk",
        "bogus",
        "a constructor in an operation body",
    );
}

/// NESTED, so the check cannot be one that only inspects a term's outermost functor.
#[test]
fn nested_constructor_in_operation_body() {
    assert_refused(
        &with_box("  sort D\n    operation go() -> Box = outer(inner: mk(a: 1, bogus: 2))\n  end"),
        "mk",
        "bogus",
        "a constructor nested inside another constructor's argument",
    );
}

#[test]
fn rule_head() {
    assert_refused(
        &with_box(
            "  sort Flag\n    entity on(v: Int64)\n  end\n  rule mk(a: ?x, bogus: 2) :- on(v: 1)",
        ),
        "mk",
        "bogus",
        "a rule head's unknown field label",
    );
}

/// A rule BODY atom is a PATTERN, not a value — the var-fill path. It must be refused
/// too: an undeclared label there matches nothing that can ever be asserted.
#[test]
fn rule_body_atom() {
    assert_refused(
        &with_box("  rule r(?x) :- mk(a: ?x, bogus: ?y)"),
        "mk",
        "bogus",
        "a rule-body pattern's unknown field label",
    );
}

#[test]
fn constraint_body() {
    assert_refused(
        &with_box("  constraint c :- mk(a: ?x, bogus: ?y)"),
        "mk",
        "bogus",
        "a constraint body's unknown field label",
    );
}

/// CONTROL 1 — a well-formed fact still loads. Without this, every test above would
/// pass on an implementation that simply refused all constructors.
#[test]
fn a_well_formed_constructor_still_loads() {
    try_load_kb_with(&with_box("  fact mk(a: 1)"))
        .unwrap_or_else(|errs| panic!("a declared field must still load: {errs:?}"));
}

/// CONTROL 2 — partial named args still load. The loader FILLS the missing fields
/// (WI-716), and that fill must not be mistaken for an unknown label.
#[test]
fn a_partial_named_arg_list_still_loads() {
    try_load_kb_with(&format!(
        "namespace test.wi851.partial\n  import anthill.prelude.{{Int64}}\n\
         \x20 sort Pair\n    entity mk(a: Int64, b: Int64)\n  end\n  fact mk(a: 1)\nend\n"
    ))
    .unwrap_or_else(|errs| panic!("a partial named-arg list must still load: {errs:?}"));
}

/// CONTROL 3 — an ORDERED PRODUCT (named tuple) carries the AUTHOR's labels, not a
/// declared schema, so it must be exempt. This is the case that would break if the
/// check gated on "has named args" instead of "has a declared field schema".
#[test]
fn a_named_tuple_with_arbitrary_labels_still_loads() {
    try_load_kb_with(
        r#"
namespace test.wi851.tuple
  import anthill.prelude.{Int64, String}
  sort D
    operation go() -> (whatever: Int64, another: String) = (whatever: 1, another: "x")
  end
end
"#,
    )
    .unwrap_or_else(|errs| panic!("a named tuple's own labels must still load: {errs:?}"));
}

/// A ZERO-FIELD entity's label list is CLOSED AT ZERO — it accepts no labels at all.
///
/// This is the case the first cut got wrong (/code-review). The gate read an EMPTY
/// declared list as "no schema" and exempted it, on the false premise that a zero-field
/// entity cannot be declared. The paren-less spelling is not only legal, it is what the
/// prelude uses (`entity nil`, `entity none`, `entity console`, `entity Nothing`), so
/// the exemption covered the two most-written constructors in the language.
#[test]
fn a_zero_field_entity_accepts_no_labels() {
    assert_refused(
        &with_box("  sort Flag\n    entity on\n  end\n  fact on(bogus: 1)"),
        "on",
        "bogus",
        "a user zero-field entity's label list is closed at zero",
    );
}

/// The prelude's own zero-field constructors, which the broken gate let through. Driven
/// through a NESTED position so this also pins that the check sees a constructor inside
/// a field value, not just at the top of a fact.
///
/// The namespaces are `…nil_ctor` / `…none_ctor`, NOT `…nil` / `…none`: a namespace whose
/// LAST SEGMENT equals a constructor's short name shadows it (WI-714), so the first cut
/// of this test resolved `nil` to the namespace and loaded clean — passing as a refusal
/// test would have, for entirely the wrong reason.
#[test]
fn prelude_zero_field_constructors_accept_no_labels() {
    assert_refused(
        r#"
namespace test.wi851.nil_ctor
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{nil}
  sort Box
    entity mk(xs: List)
  end
  fact mk(xs: nil(bogus: 1))
end
"#,
        "nil",
        "bogus",
        "`nil` declares no fields, so it accepts no labels",
    );
    assert_refused(
        r#"
namespace test.wi851.none_ctor
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{none}
  sort Box
    entity mk(v: Option)
  end
  fact mk(v: none(bogus: 1))
end
"#,
        "none",
        "bogus",
        "`none` declares no fields, so it accepts no labels",
    );
}

/// The refusal is LOCATED and not collapsed. A span-less `LoadError::Other` renders with
/// no `path:line:col`, and `dedup_load_errors` keys on the rendered string — so two
/// violations of the same entity+label anywhere in the load became ONE unlocatable
/// message (/code-review). Two sites must produce two errors, each carrying a position.
#[test]
fn each_violation_is_reported_with_its_own_location() {
    let errs = try_load_kb_with(&with_box(
        "  fact mk(a: 1, bogus: 2)\n  fact mk(a: 3, bogus: 4)",
    ))
    .err()
    .expect("both violations must be refused");
    let hits: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("'mk' has no field 'bogus'"))
        .collect();
    assert_eq!(
        hits.len(),
        2,
        "one error per violation, not one deduped message: {errs:?}"
    );
    for e in hits {
        assert!(
            e.split(':').next().is_some_and(|s| !s.trim().is_empty()) && e.contains(':'),
            "each refusal must carry a location: {e:?}",
        );
    }
}

/// CONTROL 4 — the stdlib loads. The blunt whole-corpus control: the check runs over
/// every constructor in every prelude/reflect file, so a wrong exemption shows up here
/// as a load failure rather than as a subtle behaviour change. (`try_load_kb_with`
/// loads the full stdlib alongside the source, so every test in this file is also
/// asserting this — stated once, explicitly, because it is the main risk of the change.)
#[test]
fn the_stdlib_still_loads() {
    try_load_kb_with("namespace test.wi851.empty\nend\n")
        .unwrap_or_else(|errs| panic!("the stdlib must still load: {errs:?}"));
}
