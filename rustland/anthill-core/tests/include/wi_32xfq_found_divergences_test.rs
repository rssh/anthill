//! WI-20260923-32XFQ — the divergences its consolidation found and did NOT merge, each
//! decided by a program rather than by reading.
//!
//! The consolidation kept two decodes apart that it could not prove equal: the provision
//! relation's SPEC-BASE decode and its CARRIER decode each had a second spelling. Both
//! second spellings reproduced as silent wrong answers — a provision that every reader
//! should see went invisible to the dot-member resolver — and both are fixed; the third
//! suspicion (positional bindings missing from the symbol-keyed σ) did not reproduce,
//! and its section pins why. Each test states its back-out at its own site.

use crate::common::{assert_refused_naming, interp_for, try_load_kb_with};
use anthill_core::eval::Value;

// ── A user sort named `SortView` is not the reflect view wrapper ──────────────────────
//
// The provision relation's `spec` field is either a bare spec reference or the reflect
// wrapper `anthill.reflect.SortView(base, bindings…)`, and every reader decides which by
// asking whether the functor IS that wrapper. The question was asked by NAME: a dotted
// suffix (`<anything>.SortView`) in the typer's `is_sort_view_functor`, the last segment
// (`SortView`) in `load::provides_spec_base_sym`. So a spec the author called `SortView`
// — in any namespace, or at the top level — was read as the wrapper, its "base" looked for
// in a positional slot a bare spec does not have, and its provision decoded as nothing.

/// `Widget provides <spec>`, where `<spec>` has a defaulted member `describe`, reached by a
/// dot-call on a `Widget` — the path through the provision relation that
/// `find_spec_op_for_provided_sort` resolves. `go()` returns what the dispatched default
/// returns.
fn provided_spec_program(namespace: Option<&str>, spec: &str) -> String {
    let body = format!(
        r#"
  import anthill.prelude.{{Int64}}

  sort {spec}
    operation describe(x: {spec}) -> Int64 = 7
  end

  sort Widget provides {spec}
    entity widget(n: Int64)
  end

  operation go() -> Int64 = widget(n: 1).describe()

  operation via_spec(s: {spec}) -> Int64 = s.describe()
  operation go_via_spec() -> Int64 = via_spec(widget(n: 2))
"#
    );
    match namespace {
        Some(ns) => format!("namespace {ns}\n{body}\nend\n"),
        None => body,
    }
}

fn go(namespace: Option<&str>, spec: &str) -> i64 {
    run(namespace, spec, "go")
}

fn run(namespace: Option<&str>, spec: &str, op: &str) -> i64 {
    let mut interp = interp_for(&provided_spec_program(namespace, spec));
    let entry = match namespace {
        Some(ns) => format!("{ns}.{op}"),
        None => op.to_string(),
    };
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` over a provided `{spec}` must run to an Int64: {other:?}"),
    }
}

/// A NAMESPACED user sort called `SortView`. MEASURED before the fix: the load refused
/// `widget(n: 1).describe()` with "expected operation declared on the receiver's sort, got
/// no such member (dot dispatch)" — `Widget provides wi32xfq.sv.SortView` had been decoded
/// as the wrapper `anthill.reflect.SortView` with no base, i.e. as no provision at all.
///
/// BACK-OUTS, MEASURED — each restores one spelling in `typing::is_sort_view_functor`, the
/// one discriminant every decoder now asks: the dotted suffix (`anything.SortView`, the
/// typer's own until this fix) fails this row and the namespaced half of the spec-typed row;
/// the last segment (the loader's `provides_spec_base_sym` spelling, which also takes a
/// dotless `SortView`) fails those and the top-level row as well. Restoring the old
/// spelling in `provides_spec_base_sym` ALONE passes every row: the readers these rows
/// drive decode provision rows, which ask the discriminant, not that function. The control
/// and the wrapper row pass both ways by design.
#[test]
fn a_namespaced_sort_named_sort_view_is_provided_like_any_other() {
    assert_eq!(go(Some("wi32xfq.sv"), "SortView"), 7);
}

/// A TOP-LEVEL user sort called `SortView` (qualified name `SortView`, no dot). The typer's
/// suffix test did not match it — but `provides_spec_base_sym` did, by last segment, and
/// before this fix that was the decode the dot-member resolver and the transitive
/// `provides` walk read. MEASURED before the fix: refused exactly as the namespaced row.
/// Back-outs: see the namespaced row (this one fails under the last-segment spelling).
#[test]
fn a_top_level_sort_named_sort_view_is_provided_like_any_other() {
    assert_eq!(go(None, "SortView"), 7);
}

/// Through a parameter TYPED by the spec: `describe` on an abstract `SortView`-typed value,
/// dispatched on the runtime `Widget` — the value-directed half of the same provision.
/// Back-outs: see the namespaced row.
#[test]
fn a_value_typed_by_a_spec_named_sort_view_dispatches() {
    assert_eq!(run(Some("wi32xfq.svd"), "SortView", "go_via_spec"), 7);
    assert_eq!(run(None, "SortView", "go_via_spec"), 7);
}

/// THE CONTROL: the same program with the spec named anything else. Passes either way by
/// design — it is what the two rows above are measured against.
#[test]
fn the_same_provision_under_another_name_is_the_baseline() {
    assert_eq!(go(Some("wi32xfq.ctl"), "Viewish"), 7);
    assert_eq!(go(None, "Viewish"), 7);
    assert_eq!(run(Some("wi32xfq.ctld"), "Viewish", "go_via_spec"), 7);
    assert_eq!(run(None, "Viewish", "go_via_spec"), 7);
}

/// The wrapper itself is still the wrapper: a PARAMETERIZED provision is stored as
/// `anthill.reflect.SortView(Spec, T = …)`, and its binding still reaches the member's
/// signature — a wrong override is refused at those bindings. Passes either way by design:
/// it guards the identity test against answering `false` for the real wrapper, which would
/// drop every parameterized provision's bindings.
#[test]
fn the_reflect_wrapper_is_still_read_as_the_wrapper() {
    let src = r#"
namespace wi32xfq.wrap
  import anthill.prelude.{Int64, String}
  sort Sp
    sort T = ?
    operation get(x: Sp) -> T
  end
  sort Carrier provides Sp[T = Int64]
    entity carrier(n: Int64)
    operation get(x: Carrier) -> String = "no"
  end
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert_refused_naming(
        &errs,
        &["does not fit", "wi32xfq.wrap.Sp.get", "Int64"],
        "a wrong override at a `SortView`-wrapped provision's bindings",
    );
}

// ── A carrier applied at a parameter called `name` is still the carrier ──────────────
//
// `load::sort_ref_functor` read a `sort_ref`'s carrier and, for a `Fn`, preferred a child
// labelled `name` — the deep `sort_ref(name: Ref(S))` wrapper, which nothing has minted
// since WI-361. The only other `sort_ref` with such a child is an APPLIED carrier whose
// parameter is called `name`, and for it the preference answered the parameter's VALUE.
// Two dispatch readers (`impl_sorts_providing_spec`, `collect_provides_candidates`) read
// the bare head instead, so the one fact had two providers depending on who asked.

/// A provision written as the relation's own fact — the one spelling that puts an APPLIED
/// carrier in `sort_ref` — whose carrier `Box` has a parameter called `param`. `go()` runs
/// `Spec`'s default through a dot-call on a `Box`.
fn written_provision_program(ns: &str, param: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.reflect.{{SortProvidesInfo}}

  sort Spec
    operation describe(x: Spec) -> Int64 = 7
  end

  sort Box
    sort {param} = ?
    entity box(v: Int64)
  end

  fact SortProvidesInfo(sort_ref: Box[{param} = Int64], spec: Spec)

  operation go() -> Int64 = box(v: 1).describe()
end
"#
    )
}

fn go_written(ns: &str, param: &str) -> i64 {
    let mut interp = interp_for(&written_provision_program(ns, param));
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` with a `{param}` parameter must run to an Int64: {other:?}"),
    }
}

/// MEASURED before the fix: the load refused `box(v: 1).describe()` with "expected
/// operation declared on the receiver's sort, got no such member (dot dispatch)" — the
/// provision's carrier had been read as `Int64`, the value bound to `name`.
///
/// BACK-OUT, MEASURED: restoring the `name:`-child preference in `sort_ref_functor` fails
/// this test. The control below passes both ways by design.
#[test]
fn a_carrier_applied_at_a_parameter_called_name_is_still_the_carrier() {
    assert_eq!(go_written("wi32xfq.sr", "name"), 7);
}

/// THE CONTROL: the same written provision with the parameter called anything else.
#[test]
fn the_same_written_provision_under_another_parameter_name_is_the_baseline() {
    assert_eq!(go_written("wi32xfq.srctl", "nm"), 7);
}

// ── Positional bindings and the symbol-keyed σ — did NOT reproduce ─────────────────────
//
// Three σ builders keyed by the spec's parameter symbol (`check_override_refinement`,
// `check_instance_fact_op_signatures`, `requires_shadow_is_confusable`) read only a view's
// NAMED bindings, where `check_provider_requires` also pairs its positionals — so a
// provision written positionally looked as if it would fail open. It does not: since
// WI-20260923-N3W68 #9 the loader stores a positional TYPE-PARAMETER binding as the named
// binding of the parameter it fills (`KnowledgeBase::positional_param_slots`), so no stored
// view hands these builders one. These rows pin that, and pass either way by design — no
// code changed for them; they fail if storage ever stops normalizing, which is when the
// three builders would need the pairing after all.

/// `provides Sp[Int64]` is refused like `provides Sp[T = Int64]`: the override check reads
/// `T = Int64` either way.
#[test]
fn a_positional_provision_is_held_to_its_members_like_a_named_one() {
    for (ns, clause) in [
        ("wi32xfq.pos.named", "Sp[T = Int64]"),
        ("wi32xfq.pos.positional", "Sp[Int64]"),
    ] {
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Sp
    sort T = ?
    operation get(x: Sp) -> T
  end
  sort Carrier provides {clause}
    entity carrier(n: Int64)
    operation get(x: Carrier) -> String = "no"
  end
end
"#
        );
        let errs = try_load_kb_with(&src).err().unwrap_or_default();
        assert_refused_naming(
            &errs,
            &["does not fit", "the member returns `String`", "Int64"],
            &format!("`provides {clause}` with a `String`-returning `get`"),
        );
    }
}

/// `provides Comb[Thing, combine = wrongOp]` is refused like its named spelling: the
/// instance-binding check substitutes `T = Thing` either way.
#[test]
fn a_positional_instance_binding_is_checked_like_a_named_one() {
    for (ns, clause) in [
        ("wi32xfq.ib.named", "Comb[T = Thing, combine = wrongOp]"),
        ("wi32xfq.ib.positional", "Comb[Thing, combine = wrongOp]"),
    ] {
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Comb
    sort T = ?
    operation combine(a: T, b: T) -> T
  end
  operation wrongOp(a: String, b: String) -> String = a
  sort Thing provides {clause}
    entity thing(n: Int64)
  end
end
"#
        );
        let errs = try_load_kb_with(&src).err().unwrap_or_default();
        assert_refused_naming(
            &errs,
            &["signature-incompatible", "`String`", "`Thing`"],
            &format!("`provides {clause}` binding a `String` operation"),
        );
    }
}
