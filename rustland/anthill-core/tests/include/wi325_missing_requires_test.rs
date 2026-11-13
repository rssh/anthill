//! WI-325 — abstract-binding `NoCandidates` reports `MissingRequiresForSpecOp`.
//!
//! Background: when the typer's spec-op dispatch returns `NoCandidates`
//! AND the per-call substitution leaves at least one of the spec's type
//! parameters abstract (an unground type-param `Var` or a sort-param
//! `Ref`), the runtime has no impl to dispatch to. Pre-WI-325 the typer
//! silently passed these through, deferring the failure to the first
//! call site — landing as an "unknown operation" eval error days later.
//!
//! Post-WI-325 the typer tags such occurrences with
//! `CallClass::UnresolvedSpecOp`; `req_insertion::run` translates the
//! tag into a `MissingRequiresForSpecOp` diagnostic that surfaces at
//! body load. Concrete-binding `NoCandidates` is unchanged — host
//! builtins / spec-derived rules still resolve at runtime.
//!
//! Acceptance bullet from the WI:
//!   `operation foo(x: T) -> Bool = eq(x, x)` WITHOUT `requires Eq[T]`
//!   fails to load; adding `requires Eq[T]` makes it load.

use anthill_core::kb::load::{self};
use anthill_core::kb::typing::TypeError;
use anthill_core::kb::KnowledgeBase;

/// Stdlib + extra source → (kb, load errors). Mirrors the helper in
/// `wi270_expected_type_test.rs`.
fn try_load(extra: &str) -> (KnowledgeBase, Vec<load::LoadError>) {
    crate::common::load_outcome(extra).kb_and_errors()
}

fn fmt_errs(errs: &[load::LoadError]) -> String {
    errs.iter()
        .map(|e| format!("{}", e))
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn missing_requires_eq_in_operation_body_errors() {
    // The whole point of WI-325: an operation body that calls a spec op
    // on an abstract type parameter must fail to load when the enclosing
    // sort doesn't declare the corresponding `requires`.
    let src = r#"
namespace test.wi325.missing_eq
  import anthill.prelude.{Bool, Eq}
  import anthill.prelude.Eq.{eq}

  sort Container
    sort T = ?
    operation foo(x: T) -> Bool = eq(x, x)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        !errs.is_empty(),
        "expected MissingRequiresForSpecOp diagnostic; got clean load",
    );
    let formatted = fmt_errs(&errs);
    assert!(
        // WI-644: the op calls `eq`, whose spec is now the `PartialEq` base — the
        // diagnostic suggests `requires PartialEq` (a `requires Eq` would also cover it
        // transitively). The check still fires: an uncovered spec-op call is rejected.
        formatted.contains("requires PartialEq"),
        "expected diagnostic to suggest `requires PartialEq[…]`; got:\n{formatted}",
    );
    assert!(
        formatted.contains("anthill.prelude.PartialEq.eq"),
        "expected diagnostic to name the spec op; got:\n{formatted}",
    );
}

#[test]
fn requires_eq_in_enclosing_sort_makes_call_load() {
    // The fix: declaring `requires Eq[T]` on the enclosing sort closes
    // the gap and the same body loads cleanly.
    let src = r#"
namespace test.wi325.has_eq
  import anthill.prelude.{Bool, Eq}
  import anthill.prelude.Eq.{eq}

  sort Container
    sort T = ?
    requires Eq[T]
    operation foo(x: T) -> Bool = eq(x, x)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "expected `requires Eq[T]` to make the call load; got:\n{}",
        fmt_errs(&errs),
    );
}

#[test]
fn concrete_binding_no_candidates_is_not_an_error() {
    // The WI is explicit that concrete-sort `NoCandidates` stays a
    // legitimate pass-through — host builtins / spec-derived rules may
    // still resolve at runtime. Here `eq(x, x)` with x: Int64 has a
    // matching `fact Eq[T = Int64]` in stdlib so it actually goes through
    // the `Unique` path; the case under test is that a body using a
    // spec op at a concrete T (no abstract var) doesn't trip WI-325.
    let src = r#"
namespace test.wi325.concrete_eq
  import anthill.prelude.{Bool, Eq, Int64}
  import anthill.prelude.Eq.{eq}

  sort Driver
    operation foo(x: Int64) -> Bool = eq(x, x)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "concrete-T spec-op call should still load; got:\n{}",
        fmt_errs(&errs),
    );
}

#[test]
fn user_defined_spec_without_providers_errors_on_abstract_call() {
    // The closing-the-gate case: a user-defined spec sitting OUTSIDE the
    // stdlib `anthill.*` namespace, with no `fact MySpec[…]` records,
    // must still trigger `MissingRequiresForSpecOp` when called on an
    // abstract type parameter. Pre-fix the `spec_has_any_providers`
    // gate let this slip through silently (zero providers → no tag),
    // re-introducing the WI-324 phantom for any user spec that hadn't
    // yet been satisfied by a provider fact.
    let src = r#"
namespace test.wi325.user_spec_no_provider
  import anthill.prelude.Bool
  import test.wi325.user_spec_no_provider.MySpec.{describe}

  sort MySpec
    sort T = ?
    operation describe(x: T) -> Bool
  end

  sort Driver
    sort T = ?
    operation drive(x: T) -> Bool = describe(x)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        !errs.is_empty(),
        "user-defined spec without providers should still error on abstract call; got clean load",
    );
    let formatted = fmt_errs(&errs);
    assert!(
        formatted.contains("requires MySpec"),
        "expected diagnostic to suggest `requires MySpec[…]`; got:\n{formatted}",
    );
}

/// A SELF-RECEIVER spec nothing provides: `render(w)` on `w: Widget` is a call on a `Widget`
/// instance (proposal 073 §2), which runs the operation the instance holds, fixed where the
/// instance is made. It loads: with no provider no instance can be made, so the call never
/// runs, and a provision added later is what makes one. It was refused while the call was
/// dispatched on the value, which had no provider to choose (WI-350's guard). The twin with
/// `Pane provides Widget` drives the same `drive` body to `Pane`'s `render`.
#[test]
fn a_call_on_an_instance_of_an_unprovided_spec_loads() {
    let src = r#"
namespace test.wi325.user_self_receiver_no_provider
  import anthill.prelude.Bool
  import test.wi325.user_self_receiver_no_provider.Widget.{render}

  sort Widget
    sort T = ?
    operation render(w: Self) -> Bool
  end

  sort Driver
    operation drive(w: Widget) -> Bool = render(w)
  end
PROVIDER
end
"#;
    let (_kb, errs) = try_load(&src.replace("PROVIDER", ""));
    assert!(errs.is_empty(), "a call on an instance loads:\n{}", fmt_errs(&errs));
    let driven = src.replace(
        "PROVIDER",
        "  sort Pane\n    import anthill.prelude.Bool\n    entity pane\n    \
         provides Widget[T = Bool]\n    operation render(w: Pane) -> Bool = true\n  end\n  \
         operation go() -> Bool = Driver.drive(pane())\n",
    );
    let mut interp = crate::common::interp_for(&driven);
    let v = interp
        .call("test.wi325.user_self_receiver_no_provider.go", &[])
        .unwrap_or_else(|e| panic!("drive(pane()): {e:?}"));
    assert!(matches!(v, anthill_core::eval::Value::Bool(true)), "{v:?}");
}

#[test]
fn stdlib_spec_without_providers_still_passes_through() {
    // Counter-test for the namespace heuristic: stdlib `Map` (in
    // `anthill.prelude.*`) has zero providers but is a host built-in.
    // Calling `Map.empty()` from a context where K and V are unbound
    // must NOT trigger WI-325 — the runtime resolves Map operations
    // directly.
    let src = r#"
namespace test.wi325.stdlib_no_provider
  import anthill.prelude.{Map, Int64}
  import anthill.prelude.Map.{empty, put, size}

  sort Driver
    operation build() -> Int64 = size(put(empty(), "a", 1))
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "abstract Map.empty() should pass through (host built-in); got:\n{}",
        fmt_errs(&errs),
    );
}

/// Unit-level check that `MissingRequiresForSpecOp` round-trips through
/// `format` with the suggested `requires` clause. Independent of the
/// full load pipeline.
#[test]
fn missing_requires_format_names_spec_and_param() {
    let mut kb = KnowledgeBase::new();
    let op_sym = kb.intern("anthill.prelude.PartialEq.eq");
    let spec_sym = kb.intern("anthill.prelude.Eq");
    let t_sym = kb.intern("T");
    let mut abstract_params = smallvec::SmallVec::<[anthill_core::intern::Symbol; 2]>::new();
    abstract_params.push(t_sym);
    let caller = kb.intern("test.wi325.caller");
    let err = TypeError::MissingRequiresForSpecOp {
        span: None,
        spec_op_sym: op_sym,
        spec_sort_sym: spec_sym,
        abstract_params,
        site: anthill_core::kb::typing::RequiresSite::Operation {
            op: caller,
            sort: None,
        },
    };
    let formatted = err.format(&kb);
    assert!(
        formatted.contains("anthill.prelude.PartialEq.eq"),
        "should name the spec op QN; got: {formatted}",
    );
    assert!(
        formatted.contains("requires Eq[T = "),
        "should suggest `requires Eq[T = …]`; got: {formatted}",
    );
}
