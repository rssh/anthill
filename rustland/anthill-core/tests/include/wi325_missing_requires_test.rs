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

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::typing::TypeError;
use anthill_core::parse;

/// Stdlib + extra source → (kb, load errors). Mirrors the helper in
/// `wi270_expected_type_test.rs`.
fn try_load(extra: &str) -> (KnowledgeBase, Vec<load::LoadError>) {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let result = load::load_all(&mut kb, &refs, &NullResolver);
    let errs = result.err().unwrap_or_default();
    (kb, errs)
}

fn fmt_errs(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{}", e)).collect::<Vec<_>>().join("\n")
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
        formatted.contains("requires Eq"),
        "expected diagnostic to suggest `requires Eq[…]`; got:\n{formatted}",
    );
    assert!(
        formatted.contains("anthill.prelude.Eq.eq"),
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

#[test]
fn user_defined_self_receiver_spec_without_providers_errors_on_abstract_call() {
    // WI-350 guard: a SELF-RECEIVER spec (`render(w: Widget)` — `w` typed as
    // the spec sort itself, not its type-parameter) types abstract receivers
    // through the interface and defers the impl to the runtime value's witness.
    // But a user-defined self-receiver spec with NO provider at all has no
    // witness — every call fails at first dispatch. The Abstract branch must
    // fall through to the `NoCandidates` WI-325 diagnostic so a wholly-
    // unimplemented spec is caught at type-check, not deferred to a runtime
    // `UnknownOperation`. Distinct from the type-param-carrier case above
    // (`describe(x: T)`), which never took the Abstract early return.
    let src = r#"
namespace test.wi325.user_self_receiver_no_provider
  import anthill.prelude.Bool

  sort Widget
    sort T = ?
    operation render(w: Widget) -> Bool
  end

  sort Driver
    operation drive(w: Widget) -> Bool = render(w)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        !errs.is_empty(),
        "wholly-unimplemented self-receiver spec should error on abstract call; got clean load",
    );
    let formatted = fmt_errs(&errs);
    assert!(
        formatted.contains("Widget"),
        "expected a Widget spec diagnostic; got:\n{formatted}",
    );
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
    let op_sym = kb.intern("anthill.prelude.Eq.eq");
    let spec_sym = kb.intern("anthill.prelude.Eq");
    let t_sym = kb.intern("T");
    let mut abstract_params = smallvec::SmallVec::<[anthill_core::intern::Symbol; 2]>::new();
    abstract_params.push(t_sym);
    let err = TypeError::MissingRequiresForSpecOp {
        span: None,
        spec_op_sym: op_sym,
        spec_sort_sym: spec_sym,
        abstract_params,
    };
    let formatted = err.format(&kb);
    assert!(
        formatted.contains("anthill.prelude.Eq.eq"),
        "should name the spec op QN; got: {formatted}",
    );
    assert!(
        formatted.contains("requires Eq[T = "),
        "should suggest `requires Eq[T = …]`; got: {formatted}",
    );
}
