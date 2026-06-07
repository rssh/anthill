//! Soundness tests for the typer's `if` branch-type handling (WI-287).
//!
//! `IfExpr` (kb/typing.rs) used to set the if-expression's result type to
//! the THEN branch's type and ignore the else branch — the same
//! first-branch-wins gap that `match` had, and the `IfExpr` frame didn't
//! even carry `expected`, so a declared return type was never enforced on
//! the else branch either.
//!
//! WI-287 routes `if` through the same `compute_branch_join_type` as
//! `match`: in synthesis mode the result is the join (a common supertype)
//! of the then / else types and an `Int64`/`String` clash is rejected; in
//! checked mode every branch must conform to the expected type. These
//! tests pin that down — two clash cases plus a positive control that
//! compatible branches still load clean (guarding against over-rejection).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra source → load errors (empty Vec on clean load).
fn try_load(extra: &str) -> Vec<load::LoadError> {
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
    load::load_all(&mut kb, &refs, &NullResolver).err().unwrap_or_default()
}

/// An `if` in synthesis position (value of an unannotated `let`) whose
/// branches return incompatible types — `Int64` vs `String`, with no
/// common supertype in the (top-less) Type lattice. WI-287 makes
/// synthesis-mode `if` compute the join of its branch types, so the
/// clash is a type error instead of being silently typed as the then
/// branch (`Int64`).
#[test]
fn if_synthesis_rejects_incompatible_branches() {
    let src = r#"
namespace test.if_cheat.synth
  import anthill.prelude.{Int64, String, Bool}

  sort Driver
    operation pick(c: Bool) -> Int64 =
      let x = if c then 1 else "hello"
      x
  end
end
"#;
    let errs = try_load(src);
    assert!(
        !errs.is_empty(),
        "unsound: if with incompatible branches (Int64 vs String) loaded clean — \
         the else branch was never type-checked (then-branch-wins)",
    );
}

/// An `if` placed directly as an operation body, where the declared
/// return type `Int64` flows in as the if's expected type. Before WI-287
/// the `IfExpr` frame dropped `expected` entirely and the op-body return
/// check only saw the then-branch (`Int64`), so the `String` else branch
/// leaked. Now `if` runs in checked mode and rejects the else branch.
#[test]
fn if_as_op_body_rejects_incompatible_branches() {
    let src = r#"
namespace test.if_cheat.checked
  import anthill.prelude.{Int64, String, Bool}

  sort Driver
    operation pick(c: Bool) -> Int64 =
      if c then 1 else "hello"
  end
end
"#;
    let errs = try_load(src);
    assert!(
        !errs.is_empty(),
        "unsound: if-as-op-body with a String else branch loaded clean against an Int64 \
         return type — only the then branch was checked",
    );
}

/// Positive control: an `if` whose branches share a type still loads
/// clean. Guards against the WI-287 join/checked-mode logic
/// over-rejecting well-typed `if`s (both arms `Int64`, joining to `Int64`,
/// which satisfies the `Int64` return type).
#[test]
fn if_with_compatible_branches_is_accepted() {
    let src = r#"
namespace test.if_ok
  import anthill.prelude.{Int64, Bool}

  sort Driver
    operation pick(c: Bool) -> Int64 =
      if c then 1 else 2
  end
end
"#;
    let errs = try_load(src);
    assert!(
        errs.is_empty(),
        "well-typed if (both branches Int64) was wrongly rejected: {errs:?}",
    );
}

/// Bare-vs-parameterized branches (`none()` : `Option` vs `some(1)` :
/// `Option[T=Int64]`) must join cleanly in BOTH orders. These are mutually
/// `types_compatible`, so `join_types` resolves them via
/// `more_general_type` (the bare `Option` wins) rather than treating them
/// as a clash — and the result is the same regardless of branch order
/// (`join_types` is commutative). Guards the WI-287 code-review fix for
/// the bare/parameterized join path against a spurious-clash regression.
#[test]
fn if_bare_vs_parameterized_branches_join_in_both_orders() {
    let none_then = r#"
namespace test.if_optjoin.a
  import anthill.prelude.{Int64, Bool, Option}

  sort Driver
    operation pick(c: Bool) -> Option[T = Int64] =
      let x = if c then none() else some(1)
      x
  end
end
"#;
    let some_then = r#"
namespace test.if_optjoin.b
  import anthill.prelude.{Int64, Bool, Option}

  sort Driver
    operation pick(c: Bool) -> Option[T = Int64] =
      let x = if c then some(1) else none()
      x
  end
end
"#;
    let errs_a = try_load(none_then);
    let errs_b = try_load(some_then);
    assert!(
        errs_a.is_empty(),
        "none()/some() if (none first) wrongly rejected: {errs_a:?}",
    );
    assert!(
        errs_b.is_empty(),
        "some()/none() if (some first) wrongly rejected: {errs_b:?}",
    );
}
