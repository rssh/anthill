//! WI-642 — the STATIC face of the WI-300 rule-body dictionary.
//!
//! `req_insertion::run` / the typer flag a MISSING requirement on an OPERATION
//! body (WI-325 `MissingRequiresForSpecOp`), but NOT on a RULE / relation clause
//! body — so a clause calling a `requires`-carrying spec op whose requirement is
//! neither declared nor satisfiable was caught only at RESOLUTION (the WI-300
//! `find_dictionary` guard silently `DontFire`s), never at load. WI-642 walks each
//! rule body's spec-op calls and makes the statically-missing case a load error.
//!
//! The WI-292 distinction is the whole point (mirrors `find_dictionary_guard`):
//!   * a CONCRETE carrier that provides no instance, undeclared  → LOAD ERROR;
//!   * a rule that DECLARES the requirement (`requires(Spec[T])`) → loads clean
//!     (its own WI-300 dictionary — propagates the obligation to the query);
//!   * a POLYMORPHIC rule whose carrier is under-determined       → loads clean
//!     (suspends as a residual at fire time, never NAF-decided; WI-067).
//!
//! A structural-BUILTIN spec op (`Eq.eq`, `Ordered.gt`, …) resolves without a
//! dictionary, so it is never "missing" and never flagged — see
//! `builtin_comparison_op_on_concrete_no_instance_loads` (the stdlib itself relies
//! on this: `needs_rebuild`'s `gt` on two `Timestamp`s).

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Stdlib + extra source → (kb, load errors). Mirrors `wi325_missing_requires_test`.
fn try_load(extra: &str) -> (KnowledgeBase, Vec<load::LoadError>) {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let errs = load::load_all(&mut kb, &refs, &NullResolver)
        .err()
        .unwrap_or_default();
    (kb, errs)
}

fn fmt_errs(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

/// A user-defined spec (`Relatable`) whose op is *relational* (`-> Bool`, used as a
/// top-level goal, like `eq` in the WI-300 test) and — crucially — NOT a structural
/// builtin, so its requirement genuinely needs an instance. `Blob` is a concrete
/// sort that provides no `Relatable`; `Item` wraps a `Blob` so a clause var types at
/// `Blob`, not at `Relatable.T`.
const PRELUDE: &str = r#"
  sort Relatable
    sort T = ?
    operation related(a: T, b: T) -> Bool
  end

  sort Blob
    entity B(v: Int64)
  end

  sort Item
    entity I(b: Blob)
  end
"#;

/// ACCEPTANCE (the error case): a rule body calls `related` on two `Blob`s, `Blob`
/// provides no `Relatable`, and the rule declares no `requires` — a load error, not
/// a silent resolution-time failure.
#[test]
fn concrete_no_instance_rule_body_is_a_load_error() {
    let src = format!(
        r#"
namespace test.wi642.no_instance
  import anthill.prelude.{{Int64, Bool}}
  import test.wi642.no_instance.Relatable.{{related}}
{PRELUDE}
  rule linked(?x, ?y) :- I(b: ?x), I(b: ?y), related(?x, ?y)
end
"#
    );
    let (_kb, errs) = try_load(&src);
    assert!(
        !errs.is_empty(),
        "expected a MissingRequiresForSpecOp load error for a rule-body spec-op call \
         at a concrete no-instance carrier; got clean load",
    );
    let formatted = fmt_errs(&errs);
    assert!(
        formatted.contains("Relatable.related"),
        "diagnostic should name the spec op; got:\n{formatted}",
    );
    assert!(
        formatted.contains("requires Relatable"),
        "diagnostic should suggest `requires Relatable[…]`; got:\n{formatted}",
    );
}

/// ACCEPTANCE (declared-requires case): the same clause that DECLARES its
/// requirement in-body (`requires(Relatable[T])`) loads clean — the rule threads its
/// own dictionary (WI-300), propagating the obligation to whoever queries it.
#[test]
fn declared_in_body_requires_loads_clean() {
    let src = format!(
        r#"
namespace test.wi642.declared
  import anthill.prelude.{{Int64, Bool}}
  import test.wi642.declared.Relatable.{{related}}
{PRELUDE}
  rule linked(?x, ?y) :- requires(Relatable[T]), I(b: ?x), I(b: ?y), related(?x, ?y)
end
"#
    );
    let (_kb, errs) = try_load(&src);
    assert!(
        errs.is_empty(),
        "a rule that declares `requires(Relatable[T])` should load clean; got:\n{}",
        fmt_errs(&errs),
    );
}

/// ACCEPTANCE (under-determined case): a polymorphic rule whose carrier is not
/// pinned to any concrete sort SUSPENDS — it must NOT error (WI-292: never flag a
/// not-yet-ground requirement, never a rule that legitimately propagates it).
#[test]
fn polymorphic_under_determined_rule_body_suspends_no_error() {
    let src = format!(
        r#"
namespace test.wi642.poly
  import anthill.prelude.{{Int64, Bool}}
  import test.wi642.poly.Relatable.{{related}}
{PRELUDE}
  rule anyLinked(?x, ?y) :- related(?x, ?y)
end
"#
    );
    let (_kb, errs) = try_load(&src);
    assert!(
        errs.is_empty(),
        "a polymorphic (under-determined carrier) rule body must not error; got:\n{}",
        fmt_errs(&errs),
    );
}

/// A concrete carrier that DOES provide the spec (both the `fact` and the impl op)
/// loads clean — the satisfiable (`Fire`) case.
#[test]
fn concrete_with_instance_loads_clean() {
    let src = r#"
namespace test.wi642.has_instance
  import anthill.prelude.{Int64, Bool}
  import test.wi642.has_instance.Relatable.{related}

  sort Relatable
    sort T = ?
    operation related(a: T, b: T) -> Bool
  end

  sort Blob
    entity B(v: Int64)
    operation related(a: Blob, b: Blob) -> Bool = true
  end

  sort Item
    entity I(b: Blob)
  end

  fact Relatable[T = Blob]
  rule linked(?x, ?y) :- I(b: ?x), I(b: ?y), related(?x, ?y)
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "a concrete carrier that provides the spec should load clean; got:\n{}",
        fmt_errs(&errs),
    );
}

/// A structural-BUILTIN spec op (`Ordered.gt`) on a concrete sort with no `Ordered`
/// instance loads clean — it resolves structurally, so its requirement is never
/// "missing". This is exactly the stdlib `needs_rebuild` pattern (`gt` on two
/// `Timestamp`s); flagging it would break the stdlib.
#[test]
fn builtin_comparison_op_on_concrete_no_instance_loads() {
    let src = r#"
namespace test.wi642.builtin_cmp
  import anthill.prelude.{Int64, Bool, Ordered}
  import anthill.prelude.Ordered.{gt}

  sort Blob
    entity B(v: Int64)
  end

  sort Item
    entity I(b: Blob)
  end

  rule ordered(?x, ?y) :- I(b: ?x), I(b: ?y), gt(?x, ?y)
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "a builtin comparison op (`gt`) resolves structurally — no missing-requirement \
         error even at a no-instance concrete carrier; got:\n{}",
        fmt_errs(&errs),
    );
}

/// The op-body WI-325 diagnostic is UNCHANGED — an abstract op-body spec-op call
/// with no covering `requires` still errors (this pass is additive over rule bodies,
/// it does not touch the op-body path).
#[test]
fn op_body_missing_requires_still_errors() {
    let src = r#"
namespace test.wi642.op_body
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
        "the WI-325 op-body MissingRequiresForSpecOp diagnostic must still fire; got clean load",
    );
    assert!(
        fmt_errs(&errs).contains("requires PartialEq"),
        "op-body diagnostic should still suggest `requires PartialEq[…]` (WI-644: `eq`'s spec is the PartialEq base); got:\n{}",
        fmt_errs(&errs),
    );
}
