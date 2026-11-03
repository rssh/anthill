//! WI-722 (proposal 043.1) — compile-time MACROS in the `@[simp]` engine.
//!
//! A macro is an occurrence→occurrence operation (every parameter AND the result
//! is a `NodeOccurrence` / reflect `Expr`, so the signature classifies it — no
//! marker). When it heads a fired `@[simp]` rule's RHS, the engine EVALUATES it at
//! compile time over its argument occurrences and splices the occurrence it
//! returns, instead of leaving the template call.
//!
//! This is the inverse of the verified-absent baseline: before WI-722, an
//! occurrence-returning op placed in a `@[simp]` RHS was NOT run — its argument
//! arrived as its evaluated *value* type (`Int64`), not the occurrence, so the
//! program failed to type-check. Here the macro `wrap` runs, rewriting
//! `trigger(5)` to `wrapped(5)` at compile time (via the occurrence BUILD builtin
//! `make_apply`), so the program loads AND `wrapped(5)` evaluates to `105`.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace test.wi722
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence, make_apply}

  -- The macro's OUTPUT target — an ordinary op. wrapped(5) = 105, so a
  -- successful rewrite is observable both structurally (head `wrapped`) and by
  -- evaluation.
  operation wrapped(v: Int64) -> Int64 = add(v, 100)

  -- The MACRO: every parameter and the result is a NodeOccurrence, so the
  -- @[simp] engine evaluates it at compile time. Its body BUILDS `wrapped(x)` as
  -- an occurrence, reusing the argument occurrence `x` in place (a `Term`-level
  -- `make_fn` could not carry a child occurrence — this is why `make_apply`
  -- returns a `NodeOccurrence`).
  operation wrap(x: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi722.wrapped", cons(x, nil()), x)

  -- The @[simp] LHS functor. Its own body is never evaluated — the call is
  -- rewritten away at compile time before it would be run.
  operation trigger(x: Int64) -> Int64 = x

  rule trigger(?x) <=> wrap(?x) @[simp]

  -- The consumer holding the redex. After type-checking, its STORED body is
  -- `wrapped(5)` (the macro ran), not `trigger(5)` / `wrap(5)`.
  operation consumer() -> Int64 = trigger(5)
end
"#;

fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol `{qn}` not found"))
}

/// The macro fires at COMPILE time: the consumer's stored body is rewritten from
/// `trigger(5)` to the macro's output `wrapped(5)`. (If the macro machinery were
/// absent, `wrap(5)` would type-error on `NodeOccurrence` vs `Int64` and the
/// spec would not load at all — so a successful `load_kb_with` is itself half the
/// proof.)
#[test]
fn macro_rewrites_consumer_body_at_compile_time() {
    let kb = crate::common::load_kb_with(SRC);
    let consumer = sym(&kb, "test.wi722.consumer");
    let body = kb.op_body_node(consumer).expect("consumer has a body node");
    assert_eq!(
        crate::common::head_short(&kb, &body),
        "wrapped",
        "the macro should have rewritten the consumer body to `wrapped(...)` at compile time",
    );
}

/// End-to-end: the macro-built occurrence re-types and evaluates. `wrapped(5)`
/// runs its ordinary body `add(5, 100)` → `105`.
#[test]
fn macro_output_re_types_and_evaluates() {
    let mut interp = crate::common::interp_for(SRC);
    let got = interp
        .call("test.wi722.consumer", &[])
        .expect("consumer evaluates");
    match got {
        Value::Int(n) => assert_eq!(n, 105, "wrapped(5) = add(5, 100) = 105"),
        other => panic!("expected Int(105), got {other:?}"),
    }
}

/// `is_macro` is signature-directed: an occurrence→occurrence op is a macro; an
/// op with a non-occurrence parameter or result is not. `wrap` (occ→occ) is;
/// `wrapped` (Int64→Int64) and `trigger` (Int64→Int64) are not — so they are only
/// ever ordinary calls, never macro-expanded.
#[test]
fn classifier_is_signature_directed() {
    use anthill_core::kb::typing::is_macro;
    let kb = crate::common::load_kb_with(SRC);
    assert!(
        is_macro(&kb, sym(&kb, "test.wi722.wrap")),
        "wrap is occ->occ"
    );
    assert!(
        !is_macro(&kb, sym(&kb, "test.wi722.wrapped")),
        "wrapped is Int64->Int64"
    );
    assert!(
        !is_macro(&kb, sym(&kb, "test.wi722.trigger")),
        "trigger is Int64->Int64"
    );
    // A container of an occurrence is NOT a macro result (the open-edge guard):
    // `operation_body -> Option[NodeOccurrence]` must not be misread.
    assert!(
        !is_macro(&kb, sym(&kb, "anthill.reflect.operation_body")),
        "operation_body returns Option[NodeOccurrence], not a bare occurrence",
    );
}

/// A macro runs at compile time with no effect handlers, so an occurrence→
/// occurrence op with a non-`Error` effect row is rejected at LOAD (proposal
/// 043.1 §6) — early and named, rather than a confusing residualize at first use.
#[test]
fn impure_macro_is_rejected_at_load() {
    const BAD: &str = r#"
namespace test.wi722bad
  import anthill.prelude.{Int64, Branch}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}

  operation wrapped(v: Int64) -> Int64 = v

  -- An occurrence->occurrence op that declares an effect (Branch): a macro must
  -- be pure, so this is a load error.
  operation bad(x: NodeOccurrence) -> NodeOccurrence effects {Branch} =
    make_apply("test.wi722bad.wrapped", cons(x, nil()), x)
end
"#;
    let errs = match crate::common::try_load_kb_with(BAD) {
        Err(errs) => errs,
        Ok(_) => panic!("an impure macro must be rejected at load, but the spec loaded"),
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("macro") && e.contains("pure")),
        "expected a macro-purity load error, got: {errs:?}",
    );
}

/// WI-904 — `is_macro` gives one verdict on both tiers it reads: the operation's cached
/// signature, which the typer builds (`build_op_signatures`), and the `OperationInfo`
/// fact, which is what a load stopped before the typer has. Each row is asked of a typed
/// load and of an untyped one: a macro; an operation with an occurrence result and one
/// value parameter; a value operation; a nullary occurrence operation; the stdlib's
/// `make_apply` (occurrence result, a `String` and a `List` parameter); an entity
/// constructor, a sort and a namespace, none of them an operation.
///
/// Each row also says whether its symbol is an operation, asked of `lookup_operation_info`,
/// and the constructor row that it is a constructor, so a row cannot pass by naming
/// something else.
///
/// Passes before and after WI-904's change by design: the change reads the cached
/// signature by reference instead of cloning it into an `OpInfoRecord`, and moves no
/// verdict. With the fact tier backed out (`false` where no signature is cached), the
/// untyped half fails at `wrap`.
#[test]
fn classifier_verdict_is_one_on_both_tiers() {
    use anthill_core::kb::typing::is_macro;
    const TIERS: &str = r#"
namespace test.wi904
  import anthill.prelude.{Int64, todo}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}

  sort Shape
    entity circle(r: Int64)
  end

  operation plain(v: Int64) -> Int64 = v
  operation wrap(x: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi904.plain", cons(x, nil()), x)
  operation half(x: NodeOccurrence, n: Int64) -> NodeOccurrence = x
  operation occ0() -> NodeOccurrence = todo()
end
"#;
    // (symbol, is a macro, is an operation)
    let rows: &[(&str, bool, bool)] = &[
        ("test.wi904.wrap", true, true),
        ("test.wi904.half", false, true),
        ("test.wi904.plain", false, true),
        ("test.wi904.occ0", false, true),
        ("anthill.reflect.make_apply", false, true),
        ("test.wi904.Shape.circle", false, false),
        ("test.wi904.Shape", false, false),
        ("test.wi904", false, false),
    ];
    let typed = crate::common::load_kb_with(TIERS);
    let untyped = crate::common::try_load_kb_untyped_with(TIERS)
        .unwrap_or_else(|errs| panic!("the untyped load must succeed: {errs:?}"));
    for (kb, tier) in [(&typed, "typed"), (&untyped, "untyped")] {
        for &(name, is_a_macro, is_an_operation) in rows {
            let s = sym(kb, name);
            assert_eq!(
                anthill_core::kb::op_info::lookup_operation_info(kb, s).is_some(),
                is_an_operation,
                "{name} is an operation? on the {tier} load",
            );
            assert_eq!(is_macro(kb, s), is_a_macro, "is_macro({name}) on the {tier} load");
        }
        assert!(
            kb.is_entity_constructor(sym(kb, "test.wi904.Shape.circle")),
            "`circle` is the constructor row on the {tier} load",
        );
    }
}
