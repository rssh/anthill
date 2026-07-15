//! WI-722 (proposal 043.1) — compile-time MACROS in the `[simp]` engine.
//!
//! A macro is an occurrence→occurrence operation (every parameter AND the result
//! is a `NodeOccurrence` / reflect `Expr`, so the signature classifies it — no
//! marker). When it heads a fired `[simp]` rule's RHS, the engine EVALUATES it at
//! compile time over its argument occurrences and splices the occurrence it
//! returns, instead of leaving the template call.
//!
//! This is the inverse of the verified-absent baseline: before WI-722, an
//! occurrence-returning op placed in a `[simp]` RHS was NOT run — its argument
//! arrived as its evaluated *value* type (`Int64`), not the occurrence, so the
//! program failed to type-check. Here the macro `wrap` runs, rewriting
//! `trigger(5)` to `wrapped(5)` at compile time (via the occurrence BUILD builtin
//! `make_apply`), so the program loads AND `wrapped(5)` evaluates to `105`.

mod common;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::Expr;
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
  -- [simp] engine evaluates it at compile time. Its body BUILDS `wrapped(x)` as
  -- an occurrence, reusing the argument occurrence `x` in place (a `Term`-level
  -- `make_fn` could not carry a child occurrence — this is why `make_apply`
  -- returns a `NodeOccurrence`).
  operation wrap(x: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi722.wrapped", cons(x, nil()), x)

  -- The [simp] LHS functor. Its own body is never evaluated — the call is
  -- rewritten away at compile time before it would be run.
  operation trigger(x: Int64) -> Int64 = x

  rule trigger(?x) <=> wrap(?x) [simp]

  -- The consumer holding the redex. After type-checking, its STORED body is
  -- `wrapped(5)` (the macro ran), not `trigger(5)` / `wrap(5)`.
  operation consumer() -> Int64 = trigger(5)
end
"#;

fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("symbol `{qn}` not found"))
}

/// The short name of an occurrence's head functor (`wrapped(...)` → `"wrapped"`).
fn head_short(kb: &KnowledgeBase, occ: &std::rc::Rc<anthill_core::kb::node_occurrence::NodeOccurrence>) -> String {
    match occ.as_expr() {
        Some(Expr::Apply { functor, .. }) => {
            kb.resolve_sym(*functor).rsplit('.').next().unwrap_or("").to_string()
        }
        other => panic!("expected a functor application, got {other:?}"),
    }
}

/// The macro fires at COMPILE time: the consumer's stored body is rewritten from
/// `trigger(5)` to the macro's output `wrapped(5)`. (If the macro machinery were
/// absent, `wrap(5)` would type-error on `NodeOccurrence` vs `Int64` and the
/// spec would not load at all — so a successful `load_kb_with` is itself half the
/// proof.)
#[test]
fn macro_rewrites_consumer_body_at_compile_time() {
    let kb = common::load_kb_with(SRC);
    let consumer = sym(&kb, "test.wi722.consumer");
    let body = kb.op_body_node(consumer).expect("consumer has a body node");
    assert_eq!(
        head_short(&kb, &body),
        "wrapped",
        "the macro should have rewritten the consumer body to `wrapped(...)` at compile time",
    );
}

/// End-to-end: the macro-built occurrence re-types and evaluates. `wrapped(5)`
/// runs its ordinary body `add(5, 100)` → `105`.
#[test]
fn macro_output_re_types_and_evaluates() {
    let mut interp = common::interp_for(SRC);
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
    let kb = common::load_kb_with(SRC);
    assert!(is_macro(&kb, sym(&kb, "test.wi722.wrap")), "wrap is occ->occ");
    assert!(!is_macro(&kb, sym(&kb, "test.wi722.wrapped")), "wrapped is Int64->Int64");
    assert!(!is_macro(&kb, sym(&kb, "test.wi722.trigger")), "trigger is Int64->Int64");
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
    let errs = match common::try_load_kb_with(BAD) {
        Err(errs) => errs,
        Ok(_) => panic!("an impure macro must be rejected at load, but the spec loaded"),
    };
    assert!(
        errs.iter().any(|e| e.contains("macro") && e.contains("pure")),
        "expected a macro-purity load error, got: {errs:?}",
    );
}
