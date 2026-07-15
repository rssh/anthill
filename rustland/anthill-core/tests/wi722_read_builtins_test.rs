//! WI-722 inc 2 (proposal 043.1) — the occurrence-READ side of a compile-time
//! macro: the value-domain reflect builtins a macro body uses to inspect its
//! argument occurrences before rebuilding through `make_apply`.
//!
//!   * `sub_occurrences(occ) -> List[NodeOccurrence]` — the direct child
//!     occurrences, identity-preserving (so a child can be reused in place).
//!   * `occurrence_term(occ) -> Term` — reflect the node to its `Term` twin, so a
//!     macro reads its head/shape through the `Term` reflect surface
//!     (`term_functor_name`, …). `Bottom` for a child-bearing form.
//!   * `occurrence_type(occ) -> Option[Type]` — the typer-stamped `inferred_type`
//!     (the schema source for `where`/`join`), read on a TYPED occurrence.
//!
//! Each macro below reads its argument through one of these and rebuilds
//! `wrapped(5)` (= 105) — so a working read path is observable both structurally
//! (the consumer body's head becomes `wrapped`) and by evaluation (105). If a read
//! builtin misbehaved, the macro's `none`/empty branch would leave the argument
//! untouched and the consumer would evaluate to 5, not 105.

mod common;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace test.wi722read
  import anthill.prelude.{Int64}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence, make_apply}
  import anthill.reflect.{sub_occurrences, occurrence_term, occurrence_type}
  import anthill.reflect.{term_functor_name}

  -- The shared macro OUTPUT target. wrapped(5) = 105, so a rewrite is observable.
  operation wrapped(v: Int64) -> Int64 = add(v, 100)
  -- A one-arg application used to give a macro's argument a functor + a child.
  operation orig(v: Int64) -> Int64 = v

  -- (A) sub_occurrences: read x's child occurrences and splice them straight into
  -- wrapped(...). x is `orig(?v)`, so sub_occurrences(x) = [<occ v>] and this
  -- rebuilds `wrapped(v)` — proving the children are real, in order, reusable.
  operation via_subs(x: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi722read.wrapped", sub_occurrences(x), x)

  -- (B) occurrence_type: read on the TYPED reused pattern-var occurrence (a macro
  -- fires after its args are typed, bottom-up). `some` ⇒ wrap; a spurious `none`
  -- would passthrough to 5.
  operation via_type(x: NodeOccurrence) -> NodeOccurrence =
    match occurrence_type(x)
      case some(_) -> make_apply("test.wi722read.wrapped", cons(x, nil()), x)
      case none() -> x

  -- (C) occurrence_term: reflect the argument application to its Term twin and read
  -- its functor. `some` ⇒ the reflection round-tripped; `none` (Bottom) would
  -- passthrough. Rebuild reuses the reflected node's child via sub_occurrences.
  operation via_term(x: NodeOccurrence) -> NodeOccurrence =
    match term_functor_name(occurrence_term(x))
      case some(_) -> make_apply("test.wi722read.wrapped", sub_occurrences(x), x)
      case none() -> x

  operation trig_a(x: Int64) -> Int64 = x
  operation trig_b(x: Int64) -> Int64 = x
  operation trig_c(x: Int64) -> Int64 = x
  rule trig_a(?x) <=> via_subs(orig(?x))  [simp]
  rule trig_b(?x) <=> via_type(?x)        [simp]
  rule trig_c(?x) <=> via_term(orig(?x))  [simp]

  operation consumer_a() -> Int64 = trig_a(5)
  operation consumer_b() -> Int64 = trig_b(5)
  operation consumer_c() -> Int64 = trig_c(5)
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

fn eval_int(consumer: &str) -> i64 {
    let mut interp = common::interp_for(SRC);
    match interp.call(consumer, &[]).unwrap_or_else(|e| panic!("{consumer} evaluates: {e:?}")) {
        Value::Int(n) => n,
        other => panic!("{consumer}: expected Int, got {other:?}"),
    }
}

/// `sub_occurrences` drives an identity-preserving rewrite: the macro reads the
/// argument application's child occurrences and reuses them in the rebuilt call,
/// so `via_subs(orig(5))` becomes `wrapped(5)` at compile time.
#[test]
fn sub_occurrences_children_rebuild() {
    let kb = common::load_kb_with(SRC);
    let body = kb.op_body_node(sym(&kb, "test.wi722read.consumer_a")).expect("consumer_a body");
    assert_eq!(head_short(&kb, &body), "wrapped", "sub_occurrences should have rebuilt wrapped(...)");
    assert_eq!(eval_int("test.wi722read.consumer_a"), 105, "wrapped(5) = 105");
}

/// `occurrence_type` reads the typer-stamped type of the reused (typed) argument
/// occurrence: the macro takes the `some` branch and wraps, so the consumer
/// evaluates to 105 (a spurious `none` would leave the argument and yield 5).
#[test]
fn occurrence_type_reads_inferred_type() {
    assert_eq!(
        eval_int("test.wi722read.consumer_b"),
        105,
        "occurrence_type(x) should be some(Int64) on the typed argument, so the macro wraps",
    );
}

/// `occurrence_term` reflects the argument application to a `Term` whose functor
/// `term_functor_name` reads: the macro takes the `some` branch and wraps → 105 (a
/// `Bottom` reflection would read no functor and yield 5).
#[test]
fn occurrence_term_reflects_functor() {
    assert_eq!(
        eval_int("test.wi722read.consumer_c"),
        105,
        "occurrence_term(orig(5)) should reflect to Fn{{orig,…}} with a readable functor",
    );
}
