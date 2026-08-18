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
//!   * `sub_occurrence_labels(occ) -> List[String]` (WI-1129) — those same
//!     children's COMPONENT NAMES, same order, same length. The pair is what lets
//!     a macro enumerate a record whose labels it cannot know in advance (056
//!     §2.3's rule-head capture).
//!
//! Each macro below reads its argument through one of these and rebuilds
//! `wrapped(5)` (= 105) — so a working read path is observable both structurally
//! (the consumer body's head becomes `wrapped`) and by evaluation (105). If a read
//! builtin misbehaved, the macro's `none`/empty branch would leave the argument
//! untouched and the consumer would evaluate to 5, not 105.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
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
    kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol `{qn}` not found"))
}

fn eval_int(consumer: &str) -> i64 {
    let mut interp = crate::common::interp_for(SRC);
    match interp
        .call(consumer, &[])
        .unwrap_or_else(|e| panic!("{consumer} evaluates: {e:?}"))
    {
        Value::Int(n) => n,
        other => panic!("{consumer}: expected Int, got {other:?}"),
    }
}

/// `sub_occurrences` drives an identity-preserving rewrite: the macro reads the
/// argument application's child occurrences and reuses them in the rebuilt call,
/// so `via_subs(orig(5))` becomes `wrapped(5)` at compile time.
#[test]
fn sub_occurrences_children_rebuild() {
    let kb = crate::common::load_kb_with(SRC);
    let body = kb
        .op_body_node(sym(&kb, "test.wi722read.consumer_a"))
        .expect("consumer_a body");
    assert_eq!(
        crate::common::head_short(&kb, &body),
        "wrapped",
        "sub_occurrences should have rebuilt wrapped(...)"
    );
    assert_eq!(
        eval_int("test.wi722read.consumer_a"),
        105,
        "wrapped(5) = 105"
    );
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

// ── sub_occurrence_labels (WI-1129) ─────────────────────────────────────────
//
// ITS OWN FIXTURE, not a fourth macro in `SRC`. The macro below spells its callee
// out of the labels it reads, so a wrong label names an operation that does not
// exist — which fails the LOAD, taking every other test sharing that namespace
// down with it. MEASURED: folded into `SRC`, a back-out of `child_labels` turned
// all four tests in this file red, and three of them say nothing about labels.

const LABELS_SRC: &str = r#"
namespace test.wi722labels
  import anthill.prelude.{Int64, String}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.prelude.String.{concat}
  import anthill.reflect.{NodeOccurrence, make_apply, sub_occurrences, sub_occurrence_labels}

  -- The macro's argument: ONE positional child and ONE named child.
  operation orig2(a: Int64, b: Int64) -> Int64 = a
  -- The splice target, named for the two labels it takes to reach.
  operation lbl_1b(v: Int64, w: Int64) -> Int64 = add(add(v, w), 100)

  -- The callee's NAME is built out of the labels, so the splice resolves only if
  -- they are exactly `_1` (§4.5's 1-based positional convention) and `b` (the
  -- named arg's short name), in `for_each_child` order — positional first.
  operation via_labels(x: NodeOccurrence) -> NodeOccurrence =
    match sub_occurrence_labels(x)
      case cons(p, cons(n, _)) ->
        make_apply(concat(concat("test.wi722labels.lbl", p), n), sub_occurrences(x), x)
      case _ -> x

  operation trig_d(x: Int64) -> Int64 = x
  rule trig_d(?x) <=> via_labels(orig2(?x, b: 2)) [simp]

  operation consumer_d() -> Int64 = trig_d(5)
end
"#;

/// WI-1129 — `sub_occurrence_labels` is PARALLEL to `sub_occurrences`: same order,
/// same length, a positional child under its `_N` label and a named one under its
/// short name. The spliced `lbl_1b(5, 2)` = 107 pins all four claims at once.
///
/// BACK-OUT: change `child_labels` (kb/node_occurrence.rs) to mint
/// `positional_label(i + 1)` — a CONTENT mutation, so the two lists stay the same
/// length and the parallelism `debug_assert` does not pre-empt the measurement (an
/// emptied list trips that assert instead, which measures the guard, not the
/// labels). The macro then spells `lbl_2b`, which no operation answers. MEASURED:
/// 1 failed, 3 passed — the three tests above pass either way BY DESIGN, since
/// none of them reads a label and they are in a different namespace, so this
/// fixture's load failure cannot reach them. The NAMED half has its own back-out:
/// mint a positional label for a named child too, and this plus the four
/// `wi1129_rule_head_capture_test` splice rows go red together.
#[test]
fn sub_occurrence_labels_pairs_with_the_children() {
    let kb = crate::common::load_kb_with(LABELS_SRC);
    let body = kb
        .op_body_node(sym(&kb, "test.wi722labels.consumer_d"))
        .expect("consumer_d body");
    assert_eq!(
        crate::common::head_short(&kb, &body),
        "lbl_1b",
        "the labels `_1` and `b`, in that order, should have named the spliced callee",
    );
    let mut interp = crate::common::interp_for(LABELS_SRC);
    match interp
        .call("test.wi722labels.consumer_d", &[])
        .expect("consumer_d evaluates")
    {
        Value::Int(n) => assert_eq!(n, 107, "lbl_1b(5, 2) = add(add(5, 2), 100)"),
        other => panic!("expected Int(107), got {other:?}"),
    }
}
