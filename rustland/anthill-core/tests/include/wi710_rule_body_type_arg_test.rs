//! WI-710 — the THIRD lowering path for a written parameterized type: a sort-headed term
//! in TERM position (a rule body, a `fact`, a constraint), built by `convert_term`.
//!
//! WI-709 made a stray type argument loud in the two positions it knew about — the type
//! annotation (`c: Cell[W = Int64]`, the loader's `type_expr_to_child`) and the value
//! argument (`is_modifiable(Cell[W = Int64])`, the typer's sort-application arm). It
//! missed this one: a rule body is never type-checked, and `convert_term` builds its
//! terms directly, so `rule bad(?x) :- eq(?x, is_modifiable(Cell[W = Int64]))` LOADED and
//! RESOLVED with the undeclared `W` riding in the term.
//!
//! `convert_term` now runs the same `KnowledgeBase::check_sort_type_args`, keyed on the
//! functor's KIND (an entity constructor's named args are declared FIELDS, not type
//! params). It reads only argument NAMES and COUNT, never their values — which is what
//! lets a LOGIC VARIABLE argument (`List[T = ?x]`, the rule-body type pattern reflect
//! rules are written with) keep loading.

use crate::common::try_load_kb_with;

/// The WI-710 repro: the stray `W` is now heard at LOAD, with the same diagnostic the
/// other two positions raise.
#[test]
fn an_undeclared_type_argument_in_a_rule_body_is_loud() {
    let src = r#"
namespace test.wi710.body
  import anthill.prelude.{Cell, Int64, Bool}
  import anthill.reflect.{is_modifiable}

  rule bad(?x) :- eq(?x, is_modifiable(Cell[W = Int64]))
end
"#;
    let errs = match try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!(
            "a rule body's `Cell[W = Int64]` names a type parameter `Cell` does not \
             declare — it must not load"
        ),
    };
    assert!(
        errs.iter().any(|e| e.contains("no type parameter named 'W'")),
        "expected the shared undeclared-type-argument diagnostic, got {errs:?}"
    );
}

/// A NESTED type inside a fact's binding value is a type, so it is checked too — the
/// depth gate is about the READING of the syntax, not about rule bodies specifically.
#[test]
fn an_undeclared_type_argument_nested_in_a_fact_binding_is_loud() {
    let src = r#"
namespace test.wi710.nested
  import anthill.prelude.{Cell, Int64, Modifiable}

  fact Modifiable[T = Cell[W = Int64]]
end
"#;
    let errs = match try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!("the nested `Cell[W = Int64]` is a TYPE with a stray param — must not load"),
    };
    assert!(
        errs.iter().any(|e| e.contains("no type parameter named 'W'")),
        "expected the shared diagnostic, got {errs:?}"
    );
}

/// A CALL-SITE type-argument list (`op[A = Int](args)`, WI-271) rides as a `type_args`
/// ParseAux named-arg on the parse `Fn`. It is not a sort application and must not be
/// read as one — `type_args` is not a type parameter of anything.
#[test]
fn a_call_site_type_argument_list_is_not_a_sort_application() {
    let src = r#"
namespace test.wi710.callsite
  import anthill.prelude.{Int64, Bool, List}

  operation pick[T](xs: List[T = T]) -> Bool = true
  -- The call carries an explicit call-site type-argument list.
  rule ok(?b) :- eq(?b, pick[T = Int64](nil))
end
"#;
    try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!("a call-site type-arg list must not be read as a sort application: {errs:?}")
    });
}

/// THE third guard against over-reach, and the subtlest: a sort and its constructor may
/// share a NAME (`sort Leaf { entity Leaf(name: String) }`), in which case the bare `Leaf`
/// resolves to the SORT — so a nested CONSTRUCTOR call `Leaf(name: "tip")` is a
/// sort-headed `Term::Fn` whose named args are FIELDS, indistinguishable BY SHAPE from a
/// type application. Only the surface tells them apart (`(…)` call vs `[…]` type
/// application), which is why the parse converter records the bracketed provenance and
/// this check reads it. Reading the fields as type arguments rejected the WI-321
/// cross-file suite; that is what this pins.
#[test]
fn a_constructor_call_sharing_its_sort_name_is_not_a_type_application() {
    let src = r#"
namespace test.wi710.collision
  import anthill.prelude.{String, Option}

  sort Leaf
    entity Leaf(name: String)
  end

  sort Tree
    entity Node(name: String, leaf: Leaf)
  end

  -- `Leaf(name: …)` is a CONSTRUCTOR call (parens), nested inside another constructor
  -- and inside a rule body — `name` is a FIELD, not a type argument.
  fact Node(name: "root", leaf: Leaf(name: "tip"))
  rule tip(?t) :- Node(name: ?, leaf: Leaf(name: ?t))
end
"#;
    try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!("a constructor call sharing its sort's name is not a type application: {errs:?}")
    });
}

/// THE other guard against over-reach: at TOP level the same syntax is an INSTANCE
/// CLAIM, whose argument grammar is a different, richer language — a positional on a
/// non-parametric spec is the WI-407 CARRIER slot (below), and an op-bearing instance
/// fact names the spec's OPERATIONS rather than its type params
/// (`fact Monad[M = Option, pure = optionPure, …]` — `pure`/`flatMap`/`map` are Monad's
/// operations; Monad declares only `M`). Neither is a type argument.
///
/// The op-bearing shape needs no case of its own here: it lives in the STDLIB
/// (`prelude/option.anthill`), which every one of these tests loads — the first,
/// un-gated version of this check rejected it and took the whole stdlib down with it.
#[test]
fn a_top_level_instance_fact_is_not_a_type_application() {
    let src = r#"
namespace test.wi710.instance
  import anthill.prelude.{Int64}

  sort Marker
  end
  sort Carrier
    entity carrier(x: Int64)
  end
  -- A positional on a spec that declares NO type params is the carrier slot (WI-407),
  -- not an over-applied type argument.
  fact Marker[Carrier]
end
"#;
    try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!("a top-level instance fact must not be read as a type application: {errs:?}")
    });
}

/// Over-application is caught in term position too.
#[test]
fn an_over_applied_positional_in_a_rule_body_is_loud() {
    let src = r#"
namespace test.wi710.overapplied
  import anthill.prelude.{Cell, Int64, String, Bool}
  import anthill.reflect.{is_modifiable}

  rule bad(?x) :- eq(?x, is_modifiable(Cell[Int64, String]))
end
"#;
    let errs = match try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!("`Cell[Int64, String]` over-applies a one-param sort — must not load"),
    };
    assert!(
        errs.iter().any(|e| e.contains("over-applied")),
        "expected the over-application diagnostic, got {errs:?}"
    );
}

/// THE guard against over-reach: the check reads argument NAMES and COUNT, never values,
/// so a rule-body type pattern with a LOGIC VARIABLE argument — the shape reflect rules
/// are written with — still loads. A check that tried to validate the argument as a type
/// would reject these.
#[test]
fn a_rule_body_type_pattern_with_variable_arguments_still_loads() {
    let src = r#"
namespace test.wi710.vars
  import anthill.prelude.{Cell, List, Int64, Bool, Modifiable}
  import anthill.reflect.{is_modifiable}

  -- A variable type ARGUMENT, named and positional, in a rule body and in a goal.
  rule modifiable_elem(?t) :- Modifiable[T = ?t]
  rule any_list(?t, ?b) :- eq(?b, is_modifiable(List[T = ?t]))
  rule positional_var(?t) :- Modifiable[?t]

  -- A ground one alongside, to pin that the well-formed spelling is untouched.
  fact Modifiable[T = Cell]
end
"#;
    try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!("a rule-body type pattern with variable arguments must still load: {errs:?}")
    });
}
