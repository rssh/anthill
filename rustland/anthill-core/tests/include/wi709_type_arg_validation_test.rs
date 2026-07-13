//! WI-709 — a sort application's type ARGUMENTS are validated against the sort's
//! declared type params, by ONE rule that both positions a type can be written in obey.
//!
//! WI-707 routed the VALUE position (`is_modifiable(Cell[V = Int64])`) through the same
//! canonical builder as the TYPE position (`c: Cell[V = Int64]`), so the two spellings
//! hash-cons to one term. That identity only holds if the positions also agree on which
//! arguments are ADMISSIBLE — and they did not: a stray named binding (`Cell[W = …]`,
//! `Cell` declaring only `V`) rode into the written type term untouched, an over-applied
//! positional was silently DROPPED at load, and the same positional was rejected only at
//! EVAL. Three answers to one written type. Nothing observed it only because no consumer
//! reads type ARGUMENTS yet (every `Type`-taking reflect op keys on the head sort).
//!
//! The rule is now `KnowledgeBase::check_sort_type_args`, shared by the loader's
//! `type_expr_to_child` and the typer's sort-application arm: an undeclared param name,
//! or a positional with no declared param left to bind, is a LOAD error in BOTH positions
//! (CLAUDE.md's loud-over-silent rule — a typo'd type argument is a bug the author wants
//! to hear about). Eval's `finish_sort_type` runs the SAME rule (it used to state a
//! weaker one of its own, blind to an undeclared name), so a synthesized occurrence that
//! never met the typer is loud too.
//!
//! NOT covered: a sort application inside a RULE BODY, which `convert_term` builds as a
//! plain term at load — a third lowering path that never reaches either checked site.
//! `rule bad(?x) :- eq(?x, is_modifiable(Cell[W = Int64]))` still loads and resolves with
//! the stray `W` in the term. Filed as WI-710.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// `Cell` declares one type param, `V`. A stray `W` is rejected the same way whether the
/// type is written in TYPE position or as a VALUE argument — the acceptance line: the two
/// positions cannot disagree about one written type.
#[test]
fn an_undeclared_type_argument_is_loud_in_both_positions() {
    let written = r#"
namespace test.wi709.written
  import anthill.prelude.{Cell, Int64}

  operation take(c: Cell[W = Int64]) -> Int64 = 0
end
"#;
    let value = r#"
namespace test.wi709.value
  import anthill.prelude.{Cell, Int64, Bool}
  import anthill.reflect.{is_modifiable}

  operation ask() -> Bool = is_modifiable(Cell[W = Int64])
end
"#;

    for (position, src) in [("type position", written), ("value position", value)] {
        let errs = match try_load_kb_with(src) {
            Err(errs) => errs,
            Ok(_) => panic!(
                "{position}: `Cell[W = Int64]` names a type parameter `Cell` does not \
                 declare — it must not load"
            ),
        };
        assert!(
            errs.iter().any(|e| e.contains("no type parameter named 'W'")),
            "{position}: expected the shared undeclared-type-argument diagnostic, got {errs:?}"
        );
    }
}

/// A positional type argument with no declared param to bind is diagnosed at LOAD, in
/// both positions. Previously the written form dropped it silently (`Cell[Int64, String]`
/// loaded as plain `Cell`) and the value form only complained at EVAL, from
/// `finish_sort_type` — so the same source text failed at two different times, or not at
/// all.
#[test]
fn an_over_applied_positional_is_diagnosed_at_load_in_both_positions() {
    let written = r#"
namespace test.wi709.written_pos
  import anthill.prelude.{Cell, Int64, String}

  operation take(c: Cell[Int64, String]) -> Int64 = 0
end
"#;
    let value = r#"
namespace test.wi709.value_pos
  import anthill.prelude.{Cell, Int64, String, Bool}
  import anthill.reflect.{is_modifiable}

  operation ask() -> Bool = is_modifiable(Cell[Int64, String])
end
"#;

    for (position, src) in [("type position", written), ("value position", value)] {
        let errs = match try_load_kb_with(src) {
            Err(errs) => errs,
            Ok(_) => panic!(
                "{position}: `Cell[Int64, String]` supplies two positional type arguments \
                 to a sort declaring one param — it must not load"
            ),
        };
        assert!(
            errs.iter().any(|e| e.contains("over-applied")),
            "{position}: expected the over-application diagnostic at LOAD, got {errs:?}"
        );
    }
}

/// A non-parametric sort takes no type arguments at all — the case
/// `make_parameterized_type`'s "stray bindings were dropped at load" comment described.
#[test]
fn a_non_parametric_sort_takes_no_type_arguments() {
    let src = r#"
namespace test.wi709.nonparam
  import anthill.prelude.{Int64}

  sort Plain
    entity plain(x: Int64)
  end

  operation take(p: Plain[Int64]) -> Int64 = 0
end
"#;
    let errs = match try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!("`Plain[Int64]` over-applies a non-parametric sort — it must not load"),
    };
    assert!(
        errs.iter().any(|e| e.contains("over-applied")),
        "expected the over-application diagnostic, got {errs:?}"
    );
}

/// The check rejects only what does not fit: the well-formed spellings — named,
/// positional, and the mixed form whose positional must SKIP the param already given by
/// name — still load and still evaluate to the one canonical term.
#[test]
fn well_formed_type_arguments_still_load_and_agree() {
    let src = r#"
namespace test.wi709.ok
  import anthill.prelude.{Cell, Map, Int64, String, Type}

  operation named() -> Type = Cell[V = Int64]
  operation positional() -> Type = Cell[Int64]

  -- The positional `Int64` must bind `V`, not re-bind the named `K`: the rule eval
  -- already applied, now the loader's too.
  operation mixed_written(m: Map[K = String, Int64]) -> Int64 = 0
  operation mixed_value() -> Type = Map[K = String, Int64]
  operation both_named() -> Type = Map[K = String, V = Int64]
end
"#;
    let mut interp = interp_for(src);

    let term_of = |interp: &mut anthill_core::eval::Interpreter, op: &str| match interp
        .call(&format!("test.wi709.ok.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op}: {e:?}"))
    {
        Value::Term { id, .. } => id,
        other => panic!("{op}: a type application must evaluate to a Term-carried type, got {other:?}"),
    };

    assert_eq!(
        term_of(&mut interp, "named"),
        term_of(&mut interp, "positional"),
        "`Cell[Int64]` binds the declared param `V`, so it is the same term as `Cell[V = Int64]`"
    );
    assert_eq!(
        term_of(&mut interp, "mixed_value"),
        term_of(&mut interp, "both_named"),
        "in `Map[K = String, Int64]` the positional binds the next param not already \
         given by name (`V`), so it is `Map[K = String, V = Int64]`"
    );
}
