//! WI-20260827-EJ5F5 — A BINDER `case` ARM LOWERS TO A BINDING, NOT A TAG CHECK.
//!
//! cpp-gen was the third reader of "a bare name in a `case` pattern", and the one that
//! got it wrong in the OTHER direction: `analyse_pattern_occ`'s `Pattern::Var` arm
//! emitted `std::holds_alternative<X>(s)` for EVERY bare name, while the interpreter
//! bound every one. The typer now rewrites a bare name that denotes one of the position's
//! own nullary constructors into a `Pattern::Constructor` before the body is stored, so
//! what reaches this arm is a genuine binder — `case other -> …`, the shape the corpus's
//! own two arms in `anthill-todo/anthill/main.anthill` have — and
//! `std::holds_alternative<other>(c)` names a C++ type that does not exist.
//!
//! MEASURED BEFORE CHANGING IT: with the `Pattern::Var` arm replaced by a `panic!`, the
//! whole cpp-gen suite (197 tests) stayed green — no fixture reached it once the typer's
//! rewrite landed. So the arm had no coverage at all, and these two rows are it.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_with;

/// `other` names no `Colour` constructor, so it stays a binder, and the arm is a
/// catch-all whose body reads the bound value.
///
/// BACK OUT the `Pattern::Var` arm (restore the tag check and drop the binding) and this
/// emits, MEASURED:
///
/// ```cpp
/// return (std::holds_alternative<Red>(c) ? 0 : rank(other));
/// ```
///
/// — where `other` is an undeclared identifier, so the generated translation unit does
/// not compile.
#[test]
fn a_binder_arm_binds_the_scrutinee_instead_of_tag_checking_its_name() {
    let source = r#"
        namespace test.ej5f5cpp
          import anthill.prelude.{Int64}
          enum Colour
            entity Red
            entity Green
            entity Blue
          end
          sort Calc
            operation rank(c: Colour) -> Int64 = 7
            operation tag(c: Colour) -> Int64 =
              match c
                case Red -> 0
                case other -> Calc.rank(other)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.ej5f5cpp.Calc").expect("emit Calc");

    assert!(
        cpp.contains("auto other = c;"),
        "the binder arm must DECLARE the bound name from the scrutinee:\n{cpp}"
    );
    assert!(
        !cpp.contains("holds_alternative<other>"),
        "and must not tag-check on a name that is no constructor — that names a C++ \
         type which does not exist:\n{cpp}"
    );
    assert!(
        cpp.contains("std::holds_alternative<Red>(c)"),
        "CONTROL, unmoved by this change: the arm that DOES name a constructor still \
         tag-checks — it reaches the constructor arm, via the typer's rewrite:\n{cpp}"
    );
}

/// AND THE ORDER IS NOW ENFORCED. A binder arm is a catch-all, so an arm after it is
/// dead; `lower_match_branches_node` already refuses a non-final catch-all, and a binder
/// arm now falls under that refusal instead of being smuggled past it by a bogus tag
/// check.
///
/// BACK OUT the `Pattern::Var` arm and `emit_traits_struct` returns `Ok` with, MEASURED:
///
/// ```cpp
/// return (std::holds_alternative<other>(c) ? 9 : 2);
/// ```
///
/// — `other` names no C++ type, so a wrong program is accepted here and refused only by
/// the C++ compiler, pointing at generated text.
#[test]
fn a_binder_arm_before_another_arm_is_refused() {
    let source = r#"
        namespace test.ej5f5cpp2
          import anthill.prelude.{Int64}
          enum Colour
            entity Red
            entity Green
            entity Blue
          end
          sort Calc
            operation tag(c: Colour) -> Int64 =
              match c
                case other -> 9
                case Blue -> 2
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_traits_struct(&mut kb, "test.ej5f5cpp2.Calc")
        .expect_err("a catch-all before another arm must be refused");
    assert!(
        err.message.contains("catch-all only allowed last"),
        "and refused by the rule that already owns dead arms: {}",
        err.message
    );
}

/// A NESTED CONSTRUCTOR SUB-PATTERN IS REFUSED, and the refusal names the MATCH.
///
/// `case some(red)` now reaches cpp-gen as `some(red())` — the typer resolved the nested
/// name — and cpp-gen lowers a sub-pattern as a plain binding, which has no spelling for a
/// nested tag check. Before this ticket the bare spelling arrived as a `Var` and was
/// lowered as `auto red = o.value();`, ignoring the constructor completely: the arm fired
/// for EVERY `some`, which is the same silent wrong answer the interpreter had.
///
/// The parenthesized twin is asserted beside it as the CONTROL: it always came down this
/// path, so it shows the refusal is about the SHAPE and not about the new spelling.
///
/// BACK OUT `match_subpattern_name` (call `pattern_var_name_occ` directly again) and both
/// rows still refuse, but say `let/lambda binder: only Var pattern supported` about a
/// `match` — a message that sends the author to a line that does not exist.
#[test]
fn a_nested_constructor_sub_pattern_is_refused_naming_the_match() {
    let src = |arm: &str| {
        format!(
            r#"
        namespace test.ej5f5cpp3
          import anthill.prelude.{{Int64, Option}}
          import anthill.prelude.Option.{{some, none}}
          enum Colour
            entity Red
            entity Green
          end
          sort Calc
            operation tag(o: Option[T = Colour]) -> Int64 =
              match o
                case some({arm}) -> 1
                case _ -> 0
          end
        end
    "#
        )
    };
    for (label, arm) in [("bare", "Red"), ("parenthesized", "Red()")] {
        let mut kb = load_kb_with(&src(arm));
        let err = emit_traits_struct(&mut kb, "test.ej5f5cpp3.Calc")
            .expect_err("a nested constructor sub-pattern has no cpp-gen lowering");
        assert!(
            err.message.contains("not yet supported in cpp-gen")
                && err.message.contains("sub-pattern"),
            "{label}: the refusal must name the match, not a let/lambda binder: {}",
            err.message
        );
    }
}
