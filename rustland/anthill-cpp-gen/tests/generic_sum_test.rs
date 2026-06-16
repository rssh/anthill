//! Slice 2 of generic-sort support: `enum E { sort T = ?; entity Some(value: ?T); … }`.
//!
//! Generic sum sorts emit:
//! - per-constructor structs, templated when they reference any param
//! - a templated alias `template<typename T> using E = std::variant<…>;`
//! - constructor entries inside the `variant<…>` either bare (when
//!   no parameter is referenced) or `Ctor<T>` (when one or more is)
//!
//! Composes with the lexical type-param scope stack landed alongside
//! this slice so a generic enum's constructor structs see the enum's
//! params during field-type lowering.

use super::common;

use anthill_cpp_gen::emit_sum;
use common::load_kb_with_lenient;

#[test]
fn generic_sum_emits_templated_alias() {
    // Option = Some(value: T) | None — Some is templated, None is not.
    let source = r#"
        namespace test.gen_opt
          enum Option
            sort T = ?
            entity Some(value: ?T)
            entity None
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_sum(&kb, "test.gen_opt.Option")
        .expect("emit Option sum");

    // Constructor structs:
    assert!(
        cpp.contains("template<typename T>\nstruct Some {\n    T value;\n};"),
        "Some should be a templated struct:\n{cpp}"
    );
    assert!(
        cpp.contains("struct None {\n};"),
        "None should be a non-templated empty struct:\n{cpp}"
    );

    // Variant alias: templated, with Some<T> and bare None.
    assert!(
        cpp.contains("template<typename T>\nusing Option = std::variant<None, Some<T>>;"),
        "templated variant alias missing or wrong:\n{cpp}"
    );
}

#[test]
fn generic_sum_with_two_params_emits_two_arg_template() {
    // Either = Left(value: L) | Right(value: R) — both templated.
    let source = r#"
        namespace test.gen_either
          enum Either
            sort L = ?
            sort R = ?
            entity Left(value: ?L)
            entity Right(value: ?R)
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_sum(&kb, "test.gen_either.Either")
        .expect("emit Either sum");

    // Each constructor templated independently — Left only mentions L,
    // Right only mentions R, but the alias's full param list is on
    // the alias itself. We instantiate each constructor with the
    // alias's full param list to keep the alias signature uniform.
    assert!(
        cpp.contains("template<typename L, typename R>"),
        "Either alias should template over both params:\n{cpp}"
    );
    assert!(
        cpp.contains("using Either = std::variant<Left<L, R>, Right<L, R>>"),
        "alias arg list should pass both params to each constructor:\n{cpp}"
    );
}

#[test]
fn nullary_sum_unchanged_by_generic_machinery() {
    // Regression: a non-generic enum still emits without `template<>`.
    let source = r#"
        namespace test.gen_nullary
          enum StepResult
            entity Running
            entity Quit
          end
        end
    "#;
    let kb = load_kb_with_lenient(source);
    let cpp = emit_sum(&kb, "test.gen_nullary.StepResult")
        .expect("emit StepResult");

    assert!(
        !cpp.contains("template<"),
        "non-generic sum should not gain a template prefix:\n{cpp}"
    );
    assert!(
        cpp.contains("using StepResult = std::variant<Quit, Running>;"),
        "alias missing:\n{cpp}"
    );
}
