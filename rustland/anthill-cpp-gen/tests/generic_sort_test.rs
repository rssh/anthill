//! Slice 1 of generic-sort support: first-order (non-higher-kinded)
//! type parameters on sorts.
//!
//! Covers:
//! - entity inside a parameterised sort emits `template<typename T> struct …`
//! - traits-class for a parameterised sort emits a template prefix and
//!   substitutes `T` references in operation parameter / return types
//! - multi-param sorts emit `template<typename A, typename B>`
//! - non-generic sorts continue to emit without a template prefix
//! - keyword clashes get suffixed (`class` → `class0`)
//!
//! Out of scope (later slices):
//! - higher-kinded params (`F[T = ?]` where F itself is a parameter)
//! - generic sum sorts (`enum Tree { entity Leaf(value: T); ... }`)

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_entity_struct, emit_namespace_header, emit_traits_struct};
use common::{find_cxx, load_kb_with, scratch_dir};

#[test]
fn generic_entity_emits_template_prefix() {
    let source = r#"
        namespace test.gen_box
          sort Box
            sort T = ?
            entity Box(value: T)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.gen_box.Box").expect("emit Box");

    assert!(
        cpp.contains("template<typename T>\nstruct Box {\n    T value;\n};"),
        "generic entity should emit template prefix:\n{cpp}"
    );
}

#[test]
fn multi_param_entity_emits_template_with_two_args() {
    let source = r#"
        namespace test.gen_pair
          sort Pair
            sort A = ?
            sort B = ?
            entity Pair(first: A, second: B)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.gen_pair.Pair").expect("emit Pair");

    assert!(
        cpp.contains("template<typename A, typename B>"),
        "multi-param prefix missing:\n{cpp}"
    );
    assert!(
        cpp.contains("A first;") && cpp.contains("B second;"),
        "field types should reference template params:\n{cpp}"
    );
}

#[test]
fn non_generic_entity_keeps_no_prefix() {
    // Sanity: a plain entity-with-fields emits without `template<…>`.
    let source = r#"
        namespace test.plain
          import anthill.prelude.{Int64}
          entity Pose(x: Int64, y: Int64)
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.plain.Pose").expect("emit Pose");

    assert!(
        !cpp.contains("template<"),
        "non-generic entity should not emit a template prefix:\n{cpp}"
    );
    assert!(cpp.contains("struct Pose {"), "struct missing:\n{cpp}");
}

#[test]
fn generic_traits_class_emits_template_prefix() {
    // The traits class for a generic sort emits `template<typename T>`
    // and substitutes the sort's `T` in operation parameter / return types.
    //
    // A VARIABLE `?T` IN THE SIGNATURE IS NOT THE SORT'S `T` (§5.4, proposal 070): it is
    // the operation's own type parameter, so `pass2` is a template of its own. This row
    // wrote `pass(x: ?T)` and read the class's `T` back by the coincidence of the name.
    let source = r#"
        namespace test.gen_id
          sort Identity
            sort T = ?
            operation pass(x: T) -> T = x
            operation pass2(x: ?T) -> ?T = x
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.gen_id.Identity").expect("emit Identity");

    assert!(
        cpp.contains("template<typename T>\nstruct Identity {"),
        "generic traits class should emit template prefix:\n{cpp}"
    );
    assert!(
        cpp.contains("static T pass(T x)"),
        "operation signature should use template parameter T:\n{cpp}"
    );
    assert!(
        cpp.contains("template<typename T0>\n    static T0 pass2(T0 x)"),
        "a variable written in the signature is the operation's own template parameter:\n{cpp}"
    );
}

/// WI-20260911-VNQTR — a variable a signature writes in a parameter type is a template
/// parameter of the operation's own, apart from a bracket's or the sort's parameter of the
/// same name and from a value parameter of its name. Held in the frame by its name, `?U`
/// took the bracket `U`'s place and `?T` the sort's `T` — every `U` lowered to the
/// variable's parameter, which no call can deduce — and `keep(x: ?x)` named its template
/// parameter like its value parameter, which C++ refuses (MEASURED, g++).
#[test]
fn an_inline_variable_is_a_template_parameter_of_its_own() {
    let source = r#"
        namespace test.gen_inline
          sort Identity
            sort T = ?
            operation pass4[U](a: U, b: ?U) -> U = a
            operation mix(a: T, b: ?T) -> T = a
            operation keep(x: ?x) -> ?x = x
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.gen_inline.Identity").expect("emit Identity");
    assert!(
        cpp.contains("template<typename U, typename U0>\n    static U pass4(U a, U0 b)"),
        "a bracket and a variable of one name are two template parameters:\n{cpp}"
    );
    assert!(
        cpp.contains("template<typename T0>\n    static T mix(T a, T0 b)"),
        "the sort's `T` stays the class's beside a variable `?T`:\n{cpp}"
    );
    assert!(
        cpp.contains("template<typename x0>\n    static x0 keep(x0 x)"),
        "a template parameter is not named like a value parameter:\n{cpp}"
    );
}

#[test]
fn keyword_clash_gets_suffixed() {
    // A type parameter named `class` would collide with the C++
    // keyword — the canonicaliser appends a `0` (or higher) suffix
    // so the emitted template stays valid.
    let source = r#"
        namespace test.gen_kw
          sort Holder
            sort class = ?
            entity Holder(value: class)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_entity_struct(&mut kb, "test.gen_kw.Holder").expect("emit Holder");

    assert!(
        cpp.contains("template<typename class0>"),
        "keyword param should be suffixed to 'class0':\n{cpp}"
    );
    assert!(
        cpp.contains("class0 value;"),
        "field type should use suffixed name:\n{cpp}"
    );
}

/// A sort's parameter written by its name — the only way a field names it (§5.2: a
/// `?T` there is the entity's own variable) — is the template parameter, in the member
/// form, the bracket form, through an alias and inside a mapped type. The loader stores
/// such a field as the parameter's variable, whose name is `_`, and cpp-gen looked the
/// parameter up by that name: every program here was refused "type variable '?_' is not
/// bound". FAILS with `type_param_of_var` backed out; and with `type_references_param`'s
/// variable arm backed out the sum constructors lose their `<T>`.
#[test]
fn a_sort_parameter_written_by_its_name_is_the_template_parameter() {
    let header = |body: &str| {
        let source = format!(
            "namespace test.gs_bare\n  import anthill.prelude.{{List, Option}}\n{body}\nend\n"
        );
        let mut kb = load_kb_with(&source);
        emit_namespace_header(&mut kb, "test.gs_bare").expect("emit test.gs_bare")
    };
    let one = "template<typename T>\nstruct one {\n    T v;\n};";
    let alias = "template<typename T>\nusing Box = std::variant<one<T>>;";
    for body in [
        "  sort Box\n    sort T = ?\n    entity one(v: T)\n  end",
        "  sort Box[T]\n    entity one(v: T)\n  end",
        "  sort Box[T]\n    sort Elem = T\n    entity one(v: Elem)\n  end",
    ] {
        let h = header(body);
        assert!(h.contains(one) && h.contains(alias), "{body}:\n{h}");
    }
    let h = header("  sort Pair2[A, B]\n    entity mk(a: A, b: B)\n  end");
    assert!(
        h.contains("template<typename A, typename B>\nstruct mk {\n    A a;\n    B b;\n};"),
        "{h}"
    );
    let h = header(
        "  sort Bag[T]\n    entity many(vs: List[T = T], first: Option[T = T])\n  end",
    );
    assert!(
        h.contains("    std::vector<T> vs;\n    std::optional<T> first;"),
        "{h}"
    );
}

/// A variable written in a field is the entity's own (§5.2), not the sort's parameter
/// of its name, and C++ has no template parameter for it. Emitted as the class's `T`
/// before, by the coincidence of the name — where the typer reads `one(v: "x")` at
/// `Box[T = Int64]` as well typed. FAILS when the frame is keyed by name.
#[test]
fn a_variable_written_in_a_field_is_no_sort_parameter() {
    let source = r#"
        namespace test.gs_var
          sort Box
            sort T = ?
            entity Box(value: ?T)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_entity_struct(&mut kb, "test.gs_var.Box").expect_err("?T is no parameter");
    assert!(
        err.message
            .contains("type variable '?T' is no type parameter of an enclosing sort"),
        "{}",
        err.message
    );
}

/// The namespace's own sort `T`, named in an operation of a sort whose parameter is `T`,
/// is that sort (the typer accepts `get(x: tval(x: 1), y: 5)` and refuses `x: 7`) — and
/// inside `template<typename T>` a plain `T` is the parameter, so it is written with its
/// path. FAILS with `is_template_param_name` backed out (`static T get(T x, T y)`, which
/// does not compile against the call below), and when the parameter is looked up by the
/// sort's short name.
#[test]
fn a_namespace_sort_spelled_like_a_template_parameter_is_written_with_its_path() {
    let source = r#"
        namespace test.gs_hide
          import anthill.prelude.{Int64}
          sort T
            entity tval(x: Int64)
          end
          sort Wrap[T]
            operation get(x: test.gs_hide.T, y: T) -> T = y
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let h = emit_namespace_header(&mut kb, "test.gs_hide").expect("emit test.gs_hide");
    assert!(h.contains("static T get(::test::gs_hide::T x, T y)"), "{h}");

    let Some(cxx) = find_cxx() else {
        eprintln!("no C++ compiler — skipping the compile check");
        return;
    };
    let dir = scratch_dir("gs_hide");
    std::fs::write(dir.join("test_gs_hide.hpp"), &h).unwrap();
    std::fs::write(
        dir.join("main.cpp"),
        r#"#include "test_gs_hide.hpp"
int main() {
    test::gs_hide::T t = test::gs_hide::tval{1};
    return test::gs_hide::Wrap<long>::get(t, 4) == 4 ? 0 : 1;
}
"#,
    )
    .unwrap();
    let exe = dir.join("main");
    let out = Command::new(cxx)
        .args(["-std=c++17", "-o"])
        .arg(&exe)
        .arg(dir.join("main.cpp"))
        .arg("-I")
        .arg(&dir)
        .output()
        .expect("invoke compiler");
    assert!(
        out.status.success(),
        "compile failed ({cxx}):\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(Command::new(&exe).status().expect("run").success());
}

/// An entity of a nested sort naming the outer sort's parameter: its struct is a template
/// over its own sort's parameters only, and the refusal says the parameter is out of
/// scope. It advised a `CarrierBinding` for "sort 'test.gs_nest.Outer.T'" — FAILS with the
/// `type_param_out_of_scope` arm of `sort_to_cpp` backed out. The struct is refused either
/// way. The arm for the parameter's VARIABLE is the same refusal on the other carrier, and
/// no row reaches it: the loader writes an outer parameter in a field by its declaration.
#[test]
fn an_outer_sort_parameter_is_refused_by_its_name() {
    let source = r#"
        namespace test.gs_nest
          sort Outer[T]
            sort Inner[U]
              entity e(v: T, u: U)
            end
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let err = emit_entity_struct(&mut kb, "test.gs_nest.Outer.Inner.e")
        .expect_err("the outer parameter is not in the struct's template");
    assert!(
        err.message.contains(
            "type parameter 'test.gs_nest.Outer.T' has no C++ template parameter"
        ),
        "{}",
        err.message
    );
}
