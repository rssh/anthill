//! WI-850 — a declared operation type-param DEFAULT (`operation foo[T = Int64](…)`).
//!
//! WI-850 REFUSED IT, and proposal 069 stage 2 (WI-20261023-GBH5F) GAVE IT A MEANING, which
//! is why the refusal rows here became driven ones. MEASURED on WI-850's parent commit: the
//! grammar parsed the `= Type` form, the converter stored it in `TypeParam.default`, and
//! nobody read it — `[T = Int64]` loaded exactly as `[T]`, and a call that left `T`
//! unconstrained was told to pin `T` with `foo[T = …]`, which the author had written on the
//! declaration. WI-850 took the form out of the language until a driver appeared; 069's was
//! `Function[A, B]`'s purity, and its stage 2 installs an operation's default where WI-270
//! refused the unconstrained parameter (`typing::install_type_param_defaults`).
//!
//! What stays from WI-850 is its rule that a parsed default is never dropped: the converter
//! carries it as the converted type, the loader records it or refuses it at the declaration,
//! and the parse-only code generator emits the operation without it (user, 2026-10-24: a
//! Rust function admits no default type parameter, and generated code holds no call site a
//! default could fill). `wi_gbh5f_operation_type_param_defaults_test` has the stage's rows.

use crate::common::{interp_for, parses_clean};
use anthill_core::codegen::generate_rust;
use anthill_core::parse;

/// THE TICKET'S DECLARATION, `operation foo[T = Int64](x: T) -> T`, LOADS, and a call that
/// leaves `T` to the default is no longer told to pin it: `mk()` over `mk[T = Int64]() ->
/// Type` answers `Int64`. FAILS with the installation backed out: `useMk` is refused as an
/// unconstrained `T`, WI-850's measured complaint.
#[test]
fn the_declared_default_answers_where_wi850_refused_it() {
    let src = r#"
namespace test.wi850.decl
  import anthill.prelude.{Int64, Type}
  import anthill.reflect.{TypeValue}
  operation foo[T = Int64](x: T) -> T = x
  operation mk[T = Int64]() -> Type requires TypeValue[T = T] = TypeValue.type_value[T = T]()
  operation useFoo() -> Int64 = foo(7)
  operation useMk() -> Type = mk()
end
"#;
    let mut interp = interp_for(src);
    let v = interp.call("test.wi850.decl.useFoo", &[]).expect("useFoo");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(7));
    let t = interp.call("test.wi850.decl.useMk", &[]).expect("useMk");
    assert_eq!(anthill_core::kb::typing::type_display_name_value(interp.kb(), &t), "Int64");
}

/// The SECOND declaration spelling — an `operation { … }` block entry — reaches the same
/// converter (`convert_operation_block` → `convert_operation`), so its default is read as
/// the first spelling's is.
#[test]
fn the_operation_block_entry_form_takes_its_default_too() {
    let src = r#"
namespace test.wi850.block
  import anthill.prelude.{Int64, Type}
  import anthill.reflect.{TypeValue}
  sort Driver
    operation {
      mk[T = Int64]() -> Type requires TypeValue[T = T] = TypeValue.type_value[T = T]()
    }
    operation useMk() -> Type = mk()
  end
end
"#;
    let mut interp = interp_for(src);
    let t = interp.call("test.wi850.block.Driver.useMk", &[]).expect("useMk");
    assert_eq!(anthill_core::kb::typing::type_display_name_value(interp.kb(), &t), "Int64");
}

/// EVERY defaulted parameter of one bracket takes its own default, and a bare one beside
/// them its inference: `bOf(true)` and `cOf(true)` over `[A, B = Int64, C = String]` read
/// `B` as `Int64` and `C` as `String`, `A` being the argument's `Bool`.
#[test]
fn each_defaulted_param_takes_its_own_default_and_the_bare_one_its_inference() {
    let src = r#"
namespace test.wi850.several
  import anthill.prelude.{Int64, String, Bool, Type}
  import anthill.reflect.{TypeValue}
  operation bOf[A, B = Int64, C = String](a: A) -> Type requires TypeValue[T = B] =
    TypeValue.type_value[T = B]()
  operation cOf[A, B = Int64, C = String](a: A) -> Type requires TypeValue[T = C] =
    TypeValue.type_value[T = C]()
  operation aOf[A, B = Int64, C = String](a: A) -> Type requires TypeValue[T = A] =
    TypeValue.type_value[T = A]()
  operation b() -> Type = bOf(true)
  operation c() -> Type = cOf(true)
  operation a() -> Type = aOf(true)
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [("b", "Int64"), ("c", "String"), ("a", "Bool")] {
        let t = interp
            .call(&format!("test.wi850.several.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(anthill_core::kb::typing::type_display_name_value(interp.kb(), &t), want, "{op}");
    }
}

/// THE CONTROL a default must not break, driven end to end: a bare `[T]` operation still
/// loads AND runs, with `T` inferred from the argument.
#[test]
fn a_bare_type_param_still_loads_and_runs() {
    let src = r#"
namespace test.wi850.bare
  import anthill.prelude.{Int64}
  sort Driver
    operation identity[T](x: T) -> T = x
    operation drive() -> Int64 = identity(7)
  end
end
"#;
    parses_clean(src);
    let mut interp = interp_for(src);
    match interp
        .call("test.wi850.bare.Driver.drive", &[])
        .expect("drive")
    {
        anthill_core::eval::Value::Int(7) => {}
        other => panic!("a bare `[T]` op must still evaluate; got {other:?}"),
    }
}

/// A parameter pinned at the CALL — the position a bracket is read in (WI-839), and the
/// first source of a parameter's binding, before inference and the default (069 §1.3).
/// A fresh `Interpreter` per call — a trapped call poisons later ones.
#[test]
fn pinning_the_param_at_the_call_is_the_working_alternative() {
    let src = r#"
namespace test.wi850.pinned
  import anthill.prelude.{Int64}
  sort Driver
    operation identity[T](x: T) -> T = x
    operation drive() -> Int64 = identity[T = Int64](7)
  end
end
"#;
    let mut interp = interp_for(src);
    match interp
        .call("test.wi850.pinned.Driver.drive", &[])
        .expect("drive")
    {
        anthill_core::eval::Value::Int(7) => {}
        other => panic!("a call-site pin is the advertised alternative; got {other:?}"),
    }
}

/// THE PARSE-ONLY CODE GENERATOR emits a defaulted operation WITHOUT its default (user,
/// 2026-10-24). `generate_rust` consumes a `&ParsedFile`, never loads a KB and emits no call
/// site, and a Rust function admits no default type parameter, so `fn identity<T>(…)` is
/// the declaration's whole host shape. The bare form is the control: the two generate the
/// same signature.
#[test]
fn the_parse_only_codegen_path_emits_a_defaulted_operation_without_its_default() {
    let gen = |src: &str| {
        let parsed = parse::parse(src).expect("the declaration parses");
        generate_rust(&parsed).expect("the declaration generates")
    };
    let bare = gen("namespace test.wi850.gen\n  sort Driver\n    operation identity[T](x: T) -> T\n  end\nend\n");
    let defaulted = gen(
        "namespace test.wi850.gen\n  import anthill.prelude.{Int64}\n  sort Driver\n    operation identity[T = Int64](x: T) -> T\n  end\nend\n",
    );
    assert!(bare.contains("identity"), "control: the bare form generates; got:\n{bare}");
    let signature = |code: &str| {
        code.lines()
            .find(|l| l.contains("fn identity"))
            .map(str::trim)
            .map(str::to_owned)
            .unwrap_or_else(|| panic!("a `fn identity` line; got:\n{code}"))
    };
    assert_eq!(signature(&defaulted), signature(&bare), "the default is not emitted");
}
