//! K6WFS: `anthill.prelude.Result` in C++ — its type through the `TypeMapping` template
//! (`anthill::runtime::Result<$T, $E>`, success type first), its values built at the
//! type the typer inferred, its `match` read through `is_ok()` / `value()`, and the
//! header compiled and run.
//!
//! MEASURED before the change (the pre-change `anthill` binary on these programs):
//! every one was refused "no C++ mapping for parameterized sort
//! 'anthill.prelude.Result'". With the mapping and without the value / pattern
//! lowering, `ok(n)` died "type variable '?_' is not bound" and the match emitted
//! `std::holds_alternative<ok>(r)`, which does not compile against the runtime type.

use super::common;

use std::process::Command;

use anthill_cpp_gen::{emit_namespace_header, emit_runtime_header};
use common::{find_cxx, load_kb_with, scratch_dir};

const PROGRAM: &str = r#"
    namespace test.rbody
      import anthill.prelude.{Int64, String, Option, Result}
      import anthill.prelude.Result.{ok, err}
      sort Boom
        entity boom(why: String)
      end
      sort Calc
        operation find(n: Int64) -> Option[T = Int64] = none()
        operation check(n: Int64) -> Result[E = Boom, T = Int64] = ok(n)
        operation fail(n: Int64) -> Result[E = String, T = Int64] = err("no")
        operation pick(n: Int64) -> Result[E = String, T = Int64] =
          if n > 0 then ok(n) else err("neg")
        operation get(r: Result[E = String, T = Int64]) -> Int64 =
          match r
            case ok(v) -> v
            case err(e) -> 0
      end
    end
"#;

fn header() -> String {
    let source = PROGRAM.replace(
        "import anthill.prelude.Result.{ok, err}",
        "import anthill.prelude.Result.{ok, err}\n      import anthill.prelude.Option.{none}",
    );
    let mut kb = load_kb_with(&source);
    emit_namespace_header(&mut kb, "test.rbody").expect("emit test.rbody")
}

#[test]
fn result_is_declared_success_first_and_built_at_its_inferred_type() {
    let h = header();
    assert!(
        h.contains("static anthill::runtime::Result<int64_t, Boom> check(int64_t n)"),
        "{h}"
    );
    assert!(
        h.contains(
            "return anthill::runtime::Result<int64_t, std::string>(anthill::runtime::err(\"no\"));"
        ),
        "{h}"
    );
    // The two arms of an `if` have one C++ type only when each is built at it.
    assert!(
        h.contains(
            "((n > 0) ? anthill::runtime::Result<int64_t, std::string>(anthill::runtime::ok(n)) \
             : anthill::runtime::Result<int64_t, std::string>(anthill::runtime::err(\"neg\")))"
        ),
        "{h}"
    );
    assert!(h.contains("r.is_ok() ?"), "{h}");
    assert!(h.contains("auto v = r.value();"), "{h}");
    assert!(h.contains("auto e = r.error();"), "{h}");
    assert!(h.contains("#include \"anthill_runtime.hpp\""), "{h}");
}

#[test]
fn the_result_header_compiles_and_runs() {
    let cxx = match find_cxx() {
        Some(c) => c,
        None => {
            eprintln!("no C++ compiler — skipping the Result header compile check");
            return;
        }
    };
    let dir = scratch_dir("k6wfs_result");
    std::fs::write(dir.join("anthill_runtime.hpp"), emit_runtime_header()).unwrap();
    std::fs::write(dir.join("test_rbody.hpp"), header()).unwrap();
    std::fs::write(
        dir.join("main.cpp"),
        r#"#include "test_rbody.hpp"
int main() {
    using C = test::rbody::Calc;
    auto c = C::check(7);
    return (c.is_ok() && c.value() == 7
            && C::get(C::pick(5)) == 5 && C::get(C::pick(-1)) == 0
            && C::get(C::fail(1)) == 0 && C::fail(1).error() == "no") ? 0 : 1;
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
    let run = Command::new(&exe).status().expect("run");
    assert!(run.success(), "the compiled program answered wrongly");
}

/// A sort written unapplied, to a higher-kinded parameter, stands as its template's
/// name — where the template applies it to the parameters in declaration order. FAILS
/// without `bare_template_name`: `Wrap[F = Option]` was refused "applied without its
/// parameter `T`", where it lowered to `std::optional` before templates. `Result`'s
/// template reorders its parameters, so its name would take them in the wrong order,
/// and it is refused (passes either way: it was refused before for want of a mapping).
#[test]
fn an_unapplied_mapped_sort_stands_as_its_template_name() {
    let program = |arg: &str| {
        format!(
            r#"
            namespace test.hk
              import anthill.prelude.{{Int64, Option, Result}}
              import anthill.realization.{{Implementation, CarrierBinding}}
              import anthill.prelude.Option.{{none}}
              sort Wrap[F[T]]
              end
              fact Implementation(target: "test.hk.Wrap", artifact: "", language: "cpp",
                                  profile: none, description: none,
                                  carrier: [CarrierBinding(sort_name: "Wrap", host_type: "my::Wrap")],
                                  namespace_map: [])
              entity Holder(w: Wrap[F = {arg}])
            end
        "#
        )
    };
    let mut kb = load_kb_with(&program("Option"));
    let h = emit_namespace_header(&mut kb, "test.hk").expect("emit test.hk");
    assert!(h.contains("my::Wrap<std::optional> w;"), "{h}");

    let mut kb = load_kb_with(&program("Result"));
    let err = emit_namespace_header(&mut kb, "test.hk").expect_err("Result has no bare name");
    assert!(
        err.message
            .contains("'anthill.prelude.Result' is written without its parameters"),
        "{}",
        err.message
    );
}

/// `Unit` lowers to `void`, which no template takes: `Result[T = Unit]` is refused
/// naming it. FAILS without the `void` check: the header declared
/// `anthill::runtime::Result<void, std::string>`, which does not compile. CONTROL: the
/// same operation at `T = Int64` lowers.
#[test]
fn unit_as_a_template_argument_is_refused() {
    let program = |t: &str| {
        format!(
            r#"
            namespace test.unitres
              import anthill.prelude.{{Int64, String, Unit, Result}}
              sort Api
                operation save(n: Int64) -> Result[E = String, T = {t}]
              end
            end
        "#
        )
    };
    let mut kb = load_kb_with(&program("Int64"));
    let h = emit_namespace_header(&mut kb, "test.unitres").expect("emit");
    assert!(
        h.contains("anthill::runtime::Result<int64_t, std::string> save"),
        "{h}"
    );

    let mut kb = load_kb_with(&program("Unit"));
    let err = emit_namespace_header(&mut kb, "test.unitres").expect_err("void refused");
    assert!(
        err.message
            .contains("is applied with `T` = Unit, which this profile lowers to `void`"),
        "{}",
        err.message
    );
}
