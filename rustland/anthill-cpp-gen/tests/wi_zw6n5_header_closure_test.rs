//! WI-20260823-ZW6N5: a namespace's header CLOSURE — its own header plus every
//! header it includes, transitively — is what a project layout must ship.
//!
//! lf1's `codegen cpp-project` emitted exactly one header, for `--namespace`
//! itself, and named it by its LAST segment (`lf1.hpp`), while every generated
//! cross-namespace `#include` spells the FULL path (`anthill_examples_lf1_leader.hpp`).
//! Once the spec was split per controller the umbrella declared nothing and the
//! scaffold died. `emit_namespace_header_closure` follows the includes the code
//! actually needs; the CLI end of this is `anthill-cli`'s
//! `wi_zw6n5_lf1_scaffold_test`.

use super::common;

use anthill_cpp_gen::emit_namespace_header_closure;
use common::{find_cxx, load_kb_with, scratch_dir};
use std::process::Command;

const SPEC: &str = r#"
namespace test.zw6n5.geo
  import anthill.prelude.{Float}
  entity P(x: Float, y: Float)
end

namespace test.zw6n5.mid
  import test.zw6n5.geo.{P}
  entity Seg(a: P, b: P)
end

namespace test.zw6n5.top
  import anthill.prelude.{Float}
  import test.zw6n5.mid.{Seg}
  sort Ctl
    operation start_x(s: Seg) -> Float = s.a.x
  end
end

namespace test.zw6n5.lit
  import anthill.prelude.{Float}
  import test.zw6n5.geo.{P}
  sort Mk
    operation diag(v: Float) -> Float =
      let p = P(x: v, y: v)
      p.x
  end
end

namespace test.zw6n5.unrelated
  import anthill.prelude.{Float}
  entity Q(v: Float)
end

namespace test.zw6n5.shapes
  import anthill.prelude.{Float}
  sort Shape
    entity Circle(r: Float)
    entity Sq(a: Float)
  end
  sort Mk
    operation mk(x: Float) -> Shape = Circle(r: x)
  end
end

namespace test.zw6n5.draw
  import anthill.prelude.{Float}
  import test.zw6n5.shapes.{Shape}
  import test.zw6n5.shapes.Shape.{Circle}
  sort Pen
    operation dot(x: Float) -> Shape = Circle(r: x)
  end
end
"#;

/// Write every header of a closure into a fresh directory and syntax-check a
/// driver that includes only the ROOT's — so each include the root pulls in must
/// resolve to a file the closure shipped.
fn compile_root(test: &str, headers: &[anthill_cpp_gen::NamespaceHeader], root_file: &str) {
    let Some(cxx) = find_cxx() else {
        eprintln!("no C++ compiler available — skipping {test} compile check");
        return;
    };
    let dir = scratch_dir(test);
    for h in headers {
        std::fs::write(dir.join(&h.filename), &h.text).expect("write header");
    }
    let driver = dir.join("driver.cpp");
    std::fs::write(
        &driver,
        format!("#include \"{root_file}\"\nint main() {{ return 0; }}\n"),
    )
    .expect("write driver");
    let out = Command::new(cxx)
        .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Wextra", "-Werror"])
        .arg(&driver)
        .output()
        .expect("invoke compiler");
    let texts: Vec<String> = headers
        .iter()
        .map(|h| format!("── {} ──\n{}", h.filename, h.text))
        .collect();
    assert!(
        out.status.success(),
        "{root_file} does not compile from its closure (compiler: {cxx})\n{}\n── stderr ──\n{}",
        texts.join("\n"),
        String::from_utf8_lossy(&out.stderr),
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `top` names only `mid.Seg`; `Seg` names `geo.P`. The closure is all three —
/// `geo` reached only THROUGH `mid` — and never the sibling `unrelated`.
/// Fails with the closure cut to the root alone (a one-header layout, as
/// cpp-project had): `geo` / `mid` go missing and the driver does not compile.
#[test]
fn closure_is_transitive_and_follows_references_only() {
    let mut kb = load_kb_with(SPEC);
    let headers = emit_namespace_header_closure(&mut kb, "test.zw6n5.top", None)
        .expect("emit the closure of test.zw6n5.top");

    let names: Vec<(&str, &str)> = headers
        .iter()
        .map(|h| (h.namespace.as_str(), h.filename.as_str()))
        .collect();
    assert_eq!(
        names,
        vec![
            ("test.zw6n5.geo", "test_zw6n5_geo.hpp"),
            ("test.zw6n5.mid", "test_zw6n5_mid.hpp"),
            ("test.zw6n5.top", "test_zw6n5_top.hpp"),
        ],
    );
    let top = &headers[2].text;
    assert!(top.contains("#include \"test_zw6n5_mid.hpp\""), "{top}");
    assert!(
        !top.contains("test_zw6n5_geo.hpp"),
        "top names nothing in geo, so geo arrives through mid's include:\n{top}"
    );

    compile_root("zw6n5_transitive", &headers, "test_zw6n5_top.hpp");
}

/// A constructor literal is a cross-namespace reference too: `diag` builds a
/// `geo.P` that no signature mentions. The literal site used to print
/// `::test::zw6n5::geo::P{…}` WITHOUT registering the include, so the header
/// named a type it never included. MEASURED: with the literal site put back to
/// qualify-without-recording, `geo` leaves the closure and the namespace
/// assertion below fails; the transitive test above passes either way.
#[test]
fn a_constructor_literal_pulls_in_its_namespace() {
    let mut kb = load_kb_with(SPEC);
    let headers = emit_namespace_header_closure(&mut kb, "test.zw6n5.lit", None)
        .expect("emit the closure of test.zw6n5.lit");

    let namespaces: Vec<&str> = headers.iter().map(|h| h.namespace.as_str()).collect();
    assert_eq!(namespaces, vec!["test.zw6n5.geo", "test.zw6n5.lit"]);
    let lit = &headers[1].text;
    assert!(lit.contains("::test::zw6n5::geo::P{"), "{lit}");
    assert!(lit.contains("#include \"test_zw6n5_geo.hpp\""), "{lit}");

    compile_root("zw6n5_literal", &headers, "test_zw6n5_lit.hpp");
}

/// The root is REQUIRED: a namespace declaring nothing emittable is the WI-761
/// empty-namespace error, as for a single header — which is exactly how the lf1
/// umbrella `anthill.examples.lf1` failed.
#[test]
fn an_empty_root_is_refused() {
    let mut kb = load_kb_with(SPEC);
    let err = emit_namespace_header_closure(&mut kb, "test.zw6n5", None)
        .expect_err("test.zw6n5 declares nothing directly");
    assert!(
        err.message
            .contains("to emit directly under namespace 'test.zw6n5'"),
        "{}",
        err.message
    );
}

/// A sum constructor lives in its SORT's scope (`shapes.Shape.Circle`) but its C++
/// struct is emitted beside `using Shape = std::variant<…>` in the NAMESPACE. Its
/// declaring namespace is therefore the nearest ancestor that is not a sort. Reading
/// the plain parent made `Shape` a dependency: the closure shipped a bogus
/// `test_zw6n5_shapes_Shape.hpp` redeclaring `Shape` as a namespace, and the header
/// no longer compiled — MEASURED against `parent_namespace_of` in
/// `qualify_cross_namespace` (found by the /code-review of this change): the first
/// closure assertion fails, `Shape` listed as a namespace. Within the namespace the literal is now the bare `Circle{x}` (it was
/// `::test::zw6n5::shapes::Shape::Circle{x}`, naming no C++ entity); from another
/// namespace it is `::test::zw6n5::shapes::Circle{…}`, including `shapes`' header.
#[test]
fn a_sum_constructor_belongs_to_its_sorts_namespace() {
    let mut kb = load_kb_with(SPEC);

    let own = emit_namespace_header_closure(&mut kb, "test.zw6n5.shapes", None)
        .expect("emit the closure of test.zw6n5.shapes");
    let namespaces: Vec<&str> = own.iter().map(|h| h.namespace.as_str()).collect();
    assert_eq!(namespaces, vec!["test.zw6n5.shapes"]);
    assert!(own[0].text.contains("return Circle{x};"), "{}", own[0].text);
    compile_root("zw6n5_sum_own", &own, "test_zw6n5_shapes.hpp");

    let other = emit_namespace_header_closure(&mut kb, "test.zw6n5.draw", None)
        .expect("emit the closure of test.zw6n5.draw");
    let namespaces: Vec<&str> = other.iter().map(|h| h.namespace.as_str()).collect();
    assert_eq!(namespaces, vec!["test.zw6n5.draw", "test.zw6n5.shapes"]);
    let draw = &other[0].text;
    assert!(draw.contains("::test::zw6n5::shapes::Circle{x}"), "{draw}");
    assert!(
        draw.contains("#include \"test_zw6n5_shapes.hpp\""),
        "{draw}"
    );
    compile_root("zw6n5_sum_other", &other, "test_zw6n5_draw.hpp");
}
