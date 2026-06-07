//! WI-270 — top-down `expected` type threading.
//!
//! The typer carries the caller's expected type through Visit / Build
//! frames so:
//!
//! 1. A call to `op[E](…) -> Container[E]` without any caller-side
//!    hint surfaces an `UnconstrainedTypeParam` diagnostic naming the
//!    unconstrained parameter (replaces the WI-269 Phase D silent-
//!    drop site).
//! 2. The same call inside `let v: Container[Concrete] = op(…)` pins
//!    `E` to `Concrete` via the let-annotation `expected` flow.
//! 3. A 0-arg constructor in an annotated let — `let xs: List[T =
//!    Int64] = nil()` — typechecks to the annotated parametric type
//!    instead of leaving the element type unbound.
//!
//! Operations under test sit inside a `sort` block because
//! `type_check_sorts` walks operations per-sort; free-standing
//! namespace-level operations aren't reached by the typer pass.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::typing::TypeError;
use anthill_core::parse;

/// Stdlib + extra source → (kb, load errors). The caller asserts the
/// diagnostic shape it expects (or absence of typer-level errors).
fn try_load(extra: &str) -> (KnowledgeBase, Vec<load::LoadError>) {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let result = load::load_all(&mut kb, &refs, &NullResolver);
    let errs = result.err().unwrap_or_default();
    (kb, errs)
}

/// Render load errors as joined strings so an assertion failure shows
/// the actual diagnostic text without dumping the whole Vec.
fn fmt_errs(errs: &[load::LoadError]) -> String {
    errs.iter().map(|e| format!("{}", e)).collect::<Vec<_>>().join("\n")
}

#[test]
fn explicit_type_param_call_without_context_errors_with_unconstrained_type_param() {
    // The let value has no annotation and no `[E = …]` binding, so E
    // is unconstrained and the typer must surface the diagnostic.
    let src = r#"
namespace test.wi270.unconstrained
  import anthill.prelude.{Option, Int64}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term}

  sort Driver
    operation take_entity[E](t: Term) -> Option[T = E]

    operation main(t: Term) -> Int64 =
      let _v = take_entity(t)
      0
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        !errs.is_empty(),
        "expected UnconstrainedTypeParam diagnostic; got clean load",
    );
    let formatted = fmt_errs(&errs);
    assert!(
        formatted.contains("'E'") && formatted.contains("unconstrained"),
        "expected diagnostic to name 'E' as unconstrained; got:\n{formatted}",
    );
    assert!(
        formatted.contains("take_entity[E = "),
        "expected diagnostic to suggest `take_entity[E = …](…)` form; got:\n{formatted}",
    );
}

#[test]
fn explicit_type_param_call_with_let_annotation_pins_e() {
    let src = r#"
namespace test.wi270.pinned_via_let
  import anthill.prelude.{Option}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term}

  entity Item(id: String)

  sort Driver
    operation take_entity[E](t: Term) -> Option[T = E]

    operation main(t: Term) -> Option[T = Item] =
      let v : Option[T = Item] = take_entity(t)
      v
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "expected clean load with let-annotation pin; got:\n{}",
        fmt_errs(&errs),
    );
}

#[test]
fn explicit_type_param_call_with_bindings_pins_e() {
    let src = r#"
namespace test.wi270.pinned_via_bindings
  import anthill.prelude.{Option}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term}

  entity Item(id: String)

  sort Driver
    operation take_entity[E](t: Term) -> Option[T = E]

    operation main(t: Term) -> Option[T = Item] = take_entity[E = Item](t)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "expected clean load with explicit `[E = Item]` binding; got:\n{}",
        fmt_errs(&errs),
    );
}

#[test]
fn no_such_type_param_binding_name_errors() {
    let src = r#"
namespace test.wi270.no_such_param
  import anthill.prelude.{Option}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term}

  entity Item(id: String)

  sort Driver
    operation take_entity[E](t: Term) -> Option[T = E]

    -- `Q` is not a declared type parameter of `take_entity`. Should
    -- surface `NoSuchTypeParam` rather than silently dropping the
    -- binding the way pre-WI-270 did.
    operation main(t: Term) -> Option[T = Item] = take_entity[Q = Item](t)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        !errs.is_empty(),
        "expected NoSuchTypeParam diagnostic; got clean load",
    );
    let formatted = fmt_errs(&errs);
    assert!(
        formatted.contains("'Q'"),
        "expected diagnostic to name 'Q' as unknown type-param; got:\n{formatted}",
    );
}

#[test]
fn nil_in_annotated_let_pins_list_element_type() {
    let src = r#"
namespace test.wi270.nil_pinned
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{nil, cons}

  sort Driver
    operation main() -> List[T = Int64] =
      let xs : List[T = Int64] = nil()
      xs
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "expected `nil()` in let `List[T = Int64]` to typecheck; got:\n{}",
        fmt_errs(&errs),
    );
}

#[test]
fn nil_in_operation_return_position_pins_element_type() {
    // WI-270 driver (c): `operation foo() -> List[Int64] = nil()` —
    // the body's expected flows from the declared return type.
    let src = r#"
namespace test.wi270.nil_op_return
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{nil, cons}

  sort Driver
    operation empty_ints() -> List[T = Int64] = nil()
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "expected `nil()` as op body to typecheck with return-type hint; got:\n{}",
        fmt_errs(&errs),
    );
}

// ── WI-269 Phase F (typing-only acceptance bullets) ──────────────
//
// Frame-inspection of `foo[T](x: T) -> T` per the operation-call
// model design doc needs Phase E (eval threads type-args through
// `frame.requirements`), tracked separately. The typing-only
// bullets — foo[A,B] / map[A,B,C] — close out here.

#[test]
fn foo_two_type_params_parses_loads_and_typechecks() {
    // The proposal-042 acceptance fixture: declare a two-parameter
    // op, build a Pair from its args, then call it with explicit
    // bindings and observe a typed return.
    let src = r#"
namespace test.wi269.foo_two_params
  import anthill.prelude.{Pair, Int64, String}
  import anthill.prelude.Pair.{pair}

  sort Driver
    operation foo[A, B](a: A, b: B) -> Pair[A = A, B = B] = pair(a, b)
    operation main() -> Pair[A = Int64, B = String] =
      foo[A = Int64, B = String](42, "hi")
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "foo[A, B] should parse + load + type-check; got:\n{}",
        fmt_errs(&errs),
    );
}

#[test]
fn map_two_type_params_explicit_call_typechecks() {
    // map[A, B](xs: List[A], f: (A) -> B) -> List[B] with explicit
    // [A = Int64, B = String] at the call site. Tests that explicit
    // bindings unify through nested parameterized types and through
    // arrow-typed parameters.
    let src = r#"
namespace test.wi269.map_explicit
  import anthill.prelude.{List, Int64, String}

  sort Driver
    operation map[A, B](xs: List[T = A], f: (A) -> B) -> List[T = B]
    operation drive(xs: List[T = Int64], f: (Int64) -> String) -> List[T = String] =
      map[A = Int64, B = String](xs, f)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "map[A, B] with explicit bindings should type-check; got:\n{}",
        fmt_errs(&errs),
    );
}

#[test]
fn map_two_type_params_inferred_from_args_typechecks() {
    // Same map signature, but the caller leaves the [A, B] off and
    // lets the typer infer them from the arg types. WI-270 added the
    // caller-side `expected` flow plus arg-driven unification — this
    // fixture exercises the latter.
    let src = r#"
namespace test.wi269.map_inferred
  import anthill.prelude.{List, Int64, String}

  sort Driver
    operation map[A, B](xs: List[T = A], f: (A) -> B) -> List[T = B]
    operation drive(xs: List[T = Int64], f: (Int64) -> String) -> List[T = String] =
      map(xs, f)
  end
end
"#;
    let (_kb, errs) = try_load(src);
    assert!(
        errs.is_empty(),
        "map[A, B] with inferred bindings should type-check; got:\n{}",
        fmt_errs(&errs),
    );
}

/// Unit-level check of the structured `TypeError` shape (independent
/// of the load-error stringification). Confirms the diagnostic is
/// reachable from in-tree code.
#[test]
fn unconstrained_type_param_format_names_parameter() {
    let mut kb = KnowledgeBase::new();
    let op_sym = kb.intern("test.wi270.take_entity");
    let e_sym = kb.intern("E");
    let err = TypeError::UnconstrainedTypeParam {
        span: None,
        op: op_sym,
        type_param: e_sym,
    };
    let formatted = err.format(&kb);
    assert!(formatted.contains("'E'"), "should name 'E'; got {formatted}");
    assert!(
        formatted.contains("[E = "),
        "should suggest `[E = …]`; got {formatted}",
    );
}
