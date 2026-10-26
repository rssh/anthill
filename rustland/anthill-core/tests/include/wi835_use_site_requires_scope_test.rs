//! WI-835 — the USE-SITE `requires Eq` check covers EVERY written type position,
//! not just entity fields.
//!
//! WI-644 shipped the check (see `wi644_use_site_requires_test`) but scoped it to
//! entity FIELD types, which left its own acceptance program — `operation m() ->
//! Map[K = Float, V = Int64]` — loading clean: nothing distinguished `Map[K =
//! Float]` from `Map[K = TotalFloat]`, so the acceptance pair passed only
//! VACUOUSLY. The sites are now recorded by the sole type lowering
//! (`type_expr_to_child`'s `Parameterized` arm), so the scope follows the PRODUCER
//! rather than a list — which is what the entity-field enumeration got wrong.
//!
//! Every position below is one this file MEASURED as newly covered. They are
//! pinned individually rather than as one representative, because "the producer
//! covers them" is the claim under test: a future change that re-routes any one
//! position past the lowering must fail here, not pass by association.
//!
//! The entity-field cases and the lawful-key controls stay in
//! `wi644_use_site_requires_test`; this file adds the positions that escaped.

fn errors_for(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default()
}

/// The refusal must name all four parts of the acceptance diagnostic — the SORT,
/// its own PARAMETER, the required SPEC, and the CARRIER bound there.
fn assert_non_eq_key_error(errs: &[String], container: &str, param: &str, carrier: &str) {
    assert!(
        errs.iter().any(|e| {
            e.contains(container)
                && e.contains(carrier)
                && e.contains("Eq")
                && e.contains(&format!("`{param}`"))
        }),
        "expected a `{container}` requires-`Eq`-at-`{param}` error naming `{carrier}`; got:\n{}",
        errs.join("\n"),
    );
}

fn assert_loads_clean(src: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("expected a clean load; got errors:\n{}", errs.join("\n"));
    }
}

// ── The positions WI-644's entity-field scope missed ────────────────────────

/// The ticket's own EMPIRICAL GAP program: an operation RETURN type. Loaded clean
/// before WI-835.
#[test]
fn float_key_in_operation_return_type_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.ret
  import anthill.prelude.{Map, Float, Int64}
  operation m() -> Map[K = Float, V = Int64] = Map.empty()
end
"#,
    );
    assert_non_eq_key_error(&errs, "Map", "K", "Float");
}

/// An operation PARAMETER type — the other half of a signature.
#[test]
fn float_key_in_operation_param_type_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.param
  import anthill.prelude.{Map, Float, Int64, Bool}
  operation f(m: Map[K = Float, V = Int64]) -> Bool = true
end
"#,
    );
    assert_non_eq_key_error(&errs, "Map", "K", "Float");
}

/// `Set[T = Float]` in a signature — the acceptance's second container.
#[test]
fn float_element_set_in_operation_return_type_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.setret
  import anthill.prelude.{Set, Float}
  operation s() -> Set[T = Float] = Set.empty()
end
"#,
    );
    assert_non_eq_key_error(&errs, "Set", "T", "Float");
}

/// A NESTED instantiation: the inner `Set[T = Float]` is refused on its own,
/// without appearing anywhere as a type in its own right. WI-644's doc listed this
/// as deliberate non-scope ("caught only if it also appears as a field type");
/// recording at the lowering closes it, since the recursion visits every written
/// instantiation.
#[test]
fn float_key_nested_inside_another_instantiation_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.nested
  import anthill.prelude.{Map, Set, Float, Int64}
  operation m() -> Map[K = Int64, V = Set[T = Float]] = Map.empty()
end
"#,
    );
    assert_non_eq_key_error(&errs, "Set", "T", "Float");
}

/// A Float-CONTAINING composite (WI-664 derives `NonEq` for it) in a signature —
/// the derived half of the acceptance, in a position WI-644 did not reach.
#[test]
fn float_composite_key_in_operation_signature_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.composite
  import anthill.prelude.{Map, Float, Int64}
  sort Pt
    entity pt(x: Float, y: Float)
  end
  operation m() -> Map[K = Pt, V = Int64] = Map.empty()
end
"#,
    );
    assert_non_eq_key_error(&errs, "Map", "K", "Pt");
}

/// A `sort S = <instantiation>` ALIAS — a declared type with no field and no
/// signature at all.
#[test]
fn float_key_in_a_sort_alias_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.alias
  import anthill.prelude.{Map, Float, Int64}
  sort FloatIndex = Map[K = Float, V = Int64]
end
"#,
    );
    assert_non_eq_key_error(&errs, "Map", "K", "Float");
}

/// Nested inside a TUPLE component, and inside an ARROW parameter — the two
/// structural type shapes that are not themselves instantiations, so the recursion
/// through them is what carries the check.
#[test]
fn float_element_set_nested_in_a_tuple_component_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.tuple
  import anthill.prelude.{Set, Float, Int64}
  operation t() -> (a: Int64, b: Set[T = Float]) = (a: 1, b: Set.empty())
end
"#,
    );
    assert_non_eq_key_error(&errs, "Set", "T", "Float");
}

#[test]
fn float_element_set_nested_in_an_arrow_param_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.arrow
  import anthill.prelude.{Set, Float, Bool}
  operation h(f: (Set[T = Float]) -> Bool) -> Bool = true
end
"#,
    );
    assert_non_eq_key_error(&errs, "Set", "T", "Float");
}

/// The POSITIONAL binding spelling. `Map[Float, Int64]` binds `K` by position, and
/// the diagnostic must still name `K`, which the author never wrote. What this pins
/// is the LOWERING's positional→declared-param mapping, which is where that mapping
/// happens; the recorded site is always named, so there is no positional case left
/// downstream (an earlier cut carried a second positional mapping in the check, and
/// it was dead code this test would not have caught).
#[test]
fn a_positionally_bound_float_key_is_a_load_error_naming_the_declared_param() {
    let errs = errors_for(
        r#"
namespace test.wi835.positional
  import anthill.prelude.{Map, Float, Int64}
  operation m() -> Map[Float, Int64] = Map.empty()
end
"#,
    );
    assert_non_eq_key_error(&errs, "Map", "K", "Float");
}

/// A `const`'s declared type.
#[test]
fn float_element_set_in_a_const_type_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.constty
  import anthill.prelude.{Set, Float}
  const empties: Set[T = Float] = Set.empty()
end
"#,
    );
    assert_non_eq_key_error(&errs, "Set", "T", "Float");
}

/// A binding VALUE inside a `requires` clause. This reaches `sort_binding_to_value`,
/// NOT `type_expr_to_child` — two independent `TypeExpr::Parameterized` lowerings —
/// so recording at only the ordinary one let a Float key written in a spec clause
/// load clean. The comment claiming a "sole type lowering" was the bug.
#[test]
fn float_key_in_a_requires_clause_binding_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.reqclause
  import anthill.prelude.{Map, Float, Int64, Iterable}
  sort Idx
    requires Iterable[C = Map[K = Float, V = Int64], Element = Int64, E = {}]
  end
end
"#,
    );
    assert_non_eq_key_error(&errs, "Map", "K", "Float");
}

/// A DENOTED-bearing sibling must not disable the check for the carrier bindings
/// beside it. The literal `3` poisons the whole instantiation to a `Value::Node`,
/// which has no ground term — so recording the assembled TERM dropped `K = Float`
/// with it, and adding an unrelated value-in-type argument silently turned the
/// lawful-key check off. Recording the BINDINGS drops only the denoted one.
#[test]
fn a_denoted_sibling_binding_does_not_disable_the_key_check() {
    let src = r#"
namespace test.wi835.denoted
  import anthill.prelude.{Map, Float, Int64}
  sort Buf
    sort T = ?
    sort N = ?
    entity Buf(v: T)
  end
  sort H
    entity H(m: Map[K = Float, V = Buf[T = Int64, N = 3]])
  end
end
"#;
    assert_non_eq_key_error(&errors_for(src), "Map", "K", "Float");
    // Control: the same literal with a LAWFUL key still loads, so the refusal above
    // is about `K = Float` and not about the value-in-type itself.
    assert_loads_clean(
        &src.replace("K = Float", "K = Int64")
            .replace("wi835.denoted", "wi835.denotedok"),
    );
}

/// A body `let` ANNOTATION and a typed LAMBDA BINDER. Both are written inside an
/// operation body rather than in its signature, and both still lower through
/// `type_expr_to_child` — measured, not assumed (an earlier draft of the check's doc
/// claimed the opposite as deliberate non-scope, and a probe refuted it).
#[test]
fn float_key_in_a_body_let_annotation_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.letanno
  import anthill.prelude.{Map, Float, Int64, Bool}
  operation f() -> Bool =
    let m: Map[K = Float, V = Int64] = Map.empty()
    true
end
"#,
    );
    assert_non_eq_key_error(&errs, "Map", "K", "Float");
}

#[test]
fn float_element_set_on_a_typed_lambda_binder_is_a_load_error() {
    let errs = errors_for(
        r#"
namespace test.wi835.lambda
  import anthill.prelude.{Set, Float, Bool}
  operation g() -> Bool =
    let h = lambda (s: Set[T = Float]) -> true
    true
end
"#,
    );
    assert_non_eq_key_error(&errs, "Set", "T", "Float");
}

// ── The refusal is LOCATED ──────────────────────────────────────────────────

/// Loud-over-silent: the refusal is a LOAD error that points at the instantiation
/// it is about. For a nested one that means the INNER base name's position, not
/// the enclosing annotation's — `Set` sits at column 39 of the operation line.
#[test]
fn the_refusal_names_the_line_and_column_of_the_offending_instantiation() {
    let errs = errors_for(
        r#"
namespace test.wi835.located
  import anthill.prelude.{Map, Set, Float, Int64}
  operation m() -> Map[K = Int64, V = Set[T = Float]] = Map.empty()
end
"#,
    );
    assert!(
        errs.iter().any(|e| e.contains("4:39") && e.contains("Set")),
        "expected the refusal located at the inner `Set` (line 4, col 39); got:\n{}",
        errs.join("\n"),
    );
}

/// Two refusals are TWO things to fix, so both must be reported — including when
/// the two sites sit at the SAME byte offsets in DIFFERENT files. Byte offsets are
/// per-file, so a site key that carried only the offsets (and not the `SourceId`)
/// collapsed these two into one and silently dropped the second file's diagnostic —
/// measured on byte-identical-layout files before the key was widened to the whole
/// `SourceSpan`.
#[test]
fn one_refusal_per_site_including_across_files_at_equal_offsets() {
    let a = r#"
namespace test.wi835.xfa
  import anthill.prelude.{Map, Float, Int64}
  operation m() -> Map[K = Float, V = Int64] = Map.empty()
end
"#;
    // Same LENGTH up to the namespace name, so the `Map` base name lands on the
    // identical byte offset in both files — the collision the key must survive.
    let b = a.replace("xfa", "xfb");
    let errs = crate::common::try_load_kb_with_files(&[a, &b])
        .err()
        .unwrap_or_default();
    let refusals = errs
        .iter()
        .filter(|e| e.contains("does not provide `Eq`") && e.contains("Map"))
        .count();
    assert_eq!(
        refusals,
        2,
        "expected one refusal per file (2), got {refusals}; errors:\n{}",
        errs.join("\n"),
    );
}

// ── The controls: lawful keys still load in the SAME positions ──────────────

/// The acceptance's lawful pairs, in the newly-covered signature positions —
/// widening the scope must not make a lawful key fail where it used to pass.
#[test]
fn lawful_keys_in_operation_signatures_load() {
    assert_loads_clean(
        r#"
namespace test.wi835.lawful
  import anthill.prelude.{Map, Set, Int64, String, TotalFloat}
  operation m1() -> Map[K = TotalFloat, V = Int64] = Map.empty()
  operation m2() -> Map[K = Int64, V = Int64] = Map.empty()
  operation m3() -> Map[K = String, V = Int64] = Map.empty()
  operation s1(s: Set[T = Int64]) -> Set[T = Int64] = s
end
"#,
    );
}

/// A `Float` in a NON-key position is untouched: `Map[V = Float]` is lawful — only
/// the parameter the container `requires Eq` at is constrained. The check is not
/// "no Floats in containers".
#[test]
fn a_float_value_type_is_not_a_key_and_loads() {
    assert_loads_clean(
        r#"
namespace test.wi835.value
  import anthill.prelude.{Map, Float, Int64}
  operation m() -> Map[K = Int64, V = Float] = Map.empty()
end
"#,
    );
}

// ── The documented NON-scope, pinned so it stays known ──────────────────────

/// WI-20260919-9KYPA — THE PARAMETRIC HALF OF THIS GAP IS CLOSED, and this test is the
/// inversion its previous form asked for ("it should be inverted when WI-664's
/// parametric-container propagation lands"). A `List[T = Float]` key is refused where the
/// type is written, through the conditional `NonEq[List] :- NonEq[T]` row `eq_derive`
/// derives and the goal `check_use_site_requires_eq` now resolves against it.
///
/// The refusal names the WHOLE key, `List[T = Float]` — not `List`, which is a lawful
/// container at every other argument.
#[test]
fn a_parametric_key_over_float_is_refused() {
    let errs = errors_for(
        r#"
namespace test.wi835.gaplist
  import anthill.prelude.{Map, List, Float, Int64}
  operation m() -> Map[K = List[T = Float], V = Int64] = Map.empty()
end
"#,
    );
    assert_non_eq_key_error(
        &errs,
        "anthill.prelude.Map",
        "K",
        "anthill.prelude.List[T = anthill.prelude.Float]",
    );
}

/// A tuple key whose unlawfulness lives in a component is refused: a tuple provides `Eq`
/// when each component's type does, and `Float` does not. FAILS with the positive check
/// backed out — it loaded clean, the gap this row used to pin.
#[test]
fn a_tuple_key_over_float_is_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(
            r#"
namespace test.wi835.gaptuple
  import anthill.prelude.{Map, Float, Int64}
  operation m() -> Map[K = (a: Float), V = Int64] = Map.empty()
end
"#,
        ),
        &["anthill.prelude.Map", "`K = (a: Float)`", "does not provide `Eq`"],
        "a tuple key over Float",
    );
}

/// A container over the enclosing operation's own TYPE PARAMETER is abstract, not a
/// concrete carrier — the check must defer, in a signature exactly as it does in a
/// field.
#[test]
fn a_container_over_an_operation_type_param_loads() {
    assert_loads_clean(
        r#"
namespace test.wi835.abstract
  import anthill.prelude.{Map, Int64}
  operation m[A]() -> Map[K = A, V = Int64] = Map.empty()
end
"#,
    );
}

// ── A key must provide `Eq` (user, 2026-10-26) ──────────────────────────────
//
// The check is POSITIVE: the written key type must provide `Eq`, where it used to refuse
// only a witnessed `NonEq`. A tuple provides `Eq` when each component's type does.
//
// CONTROLS — measured with each half backed out:
//   FAIL with the positive check backed out (the negative one restored), loading clean:
//     a_dictionary_reference_is_no_key, a_function_is_no_key, a_set_of_functions_is_refused,
//     an_entity_holding_a_function_is_no_key, a_tuple_key_over_float_is_refused (above);
//     and outside this file wi_9kypa's a_tuple_key_over_float_is_refused, wi858's
//     a_pair_of_floats_loads_and_is_no_lawful_key, wi_5nszy's
//     the_set_literal_spelling_is_refused_at_the_sets_type, and the capability matrix's
//     set-literal cells.
//   FAIL with the tuple rule backed out (a tuple asked the `Eq` goal like any type):
//     a_tuple_of_lawful_components_is_a_key, a_nested_tuple_is_a_key, the_unit_is_a_key;
//     and every row of wi_qj6x1_a_builtin_judges_the_value_test, whose shared fixture
//     writes `Map[K = (Int64, Int64)]`.
//   FAIL with `Symbol`'s `Eq` provision backed out (reflect.anthill): a_symbol_is_a_key
//   FAIL with a tie between two `Eq` providers counted as no `Eq`:
//     a_key_whose_eq_two_providers_give_is_a_key
//   PASS either way, by design: a_lawful_entity_is_a_key,
//     a_parametric_key_is_a_key_at_a_lawful_argument, a_term_is_no_key

/// `n` as a program with one operation over `ty`.
fn key_program(n: &str, ty: &str) -> String {
    format!(
        "namespace test.wi835.pos{n}\n  import anthill.prelude.{{Map, Set, List, Option, Int64, Bool, String, Float, Function, Unit}}\n  import anthill.realization.runtime.{{OpRef}}\n  import anthill.reflect.{{Symbol, Term}}\n  sort Box\n    entity bx(v: Int64)\n  end\n  sort Holder\n    entity h(f: Function[A = Int64, B = Int64])\n  end\n  operation m(s: {ty}) -> Int64 = 1\nend\n"
    )
}

#[test]
fn a_dictionary_reference_is_no_key() {
    let errs = errors_for(&key_program("opref", "Map[K = OpRef, V = Int64]"));
    assert_non_eq_key_error(&errs, "Map", "K", "OpRef");
}

#[test]
fn a_function_is_no_key() {
    let errs = errors_for(&key_program(
        "fn",
        "Map[K = Function[A = Int64, B = Int64], V = Int64]",
    ));
    assert_non_eq_key_error(&errs, "Map", "K", "Function");
}

#[test]
fn a_set_of_functions_is_refused() {
    let errs = errors_for(&key_program("setfn", "Set[T = Function[A = Int64, B = Int64]]"));
    assert_non_eq_key_error(&errs, "Set", "T", "Function");
}

/// An entity whose field has no equality derives none, so it is no key either.
#[test]
fn an_entity_holding_a_function_is_no_key() {
    let errs = errors_for(&key_program("holder", "Map[K = Holder, V = Int64]"));
    assert_non_eq_key_error(&errs, "Map", "K", "Holder");
}

#[test]
fn a_tuple_of_lawful_components_is_a_key() {
    assert_loads_clean(&key_program("tup", "Map[K = (Int64, Bool), V = Int64]"));
    assert_loads_clean(&key_program("ntup", "Map[K = (a: Int64, b: String), V = Int64]"));
}

#[test]
fn a_nested_tuple_is_a_key() {
    assert_loads_clean(&key_program("nest", "Map[K = ((Int64, Bool), String), V = Int64]"));
}

#[test]
fn the_unit_is_a_key() {
    assert_loads_clean(&key_program("unit", "Map[K = Unit, V = Int64]"));
}

/// The controls of the positive reading: a composite whose fields are lawful derives `Eq`,
/// and a parametric sort's conditional `Eq` holds at a lawful argument.
#[test]
fn a_lawful_entity_is_a_key() {
    assert_loads_clean(&key_program("box", "Map[K = Box, V = Int64]"));
}

#[test]
fn a_parametric_key_is_a_key_at_a_lawful_argument() {
    assert_loads_clean(&key_program("list", "Map[K = List[T = Int64], V = Int64]"));
}

/// A symbol's equality is its identity, which is lawful.
#[test]
fn a_symbol_is_a_key() {
    assert_loads_clean(&key_program("sym", "Map[K = Symbol, V = Int64]"));
    assert_loads_clean(&key_program("symopt", "Set[T = Option[T = Symbol]]"));
}

/// A term's `=` is IEEE for a `Float` it holds, so a term holding `nan` is not equal to
/// itself: no lawful key.
#[test]
fn a_term_is_no_key() {
    let errs = errors_for(&key_program("term", "Map[K = Term, V = Int64]"));
    assert_non_eq_key_error(&errs, "Map", "K", "Term");
}

/// A type two witnesses give `Eq` provides it: the tie is the question of a call that
/// dispatches `Eq` there, which reports it naming both providers.
#[test]
fn a_key_whose_eq_two_providers_give_is_a_key() {
    let src = "namespace test.wi835.postie\n  import anthill.prelude.{Map, Int64, Eq, PartialEq, Function}\n  sort Opq\n    entity op(f: Function[A = Int64, B = Int64])\n  end\n  sort W1\n    provides PartialEq[T = Opq]\n    provides Eq[T = Opq]\n  end\n  sort W2\n    provides PartialEq[T = Opq]\n    provides Eq[T = Opq]\n  end\n  operation m(s: Map[K = Opq, V = Int64]) -> Int64 = 1\n  operation needEq[X](x: X) -> Int64 requires Eq[T = X] = 1\n  operation c(o: Opq) -> Int64 = needEq(o)\nend\n";
    let errs = errors_for(src);
    assert!(
        !errs.iter().any(|e| e.contains("does not provide `Eq`")),
        "the key provides `Eq`, twice: {errs:?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("ambiguous among providers")
            && e.contains("test.wi835.postie.W1")
            && e.contains("test.wi835.postie.W2")),
        "the call that requires `Eq` reports the tie: {errs:?}"
    );
}
