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
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
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

/// The POSITIONAL binding spelling. `Map[Float, Int64]` binds `K` by position, so
/// the σ build must map it onto the declared parameter — and the diagnostic must
/// still name `K`, which the author never wrote.
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
        .filter(|e| e.contains("NonEq") && e.contains("Map"))
        .count();
    assert_eq!(
        refusals, 2,
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
  operation s1() -> Set[T = Int64] = Set.empty()
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
