//! Ring + VectorSpace algebra specs (WI-138). Verifies that the
//! new typeclass abstractions in `stdlib/anthill/prelude/algebra.anthill`
//! load cleanly + the satisfaction facts (Float provides Ring,
//! Vec3 provides VectorSpace) resolve in the registry.
//!
//! Loads through `common::load_kb_with`, which RAISES load errors. This file
//! previously hand-rolled that sequence ending in `let _ = load::load_all(…)` —
//! errors discarded — which is load-bearing for what it now asserts:
//! `fact VectorSpace[Vec3, Float]` is legitimate only while
//! `check_provider_operations` accepts it, and that check reports as a LOAD
//! ERROR. Swallowing it would let the satisfaction assertion pass over a KB
//! that never finished loading.

#[test]
fn ring_spec_loads_and_resolves() {
    let kb = crate::common::load_kb_with(
        r#"
        namespace test.algebra.ring_smoke
          rule Marker(?x) :- ?x = 1
        end
    "#,
    );
    assert!(
        kb.try_resolve_symbol("anthill.prelude.algebra.Ring")
            .is_some(),
        "Ring spec must be loaded from stdlib"
    );
    // Operation symbols are scoped under Ring (Ring.add, Ring.mul, …).
    for op in [
        "anthill.prelude.algebra.Ring.add",
        "anthill.prelude.algebra.Ring.sub",
        "anthill.prelude.algebra.Ring.mul",
        "anthill.prelude.algebra.Ring.zero",
        "anthill.prelude.algebra.Ring.one",
    ] {
        assert!(
            kb.try_resolve_symbol(op).is_some(),
            "missing Ring operation: {op}"
        );
    }
}

#[test]
fn vector_space_spec_loads_and_resolves() {
    let kb = crate::common::load_kb_with(
        r#"
        namespace test.algebra.vs_smoke
          rule Marker(?x) :- ?x = 1
        end
    "#,
    );
    assert!(
        kb.try_resolve_symbol("anthill.prelude.algebra.VectorSpace")
            .is_some(),
        "VectorSpace spec must be loaded from stdlib"
    );
    for op in [
        "anthill.prelude.algebra.VectorSpace.vec_add",
        "anthill.prelude.algebra.VectorSpace.vec_sub",
        "anthill.prelude.algebra.VectorSpace.vec_scale",
        "anthill.prelude.algebra.VectorSpace.vec_zero",
    ] {
        assert!(
            kb.try_resolve_symbol(op).is_some(),
            "missing VectorSpace operation: {op}"
        );
    }
}

#[test]
fn float_provides_ring_and_vec3_provides_vector_space() {
    // Verify the satisfaction declarations land as facts under each spec's functor
    // in the `rules_by_functor` index: `fact Ring[T = Float]` (float.anthill) and
    // `fact VectorSpace[Vec3, Float]` (the binding-layer geometry.anthill). Both
    // live in the binding layer because `Ring[Float]` is a per-language fact and
    // `VectorSpace requires Ring[F]` (proposal 038).
    //
    // WI-931 WITHDREW the VectorSpace half and this test asserted its ABSENCE:
    // the provision was never BACKED, because `VectorSpace`'s members are
    // functional (`vec_add(a, b) -> V`) while `anthill.geometry` implemented the
    // vector operations RELATIONALLY, and a rule is not backing (WI-818).
    // WI-935 backed them for real — `Vec3` now declares the four as bodied
    // operations — so the assertion flips back.
    //
    // This test does NOT prove the members run; `check_provider_operations` is
    // what makes the fact load-blocking, and `vec3_ops_test::the_four_members_evaluate`
    // is what drives them. Backing the bodies out fails BOTH — this one at load.
    let kb = crate::common::load_kb_with(
        r#"
        namespace test.algebra.satisfaction
          rule Marker(?x) :- ?x = 1
        end
    "#,
    );
    // CARRIER-AWARE, via the shared `common::sort_provisions` walk. `!rules_by_
    // functor(spec).is_empty()` would NOT do: it keys on the spec functor alone, so
    // ANY carrier's fact satisfies it — move the provision to some other carrier and
    // a test named `…vec3_provides_vector_space` keeps passing. WI-931's original
    // `is_empty()` form was sound for its claim ("NOTHING provides VectorSpace");
    // the predicate stopped matching the claim when WI-935 flipped the polarity.
    let short = |s: String| s.rsplit('.').next().unwrap_or("").to_string();
    let provisions: Vec<(String, String)> = crate::common::sort_provisions(&kb)
        .into_iter()
        .map(|(c, s)| (short(c), short(s)))
        .collect();
    assert!(
        provisions.contains(&("Float".to_string(), "Ring".to_string())),
        "Float must provide Ring; provisions: {provisions:?}",
    );
    assert!(
        provisions.contains(&("Vec3".to_string(), "VectorSpace".to_string())),
        "Vec3 must provide VectorSpace (WI-935); provisions: {provisions:?}",
    );
}
