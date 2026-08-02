//! Ring + VectorSpace algebra specs (WI-138). Verifies that the
//! new typeclass abstractions in `stdlib/anthill/algebra.anthill`
//! load cleanly + the satisfaction facts (Float provides Ring,
//! Vec3 provides VectorSpace) resolve in the registry.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_with(extra: &str) -> KnowledgeBase {
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
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

#[test]
fn ring_spec_loads_and_resolves() {
    let kb = load_with(r#"
        namespace test.algebra.ring_smoke
          rule Marker(?x) :- ?x = 1
        end
    "#);
    assert!(
        kb.try_resolve_symbol("anthill.prelude.algebra.Ring").is_some(),
        "Ring spec must be loaded from stdlib"
    );
    // Operation symbols are scoped under Ring (Ring.add, Ring.mul, …).
    for op in ["anthill.prelude.algebra.Ring.add", "anthill.prelude.algebra.Ring.sub",
               "anthill.prelude.algebra.Ring.mul", "anthill.prelude.algebra.Ring.zero",
               "anthill.prelude.algebra.Ring.one"] {
        assert!(
            kb.try_resolve_symbol(op).is_some(),
            "missing Ring operation: {op}"
        );
    }
}

#[test]
fn vector_space_spec_loads_and_resolves() {
    let kb = load_with(r#"
        namespace test.algebra.vs_smoke
          rule Marker(?x) :- ?x = 1
        end
    "#);
    assert!(
        kb.try_resolve_symbol("anthill.prelude.algebra.VectorSpace").is_some(),
        "VectorSpace spec must be loaded from stdlib"
    );
    for op in ["anthill.prelude.algebra.VectorSpace.vec_add",
               "anthill.prelude.algebra.VectorSpace.vec_sub",
               "anthill.prelude.algebra.VectorSpace.vec_scale",
               "anthill.prelude.algebra.VectorSpace.vec_zero"] {
        assert!(
            kb.try_resolve_symbol(op).is_some(),
            "missing VectorSpace operation: {op}"
        );
    }
}

#[test]
fn float_provides_ring_but_nothing_provides_vector_space_yet() {
    // Verify the satisfaction declaration `fact Ring[T = Float]` (float.anthill)
    // lands as a fact under the spec's functor in the rules_by_functor index.
    //
    // WI-931 — `Vec3` NO LONGER provides `VectorSpace`, and this test asserted
    // that it did. The provision was never BACKED: `VectorSpace`'s members are
    // functional (`vec_add(a, b) -> V`) while `anthill.geometry` implements the
    // vector operations RELATIONALLY (`vec_add(?a, ?b, ?c)`), and a rule is not
    // backing (WI-818). It read as satisfied only because `Vec3` is a §6.3
    // free-standing entity, which emitted no `SortInfo` and so was skipped by
    // `check_provider_operations` as if it were abstract (WI-928).
    //
    // The negative half is asserted rather than deleted, because "nothing
    // provides VectorSpace" is a state WI-935 is meant to END: when it lands,
    // this flips back and the assertion says which way.
    let kb = load_with(r#"
        namespace test.algebra.satisfaction
          rule Marker(?x) :- ?x = 1
        end
    "#);
    let ring_sym = kb.try_resolve_symbol("anthill.prelude.algebra.Ring")
        .expect("Ring spec must resolve");
    let ring_facts = kb.rules_by_functor(ring_sym);
    assert!(!ring_facts.is_empty(),
        "expected at least one Ring satisfaction fact (Float should provide Ring)");
    let vs_sym = kb.try_resolve_symbol("anthill.prelude.algebra.VectorSpace")
        .expect("VectorSpace spec must resolve");
    assert!(kb.rules_by_functor(vs_sym).is_empty(),
        "no carrier backs VectorSpace's functional members today (WI-935); a \
         satisfaction fact here would certify operations that die at the call");
}
