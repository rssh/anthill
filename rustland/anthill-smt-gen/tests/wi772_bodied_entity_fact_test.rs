//! WI-772(b): a BODIED rule whose head is a referenced entity must be
//! refused loudly at emission, never harvested or silently skipped.
//! The old reader walked `rules_by_functor` with no `is_fact` guard and
//! accepted the first head carrying concrete numeric literals, so
//! `rule LinkParameters(mass: 2.0) :- heavy_variant()` could feed
//! mass=2.0 into the SMT encoding whether or not the guard holds — a
//! formal proof discharged from a premise the source guarded.

use super::common::load_kb_with;

use anthill_smt_gen::{emit_obligation, Obligation};

#[test]
fn bodied_referenced_entity_rule_is_refused_even_with_ground_fact() {
    // A ground fact AND a guarded rule both exist for the entity. The
    // read must refuse — candidates enumerate in insertion (source)
    // order, so without the pre-scan the fact written first would
    // deterministically win the harvest and the guarded mass=2.0 head
    // would be silently ignored (or shadow the fact if reordered).
    let kb = load_kb_with(r#"
        namespace test.smt_gen.wi772
          import anthill.prelude.{Float}
          import anthill.prelude.Numeric.{mul}

          sort Variant
            entity heavy_variant
          end

          entity LinkParameters(mass: Float)

          rule payload_bound(?m)
            :- LinkParameters(mass: ?mass),
               ?m = mul(?mass, 2.0)

          fact LinkParameters(mass: 1.0)

          rule LinkParameters(mass: 2.0) :- heavy_variant()
        end
    "#);
    let err = emit_obligation(&kb, &Obligation {
        rule_qn: "test.smt_gen.wi772.payload_bound".to_string(),
        upper_bound: 10.0,
    })
    .expect_err("a bodied LinkParameters rule must refuse emission");
    assert!(
        err.message.contains("bodied rule for referenced entity"),
        "refusal must state the unsupported shape, got: {}",
        err.message
    );
    assert!(
        err.message.contains("heavy_variant"),
        "refusal must name the offending rule (head :- body), got: {}",
        err.message
    );
}
