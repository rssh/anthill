//! `anthill.geometry.Vec3`'s VectorSpace members (WI-137 → WI-138 → WI-935).
//!
//! WI-137 wrote these as namespace-level RELATIONAL rules (`vec_add(?a, ?b, ?c)`)
//! because in April a hand-written twin was the only way to put Vec3 arithmetic
//! in front of Z3. WI-138 lifted the shape to `anthill.prelude.algebra.VectorSpace`
//! — whose members are FUNCTIONAL — but left the relational spelling standing, so
//! the two coexisted with nothing implementing the spec (a rule is not backing,
//! WI-818). WI-935 finished that lift: ONE definition, the bodied operation, and
//! the relational reading DERIVED from it rather than written twice.
//!
//! Landing it required three resolver fixes, because deleting the hand-written
//! clauses exposed that the derived reading did not actually work outside a prove
//! run: WI-937 (an eponymous entity failed to materialize, so a body reading
//! `a.x` aborted the SLD→eval bridge), WI-938 (a rule-less bodied op's arity+1
//! goal had no relational view at resolve time — it now routes to
//! `unify(op(args), ?r)`, which BINDS, where the spec's former `eq` wording could
//! only test), and WI-941 (a nullary op never folded, answering an unbound
//! residual that read as success).
//!
//! What each test here measures, and what it costs to back the change out:
//!  - `the_four_members_evaluate` is the capability test. It fails if the bodies
//!    are removed or wrong. Its predecessor (`vec_ops_callable_from_user_rule`)
//!    asserted only that a rule mentioning `vec_add` LOADED, which is why the
//!    unbacked provision survived from WI-138 to WI-931 unnoticed.
//!  - `the_relational_view_is_derived_from_the_body` is what replaces the deleted
//!    `vec_add/3` clauses: the same `op(args…, ?result)` shape, under the op's own
//!    functor, generated from the body. This is the form lf1 already consumes
//!    (`FollowerController.desired_position(?leader, ?off, ?target)`).
//!  - `control_the_namespace_level_relational_rules_are_gone` passes only AFTER
//!    the lift; it is the one that pins that there is no second `vec_add`.
//!
//! CONTROL DISCIPLINE for the three resolver fixes, each MEASURED during
//! development by observing the failure the fix removes:
//!  - WI-937 (`term_to_value` → `sort_of_constructor`): before it, every rule-body
//!    route aborted `bridge_op_to_eval: field_access: receiver is not an entity`.
//!    `the_four_members_evaluate` passes either way — it calls the interpreter
//!    directly — which is why that test is kept separate.
//!  - WI-938 (the arity+1 → `unify` routing): before it, the two relational tests
//!    answered 0 solutions and LOADED CLEAN.
//!  - WI-941 (the nullary fold): with WI-937+938 in place but this one backed out,
//!    `every_member_answers_relationally` fails on `zero_r` ALONE — the other two
//!    members pass, which is what isolates the nullary path from the rest.
//!
//! CONTROL DISCIPLINE for the lift itself — two perturbations of
//! `stdlib/anthill/geometry.anthill`, each failing exactly ONE test here:
//!  - restoring the pre-WI-935 NAMESPACE-level `rule vec_add(?a, ?b, ?c)` fails
//!    `control_the_namespace_level_relational_rules_are_gone` and nothing else.
//!    It does NOT disturb the derived view, because `Vec3.vec_add` and
//!    `anthill.geometry.vec_add` are different symbols — which is precisely the
//!    collision WI-935 removed rather than adjudicated.
//!  - adding the same clause INSIDE `sort Vec3` — i.e. under the op's own functor
//!    — fails `the_relational_view_is_derived_from_the_body` and nothing else.
//!    That is the suppression claim, driven: a hand-written clause makes the op
//!    non-rule-less, and the WI-669 seam only synthesizes for a rule-less op.
//! `the_four_members_evaluate` passes under BOTH by design: the bodies are
//! untouched either way, so it measures the members and not the naming.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;

const MARKER: &str = r#"
    namespace test.vec3.probe
      rule Marker(?x) :- ?x = 1
    end
"#;

fn op_sym(kb: &KnowledgeBase, short: &str) -> Symbol {
    let qn = format!("anthill.geometry.Vec3.{short}");
    kb.try_resolve_symbol(&qn).unwrap_or_else(|| panic!("missing Vec3 member: {qn}"))
}

/// A `Vec3(x:, y:, z:)` entity value. Field symbols are interned rather than
/// resolved: `Value::Entity.named` keys on the field label, and the constructor's
/// canonical order is the DECLARED one (x, y, z), which is the order written here.
fn vec3(kb: &mut KnowledgeBase, x: f64, y: f64, z: f64) -> Value {
    let functor = kb.try_resolve_symbol("anthill.geometry.Vec3").expect("Vec3 sort");
    let named = vec![
        (kb.intern("x"), Value::Float(x)),
        (kb.intern("y"), Value::Float(y)),
        (kb.intern("z"), Value::Float(z)),
    ];
    Value::Entity { functor, pos: vec![].into(), named: named.into() }
}

/// The (x, y, z) of a `Value::Entity` Vec3, by field label.
fn components(kb: &KnowledgeBase, v: &Value) -> (f64, f64, f64) {
    let Value::Entity { named, .. } = v else {
        panic!("expected a Vec3 entity, got {v:?}");
    };
    let read = |label: &str| -> f64 {
        named.iter()
            .find(|(sym, _)| kb.resolve_sym(*sym) == label)
            .map(|(_, val)| match val {
                Value::Float(f) => *f,
                other => panic!("field `{label}` is not a Float: {other:?}"),
            })
            .unwrap_or_else(|| panic!("no field `{label}` on {v:?}"))
    };
    (read("x"), read("y"), read("z"))
}

#[test]
fn vec_ops_symbols_resolve() {
    // The four members are SORT-SCOPED now (`Vec3.vec_add`), not namespace-level.
    // A name check only — `the_four_members_evaluate` is what says they work.
    let kb = crate::common::load_kb_with(MARKER);
    for short in ["vec_add", "vec_sub", "vec_scale", "vec_zero"] {
        let _ = op_sym(&kb, short);
    }
}

/// THE CAPABILITY TEST: each member runs and returns the right vector.
///
/// FOUR stdlib loads for ONE claim, which is worth the ~2s: a FRESH interpreter
/// per call is required, because a reused one carries frame state forward and
/// turns four independent results into four dependent ones — the failure mode is
/// a later call passing on the earlier call's leftovers.
///
/// The calls go through the INTERPRETER. The rule-body routes are covered by
/// `the_imported_short_name_answers_through_the_derived_view` and
/// `every_member_answers_relationally`; this one keeps a direct `Interpreter::call`
/// so a regression in the resolver's bridge cannot make all three fail at once
/// and hide which layer broke.
#[test]
fn the_four_members_evaluate() {
    // vec_add((1,2,3), (10,20,30)) = (11,22,33)
    let mut interp = crate::common::interp_for(MARKER);
    let a = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    let b = vec3(interp.kb_mut(), 10.0, 20.0, 30.0);
    let out = interp.call("anthill.geometry.Vec3.vec_add", &[a, b]).expect("vec_add runs");
    assert_eq!(components(interp.kb(), &out), (11.0, 22.0, 33.0));

    // vec_sub((1,2,3), (10,20,30)) = (-9,-18,-27)
    let mut interp = crate::common::interp_for(MARKER);
    let a = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    let b = vec3(interp.kb_mut(), 10.0, 20.0, 30.0);
    let out = interp.call("anthill.geometry.Vec3.vec_sub", &[a, b]).expect("vec_sub runs");
    assert_eq!(components(interp.kb(), &out), (-9.0, -18.0, -27.0));

    // vec_scale(2.0, (1,2,3)) = (2,4,6) — scalar FIRST, matching the spec's
    // `vec_scale(c: F, v: V)`; a swapped signature would still typecheck here
    // (both params are read) but would dispatch wrong against the spec.
    let mut interp = crate::common::interp_for(MARKER);
    let v = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    let out = interp
        .call("anthill.geometry.Vec3.vec_scale", &[Value::Float(2.0), v])
        .expect("vec_scale runs");
    assert_eq!(components(interp.kb(), &out), (2.0, 4.0, 6.0));

    // vec_zero() = (0,0,0)
    let mut interp = crate::common::interp_for(MARKER);
    let out = interp.call("anthill.geometry.Vec3.vec_zero", &[]).expect("vec_zero runs");
    assert_eq!(components(interp.kb(), &out), (0.0, 0.0, 0.0));
}

/// The relational reading of a functional member is DERIVED, not written.
///
/// This is the capability the deleted `rule vec_add(?a, ?b, ?c)` clauses were a
/// hand-rolled instance of: WI-669 builds `op(?0…?n-1, ?result) :- ?result = <body>`
/// under the op's OWN functor, which is what the SMT emitter inlines at a
/// `vec_add(?a, ?b, ?c)` goal. A hand-written clause of the same functor would
/// SUPPRESS this — `synthesize_body_derived_defrules` only synthesizes for a
/// rule-less op, and `synthesize_op_defining_rule` returns any existing rule as-is.
#[test]
fn the_relational_view_is_derived_from_the_body() {
    let mut kb = crate::common::load_kb_with(MARKER);
    for (short, params) in [("vec_add", 2), ("vec_sub", 2), ("vec_scale", 2), ("vec_zero", 0)] {
        let op = op_sym(&kb, short);
        assert!(
            kb.rules_by_functor(op).is_empty(),
            "{short} must be RULE-LESS before synthesis — a hand-written clause would \
             suppress the derived view",
        );
        let rid = kb
            .synthesize_op_defining_rule(op)
            .unwrap_or_else(|| panic!("{short}'s body must yield a defining rule"));
        assert_eq!(
            kb.rule_arity(rid),
            params + 1,
            "{short}'s derived rule is `{short}(<{params} params>, ?result)`",
        );
        assert!(
            kb.rules_by_functor(op).contains(&rid),
            "{short}'s derived rule is keyed under the op's own functor",
        );
    }
}

/// CONTROL — there is exactly one `vec_add` in the namespace: the sort-scoped
/// member. The namespace-level relational twin is gone.
///
/// READ THE NEXT TEST BEFORE CONCLUDING ANYTHING FROM THIS ONE. An earlier
/// version of this docstring said the collision is gone "so the bare name has one
/// target" — true, and it does NOT mean what it sounds like. This checks the
/// FULLY QUALIFIED name, while the hazard WI-931 measured lives on the IMPORT
/// path, and the bare name resolving to one target says nothing about whether
/// that target answers. `the_imported_short_name_no_longer_answers` measures the
/// thing this test cannot see.
#[test]
fn control_the_namespace_level_relational_rules_are_gone() {
    let kb = crate::common::load_kb_with(MARKER);
    for short in ["vec_add", "vec_sub", "vec_scale", "vec_zero"] {
        let qn = format!("anthill.geometry.{short}");
        assert!(
            kb.try_resolve_symbol(&qn).is_none(),
            "`{qn}` must be gone — the sort-scoped `Vec3.{short}` is the only definition, \
             and a namespace-level twin is what made the short name ambiguous",
        );
    }
}

/// THE POINT OF THE WHOLE LIFT, DRIVEN: the pre-WI-935 user spelling still
/// answers, through the DERIVED relational view instead of a hand-written clause
/// — and it now answers with a VALUE, which it never did before.
///
/// `import anthill.geometry.{vec_add}` + `vec_add(a, b, ?c)` was the exact goal
/// WI-931 measured going 1 → 0 when the operations were added beside the rules.
/// Deleting the rules reproduced that 0 by another route, until WI-938 gave a
/// rule-less bodied op its arity+1 relational view.
///
/// STRICTLY BETTER THAN WHAT WAS THERE. The old namespace-level clauses answered
/// 1 INDEFINITE solution with `?c` unbound and the whole body residual (measured
/// before the change — the residual was what Z3 consumed). This answers 1
/// DEFINITE solution carrying `Vec3(11.0, 22.0, 33.0)`. Asserting the VALUE is
/// the assertion: `len() == 1` passed for the residual too, which is how the old
/// suite stayed green over a surface that computed nothing.
#[test]
fn the_imported_short_name_answers_through_the_derived_view() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.vec3.legacy
  import anthill.geometry.{Vec3, vec_add}

  rule try_add(?c) :- vec_add(Vec3(x: 1.0, y: 2.0, z: 3.0),
                              Vec3(x: 10.0, y: 20.0, z: 30.0), ?c)
end
"#,
    );
    let sols = crate::common::query_unary(&mut kb, "test.vec3.legacy.try_add");
    assert_eq!(sols.len(), 1, "the imported short name must reach the derived view");
    let (value, definite) = &sols[0];
    assert!(definite, "the answer must be DEFINITE, not a residual: {value:?}");
    assert_eq!(components(&kb, value), (11.0, 22.0, 33.0));
}

/// The other three members answer relationally too — including the NULLARY one,
/// which takes a different path (no arguments to reduce).
#[test]
fn every_member_answers_relationally() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.vec3.rel
  import anthill.geometry.{Vec3}

  rule sub_r(?c)   :- Vec3.vec_sub(Vec3(x: 1.0, y: 2.0, z: 3.0),
                                   Vec3(x: 10.0, y: 20.0, z: 30.0), ?c)
  rule scale_r(?c) :- Vec3.vec_scale(2.0, Vec3(x: 1.0, y: 2.0, z: 3.0), ?c)
  rule zero_r(?c)  :- Vec3.vec_zero(?c)
end
"#,
    );
    for (rule, expect) in [
        ("test.vec3.rel.sub_r", (-9.0, -18.0, -27.0)),
        ("test.vec3.rel.scale_r", (2.0, 4.0, 6.0)),
        ("test.vec3.rel.zero_r", (0.0, 0.0, 0.0)),
    ] {
        let sols = crate::common::query_unary(&mut kb, rule);
        assert_eq!(sols.len(), 1, "{rule} must answer");
        let (value, definite) = &sols[0];
        assert!(definite, "{rule} must be DEFINITE, got residual: {value:?}");
        assert_eq!(components(&kb, value), expect, "{rule}");
    }
}

/// The algebraic laws live on the SPEC now, written over the abstract `V`, not
/// restated per-component at the carrier. `vec_sub_def` is the one WI-137 law with
/// no WI-138 counterpart; WI-935 added it to the spec rather than dropping it.
///
/// THIS IS A NAME CHECK, not a capability test, and it is one deliberately: an
/// algebraic law is consumed by `using <law>` from a proof block, and NO proof in
/// the tree cites any of these eight (grepped repo-wide — lf1 uses `Vec3` the
/// entity and never the vector operations). There is nothing to drive. What it
/// does buy is the second half: that the per-component copies in
/// `anthill.geometry` are gone, so a reader cannot cite a law that silently
/// pins the concrete shape.
#[test]
fn algebraic_law_rules_present() {
    let kb = crate::common::load_kb_with(MARKER);
    for law in [
        "vec_add_comm",
        "vec_add_assoc",
        "vec_add_identity",
        "vec_sub_def",
        "vec_scale_distrib_v",
        "vec_scale_distrib_s",
        "vec_scale_assoc",
        "vec_scale_identity",
    ] {
        let qn = format!("anthill.prelude.algebra.VectorSpace.{law}");
        assert!(kb.try_resolve_symbol(&qn).is_some(), "missing VectorSpace law: {qn}");
        // …and the per-component copy in `anthill.geometry` is gone.
        let old = format!("anthill.geometry.{law}");
        assert!(
            kb.try_resolve_symbol(&old).is_none(),
            "`{old}` must be gone — the law belongs to the spec, over the abstract V",
        );
    }
}

/// CONTROL — why the four members are the CARRIER'S OWN rather than free
/// namespace operations, which is the alternative spelling for the same bodies.
///
/// Writing `sort Vec3 { entity Vec3(…); operation … }` adds no layer: `entity
/// Vec3(…)` already IS that sort (§6.3 / WI-926 — an equivalence, not a rename).
/// The long form is simply the only spelling with a place to put members, and
/// membership is what a provision needs, because a provision is PER-CARRIER.
///
/// Measured here: the same four operations, same names, same signatures, declared
/// at NAMESPACE level beside the carrier, back nothing —
/// `check_provider_operations` reports one `UnbackedProviderOperation` per member
/// ("no own `vec_add` on …"). That refusal is correct rather than incidental: with
/// two carriers of `VectorSpace` there are two `vec_add`s, and carrier ownership
/// is the only thing that tells them apart. A free namespace operation has no
/// carrier dimension — which is the same missing dimension that made the
/// pre-WI-935 `anthill.geometry.vec_add` collide with `Vec3.vec_add` under one
/// short name.
#[test]
fn control_a_namespace_level_operation_does_not_back_a_provision() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace test.vec3.freeop
  import anthill.prelude.{Float}
  import anthill.prelude.algebra.{VectorSpace}

  entity FreeVec(x: Float)

  operation vec_add(a: FreeVec, b: FreeVec) -> FreeVec = FreeVec(x: a.x + b.x)
  operation vec_sub(a: FreeVec, b: FreeVec) -> FreeVec = FreeVec(x: a.x - b.x)
  operation vec_scale(c: Float, v: FreeVec) -> FreeVec = FreeVec(x: c * v.x)
  operation vec_zero() -> FreeVec = FreeVec(x: 0.0)

  fact VectorSpace[FreeVec, Float]
end
"#,
    )
    .err()
    .expect("a namespace-level operation must not back a per-carrier provision");

    assert_eq!(errs.len(), 4, "one report per unbacked member, got:\n{}", errs.join("\n"));
    for member in ["vec_add", "vec_sub", "vec_scale", "vec_zero"] {
        assert!(
            errs.iter().any(|e| {
                e.contains(&format!("no own '{member}' on 'test.vec3.freeop.FreeVec'"))
            }),
            "expected an unbacked-member report naming `{member}`, got:\n{}",
            errs.join("\n"),
        );
    }
}

/// THE FIRST GENERIC CONSUMER OF THE LIFT CERTIFIES AT LOAD AND DIES AT THE CALL.
///
/// WI-138 lifted `Vec3`'s operations to an abstract `VectorSpace[V, F]` so code
/// could be written against the SPEC rather than the carrier. WI-935 made the
/// provision real. This test measures what a consumer actually gets, and the
/// answer is: the abstract route does not work.
///
/// `operation twice[V, F](a: V) -> V requires VectorSpace[V, F] =
///  VectorSpace.vec_add(a, a)` LOADS CLEAN and then fails at the call with
/// `OperationBodyMissing { anthill.prelude.algebra.VectorSpace.vec_add }` — the
/// dictionary route does not reach `Vec3`'s member. That is exactly the class
/// §8.7's WI-818 paragraph says the loader prevents ("rather than certify a
/// program whose call fails only at run time"); the check guards the PROVIDER,
/// and nothing guards the generic CONSUMER.
///
/// CONTROL A — the same call at a CONCRETE carrier works and returns the right
/// vector, so the provision and the member are both fine; it is the abstract
/// dispatch that fails.
///
/// CONTROL B — the same shape over the one-param `Ring` is REFUSED AT LOAD with
/// a located diagnostic. So the two specs disagree about the identical
/// construct: one is caught, the other is certified and dies. That disagreement,
/// not the failure alone, is what makes this a defect rather than a limitation.
///
/// This test asserts CURRENT behaviour so it cannot be lost, and is expected to
/// FLIP when the gap is closed — at which point `twice` must return
/// `Vec3(2.0, 4.0, 6.0)` and this should assert that instead of being deleted.
/// Tracked as WI-942. Pre-existing (a generic-dispatch gap, not created here);
/// WI-935 is what makes it reachable against a stdlib type.
#[test]
fn a_generic_consumer_of_vector_space_loads_clean_and_fails_at_the_call() {
    let src = r#"
namespace test.vec3.generic
  import anthill.geometry.{Vec3}
  import anthill.prelude.algebra.{VectorSpace}

  sort G
    operation twice[V, F](a: V) -> V requires VectorSpace[V, F] =
      VectorSpace.vec_add(a, a)

    operation twice_vec3(a: Vec3) -> Vec3 = VectorSpace.vec_add(a, a)
  end
end
"#;
    // SUBJECT — loads clean, then dies at the call.
    crate::common::try_load_kb_with(src)
        .map(|_| ())
        .expect("the generic consumer LOADS CLEAN — that is half the defect");

    let mut interp = crate::common::interp_for(src);
    let a = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    let err = interp
        .call("test.vec3.generic.G.twice", &[a])
        .expect_err("the generic route must fail at the call (WI-942)");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("OperationBodyMissing")
            && rendered.contains("anthill.prelude.algebra.VectorSpace.vec_add"),
        "expected OperationBodyMissing naming the SPEC op, got: {rendered}",
    );

    // CONTROL A — the concrete carrier route works, so the member is backed and
    // the provision is sound; only the abstract dispatch fails.
    let mut interp = crate::common::interp_for(src);
    let a = vec3(interp.kb_mut(), 1.0, 2.0, 3.0);
    let out = interp
        .call("test.vec3.generic.G.twice_vec3", &[a])
        .expect("the concrete route must work");
    assert_eq!(components(interp.kb(), &out), (2.0, 4.0, 6.0));

    // CONTROL B — the SAME construct over the one-param `Ring` is REFUSED at
    // load. The two specs disagree; that is the defect's shape.
    let ring_src = r#"
namespace test.ring.generic
  import anthill.prelude.{Float}
  import anthill.prelude.algebra.{Ring}
  sort H
    operation dbl[T](a: T) -> T requires Ring[T] = Ring.add(a, a)
  end
end
"#;
    let errs = crate::common::try_load_kb_with(ring_src)
        .err()
        .expect("the Ring-shaped generic is REFUSED at load, unlike the VectorSpace one");
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.algebra.Ring.add.requires")),
        "expected a located requires-coverage diagnostic, got:\n{}",
        errs.join("\n"),
    );
}
