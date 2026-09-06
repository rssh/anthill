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

use anthill_core::kb::term_view::TermView;

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
    // WI-20260825-1WBZT — `Ring` DECLARES NONE OF THEM ANY MORE, and this row is where
    // that is pinned. It used to assert five `anthill.prelude.algebra.Ring.*` addresses;
    // those were a SECOND declaration of `add` / `sub` / `mul` under a spelling
    // `anthill.prelude.Numeric` also carried, plus a `zero` that was the same value as
    // `Numeric.zero-val` under a different name. The categories own them now
    // (`stdlib/anthill/prelude/arithmetic.anthill`) and `Ring` reaches them by
    // `provides`, so the qualified addresses are the categories'.
    for op in [
        "anthill.prelude.Additive.add",
        "anthill.prelude.Additive.sub",
        "anthill.prelude.Additive.neg",
        "anthill.prelude.Additive.zero",
        "anthill.prelude.Multiplicative.mul",
        "anthill.prelude.Multiplicative.one",
    ] {
        assert!(
            kb.try_resolve_symbol(op).is_some(),
            "missing arithmetic-category operation: {op}"
        );
    }
    // …and the OLD addresses are gone rather than merely unused. Without this half the
    // row above passes on a KB where `Ring` still declares its own five and the
    // duplication the ticket removed is back — which is exactly the state a careless
    // merge would restore.
    for gone in [
        "anthill.prelude.algebra.Ring.add",
        "anthill.prelude.algebra.Ring.sub",
        "anthill.prelude.algebra.Ring.mul",
        "anthill.prelude.algebra.Ring.zero",
        "anthill.prelude.algebra.Ring.one",
        "anthill.prelude.Numeric.add",
        "anthill.prelude.Numeric.zero-val",
    ] {
        assert!(
            kb.try_resolve_symbol(gone).is_none(),
            "{gone} must NOT be declared: one spec declares each short name, and the \
             bundles reach it by `provides` (WI-20260825-1WBZT)"
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

// ── A FIELD NEEDS NO ORDER, AND A FIELD IS A RING ────────────────────────────
//
// `stdlib/anthill/prelude/field.anthill` required `Numeric[T]` until 2026-09-06, and
// `Numeric` is `Additive` + `Multiplicative` + `requires PartialOrd[T]` — so every field
// owed an ORDER, which a field does not have in general (the complex numbers admit no
// compatible order; neither does a finite field). It now requires `algebra.Ring[T]`, the
// standard base — a commutative ring with 1, deliberately Ord-free — plus `PartialEq[T]`
// for the `eq`/`neq` its own guards spell.
//
// WHAT FAILS WHEN THAT IS BACKED OUT. Restore `requires Numeric[T]` and BOTH tests below
// stop loading, each on its own error: `a_field_needs_no_order` on
//
//   'test.f5.F5' provides 'anthill.prelude.Field', which requires
//   'anthill.prelude.Numeric', but 'test.f5.F5' does not provide 'anthill.prelude.Numeric'
//
// and `a_field_extension_is_a_vector_space_over_the_base_field` on the same, for `F5` and
// `L` both. Note what the back-out does NOT produce: a `VectorSpace requires Ring[F]`
// refusal. Both carriers write `provides Ring[...]` by hand, so the vector-space half
// still resolves — which is the honest shape of the defect. `requires Ring` makes that
// hand-written row redundant rather than making the extension newly possible; what was
// impossible before is an extension over a base with NO ORDER, which is these two.
//
// WHAT PASSES EITHER WAY, by design: every other row in this file. `Float` provides
// `Numeric`, `Ring` and `Field` all three, so no shipped carrier can tell the two
// requirements apart — which is exactly why the defect survived, and why these carriers
// provide the field structure and NO order at all.

/// `F_5`, the integers mod 5. A field by every law `Field` states, and not an ordered one:
/// it provides `PartialEq`, `Ring` and `Field`, and neither `PartialOrd` nor `WeakOrd`.
const F5: &str = r#"
    sort test.f5.F5
      import anthill.prelude.{Int64, Bool, PartialEq, Field}
      import anthill.prelude.algebra.{Ring}

      entity f5(v: Int64)

      operation add(a: F5, b: F5) -> F5 = f5(v: Int64.mod(Int64.add(a.v, b.v), 5))
      operation neg(a: F5) -> F5        = f5(v: Int64.mod(Int64.sub(5, a.v), 5))
      operation zero() -> F5            = f5(v: 0)
      operation mul(a: F5, b: F5) -> F5 = f5(v: Int64.mod(Int64.mul(a.v, b.v), 5))
      operation one() -> F5             = f5(v: 1)
      operation eq(a: F5, b: F5) -> Bool = a.v = b.v
      -- Fermat: a^(p-2) = a^3 inverts in F_5.
      --
      -- IT ANSWERS 0 AT 0 AND THAT IS A GAP, stated rather than left to be found.
      -- `Field.recip` declares `effects { Error[DivisionByZero] :- eq(a, 0) }`, so the
      -- operation is PARTIAL by its specification; this body is total and returns
      -- `0^3 = 0`, so `div(x, zero)` answers `zero` rather than raising. MEASURED only as
      -- far as this: the carrier loads clean and the wrong answer is reachable. WHY the
      -- load permits it — whether a carrier's body is held to a spec op's guarded effect
      -- at all — is NOT measured here and should not be read off this comment. The fixture
      -- drives none of it: every divisor it uses is non-zero, so nothing asserted below
      -- rests on the wrong answer. A carrier meant for use rather than for measurement
      -- would have to raise.
      operation recip(a: F5) -> F5 =
        f5(v: Int64.mod(Int64.mul(Int64.mul(a.v, a.v), a.v), 5))
      operation div(a: F5, b: F5) -> F5 = mul(a, recip(b))

      -- DRIVEN, not merely declared: 2 * 3 = 6 = 1 (mod 5), so recip(2) is 3.
      operation probe_recip() -> Int64 = recip(f5(v: 2)).v
      -- ...and the inverse law `mul(div(a, b), b) = a` on a concrete pair: div(4, 3) = 3,
      -- since 3 * 3 = 9 = 4 (mod 5).
      operation probe_div() -> Int64 = div(f5(v: 4), f5(v: 3)).v

      provides PartialEq[T = F5]
      provides Ring[F5]
      provides Field[T = F5]
    end
"#;

#[test]
fn a_field_needs_no_order() {
    // ONE stdlib load, reused for both halves. This file was consolidated to amortize
    // exactly that cost (see its header), so loading twice for one test would give the
    // saving straight back.
    let kb = crate::common::load_kb_with(F5);

    // THE CARRIER OWES NO COMPARISON SURFACE, and this is the half that says so rather
    // than leaving it to the source being short. Carrier-aware, on the same
    // `sort_provisions` walk `float_provides_ring_and_vec3_provides_vector_space` uses,
    // and for the same reason: keying on the spec functor alone would be satisfied by
    // `Float`'s rows, which the stdlib load puts in this very KB.
    let short = |s: String| s.rsplit('.').next().unwrap_or("").to_string();
    let provisions: Vec<(String, String)> = crate::common::sort_provisions(&kb)
        .into_iter()
        .map(|(c, s)| (short(c), short(s)))
        .collect();
    for spec in ["Field", "Ring", "PartialEq"] {
        assert!(
            provisions.contains(&("F5".to_string(), spec.to_string())),
            "F5 must provide {spec}; provisions: {provisions:?}"
        );
    }
    // `Numeric` is in this list as the BUNDLE that carries the order, not as an order
    // itself — it is the requirement this change removed, so a carrier that started
    // providing it would silence the whole test.
    for absent in ["PartialOrd", "WeakOrd", "Ord", "Numeric"] {
        assert!(
            !provisions.contains(&("F5".to_string(), absent.to_string())),
            "F5 must provide no order and no order-carrying bundle, but it provides \
             {absent} — the carrier has stopped measuring what this test exists for; \
             provisions: {provisions:?}"
        );
    }

    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    let r = interp
        .call("test.f5.F5.probe_recip", &[])
        .expect("call probe_recip");
    assert_eq!(
        r.literal_int64(interp.kb()),
        Some(3),
        "recip(2) must be 3 in F_5, got {r:?}"
    );
    let d = interp
        .call("test.f5.F5.probe_div", &[])
        .expect("call probe_div");
    assert_eq!(
        d.literal_int64(interp.kb()),
        Some(3),
        "div(4, 3) must be 3 in F_5, got {d:?}"
    );
}

/// `L = F_5[t]/(t^2 - 2)`, a degree-2 extension of `F_5`. An extension L/K is exactly the
/// statement that L is a K-vector space, and `algebra.VectorSpace` declares
/// `requires Ring[F]` — which `Field` now supplies, so a field is a legal scalar without
/// a hand-written second provision. What this row measures is the extension over a base
/// with NO ORDER, which is what was refused outright before (see the block above); the
/// `provides Ring[...]` lines below are kept explicit so the fixture states its own
/// structure rather than leaning on the chain it is testing.
///
/// WHAT IT DOES NOT MEASURE, because the tower cannot state it: that `F_5` is a SUBFIELD
/// of `L`. `inject` below is written as an ordinary operation and nothing relates it to
/// either structure — there is no homomorphism notion, and `provides`/`requires` relate a
/// carrier to a SPEC, never a carrier to another carrier. WI-20260906-CCT6B owns that.
#[test]
fn a_field_extension_is_a_vector_space_over_the_base_field() {
    let src = format!(
        "{F5}\n{}",
        r#"
        sort test.f5.L
          import anthill.prelude.{Int64, Bool, PartialEq, Field}
          import anthill.prelude.algebra.{Ring, VectorSpace}
          import test.f5.{F5}

          entity lv(a: F5, b: F5)

          operation add(x: L, y: L) -> L = lv(a: F5.add(x.a, y.a), b: F5.add(x.b, y.b))
          operation neg(x: L) -> L       = lv(a: F5.neg(x.a), b: F5.neg(x.b))
          operation zero() -> L          = lv(a: F5.zero(), b: F5.zero())
          operation one() -> L           = lv(a: F5.one(), b: F5.zero())
          -- BOTH COMPONENTS. Reading only `a` made `t` equal `2t`, and `Field`'s own
          -- guards (`recip … :- eq(a, 0)`, the laws' `neq(?b, 0)`) read exactly this
          -- operation — so a wrong `eq` here is a wrong answer to the spec, not a
          -- cosmetic fixture defect. Found by /code-review.
          operation eq(x: L, y: L) -> Bool = Bool.and(F5.eq(x.a, y.a), F5.eq(x.b, y.b))
          -- (a + bt)(c + dt) = (ac + 2bd) + (ad + bc)t, since t^2 = 2.
          operation mul(x: L, y: L) -> L =
            lv(a: F5.add(F5.mul(x.a, y.a),
                         F5.mul(F5.mul(x.b, y.b), F5.add(F5.one(), F5.one()))),
               b: F5.add(F5.mul(x.a, y.b), F5.mul(x.b, y.a)))
          -- THE REAL INVERSE, and it was `= x` until /code-review caught it. In
          -- `F_5[t]/(t^2 - 2)` the inverse of `a + bt` is `(a - bt) / (a^2 - 2b^2)`, the
          -- denominator being the field norm. With the identity standing in, `div` was
          -- `mul` and `Field`'s inverse law `mul(div(?a, ?b), ?b) = ?a` was FALSE of the
          -- carrier declaring it — a stub backing a provision, which is exactly what a
          -- fixture must not be when the provision is the thing under discussion.
          operation recip(x: L) -> L =
            let two  = F5.add(F5.one(), F5.one())
            let norm = F5.add(F5.mul(x.a, x.a),
                              F5.neg(F5.mul(two, F5.mul(x.b, x.b))))
            let inv  = F5.recip(norm)
            lv(a: F5.mul(x.a, inv), b: F5.neg(F5.mul(x.b, inv)))
          operation div(x: L, y: L) -> L = mul(x, recip(y))

          -- The K-vector-space structure of L: scalars act by multiplication in L.
          operation inject(c: F5) -> L = lv(a: c, b: F5.zero())
          operation vec_add(x: L, y: L) -> L = add(x, y)
          operation vec_sub(x: L, y: L) -> L = add(x, neg(y))
          operation vec_scale(c: F5, x: L) -> L = mul(inject(c), x)
          operation vec_zero() -> L = zero()

          -- DRIVEN. `t * t = 2`, the defining relation of the extension: the `a`
          -- component of t^2 is 2 and its `b` component is 0.
          operation probe_t_squared() -> Int64 = mul(lv(a: F5.zero(), b: F5.one()),
                                                     lv(a: F5.zero(), b: F5.one())).a.v
          -- ...and the scalar action: 3 * t = 3t, so the `b` component is 3.
          operation probe_scale() -> Int64 = vec_scale(F5.f5(v: 3),
                                                       lv(a: F5.zero(), b: F5.one())).b.v
          -- THE INVERSE LAW, DRIVEN on a concrete element. recip(t) = 3t, since
          -- t * 3t = 3t^2 = 3 * 2 = 6 = 1. Both components of the product are checked:
          -- `a` must be 1 and `b` must be 0, or `mul(recip(t), t)` is not `one`.
          operation probe_recip_b() -> Int64 = recip(lv(a: F5.zero(), b: F5.one())).b.v
          operation probe_inv_law_a() -> Int64 =
            mul(recip(lv(a: F5.zero(), b: F5.one())), lv(a: F5.zero(), b: F5.one())).a.v
          operation probe_inv_law_b() -> Int64 =
            mul(recip(lv(a: F5.zero(), b: F5.one())), lv(a: F5.zero(), b: F5.one())).b.v
          -- ...and that `eq` separates `t` from `2t`, which it did not while it read
          -- only the `a` component.
          operation probe_t_not_2t() -> Bool =
            eq(lv(a: F5.zero(), b: F5.one()), lv(a: F5.zero(), b: F5.f5(v: 2)))

          provides PartialEq[T = L]
          provides Ring[L]
          provides Field[T = L]
          provides VectorSpace[V = L, F = F5]
        end
    "#
    );

    let mut interp = crate::common::interp_for(&src);
    let t2 = interp
        .call("test.f5.L.probe_t_squared", &[])
        .expect("call probe_t_squared");
    assert_eq!(
        t2.literal_int64(interp.kb()),
        Some(2),
        "t^2 must be 2, the defining relation of L = F_5[t]/(t^2 - 2); got {t2:?}"
    );
    let s = interp
        .call("test.f5.L.probe_scale", &[])
        .expect("call probe_scale");
    assert_eq!(
        s.literal_int64(interp.kb()),
        Some(3),
        "the scalar action must send (3, t) to 3t; got {s:?}"
    );

    // L IS A FIELD, DRIVEN, and not merely declared to be one. Both of these were
    // wrong while `recip` was the identity and `eq` read one component: `div` was
    // `mul`, so `Field`'s inverse law was false of the carrier that provides it.
    let r = interp
        .call("test.f5.L.probe_recip_b", &[])
        .expect("call probe_recip_b");
    assert_eq!(
        r.literal_int64(interp.kb()),
        Some(3),
        "recip(t) must be 3t, since t * 3t = 3t^2 = 6 = 1; got {r:?}"
    );
    let la = interp
        .call("test.f5.L.probe_inv_law_a", &[])
        .expect("call probe_inv_law_a");
    let lb = interp
        .call("test.f5.L.probe_inv_law_b", &[])
        .expect("call probe_inv_law_b");
    assert_eq!(
        (la.literal_int64(interp.kb()), lb.literal_int64(interp.kb())),
        (Some(1), Some(0)),
        "mul(recip(t), t) must be `one` = 1 + 0t; got {la:?} + {lb:?}t"
    );
    let neq = interp
        .call("test.f5.L.probe_t_not_2t", &[])
        .expect("call probe_t_not_2t");
    assert_eq!(
        neq.literal_bool(interp.kb()),
        Some(false),
        "`eq` must separate t from 2t; reading only the `a` component made them equal"
    );
}

// ── THE CROSS-NAMESPACE `requires` WIDENS THE SIBLING REACH, AND BY HOW MUCH ──
//
// `Field` requires `anthill.prelude.algebra.Ring`, which crosses a namespace boundary. A
// `requires` reaches the target's SIBLINGS BY DESIGN — WI-1089's rule, restated by
// `wi_n2865_provision_edge_scope_test::a_requires_still_reaches_the_targets_siblings` —
// and N2865 stopped the enclosing chain on a `provides` edge ONLY, recording the
// `requires` residual as deliberate rather than a bug. So the resolver is not where this
// is fixed, and the honest thing is to measure the cost and pin it.
//
// THE FIRST DRAFT OF THIS TEST ASSERTED "NO LEAK" AND WAS WRONG, which is why it is
// written this way. It declared a NAMESPACED `user.Ring` reached by explicit import and
// passed — but the collision needs two candidates for one UNQUALIFIED name, so the shape
// that reproduces it is a BARE top-level `Ring`, which is N2865's own shape.
//
// AND THE HAZARD IS PRE-EXISTING, which is the measurement that decided the change was
// acceptable. Driven with the old `requires Numeric[T]` in place, a consumer's own
// top-level `Additive`, `Numeric` and `Divisible` were EACH already ambiguous under
// `requires Field` — `Field` lives in `anthill.prelude`, so a `requires` on it already
// reached that whole namespace. Only `Ring` was not, because it lives one namespace over.
// This change adds `Ring` and `VectorSpace` to a set that already held the entire prelude.
#[test]
fn requiring_ring_across_namespaces_widens_the_sibling_reach() {
    let consumer = |name: &str| {
        format!(
            r#"
        sort {name}
          entity mk
        end

        sort user.Poly
          import anthill.prelude.{{Field}}
          sort T = ?
          requires Field[T]
          entity poly(coeff: T, tag: {name})
        end
    "#
        )
    };

    // ONE REPRESENTATIVE OF WHAT WAS ALREADY AMBIGUOUS, not the whole census. Each case
    // costs a full stdlib load and this file exists to amortize those (see its header);
    // the full count — 69 of 75 one-segment prelude names — is measured and recorded on
    // WI-20260906-6BX85 rather than re-run here on every suite.
    let errs = crate::common::try_load_kb_with(&consumer("Additive"))
        .err()
        .expect("a top-level `Additive` beside `requires Field` was ALREADY ambiguous before \
                 this change, and must stay so — it is the control, not the cost");
    assert!(
        errs.iter().any(|e| e.contains("ambiguous symbol")),
        "expected the pre-existing ambiguity for Additive; got {errs:?}"
    );

    // AND THE ONE THIS CHANGE ADDED. Backing `requires Ring[T]` out of `field.anthill`
    // makes this row fail and leaves the one above passing — which is what makes it a
    // measurement of the COST rather than of the hazard.
    //
    // THIS ROW PINS BEHAVIOUR THE PROJECT WANTS TO LOSE. It asserts an ambiguity that
    // WI-20260906-6BX85 exists to remove: when the `requires` edge stops carrying the
    // enclosing chain, this assertion goes red and that is the FIX landing, not a
    // regression. Delete the row then; do not repair it.
    let errs = crate::common::try_load_kb_with(&consumer("Ring"))
        .err()
        .expect("a top-level `Ring` beside `requires Field` is ambiguous once Field requires Ring");
    assert!(
        errs.iter().any(|e| {
            e.contains("ambiguous symbol 'Ring'") && e.contains("anthill.prelude.algebra.Ring")
        }),
        "the ambiguity must name `algebra.Ring` as the rival candidate. If this went away \
         because WI-20260906-6BX85 stopped the enclosing chain below a `requires`, DELETE \
         this row rather than repairing it; got {errs:?}"
    );

    // THE REPAIR, MEASURED, because `field.anthill`'s header now offers it to anyone who
    // hits the ambiguity and an unmeasured repair is worth nothing. An explicit import of
    // the name you meant resolves at §8.6 step 2, BEFORE the parent walk runs, so it wins
    // over everything the `requires` edge dragged in. This is also why `Field` itself was
    // one of the three prelude names that did not collide in the census: the consumer
    // imports it.
    crate::common::load_kb_with(
        r#"
        namespace mine
          sort Ring
            entity mk
          end
        end

        sort user.Poly
          import anthill.prelude.{Field}
          import mine.{Ring}
          sort T = ?
          requires Field[T]
          entity poly(c: T, tag: Ring)
        end
    "#,
    );
}

/// `requires PartialEq[T]` is a SEPARATE claim from `requires Ring[T]`, and this is its
/// own control — /code-review found the pair had none, since the stated back-out replaces
/// BOTH lines with `requires Numeric[T]` and every shipped `Field` carrier provides
/// `PartialEq` anyway.
///
/// WHY THE LINE IS THERE: `Field`'s guards spell `eq` and `neq` (`recip … :- eq(a, 0)`,
/// and the three laws' `:- neq(?b, 0)`). Those names reach the DECLARATION through the
/// file's `import anthill.prelude.PartialEq.{eq, neq}`, which is name resolution and says
/// nothing about the carrier. Without this `requires`, a carrier could satisfy `Field`
/// while owing no equality, and every guard in the file would read an `eq` it has not got.
/// `Ring` does not supply it: the algebra tower is equality-free by design.
///
/// THE CARRIER HAS TO DECLARE ITS OWN `eq` FOR THE HOLE TO BE VISIBLE, and that is not a
/// trick — it is `eq_derive`'s rule, and the first draft of this test got it wrong. A
/// composite is DERIVED lawfully `Eq` (hence `PartialEq`) when every field is, so
/// `entity ne(v: Int64)` is handed a `PartialEq` provision by the loader and satisfies the
/// requirement without writing a row. Declaring an `operation eq` makes the sort a
/// DISPATCH BOUNDARY, the derivation stops there, and the carrier then owes the provision
/// it has taken over. Measured, all four combinations:
///
///   provides Ring + PartialEq + Field   LOADS
///   provides Ring            + Field    REFUSED, naming the missing `PartialEq`
///   provides       PartialEq + Field    REFUSED, naming the missing `Ring`
///   provides                   Field    REFUSED, naming BOTH
///
/// WHAT FAILS WHEN IT IS BACKED OUT: this row alone, and that is DRIVEN rather than
/// asserted. Deleting `requires PartialEq[T]` from `field.anthill` and leaving
/// `requires Ring[T]` in place was run: 22 passed, this one failed, and the carrier below
/// loaded clean — which is precisely the hole.
#[test]
fn a_field_carrier_owes_equality() {
    let src = r#"
        -- A would-be field that provides `Ring` and `Field` and NO equality. It declares
        -- its own `eq`, which is what stops `eq_derive` from handing it a `PartialEq` it
        -- never claimed — see this test's own note.
        sort test.noeq.NoEq
          import anthill.prelude.{Int64, Bool, Field, PartialEq}
          import anthill.prelude.algebra.{Ring}

          entity ne(v: Int64)

          operation add(a: NoEq, b: NoEq) -> NoEq = ne(v: Int64.add(a.v, b.v))
          operation neg(a: NoEq) -> NoEq          = ne(v: Int64.sub(0, a.v))
          operation zero() -> NoEq                = ne(v: 0)
          operation mul(a: NoEq, b: NoEq) -> NoEq = ne(v: Int64.mul(a.v, b.v))
          operation one() -> NoEq                 = ne(v: 1)
          operation eq(a: NoEq, b: NoEq) -> Bool  = a.v = b.v
          operation recip(a: NoEq) -> NoEq        = a
          operation div(a: NoEq, b: NoEq) -> NoEq = a

          provides Ring[NoEq]
          provides Field[T = NoEq]
        end
    "#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .expect("a carrier providing Field while providing no PartialEq must be REFUSED");
    assert!(
        errs.iter()
            .any(|e| e.contains("PartialEq") && e.contains("test.noeq.NoEq")),
        "the refusal must name the missing `PartialEq` and the carrier; got {errs:?}"
    );
}
