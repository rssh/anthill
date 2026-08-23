//! WI-20260822-1MAGR — a provision's member SIGNATURE, compared where the member is
//! the only backing.
//!
//! THE STATE THIS REPLACES. `op_backed` matched a declared member by SHORT NAME ONLY,
//! and kernel-language.md §8.7 said so: "Backing conformance is NOT checked beyond the
//! name (WI-935, measured)". `fact VectorSpace[BadVec, Float]` loaded clean with
//! `vec_add` at one argument, with `vec_sub` returning `Float`, or with `vec_scale`'s
//! parameters swapped — the three repros WI-935 recorded and nobody owned. Each then
//! mis-dispatched or died at the call. The first three rows here are those three
//! programs.
//!
//! THE CENSUS THAT DECIDED THE SHAPE, report-only over the whole corpus and fixture
//! suite — 1152 distinct (carrier, spec, op) pairs across 999 carriers. Running the
//! instance-fact pass's comparison raw flagged 67 of them, and every one was a
//! legitimate program. Two structural exemptions account for 56: the SELF-RECEIVER
//! parameter (a spec typing a parameter as itself names the dispatch receiver; an
//! override narrows it to the carrier) at 42 sites across 32 carriers, and a type
//! carrying an EXPRESSION PROJECTION (`s.T`, which the provision's σ cannot ground) at
//! 14. With both applied, 11 findings survive, and the SOLE-BACKING gate splits them
//! exactly:
//!
//! (The census ran with `op_is_executable` as the gate. The shipped gate is narrower —
//! `is_builtin │ op_has_runnable_body`, which is `op_backed`'s OWN spec-op predicate,
//! because a host `operation_map` on the spec's member says nothing about a given
//! CARRIER (WI-876 defect A) and so must not excuse one. Narrowing can only widen what
//! is compared; re-measured over the full workspace, it moved nothing — 5564 passed, 0
//! failed either way. No corpus provision has a member beside a host-mapped-only spec
//! operation.)
//!
//!   * 3 sit beside a spec operation that HAS its own implementation, and all
//!     three are programs the codebase has already decided must load —
//!     `wi1125.nullary` (`operation neq() -> Bool` beside the `PartialEq.neq`
//!     builtin), `wi1125.witnessunrelated` (an `Int64` helper on a witness sort) and
//!     `wi1042.nonparametric` (a non-parametric `provides`). They still load.
//!   * 8 sit beside a body-less spec operation, and all eight are deliberate mismatch
//!     fixtures. Six are in `wi347_override_refinement_test`: three were already
//!     refused by WI-20260822-59CDQ's result-binder guard, and the other three were
//!     its SCOPE CONTROLS, so this ticket is the reason their boundary moves — each is
//!     re-pinned there as "refused by the signature rule, and NOT by the discharge
//!     one". The other two are `p3_spec_wrong_sig.anthill` and `p7_sig_and_row.anthill`
//!     in `docs/measurements/guardians/`, the probes that RECORDED this gap: C1 of
//!     `examples/guardians/docs/design/measured.md` is "signature conformance is not
//!     checked · **the gap**", and it is now closed.
//!
//! WHAT FAILS WHEN THIS IS BACKED OUT — MEASURED, not predicted, by mutating rather
//! than deleting (`check_member_signature` returns immediately, so the pass still runs
//! and only the verdict changes) over all 3353 `anthill-core` tests. EXACTLY SIX fail
//! and nothing else:
//!
//!   * the four arms here — `vec_add_at_one_argument_is_refused`,
//!     `vec_sub_returning_the_scalar_is_refused`,
//!     `vec_scale_with_its_parameters_swapped_is_refused`,
//!     `a_wrong_return_with_no_spec_default_is_refused`;
//!   * two of the three re-pinned `wi347_override_refinement_test` rows —
//!     `a_mismatched_return_type_no_clause_reads_is_not_the_discharge_rules_business`
//!     and `an_impl_only_ensures_over_result_is_not_the_discharge_rules_business`.
//!
//! THE SEVENTH ROW I EXPECTED IS NOT THERE, and naming it is half the measurement:
//! `a_weakening_is_reported_as_one_even_when_the_return_types_also_differ` passes
//! EITHER WAY, because after the re-pin both its assertions are about the DISCHARGE
//! rule ("weakens the postcondition" is reported, and no discharge refusal is) and
//! neither depends on this check. It moved its spelling, not its subject. That the
//! back-out reaches nothing else is the other half: this rule refuses only programs
//! that declare a member which does not fit, and no stdlib carrier, no example and no
//! other fixture has one.
//!
//! The CONTROLS below pass either way BY DESIGN and each says so at its own site: they
//! exist to pin the exemptions, and a back-out of the whole check cannot move a row
//! that asserts a clean load. Each control therefore names its OWN back-out — the
//! narrower mutation that does move it.
//!
//! TWO MORE ROWS CAME FROM THIS TICKET'S `/code-review`, at the end of the file, and
//! each has its own back-out MEASURED rather than predicted:
//!   * dropping the `continue` on `MemberSignature::ArityDiffers` takes
//!     `an_arity_mismatch_does_not_also_report_a_strengthened_precondition` and only it;
//!   * widening the gate back to `op_is_executable` takes
//!     `a_host_mapping_on_the_spec_member_does_not_excuse_the_carriers` and only it.

use anthill_core::eval::Value;

use crate::common;

/// Load `src` beside the stdlib and return the rendered load errors.
fn load_errors(src: &str) -> Vec<String> {
    common::try_load_kb_with(src).err().unwrap_or_default()
}

/// The one message this ticket raises, so a row cannot pass on an unrelated error
/// that happens to mention the operation.
fn signature_refusals(src: &str) -> Vec<String> {
    load_errors(src)
        .into_iter()
        .filter(|e| e.contains("does not fit"))
        .collect()
}

/// The three WI-935 repros are one program with one member rewritten, so they are
/// written as one fixture with a hole. `members` replaces the whole member block.
fn bad_vec(ns: &str, members: &str) -> String {
    format!(
        r#"
namespace wi1magr.{ns}
  import anthill.prelude.{{Float}}
  import anthill.prelude.algebra.{{VectorSpace}}

  sort BadVec
    entity BadVec(x: Float, y: Float, z: Float)
{members}
  end

  fact VectorSpace[BadVec, Float]
end
"#
    )
}

/// Replace one whole member line of [`GOOD_MEMBERS`], asserting the replacement
/// happened. Without the assert, a whitespace drift in `GOOD_MEMBERS` would leave the
/// CONFORMING program in place and the row would fail as "expected 1 refusal, got 0" —
/// a true statement about a fixture that no longer contains the defect it names.
fn swap_member(from: &str, to: &str) -> String {
    let out = GOOD_MEMBERS.replace(from, to);
    assert_ne!(out, GOOD_MEMBERS, "fixture drift: no member line matches `{from}`");
    out
}

/// The conforming member block — the shape `anthill.geometry.Vec3` ships. Each repro
/// below replaces exactly one of these four lines.
const GOOD_MEMBERS: &str = r#"    operation vec_add(a: BadVec, b: BadVec) -> BadVec = BadVec(x: a.x + b.x, y: a.y + b.y, z: a.z + b.z)
    operation vec_sub(a: BadVec, b: BadVec) -> BadVec = BadVec(x: a.x - b.x, y: a.y - b.y, z: a.z - b.z)
    operation vec_scale(c: Float, v: BadVec) -> BadVec = BadVec(x: c * v.x, y: c * v.y, z: c * v.z)
    operation vec_zero() -> BadVec = BadVec(x: 0.0, y: 0.0, z: 0.0)"#;

// ── the three WI-935 repros ──────────────────────────────────────────────────

#[test]
fn vec_add_at_one_argument_is_refused() {
    // REPRO 1 of WI-935, verbatim from its own text: "`fact VectorSpace[BadVec, Float]`
    // loads clean when `vec_add` takes one argument". It does not any more.
    let members = swap_member(
        "    operation vec_add(a: BadVec, b: BadVec) -> BadVec = BadVec(x: a.x + b.x, y: a.y + b.y, z: a.z + b.z)",
        "    operation vec_add(a: BadVec) -> BadVec = a",
    );
    let errs = signature_refusals(&bad_vec("arity", &members));
    assert_eq!(
        errs.len(),
        1,
        "a one-argument `vec_add` must be refused exactly once; got: {errs:#?}"
    );
    // BOTH SHAPES NAMED — the acceptance condition. An author told only "it does not
    // fit" has to go read the spec to find out how.
    assert!(
        errs[0].contains("vec_add(a: BadVec, b: BadVec) -> BadVec")
            && errs[0].contains("vec_add(a: BadVec) -> BadVec"),
        "the refusal must name the spec's declared shape AND the member's; got: {errs:#?}"
    );
    assert!(
        errs[0].contains("2 parameter(s)") && errs[0].contains("(1)"),
        "and the arity that differs; got: {errs:#?}"
    );
}

#[test]
fn vec_sub_returning_the_scalar_is_refused() {
    // REPRO 2: "`vec_sub` returning `Float`". This is the leg WI-20260822-59CDQ could
    // NOT reach — no contract clause here mentions `result`, so its result-binder guard
    // never looks at the return type. §8.7 named that gap and handed it here.
    let members = swap_member(
        "    operation vec_sub(a: BadVec, b: BadVec) -> BadVec = BadVec(x: a.x - b.x, y: a.y - b.y, z: a.z - b.z)",
        "    operation vec_sub(a: BadVec, b: BadVec) -> Float = a.x - b.x",
    );
    let errs = signature_refusals(&bad_vec("ret", &members));
    assert_eq!(
        errs.len(),
        1,
        "a `vec_sub` returning the scalar must be refused exactly once; got: {errs:#?}"
    );
    assert!(
        errs[0].contains("returns `Float`") && errs[0].contains("spec's `BadVec`"),
        "the refusal must name both return types, the spec's at THIS provision's \
         bindings (`V` is `BadVec` here, not `V`); got: {errs:#?}"
    );
}

#[test]
fn vec_scale_with_its_parameters_swapped_is_refused() {
    // REPRO 3: "`vec_scale`'s parameters are swapped". The spec is
    // `vec_scale(c: F, v: V)`; this writes the vector first. Reported as an ORDER
    // mistake rather than as two unrelated parameter mismatches, because that is the
    // repair — and it is decidable HERE only because `Float` and `BadVec` differ (see
    // `two_parameters_of_the_same_type_swapped_are_not_decidable`).
    let members = swap_member(
        "    operation vec_scale(c: Float, v: BadVec) -> BadVec = BadVec(x: c * v.x, y: c * v.y, z: c * v.z)",
        "    operation vec_scale(v: BadVec, c: Float) -> BadVec = BadVec(x: c * v.x, y: c * v.y, z: c * v.z)",
    );
    let errs = signature_refusals(&bad_vec("order", &members));
    assert_eq!(
        errs.len(),
        1,
        "a swapped `vec_scale` must be refused exactly once; got: {errs:#?}"
    );
    assert!(
        errs[0].contains("different ORDER"),
        "a permutation that WOULD fit is an order mistake and must be named as one; \
         got: {errs:#?}"
    );
    assert!(
        errs[0].contains("vec_scale(c: Float, v: BadVec) -> BadVec")
            && errs[0].contains("vec_scale(v: BadVec, c: Float) -> BadVec"),
        "and both shapes must be named; got: {errs:#?}"
    );
}

#[test]
fn the_conforming_carrier_loads_and_its_members_evaluate() {
    // THE ARM'S OWN CONTROL, and it DRIVES rather than asserting a clean load: the
    // three rows above differ from this one by a single member line, so if this were
    // refused too they would be measuring the fixture and not the rule.
    let probe = format!(
        "{GOOD_MEMBERS}\n    operation sumX() -> Float = vec_add(BadVec(x: 1.0, y: 2.0, z: 3.0), BadVec(x: 10.0, y: 20.0, z: 30.0)).x"
    );
    let src = bad_vec("good", &probe);
    let mut interp = common::interp_for(&src);
    let out = interp
        .call("wi1magr.good.BadVec.sumX", &[])
        .expect("the conforming provision's member must RUN, not merely load");
    assert!(
        matches!(out, Value::Float(f) if (f - 11.0).abs() < 1e-9),
        "1.0 + 10.0 = 11.0 through the carrier's own `vec_add`; got: {out:?}"
    );
}

// ── what is NOT decidable, each pinned by its own program ────────────────────

#[test]
fn two_parameters_of_the_same_type_swapped_are_not_decidable() {
    // THE PARTIAL CHECK, SAID OUT LOUD. `combine(a: Int64, b: Int64)` written in either
    // order is the SAME signature — nothing in the types distinguishes them — so the
    // order leg cannot see this swap and the message never claims it could. The rule
    // documents this rather than implying full coverage.
    //
    // DRIVEN, because that is what makes the gap concrete rather than a caveat: the
    // member below is written with its parameters reversed, it loads, and it answers
    // the SECOND argument where the spec's own reading would give the first.
    //
    // NO BACK-OUT FLIPS THIS ROW, and that is the point rather than a weakness. The
    // positional comparison finds nothing wrong here — `Int64` against `Int64` at both
    // positions — so the order leg is never even reached, and no mutation of this check
    // can make it reached. The row measures the BOUNDARY of the rule, which is why the
    // assertion is on the ANSWER (2, the second argument) and not on a clean load: the
    // swap is real and changes what runs, and the only thing pinned is that nothing
    // here can see it.
    let src = r#"
namespace wi1magr.sametype
  import anthill.prelude.{Int64}

  sort TwoInts
    sort T = ?
    operation combine(a: Int64, b: Int64) -> Int64
  end

  sort Marker
    entity marker
    fact TwoInts[T = Marker]
    -- The spec's FIRST parameter is `a`; this member names its SECOND one `a`.
    operation combine(b: Int64, a: Int64) -> Int64 = a
  end
end
"#;
    let mut interp = common::interp_for(src);
    let out = interp
        .call(
            "wi1magr.sametype.Marker.combine",
            &[Value::Int(1), Value::Int(2)],
        )
        .expect("the swapped-but-indistinguishable member must load and run");
    assert!(
        matches!(out, Value::Int(2)),
        "the member reads its SECOND parameter where the spec's first is `a` — the swap \
         is real, it changes the answer, and nothing here can see it; got: {out:?}"
    );
}

#[test]
fn a_self_receiver_narrowed_to_the_carrier_loads_and_dispatches() {
    // THE SELF-RECEIVER EXEMPTION. A spec that types a parameter as ITSELF
    // (`peek(b: Boxy)`) is naming the dispatch receiver; the override narrows it to the
    // carrier (`peek(b: IntBox)`), which contravariance would refuse and dispatch makes
    // sound. This is not a rare shape: the census counted 42 such parameters across 32
    // carriers, `anthill.prelude`'s `FiniteStream`/`List`/`LogicalStream`/
    // `MappedStream`/`Relation` among them — it is the ORDINARY way a stdlib member
    // that takes its own carrier is written.
    //
    // PASSES EITHER WAY under a back-out of the whole check, and its own back-out is
    // not worth running as a test: deleting the `is_receiver` disjunct refuses all 42
    // of those, which the census already recorded one by one. This row is the small
    // driven instance of that population.
    let src = r#"
namespace wi1magr.receiver
  import anthill.prelude.{Int64}

  sort Boxy
    sort T = ?
    operation peek(b: Boxy) -> Int64
  end

  sort IntBox
    entity intBox(v: Int64)
    fact Boxy[T = Int64]
    operation peek(b: IntBox) -> Int64 = b.v

    operation peeked() -> Int64 = peek(intBox(7))
  end
end
"#;
    let mut interp = common::interp_for(src);
    let out = interp
        .call("wi1magr.receiver.IntBox.peeked", &[])
        .expect("a receiver-narrowing override must DISPATCH, not merely load");
    assert!(
        matches!(out, Value::Int(7)),
        "the carrier's own `peek` ran; got: {out:?}"
    );
}

// ── the SOLE-BACKING gate, in both directions ────────────────────────────────

#[test]
fn a_wrong_return_with_no_spec_default_is_refused() {
    // ARM. `Undefaulted.describe` is body-less, so this member is the only thing that
    // could ever back it — and it returns the wrong type.
    let src = r#"
namespace wi1magr.nodefault
  import anthill.prelude.{Int64, Bool}

  sort Undefaulted
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leafy
    entity leafy
    fact Undefaulted[T = Leafy]
    operation describe(x: Leafy) -> Bool = true
  end
end
"#;
    let errs = signature_refusals(src);
    assert_eq!(
        errs.len(),
        1,
        "a body-less spec operation's only candidate implementation must fit; \
         got: {errs:#?}"
    );
    assert!(
        errs[0].contains("returns `Bool`") && errs[0].contains("spec's `Int64`"),
        "naming both return types; got: {errs:#?}"
    );
}

#[test]
fn the_same_mismatch_beside_a_spec_default_still_loads() {
    // THE GATE, and its own fixture rather than a mutation of the row above — the two
    // sources differ by exactly the ` = 1` that gives the spec operation a body. With
    // one, the member is a DISTINCT operation and the default is what backs the
    // provision (§8.7's `requires`-direction reading, WI-1048); a call that expected
    // the spec's `Int64` is already a type error naming both types. Without one, the
    // member is the only backing there is.
    //
    // This is the gate that keeps three DECIDED programs loading — `wi1125.nullary`,
    // `wi1125.witnessunrelated` and `wi1042.nonparametric`, each of which sits beside
    // an executable spec operation (two builtins and a default body).
    //
    // PASSES EITHER WAY under a back-out of the whole check. Its own back-out: delete
    // the `op_is_executable` early return, and this row is refused — which is also what
    // takes `wi1125_neq_not_an_override_test::a_nullary_member_named_neq_is_not_this_
    // spec_op` and two others with it.
    let src = r#"
namespace wi1magr.defaulted
  import anthill.prelude.{Int64, Bool}

  sort Defaulted
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leafy
    entity leafy
    fact Defaulted[T = Leafy]
    operation describe(x: Leafy) -> Bool = true
  end
end
"#;
    let errs = signature_refusals(src);
    assert!(
        errs.is_empty(),
        "beside a spec default the same member is a distinct operation, not a bad \
         override; got: {errs:#?}"
    );
}

// ── two rows from this ticket's /code-review, each a driven repro ────────────

#[test]
fn an_arity_mismatch_does_not_also_report_a_strengthened_precondition() {
    // /code-review FINDING 2. Every leg after the signature check compares in the
    // SPEC'S param vocabulary through a positional `zip` of the two parameter lists.
    // Across two different arities that zip pairs unrelated parameters and leaves the
    // member's surplus ones unaligned, so a precondition the member restates VERBATIM
    // stops matching and is reported as a STRENGTHENING it is not.
    //
    // MEASURED before the fix: this program produced the signature refusal AND
    // "it strengthens the precondition — the override `requires` a condition the spec
    // operation does not". The member's `requires posi(b)` is character-for-character
    // the spec's.
    //
    // BACK-OUT: drop the `continue` on `MemberSignature::ArityDiffers` at
    // `check_override_refinement`'s call site and this row fails on the second
    // assertion. The FIRST assertion passes either way — it is the control that says
    // the fixture still trips the rule it is about.
    let src = r#"
namespace wi1magr.arity_and_contract
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Ord.{gt}

  sort Sp
    sort T = ?
    operation posi(n: Int64) -> Bool = gt(n, 0)
    operation describe(a: T, b: Int64) -> Int64 requires posi(b)
  end

  sort Leafy
    entity leafy
    fact Sp[T = Leafy]
    operation describe(b: Int64) -> Int64 requires posi(b) = b
  end
end
"#;
    let errs = load_errors(src);
    assert_eq!(
        signature_refusals(src).len(),
        1,
        "the arity mismatch itself must still be refused; got: {errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("strengthens the precondition")),
        "the member's `requires posi(b)` IS the spec's — reporting it as a \
         strengthening sends the author to a line that is already correct; got: {errs:#?}"
    );
}

#[test]
fn a_host_mapping_on_the_spec_member_does_not_excuse_the_carriers() {
    // /code-review FINDING 1's subject, from the other side. `anthill.persistence`'s
    // `Store.persist` is body-less and not a builtin — it is realized by a host
    // `operation_map` entry (`persist: "store_persist"` in
    // `rustland/anthill-stl/anthill/persistence.anthill`). That index is FLAT: it has
    // no carrier dimension, so it says an implementation exists somewhere and never
    // that THIS carrier is realized (WI-876 defect A, which is why `op_backed` does not
    // count it for its spec-op candidate either).
    //
    // So a carrier of `Store` whose own `persist` does not fit IS unbacked, and the
    // gate must not excuse it. The refusal must also not CLAIM there is no host
    // implementation, because there is one — it just backs no carrier.
    //
    // BACK-OUT: widen the gate back to `op_is_executable` and this row loads clean.
    let src = r#"
namespace wi1magr.hostmapped
  import anthill.prelude.{Int64, Bool}
  import anthill.persistence.{Store}

  sort MyStore
    entity myStore(n: Int64)
    provides Store
    operation persist(s: Int64) -> Bool = true
  end
end
"#;
    let errs = signature_refusals(src);
    assert_eq!(
        errs.len(),
        1,
        "a host mapping on `Store.persist` backs no carrier, so this member is still \
         the only backing and must fit; got: {errs:#?}"
    );
    assert!(
        !errs[0].contains("or host implementation"),
        "and the message must not claim there is no host implementation — there is \
         one, it just names no carrier; got: {errs:#?}"
    );
    assert!(
        errs[0].contains("names no carrier"),
        "the message must say WHY the host mapping does not count; got: {errs:#?}"
    );
}
