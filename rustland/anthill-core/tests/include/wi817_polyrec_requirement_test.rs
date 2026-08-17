//! WI-817 — the witness: POLYMORPHIC RECURSION whose requirement changes to
//! the type-argument type at each step (`Desc[Leaf]`, `Desc[Wrap[Leaf]]`,
//! `Desc[Wrap[Wrap[Leaf]]]`, … — unbounded, so `PinNow` is unreachable), with
//! the g→f leg once direct (the operation-only CONTROL) and once routed
//! through a lambda invoked by a requirement-free applier (the WITNESS).
//!
//! THE PREDICTION UNDER TEST (ticket): per-call resolution can serve the
//! changing requirement and resolve-once-at-creation cannot, so the case
//! should be EXPRESSIBLE AS AN OPERATION and INEXPRESSIBLE AS A LAMBDA.
//!
//! THE MEASURED VERDICT (at WI-817 time): the prediction was NOT OBSERVABLE —
//! the operation-only CONTROL failed in every expressible spelling, and the
//! lambda witness NEVER failed differently from its control. A shared defect
//! upstream of any operation/lambda asymmetry decided every outcome: the
//! CALL-SITE REQUIREMENT SUPPLY for a requirement instantiated at a CHANGED
//! type. Concretely (`build_dep_projection`, kb/typing.rs): Strategy 1's
//! `entries_cover` is wildcard-tolerant — a caller `requires Desc[GT]` covers
//! a callee dep `Desc[FT]` whenever either element is a type param — and its
//! σ-class check (WI-419) only disambiguated 2+ covering entries, so a SOLE
//! covering wildcard entry blindly FORWARDED the caller's dictionary even when
//! the call-site substitution maps the dep's element to a COMPOUND of the
//! caller's element (FT := Wrap[GT]).
//!
//! WI-821 FIXED the sort-level half: σ-class agreement now GATES forwarding —
//! in Strategies 1/2 (a disagreeing cover, sole included, is no cover), in
//! Strategy 3's own scope lookup (`resolve_inner`'s `FromScope` step, which
//! would otherwise resurrect the same forward one layer down), and the
//! provider-head match records a RIGID per-call element so the conditional
//! instance's sub-goal instantiates at it instead of dying Cyclic. The
//! sort-level rows below now measure their CORRECT values.
//!
//! WI-822 FIXED the op-scoped-over-SORT-param rows. Their failure was NOT the
//! missing call-site supply channel the ticket predicted (that channel is still
//! absent — `ConcreteApplyWithin` gates on the callee's PARENT SORT chain, and
//! an op-scoped chain has no frame slots at all): the frame that died was the
//! IMPL's, entered by VALUE-DIRECTED dispatch without the impl's own `requires`.
//! That impl's chain is now resolved at the receiver's runtime type and seeded
//! at dispatch, so the op-scoped rows measure the sort-level rows' values.
//! Op-scoped requirements are therefore served BY VALUE-DIRECTION, not by
//! dictionaries — correct wherever a receiver value can direct them (the 551
//! relay chain below), and pinned as a defect where none can
//! (`wi822_op_scoped_supply_test.rs`: a receiver-less spec op is rejected at
//! LOAD under an op-scoped `requires` while its sort-level twin is correct —
//! the residue WI-822 LEG 1 would close).
//!
//! WI-943 FIXED THE OP-TYPE-PARAM ROW — the "separate §5.4 op-param-requires
//! gap" the (b) pins below were written to flip on. An operation type parameter
//! had no symbol→canonical-var channel at all, so `sigma_class` could not
//! classify the `PT` written inside `requires Desc[PT]` and the operation's own
//! clause never covered its own call. (WI-942 hit the same wall for `Ord[T]`
//! and got away with it: `T` collided by SHORT NAME with a stdlib `SortAlias`,
//! so both sides landed on one wrong var and agreed. `PT` / `FT` / `GT` collide
//! with nothing, so they simply had no answer.) With the channel in place the
//! row measures the values this file has always stated as CORRECT.
//!
//! Outcome matrix (all pinned below; letters are the ticket's outcome codes —
//! (b) load error, (c) eval error):
//!
//! | requires channel                  | 1 cond. level | mutual recursion | + lambda leg |
//! |-----------------------------------|---------------|------------------|--------------|
//! | op-scoped over OP type param      | CORRECT (1)   | CORRECT 1/12/122 | CORRECT      |
//! | op-scoped over SORT param         | CORRECT (12)  | CORRECT 1/12/122 | CORRECT      |
//! | SORT-level                        | CORRECT (12)  | CORRECT 1/12/122 | CORRECT      |
//!
//! With every row correct, the ticket's PREDICTION is finally measurable on the
//! op-param row it was written about — and it stays UNOBSERVED: control and
//! witness are identical there too (1/12/122 both ways), so the operation/lambda
//! asymmetry the ticket predicted is still nowhere in the measurements.
//!
//! The `requires`-eval-path hazard flagged by the ticket ("sort-level
//! `requires` makes ops untrappable"; two competing error spellings, neither
//! established) is SETTLED: neither reported error reproduces; sort-level
//! requires works end-to-end through a conditional instance (V8 pins the
//! correct 12). No pinned defects remain in this file.
//! The GLOBAL two-provider rejection this file used to pin as a defect is
//! GONE — WI-843 (058 §4.1 tier 3) moved it to the unselected use site, so
//! the pair below is now a coexistence fixture (`two_describers_pinned_
//! per_site_survive_the_closure_hop`, 75) plus the tier-3 control that
//! keeps the unpinned form an error. The bonus hazard found here — an UNCONDITIONED parametric
//! provider fact silently MIS-PINNING an abstract spec-op call at load — is
//! FIXED by WI-824 (`unconditioned_parametric_fact_refused_at_abstract_call`;
//! the rule and its second, silently-wrong-VALUE witness live in
//! `wi824_abstract_mispin_test.rs`).
//!
//! (The (c) rows flipped under WI-822 and the (b) rows under WI-943; all now
//! assert their correct values.)

use anthill_core::eval::Value;

/// The shared instance block: spec `Desc` with one op, base instance at
/// `Leaf` (describe → 1), CONDITIONAL instance at `Wrap[E]` given `Desc[E]`
/// (describe → 10·describe(inner) + 2). Correct values are therefore
/// depth-coded: describe(wrapⁿ(leaf)) = 1, 12, 122, 1222, … — a wrong
/// dictionary at any step produces a detectably different number.
///
/// Shared with the WI-822 / WI-855 files, which read the SAME depth coding —
/// hence one owner (`common::DESC_INSTANCES`) rather than three copies.
const INSTANCES: &str = crate::common::DESC_INSTANCES;

fn with_instances(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Function}}
{INSTANCES}
{body}
end
"#
    )
}

/// Load `src` and call `entry(n)` on a FRESH interpreter, returning the
/// verbatim result. Fresh per call because a trapped call poisons later
/// calls on the same interpreter; the load doubles as the clean-load gate —
/// `interp_for` prints every load error and panics on a dirty load, so the
/// "loads clean" half of each pin needs no separate load.
fn eval_fresh(src: &str, entry: &str, n: i64) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(n)])
}

/// The WI-325 ladder's suggestion for this spec — asserted by the three pins
/// WI-824 moved onto that ladder. One owner beside `DESC_INSTANCES`, which the
/// same three files share; see `common::MISSING_DESC_REQUIRES`.
const MISSING_REQUIRES: &str = crate::common::MISSING_DESC_REQUIRES;

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but the source loaded clean"))
}

// ── Positive controls: the harness must actually report breakage ─────

/// A deliberately broken program (unknown sort in a signature) must FAIL the
/// load — proves the load path reports errors, so the loads-clean half of
/// the pins below (enforced by `interp_for`'s panic-on-error) is not vacuous.
#[test]
fn positive_control_load_error_is_reported() {
    let src = with_instances(
        "wi817.posload",
        "  sort Holder\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    );
    let errs = load_errs(&src);
    assert!(!errs.is_empty());
}

/// A bogus operation name must Err at eval — proves `interp.call` verdicts
/// are real, so the Ok-value assertions below are not vacuous.
#[test]
fn positive_control_eval_error_is_reported() {
    let mut interp = crate::common::interp_for("");
    let got = interp.call("wi817.no_such.op", &[Value::Int(0)]);
    assert!(got.is_err(), "a bogus op name must Err; got {got:?}");
}

// ── (b) op-scoped requires over an OP-level type param: LOAD-rejected ─

/// FIXED BY WI-943 (was: rejected at load, pinned here as the §5.4 op-param
/// gap). An op-scoped `requires Desc[PT]` over the operation's OWN `[PT]` type
/// param now licenses the abstract spec-op call exactly as the same clause over
/// a SORT param does, in BOTH binding spellings (`Desc[PT]`, `Desc[T = PT]`).
///
/// The gap was an identity one, not a licensing one: `op_requires_covers` asks
/// whether the clause's element and the call's carrier are the same variable,
/// and the WRITTEN `PT` resolved through `type_param_global_var`, which knew
/// only the `SortAlias` channel — a channel an operation parameter is
/// deliberately absent from. So `PT` resolved to NOTHING and no clause could
/// cover anything. Driven to a VALUE (1, the `Leaf` describer), not merely to a
/// clean load: `probe[Leaf](leaf())` must reach the right instance, and "it
/// loads" would pass on a license granted to the wrong dictionary.
///
/// Backing WI-943 out restores the exact pre-fix text this test used to assert:
/// the WI-325 ladder (`MissingRequiresForSpecOp`) at
/// `wi817.opparam.Desc.describe.requires`, both spellings.
#[test]
fn op_param_requires_is_licensed_by_the_operations_own_clause() {
    for req in ["requires Desc[PT]", "requires Desc[T = PT]"] {
        let src = with_instances(
            "wi817.opparam",
            &format!(
                "  sort Holder\n    operation probe[PT](x: PT) -> Int64 {req} = Desc.describe(x)\n    operation drive(n: Int64) -> Int64 = probe[Leaf](leaf())\n  end"
            ),
        );
        let got = eval_fresh(&src, "wi817.opparam.Holder.drive", 0);
        assert!(
            matches!(got, Ok(Value::Int(1))),
            "({req}): expected Ok(Int(1)) — the operation's own `requires` licenses its \
             own describe call and dispatch reaches the Leaf describer (WI-943; pre-fix \
             the load was refused with the WI-325 ladder); got {got:?}"
        );
    }
}

/// FIXED BY WI-943 at full scale — the same §5.4 gap as the test above, on the
/// ticket's actual witness: mutual recursion via explicit per-call type
/// arguments (proposal 042), CONTROL (direct g→f leg) and WITNESS (the leg
/// routed through a lambda invoked by a requirement-free applier). Both load
/// clean and compute the depth-coded 1 / 12 / 122 — the values this test named
/// as CORRECT while it pinned the load rejection.
///
/// AND THIS IS WHERE THE TICKET'S PREDICTION FINALLY GETS ITS OP-PARAM ROW:
/// "expressible as an operation, inexpressible as a lambda". Control and witness
/// are IDENTICAL, at every depth. The prediction stays unobserved on the one row
/// that could not previously be measured at all, which is the same verdict every
/// other row reached.
#[test]
fn op_param_control_and_witness_recurse_identically() {
    let control = with_instances(
        "wi817.control",
        r#"  sort Poly
    operation f[FT](n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else g[FT](n, x)
    operation g[GT](n: Int64, x: GT) -> Int64 requires Desc[GT] =
      f[Wrap[A = GT]](sub(n, 1), wrap(x))
    operation drive(n: Int64) -> Int64 = f[Leaf](n, leaf())
  end"#,
    );
    let witness = with_instances(
        "wi817.lam",
        r#"  sort Poly
    operation apply_fn[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
    operation f[FT](n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else g[FT](n, x)
    operation g[GT](n: Int64, x: GT) -> Int64 requires Desc[GT] =
      apply_fn[Wrap[A = GT]](lambda w -> f[Wrap[A = GT]](sub(n, 1), w), wrap(x))
    operation drive(n: Int64) -> Int64 = f[Leaf](n, leaf())
  end"#,
    );
    for (label, src, ns) in [
        ("control", &control, "wi817.control"),
        ("witness", &witness, "wi817.lam"),
    ] {
        let entry = format!("{ns}.Poly.drive");
        // One interpreter for all three depths: every call is asserted Ok (no trap
        // ever occurs), so the poisoning footgun does not apply.
        let mut interp = crate::common::interp_for(src);
        for (n, correct) in [(0, 1), (1, 12), (2, 122)] {
            let got = interp.call(&entry, &[Value::Int(n)]);
            assert!(
                matches!(got, Ok(Value::Int(v)) if v == correct),
                "{label} drive({n}): expected the depth-coded Ok(Int({correct})) \
                 (WI-943 gave the op type param a canonical identity, so f's own \
                 `requires Desc[FT]` covers its own describe; pre-fix the load was \
                 refused with the WI-325 ladder at {ns}.Desc.describe.requires); \
                 got {got:?}"
            );
        }
    }
}

// ── op-scoped requires over a SORT param ─────────────────────────────

/// The BASELINE that works: op-scoped requires over a sort param, simple
/// concrete binding (`probe(leaf())`). Serves via value-directed eval
/// (WI-562 licensing) — no dictionary involved.
#[test]
fn op_scoped_sort_param_simple_concrete_works() {
    let src = with_instances(
        "wi817.v1",
        r#"  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(leaf())
  end"#,
    );
    let got = eval_fresh(&src, "wi817.v1.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(1))),
        "expected Ok(Int(1)); got {got:?}"
    );
}

/// FIXED BY WI-822 (was: loads clean, then died
/// `Internal(DeferToRequirement: … __req_desc not bound)`). One conditional
/// level (`probe(wrap(leaf()))`), no recursion, no lambda. Value-directed
/// dispatch finds `WrapDesc.describe` from the wrap value; it now also
/// resolves that impl's OWN `requires Desc[T = E]` at the receiver's runtime
/// type (`E := Leaf`) and seeds the frame, so the body's inner describe read
/// finds its dictionary. 12 = 10·1 + 2.
///
/// The frame that died was the IMPL's (`WrapDesc.describe`), NOT the
/// op-scoped caller's (`Holder.probe`) — established by probe, since the
/// message named no frame; it does now. `probe`'s own frame holds no
/// dictionary even after this fix and does not need one: WI-562 licensing
/// leaves its `Desc.describe(x)` for value-directed eval, which reads no
/// slot.
#[test]
fn op_scoped_single_conditional_level_is_correct() {
    let src = with_instances(
        "wi817.v6",
        r#"  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(wrap(leaf()))
  end"#,
    );
    let got = eval_fresh(&src, "wi817.v6.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(12))),
        "expected Ok(Int(12)) — the conditional impl's own requires resolved at \
         the receiver's runtime type (WI-822 LEG 2; pre-fix died unbound); got {got:?}"
    );
}

/// FIXED BY WI-822 (was: depth 0 worked, depth ≥ 1 died unbound) — CONTROL
/// and WITNESS identical, with the lambda leg and without it. The mutual
/// recursion on op-scoped sort-param `requires`: each step wraps the value,
/// so each `Desc.describe` selects `WrapDesc.describe` one level deeper and
/// its chain resolves at the value's own (concrete, deeper) type. Depth-coded
/// 1 / 12 / 122, the same values the sort-level twin measures — so the
/// op-scoped channel now agrees with the sort-level one on this witness.
#[test]
fn op_scoped_recursion_correct_control_and_lambda_identical() {
    let control = with_instances(
        "wi817.v4",
        r#"  sort FHolder
    sort FT = ?
    operation f(n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    operation g(n: Int64, x: GT) -> Int64 requires Desc[GT] =
      FHolder.f(sub(n, 1), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    let witness = with_instances(
        "wi817.v7",
        r#"  sort Applier
    operation apply_fn[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
  end
  sort FHolder
    sort FT = ?
    operation f(n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    operation g(n: Int64, x: GT) -> Int64 requires Desc[GT] =
      Applier.apply_fn(lambda w -> FHolder.f(sub(n, 1), w), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    for (label, src, ns) in [
        ("control", &control, "wi817.v4"),
        ("witness", &witness, "wi817.v7"),
    ] {
        let entry = format!("{ns}.Driver.drive");
        // One interpreter for all three depths: every call is asserted Ok
        // (no trap ever occurs), so the poisoning footgun does not apply and
        // two of the three stdlib loads are saved.
        let mut interp = crate::common::interp_for(src);
        for (n, correct) in [(0, 1), (1, 12), (2, 122)] {
            let got = interp.call(&entry, &[Value::Int(n)]);
            assert!(
                matches!(got, Ok(Value::Int(v)) if v == correct),
                "{label} drive({n}): expected the depth-coded Ok(Int({correct})) \
                 (WI-822 LEG 2 seeds the value-selected impl's own requires; \
                 pre-fix depth 0 gave 1 and depth ≥ 1 died unbound); got {got:?}"
            );
        }
    }
}

// ── SORT-level requires ──────────────────────────────────────────────

/// The requires-eval-path hazard SETTLED: sort-level requires + a
/// CONDITIONAL instance at a concrete compound binding works end-to-end —
/// the call site resolves `Desc[Wrap[Leaf]]` to the nested
/// `Dictionary(Dictionary(impl: Leaf), impl: WrapDesc)` tree and eval expands it
/// correctly (12 = 10·1 + 2). Neither error spelling reported in the ticket
/// (`projection index 0 out of range` / `UnknownOperation`) reproduces here.
#[test]
fn sort_level_single_conditional_level_is_correct() {
    let src = with_instances(
        "wi817.v8",
        r#"  sort Holder
    sort HT = ?
    requires Desc[HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(wrap(leaf()))
  end"#,
    );
    let got = eval_fresh(&src, "wi817.v8.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(12))),
        "expected Ok(Int(12)); got {got:?}"
    );
}

/// FIXED BY WI-821 (was outcome (d), silently wrong at every depth), CONTROL
/// and WITNESS identical. Sort-level requires + the mutual recursion now
/// computes the depth-coded values 1/12/122: the g→f leg's `Desc[FT :=
/// Wrap[GT]]` dep σ-DISAGREES with g's covering `Desc[GT]` entry (mixed
/// param/compound), so instead of forwarding g's dictionary unchanged the
/// call site constructs `Dictionary(var_ref(__req_desc), impl:
/// WrapDesc)` — the conditional instance wrapping the caller's
/// own dictionary one level deeper each round — while the f→g leg (same
/// σ-class, FT ↦ GT) keeps forwarding BY NAME. Before WI-821 the wildcard
/// forward returned 1 at EVERY depth, running the Leaf impl on wrapped
/// values. The lambda leg changes nothing: the closure faithfully restores
/// its creation scope, whose dictionary is now the correct one.
#[test]
fn sort_level_recursion_correct_control_and_lambda_identical() {
    let control = with_instances(
        "wi817.v9",
        r#"  sort FHolder
    sort FT = ?
    requires Desc[FT]
    operation f(n: Int64, x: FT) -> Int64 =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    requires Desc[GT]
    operation g(n: Int64, x: GT) -> Int64 =
      FHolder.f(sub(n, 1), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    let witness = with_instances(
        "wi817.v10",
        r#"  sort Applier
    operation apply_fn[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
  end
  sort FHolder
    sort FT = ?
    requires Desc[FT]
    operation f(n: Int64, x: FT) -> Int64 =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    requires Desc[GT]
    operation g(n: Int64, x: GT) -> Int64 =
      Applier.apply_fn(lambda w -> FHolder.f(sub(n, 1), w), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    for (label, src, ns) in [
        ("control", &control, "wi817.v9"),
        ("witness", &witness, "wi817.v10"),
    ] {
        let entry = format!("{ns}.Driver.drive");
        // One interpreter for all three depths: every call is asserted Ok
        // (no trap ever occurs), so the poisoning footgun does not apply and
        // two of the three stdlib loads are saved.
        let mut interp = crate::common::interp_for(src);
        for (n, correct) in [(0, 1), (1, 12), (2, 122)] {
            let got = interp.call(&entry, &[Value::Int(n)]);
            assert!(
                matches!(got, Ok(Value::Int(v)) if v == correct),
                "{label} drive({n}): expected the depth-coded Ok(Int({correct})) \
                 (WI-821 σ-gated supply; pre-fix wildcard forward measured 1 at \
                 every depth); got {got:?}"
            );
        }
    }
}

/// WI-821 /code-review follow-up: the PARENT-SORT-param half of the staging
/// trigger, measured. `op_tp_pinning_params` claims to cover a callee whose
/// pinnable param is its parent SORT's (`sort X = ?` on Applier) exactly like
/// the op-scoped `[X]` spelling the v10 witness drives — this is the witness
/// twin for that half: the lambda's binder must type from the staged sibling
/// (`a: X` pinned by `wrap(x)`), so its inner f-call constructs the same
/// conditional dict and the recursion stays depth-coded. A wildcard-typed
/// binder would measure 1 at every depth (the WI-817 defect) or die unbound.
#[test]
fn sort_param_applier_witness_matches_control() {
    let witness = with_instances(
        "wi817.v11",
        r#"  sort Applier
    sort X = ?
    operation apply_fn(fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
  end
  sort FHolder
    sort FT = ?
    requires Desc[FT]
    operation f(n: Int64, x: FT) -> Int64 =
      if eq(n, 0) then Desc.describe(x) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    requires Desc[GT]
    operation g(n: Int64, x: GT) -> Int64 =
      Applier.apply_fn(lambda w -> FHolder.f(sub(n, 1), w), wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    let mut interp = crate::common::interp_for(&witness);
    for (n, correct) in [(0, 1), (1, 12), (2, 122)] {
        let got = interp.call("wi817.v11.Driver.drive", &[Value::Int(n)]);
        assert!(
            matches!(got, Ok(Value::Int(v)) if v == correct),
            "sort-param applier drive({n}): expected the depth-coded \
             Ok(Int({correct})); got {got:?}"
        );
    }
}

// ── Multi-hop: lambda relayed through ops holding DIFFERENT dicts ────

/// FIXED BY WI-821 (was 111 — hop dicts wrongly forwarded). The lambda is
/// created under one dictionary (Desc[Leaf], describe→1) and RELAYED through
/// two further operations that each hold their OWN, DIFFERENT `Desc`
/// dictionary (Desc[Pebble], describe→5) before being invoked two frames
/// from its creation scope. Every requirement binding is CONCRETE, so this
/// isolates the dictionary-FLOW question from the changed-type recursion.
///
/// Value coding, CORRECT = 551: invoke = fn(0) + 10·describe(pebble)
/// = 1 + 50 = 51; relay = invoke + 100·describe(pebble) = 51 + 500 = 551
/// (a hop-dict leak INTO the closure would read 555; a pre-WI-821 wildcard
/// forward of the Maker's Leaf dict into both hops read 111).
///
/// The two halves after the σ-gate:
///   - fn(0) = 1 — the closure reads its creation dictionary even two frames
///     away (creation-scope capture holds through the chain; this half was
///     correct before WI-821 too);
///   - each hop's OWN describe reads 5 — the make→relay hand-off's dep
///     (`Desc[RT := Pebble]`) σ-DISAGREES with Maker's `Desc[MT]` entry
///     (mixed param/concrete → no cover), so Strategy 3 constructs the
///     Pebble dictionary; the relay→invoke hand-off (same σ-class, IT ↦ RT)
///     keeps forwarding BY NAME, carrying that constructed dict onward.
///     wi419 measured the 2-covering-entries disambiguation; the SOLE-entry
///     different-instantiation forward was the WI-821 gap.
#[test]
fn lambda_relay_chain_closure_and_hop_dicts_correct() {
    let src = format!(
        r#"
namespace wi817.hops
  import anthill.prelude.{{Int64, Bool, Function}}
{INSTANCES}
  sort Pebble
    entity pebble
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end

  sort Invoker
    sort IT = ?
    requires Desc[IT]
    operation invoke(fn: Function[A = Int64, B = Int64], z: IT) -> Int64 =
      add(fn(0), mul(10, Desc.describe(z)))
  end

  sort Relay
    sort RT = ?
    requires Desc[RT]
    operation relay(fn: Function[A = Int64, B = Int64], y: RT) -> Int64 =
      add(Invoker.invoke(fn, y), mul(100, Desc.describe(y)))
  end

  sort Maker
    sort MT = ?
    requires Desc[MT]
    operation make(x: MT) -> Int64 =
      Relay.relay(lambda ignored -> Desc.describe(x), pebble())
  end

  sort Driver
    operation drive(n: Int64) -> Int64 = Maker.make(leaf())
  end
end
"#
    );
    let got = eval_fresh(&src, "wi817.hops.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(551))),
        "expected Ok(Int(551)) = correct closure (1) + each hop reading its \
         OWN Pebble dict (50 + 500) under the WI-821 σ-gate (pre-fix wildcard \
         forward measured 111); got {got:?}"
    );
}

/// THE SEARCHED CASE (user framing), measured. The relay chain's
/// requirements are OP-SCOPED and their instantiation CHANGES at each
/// hand-off (make holds Desc[Leaf], relay/invoke each hold Desc[Pebble]);
/// the sort-level twin above measured 111 until WI-821's σ-gate made the
/// hand-offs construct (now 551 there too).
/// This op-scoped spelling measures the CORRECT 551 TODAY — but NOT because
/// the op-scoped supply works (it supplies nothing; see the unbound pins):
/// every describe here resolves VALUE-DIRECTED — the runtime value itself
/// picks Leaf/Pebble.describe, no dictionary is ever consulted — so the
/// changed instantiation is served by the values. Pre-WI-821 the two
/// channels failed on COMPLEMENTARY shapes: dict-directed pass-as-is was
/// wrong the moment the instantiation changed (now σ-gated to construct);
/// value-directed no-supply remains right until a dictionary is semantically
/// REQUIRED (a conditional impl's own chain), where it still dies unbound.
/// WI-822's supply channel must KEEP this 551 green.
#[test]
fn op_scoped_relay_chain_correct_via_value_direction() {
    let src = format!(
        r#"
namespace wi817.ophops
  import anthill.prelude.{{Int64, Bool, Function}}
{INSTANCES}
  sort Pebble
    entity pebble
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end

  sort Invoker
    sort IT = ?
    operation invoke(fn: Function[A = Int64, B = Int64], z: IT) -> Int64 requires Desc[IT] =
      add(fn(0), mul(10, Desc.describe(z)))
  end

  sort Relay
    sort RT = ?
    operation relay(fn: Function[A = Int64, B = Int64], y: RT) -> Int64 requires Desc[RT] =
      add(Invoker.invoke(fn, y), mul(100, Desc.describe(y)))
  end

  sort Maker
    sort MT = ?
    operation make(x: MT) -> Int64 requires Desc[MT] =
      Relay.relay(lambda ignored -> Desc.describe(x), pebble())
  end

  sort Driver
    operation drive(n: Int64) -> Int64 = Maker.make(leaf())
  end
end
"#
    );
    let got = eval_fresh(&src, "wi817.ophops.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(551))),
        "the op-scoped relay chain must compute 551 (today via value-directed \
         dispatch, no dictionaries; must SURVIVE the WI-822 supply channel); got {got:?}"
    );
}

/// TWO DESCRIBERS FOR ONE CARRIER, UNPINNED — WI-843 (058 §4.1 tier 3,
/// §5.2) turned this from a DECLARATION-level refusal into a USE-SITE one,
/// and this is the control that says the refusal did not merely vanish.
///
/// Providers for Desc[Pebble] in TWO scopes: LoudDesc (describe→5) in
/// wi817.tdl, QuietDesc (describe→7) in wi817.tdq; a loud-scope op creates
/// the lambda, a quiet-scope op invokes it and describes the same value
/// itself. Neither `Desc.describe` call says which describer it means.
///
/// WHAT CHANGED. Before WI-843 this program drew TWO refusals: a
/// DispatchAmbiguous at each describe site AND the global
/// `ambiguous witness … (keep exactly one)`, the second of which did not
/// depend on any call at all — delete both callers and the load still
/// failed. The declarations are now legal (the pinned sibling below runs
/// them both, in one program), so the ONLY thing refused is the pair of
/// calls that pick no variant, each naming LoudDesc/QuietDesc and the
/// bracket that would choose. Keeping this fixture UNPINNED is what keeps
/// tier 3's refusal tested: editing the only copy into the pinned form
/// would leave "an ambiguous site that says nothing is still an error"
/// asserted nowhere (§5.2 chore (b)).
///
/// Note what this fixture no longer claims. Under a load-time global rule
/// it stood for "the global rule is the WRONG rule" — kernel-language.md
/// §Instance coherence specifies SCOPED selection, and an algebraic
/// language must let Int carry both the additive and the multiplicative
/// monoid. That argument is now DELIVERED, not pending, and its committed
/// form is `wi843_coexisting_instances_test`. What is still deferred is
/// IMPLICIT scoped selection (058 §8): a bare `Desc.describe(w)` does not
/// pick up the enclosing namespace's provider, which is precisely why the
/// two calls below must be written explicitly and why this one is an error.
#[test]
fn two_describers_unpinned_are_refused_at_the_use_site() {
    let src = r#"
namespace wi817.tds
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Pebble
    entity pebble
  end
  sort Mk
    operation mk() -> Pebble = pebble()
  end
end

namespace wi817.tdq
  import anthill.prelude.{Int64, Function}
  import wi817.tds.{Desc, Pebble}
  sort QuietDesc
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 7
  end
  sort QuietOps
    operation invoke(fn: Function[A = Pebble, B = Int64], z: Pebble) -> Int64 =
      add(fn(z), mul(10, Desc.describe(z)))
  end
end

namespace wi817.tdl
  import anthill.prelude.{Int64, Function}
  import wi817.tds.{Desc, Pebble}
  import wi817.tdq.{QuietOps}
  sort LoudDesc
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort LoudOps
    operation run(z: Pebble) -> Int64 =
      QuietOps.invoke(lambda w -> Desc.describe(w), z)
  end
end

namespace wi817.tdd
  import anthill.prelude.{Int64}
  import wi817.tds.{Mk}
  import wi817.tdl.{LoudOps}
  sort Driver
    operation drive(n: Int64) -> Int64 = LoudOps.run(Mk.mk())
  end
end
"#;
    let errs = load_errs(src);
    let text = errs.join("\n");
    assert!(
        text.contains("ambiguous dispatch of `wi817.tds.Desc.describe`")
            && text.contains("wi817.tdl.LoudDesc")
            && text.contains("wi817.tdq.QuietDesc")
            && text.contains("[Desc = "),
        "an unselected dispatch must be refused AT THE CALL, naming both \
         describers and the bracket that picks one; got:\n{text}"
    );
    assert!(
        !text.contains("keep exactly one"),
        "the DECLARATIONS are legal now (the pinned sibling runs them both) — a \
         surviving declaration-level refusal would mean tier 3 doubled the old \
         rule instead of replacing it; got:\n{text}"
    );
}

/// THE SAME PROGRAM WITH ONE SELECTION WRITTEN PER SITE — §9 phase 3b's
/// second acceptance, and the fixture's flipped form (§5.2).
///
/// It measures PIN SURVIVAL THROUGH A CLOSURE HOP, not scope capture. A
/// selection is a per-occurrence static constant emitted at classification
/// (058 §4.5 step 0), so the lambda's pin is decided where its body is
/// WRITTEN and capture plays no part — `reduce_lambda`'s requirement
/// snapshot matters for UNPINNED forwarding. The quiet caller invoking the
/// loud-pinned lambda therefore still gets 5, and the quiet site its own 7:
///
///   5 + 10·7 = 75
///
/// 55 or 77 is a FAILURE, not a variant — 55 means the quiet site took the
/// lambda's provider (a pin cross-wired), 77 that the lambda took the
/// caller's (a pin ignored at the hop). The value is UNCHANGED from what
/// this fixture always documented as its WI-648 acceptance, which is
/// exactly why its old doc comment — "lambda keeps its creation-scope
/// provider" — could have stayed and gone unnoticed while describing a
/// mechanism (scope capture) the pinned program does not use. Implicit
/// scoped selection is deferred (058 §8); this is the acceptance that
/// belongs to what shipped.
#[test]
fn two_describers_pinned_per_site_survive_the_closure_hop() {
    let src = r#"
namespace wi817.tdsp
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Pebble
    entity pebble
  end
  sort Mk
    operation mk() -> Pebble = pebble()
  end
end

namespace wi817.tdqp
  import anthill.prelude.{Int64, Function}
  import wi817.tdsp.{Desc, Pebble}
  sort QuietDesc
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 7
  end
  sort QuietOps
    operation invoke(fn: Function[A = Pebble, B = Int64], z: Pebble) -> Int64 =
      add(fn(z), mul(10, Desc.describe[Desc = QuietDesc](z)))
  end
end

namespace wi817.tdlp
  import anthill.prelude.{Int64, Function}
  import wi817.tdsp.{Desc, Pebble}
  import wi817.tdqp.{QuietOps}
  sort LoudDesc
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort LoudOps
    operation run(z: Pebble) -> Int64 =
      QuietOps.invoke(lambda w -> Desc.describe[Desc = LoudDesc](w), z)
  end
end

namespace wi817.tddp
  import anthill.prelude.{Int64}
  import wi817.tdsp.{Mk}
  import wi817.tdlp.{LoudOps}
  sort Driver
    operation drive(n: Int64) -> Int64 = LoudOps.run(Mk.mk())
  end
end
"#;
    let got = eval_fresh(src, "wi817.tddp.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(75))),
        "expected Ok(Int(75)) = 5 (the lambda's pin, surviving the hop) + 10·7 \
         (the quiet site's own pin); 55 means the pins cross-wired, 77 that one \
         was ignored; got {got:?}"
    );
}

/// FIXED BY WI-821 (was 31001) — the essence-of-the-bug measurement (user
/// framing: every earlier fixture gave all operations the SAME singleton
/// set, so as-is frame inheritance and correct per-callee supply were
/// indistinguishable; the essence is that the SETS DIFFER and a hand-off
/// must REBUILD the callee's set). Caller a requires {Desc[AT]}; callee b
/// requires {Desc[BT], Tagd[BT]} — overlapping in Desc, disjoint in Tagd —
/// and the call instantiates BT := Pebble concretely while a holds
/// AT := Leaf. CORRECT: b(pebble) = 5 + 10·3 = 35, drive = 1 + 1000·35
/// = 35001, and both deps now measure it: the OVERLAPPING dep's wildcard
/// cover (a's `Desc[AT]` over `Desc[BT := Pebble]`) σ-DISAGREES, so it is
/// no cover and Strategy 3 constructs the Pebble dictionary (describe = 5)
/// — the same construction the DISJOINT dep always took (a has no Tagd
/// entry to falsely cover it; tag = 3). Pre-WI-821 the overlap was
/// wildcard-forwarded (a's Leaf dict, describe = 1 → 31001): the callee's
/// set was rebuilt exactly where the caller's set did NOT overlap, and
/// inherited as-is exactly where it did — in ONE call.
#[test]
fn different_sets_overlapping_dep_and_disjoint_dep_both_constructed() {
    let src = r#"
namespace wi817.dsets
  import anthill.prelude.{Int64, Bool}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tagd
    sort T = ?
    operation tag(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort PebbleTag
    fact Tagd[T = Pebble]
    operation tag(x: Pebble) -> Int64 = 3
  end

  sort BOps
    sort BT = ?
    requires Desc[BT]
    requires Tagd[BT]
    operation b(y: BT) -> Int64 = add(Desc.describe(y), mul(10, Tagd.tag(y)))
  end
  sort AOps
    sort AT = ?
    requires Desc[AT]
    operation a(x: AT) -> Int64 = add(Desc.describe(x), mul(1000, BOps.b(pebble())))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = AOps.a(leaf())
  end
end
"#;
    let got = eval_fresh(src, "wi817.dsets.Driver.drive", 0);
    assert!(
        matches!(got, Ok(Value::Int(35001))),
        "expected Ok(Int(35001)) = overlap dep σ-gated to the Pebble construction \
         (5) + disjoint dep constructed (3) under WI-821 (pre-fix forward measured \
         31001); got {got:?}"
    );
}

// ── Bonus hazard found while constructing the witness ────────────────

/// FIXED BY WI-824 (was: loads clean, dies at eval on `no field 'inner'`).
/// With WrapDesc's `requires Desc[T = E]` REMOVED — leaving an UNCONDITIONED
/// parametric provider `fact Desc[T = Wrap[A = E]]` with free `E` — the
/// abstract `Desc.describe(x)` call inside f was silently MIS-PINNED to
/// `WrapDesc.describe` at load: candidate matching let the structured head
/// match the abstract per-call binding var-to-structure, dispatch returned a
/// bogus `Unique`, and WI-325's protection never fired (it guards
/// `NoCandidates`/`NoMatch`, not a `Unique`). WI-824 refuses that match — a
/// rigid skolem is not provably a `Wrap` — so the call falls into the WI-325
/// ladder and is REJECTED AT LOAD, naming the spec op and the `requires`
/// clause that would license it.
///
/// WI-943 narrowed WHICH site: the rejection used to name TWO — f's covered
/// call, uncovered only because of the op-param gap, and `WrapDesc.describe`'s
/// own body. f's is now licensed (its `requires Desc[FT]` covers it), so the
/// ONE surviving error is `Desc.describe(w.inner)` in `WrapDesc`'s body, which
/// genuinely lost its `requires` here — measured, and the sharper report: the
/// only thing named is the only thing actually missing a clause.
#[test]
fn unconditioned_parametric_fact_refused_at_abstract_call() {
    let src = with_instances(
        "wi817.v5",
        r#"  sort Poly
    operation f[FT](n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else g[FT](n, x)
    operation g[GT](n: Int64, x: GT) -> Int64 requires Desc[GT] =
      f[Wrap[A = GT]](sub(n, 1), wrap(x))
    operation drive(n: Int64) -> Int64 = f[Leaf](n, leaf())
  end"#,
    )
    .replace("    requires Desc[T = E]\n", "");
    assert!(
        !src.contains("requires Desc[T = E]"),
        "the conditional's requires must be removed"
    );
    let errs = load_errs(&src);
    let text = errs.join("\n");
    assert!(
        text.contains("wi817.v5.Desc.describe.requires") && text.contains(MISSING_REQUIRES),
        "expected the WI-325 ladder to name the spec op and the missing requires \
         (WI-824: no bogus Unique); got:\n{text}"
    );
}
