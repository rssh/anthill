//! WI-827 — σ integration into provider-candidate matching
//! (`match_candidate_against_goal`), fixed.
//!
//! Background (WI-821 /code-review findings 3, 5, 8, 11): the candidate matcher
//! classified a per-call element by its SURFACE SPELLING — arm (1)'s record leg
//! fired only on a literal `Var::Rigid`, its consistency leg on
//! `values_structurally_equal`. Both mis-read the σ-ROLE of an element:
//!
//!   (a) COMPOUND requirement. `substitute_spec_via_subst` deliberately
//!       preserves an abstract element as a written `Ref` (`requires
//!       Desc[T = Wrap[A = DT]]` handed a bare param keeps `Wrap[A = Ref(DT)]`,
//!       NOT `Wrap[A = Var::Rigid]`). The `Ref`-spelled interior is a definite
//!       skolem the subst chases to the caller's rigid, but the head-only
//!       `Var::Rigid` test SKIPPED recording it — so the conditional sub-goal
//!       kept the raw impl param, matched the same parametric provider again,
//!       and died Cyclic (dict `None` → runtime `__req_desc not bound`). The
//!       semantically identical WHOLE-PARAM spelling (`requires Desc[T = WT]`
//!       at `WT := Wrap[A = rigid]`) substitutes the concrete-headed compound
//!       and DOES record its `Var::Rigid` interior, so it worked — a spelling
//!       split over one program.
//!
//!   (b) A DIAGONAL provider (`fact Desc[T = Pair[A = E, B = E]]`) binds one
//!       impl param `E` in two slots. At two DISTINCT rigids (`A := rigidG,
//!       B := rigidH`) the type-param early-return recorded only the FIRST and
//!       never compared the second against the occupied slot — a half-wrong
//!       dict. The provider genuinely cannot describe a pair of two different
//!       element types; the sound verdict is refusal.
//!
//!   (c) A COMPOUND element compared component-wise: the stored-rigid-yield /
//!       consistency legs read only the stored HEAD, so a slot holding a
//!       compound-containing-rigid and one holding a bare rigid disagreed about
//!       the same structural disagreement — the verdict depended on which side
//!       of the fact the compound was written, not on the disagreement.
//!
//! THE FIX: the call-site σ (`ResolutionScope.sigma`, already in
//! `resolve_inner`'s hand at the `collect_provides_candidates` call) rides into
//! candidate matching, and each per-call element is classified ONCE via
//! `sigma_class_terminal` — spelling-neutrally: rigid-terminal → RECORD the
//! skolem (any spelling); unbound global → unconstraining skip (WI-507);
//! concrete → bind / check σ-structurally. Rigid-conflict semantics are
//! deliberate: two DISTINCT rigids in one slot REFUSE; a compound is compared
//! component-wise (`sigma_pair_precise`); a stored rigid yields to an incoming
//! concrete (order symmetry). The σ-less consumers (`resolve_at_goal`) pass
//! `None` and keep the head-only behaviour.
//!
//! Depth coding (shared with the wi817 / wi825 suites):
//! describe(wrapⁿ(leaf)) = 1, 12, 122; describe on a `Pebble` base = 5. A wrong
//! dictionary at any step produces a detectably different number.

use anthill_core::eval::Value;

/// Spec `Desc` + a `Leaf` base (describe → 1), a `Pebble` base (describe → 5),
/// and the CONDITIONAL `WrapDesc` (describe → 10·inner + 2). Same block as the
/// wi817 / wi825 suites.
const INSTANCES: &str = r#"
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
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

  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end

  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end
"#;

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

/// Load `src` on a FRESH interpreter (which panics on a dirty load, so the
/// "loads clean" half of each value pin is enforced) and call `entry(0)`.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but the source loaded clean"))
}

// ── Positive control ─────────────────────────────────────────────────

/// A deliberately broken program (unknown sort in a signature) must FAIL the
/// load — proves the load path reports errors, so the loads-clean half of the
/// value pins below (enforced by `interp_for`'s panic-on-error) is not vacuous.
#[test]
fn positive_control_load_error_is_reported() {
    let src = with_instances(
        "wi827.posload",
        "  sort Holder\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    );
    assert!(!load_errs(&src).is_empty());
}

// ── (a) COMPOUND requirement: Ref-spelled interior is recorded ───────

/// THE DRIVEN DEFECT (a). `DeepHolder requires Desc[T = Wrap[A = DT]]` handed a
/// BARE abstract param (`CHolder.c(x: CT) = DeepHolder.d(x)`, so `DT := CT`).
/// `substitute_spec_via_subst` preserves the interior as `Wrap[A = Ref(DT)]`
/// (an abstract element), and the pre-fix head-only `Var::Rigid` record leg
/// SKIPPED it — the conditional sub-goal kept the raw impl param and died
/// Cyclic at LOAD. The σ classifier now records the `Ref`-spelled skolem, so
/// the sub-goal resolves `FromScope` against `CHolder`'s own `Desc[T = CT]`
/// and the dict is built: describe(wrap(pebble)) = 10·5 + 2 = 52.
#[test]
fn compound_requirement_constructs_dict_not_cyclic() {
    let src = with_instances(
        "wi827.compound",
        r#"  sort DeepHolder
    sort DT = ?
    requires Desc[T = Wrap[A = DT]]
    operation d(y: DT) -> Int64 = Desc.describe(wrap(y))
  end
  sort CHolder
    sort CT = ?
    requires Desc[T = CT]
    operation c(x: CT) -> Int64 = DeepHolder.d(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = CHolder.c(pebble())
  end"#,
    );
    let got = eval_fresh(&src, "wi827.compound.Driver.drive");
    assert!(
        matches!(got, Ok(Value::Int(52))),
        "expected Ok(Int(52)) = the compound requirement's Ref-spelled skolem \
         recorded so the dict constructs (pre-fix the record leg skipped it and \
         the load died Cyclic); got {got:?}"
    );
}

/// THE SEMANTIC CONTROL for (a): the WHOLE-PARAM spelling of the SAME program.
/// `WHolder requires Desc[T = WT]` handed `wrap(x)` binds `WT := Wrap[A =
/// rigid]`, whose concrete-headed compound `substitute_spec_via_subst`
/// substitutes with a `Var::Rigid` interior — so this spelling was recorded and
/// worked pre-fix too. Both spellings compute the identical 52; the fix removes
/// the split.
#[test]
fn whole_param_spelling_is_the_semantic_control() {
    let src = with_instances(
        "wi827.whole",
        r#"  sort WHolder
    sort WT = ?
    requires Desc[T = WT]
    operation hw(w: WT) -> Int64 = Desc.describe(w)
  end
  sort CHolder2
    sort CT = ?
    requires Desc[T = CT]
    operation c2(x: CT) -> Int64 = WHolder.hw(wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = CHolder2.c2(pebble())
  end"#,
    );
    let got = eval_fresh(&src, "wi827.whole.Driver.drive");
    assert!(
        matches!(got, Ok(Value::Int(52))),
        "expected Ok(Int(52)) = the whole-param spelling (worked pre-fix too); got {got:?}"
    );
}

// ── (b) DIAGONAL provider: one impl param bound in two slots ─────────

/// The shared diagonal provider + callee that REQUIRES it, so a cross-sort
/// hand-off constructs `Desc[Pair[…]]` via `build_dep_projection` Strategy 3
/// (where the call-site σ is in hand).
const DIAGONAL: &str = r#"  sort Pair
    sort A = ?
    sort B = ?
    entity pair(fst: A, snd: B)
  end
  sort PairDesc
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Pair[A = E, B = E]]
    operation describe(p: Pair[A = E, B = E]) -> Int64 =
      add(Desc.describe(p.fst), mul(10, Desc.describe(p.snd)))
  end
  sort PHolder
    sort PA = ?
    sort PB = ?
    requires Desc[T = Pair[A = PA, B = PB]]
    operation ph(a: PA, b: PB) -> Int64 = Desc.describe(pair(a, b))
  end"#;

/// THE DRIVEN DEFECT (b), SAME rigid. `CallerSame(a: CT, b: CT)` binds both of
/// PHolder's params to ONE rigid `CT`, so the diagonal `Pair[A = E, B = E]`
/// matches with both slots agreeing on `E := CT`. Pre-fix neither `Ref`-spelled
/// slot was recorded, the sub-goal `Desc[T = Ref(E)]` matched WrapDesc AND
/// PairDesc as wildcards, and the load died Ambiguous. The σ classifier records
/// the skolem and confirms the second slot's rigid EQUALS the first, so the
/// dict constructs: describe(pair(pebble, pebble)) = 5 + 10·5 = 55.
#[test]
fn diagonal_same_rigid_both_correct() {
    let src = with_instances(
        "wi827.diag_same",
        &format!(
            r#"{DIAGONAL}
  sort CallerSame
    sort CT = ?
    requires Desc[T = CT]
    operation call(a: CT, b: CT) -> Int64 = PHolder.ph(a, b)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = CallerSame.call(pebble(), pebble())
  end"#
        ),
    );
    let got = eval_fresh(&src, "wi827.diag_same.Driver.drive");
    assert!(
        matches!(got, Ok(Value::Int(55))),
        "expected Ok(Int(55)) = the diagonal recorded and its two slots agreeing \
         on one rigid (pre-fix the unrecorded raw impl param matched two \
         providers and the load died Ambiguous); got {got:?}"
    );
}

/// THE SOUND verdict for (b), DISTINCT rigids. `CallerDiff(a: CA, b: CB)` binds
/// PHolder's two params to DISTINCT rigids, so the diagonal's single `E` meets
/// `CA` in one slot and `CB` in the other — it cannot be one type, and no other
/// provider describes a two-different-element pair. Pre-fix the first rigid was
/// recorded and the conflicting second SILENTLY IGNORED (a half-wrong dict);
/// the σ classifier compares the second against the occupied slot and REFUSES,
/// surfaced as a load diagnostic (WI-828). Refusal is the sound outcome.
#[test]
fn diagonal_distinct_rigids_refused() {
    let src = with_instances(
        "wi827.diag_diff",
        &format!(
            r#"{DIAGONAL}
  sort CallerDiff
    sort CA = ?
    sort CB = ?
    requires Desc[T = CA]
    requires Desc[T = CB]
    operation calld(a: CA, b: CB) -> Int64 = PHolder.ph(a, b)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = CallerDiff.calld(leaf(), pebble())
  end"#
        ),
    );
    let errs = load_errs(&src);
    let text = errs.join("\n");
    assert!(
        text.contains("wi827.diag_diff.PHolder.ph")
            && text.contains("cannot be supplied"),
        "expected a load refusal of PHolder.ph's diagonal requirement at two \
         distinct rigids (sound: the diagonal cannot describe a mismatched \
         pair); got:\n{text}"
    );
}

/// THE SOUND verdict for the MIXED rigid/concrete slot (/code-review finding).
/// `CallerMixed(a: CT)` forwards `Desc[T = Pair[A = CT, B = Pebble]]` — the
/// diagonal's `E` meets an abstract RIGID `CT` in one slot and the CONCRETE
/// `Pebble` in the other. A rigid skolem is never provably a specific concrete,
/// so the slot cannot be one `E` and no provider describes the heterogeneous
/// pair — REFUSE, exactly like the distinct-rigids case. The unsound
/// alternative (a stored rigid yielding to the incoming concrete, WI-821 order
/// symmetry) bound `E := Pebble` and used Pebble's describe for BOTH
/// components: `CallerMixed.cm(leaf())` loaded clean and evaluated to 55
/// (Pebble.describe(leaf) = 5 → 5 + 10·5) instead of refusing.
#[test]
fn diagonal_mixed_rigid_concrete_refused() {
    let src = with_instances(
        "wi827.diag_mixed",
        &format!(
            r#"{DIAGONAL}
  sort CallerMixed
    sort CT = ?
    requires Desc[T = CT]
    operation cm(a: CT) -> Int64 = PHolder.ph(a, pebble())
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = CallerMixed.cm(leaf())
  end"#
        ),
    );
    let errs = load_errs(&src);
    let text = errs.join("\n");
    assert!(
        text.contains("wi827.diag_mixed.PHolder.ph")
            && text.contains("cannot be supplied"),
        "expected a load refusal of PHolder.ph's diagonal requirement at a \
         mixed rigid/concrete slot (sound: a rigid skolem is never a specific \
         concrete, so the yield to Pebble that measured 55 was unsound); got:\n{text}"
    );
}

// ── (c) COMPOUND element in the diagonal: component-wise ─────────────

/// (c): the diagonal's impl param `E` appears WRAPPED in one slot
/// (`fact Desc[T = Pair[A = Wrap[A = E], B = E]]`), so matching recurses into a
/// COMPOUND element before reaching the skolem. At the same rigid the
/// component-wise comparison confirms agreement and the dict constructs;
/// pre-fix the unrecorded interior left the sub-goal ambiguous. describe reads
/// `p.snd` (a `Pebble`): 5 + 7 = 12 — consistent with the bare-diagonal
/// spelling above (both construct correctly, where pre-fix both died).
#[test]
fn wrapped_diagonal_same_rigid_constructs() {
    let src = with_instances(
        "wi827.wdiag",
        r#"  sort Pair
    sort A = ?
    sort B = ?
    entity pair(fst: A, snd: B)
  end
  sort WPairDesc
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Pair[A = Wrap[A = E], B = E]]
    operation describe(p: Pair[A = Wrap[A = E], B = E]) -> Int64 =
      add(Desc.describe(p.snd), 7)
  end
  sort WPHolder
    sort PA = ?
    sort PB = ?
    requires Desc[T = Pair[A = Wrap[A = PA], B = PB]]
    operation ph(a: Wrap[A = PA], b: PB) -> Int64 = Desc.describe(pair(a, b))
  end
  sort CallerW
    sort CT = ?
    requires Desc[T = CT]
    operation call(a: Wrap[A = CT], b: CT) -> Int64 = WPHolder.ph(a, b)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = CallerW.call(wrap(pebble()), pebble())
  end"#,
    );
    let got = eval_fresh(&src, "wi827.wdiag.Driver.drive");
    assert!(
        matches!(got, Ok(Value::Int(12))),
        "expected Ok(Int(12)) = the compound-element diagonal recorded \
         component-wise and constructed (pre-fix the unrecorded interior left \
         the sub-goal Ambiguous); got {got:?}"
    );
}
