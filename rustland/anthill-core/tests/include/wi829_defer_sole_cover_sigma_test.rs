//! WI-829 — the direct-dispatch DEFER path's SOLE-cover arm did not σ-gate a
//! COMPOUND element (WI-825 /code-review, max effort, CONFIRMED by driving).
//!
//! Background: WI-825 made the FORWARDING path (`build_dep_projection`) compound-
//! aware, but the CLASSIFICATION path — `find_requires_location` /
//! `find_requires_slot` — returned a SOLE coarse cover unchecked: its sole-cover
//! arm (`[(only, _)] => Some(..)`) never consulted σ (σ was tie-break-only via
//! `pick_precise`), and the dispatch trigger `dispatch_spec_op_cached` passed
//! `sigma = None`. `entry_matches_subst` coarse-accepts a shallow-vs-deep compound
//! pair through `dispatch_values_match`'s head fallback (`Wrap == Wrap`, interiors
//! ignored), so `DeferToRequirement` read the frame's WRONG-depth dictionary.
//!
//! The fix (WI-829): a σ-refuting cover is dropped when σ is present and the
//! entry's compound element σ-DISAGREES with the per-call value
//! (`entry_sigma_verdict` → `SigmaVerdict::Refutes`, sharing WI-825's
//! `sigma_pair_precise` verdict), and `dispatch_spec_op_cached`
//! threads the call-site σ into its defer trigger so the refusal reaches
//! construction. The classification then constructs the deeper dictionary around
//! the frame's own requirement (the WrapDesc conditional instance with a FromScope
//! sub-goal) exactly as the cover-free positive control already did.
//!
//! Depth coding (same `Desc`/`Leaf`/`Wrap`/`WrapDesc` block as the wi817/wi825
//! suites; the copies MUST stay in sync — lifting the block into `tests/common`
//! is tracked under WI-829's residuals):
//! describe(wrapⁿ(leaf)) = 1, 12, 122, 1222 — a wrong dictionary at any step
//! produces a detectably different number.

use anthill_core::eval::Value;

/// Same instance block as the wi817/wi825 suites: spec `Desc`, base instance at
/// `Leaf` (describe → 1), CONDITIONAL instance at `Wrap[E]` given `Desc[E]`
/// (describe → 10·describe(inner) + 2).
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
  import anthill.prelude.{{Int64, Bool}}
{INSTANCES}
{body}
end
"#
    )
}

/// THE DRIVEN DEFECT (WI-825 /code-review repro). `DHolder2 requires
/// Desc[T = Wrap[A = HT]]`, but its body reads the requirement one wrap DEEPER
/// than the entry (`Desc.describe(wrap(wrap(y)))`, y : HT) — the per-call element
/// is `Wrap[A = Wrap[A = HT]]`, one constructor deeper than the entry's
/// `Wrap[A = HT]`. Pre-fix the sole coarse cover forwarded the frame's shallower
/// dict and drive measured 12; correct is 122 (the deeper dict constructed around
/// the frame's own requirement).
#[test]
fn direct_dispatch_sole_cover_constructs_deeper_dict() {
    let src = with_instances(
        "wi829.d2",
        r#"  sort DHolder2
    sort HT = ?
    requires Desc[T = Wrap[A = HT]]
    operation d2(y: HT) -> Int64 = Desc.describe(wrap(wrap(y)))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = DHolder2.d2(leaf())
  end"#,
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi829.d2.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(122))),
        "expected Ok(Int(122)) = the deeper dict constructed around the frame's \
         own compound requirement (pre-fix the sole coarse cover forwarded the \
         shallower dict and measured 12); got {got:?}"
    );
}

/// CONTROL: an EXACT-depth sole cover must still DEFER. `SHolder requires
/// Desc[T = Wrap[A = ST]]` and its body reads the requirement at exactly that
/// depth (`Desc.describe(wrap(y))`, y : ST → `Wrap[A = ST]`), so the sole cover
/// σ-AGREES and the frame dict is read directly. Evaluates to 12 (the frame dict
/// for `Wrap[A = Leaf]` computed by the driver). Pins that the σ-gate refuses ONLY
/// a disagreeing cover, not every compound one.
#[test]
fn exact_depth_sole_cover_still_defers() {
    let src = with_instances(
        "wi829.exact",
        r#"  sort SHolder
    sort ST = ?
    requires Desc[T = Wrap[A = ST]]
    operation s(y: ST) -> Int64 = Desc.describe(wrap(y))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = SHolder.s(leaf())
  end"#,
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi829.exact.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(12))),
        "expected Ok(Int(12)) from the exact-depth sole cover still deferring; got {got:?}"
    );
}

/// CONTROL: a plain SCALAR sole cover must still DEFER. `EHolder requires
/// Desc[T = ET]` reads `Desc.describe(y)` at exactly the element — the entry's
/// element is the bare param `ET`, the per-call value is the same param, so the
/// sole cover σ-AGREES (both type-params, same σ-class) and defers. Evaluates to
/// 1 (the Leaf dict the driver supplies). Pins the gate does not over-refuse a
/// bare-param cover.
#[test]
fn scalar_param_sole_cover_still_defers() {
    let src = with_instances(
        "wi829.scalar",
        r#"  sort EHolder
    sort ET = ?
    requires Desc[T = ET]
    operation e(y: ET) -> Int64 = Desc.describe(y)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = EHolder.e(leaf())
  end"#,
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi829.scalar.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(1))),
        "expected Ok(Int(1)) from the scalar-param sole cover still deferring; got {got:?}"
    );
}

/// RECURSION variant: the deepening happens inside the SAME sort's body, driven
/// two levels down. `RHolder requires Desc[T = Wrap[A = RT]]` reads the
/// requirement TWO wraps deeper (`Desc.describe(wrap(wrap(wrap(y))))`), so the
/// sole cover σ-disagrees by two constructors and the depth-3 dict is
/// constructed. Correct is 1222.
#[test]
fn direct_dispatch_sole_cover_constructs_depth3() {
    let src = with_instances(
        "wi829.d3",
        r#"  sort RHolder
    sort RT = ?
    requires Desc[T = Wrap[A = RT]]
    operation r(y: RT) -> Int64 = Desc.describe(wrap(wrap(wrap(y))))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = RHolder.r(leaf())
  end"#,
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi829.d3.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(1222))),
        "expected Ok(Int(1222)) = the depth-3 dict constructed around the frame's \
         Wrap[A = RT] requirement; got {got:?}"
    );
}
