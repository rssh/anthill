//! WI-825 — the σ-gate's COMPOUND-element blindness (WI-821 /code-review
//! finding 1, CONFIRMED by driving), fixed.
//!
//! Background: `binding_pair_covers`' σ mode classified elements HEAD-only —
//! `is_type_param_value` tests only the head, so a compound element
//! (`Wrap[A = CT]`) classifies concrete, and two same-head compounds with
//! different interiors fell to `dispatch_values_match`, whose fallback
//! compares head sort symbols with the args IGNORED (`types_lesseq` rejects
//! the pair first, so the head fallback was the accepting leg; neither leg
//! consults σ). A caller entry `Desc[T = Wrap[A = CT]]` therefore COVERED a
//! callee dep σ-instantiated one constructor DEEPER
//! (`Desc[T = Wrap[A = Wrap[A = CT]]]`) and the shallower dict was forwarded
//! — the exact pre-WI-821 (d) signature one constructor level down.
//!
//! The fix (WI-825): under σ, a pair whose sides are BOTH parameterized
//! applications compares σ-STRUCTURALLY — same base sort AND each argument
//! pair recursively via the shared σ verdict (`sigma_pair_precise`:
//! σ-classes at param leaves,
//! `dispatch_values_match` at ground leaves). Mixed param/compound argument
//! pairs σ-disagree, so the deeper dep is no longer covered and Strategy 3
//! constructs the conditional instance around the caller's own dictionary —
//! whose sub-goal (`Desc[T = Wrap[A = CT]]` vs the caller's identical entry)
//! still covers σ-precisely through the same recursion.
//!
//! Depth coding (same `Desc`/`Leaf`/`Wrap`/`WrapDesc` block as the wi817
//! suite — own copy, per the suite's self-contained-file convention):
//! describe(wrapⁿ(leaf)) = 1, 12, 122, 1222 — a wrong
//! dictionary at any step produces a detectably different number. Pre-fix
//! measurements: single hand-off 12 (correct 122); recursion 12 at EVERY
//! depth (correct 12/122/1222).

use anthill_core::eval::Value;

/// Same instance block as the wi817 suite: spec `Desc`, base instance at
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

/// The hand-off CALLEE shared by the fixtures below: its requirement's
/// element is the COMPOUND `Wrap[A = DT]` over its own param, and its body
/// reads the requirement one wrap above its argument.
const DEEP_HOLDER: &str = r#"  sort DeepHolder
    sort DT = ?
    requires Desc[T = Wrap[A = DT]]
    operation d(y: DT) -> Int64 = Desc.describe(wrap(y))
  end"#;

/// THE DRIVEN DEFECT, single hand-off. Caller `requires Desc[T = Wrap[A =
/// CT]]` hands off to DeepHolder with `DT := Wrap[A = CT]`, so the dep
/// σ-instantiates to `Desc[T = Wrap[A = Wrap[A = CT]]]` — one constructor
/// DEEPER than the caller's entry. Pre-fix the head-only cover forwarded the
/// caller's shallower dict and drive measured 12; correct is 122 (the
/// conditional instance constructed around the caller's own dictionary).
#[test]
fn compound_single_handoff_constructs_deeper_dict() {
    let src = with_instances(
        "wi825.h1",
        &format!(
            r#"{DEEP_HOLDER}
  sort CHolder
    sort CT = ?
    requires Desc[T = Wrap[A = CT]]
    operation c(x: CT) -> Int64 = DeepHolder.d(wrap(x))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = CHolder.c(leaf())
  end"#
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi825.h1.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(122))),
        "expected Ok(Int(122)) = the callee dep constructed one level deeper \
         than the caller's compound entry (pre-fix head-only cover forwarded \
         the shallower dict and measured 12); got {got:?}"
    );
}

/// THE DRIVEN DEFECT, recursion. Mutual recursion whose entries are BOTH
/// compound (`Desc[T = Wrap[A = FT]]` / `Desc[T = Wrap[A = GT]]`): the f→g
/// leg keeps the σ-class (`GT := FT`, identical compounds — still covers
/// through the structural recursion, forwarding BY NAME), while the g→f leg
/// deepens (`FT := Wrap[A = GT]`) and must CONSTRUCT. Pre-fix the deepening
/// leg forwarded and drive measured 12 at EVERY depth; correct is the
/// depth-coded 12/122/1222.
#[test]
fn compound_recursion_depth_coded() {
    let src = with_instances(
        "wi825.rec",
        r#"  sort FHolder
    sort FT = ?
    requires Desc[T = Wrap[A = FT]]
    operation f(n: Int64, x: FT) -> Int64 =
      if eq(n, 0) then Desc.describe(wrap(x)) else GHolder.g(n, x)
  end
  sort GHolder
    sort GT = ?
    requires Desc[T = Wrap[A = GT]]
    operation g(n: Int64, y: GT) -> Int64 =
      FHolder.f(sub(n, 1), wrap(y))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = FHolder.f(n, leaf())
  end"#,
    );
    // One interpreter for all three depths: every call is asserted Ok, so
    // the trapped-call poisoning footgun does not apply.
    let mut interp = crate::common::interp_for(&src);
    for (n, correct) in [(0, 12), (1, 122), (2, 1222)] {
        let got = interp.call("wi825.rec.Driver.drive", &[Value::Int(n)]);
        assert!(
            matches!(got, Ok(Value::Int(v)) if v == correct),
            "drive({n}): expected the depth-coded Ok(Int({correct})) \
             (pre-fix the g→f hand-off forwarded the shallower compound \
             dict and measured 12 at every depth); got {got:?}"
        );
    }
}

/// POSITIVE CONTROL (passed pre-fix too): with NO covering entry in scope —
/// the driver calls DeepHolder directly — Strategy 3 constructs the depth-2
/// dictionary correctly (122). Pins that construction handles the compound
/// shape, so the defect above was the GATE letting the forward through, not
/// a construction gap.
#[test]
fn positive_control_no_cover_constructs_depth2() {
    let src = with_instances(
        "wi825.ctl",
        &format!(
            r#"{DEEP_HOLDER}
  sort Driver
    operation drive(n: Int64) -> Int64 = DeepHolder.d(wrap(leaf()))
  end"#
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi825.ctl.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(122))),
        "expected Ok(Int(122)) from cover-free construction (this worked \
         pre-fix too — the ticket's positive control); got {got:?}"
    );
}

/// The ticket's WATCH item: a concrete GROUND same-head compound pair
/// (`Wrap[A = Leaf]` vs `Wrap[A = Leaf]`) must still cover — the structural
/// recursion bottoms out in `dispatch_values_match`, whose `types_lesseq`
/// leg accepts identical grounds. Loads and evaluates to 12 (the value is
/// path-independent here; the pin is that the ground cover neither refuses
/// nor breaks the load).
#[test]
fn ground_compound_cover_still_serves() {
    let src = with_instances(
        "wi825.gnd",
        &format!(
            r#"{DEEP_HOLDER}
  sort GroundHolder
    requires Desc[T = Wrap[A = Leaf]]
    operation h(x: Leaf) -> Int64 = DeepHolder.d(x)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = GroundHolder.h(leaf())
  end"#
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi825.gnd.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(12))),
        "expected Ok(Int(12)) with the ground compound entry still covering; got {got:?}"
    );
}
