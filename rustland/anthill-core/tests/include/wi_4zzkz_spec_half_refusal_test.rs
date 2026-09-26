//! WI-20260925-4ZZKZ — a SPEC-HALF slot that does not resolve is refused, not recorded.
//!
//! The ticket moved WI-857's recorded absence out of the load: `resolve_inner` fails a
//! spec-half sub-goal as it fails a provider-half one, `check_provider_requires` resolves
//! every goal (its base-level fallback is gone), and the tree type has no absence node.
//! The fixture rewrites that move forced are in `wi857` / `wi865` / `wi868`; this file pins
//! what the move itself needed, each found by /code-review of the first cut:
//!
//!  1. the use-site scope answers a sub-goal through a requirement's chain TO ANY DEPTH —
//!     a spec half is no longer tolerated, so one hop refused a generic body the load
//!     check (whose assumptions are closed under `requires`) had admitted;
//!  2. a failure in the SPEC half of the carrier's own provision is not blamed on this
//!     provision's conditions (`ProvisionConditionsTooWeak`);
//!  3. a provider that REFUSES the goal is named with the resolver's reason, not reported
//!     as "does not provide".

use anthill_core::eval::value::Value;

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

// ── 1. a requirement's chain, followed to any depth ─────────────────────────

/// `Holder requires Ord[A]` and compares two `Pair[A, A]`. The dictionary for
/// `WeakOrd[Pair[A, A]]` has a spec half — `Eq[Pair[A, A]]`, `PartialOrd[Pair[A, A]]` —
/// whose conditions ask `Eq[A]` and `PartialOrd[A]`, which the body holds TWO hops into
/// its `Ord` slot (`Ord` → `WeakOrd` → `Eq`). The load check reaches them the same way
/// (`closed_under_requires`); the use site stopped at one hop and refused a program that
/// loaded and ran at the parent commit.
///
/// CONTROL (MEASURED): stop `scope_chain_cover` after the first hop and this fails at load
/// with `unresolved: anthill.prelude.Eq[…]`.
const TWO_HOP: &str = r#"
namespace wi4zzkz.twohop
  import anthill.prelude.{Ord, WeakOrd, Int64, Pair}
  import anthill.prelude.Pair.{pair}
  sort Holder
    sort A = ?
    requires Ord[A]
    operation cmp2(x: Pair[A = A, B = A], y: Pair[A = A, B = A]) -> Int64 = WeakOrd.compare(x, y)
  end
  sort Driver
    operation lt(n: Int64) -> Int64 = Holder.cmp2(pair(1, 2), pair(1, 3))
    operation gt(n: Int64) -> Int64 = Holder.cmp2(pair(1, 3), pair(1, 2))
  end
end
"#;

#[test]
fn a_spec_half_is_answered_two_hops_into_a_requirement() {
    for (entry, want) in [("lt", -1), ("gt", 1)] {
        let mut interp = crate::common::interp_for(TWO_HOP);
        match interp.call(&format!("wi4zzkz.twohop.Driver.{entry}"), &[Value::Int(0)]) {
            Ok(Value::Int(n)) => assert_eq!(n, want, "`{entry}` compares lexicographically"),
            other => panic!("`{entry}` must answer {want}; got {other:?}"),
        }
    }
}

// ── 2. the carrier's own provision, failing in its SPEC half ────────────────

/// `C provides S`, and `S requires R`: the resolver chooses `C`'s own `R` provision, whose
/// SPEC half (`R requires Q`) has no provider. That is `C`'s `R` provision breaking its
/// own contract — reported where it is, as the first refusal — and not a condition of
/// `S`'s provision too weak to entail it: `C`'s `R` has no condition at all.
///
/// CONTROL (MEASURED): classify from a scan of the provider half with the innermost goal
/// as the fallback (P5G39's re-derivation) and the second refusal becomes a
/// `ProvisionConditionsTooWeak` advising to strengthen `provides S[…] :- …`.
const OWN_SPEC_HALF: &str = r#"
namespace wi4zzkz.ownspec
  sort Q
    sort T = ?
  end
  sort R
    sort T = ?
    requires Q[T = T]
  end
  sort S
    sort T = ?
    requires R[T = T]
  end
  enum C
    entity c
    provides R[T = C]
    provides S[T = C]
  end
end
"#;

#[test]
fn a_spec_half_failure_under_the_carriers_own_provision_is_not_too_weak() {
    let errs = load_errs(OWN_SPEC_HALF);
    assert!(
        errs.iter().any(|e| e.contains(
            "'wi4zzkz.ownspec.C' provides 'wi4zzkz.ownspec.R', which requires \
             'wi4zzkz.ownspec.Q', but 'wi4zzkz.ownspec.C' does not provide"
        )),
        "the defect itself is reported where it is: {errs:?}",
    );
    assert!(
        !errs.iter().any(|e| e.contains("DOES provide") || e.contains("Strengthen")),
        "`C`'s `R` provision has no condition, so no condition of `S`'s can be too weak \
         for it: {errs:?}",
    );
}

// ── 3. a provider that refuses the goal ─────────────────────────────────────

/// `Keyed` provides `Rel` and declares a NAMED slot `O`, and `User`'s provision reaches
/// it as `Keyed[T = E]` with `O` unwritten — so the chosen provider cannot serve the goal,
/// and the resolver says why. It loaded at the parent commit through the load check's
/// base-level fallback; the refusal must carry that reason, not "does not provide `Rel`"
/// (`Keyed` does).
///
/// CONTROL (MEASURED): map every unforwarded `NoMatch` to `RequirementFailure::NoProvider`
/// and this row fails on the missing reason.
const REFUSED: &str = r#"
namespace wi4zzkz.refused
  import anthill.prelude.{WeakOrd, Int64}
  sort Rel
    sort T = ?
  end
  enum Keyed
    sort T = ?
    requires O: WeakOrd[T]
    entity k(v: T)
    provides Rel[T = Keyed]
  end
  sort Top
    sort T = ?
    requires Rel[T = T]
  end
  sort User
    sort E = ?
    provides Top[T = Keyed[T = E]]
  end
end
"#;

#[test]
fn a_provider_that_refuses_the_goal_is_named_with_its_reason() {
    let errs = load_errs(REFUSED);
    let refusal = errs
        .iter()
        .find(|e| e.contains("'wi4zzkz.refused.User' provides 'wi4zzkz.refused.Top'"))
        .unwrap_or_else(|| panic!("`User`'s provision is refused: {errs:?}"));
    assert!(
        refusal.contains("its provider `wi4zzkz.refused.Keyed` cannot answer it here")
            && refusal.contains("named slot `O`"),
        "…naming the provider and the slot it cannot answer: {refusal}",
    );
    assert!(
        !refusal.contains("does not provide 'wi4zzkz.refused.Rel'"),
        "`Keyed` provides `Rel`: {refusal}",
    );
}

// ── 4. a requirement left open by the provision itself ──────────────────────

/// `Bag provides Container[C = Bag]` leaves `Elem` unwritten, so `Container requires
/// Eq[T = Elem]` becomes `Eq[T = Container.Elem]` — a requirement at EVERY `Elem`. It
/// loaded through the load check's base-level fallback; refused now, the refusal must say
/// that the provision left the parameter open, not that `Bag` lacks `Eq`.
///
/// CONTROL (MEASURED): drop the `Unwritten` classification and this row fails — the
/// refusal then reads "nothing provides `Eq[T = Container.Elem]`", which sends the author
/// to add a provider for a goal the provision itself left open.
const UNWRITTEN: &str = r#"
namespace wi4zzkz.unwritten
  import anthill.prelude.{Eq, PartialEq, Bool}
  sort Container
    sort C = ?
    sort Elem = ?
    requires Eq[T = Elem]
  end
  enum Bag
    entity b
    provides Container[C = Bag]
  end
end
"#;

#[test]
fn a_parameter_the_provision_leaves_unwritten_is_named() {
    let errs = load_errs(UNWRITTEN);
    let refusal = errs
        .iter()
        .find(|e| e.contains("'wi4zzkz.unwritten.Bag' provides 'wi4zzkz.unwritten.Container'"))
        .unwrap_or_else(|| panic!("`Bag`'s provision is refused: {errs:?}"));
    assert!(
        refusal.contains("names `wi4zzkz.unwritten.Container.Elem`")
            && refusal.contains("does not write"),
        "the refusal names the unwritten parameter: {refusal}",
    );
    assert!(
        !refusal.contains("does not provide"),
        "…and does not blame `Bag`: {refusal}",
    );
}
