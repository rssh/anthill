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
///
/// WI-20261001-80ZV8 — AND THE REASON IS ABOUT THE GOAL, whichever way `Keyed` writes its
/// own provision. The fixture said `provides Rel[T = Keyed]` and the reason then read "the
/// provision of `Keyed` … does not bind its named slot `O` in its head — write `O = O`":
/// a repair in the wrong declaration, and one that made things worse, because with the
/// slot written — which is what `Self` lowers to — the candidate was dropped at the head
/// and the refusal became "nothing provides `Rel[T = Keyed[…]]`". `head` is `Keyed`'s own
/// carrier as its provision writes it; `user` is `User`'s body.
///
/// CONTROLS (MEASURED on a temporary binary over this file's six rows):
///  - drop arm (2)'s `forwards_own_named_slot` case in `match_candidate_against_goal`:
///    THREE fail — the refusal row on the provider not being named ("but nothing provides
///    …"), [`the_repairs_the_refusal_names_load`] on its closing check for the same reason,
///    and the constructor-less row below;
///  - classify the miss as `NotInHead` whatever the goal says (`carried_slot`): TWO fail —
///    the refusal row on the head being blamed, and the repairs row's closing check.
/// The repairs themselves load either way, by design: they are the control that the reason
/// names real repairs, and what a back-out breaks is the reason.
fn refused(head: &str, user: &str) -> String {
    format!(
        r#"
namespace wi4zzkz.refused
  import anthill.prelude.{{WeakOrd, Int64}}
  sort Rel
    sort T = ?
  end
  enum Keyed
    sort T = ?
    requires O: WeakOrd[T]
    entity k(v: T)
    provides Rel[T = {head}]
  end
  sort Top
    sort T = ?
    requires Rel[T = T]
  end
  sort User
{user}
  end
end
"#
    )
}

/// `Self`, and what it lowers to written out: one provision, so one refusal.
const WRITTEN_HEADS: [&str; 2] = ["Self", "Keyed[T = T, O = O]"];

#[test]
fn a_provider_that_refuses_the_goal_is_named_with_its_reason() {
    for head in WRITTEN_HEADS {
        let errs = load_errs(&refused(
            head,
            "    sort E = ?\n    provides Top[T = Keyed[T = E]]",
        ));
        let refusal = errs
            .iter()
            .find(|e| e.contains("'wi4zzkz.refused.User' provides 'wi4zzkz.refused.Top'"))
            .unwrap_or_else(|| panic!("`{head}`: `User`'s provision is refused: {errs:?}"));
        assert!(
            refusal.contains("its provider `wi4zzkz.refused.Keyed` cannot answer it here")
                && refusal
                    .contains("does not write named slot `O` of `wi4zzkz.refused.Keyed`"),
            "`{head}`: …naming the provider and the slot the goal's `Keyed[…]` leaves out: \
             {refusal}",
        );
        assert!(
            !refusal.contains("in its head"),
            "`{head}`: `Keyed`'s head binds `O` — it is `User`'s `Keyed[T = E]` that does \
             not: {refusal}",
        );
        assert!(
            !refusal.contains("does not provide 'wi4zzkz.refused.Rel'")
                && !refusal.contains("nothing provides"),
            "`{head}`: `Keyed` provides `Rel`: {refusal}",
        );
    }
}

/// What the refusal above tells the author to do — write `O` in `User`'s `Keyed[…]`: a
/// named slot `User` declares, or, where the element is concrete, a witness — loads.
#[test]
fn the_repairs_the_refusal_names_load() {
    for head in WRITTEN_HEADS {
        for user in [
            "    sort E = ?\n    requires OE: WeakOrd[E]\n    \
             provides Top[T = Keyed[T = E, O = OE]]",
            "    provides Top[T = Keyed[T = Int64, O = Int64]]",
        ] {
            crate::common::expect_loaded(crate::common::try_load_kb_with(&refused(head, user)));
        }
        // …and the witness is what that second program needed: without it, the same
        // refusal.
        let errs = load_errs(&refused(head, "    provides Top[T = Keyed[T = Int64]]"));
        assert!(
            errs.iter().any(|e| e.contains("does not write named slot `O`")),
            "`{head}`: a concrete element changes nothing about the slot: {errs:?}",
        );
    }
}

/// A CARRIER WITH NO CONSTRUCTOR has no value that chose the slot, so its unwritten slot is
/// SEARCHED — and that too is one answer for both spellings of the carrier's provision.
/// `Keyed[T = Int64]` loads (`WeakOrd[Int64]` holds); `Keyed[T = Float]` is refused naming
/// the goal beneath the chosen provider, not the provider's absence.
///
/// CONTROL (MEASURED): drop arm (2)'s `forwards_own_named_slot` case and both rows fail —
/// `Int64` is refused "nothing provides `Rel[T = Keyed[T = Int64]]`", and `Float` with it.
///
/// The row first held the bare head `provides Rel[T = Keyed]` beside `Self`, to show that the
/// two agreed; since proposal 070 the bare head is another type — `Keyed` at `?`, any
/// instance — and the head written out is what stands beside `Self` now.
fn constructorless(head: &str, element: &str) -> String {
    format!(
        r#"
namespace wi4zzkz.searched
  import anthill.prelude.{{WeakOrd, Int64, Float}}
  sort Rel
    sort T = ?
  end
  sort Keyed
    sort T = ?
    requires O: WeakOrd[T]
    provides Rel[T = {head}]
  end
  sort Top
    sort T = ?
    requires Rel[T = T]
  end
  sort User
    provides Top[T = Keyed[T = {element}]]
  end
end
"#
    )
}

#[test]
fn a_constructorless_carriers_unwritten_slot_is_searched_under_either_spelling() {
    for head in WRITTEN_HEADS {
        crate::common::expect_loaded(crate::common::try_load_kb_with(&constructorless(
            head, "Int64",
        )));
        let errs = load_errs(&constructorless(head, "Float"));
        assert!(
            errs.iter().any(|e| e.contains("its provider `wi4zzkz.searched.Keyed` was chosen")
                && e.contains("`anthill.prelude.WeakOrd[T = anthill.prelude.Float]` beneath it")),
            "`provides Rel[T = {head}]`: `Float` has no ordering, and the refusal names the \
             goal beneath `Keyed`: {errs:?}",
        );
    }
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
