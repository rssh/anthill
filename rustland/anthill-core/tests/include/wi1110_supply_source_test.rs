//! WI-1110 — a chain entry carries a SUPPLY SOURCE, and a spec's `provides` is a
//! conversion rather than a provider row.
//!
//! WHAT THE TICKET IS. `requires A[T]` says the `A` dictionary is PASSED IN; a spec's
//! `provides A[T]` says it is BUILT FROM SELF. Both are chain entries and differ only in
//! where the dictionary comes from. WI-1109 filed the second one in the PROVIDER TABLE
//! instead — the searchable relation recording what has which type — and every symptom
//! followed from that one misfiling: `Ord` was offered as a candidate answer to every
//! `WeakOrd` goal, `Ord` then needed `requires WeakOrd` as well to get a dictionary at
//! all, the pair closed a cycle, and `Eq` could not forward to `PartialEq` in either
//! spelling.
//!
//! WHY IT NEEDS AN INSTRUMENTED TEST. The headline defect is INVISIBLE from outside:
//! the spurious candidate was rejected by cycle detection, so the load verdict, the
//! resolved tree and the error text were identical with and without it. The only place
//! the difference exists is the candidate list, which is why
//! `dispatch_candidate_impl_sorts` exists and why `a_weakord_goal_offers_only_carriers`
//! reads it.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT — MEASURED, listed per backout,
//! because the change has three separable halves and they do not fail together:
//!
//!   * remove the `provision_is_conversion` skip in `collect_provides_candidates`
//!     (kb/typing.rs) — 1876 of 2858 fail, the stdlib itself among them, with
//!     `construction is cyclic: PartialEq[X] -> PartialEq[X]` (12545 occurrences). This
//!     CORRECTS a first draft of this note, which predicted that only the two candidate
//!     tests would fail "because the spurious candidate is rejected by cycle detection
//!     anyway". That was true of WI-1109's stdlib and is FALSE of this one: once `Eq`
//!     forwards to `PartialEq`, the skip is what stops `Eq` joining the providers of the
//!     floor it requires nothing of, and there is no `requires` left to be rejected
//!     against — the cycle is the load.
//!
//!     The ORDERING half of the same claim does hold, and it is why the instrument
//!     exists: with the skip removed AND `Eq` restored to `requires PartialEq`, six
//!     tests fail — five of them (`an_ord_carrier_that_pays_loads_and_runs`,
//!     `provides_eq_carries_partialeq`, two wi224 fixtures, wi869's float pair) because
//!     of the `Eq` revert, and `a_weakord_goal_offers_only_carriers` because of the
//!     skip. It is the ONLY reader of that difference in the workspace; `Ord` is back as
//!     a candidate for every `WeakOrd` goal and nothing else notices.
//!   * remove `self_supplied_entries` from `direct_requires` (kb/typing.rs) — 1863 of
//!     2858 fail and the stdlib does not load at all: `TypeMismatch … missing `requires
//!     PartialEq[T = …]` on enclosing sort`. With the conversion contributing no chain
//!     entry, `Eq` and `Ord` have no chain, so nothing carries the requirement they
//!     forward.
//!   * remove the `Item::ProvidesClause` arm from sub-pass 2 (kb/load.rs) — 46 fail,
//!     both naming tests here among them, with `unresolved import
//!     'anthill.prelude.Ord.gte'` (39 sites), `'anthill.prelude.Eq.eq'` (25),
//!     `'…Ord.lt'` (10), `'…Ord.gt'` (8). Chain and scope are separate wirings and this
//!     is the one that is only a name.
//!
//! WHICH PASS EITHER WAY, BY DESIGN: `a_carrier_that_provides_a_spec_is_still_a_
//! candidate` and `a_parametric_witness_is_still_a_candidate` are the CONTROLS on the
//! skip — they measure that it discriminates rather than emptying the search space, and
//! a build with no skip at all passes them too. That is what they are for.

use anthill_core::eval::Value;
use anthill_core::kb::typing::{dispatch_candidate_impl_sorts, SortGoal};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// The candidate impl sorts offered for `<spec>[T = <carrier>]`, by qualified name.
fn candidates_at(kb: &mut KnowledgeBase, spec_qn: &str, carrier_qn: &str) -> Vec<String> {
    let spec = kb
        .try_resolve_symbol(spec_qn)
        .unwrap_or_else(|| panic!("{spec_qn} registered"));
    let carrier = kb
        .try_resolve_symbol(carrier_qn)
        .unwrap_or_else(|| panic!("{carrier_qn} registered"));
    let carrier_ref = kb.alloc(anthill_core::kb::term::Term::Ref(carrier));
    let t = kb.intern("T");
    let goal = SortGoal {
        spec_sort: spec,
        bindings: SmallVec::from_slice(&[(t, carrier_ref)]),
        carrier: None,
    };
    dispatch_candidate_impl_sorts(kb, &goal)
        .into_iter()
        .map(|s| kb.qualified_name_of(s).to_string())
        .collect()
}

fn stdlib_kb() -> KnowledgeBase {
    crate::common::load_kb_with("namespace wi1110.probe\n  import anthill.prelude.{Int64}\nend\n")
}

// ── the defect: a conversion offered as a provider ───────────────────────────

/// THE TICKET'S HEADLINE, instrumented. `Ord provides WeakOrd[T = T]` is a conversion:
/// nothing has type `Ord`, so it can never answer "who provides `WeakOrd` at `Int64`".
/// Before WI-1110 this list was `["anthill.prelude.Ord", "anthill.prelude.Int64"]` and
/// the extra entry was eliminated only by cycle detection running and failing — on every
/// ordering goal in every program.
#[test]
fn a_weakord_goal_offers_only_carriers() {
    let mut kb = stdlib_kb();
    let cands = candidates_at(
        &mut kb,
        "anthill.prelude.WeakOrd",
        "anthill.prelude.Int64",
    );
    assert!(
        !cands.iter().any(|c| c == "anthill.prelude.Ord"),
        "`Ord` is a spec — a conversion, not a carrier — and must not be offered as a \
         provider of `WeakOrd`; got {cands:?}"
    );
    assert!(
        cands.iter().any(|c| c == "anthill.prelude.Int64"),
        "and the real carrier must still be there, or the skip has emptied the search \
         space instead of cleaning it; got {cands:?}"
    );
}

/// The same on the equality tower, which WI-1110 lets forward for the first time.
#[test]
fn an_eq_goal_offers_only_carriers() {
    let mut kb = stdlib_kb();
    let cands = candidates_at(
        &mut kb,
        "anthill.prelude.PartialEq",
        "anthill.prelude.Int64",
    );
    assert!(
        !cands.iter().any(|c| c == "anthill.prelude.Eq"),
        "`Eq provides PartialEq[T = T]` is a conversion; offering `Eq` here is what made \
         the equality tower cycle in 1867 tests under WI-1109's filing; got {cands:?}"
    );
    assert!(
        cands.iter().any(|c| c == "anthill.prelude.Int64"),
        "the real carrier must still answer; got {cands:?}"
    );
}

// ── the controls: what the skip must NOT remove ──────────────────────────────

/// CONTROL. A CARRIER's `provides` is a fact about the world and stays in the search
/// space. `Int64 provides Ord[T = Int64]` binds the target's carrier parameter to a
/// concrete sort, which is the membership claim, not a conversion.
#[test]
fn a_carrier_that_provides_a_spec_is_still_a_candidate() {
    let mut kb = stdlib_kb();
    let cands = candidates_at(&mut kb, "anthill.prelude.Ord", "anthill.prelude.Int64");
    assert!(
        cands.iter().any(|c| c == "anthill.prelude.Int64"),
        "`Int64 provides Ord[T = Int64]` must remain a candidate; got {cands:?}"
    );
}

/// CONTROL, and the one that caught the first cut of the predicate. A PARAMETRIC WITNESS
/// has the conversion's SHAPE — it binds the target's carrier parameter to its own type
/// parameter — and is not a conversion, because it carries the operations itself. With
/// the shape test alone this sort's own `Monoid` slot resolved by search back to itself
/// and three wi841 tests failed with `construction is cyclic`.
#[test]
fn a_parametric_witness_is_still_a_candidate() {
    let src = r#"
namespace wi1110.witness
  import anthill.prelude.{Int64}
  sort Monoid
    sort T = ?
    operation combine(a: T, b: T) -> Int64
  end
  sort AnyM
    sort E = ?
    provides Monoid[T = E]
    operation combine(a: E, b: E) -> Int64 = 99
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let cands = candidates_at(&mut kb, "wi1110.witness.Monoid", "anthill.prelude.Int64");
    assert!(
        cands.iter().any(|c| c == "wi1110.witness.AnyM"),
        "`AnyM` carries `combine`, so it IS a Monoid dictionary and must stay a \
         candidate however abstractly its provision is written; got {cands:?}"
    );
}

/// CONTROL, and the one this file was MISSING — which is how the per-row reading came to
/// be reported as applied while the tree still had the per-pair one. A sort may write a
/// CONVERSION and a concrete MEMBERSHIP claim for the same spec. Only the first is a
/// conversion; the second is a real answer to a real goal, and asking the question per
/// `(subject, target)` PAIR instead of per ROW drops both.
///
/// THE TARGET IS A MARKER SPEC — no operations — AND THAT IS WHAT MAKES THE SHAPE
/// REACHABLE. A first fixture gave `High` a member of the target's surface so its
/// concrete row would have something to back, and that member made `High` a parametric
/// WITNESS rather than a conversion (`supplies_any_operation_of`), so the fixture passed
/// with the per-pair reading too and measured nothing. For a spec WITH operations the two
/// readings cannot differ: a subject supplying none of them is no provider at any
/// binding. For a marker — which `anthill.prelude.Ord` is, exactly — a subject can
/// legitimately both forward it and claim it at a concrete carrier.
#[test]
fn a_conversion_does_not_hide_a_sibling_concrete_row() {
    let src = r#"
namespace wi1110.sibling
  import anthill.prelude.{Int64}
  sort Mark
    sort T = ?
  end
  enum Tok
    entity tok(v: Int64)
  end
  sort High
    sort T = ?
    provides Mark[T = T]
    provides Mark[T = Tok]
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let cands = candidates_at(&mut kb, "wi1110.sibling.Mark", "wi1110.sibling.Tok");
    assert!(
        cands.iter().any(|c| c == "wi1110.sibling.High"),
        "`High provides Mark[T = Tok]` is a MEMBERSHIP claim at a concrete carrier and \
         must still answer `Mark[Tok]`, even though `High` also writes the conversion \
         `provides Mark[T = T]`; got {cands:?}"
    );
}

/// THE VACUITY GUARD, and it is what the whole exclusion rests on. A body dispatching a
/// spec op at an ABSTRACT element with no `requires` in scope must be REFUSED — there is
/// no dictionary for it and nothing can supply one. It is listed as this ticket's own
/// acceptance because the `Eq` experiment showed how it fails: a universal provider row
/// (`Eq` offered for every `PartialEq` goal) makes the goal resolve and the refusal
/// disappear, so the program loads and dies at eval instead. WI-1109 measured that
/// vacuity on the equality tower; excluding conversions is what keeps it from happening
/// on either.
#[test]
fn a_weakord_dispatch_with_no_requires_is_refused() {
    let src = r#"
namespace wi1110.novac
  import anthill.prelude.{WeakOrd, Int64}
  sort Holder
    sort T = ?
    operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.WeakOrd")),
        "an abstract `WeakOrd.compare` with no requirement in scope must be refused, not \
         answered by a conversion that can supply nothing; got {errs:?}"
    );
}

/// THE CONTROL for the arm above — the SAME body with the requirement declared loads and
/// runs. Without it the assertion measures nothing: a build that refused every spec-op
/// dispatch would pass it.
#[test]
fn the_same_weakord_dispatch_with_a_requires_runs() {
    let src = r#"
namespace wi1110.vaccontrol
  import anthill.prelude.{WeakOrd, Int64}
  sort Holder
    sort T = ?
    requires WeakOrd[T]
    operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end
  sort D
    operation go(n: Int64) -> Int64 = Holder.cmp(9, 4)
  end
end
"#;
    assert!(
        eval_int(src, "wi1110.vaccontrol.D.go") > 0,
        "with `requires WeakOrd[T]` the same body must resolve and answer: 9 vs 4"
    );
}

/// THE TICKET'S ORIGINAL FIXTURE, and the message it was filed about. A carrier with the
/// partial-order floor but NO `compare` and no `provides WeakOrd` used to report
/// `construction is cyclic: WeakOrd[T = Half] -> WeakOrd[T = Half]` — because `Ord` was
/// offered as a provider of `WeakOrd` and `Ord requires WeakOrd` closed the loop over it.
/// The truthful answer is that nothing provides `WeakOrd` here, and that is what a
/// conversion being out of the search space buys.
///
/// THE CARRIER IS REACHED THROUGH AN ABSTRACT HOLDER, and it has to be. THREE shapes were
/// probed and they get three different answers:
///
///   A. a DIRECT `WeakOrd.compare(Half.half(9), …)` from a sort with no `requires`
///      — LOADS CLEAN, and not because of anything this ticket did. It is the mask
///      `ordered.anthill` documents at its op-scoped `requires WeakOrd[T]`:
///      `check_one_spec_op_requirement` returns early for a builtin functor, so the
///      CALL-SITE half of a spec-op requirement is unchecked while the op is still a
///      resolver builtin (WI-876 measured the same for `PartialOrd.gt`; WI-879 is where
///      it comes due). A fixture in this shape measures the mask, not the ticket.
///   B. an abstract `T` with `requires PartialOrd[T]` only — refused with `missing
///      `requires WeakOrd[T = …]` on enclosing sort`. Truthful, and it is what
///      `a_weakord_dispatch_with_no_requires_is_refused` pins.
///   C. below — the concrete carrier reaching the goal through a holder that DOES declare
///      the requirement, so the requirement is checked and the carrier is asked for it.
#[test]
fn a_carrier_with_no_compare_is_told_nothing_provides_weakord() {
    let src = r#"
namespace wi1110.nocmp
  import anthill.prelude.{WeakOrd, PartialOrd, Int64}
  enum Half
    entity half(v: Int64)
    provides PartialOrd[T = Half]
  end
  sort Holder
    sort T = ?
    requires WeakOrd[T]
    operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)
  end
  sort D
    operation go(n: Int64) -> Int64 = Holder.cmp(Half.half(9), Half.half(4))
  end
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("no impl provides anthill.prelude.WeakOrd")),
        "the refusal must say nothing provides `WeakOrd`, not report a cycle through a \
         spec that provides nothing; got {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("construction is cyclic")),
        "and it must not be a cycle at all — that was the wart this ticket was filed \
         about; got {errs:?}"
    );
}

// ── the naming half ──────────────────────────────────────────────────────────

/// A CONVERSION LENDS ITS NAMES, exactly as `requires` does — because both put a
/// dictionary in the sort's hands. `Ord`'s whole content is `provides WeakOrd[T = T]`,
/// and `gte` lives two floors down on `PartialOrd`, so this drives the scope link AND
/// its transitivity in one goal. Without the sub-pass-2 arm the load fails with
/// `unresolved import 'anthill.prelude.Ord.gte'`.
#[test]
fn a_converted_spec_lends_its_names() {
    let src = r#"
namespace wi1110.naming
  import anthill.prelude.Ord.{gte}
  import anthill.prelude.{Ord, WeakOrd, Bool, Int64}
  sort Holder
    sort T = ?
    requires Ord[T]
    operation atLeast(a: T, b: T) -> Bool = gte(a, b)
  end
  sort D
    operation go(n: Int64) -> Bool = Holder.atLeast(7, 3)
  end
end
"#;
    assert!(
        eval_bool(src, "wi1110.naming.D.go"),
        "`gte` must resolve through `Ord provides WeakOrd` -> `WeakOrd requires \
         PartialOrd` and answer for the carrier's own order: 7 >= 3"
    );
}

/// AND THE SAME NAME ON THE EQUALITY TOWER. `Eq.eq` is the inherited `PartialEq.eq`
/// (proposal 004 kept it resolving for source compatibility), and WI-1109 measured that
/// switching `requires` to `provides` broke it in 32 places. It does not break here:
/// that measurement was of the misfiling, not of the clause.
#[test]
fn a_converted_eq_still_names_eq() {
    let src = r#"
namespace wi1110.eqname
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.{Eq, Bool, Int64}
  sort Holder
    sort T = ?
    requires Eq[T]
    operation same(a: T, b: T) -> Bool = eq(a, b)
  end
  sort D
    operation go(n: Int64) -> Bool = Holder.same(7, 7)
  end
end
"#;
    assert!(
        eval_bool(src, "wi1110.eqname.D.go"),
        "`import anthill.prelude.Eq.{{eq}}` must still resolve, and the call must answer"
    );
}

// ── the obligation is relocated, not waived ──────────────────────────────────

/// `Ord` no longer writes `requires Eq[T]` / `requires PartialOrd[T]` — WI-1110 deleted
/// both, on the argument that `WeakOrd`'s own requirements reach the carrier THROUGH the
/// conversion. THIS IS THAT ARGUMENT, DRIVEN: a carrier that provides `Ord` and nothing
/// else is still refused for what it owes two floors down.
///
/// IT NAMES `PartialOrd`, NOT `Eq`, AND THAT WAS MEASURED RATHER THAN CHOSEN. `Half` is
/// a TOTAL COMPOSITE — one entity over `Int64` — so `eq_derive` has already asserted
/// `provides PartialEq` and `provides Eq` for it (WI-664). Its `Eq` obligation is
/// therefore already paid, and `PartialOrd` is the first unpaid one. Do not "repair"
/// this to `Eq`: there is no composite carrier with no equality, and a probe built on
/// one measures nothing (the same trap WI-1110's own investigation fell into).
#[test]
fn an_ord_carrier_still_owes_eq() {
    let src = r#"
namespace wi1110.owes
  import anthill.prelude.{Ord, WeakOrd, Int64, Bool}
  enum Half
    entity half(v: Int64)
    provides Ord[T = Half]
    operation compare(a: Half, b: Half) -> Int64 = 0
  end
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| {
            e.contains("provides 'anthill.prelude.WeakOrd'")
                && e.contains("requires 'anthill.prelude.PartialOrd'")
        }),
        "the obligation travels from `WeakOrd` to the carrier through the conversion, so \
         a carrier providing only `Ord` must be told about it — and the message must \
         name `WeakOrd` as the requirer, since that is where the requirement is now \
         written; got {errs:?}"
    );
    // AND IT MUST SAY WHERE THE ROW CAME FROM. `Half` wrote `provides Ord[T = Half]` and
    // nothing else; the `WeakOrd` row the refusal is about was DERIVED from it. Without
    // the provenance the message attributes to the author a clause that is not in the
    // source — the exact wording WI-1109 fixed one check over, which WI-1110 would
    // otherwise have made the primary channel.
    assert!(
        errs.iter().any(|e| {
            e.contains("is not written on this carrier")
                && e.contains("`provides anthill.prelude.Ord`")
        }),
        "the refusal must name the clause the author DID write; got {errs:?}"
    );
}

/// THE `Eq` HALF OF THE SAME RELOCATION, which the arm above cannot measure. `Ord` used
/// to write `requires Eq[T]`; it does not any more, and the claim is that `WeakOrd
/// requires Eq[T]` reaches the carrier through the conversion. A PARAMETRIC composite is
/// what drives it: `eq_derive` classifies only composites whose fields are all lawful and
/// deliberately derives NOTHING for a parametric one (its equality is conditional on its
/// argument's), so `Box[T]` genuinely has no equality of its own and the `Eq` obligation
/// is the first unpaid one.
#[test]
fn a_parametric_ord_carrier_owes_eq() {
    let src = r#"
namespace wi1110.paramowes
  import anthill.prelude.{Ord, WeakOrd, Int64, Bool}
  enum Box
    sort T = ?
    entity box(v: T)
    provides Ord[T = Box]
    operation compare(a: Box, b: Box) -> Int64 = 0
  end
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| {
            e.contains("provides 'anthill.prelude.WeakOrd'")
                && e.contains("requires 'anthill.prelude.Eq'")
        }),
        "`Eq` is `WeakOrd`'s requirement and `Ord` restates it nowhere, so it must still \
         reach a carrier that provides only `Ord`; got {errs:?}"
    );
}

/// A sort writing BOTH `requires A[T]` and the conversion `provides A[T = T]` names one
/// relation twice and must get ONE slot. Two equal entries are a slot `synth_req_names`
/// cannot name apart, and the dedup that prevents it lives in `direct_requires` — where a
/// first cut compared the two specs STRUCTURALLY and could never fire, because a
/// `requires` spec is re-keyed by the required spec's own parameter symbols while a
/// `provides` row keeps the written ones. Nothing in the stdlib writes both clauses any
/// more, so this fixture is the only thing that drives it.
///
/// DRIVEN, and it fails with the structural key restored: `got ["wi1110.both.Low",
/// "wi1110.both.Low"]` — two slots for one edge, which is the collision the dedup exists
/// to prevent.
#[test]
fn a_sort_writing_both_clauses_gets_one_slot() {
    let src = r#"
namespace wi1110.both
  import anthill.prelude.{Int64, Bool}
  sort Low
    sort T = ?
    operation probe(a: T) -> Int64
  end
  sort High
    sort T = ?
    requires Low[T]
    provides Low[T = T]
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let high = kb
        .try_resolve_symbol("wi1110.both.High")
        .expect("High registered");
    let chain = anthill_core::kb::typing::direct_requires_chain(&mut kb, high);
    assert_eq!(
        chain.len(),
        1,
        "one edge, one slot — got {:?}",
        chain
            .iter()
            .map(|e| kb.qualified_name_of(e.required_sort).to_string())
            .collect::<Vec<_>>()
    );
}

/// THE CONTROL for `an_ord_carrier_still_owes_eq`, and it is what says the refusal
/// discriminates rather than refusing every carrier: the same carrier with the equality
/// floors written loads clean and its order runs.
#[test]
fn an_ord_carrier_that_pays_loads_and_runs() {
    let src = r#"
namespace wi1110.pays
  import anthill.prelude.{Ord, WeakOrd, PartialOrd, PartialEq, Eq, Int64, Bool}
  enum Half
    entity half(v: Int64)
    provides Eq[T = Half]
    provides PartialOrd[T = Half]
    provides Ord[T = Half]
    operation eq(a: Half, b: Half) -> Bool =
      match a
        case half(x) ->
          match b
            case half(y) -> PartialEq.eq(x, y)
    operation compare(a: Half, b: Half) -> Int64 =
      match a
        case half(x) ->
          match b
            case half(y) -> WeakOrd.compare(x, y)
  end
  sort D
    operation go(n: Int64) -> Int64 = WeakOrd.compare(Half.half(9), Half.half(4))
  end
end
"#;
    assert!(
        eval_int(src, "wi1110.pays.D.go") > 0,
        "one `provides Ord` must satisfy the `WeakOrd` slot and 9 vs 4 must come back \
         positive"
    );
}

/// AND `provides Eq` NOW CARRIES `PartialEq` WITH IT — the benefit the equality
/// conversion buys, driven on a carrier that writes only the upper floor. Note this
/// fixture writes NO `provides PartialEq`: before WI-1110 that was a load error
/// (`provides 'Eq', which requires 'PartialEq'`), which is what two wi224 fixtures used
/// to pin.
#[test]
fn provides_eq_carries_partialeq() {
    let src = r#"
namespace wi1110.eqonly
  import anthill.prelude.{Eq, PartialEq, Int64, Bool}
  enum Tag
    entity tag(v: Int64)
    provides Eq[T = Tag]
    operation eq(a: Tag, b: Tag) -> Bool =
      match a
        case tag(x) ->
          match b
            case tag(y) -> PartialEq.eq(x, y)
  end
  sort D
    operation go(n: Int64) -> Bool = PartialEq.eq(Tag.tag(3), Tag.tag(3))
  end
end
"#;
    assert!(
        eval_bool(src, "wi1110.eqonly.D.go"),
        "`Tag` writes only `provides Eq`, and a `PartialEq` dispatch on it must resolve \
         through the DERIVED row and answer true for two equal tags"
    );
}

// ── helpers ──────────────────────────────────────────────────────────────────

fn load_errs(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("expected load errors, got a clean load"),
        Err(errs) => errs,
    }
}

fn eval_int(src: &str, entry: &str) -> i64 {
    // A FRESH interpreter per call — a reused one poisons later calls (WI-1057's
    // measured footgun), and `interp_for` is the owner of the load-then-bind sequence.
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(v)) => v,
        other => panic!("{entry} must answer an Int64; got {other:?}"),
    }
}

fn eval_bool(src: &str, entry: &str) -> bool {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Bool(v)) => v,
        other => panic!("{entry} must answer a Bool; got {other:?}"),
    }
}
