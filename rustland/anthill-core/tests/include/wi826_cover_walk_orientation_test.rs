//! WI-826 — the cover-walk ORIENTATION holes (WI-821 /code-review findings 2, 9,
//! 10; finding 2 CONFIRMED by a live drive).
//!
//! `entries_cover` (entry-vs-entry, Strategies 1 & 2) walks the DEMAND's binding
//! keys and refuses when the SUPPLY lacks one. `requires_entry_covers_goal`
//! (entry-vs-goal, Strategy 3's `FromScope` short-circuit and the direct-dispatch
//! defer check) walked the SUPPLY's keys instead — so a key the GOAL names and the
//! ENTRY does not was never examined, and the σ-gate was bypassed for exactly the
//! spellings where the entry says LESS than the goal:
//!
//! 1. A bare bindingless `requires Desc` (legal, loads clean) covered ANY goal of
//!    that spec — the entry has no keys, so the walk had nothing to check and
//!    returned true before the σ mode was ever consulted.
//! 2. A PARTIALLY-bound entry over a multi-param spec (`requires Pair[P = MT]`,
//!    `Q` omitted) was refused by Strategy 1's dep-driven walk yet accepted by
//!    Strategy 3's scope cover, which only ever looked at `P`.
//!
//! The fix shares the KEY ITERATION the way WI-821 shared the per-pair verdict:
//! one `supply_covers_demanded_keys` walk (demand-driven, the orientation
//! `entries_cover` always had), which `requires_entry_covers_goal` now runs
//! FIRST — keeping its own supply-key check as the second leg, because its demand
//! is a DERIVED goal whose keys `sort_goal_from_subst` drops when an element is
//! unbound. A supply that says less than the demand is NO cover, in either mode.
//!
//! Depth/place coding: `describe(leaf) = 1`, `describe(pebble) = 5`, and each hop
//! multiplies by a distinct power of ten, so a wrong dictionary at any hop is a
//! detectably different number.

use anthill_core::eval::Value;

/// Two carriers for one spec, so a forwarded dictionary and a constructed one
/// give different numbers: `describe(leaf) = 1` vs `describe(pebble) = 5`.
///
/// The `Desc`/`Leaf` half is the same block the wi817/wi825/wi827/wi829 suites
/// open with and MUST stay in sync with them; the second carrier is wi826's own —
/// those suites pair `Leaf` with the CONDITIONAL `Wrap`/`WrapDesc` to get depth
/// coding, where this ticket needs a second PEER carrier so a hand-off to a
/// different concrete type is visible in one digit.
const DESC: &str = r#"
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
"#;

/// The innermost hop, shared by the fixtures below: it reads its requirement at
/// its own parameter, so whichever dictionary reaches it is what the answer's
/// last digit reports.
const BOPS: &str = r#"  sort BOps
    sort BT = ?
    requires Desc[BT]
    operation b(y: BT) -> Int64 = Desc.describe(y)
  end"#;

fn with_desc(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
{DESC}
{body}
end
"#
    )
}

/// THE DRIVEN DEFECT (finding 2). Three hops: `AOps requires Desc[AT]` (bound to
/// `Leaf`) → `MOps requires Desc` (BINDINGLESS) → `BOps.b(pebble())` (a CONCRETE
/// downstream goal).
///
/// At the `MOps → BOps` hop the dep is `Desc[T = Pebble]` and `MOps`' only scope
/// entry is the bare `Desc`. Strategy 1 already refused it (its dep-driven walk
/// finds no `T` on the caller), and Strategy 2 has nothing to compose — but
/// Strategy 3's own `FromScope` lookup ran the entry-driven walk, found no entry
/// keys to check, and short-circuited to the caller's dictionary. That is `AOps`'
/// `Leaf` dictionary, so `describe(pebble())` ran the `Leaf` implementation:
/// `1 + 10000·(1 + 100·1) = 1010001`. Correct is `1 + 10000·(1 + 100·5) =
/// 5010001` — the bare entry covers nothing, so the concrete goal is CONSTRUCTED
/// against `Pebble`.
#[test]
fn bindingless_scope_entry_does_not_cover_a_concrete_goal() {
    let src = with_desc(
        "wi826.bare",
        &format!(
            r#"{BOPS}
  sort MOps
    requires Desc
    operation m(n: Int64) -> Int64 =
      add(Desc.describe(leaf()), mul(100, BOps.b(pebble())))
  end
  sort AOps
    sort AT = ?
    requires Desc[AT]
    operation a(x: AT) -> Int64 = add(Desc.describe(x), mul(10000, MOps.m(0)))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = AOps.a(leaf())
  end"#
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi826.bare.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(5010001))),
        "expected Ok(Int(5010001)) = the concrete `Desc[T = Pebble]` goal constructed \
         because the bare bindingless `requires Desc` covers nothing (pre-fix the \
         entry-driven scope walk had no keys to check, forwarded AOps' Leaf \
         dictionary and measured 1010001); got {got:?}"
    );
}

/// The σ-AGREEING control for the same three hops: `MOps` now names the element
/// (`requires Desc[MT]`) and hands `BOps` its OWN parameter, so the forward is
/// correct and must still be taken. `AOps` passes `leaf()` all the way down, so
/// every hop's dictionary is the `Leaf` one: `1 + 10000·(1 + 100·1) = 1010001`.
/// Pins that the fix refuses only entries that say LESS than the goal, not every
/// abstract cover.
///
/// The number coincides with the DEFECT's pre-fix measurement above, and that is
/// the point rather than a distraction: both mean "the `Leaf` dictionary at every
/// hop". Here `leaf()` really is what reaches the last hop, so it is the right
/// answer; there `pebble()` did, so it was the wrong one.
///
/// This control differs from the defect in TWO variables — the `requires`
/// spelling and the data flow (`m` takes and passes its own `MT`, rather than
/// handing `BOps` a concrete `pebble()`). A one-variable control is not available:
/// a named element must be given something, and keeping `pebble()` under
/// `requires Desc[MT]` would test WI-821's different-param refusal instead of this
/// ticket's missing-key one.
#[test]
fn bound_scope_entry_over_the_same_param_still_forwards() {
    let src = with_desc(
        "wi826.bound",
        &format!(
            r#"{BOPS}
  sort MOps
    sort MT = ?
    requires Desc[MT]
    operation m(z: MT) -> Int64 =
      add(Desc.describe(z), mul(100, BOps.b(z)))
  end
  sort AOps
    sort AT = ?
    requires Desc[AT]
    operation a(x: AT) -> Int64 = add(Desc.describe(x), mul(10000, MOps.m(x)))
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = AOps.a(leaf())
  end"#
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi826.bound.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(1010001))),
        "expected Ok(Int(1010001)) = the Leaf dictionary forwarded by name through \
         both σ-agreeing hops; got {got:?}"
    );
}

/// Finding 9 REFUTED BY DRIVING, and pinned so it stays refuted. The ticket
/// predicted that a PARTIALLY-bound entry over a multi-param spec (`requires
/// Pair[P = MT]`, `Q` omitted) would be refused by Strategy 1's dep-driven walk
/// yet accepted by Strategy 3's entry-driven scope walk, which would only ever
/// look at `P`. It cannot: a BRACKETED `requires` is stored as a `SortView` whose
/// omitted parameters are FILLED with the spec's own parameter ref, so the entry
/// carries `Q = Pair.Q` — a key, not a hole. Both walks therefore see `Q` and
/// both hand it to `binding_pair_covers`, which refuses the concrete/wildcard
/// pair. Only a BRACKET-LESS `requires` (no `SortView` at all, hence genuinely no
/// bindings — the test above) produces the missing key the orientation fix is
/// about.
///
/// What that leaves is WI-828's verdict, which this pins: `Q` is unconstrained at
/// the call, so the requirement cannot be supplied and the load is refused —
/// naming the element and the wildcard cover it declined to forward.
#[test]
fn partially_bound_entry_fills_the_omitted_param_and_is_refused_at_load() {
    let src = with_desc(
        "wi826.partial",
        r#"  sort Pair
    sort P = ?
    sort Q = ?
    operation pd(a: P, b: Q) -> Int64
  end
  sort LeafLeaf
    fact Pair[P = Leaf, Q = Leaf]
    operation pd(a: Leaf, b: Leaf) -> Int64 = 7
  end
  sort AnyPebble
    sort X = ?
    fact Pair[P = X, Q = Pebble]
    operation pd(a: X, b: Pebble) -> Int64 = 8
  end

  sort Callee
    sort CP = ?
    sort CQ = ?
    requires Pair[P = CP, Q = CQ]
    operation c(a: CP, b: CQ) -> Int64 = Pair.pd(a, b)
  end
  sort Partial
    sort MT = ?
    requires Pair[P = MT]
    operation p(x: MT) -> Int64 = Callee.c(x, pebble())
  end
  sort Holder
    requires Pair[P = Leaf, Q = Leaf]
    operation h(n: Int64) -> Int64 = Partial.p(leaf())
  end"#,
    );
    let errs = crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_else(|| panic!("expected a load diagnostic, but the source loaded clean"));
    // ONLY the rendered element is asserted: it is the whole witness (the
    // unwritten `Q` came back as the spec's own `Pair.Q`, so the entry has a key
    // there, not a hole). The surrounding WI-828 wording is that ticket's to
    // change and pinning it here would rot for a reason unrelated to this claim.
    assert!(
        errs.iter().any(|e| e.contains("Q = wi826.partial.Pair.Q")),
        "expected the refusal to render the FILLED omitted parameter as \
         `Q = Pair.Q` (which is why the ticket's predicted missing-key asymmetry \
         cannot arise for a bracketed `requires`); got {errs:?}"
    );
}

/// The `Mid` slot spec and the one carrier that provides it, shared by the two
/// nested-forward fixtures. `Mid` carries its OWN `requires Desc[T = MT2]`, so a
/// caller's `Mid` slot bundles a `Desc` sub-requirement at index 0 — the thing
/// Strategy 2 projects with `requirement_at_sort`. `Gem` provides both (the
/// provider-requires obligation: providing `Mid` means discharging `Mid`'s own
/// `requires`), and its `describe` is 5, distinct from `Leaf`'s 1.
const MID: &str = r#"  sort Mid
    sort MT2 = ?
    requires Desc[T = MT2]
    operation midop(x: MT2) -> Int64
  end
  sort Gem
    entity gem
    fact Desc[T = Gem]
    fact Mid[MT2 = Gem]
    operation describe(x: Gem) -> Int64 = 5
    operation midop(x: Gem) -> Int64 = 50
  end"#;

/// Finding 10 — the bindingless SLOT. `Outer requires Mid` with no bindings, so
/// Strategy 2's one-level composition (`build_child_subst_map`) yields an EMPTY
/// map and `Mid`'s sub-entry `Desc[T = Mid.MT2]` stays in SLOT space, where it
/// σ-disagrees with any determinate dep. That refusal is the RIGHT verdict, not
/// an accident of the empty map: a bare `requires Mid` leaves `Mid`'s parameter
/// unnamed in `Outer`, so nothing written in `Outer` can denote which
/// instantiation the slot's bundled dictionary is for — the same reason the bare
/// scope entry above covers nothing. The dep is served by CONSTRUCTION instead,
/// and the answer is right: `describe(gem) = 5`.
#[test]
fn bindingless_slot_nested_forward_is_refused_and_constructed() {
    let src = with_desc(
        "wi826.slot",
        &format!(
            r#"{MID}
{BOPS}
  sort Outer
    requires Mid
    operation o(n: Int64) -> Int64 = BOps.b(gem())
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Outer.o(0)
  end"#
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi826.slot.Driver.drive", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(5))),
        "expected Ok(Int(5)) = `Desc[T = Gem]` CONSTRUCTED, the nested forward \
         under the bare `requires Mid` slot refused (its composition map is empty, \
         so the sub-entry never reaches caller scope); got {got:?}"
    );
}

/// The BOUND-slot twin of the fixture above, and a NO-OVER-REFUSAL control:
/// naming the slot's parameter (`requires Mid[MT2 = Gem]`) must keep the program
/// loadable. That single bit is all this asserts — a clean load cannot tell a
/// Strategy-2 nested forward from a Strategy-3 construction (the bare-slot twin
/// above constructs and also loads clean), so read it as "the stricter cover does
/// not refuse the bound spelling", not as a pin on which route supplies the dep.
///
/// Deliberately NOT evaluated: `Gem` provides `Mid` UNCONDITIONALLY, so the
/// resolution is a `Leaf` whose emitted `construct_requirement` bundles an EMPTY
/// sub-requirement list, while Strategy 2 indexes the forward by the SPEC's
/// static `direct_requires_chain(Mid)` — running it panics
/// `requirement_at_sort: index 0 out of range`. That mismatch (a `Leaf`'s bundle
/// is built from the CARRIER's `requires`, never from the SPEC's) is a
/// pre-existing gap on HEAD, adjacent to this ticket but not part of it; it is
/// recorded as WI-826 feedback rather than pinned here.
#[test]
fn bound_slot_nested_forward_is_found_at_load() {
    let src = with_desc(
        "wi826.slotbound",
        &format!(
            r#"{MID}
{BOPS}
  sort Outer
    requires Mid[MT2 = Gem]
    operation o(n: Int64) -> Int64 = BOps.b(gem())
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Outer.o(0)
  end"#
        ),
    );
    assert!(
        crate::common::try_load_kb_with(&src).is_ok(),
        "expected a clean load: the bound slot's composed sub-entry `Desc[T = Gem]` \
         σ-agrees with the dep, so Strategy 2 supplies it by nested forward"
    );
}
