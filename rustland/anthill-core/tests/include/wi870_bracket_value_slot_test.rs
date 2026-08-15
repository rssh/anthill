//! WI-870 (proposal 058 §3.3, §5; implementation notes §7) — a NAMED requirement slot
//! bound in a bracket VALUE steers the witness's own sub-goal.
//!
//! §3.3's last paragraph states the rule: *pinning does not reach into the resolution
//! tree*, so steering a witness's own sub-goal is written by binding the witness's
//! NAMED slot in the key's value position — `fold[Monoid = ListM[O = MyEq]]`, an
//! ordinary type application. `TieRepair::SubGoal` prints that spelling as the repair
//! for a sub-goal tie, which is why the leg being unwired was a defect and not a gap:
//! an author who followed the diagnostic got the identical error back.
//!
//! MEASURED AT HEAD before this ticket, on the fixture below: the value's bracket list
//! IS parsed and validated against the witness (an unknown slot name is refused,
//! naming the real parameters) and then DISCARDED — `selection_witness_sym` keeps the
//! BASE and nothing consumed the arguments, so every sub-goal resolved by search with
//! `selected: &[]`.
//!
//! The fixture is `Duo`, a two-component product, ordered by a conditional witness
//! `LexFst` whose element orderings are NAMED slots (`requires OA: WeakOrd[A]`,
//! `requires OB: WeakOrd[B]`) — WI-1109: the WEAK floor, because a lexicographic
//! order reads only `compare` on its components and claims nothing about their
//! kernels, so `Ord` slots would demand more than the body uses and the `Duo`
//! order it provides would over-claim in turn — the shape §3.8 calls the lawful form of an
//! alternative. Two PROGRAM-declared `Ord[Int64]` rivals sit beside `Int64`'s own,
//! so each element sub-goal genuinely ties three ways and only a per-slot pin can
//! answer it. The two rivals are opposites, which is what makes each arm's expected
//! value differ in SIGN from the others rather than in provenance: an off-by-one in
//! the slot index does not merely pick a different provider, it flips the answer.
//!
//! **THE BACK-OUT MATRIX, measured one edit at a time**, so no half of the change is
//! carried by another half's control:
//!
//! | reverted | fails |
//! |---|---|
//! | `resolve_inner`'s per-slot routing (`slot_pin_at` at the recursion) | 6 here + wi858's flipped arm |
//! | the BRACKET producer's extraction (`seed_op_type_args`) | the same 7 |
//! | the σ-READ producer's nested extraction (`selections_from_slot_bindings`) | `the_nested_pin_survives_into_a_bracket_less_later_call` ALONE |
//! | the slot-flavoured refusal wording | the two refusal arms |
//! | *applying* §3.5 check 3 to a sub-slot as well (the opposite decision) | `a_concrete_provider_is_refused_in_the_key_and_accepted_in_a_slot` ALONE |
//!
//! Three arms pass either way BY DESIGN, and each is a control rather than a
//! measurement: `a_bare_pin_leaves_the_witnesss_own_sub_goal_ambiguous` (the tie must
//! SURVIVE — it is what the other arms repair), `an_unknown_key_in_the_value_is_still_
//! refused_by_name` (pre-existing, and what made the drop a drop), and
//! `a_plain_type_parameter_in_the_value_selects_nothing` (the new channel must not
//! capture the old one).

use anthill_core::eval::Value;

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one (`interp_for` panics on a dirty load, so a value assertion is also a
/// clean-load assertion).
fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// The shared fixture: `Duo` (equality only, so it has no ordering of its own),
/// `LexFst` (the conditional witness with two NAMED element slots), and three
/// `Ord[Int64]` suppliers — `Int64`'s own host provision plus two opposite
/// program witnesses.
const PRELUDE: &str = r#"
  import anthill.prelude.{Int64, String, Bool, Ord, WeakOrd, PartialOrd, PartialEq, Eq, Pair, List, SortedSet}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Numeric.{sub}

  enum Duo
    import anthill.prelude.{PartialEq, Eq}
    sort A = ?
    sort B = ?
    requires Eq[T = A]
    requires Eq[T = B]
    entity duo(l: A, r: B)
    provides PartialEq[T = Duo]
    provides Eq[T = Duo]
    operation eq(a: Duo, b: Duo) -> Bool =
      match a
        case duo(al, ar) ->
          match b
            case duo(bl, br) ->
              if PartialEq.eq(al, bl) then PartialEq.eq(ar, br) else false
  end

  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end

  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  sort LexFst
    import anthill.prelude.{Int64, Ord, WeakOrd, PartialOrd, PartialEq}
    sort A = ?
    sort B = ?
    requires OA: WeakOrd[T = A]
    requires OB: WeakOrd[T = B]
    provides PartialOrd[T = Duo[A = A, B = B]]
    provides WeakOrd[T = Duo[A = A, B = B]]
    operation compare(a: Duo[A = A, B = B], b: Duo[A = A, B = B]) -> Int64 =
      match a
        case duo(al, ar) ->
          match b
            case duo(bl, br) ->
              let c = WeakOrd.compare(al, bl)
              if PartialEq.eq(c, 0) then WeakOrd.compare(ar, br) else c
  end
"#;

/// `Duo(1, 9)` vs `Duo(2, 1)` — the FIRST components differ, so only slot `OA`
/// decides. `Duo(5, 9)` vs `Duo(5, 1)` — the first components tie, so only slot `OB`
/// decides. One driver each, so an arm's answer names which slot the pin reached.
fn program(ns: &str, ops: &str) -> String {
    format!("\nnamespace {ns}\n{PRELUDE}\n  sort Driver\n{ops}  end\nend\n")
}

fn by_fst(name: &str, bracket: &str) -> String {
    format!(
        "    operation {name}(n: Int64) -> Int64 =\n      \
         WeakOrd.compare[WeakOrd = LexFst{bracket}](duo(l: 1, r: 9), duo(l: 2, r: 1))\n"
    )
}

fn by_snd(name: &str, bracket: &str) -> String {
    format!(
        "    operation {name}(n: Int64) -> Int64 =\n      \
         WeakOrd.compare[WeakOrd = LexFst{bracket}](duo(l: 5, r: 9), duo(l: 5, r: 1))\n"
    )
}

// ── The control: without a pin the sub-goal has no answer ────────────────

/// THE CONTROL FOR EVERY ARM BELOW, and the reason the leg exists at all: with three
/// `Ord[Int64]` suppliers the witness's OWN element sub-goal ties, and §3.3 says
/// the call-site bracket cannot reach it — `resolve_inner`'s step 0 fires only at
/// `stack.is_empty()`. So `[Ord = LexFst]` is refused, and the diagnostic
/// advertises exactly the spelling the arms below write.
#[test]
fn a_bare_pin_leaves_the_witnesss_own_sub_goal_ambiguous() {
    let errs = load_errs(&program("wi870.tie", &by_fst("go", "")));
    assert!(
        errs.iter()
            .any(|e| e.contains("Ascending") && e.contains("Descending")),
        "the tie is the witness's element ordering, naming both program rivals: {errs:?}"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("[Slot = Chosen]") || e.contains("named requirement slot")),
        "and the repair it prints is the value-position binding this ticket wires: {errs:?}"
    );
}

// ── The leg itself: the value's slot binding steers the sub-goal ─────────

/// 058 §3.3's composition, driven. Both slots pinned to the SAME rival, so the answer
/// is the whole pair's, and it is the OPPOSITE SIGN of what the natural order gives.
#[test]
fn a_slot_bound_in_the_value_steers_the_witnesss_sub_goal() {
    let src = program(
        "wi870.steer",
        &format!(
            "{}{}",
            by_fst("desc", "[OA = Descending, OB = Descending]"),
            by_fst("asc", "[OA = Ascending, OB = Ascending]"),
        ),
    );
    assert_eq!(
        eval_int(&src, "wi870.steer.Driver.asc", "both slots ascending"),
        -1,
        "first components 1 < 2 under the natural order",
    );
    assert_eq!(
        eval_int(&src, "wi870.steer.Driver.desc", "both slots descending"),
        1,
        "…and the reversed element ordering flips it. Same call, same witness, two \
         answers decided by the value's bracket — which is what `steers nothing` \
         denied.",
    );
}

/// EACH SLOT SEPARATELY, which is what makes this a per-slot channel rather than a
/// witness-wide one. The two drivers differ only in which component decides, and each
/// arm pins the two slots to OPPOSITE rivals — so a pin that landed on the wrong slot
/// index inverts the sign rather than merely choosing a different provider.
#[test]
fn each_named_slot_is_pinned_independently() {
    let src = program(
        "wi870.perslot",
        &format!(
            "{}{}",
            by_fst("fstDesc", "[OA = Descending, OB = Ascending]"),
            by_snd("sndDesc", "[OA = Ascending, OB = Descending]"),
        ),
    );
    assert_eq!(
        eval_int(
            &src,
            "wi870.perslot.Driver.fstDesc",
            "OA descending decides"
        ),
        1,
        "the first components decide — `sub(2, 1)` under the reversed ordering. Had \
         the two pins landed on each other's slots this would be `sub(1, 2)` = -1",
    );
    assert_eq!(
        eval_int(
            &src,
            "wi870.perslot.Driver.sndDesc",
            "OB descending decides"
        ),
        -8,
        "the first components tie at 5, so OB decides — `sub(1, 9)` under the reversed \
         ordering. Had the two pins landed on each other's slots this would be `sub(9, \
         1)` = 8: the sign flips, so an off-by-one in the slot index cannot pass",
    );
}

/// THE SECOND PRODUCER, which is 058 §5's own second `SortedSet` line: `let s2 =
/// SortedSet.empty[T = …, O = ListOrd[OE = LexFst]]()`. §3.4 makes a named slot an
/// ordinary type parameter, so the nested binding is part of `s2`'s TYPE — and every
/// call after the construction site carries it as an ARGUMENT, with no bracket of its
/// own. `insert` here writes none; if the σ-read producer kept only the witness BASE
/// the way the bracket producer used to, the element sub-goal would tie again one call
/// later and the type parameter would be doing none of the work §3.4 gives it.
#[test]
fn the_nested_pin_survives_into_a_bracket_less_later_call() {
    let set = |op: &str, oa: &str| {
        format!(
            "    operation {op}(n: Int64) -> Int64 =\n      \
             let s = SortedSet.empty[T = Duo[A = Int64, B = Int64], \
             O = LexFst[OA = {oa}, OB = Ascending]]()\n      \
             match SortedSet.toList(SortedSet.insert(SortedSet.insert(s, \
             duo(l: 1, r: 9)), duo(l: 2, r: 1)))\n        \
             case nil() -> 0\n        \
             case cons(h, t) ->\n          \
             match h\n            \
             case duo(hl, hr) -> hl\n"
        )
    };
    let src = program(
        "wi870.sigma",
        &format!("{}{}", set("asc", "Ascending"), set("desc", "Descending")),
    );
    assert_eq!(
        eval_int(
            &src,
            "wi870.sigma.Driver.asc",
            "the set's least element, ascending"
        ),
        1,
        "`insert` and `toList` carry the ordering in the ARGUMENT's type",
    );
    assert_eq!(
        eval_int(&src, "wi870.sigma.Driver.desc", "…and reversed"),
        2,
        "the two programs differ only in a binding nested inside the CONSTRUCTION \
         site's bracket, and the sorted order at the far end of the pipeline follows \
         it",
    );
}

// ── Validation: a binding that answers nothing is LOUD ───────────────────

/// The acceptance's other half, and it is the WI-841 SPLIT REPEATED ONE LEVEL DOWN.
/// The SITE owns "this sort provides that spec nowhere" — the two typos worth naming
/// both halves for; the RESOLUTION owns "provides it, but not at these bindings",
/// because that is the only level at which the goal exists to be rendered.
///
/// `Duo` is the site half: it provides `PartialEq`/`Eq` and no `Ord` at all.
/// `LexFst` is the resolution half: it provides `Ord` — at `Duo`, never at
/// `Int64` — so nothing at the site can tell, and the binding-precise refusal has to
/// come from the sub-goal's own candidate set going empty.
#[test]
fn a_binding_that_provides_nothing_at_the_sub_goal_is_refused() {
    let at_site = load_errs(&program("wi870.nosuch", &by_fst("go", "[OA = Duo]")));
    assert!(
        at_site
            .iter()
            .any(|e| e.contains("Duo") && e.contains("Ord")),
        "a value that provides the slot's spec NOWHERE is refused at the site, naming \
         both halves: {at_site:?}"
    );

    let at_bindings = load_errs(&program("wi870.nonsense", &by_fst("go", "[OA = LexFst]")));
    assert!(
        at_bindings.iter().any(|e| e.contains(
            "the call bound slot `OA` of `wi870.nonsense.LexFst` to \
             `wi870.nonsense.LexFst`, which provides no anthill.prelude.WeakOrd \
             instance at these bindings"
        )),
        "…and one that provides it at OTHER bindings is refused by the resolution, in \
         the author's own vocabulary — the SLOT, not the sub-goal the slot became. \
         Pinned verbatim because the outer pin's wording (`the call selected W for \
         Spec`) would send the author to the bracket's KEY: {at_bindings:?}"
    );
}

/// §3.5 CHECK 3 IS NOT A SUB-SLOT'S, and this is the pair that decides it. The check
/// refuses naming a CONCRETE provider at a call site because the argument's own value
/// already directs dispatch there, so an explicit witness could only agree redundantly
/// or contradict silently. A witness's requirement slot has no value: it is a
/// dictionary slot the typer resolves, so naming the carrier's own provision IS the
/// meaningful answer.
///
/// The same name in the two positions, so the difference is the position and nothing
/// else. `Pair` is the prelude's own lexicographic `Ord` provider (WI-877) and is
/// concrete — the very sort wi858 records as unnameable in a key.
/// The components are `String`s, not `Int64`s, deliberately: `Pair`'s own conditions
/// (`provides Ord[Pair[A, B]] :- Ord[A], Ord[B]`) are ANONYMOUS slots, so
/// they cannot be pinned, and over `Int64` they would meet this file's two rivals and
/// tie. Measured — the first cut used `Pair[Int64, Int64]` and was refused for exactly
/// that, one level below the thing under test.
#[test]
fn a_concrete_provider_is_refused_in_the_key_and_accepted_in_a_slot() {
    let key = load_errs(&program(
        "wi870.check3key",
        "    operation go(n: Int64) -> Int64 =\n      \
         WeakOrd.compare[WeakOrd = Pair](pair(fst: \"a\", snd: \"z\"), \
         pair(fst: \"b\", snd: \"a\"))\n",
    ));
    assert!(
        key.iter()
            .any(|e| e.contains("Pair") && e.contains("CONCRETE")),
        "in the KEY's value position a concrete provider is refused — §3.5 check 3, \
         unchanged: {key:?}"
    );

    let src = program(
        "wi870.check3slot",
        "    operation go(n: Int64) -> Int64 =\n      \
         WeakOrd.compare[WeakOrd = LexFst[OA = Pair, OB = Ascending]](\n        \
         duo(l: pair(fst: \"a\", snd: \"z\"), r: 3), duo(l: pair(fst: \"b\", snd: \"a\"), r: 3))\n",
    );
    assert_eq!(
        eval_int(
            &src,
            "wi870.check3slot.Driver.go",
            "a concrete provider in a slot"
        ),
        -1,
        "one level in, the identical name is ACCEPTED and answers: `Pair`'s own \
         lexicographic order puts (\"a\", \"z\") before (\"b\", \"a\"). Refusing here \
         would have made a carrier's own provision the one thing a slot cannot name.",
    );
}

/// COMPOSITION NESTS, because the value of a slot binding is itself a bracket value.
/// `Duo[A = Duo[…]]` ordered by `LexFst[OA = LexFst[…], OB = …]` — the inner witness's
/// own element slots are bound inside the outer witness's binding, two levels from the
/// call. Nothing about the mechanism is per-level, and this is what says so.
#[test]
fn a_slot_binding_composes_to_any_depth() {
    let nested = |op: &str, inner: &str| {
        format!(
            "    operation {op}(n: Int64) -> Int64 =\n      \
             WeakOrd.compare[WeakOrd = LexFst[OA = LexFst[OA = Ascending, OB = {inner}], \
             OB = Ascending]](\n        \
             duo(l: duo(l: 5, r: 9), r: 3), duo(l: duo(l: 5, r: 1), r: 3))\n"
        )
    };
    let src = program(
        "wi870.nested",
        &format!(
            "{}{}",
            nested("asc", "Ascending"),
            nested("desc", "Descending")
        ),
    );
    // The outer duo's first components are the INNER duos, which tie on THEIR first
    // component (5) — so the answer is decided by the inner witness's SECOND slot, two
    // brackets deep. The first cut of this test varied the inner `OA` instead and both
    // arms answered 8: the discriminating slot has to be the one the values reach.
    assert_eq!(
        eval_int(&src, "wi870.nested.Driver.asc", "the inner duo's own OB"),
        8,
        "the inner second components decide: `sub(9, 1)` ascending",
    );
    assert_eq!(
        eval_int(
            &src,
            "wi870.nested.Driver.desc",
            "…flipped by the innermost pin"
        ),
        -8,
        "and only the INNERMOST binding differs between these two calls. That the \
         program loads at all is half the assertion: unpinned, that sub-goal ties \
         three ways.",
    );
}

/// A key that is not a slot at all is unchanged — the pre-existing arm, kept here
/// because it is what makes the drop a DROP: the bracket list was always parsed and
/// checked against the witness's parameters.
#[test]
fn an_unknown_key_in_the_value_is_still_refused_by_name() {
    let errs = load_errs(&program("wi870.key", &by_fst("go", "[NoSuchSlot = Int64]")));
    assert!(
        errs.iter().any(|e| {
            e.contains("has no type parameter named 'NoSuchSlot'") && e.contains("OA, OB")
        }),
        "the value's bracket is validated against the witness's parameters: {errs:?}"
    );
}

/// AND AN ORDINARY TYPE PARAMETER IN THE VALUE IS NOT A SELECTION. `LexFst`'s `A` is a
/// plain parameter, not a requirement slot, so `[A = Int64]` binds a type and pins
/// nothing — the tie is still the tie. Without this the change could have read every
/// bracket entry as a selection and turned a type argument into a provider name.
#[test]
fn a_plain_type_parameter_in_the_value_selects_nothing() {
    let errs = load_errs(&program("wi870.plain", &by_fst("go", "[A = Int64]")));
    assert!(
        errs.iter()
            .any(|e| e.contains("Ascending") && e.contains("Descending")),
        "binding `A` says nothing about which `Ord[Int64]` answers, so the \
         element tie stands exactly as in the control: {errs:?}"
    );
}
