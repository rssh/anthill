//! WI-858 (proposal 058 §3.8, §5; implementation notes §8 phase 7) — TWO LAWFUL
//! ORDERINGS OF ONE CARRIER, IN THE SHIPPED LIBRARY.
//!
//! WI-844 put `SortedSet` in the prelude and its two demonstration orderings in the
//! TEST. The instruction for this phase is that the shipped library must carry the
//! coexistence itself: a mechanism only the suite can exercise has not landed. This
//! file is that claim's acceptance — `stdlib/anthill/prelude/pair.anthill` now ships
//! `PairByFst` and `PairBySnd`, and everything below runs against the prelude as
//! shipped, declaring no ordering of its own.
//!
//! WHY `Pair` AND NOT `String`, WHICH IS §5's OWN EXAMPLE. Measured, twice over
//! (`docs/brainstorms/prelude-multiple-orderings.md`):
//!
//!  * obstacle A — `String` ALREADY has an `Ordered` provider (the Rust binding's
//!    `fact Ordered[T = String]`), so a prelude rival would turn every downstream
//!    bracket-less string compare into a tier-3 error the consumer never opted into.
//!    A standard library may not impose that. `Pair` has no provider to displace.
//!  * obstacle B, the harder one — `stdlib/` must load with NO language binding
//!    (`load_stdlib_kb`, and proposal 038: the prelude is language-agnostic). No
//!    primitive's lawfulness is prelude-level: `Eq[String]`, `Ordered[Int64]` and
//!    their kin live only in the binding files, and `Ordered requires Eq[T]`, so a
//!    prelude witness ordering a PRIMITIVE cannot discharge its own `Eq` leg. A
//!    prelude-LAWFUL carrier can carry prelude-owned orderings, which is why `Pair`
//!    gained componentwise `PartialEq`/`Eq` in the same change.
//!
//! WHY EACH WITNESS IS A BUNDLE, and why no third one is coming: `ordered.anthill`
//! DERIVES `gt`/`lt`/`gte`/`lte` from `compare`, and those are inherited from the
//! carrier's `PartialOrd` — so a lone alternative `Ordered` witness contradicts the
//! surface it inherits, and the lawful form is a `PartialOrd` + `Ordered` BUNDLE
//! (058 §3.8). A compare-`fst`-ONLY witness is additionally a PREORDER: it answers 0
//! for distinct pairs and `insertSorted` reads 0 as "already present", so it would
//! silently drop elements.
//!
//! Reference: `stdlib/anthill/prelude/pair.anthill`, `wi844_sorted_set_driver_test`
//! (the same pipeline over test-local orderings), `wi857_dictionary_layout_test` (the
//! locality rule these two witnesses are the shipped exercise of).

use anthill_core::eval::Value;

/// Every program here imports the same prelude surface and declares NO ordering — the
/// point of the phase is that the orderings are already there.
fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ordered, PartialEq, String, Int64, Float, List, \
         Pair, PairByFst, PairBySnd, SortedSet}}\n  \
         import anthill.prelude.Pair.{{pair}}\n{body}\nend\n"
    )
}

/// Render a `List[Pair[Int64, Int64]]` as `(1,9)(2,1)` — spelled once, because five
/// assertions below differ only in which ordering built the set.
const RENDER: &str = r#"
    import anthill.prelude.String.{concat}
    import anthill.prelude.Int64.{to_string}
    operation render(l: List[T = Pair[Int64, Int64]]) -> String =
      match l
        case nil() -> ""
        case cons(h, t) ->
          match h
            case pair(f, s) ->
              concat(concat("(", concat(to_string(f), concat(",", concat(to_string(s), ")")))),
                     render(t))
"#;

/// THE DRIVER PIPELINE: construct with `[T = Pair[Int64, Int64], O = <ordering>]`, then
/// insert two pairs and read the whole set back — every downstream call BRACKET-LESS,
/// the choice riding in the argument's type (WI-844's mechanism, here over a prelude
/// ordering). The two pairs are chosen so the orderings DISAGREE about which comes
/// first: `(1,9)` wins on `fst`, `(2,1)` wins on `snd`.
fn pipeline(op: &str, ordering: &str) -> String {
    format!(
        "    operation {op}(n: Int64) -> String =\n      \
         let s = SortedSet.empty[T = Pair[Int64, Int64], O = {ordering}]()\n      \
         render(SortedSet.toList(\n        \
         SortedSet.insert(SortedSet.insert(s, pair(fst: 1, snd: 9)), pair(fst: 2, snd: 1))))\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

fn loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got load errors: {errs:?}");
    }
}

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one. `interp_for` panics on a dirty load, so a value assertion is also a
/// clean-load assertion.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn eval_str(src: &str, entry: &str, why: &str) -> String {
    match eval_fresh(src, entry) {
        Ok(Value::Str(s)) => s,
        other => panic!("{why}; got {other:?}"),
    }
}

fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    match eval_fresh(src, entry) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so every
/// `loads_clean` below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(&program(
        "wi858.control",
        "  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    ));
}

// ── Obstacle B: the reason the orderings may live in the prelude ──────

/// THE OBSTACLE-B CONTROL, and it is the acceptance criterion that decides WHERE the
/// two orderings live rather than whether they work: `stdlib/` must load with NO
/// language binding present. `load_stdlib_kb` is exactly that load (it collects
/// `stdlib/` alone and panics on failure), and it is what many suites use.
///
/// This is not ceremony. The identical experiment on `String` — one prelude witness
/// beside `Ordered[String]` — MEASURED two errors here (*"provides `Ordered`, which
/// requires `Eq`, but … does not provide `Eq`"*), because `Eq[String]` exists only in
/// the Rust binding. The two witnesses below pass because their `Eq` leg discharges
/// from `Pair`'s OWN provision and their `PartialOrd` leg from the bundle.
#[test]
fn the_prelude_loads_with_no_language_binding() {
    let kb = crate::common::load_stdlib_kb();
    for w in ["anthill.prelude.PairByFst", "anthill.prelude.PairBySnd"] {
        assert!(
            kb.try_resolve_symbol(w).is_some(),
            "{w} must be part of the binding-free prelude — if this fails the witness \
             was moved out rather than made to load",
        );
    }
}

// ── Coexistence, and the tier-3 refusal that comes with it ───────────

/// TWO providers of one `(spec, carrier)` in the SHIPPED library, and a program using
/// neither still loads. This is the configuration every phase before 3b refused at the
/// declaration.
#[test]
fn two_prelude_orderings_of_one_carrier_coexist() {
    loads_clean(
        &program("wi858.coexist", "  sort Use\n    operation tag(n: Int64) -> Int64 = 1\n  end"),
        "two nameable witnesses for `Ordered[Pair]` coexist (058 §3.2 tier 3)",
    );
}

/// …AND THE PRICE, paid deliberately: a bracket-less `Ordered.compare` on a `Pair` is a
/// loud error naming BOTH. For `String` that price is unpayable — the carrier already
/// had a provider, so a prelude rival would break existing programs — and for `Pair` it
/// costs nothing, since silence never meant anything here. There is deliberately no
/// `DefaultProvider` row for `(Ordered, Pair)`: no canonical pair order exists.
///
/// This also exercises the WI-857 LOCALITY rule on the shipped pair, which was pinned
/// only against a synthetic two-witness fixture: `Ordered requires PartialOrd[T]`, and
/// `PartialOrd[Pair]` has one candidate inside EACH bundle, so a global search would
/// TIE and the diagnostic would name `PartialOrd` — at the wrong level — instead of the
/// two orderings. Reaching this message is what says locality resolved that sub-goal
/// witness-locally.
#[test]
fn a_bracketless_compare_on_a_pair_names_both_orderings() {
    let src = program(
        "wi858.bare",
        "  sort Use\n    \
         operation cmp(a: Pair[Int64, Int64], b: Pair[Int64, Int64]) -> Int64 =\n      \
         Ordered.compare(a, b)\n  end",
    );
    let errs = load_errs(&src);
    let tie: Vec<&String> =
        errs.iter().filter(|e| e.contains("ambiguous dispatch of")).collect();
    assert_eq!(tie.len(), 1, "one ambiguous call, one error; all errors: {errs:?}");
    let text = tie[0];
    assert!(
        text.contains("anthill.prelude.Ordered.compare")
            && text.contains("anthill.prelude.PairByFst")
            && text.contains("anthill.prelude.PairBySnd"),
        "the tie must be reported at `Ordered.compare` and name both shipped orderings \
         — a message naming `PartialOrd` instead would mean the locality rule failed to \
         resolve the bundle's own sub-goal: {text}"
    );
}

// ── The driver: one pin, then bracket-less, and the answers differ ────

/// THE HEADLINE. Two `SortedSet`s over ONE carrier and ONE element type, differing only
/// in the bracket written at their CONSTRUCTION, fed to the same bracket-less pipeline.
/// The whole set is asserted, not just its head, so an ordering that got the first
/// element right by luck and the rest wrong still fails.
#[test]
fn each_construction_site_selects_its_own_pair_ordering() {
    let src = program(
        "wi858.thread",
        &format!(
            "  sort Driver\n{RENDER}{}{}  end",
            pipeline("byFst", "PairByFst"),
            pipeline("bySnd", "PairBySnd")
        ),
    );
    assert_eq!(
        eval_str(&src, "wi858.thread.Driver.byFst", "lexicographic by `fst`"),
        "(1,9)(2,1)",
        "`fst` 1 < 2 decides, and the `snd` components never get a vote",
    );
    assert_eq!(
        eval_str(&src, "wi858.thread.Driver.bySnd", "lexicographic by `snd`"),
        "(2,1)(1,9)",
        "the SAME two pairs through the same body, differing only in the bracket at \
         `empty` — one answer twice would mean the selection decided nothing",
    );
}

/// The discrimination control, driven rather than assumed: SWAP the two construction
/// brackets and the two answers swap. Each answer is therefore attributable to the
/// bracket at its own construction site, not to the declaration order in `pair.anthill`,
/// the insert order, or the entry name.
#[test]
fn swapping_the_construction_brackets_swaps_the_answers() {
    let src = program(
        "wi858.swap",
        &format!(
            "  sort Driver\n{RENDER}{}{}  end",
            pipeline("byFst", "PairBySnd"),
            pipeline("bySnd", "PairByFst")
        ),
    );
    // The entry NAMES are deliberately left as they were: only the brackets moved.
    assert_eq!(eval_str(&src, "wi858.swap.Driver.byFst", "the pin, swapped"), "(2,1)(1,9)");
    assert_eq!(eval_str(&src, "wi858.swap.Driver.bySnd", "the pin, swapped"), "(1,9)(2,1)");
}

/// §3.4's merge safety on the shipped pair: `union` of a `PairByFst` set and a
/// `PairBySnd` one is a TYPE error, because a named slot is a type parameter and the
/// two sets therefore have two types.
#[test]
fn union_across_two_pair_orderings_is_a_type_error() {
    let src = program(
        "wi858.merge",
        "  sort Driver\n    \
         operation mixed(n: Int64) -> List[T = Pair[Int64, Int64]] =\n      \
         let a = SortedSet.empty[T = Pair[Int64, Int64], O = PairByFst]()\n      \
         let b = SortedSet.empty[T = Pair[Int64, Int64], O = PairBySnd]()\n      \
         SortedSet.toList(SortedSet.union(a, b))\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("expected SortedSet[T = Pair[A = Int64, B = Int64], O = PairByFst]")
                && e.contains("got SortedSet[T = Pair[A = Int64, B = Int64], O = PairBySnd]")
        }),
        "the merge hazard must be refused by ordinary parameter agreement, naming BOTH \
         orderings: {errs:?}"
    );
}

/// …and the control that makes the refusal attributable to the ORDERING rather than to
/// `union` being unusable over pairs: the same call on two sets that AGREE loads, and
/// merges correctly. Without this, a `union` broken for `Pair` for any other reason
/// would leave the test above passing.
#[test]
fn union_within_one_pair_ordering_merges() {
    let src = program(
        "wi858.agree",
        &format!(
            "  sort Driver\n{RENDER}    \
             operation same(n: Int64) -> String =\n      \
             let a = SortedSet.insert(\n        \
             SortedSet.empty[T = Pair[Int64, Int64], O = PairByFst](), pair(fst: 1, snd: 9))\n      \
             let b = SortedSet.insert(\n        \
             SortedSet.empty[T = Pair[Int64, Int64], O = PairByFst](), pair(fst: 2, snd: 1))\n      \
             render(SortedSet.toList(SortedSet.union(a, b)))\n  end"
        ),
    );
    assert_eq!(
        eval_str(&src, "wi858.agree.Driver.same", "two agreeing sets merge"),
        "(1,9)(2,1)",
    );
}

/// The ELEMENT orderings are independent of the pair ordering: a HETEROGENEOUS
/// `Pair[Int64, String]` threads `Ordered[Int64]` through slot `OA` and
/// `Ordered[String]` through `OB` — two DIFFERENT providers of one spec, live in one
/// dictionary at once. Worth its own assertion because an `InstanceSelection` is keyed
/// by the SPEC: a read that collapsed the two named slots would pin one element
/// ordering onto both components.
///
/// Both spellings are driven — the direct member call and the spec-op dispatch — since
/// they reach the witness by different routes.
#[test]
fn a_heterogeneous_pair_orders_through_two_element_orderings() {
    let src = program(
        "wi858.het",
        "  sort Driver\n    \
         operation direct(n: Int64) -> Int64 =\n      \
         PairByFst.compare(pair(fst: 1, snd: \"zz\"), pair(fst: 1, snd: \"aaa\"))\n    \
         operation viaSpec(n: Int64) -> Int64 =\n      \
         Ordered.compare[Ordered = PairByFst](pair(fst: 1, snd: \"zz\"), \
         pair(fst: 1, snd: \"aaa\"))\n    \
         operation firstDecides(n: Int64) -> Int64 =\n      \
         PairByFst.compare(pair(fst: 1, snd: \"zz\"), pair(fst: 2, snd: \"aaa\"))\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi858.het.Driver.direct", "Int64 fst ties, String snd decides"),
        1,
        "`fst` ties at 1, so `snd` decides through the OTHER element ordering: \
         \"zz\" > \"aaa\"",
    );
    assert_eq!(
        eval_int(&src, "wi858.het.Driver.viaSpec", "the same, dispatched through the spec"),
        1,
    );
    assert_eq!(
        eval_int(&src, "wi858.het.Driver.firstDecides", "fst does not tie"),
        -1,
        "1 < 2 on `fst`, so `snd` never votes — without this arm a witness that read \
         only `snd` would pass the two assertions above",
    );
}

// ── What `Pair` gaining `Eq` did, and did not, do ────────────────────

/// `Pair`'s componentwise equality — the change that made the carrier prelude-LAWFUL
/// and so let the orderings ship here. Asserted in both directions: a constant `true`
/// would pass the positive arm alone.
#[test]
fn pair_equality_is_componentwise() {
    let src = program(
        "wi858.eq",
        "  sort Driver\n    \
         operation same(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: 1, snd: \"a\"), pair(fst: 1, snd: \"a\")) then 1 else 0\n    \
         operation diffSnd(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: 1, snd: \"a\"), pair(fst: 1, snd: \"b\")) then 1 else 0\n    \
         operation diffFst(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: 1, snd: \"a\"), pair(fst: 2, snd: \"a\")) then 1 else 0\n  end",
    );
    assert_eq!(eval_int(&src, "wi858.eq.Driver.same", "equal pairs"), 1);
    assert_eq!(
        eval_int(&src, "wi858.eq.Driver.diffSnd", "second component differs"),
        0,
        "a body that compared only `fst` would answer 1 here",
    );
    assert_eq!(
        eval_int(&src, "wi858.eq.Driver.diffFst", "first component differs"),
        0,
        "…and one that compared only `snd` would answer 1 here",
    );
}

/// THE CHAIN IS `PartialEq`, NOT `Eq`, and this is what that buys: `Pair` stays a
/// general PRODUCT. MEASURED with an `Eq` chain — which is what the ticket originally
/// prescribed — this program became a LOAD ERROR: `Float` provides `NonEq`, and
/// WI-835's use-site check refuses a `NonEq` carrier at a parameter whose sort
/// `requires Eq`. A pair of floats is an ordinary value and must keep loading.
///
/// The residue is recorded rather than hidden: `provides Eq[Pair]` rides the same one
/// chain, so it is claimed here too, where only the components' PARTIAL equality holds.
/// Per-provision conditions (058 §3.8's deferred `provides X[…] :- goals`) are what
/// separate the two; see the follow-up ticket. This test pins the trade, so a later
/// change that tightens the chain fails HERE, with the reason attached.
#[test]
fn a_pair_of_floats_still_loads() {
    loads_clean(
        &program(
            "wi858.float",
            "  sort Use\n    operation tag(p: Pair[Float, Int64]) -> Int64 = 1\n  end",
        ),
        "`Pair`'s chain is `PartialEq`, which `Float` provides — an `Eq` chain refused \
         this (MEASURED), and `Pair` would have stopped being a general product",
    );
}

/// THE OTHER MEASURED LIMIT, pinned so it is not discovered twice: a NESTED pair whose
/// FIRST component is a `Pair` and whose second is a primitive dies at eval, the second
/// component's compare dispatching to `Pair.eq`.
///
/// It is PRE-EXISTING and needs none of this ticket's vocabulary — reproduced on a
/// purely local two-parameter carrier with its own componentwise `eq`, no prelude
/// involvement — but `Pair` gaining a componentwise body is what makes it reachable
/// from the standard library, which is why it is pinned here. Characterized by driving:
/// `A = <carrier>, B = <primitive>` fails; `A = <primitive>, B = <carrier>` and
/// `A = B = <carrier>` both pass, so it is not "nesting" as such but the slot the FIRST
/// component's requirement occupies. Ticketed as a dictionary-slot defect.
///
/// The passing arms are the control: without them a fix that made ALL pair equality
/// fail would still satisfy the failing one.
#[test]
fn a_nested_pair_in_the_first_component_is_a_recorded_defect() {
    let src = program(
        "wi858.nested",
        "  sort Driver\n    \
         operation carrierOnLeft(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: pair(fst: 1, snd: 2), snd: 7),\n                      \
         pair(fst: pair(fst: 1, snd: 2), snd: 7)) then 1 else 0\n    \
         operation carrierOnRight(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: 7, snd: pair(fst: 1, snd: 2)),\n                      \
         pair(fst: 7, snd: pair(fst: 1, snd: 2))) then 1 else 0\n    \
         operation carrierBothSides(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: pair(fst: 1, snd: 2), snd: pair(fst: 3, snd: 4)),\n                      \
         pair(fst: pair(fst: 1, snd: 2), snd: pair(fst: 3, snd: 4))) then 1 else 0\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi858.nested.Driver.carrierOnRight", "carrier in the SECOND slot"),
        1,
    );
    assert_eq!(
        eval_int(&src, "wi858.nested.Driver.carrierBothSides", "carrier in BOTH slots"),
        1,
    );
    // Asserted STRUCTURALLY, not on the rendering: `EvalError`'s Display says only
    // "raised error" and its Debug prints raw `Symbol(n)`s, so a substring test for
    // `match_failed` would be vacuous either way.
    let mut interp = crate::common::interp_for(&src);
    let payload = match interp.call("wi858.nested.Driver.carrierOnLeft", &[Value::Int(0)]) {
        Err(anthill_core::eval::EvalError::Raised { payload }) => payload,
        Ok(v) => panic!(
            "RECORDED DEFECT FIXED: a nested pair in the FIRST component now answers \
             {v:?}. That is the wanted behaviour — delete this arm and fold the case \
             into `pair_equality_is_componentwise`, and close the dictionary-slot ticket."
        ),
        Err(other) => panic!(
            "the recorded failure is a RAISE of `match_failed`; a different `EvalError` \
             means the defect moved and the ticket needs re-measuring: {other:?}"
        ),
    };
    let expected = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.MatchFailed.match_failed")
        .expect("the match-failure payload entity is in the prelude");
    match &payload {
        Value::Entity { functor, named, .. } => {
            assert_eq!(
                interp.kb().qualified_name_of(*functor),
                interp.kb().qualified_name_of(expected),
                "the recorded failure is the SECOND component's compare landing on \
                 `Pair.eq`, which then fails to match a primitive against the entity \
                 pattern — i.e. a `match_failed` raise",
            );
            assert!(
                named.iter().any(|(_, v)| matches!(v, Value::Int(7))),
                "…and the scrutinee it could not match is the second component, `7` — \
                 without this the assertion would pass on any match failure anywhere: \
                 {named:?}",
            );
        }
        other => panic!("the raise must carry the `match_failed` entity; got {other:?}"),
    }
}

// ── The composition leg (058 §3.3), driven for the first time ────────

/// 058 §3.3 says pinning does not reach into the resolution tree, and that steering a
/// witness's own sub-goal is written by binding its NAMED slot in the key's VALUE
/// position — `fold[Monoid = ListM[O = MyEq]]`. `PairByFst`'s `OA`/`OB` are exactly
/// such slots, and this phase is the first shape that can drive it. DRIVEN: the
/// binding is accepted and then DISCARDED.
///
/// Two arms, because either alone is explicable:
///
///  * the KEY is checked — an unknown slot name is refused, naming the real ones. So
///    the value's bracket list is parsed and validated against the witness.
///  * the VALUE steers nothing — a NONSENSE binding (`OA = PairBySnd`, which provides
///    no `Ordered[Int64]` at all) loads clean and computes the unbound answer. Nothing
///    read it.
///
/// The consequence that makes this a defect rather than a gap: `TieRepair::SubGoal`
/// PRINTS this spelling as the repair for a sub-goal tie, so an author who follows the
/// diagnostic gets the identical error back. Ticketed.
#[test]
fn a_named_slot_bound_in_a_bracket_value_steers_nothing() {
    let unknown = program(
        "wi858.compose.key",
        "  sort Driver\n    \
         operation go(n: Int64) -> Int64 =\n      \
         Ordered.compare[Ordered = PairByFst[NoSuchSlot = PairBySnd]](\n        \
         pair(fst: 1, snd: 9), pair(fst: 2, snd: 1))\n  end",
    );
    let errs = load_errs(&unknown);
    assert!(
        errs.iter().any(|e| {
            e.contains("has no type parameter named 'NoSuchSlot'") && e.contains("OA, OB")
        }),
        "the value's bracket IS validated against the witness's parameters — which is \
         what makes the silent drop below a drop rather than a parse failure: {errs:?}"
    );

    let nonsense = program(
        "wi858.compose.value",
        "  sort Driver\n    \
         operation go(n: Int64) -> Int64 =\n      \
         Ordered.compare[Ordered = PairByFst[OA = PairBySnd]](\n        \
         pair(fst: 1, snd: 9), pair(fst: 2, snd: 1))\n  end",
    );
    assert_eq!(
        eval_int(&nonsense, "wi858.compose.value.Driver.go", "the nonsense binding"),
        -1,
        "RECORDED: `PairBySnd` provides no `Ordered[Int64]`, so a binding that reached \
         the sub-goal would be refused. Loading clean AND computing the unbound answer \
         (`fst` 1 < 2) is the measurement — the value's slot bindings are validated and \
         then dropped. If this ever REFUSES, the composition leg was implemented: move \
         this to a positive assertion.",
    );
}

// ── Controls: nothing outside `Pair` moved ───────────────────────────

/// The carriers that ALREADY had an `Ordered` provider are untouched — this is obstacle
/// A stated as a control. A bracket-less compare on a `String` or an `Int64` still
/// resolves silently to the binding's own provider, which is precisely what a prelude
/// witness for those carriers would have destroyed.
#[test]
fn primitive_orderings_are_unchanged() {
    let src = program(
        "wi858.primitives",
        "  sort Driver\n    \
         operation strings(n: Int64) -> Int64 = Ordered.compare(\"b\", \"a\")\n    \
         operation ints(n: Int64) -> Int64 = Ordered.compare(7, 3)\n  end",
    );
    assert_eq!(eval_int(&src, "wi858.primitives.Driver.strings", "String compare"), 1);
    assert_eq!(eval_int(&src, "wi858.primitives.Driver.ints", "Int64 compare"), 1);
}

/// (A `SortedSet` over a PRIMITIVE with no bracket at all is deliberately NOT re-tested
/// here: `wi844_sorted_set_driver_test::omitting_the_ordering_is_resolved_and_runs` is
/// the same program, and it loads the FULL stdlib — so it already runs against the two
/// orderings this change ships and already asserts they tie nothing for an `Int64` set.)
///
/// THE COST THIS CHANGE WIDENS, recorded because nothing else in the suite witnesses it:
/// a provision's carrier binding is matched by SHORT NAME at dispatch, so a user sort
/// whose short name matches a prelude provider's is offered that provider's impl and
/// then refused. Giving `Pair` a `PartialEq` provision adds `Pair` — a far likelier user
/// sort name than `Set`/`Map`/`List` — to that effectively-reserved set.
///
/// PRE-EXISTING and not about `Pair`: the `Set` arm below collides with the prelude's
/// own `provides PartialEq[T = Set]`, which has been there since WI-616, and fails
/// identically. `Duple` is the CONTROL — the same shape under a name nothing provides
/// for — so the refusal is attributable to the NAME, not to the shape or to composite
/// equality. WI-872; `wi664_composite_eq_test`'s `Pair`→`Duple` rename is the same
/// defect met as a workaround, and reverting that rename is WI-872's acceptance.
#[test]
fn a_local_sort_sharing_a_prelude_providers_short_name_is_a_recorded_defect() {
    let composite = |name: &str, ctor: &str| {
        program(
            "wi872.shadow",
            &format!(
                "  sort {name}\n    entity {ctor}(a: Int64, b: Int64)\n  end\n  \
                 sort Use\n    \
                 operation same(n: Int64) -> Int64 =\n      \
                 if PartialEq.eq({ctor}(a: 1, b: 2), {ctor}(a: 1, b: 2)) then 1 else 0\n  end"
            ),
        )
    };
    assert_eq!(
        eval_int(&composite("Duple", "duple"), "wi872.shadow.Use.same", "the CONTROL"),
        1,
        "a composite under a name no prelude sort provides for compares structurally — \
         without this the two arms below would prove nothing about the NAME",
    );
    for (name, ctor) in [("Pair", "mkpair"), ("Set", "mkset")] {
        let errs = match crate::common::try_load_kb_with(&composite(name, ctor)) {
            Err(e) => e,
            Ok(_) => panic!(
                "RECORDED DEFECT FIXED: a local `sort {name}` now loads. That is the \
                 wanted behaviour — delete this arm, revert the `Duple` rename in \
                 wi664_composite_eq_test, and close WI-872."
            ),
        };
        assert!(
            errs.iter().any(|e| e.contains("no impl matches")),
            "the recorded refusal is the prelude `{name}`'s impl being offered for a \
             DIFFERENT sort of the same short name; a different error means the defect \
             moved and WI-872 needs re-measuring: {errs:?}"
        );
    }
}

