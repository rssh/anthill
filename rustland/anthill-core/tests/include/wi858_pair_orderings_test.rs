//! WI-858 (proposal 058 §3.2, §3.8, §5; implementation notes §8 phase 7) — 058's
//! coexistence over `Pair`, and what the PRELUDE does and does not ship for it.
//!
//! WHAT THE PRELUDE SHIPS — REWRITTEN AT WI-869/WI-877, because the answer changed.
//! `Pair` now provides FOUR conditioned provisions: `PartialEq`, `Eq`, `PartialOrd`
//! and `Ord`, each with its own `:- goals` tail (058 §3.8), and the ordering is
//! the canonical lexicographic `fst`-then-`snd`. When this file was written it
//! provided only the two equality floors, for two reasons that are both now gone:
//! ordering `Pair` cost SEVEN operations where one would do (WI-876 keyed host
//! implementations per carrier, so `compare` alone suffices), and a sort's ONE
//! `requires` chain could not condition `Ord` without also demanding it of
//! `PartialEq` (WI-869 scoped conditions to their own provision).
//!
//! WHICH CHANGES THE COEXISTENCE STORY BELOW, and the arms record the new shape
//! rather than being deleted. `Pair` is now a THIRD `Ord` provider, so the two
//! witnesses declared here tie three ways at a bracket-less compare — the same
//! configuration `wi844_sorted_set_driver_test` has over `String`, whose host
//! `Ord` provider makes its ties three-way. Every repair here is still writable
//! for the two LOCAL witnesses; naming the prelude's own is not (058 §3.5 check 3
//! refuses `[Ord = Pair]` because `Pair` is a CONCRETE provider — WI-861's rung
//! 2a is what would close that, and WI-877 records the decision to keep the order as
//! `Pair`'s own identity anyway).
//!
//! WHY THE PRELUDE COULD HAVE CARRIED AN ORDERING (and what still holds): obstacle B —
//! `Ord requires Eq[T]`, and in a binding-free `stdlib/` load no primitive's `Eq`
//! exists (those live in the per-language binding files, proposal 038). `Pair`'s
//! componentwise `Eq` is what makes an ordering of it prelude-expressible at all, and
//! it is what lets the two witnesses below discharge their own `Eq` leg.
//!
//! Reference: `stdlib/anthill/prelude/pair.anthill`, `wi844_sorted_set_driver_test`,
//! `wi857_dictionary_layout_test` (the locality rule the bundles rely on).

use anthill_core::eval::Value;

/// Imports only — no ordering is declared here, because whether a program declares a
/// rival TO THE PRELUDE'S is exactly what several assertions below turn on.
fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, PartialOrd, PartialEq, String, Int64, Float, \
         List, Pair, SortedSet}}\n  \
         import anthill.prelude.Pair.{{pair}}\n{body}\nend\n"
    )
}

/// A LOCAL ordering — lexicographic `snd`-then-`fst`. A `PartialOrd` + `Ord`
/// BUNDLE with NAMED element slots, which is the lawful form (058 §3.8):
/// `ordered.anthill` derives `gt`/`lt` from `compare` off the carrier's `PartialOrd`,
/// so a lone `Ord` witness would contradict what it inherits.
const BY_SND: &str = r#"
  sort BySnd
    import anthill.prelude.{Int64, Pair, Ord, PartialOrd, PartialEq}
    import anthill.prelude.Pair.{pair}
    sort A = ?
    sort B = ?
    requires OA: Ord[A]
    requires OB: Ord[B]
    provides PartialOrd[Pair[A, B]]
    provides Ord[Pair[A, B]]
    operation compare(a: Pair[A, B], b: Pair[A, B]) -> Int64 =
      match a
        case pair(al, ar) ->
          match b
            case pair(bl, br) ->
              let c = Ord.compare(ar, br)
              if PartialEq.eq(c, 0) then Ord.compare(al, bl) else c
"#;

/// The SECOND local ordering — lexicographic `fst`-then-`snd`, the one a canonical
/// `Ord[Pair]` would be. Declared here rather than in the prelude for WI-876's
/// reason (see this file's header).
const BY_FST: &str = r#"
  sort ByFst
    import anthill.prelude.{Int64, Pair, Ord, PartialOrd, PartialEq}
    import anthill.prelude.Pair.{pair}
    sort A = ?
    sort B = ?
    requires OA: Ord[A]
    requires OB: Ord[B]
    provides PartialOrd[Pair[A, B]]
    provides Ord[Pair[A, B]]
    operation compare(a: Pair[A, B], b: Pair[A, B]) -> Int64 =
      match a
        case pair(al, ar) ->
          match b
            case pair(bl, br) ->
              let c = Ord.compare(al, bl)
              if PartialEq.eq(c, 0) then Ord.compare(ar, br) else c
"#;

/// Render a `List[Pair[Int64, Int64]]` as `(1,9)(2,1)`.
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

/// Insert `(2,1)` then `(1,9)` into a `SortedSet` and read the whole set back. `Pair`
/// provides no ordering, so the construction site always names one — 058's tier-1
/// selection, and the only thing that can answer here.
fn pipeline(op: &str, bracket: &str) -> String {
    format!(
        "    operation {op}(n: Int64) -> String =\n      \
         let s = SortedSet.empty[T = Pair[Int64, Int64]{bracket}]()\n      \
         render(SortedSet.toList(\n        \
         SortedSet.insert(SortedSet.insert(s, pair(fst: 2, snd: 1)), pair(fst: 1, snd: 9))))\n"
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

// ── Obstacle B: why the prelude may order a `Pair` at all ────────────

/// THE OBSTACLE-B CONTROL: `Pair`'s componentwise equality must hold with NO language
/// binding present — that is what makes an ordering of `Pair` prelude-EXPRESSIBLE at
/// all (`Ord requires Eq[T]`), and it is what the two witnesses below discharge
/// their own `Eq` leg from. `stdlib/` must load bindings-free. `load_stdlib_kb` is exactly that load (it collects `stdlib/` alone
/// and panics on failure), and it is what many suites use.
///
/// Not ceremony. The identical experiment on `String` — one prelude witness beside
/// `Ord[String]` — MEASURED two errors here (*"provides `Ord`, which requires
/// `Eq`, but … does not provide `Eq`"*), because `Eq[String]` exists only in the Rust
/// binding. `Pair` passes because its `Eq` is its own.
/// Asserted on the PROVISION FACT rather than on "the load did not panic": without the
/// `Ord` provision `stdlib/` loads perfectly well (it did, until this change), so a
/// bare `load_stdlib_kb()` would be vacuous for this claim. (`wi362_stream_provides_
/// iterable`'s shape.)
#[test]
fn the_prelude_makes_a_pair_lawful_with_no_language_binding() {
    use anthill_core::kb::term::Term;
    let kb = crate::common::load_stdlib_kb();
    let provides = kb
        .try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("SortProvidesInfo sort must exist");
    let functor_qn = |t| match kb.get_term(t) {
        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
            Some(kb.qualified_name_of(*functor).to_string())
        }
        _ => None,
    };
    let pair_provides: Vec<String> = kb
        .rules_by_functor(provides)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .filter_map(|rid| kb.fact_head_named_args(rid))
        .filter_map(|named| {
            let get = |key: &str| {
                named.iter().find(|(s, _)| kb.local_name_of(*s) == key).map(|(_, t)| *t)
            };
            let (sort_ref, spec) = (get("sort_ref")?, get("spec")?);
            if functor_qn(sort_ref).as_deref() != Some("anthill.prelude.Pair") {
                return None;
            }
            match kb.get_term(spec) {
                Term::Fn { pos_args, .. } => pos_args.first().copied().and_then(functor_qn),
                _ => functor_qn(spec),
            }
        })
        .collect();
    // WI-869/WI-877: all FOUR floors, not just the two equality ones. `Ord
    // requires Eq` and `PartialOrd requires PartialEq`, so the ordering provisions
    // are exactly what the equality ones make prelude-expressible — asserting only
    // the equality half would leave the tower's upper floors unpinned in the very
    // load (bindings-free) that is their precondition.
    for spec in [
        "anthill.prelude.PartialEq",
        "anthill.prelude.Eq",
        "anthill.prelude.PartialOrd",
        "anthill.prelude.Ord",
    ] {
        assert!(
            pair_provides.iter().any(|s| s == spec),
            "`Pair` must provide {spec} in a BINDING-FREE load — that is the property \
             that lets the order live in the prelude rather than in a language binding; \
             found only {pair_provides:?}",
        );
    }
}

// ── 058's coexistence: two orderings the PROGRAM declares ───────────

/// THE HEADLINE. Two orderings of one carrier coexist, each chosen at a CONSTRUCTION
/// site, each threaded to the comparison that reads it. The same two pairs through the
/// same bracket-less downstream pipeline give opposite answers — one answer twice would
/// mean the selection reached nothing.
#[test]
fn each_construction_site_selects_its_own_ordering() {
    let src = program(
        "wi858.thread",
        &format!(
            "{BY_SND}  end\n{BY_FST}  end\n  sort Driver\n{RENDER}{}{}  end",
            pipeline("byFst", ", O = ByFst"),
            pipeline("bySnd", ", O = BySnd")
        ),
    );
    assert_eq!(
        eval_str(&src, "wi858.thread.Driver.byFst", "lexicographic by `fst`"),
        "(1,9)(2,1)",
    );
    assert_eq!(
        eval_str(&src, "wi858.thread.Driver.bySnd", "lexicographic by `snd`"),
        "(2,1)(1,9)",
    );
}

/// …and the discrimination control, driven rather than assumed: SWAP the two brackets
/// and the two answers swap. Each answer is therefore attributable to the bracket at
/// its own construction site, not to declaration order or entry name.
#[test]
fn swapping_the_brackets_swaps_the_answers() {
    let src = program(
        "wi858.swap",
        &format!(
            "{BY_SND}  end\n{BY_FST}  end\n  sort Driver\n{RENDER}{}{}  end",
            pipeline("byFst", ", O = BySnd"),
            pipeline("bySnd", ", O = ByFst")
        ),
    );
    // The entry NAMES are deliberately left as they were: only the brackets moved.
    assert_eq!(eval_str(&src, "wi858.swap.Driver.byFst", "the pin, swapped"), "(2,1)(1,9)");
    assert_eq!(eval_str(&src, "wi858.swap.Driver.bySnd", "the pin, swapped"), "(1,9)(2,1)");
}

/// …AND THE PRICE OF COEXISTENCE, which is 058's whole subject: with both declared, a
/// bracket-LESS `Ord.compare` on a `Pair` is a loud tier-3 error naming both. This
/// is the configuration every phase before 3b refused at the DECLARATION; it is now
/// refused at the one call that has to choose, with the repair spelled out.
///
/// WI-869/WI-877 UPDATED THIS ARM rather than deleting it: the prelude now ships
/// `Pair`'s own lexicographic order, so the tie is THREE-way and names
/// `anthill.prelude.Pair` beside the two locals. That cost was taken knowingly —
/// WI-877's feedback measured it and chose the canonical order as `Pair`'s identity —
/// and asserting the prelude's name HERE is what keeps the choice visible: were the
/// provision withdrawn, this arm reports it instead of quietly passing on two.
#[test]
fn a_bracketless_compare_with_two_orderings_names_both() {
    let src = program(
        "wi858.bare",
        &format!(
            "{BY_SND}  end\n{BY_FST}  end\n  sort Use\n    \
             operation cmp(a: Pair[Int64, Int64], b: Pair[Int64, Int64]) -> Int64 =\n      \
             Ord.compare(a, b)\n  end"
        ),
    );
    let errs = load_errs(&src);
    let tie: Vec<&String> =
        errs.iter().filter(|e| e.contains("ambiguous dispatch of")).collect();
    assert_eq!(tie.len(), 1, "one ambiguous call, one error; all errors: {errs:?}");
    assert!(
        tie[0].contains("wi858.bare.ByFst") && tie[0].contains("wi858.bare.BySnd"),
        "the tie must name BOTH declared orderings: {}",
        tie[0]
    );
    assert!(
        tie[0].contains("anthill.prelude.Pair"),
        "…and the PRELUDE's own, which WI-877 added: a two-way tie here would mean \
         `Pair` stopped providing its canonical order: {}",
        tie[0]
    );
}


/// §3.4's merge safety, over two RIVALS — two differently-ordered sets have two TYPES,
/// so `union` is a type error before it is a wrong answer. Two locally-declared
/// witnesses rather than "canonical vs rival", since the canonical one cannot be named
/// while a rival exists (above).
#[test]
fn union_across_two_orderings_is_a_type_error() {
    let src = program(
        "wi858.merge",
        &format!(
            "{BY_SND}  end\n{BY_FST}  end\n  sort Driver\n    \
             operation mixed(n: Int64) -> List[T = Pair[Int64, Int64]] =\n      \
             let a = SortedSet.empty[T = Pair[Int64, Int64], O = BySnd]()\n      \
             let b = SortedSet.empty[T = Pair[Int64, Int64], O = ByFst]()\n      \
             SortedSet.toList(SortedSet.union(a, b))\n  end"
        ),
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("expected SortedSet[T = Pair[A = Int64, B = Int64], O = BySnd]")
                && e.contains("got SortedSet[T = Pair[A = Int64, B = Int64], O = ByFst]")
        }),
        "the merge hazard must be refused by ordinary parameter agreement, naming BOTH \
         orderings: {errs:?}"
    );
}

/// …and the control that makes the refusal attributable to the ORDERING rather than to
/// `union` being unusable over pairs: two sets that AGREE merge, and merge correctly.
#[test]
fn union_within_one_ordering_merges() {
    let src = program(
        "wi858.agree",
        &format!(
            "{BY_FST}  end\n  sort Driver\n{RENDER}    \
             operation same(n: Int64) -> String =\n      \
             let a = SortedSet.insert(\n        \
             SortedSet.empty[T = Pair[Int64, Int64], O = ByFst](), pair(fst: 1, snd: 9))\n      \
             let b = SortedSet.insert(\n        \
             SortedSet.empty[T = Pair[Int64, Int64], O = ByFst](), pair(fst: 2, snd: 1))\n      \
             render(SortedSet.toList(SortedSet.union(a, b)))\n  end"
        ),
    );
    assert_eq!(eval_str(&src, "wi858.agree.Driver.same", "two agreeing sets merge"), "(1,9)(2,1)");
}

/// The ELEMENT orderings are independent of the pair ordering: a HETEROGENEOUS
/// `Pair[Int64, String]` threads `Ord[Int64]` for `fst` and `Ord[String]` for
/// `snd` — two DIFFERENT providers of one spec, live in one dictionary at once. Worth
/// asserting because an `InstanceSelection` is keyed by the SPEC, so a read that
/// collapsed the two would pin one element ordering onto both components.
#[test]
fn a_heterogeneous_pair_orders_through_two_element_orderings() {
    let src = program(
        "wi858.het",
        &format!(
            "{BY_FST}  end\n  sort Driver\n    \
             operation sndDecides(n: Int64) -> Int64 =\n      \
             Ord.compare[Ord = ByFst](pair(fst: 1, snd: \"zz\"), \
             pair(fst: 1, snd: \"aaa\"))\n    \
             operation fstDecides(n: Int64) -> Int64 =\n      \
             Ord.compare[Ord = ByFst](pair(fst: 1, snd: \"zz\"), \
             pair(fst: 2, snd: \"aaa\"))\n  end"
        ),
    );
    assert_eq!(
        eval_int(&src, "wi858.het.Driver.sndDecides", "Int64 fst ties, String snd decides"),
        1,
        "`fst` ties at 1, so `snd` decides through the OTHER element ordering: \
         \"zz\" > \"aaa\"",
    );
    assert_eq!(
        eval_int(&src, "wi858.het.Driver.fstDecides", "fst does not tie"),
        -1,
        "1 < 2 on `fst`, so `snd` never votes — without this arm an order that read \
         only `snd` would pass the assertion above",
    );
}


// ── What `Pair` gaining `Eq` did, and did not, do ────────────────────

/// `Pair`'s componentwise equality — the change that makes the carrier prelude-LAWFUL,
/// which is what lets an ordering of it discharge its `Eq` leg at all. Asserted in both directions and on both
/// components: a constant `true`, or a body reading only one component, would pass a
/// weaker test.
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

/// THE EQUALITY CHAIN IS `PartialEq`, NOT `Eq`, and this is what that buys: `Pair`
/// stays a general PRODUCT. MEASURED with an `Eq` chain — which is what the ticket
/// originally prescribed — this program became a LOAD ERROR: `Float` provides `NonEq`,
/// and WI-835's use-site check refuses a `NonEq` carrier at a parameter whose sort
/// `requires Eq`. A pair of floats is an ordinary value and must keep loading.
///
/// THE RESIDUE, AND WI-869 RE-ATTRIBUTED IT. This arm used to say the second half is
/// still red because `provides Eq[Pair]` rides one shared chain and so over-claims.
/// That half is DONE: `pair.anthill` now writes `provides Eq[Pair] :- Eq[A], Eq[B]`
/// and the goal `Eq[Pair[Float, Int64]]` genuinely does not resolve — measured by its
/// sibling floor in `wi869_per_provision_conditions_test`, where the same shape
/// refuses `Ord.compare` on a float pair naming `Ord[Float]`.
///
/// `Set[T = Pair[Float, Int64]]` STILL LOADS, for a different and now-measured
/// reason: there is NO POSITIVE use-site check for `requires Eq`. The only refusal at
/// a written type site is the `NonEq` one below, and `Pair` provides no `NonEq` — so
/// does `Set[T = <a sort that provides nothing at all>]`, which MEASURED loads clean
/// too. The remaining halves are therefore the composite `NonEq` derivation
/// `eq.anthill` calls a follow-up, and a positive use-site discharge; neither is
/// about the provision's condition any more.
#[test]
fn a_pair_of_floats_loads_and_that_has_a_recorded_cost() {
    loads_clean(
        &program(
            "wi858.float",
            "  sort Use\n    operation tag(p: Pair[Float, Int64]) -> Int64 = 1\n  end",
        ),
        "`Pair`'s equality condition is `PartialEq`, which `Float` provides — an `Eq` \
         one refused this (MEASURED), and `Pair` would have stopped being a general \
         product. After WI-869 it is the PROVISION's condition, not a sort-level \
         chain, and `provides Eq[Pair] :- Eq[A], Eq[B]` sits beside it without \
         reaching this declaration",
    );

    let as_key = program(
        "wi858.floatkey",
        "  import anthill.prelude.{Set}\n  \
         sort Use\n    operation tag(s: Set[T = Pair[Float, Int64]]) -> Int64 = 1\n  end",
    );
    let direct = program(
        "wi858.floatkeydirect",
        "  import anthill.prelude.{Set}\n  \
         sort Use\n    operation tag(s: Set[T = Float]) -> Int64 = 1\n  end",
    );
    assert!(
        load_errs(&direct).iter().any(|e| e.contains("NonEq")),
        "the CONTROL: `Float` itself is refused as a lawful key, so the arm below is \
         about the PAIR hiding it and not about `Set` accepting anything",
    );
    // THE SECOND CONTROL, added at WI-869 because it is what re-attributed the gap: a
    // key that provides NOTHING is accepted too. So `Set` is not consulting whether
    // `Eq[key]` HOLDS at all — the only written-site refusal is the `NonEq` one above
    // — and the pair below is not a special case of over-claiming, it is the general
    // absence of a positive discharge.
    loads_clean(
        &program(
            "wi858.opaquekey",
            "  import anthill.prelude.{Set}\n  \
             sort Opaque\n    entity opaque\n  end\n  \
             sort Use\n    operation tag(s: Set[T = Opaque]) -> Int64 = 1\n  end",
        ),
        "a key providing NEITHER `Eq` nor `NonEq` is accepted, which is what makes \
         the pair arm below a case of the missing positive check and not of `Pair`",
    );
    if crate::common::try_load_kb_with(&as_key).is_err() {
        panic!(
            "RECORDED COST FIXED: a NaN-bearing pair is no longer accepted as a lawful \
             key. That is the wanted behaviour — delete this arm and the opaque-key \
             control beside it. WI-869 closed the provision half (the `Eq[Pair]` \
             provision is conditioned now); what remains is the composite `NonEq` \
             derivation and a positive use-site discharge, so whichever of those lands \
             is what this reports."
        );
    }
}

/// NESTED PAIRS, all three slot arrangements — the WI-871 matrix, now passing.
///
/// Recorded here as a DEFECT until WI-1059: with the first component itself a `Pair` and
/// the second a primitive, the second component's compare dispatched to `Pair.eq` and died
/// matching a primitive against the entity pattern (`match_failed(scrutinee: 7)`). The
/// other two arrangements always passed, so it was never "nesting" as such — it was the
/// slot the FIRST component's requirement occupied once that requirement resolved to the
/// provider itself.
///
/// WI-1059 fixed it, and the mechanism is the one that ticket is about: `Pair.eq(a: Pair,
/// b: Pair)` leaves both parameters' `A`/`B` unwritten, so the body used to be checked
/// against a slot that satisfied any demand. With the unwritten slots materialized as the
/// enclosing sort's own parameters (the member tie — `docs/design/type-parameter-scoping.md`
/// §3), the two same-spec requirement reads are indexed at the bindings they actually have
/// and the second slot stops being read from the first.
///
/// All three arms are asserted, and that is the control: a change that made pair equality
/// fail everywhere would still satisfy the one arm this test was added for.
#[test]
fn nested_pair_equality_is_componentwise_in_every_slot() {
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
    for (entry, why) in [
        ("carrierOnLeft", "carrier FIRST — the arm WI-871 recorded as failing"),
        ("carrierOnRight", "carrier SECOND"),
        ("carrierBothSides", "carrier BOTH"),
    ] {
        assert_eq!(
            eval_int(&src, &format!("wi858.nested.Driver.{entry}"), why),
            1,
            "{why}",
        );
    }
}

/// The SAME matrix on a purely LOCAL two-parameter carrier — no prelude `Pair`, no 058
/// vocabulary. WI-871 characterized the defect on both, so the fix is asserted on both:
/// without this arm a repair specific to `anthill.prelude.Pair` would read as a fix of the
/// general rule.
#[test]
fn nested_local_carrier_equality_is_componentwise_in_every_slot() {
    let src = r#"
namespace wi858.localnest
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}

  sort Duo
    sort A = ?
    sort B = ?
    requires PartialEq[A]
    requires PartialEq[B]
    entity duo(l: A, r: B)
    provides PartialEq[Duo]
    operation eq(x: Duo, y: Duo) -> Bool =
      match x
        case duo(xl, xr) ->
          match y
            case duo(yl, yr) ->
              if PartialEq.eq(xl, yl) then PartialEq.eq(xr, yr) else false
  end

  sort Driver
    operation carrierOnLeft(n: Int64) -> Int64 =
      if PartialEq.eq(duo(l: duo(l: 1, r: 2), r: 7),
                      duo(l: duo(l: 1, r: 2), r: 7)) then 1 else 0
    operation carrierOnRight(n: Int64) -> Int64 =
      if PartialEq.eq(duo(l: 7, r: duo(l: 1, r: 2)),
                      duo(l: 7, r: duo(l: 1, r: 2))) then 1 else 0
    operation carrierBothSides(n: Int64) -> Int64 =
      if PartialEq.eq(duo(l: duo(l: 1, r: 2), r: duo(l: 3, r: 4)),
                      duo(l: duo(l: 1, r: 2), r: duo(l: 3, r: 4))) then 1 else 0
    operation bothPrimitive(n: Int64) -> Int64 =
      if PartialEq.eq(duo(l: 1, r: 2), duo(l: 1, r: 2)) then 1 else 0
  end
end
"#;
    for (entry, why) in [
        ("carrierOnLeft", "carrier FIRST — the cell WI-871 recorded as failing"),
        ("carrierOnRight", "carrier SECOND"),
        ("carrierBothSides", "carrier BOTH"),
        ("bothPrimitive", "neither component is the carrier"),
    ] {
        assert_eq!(
            eval_int(src, &format!("wi858.localnest.Driver.{entry}"), why),
            1,
            "{why}",
        );
    }
}

/// THE COST THIS CHANGE WIDENS, recorded because nothing else in the suite witnesses
/// it: a provision's carrier binding is matched by SHORT NAME at dispatch, so a user
/// sort whose short name matches a prelude provider's is offered that provider's impl
/// and then refused. Giving `Pair` provisions adds `Pair` — a far likelier user sort
/// name than `Set`/`Map`/`List` — to that effectively-reserved set.
///
/// PRE-EXISTING and not about `Pair`: the `Set` arm collides with the prelude's own
/// `provides PartialEq[T = Set]`, which has been there since WI-616, and fails
/// identically. `Duple` is the CONTROL — the same shape under a name nothing provides
/// for — so the refusal is attributable to the NAME, not to the shape or to composite
/// equality. WI-872; `wi664_composite_eq_test`'s `Pair`→`Duple` rename is the same
/// defect met as a workaround, and reverting it is WI-872's acceptance.
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

// ── The composition leg (058 §3.3), driven for the first time ────────

/// 058 §3.3 says pinning does not reach into the resolution tree, and that steering a
/// witness's own sub-goal is written by binding its NAMED slot in the key's VALUE
/// position — `fold[Monoid = ListM[O = MyEq]]`. `BySnd`'s `OA`/`OB` are exactly such
/// slots.
///
/// **This was the RECORDED DEFECT and is now the positive assertion (WI-870).** As
/// written here the binding was accepted and then DISCARDED, and it took two arms to
/// show that, because either alone is explicable: the KEY is checked (an unknown slot
/// name is refused, naming the real ones — so the bracket list was parsed and
/// validated against the witness), while the VALUE steered nothing (a NONSENSE
/// binding, `OA = ByFst`, which provides no `Ord[Int64]` at all, loaded clean and
/// computed `1`, `BySnd`'s unbound answer). A silent drop of written text — and a
/// defect rather than a gap because `TieRepair::SubGoal` PRINTS this spelling as the
/// repair for a sub-goal tie, so an author who followed the diagnostic got the
/// identical error back.
///
/// Both arms are kept, one flipped: the key check is unchanged, and the nonsense
/// binding is now REFUSED naming the slot. The positive half of the leg — a MEANINGFUL
/// binding that resolves a sub-goal tie — is driven in
/// `wi870_bracket_value_slot_test`, over a carrier whose element ties are the
/// program's own rather than the prelude's.
#[test]
fn a_named_slot_bound_in_a_bracket_value_steers_its_sub_goal() {
    let unknown = program(
        "wi858.compose.key",
        &format!(
            "{BY_SND}  end\n  sort Driver\n    \
             operation go(n: Int64) -> Int64 =\n      \
             Ord.compare[Ord = BySnd[NoSuchSlot = Int64]](\n        \
             pair(fst: 1, snd: 9), pair(fst: 2, snd: 1))\n  end"
        ),
    );
    let errs = load_errs(&unknown);
    assert!(
        errs.iter().any(|e| {
            e.contains("has no type parameter named 'NoSuchSlot'") && e.contains("OA, OB")
        }),
        "the value's bracket is validated against the witness's parameters — the arm \
         that made the drop below a DROP rather than a parse failure: {errs:?}"
    );

    let nonsense = program(
        "wi858.compose.value",
        &format!(
            "{BY_SND}  end\n{BY_FST}  end\n  sort Driver\n    \
             operation go(n: Int64) -> Int64 =\n      \
             Ord.compare[Ord = BySnd[OA = ByFst]](\n        \
             pair(fst: 1, snd: 9), pair(fst: 2, snd: 1))\n  end"
        ),
    );
    let errs = load_errs(&nonsense);
    assert!(
        errs.iter().any(|e| e.contains("bound slot `OA` of") && e.contains("ByFst")),
        "`ByFst` provides `Ord` at `Pair`, never at `Int64`, so the binding is now \
         refused where it used to be dropped — and named in the author's own \
         vocabulary, the SLOT rather than the sub-goal it became: {errs:?}"
    );
}

// ── Control: nothing outside `Pair` moved ────────────────────────────

/// The carriers that ALREADY had an `Ord` provider are untouched — obstacle A
/// stated as a control. A bracket-less compare on a `String` or an `Int64` still
/// resolves silently, which is precisely what a prelude witness for those carriers
/// would have destroyed.
#[test]
fn primitive_orderings_are_unchanged() {
    let src = program(
        "wi858.primitives",
        "  sort Driver\n    \
         operation strings(n: Int64) -> Int64 = Ord.compare(\"b\", \"a\")\n    \
         operation ints(n: Int64) -> Int64 = Ord.compare(7, 3)\n  end",
    );
    assert_eq!(eval_int(&src, "wi858.primitives.Driver.strings", "String compare"), 1);
    assert_eq!(eval_int(&src, "wi858.primitives.Driver.ints", "Int64 compare"), 1);
}
