//! WI-858 (proposal 058 §3.2, §3.8, §5; implementation notes §8 phase 7) — `Pair`'s
//! CANONICAL ordering in the prelude, and an alternative ordering as the PROGRAM's
//! opt-in.
//!
//! WHAT THE PRELUDE SHIPS, and why it is one order and not two. `Pair` provides
//! `PartialOrd`/`Ordered` for itself, lexicographic `fst`-then-`snd` — the order every
//! neighbouring language gives a pair (Haskell `Ord (a, b)`, Rust `Ord for (A, B)`,
//! Python tuples, `std::pair`). Nothing in the prelude ordered a `Pair` before, so this
//! is a capability added rather than a choice imposed: a bracket-less
//! `Ordered.compare` on a pair now ANSWERS, and `SortedSet.empty[T = Pair[…]]()` needs
//! no ordering bracket.
//!
//! Shipping two co-equal witnesses instead would have made every downstream
//! bracket-less compare on a pair a tier-3 error its author never opted into — the
//! same reason no prelude witness may order `String`
//! (`docs/brainstorms/prelude-multiple-orderings.md`, obstacle A). So 058's coexistence
//! is exercised here the way a real program would: the ALTERNATIVE is declared by the
//! program that wants it, and selected by name.
//!
//! WHY `Pair` COULD CARRY IT AT ALL is obstacle B: `Ordered requires Eq[T]`, and in a
//! binding-free `stdlib/` load no primitive's `Eq` exists (those live in the
//! per-language binding files, proposal 038). A prelude-LAWFUL carrier can be ordered
//! by the prelude; a primitive cannot. `Pair` gained componentwise `PartialEq`/`Eq` in
//! the same change, which is what makes its `Ordered` provision acceptable.
//!
//! AND THE LIMIT THAT COMES WITH IT, driven and pinned below: while a rival IS
//! declared, the canonical order becomes unreachable through a `requires` slot — `Pair`
//! is a CONCRETE provider, so an explicit `[Ordered = Pair]` is refused (the value
//! decides, §3.5 check 3) while the rival makes the bracket-less goal ambiguous. Rung
//! 2a (WI-861) is the missing rung, and it needs no edit to `pair.anthill`.
//!
//! Reference: `stdlib/anthill/prelude/pair.anthill`, `wi844_sorted_set_driver_test`
//! (the same pipeline over a carrier with no canonical order),
//! `wi857_dictionary_layout_test` (the locality rule the bundles rely on).

use anthill_core::eval::Value;

/// Imports only — no ordering is declared here, because whether a program declares a
/// rival is exactly what several assertions below turn on.
fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ordered, PartialOrd, PartialEq, String, Int64, Float, \
         List, Pair, SortedSet}}\n  \
         import anthill.prelude.Pair.{{pair}}\n{body}\nend\n"
    )
}

/// A LOCAL alternative ordering — lexicographic `snd`-then-`fst`, the mirror of the
/// prelude's. A `PartialOrd` + `Ordered` BUNDLE with NAMED element slots, which is the
/// lawful form (058 §3.8): `ordered.anthill` derives `gt`/`lt` from `compare` off the
/// carrier's `PartialOrd`, so a lone `Ordered` witness would contradict what it
/// inherits.
const BY_SND: &str = r#"
  sort BySnd
    import anthill.prelude.{Int64, Pair, Ordered, PartialOrd, PartialEq}
    import anthill.prelude.Pair.{pair}
    sort A = ?
    sort B = ?
    requires OA: Ordered[A]
    requires OB: Ordered[B]
    provides PartialOrd[Pair[A, B]]
    provides Ordered[Pair[A, B]]
    operation compare(a: Pair[A, B], b: Pair[A, B]) -> Int64 =
      match a
        case pair(al, ar) ->
          match b
            case pair(bl, br) ->
              let c = Ordered.compare(ar, br)
              if PartialEq.eq(c, 0) then Ordered.compare(al, bl) else c
"#;

/// A SECOND local alternative — descending by `fst`. Needed wherever an assertion is
/// about two RIVALS rather than about a rival beside the canonical order, since the
/// canonical one cannot be named (see `the_canonical_order_is_unreachable_beside_a_rival`).
const BY_FST_DESC: &str = r#"
  sort ByFstDesc
    import anthill.prelude.{Int64, Pair, Ordered, PartialOrd, PartialEq}
    import anthill.prelude.Pair.{pair}
    sort A = ?
    sort B = ?
    requires OA: Ordered[A]
    requires OB: Ordered[B]
    provides PartialOrd[Pair[A, B]]
    provides Ordered[Pair[A, B]]
    operation compare(a: Pair[A, B], b: Pair[A, B]) -> Int64 =
      match a
        case pair(al, ar) ->
          match b
            case pair(bl, br) ->
              let c = Ordered.compare(bl, al)
              if PartialEq.eq(c, 0) then Ordered.compare(ar, br) else c
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

/// Insert `(2,1)` then `(1,9)` into a `SortedSet` and read the whole set back. `bracket`
/// is the ordering selection — EMPTY for the canonical order, which is the point.
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

/// THE OBSTACLE-B CONTROL, and it is what decides that this provision may be
/// prelude-owned rather than whether it works: `stdlib/` must load with NO language
/// binding present. `load_stdlib_kb` is exactly that load (it collects `stdlib/` alone
/// and panics on failure), and it is what many suites use.
///
/// Not ceremony. The identical experiment on `String` — one prelude witness beside
/// `Ordered[String]` — MEASURED two errors here (*"provides `Ordered`, which requires
/// `Eq`, but … does not provide `Eq`"*), because `Eq[String]` exists only in the Rust
/// binding. `Pair` passes because its `Eq` leg discharges from its OWN provision.
/// Asserted on the PROVISION FACT rather than on "the load did not panic": without the
/// `Ordered` provision `stdlib/` loads perfectly well (it did, until this change), so a
/// bare `load_stdlib_kb()` would be vacuous for this claim. (`wi362_stream_provides_
/// iterable`'s shape.)
#[test]
fn the_prelude_orders_a_pair_with_no_language_binding() {
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
                named.iter().find(|(s, _)| kb.resolve_sym(*s) == key).map(|(_, t)| *t)
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
    for spec in ["anthill.prelude.Ordered", "anthill.prelude.PartialOrd", "anthill.prelude.Eq"] {
        assert!(
            pair_provides.iter().any(|s| s == spec),
            "`Pair` must provide {spec} in a BINDING-FREE load — that is the property \
             that lets the order live in the prelude rather than in a language binding; \
             found only {pair_provides:?}",
        );
    }
}

// ── The canonical order, with no bracket anywhere ────────────────────

/// THE HEADLINE: lexicographic `fst`-then-`snd`, answering with NO bracket at all —
/// one provider, tier 2. Three arms, because a comparator has three ways to be wrong:
/// the first component deciding, the TIE handing over to the second, and equality.
#[test]
fn the_canonical_order_is_lexicographic_fst_then_snd() {
    let src = program(
        "wi858.canonical",
        "  sort Driver\n    \
         operation byFst(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 1, snd: 9), pair(fst: 2, snd: 1))\n    \
         operation bySndOnTie(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 5, snd: 9), pair(fst: 5, snd: 1))\n    \
         operation equal(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 5, snd: 9), pair(fst: 5, snd: 9))\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi858.canonical.Driver.byFst", "fst decides"),
        -1,
        "1 < 2 on `fst`, and `snd` (9 vs 1) must NOT get a vote — a 1 here would mean \
         the order is by `snd`",
    );
    assert_eq!(
        eval_int(&src, "wi858.canonical.Driver.bySndOnTie", "fst ties, snd decides"),
        1,
        "`fst` ties at 5, so 9 > 1 decides — a 0 here would mean the second component \
         is never consulted",
    );
    assert_eq!(eval_int(&src, "wi858.canonical.Driver.equal", "both components equal"), 0);
}

/// …and it threads into a `SortedSet` with NO ordering bracket, which is the capability
/// that did not exist before: nothing in the prelude ordered a `Pair`, so a set of
/// pairs was unconstructible.
#[test]
fn a_sorted_set_of_pairs_needs_no_ordering_bracket() {
    let src = program(
        "wi858.set",
        &format!("  sort Driver\n{RENDER}{}  end", pipeline("sorted", "")),
    );
    assert_eq!(
        eval_str(&src, "wi858.set.Driver.sorted", "canonical, bracket-free"),
        "(1,9)(2,1)",
        "inserted (2,1) then (1,9); ascending by `fst` puts (1,9) first",
    );
}

// ── An alternative is the PROGRAM's to declare ───────────────────────

/// 058's coexistence, exercised the way a real program would: the rival is declared by
/// the program that wants it, and selected by name at the construction site. The SAME
/// two pairs through the same bracket-less downstream pipeline give the other answer.
#[test]
fn a_program_declared_alternative_is_selected_by_name() {
    let src = program(
        "wi858.alt",
        &format!("{BY_SND}  end\n  sort Driver\n{RENDER}{}  end", pipeline("bySnd", ", O = BySnd")),
    );
    assert_eq!(
        eval_str(&src, "wi858.alt.Driver.bySnd", "the alternative, selected"),
        "(2,1)(1,9)",
        "ascending by `snd` puts (2,1) first — the canonical answer is the reverse, so \
         `(1,9)(2,1)` would mean the selection reached nothing",
    );
}

/// THE MEASURED LIMIT that comes with it, and it is the LADDER's, not `pair.anthill`'s:
/// while a rival is declared, the canonical order is unreachable through a `requires`
/// slot. Both halves are driven, because either alone is explicable:
///
///  * the bracket-LESS goal is now AMBIGUOUS — two providers, and tier 3 refuses;
///  * and the canonical one cannot be NAMED, because `Pair` is a CONCRETE provider and
///    §3.5 check 3 refuses an explicit witness where the value decides.
///
/// So the repair the first error suggests is refused by the second. Rung 2a (WI-861)
/// is exactly the missing rung — the carrier's own provision is the INFERRED default,
/// so silence would take `Pair` and the rival stay opt-in, with no edit to the prelude.
/// When that lands, this test's first arm becomes a VALUE assertion.
#[test]
fn the_canonical_order_is_unreachable_beside_a_rival() {
    let bare = program(
        "wi858.shadowed",
        &format!("{BY_SND}  end\n  sort Driver\n{RENDER}{}  end", pipeline("canonical", "")),
    );
    let errs = load_errs(&bare);
    assert!(
        errs.iter().any(|e| {
            e.contains("ambiguous among providers")
                && e.contains("anthill.prelude.Pair")
                && e.contains("wi858.shadowed.BySnd")
        }),
        "RECORDED (WI-861): with a rival declared, the bracket-less goal names both the \
         carrier's own provision and the rival. If this ever RESOLVES, rung 2a landed — \
         turn this into a value assertion expecting the canonical `(1,9)(2,1)`: {errs:?}"
    );

    let named = program(
        "wi858.namedcanon",
        &format!(
            "{BY_SND}  end\n  sort Driver\n{RENDER}{}  end",
            pipeline("canonical", ", O = Pair")
        ),
    );
    let errs = load_errs(&named);
    assert!(
        errs.iter().any(|e| e.contains("CONCRETE provider")),
        "…and the repair the first error suggests is itself refused: `Pair`'s values \
         carry their own sort, so §3.5 check 3 rejects an explicit `[Ordered = Pair]`. \
         That pincer is why WI-861 is the fix and not a bracket: {errs:?}"
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
            "{BY_SND}  end\n{BY_FST_DESC}  end\n  sort Driver\n    \
             operation mixed(n: Int64) -> List[T = Pair[Int64, Int64]] =\n      \
             let a = SortedSet.empty[T = Pair[Int64, Int64], O = BySnd]()\n      \
             let b = SortedSet.empty[T = Pair[Int64, Int64], O = ByFstDesc]()\n      \
             SortedSet.toList(SortedSet.union(a, b))\n  end"
        ),
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("expected SortedSet[T = Pair[A = Int64, B = Int64], O = BySnd]")
                && e.contains("got SortedSet[T = Pair[A = Int64, B = Int64], O = ByFstDesc]")
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
            "  sort Driver\n{RENDER}    \
             operation same(n: Int64) -> String =\n      \
             let a = SortedSet.insert(\n        \
             SortedSet.empty[T = Pair[Int64, Int64]](), pair(fst: 1, snd: 9))\n      \
             let b = SortedSet.insert(\n        \
             SortedSet.empty[T = Pair[Int64, Int64]](), pair(fst: 2, snd: 1))\n      \
             render(SortedSet.toList(SortedSet.union(a, b)))\n  end"
        ),
    );
    assert_eq!(eval_str(&src, "wi858.agree.Driver.same", "two agreeing sets merge"), "(1,9)(2,1)");
}

/// The ELEMENT orderings are independent of the pair ordering: a HETEROGENEOUS
/// `Pair[Int64, String]` threads `Ordered[Int64]` for `fst` and `Ordered[String]` for
/// `snd` — two DIFFERENT providers of one spec, live in one dictionary at once. Worth
/// asserting because an `InstanceSelection` is keyed by the SPEC, so a read that
/// collapsed the two would pin one element ordering onto both components.
#[test]
fn a_heterogeneous_pair_orders_through_two_element_orderings() {
    let src = program(
        "wi858.het",
        "  sort Driver\n    \
         operation sndDecides(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 1, snd: \"zz\"), pair(fst: 1, snd: \"aaa\"))\n    \
         operation fstDecides(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 1, snd: \"zz\"), pair(fst: 2, snd: \"aaa\"))\n  end",
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

/// `Pair`'s componentwise equality — the change that made the carrier prelude-LAWFUL
/// and so let the ordering live here at all. Asserted in both directions and on both
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
/// The residue is pinned by the second arm rather than hidden: `provides Eq[Pair]`
/// rides that same one chain, so a NaN reaches a LAWFUL-KEY position inside a pair,
/// which `Set[T = Float]` itself is refused for. Per-provision conditions (058 §3.8's
/// `provides X[…] :- goals`) separate the two — WI-869 — and the composite `NonEq`
/// derivation `eq.anthill` already calls a follow-up is the other half.
#[test]
fn a_pair_of_floats_loads_and_that_has_a_recorded_cost() {
    loads_clean(
        &program(
            "wi858.float",
            "  sort Use\n    operation tag(p: Pair[Float, Int64]) -> Int64 = 1\n  end",
        ),
        "`Pair`'s chain is `PartialEq`, which `Float` provides — an `Eq` chain refused \
         this (MEASURED), and `Pair` would have stopped being a general product",
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
    if crate::common::try_load_kb_with(&as_key).is_err() {
        panic!(
            "RECORDED COST FIXED: a NaN-bearing pair is no longer accepted as a lawful \
             key. That is the wanted behaviour — delete this arm and close WI-869's \
             composite half."
        );
    }
}

/// THE OTHER MEASURED LIMIT, pinned so it is not discovered twice: a NESTED pair whose
/// FIRST component is a `Pair` and whose second is a primitive dies at eval, the second
/// component's compare dispatching to `Pair.eq`.
///
/// PRE-EXISTING and needing none of this ticket's vocabulary — reproduced on a purely
/// local two-parameter carrier with its own componentwise `eq` — but `Pair` gaining a
/// componentwise body is what makes it reachable from the standard library.
/// Characterized by driving: `A = <carrier>, B = <primitive>` fails; `A = <primitive>,
/// B = <carrier>` and `A = B = <carrier>` both pass, so it is not "nesting" as such but
/// the slot the FIRST component's requirement occupies. WI-871.
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
    // ONE interpreter for all three arms, which the trap ordering permits: a trapped
    // call poisons later calls on a shared interpreter, so the two arms that SUCCEED
    // run first and the trapping one last.
    let mut interp = crate::common::interp_for(&src);
    let ok = |i: &mut anthill_core::eval::Interpreter, entry: &str, why: &str| {
        match i.call(entry, &[Value::Int(0)]) {
            Ok(Value::Int(n)) => n,
            other => panic!("{why}; got {other:?}"),
        }
    };
    assert_eq!(ok(&mut interp, "wi858.nested.Driver.carrierOnRight", "carrier SECOND"), 1);
    assert_eq!(ok(&mut interp, "wi858.nested.Driver.carrierBothSides", "carrier BOTH"), 1);
    // Asserted STRUCTURALLY, not on the rendering: `EvalError`'s Display says only
    // "raised error" and its Debug prints raw `Symbol(n)`s, so a substring test for
    // `match_failed` would be vacuous either way.
    let payload = match interp.call("wi858.nested.Driver.carrierOnLeft", &[Value::Int(0)]) {
        Err(anthill_core::eval::EvalError::Raised { payload }) => payload,
        Ok(v) => panic!(
            "RECORDED DEFECT FIXED: a nested pair in the FIRST component now answers \
             {v:?}. That is the wanted behaviour — delete this arm and fold the case \
             into `pair_equality_is_componentwise`, and close WI-871."
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
/// slots. DRIVEN: the binding is accepted and then DISCARDED.
///
/// Two arms, because either alone is explicable:
///
///  * the KEY is checked — an unknown slot name is refused, naming the real ones. So
///    the value's bracket list is parsed and validated against the witness.
///  * the VALUE steers nothing — a NONSENSE binding (`OA = ByFstDesc`, which provides
///    no `Ordered[Int64]` at all) loads clean and computes the unbound answer.
///
/// The consequence that makes this a defect rather than a gap: `TieRepair::SubGoal`
/// PRINTS this spelling as the repair for a sub-goal tie, so an author who follows the
/// diagnostic gets the identical error back. WI-870.
#[test]
fn a_named_slot_bound_in_a_bracket_value_steers_nothing() {
    let unknown = program(
        "wi858.compose.key",
        &format!(
            "{BY_SND}  end\n  sort Driver\n    \
             operation go(n: Int64) -> Int64 =\n      \
             Ordered.compare[Ordered = BySnd[NoSuchSlot = Int64]](\n        \
             pair(fst: 1, snd: 9), pair(fst: 2, snd: 1))\n  end"
        ),
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
        &format!(
            "{BY_SND}  end\n{BY_FST_DESC}  end\n  sort Driver\n    \
             operation go(n: Int64) -> Int64 =\n      \
             Ordered.compare[Ordered = BySnd[OA = ByFstDesc]](\n        \
             pair(fst: 1, snd: 9), pair(fst: 2, snd: 1))\n  end"
        ),
    );
    assert_eq!(
        eval_int(&nonsense, "wi858.compose.value.Driver.go", "the nonsense binding"),
        1,
        "RECORDED: `ByFstDesc` provides no `Ordered[Int64]`, so a binding that reached \
         the sub-goal would be refused. Loading clean AND computing the unbound answer \
         (`BySnd`: 9 > 1) is the measurement — the value's slot bindings are validated \
         and then dropped. If this ever REFUSES, the composition leg was implemented: \
         move this to a positive assertion.",
    );
}

// ── Control: nothing outside `Pair` moved ────────────────────────────

/// The carriers that ALREADY had an `Ordered` provider are untouched — obstacle A
/// stated as a control. A bracket-less compare on a `String` or an `Int64` still
/// resolves silently, which is precisely what a prelude witness for those carriers
/// would have destroyed.
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
