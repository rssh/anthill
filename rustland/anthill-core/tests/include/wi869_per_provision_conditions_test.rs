//! WI-869 (proposal 058 §3.8, §4) — PER-PROVISION CONDITIONAL PROVISIONS:
//! `provides X[…] :- goals`, conditions scoped to ONE provision instead of to the
//! whole sort.
//!
//! WHAT A SORT-LEVEL `requires` CHAIN COULD NOT DO. It is shared by every provision
//! the sort makes, so a provider of two floors of one tower must condition them at
//! ONE strength. `anthill.prelude.Pair` needs two: it provides `PartialEq` wherever
//! its components have the partial equality and `Eq` only where they have the lawful
//! one, `PartialOrd` wherever they are partially ordered and `Ordered` only where
//! they are totally ordered. With one chain the WEAKEST condition must win (else
//! `Pair` stops being a general product — `pair.anthill`'s header carries that
//! measurement) and every stronger provision then over-claims.
//!
//! AND IT WAS NOT ONLY AN OVER-CLAIM. MEASURED at WI-877 and reproduced here before
//! the fix: adding `requires Ordered[A], requires Ordered[B]` to `Pair`'s chain —
//! the only spelling the implementation accepted — turned
//! `PartialEq.eq(pair(fst: 1.5, snd: 1), pair(fst: 1.5, snd: 1))` into the LOAD ERROR
//! *"anthill.prelude.PartialEq.eq.dispatch: expected matching impl for per-call
//! bindings, got no impl matches"*, because a sort's chain is threaded WHOLESALE at
//! every dispatch through the carrier. `Float` provides `PartialOrd` and not
//! `Ordered`, so an ordering requirement broke EQUALITY.
//!
//! THE TWO ARMS THAT DISCRIMINATE, and they are a pair on purpose:
//! [`a_pair_of_floats_still_compares_for_equality`] EVALUATES `eq` on a pair of
//! floats (red before this ticket, on the exact `pair.anthill` this one ships), and
//! [`a_total_comparison_of_a_float_pair_names_the_unmet_condition`] refuses the
//! total comparison of the same value. Either alone is satisfiable by the wrong
//! thing — dropping the ordering makes the first pass, keeping the shared chain
//! makes the second pass — and only together do they say "two provisions,
//! two strengths".
//!
//! [`the_mechanism_on_a_local_tower`] is the same claim with NO prelude vocabulary,
//! and carries its own CONTROL: the identical carrier written with a shared
//! sort-level chain refuses the weak call, which is what the per-provision form
//! stops doing.
//!
//! Reference: 058 §3.8 and §4; `stdlib/anthill/prelude/pair.anthill`'s header;
//! `wi858_pair_orderings_test` (the coexistence story over the same carrier).

use anthill_core::eval::Value;

fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ordered, PartialOrd, PartialEq, Int64, Float, \
         List, Pair, SortedSet, String}}\n  \
         import anthill.prelude.Pair.{{pair}}\n{body}\nend\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one. `interp_for` panics on a dirty load, so a value assertion is also a
/// clean-load assertion.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    match eval_fresh(src, entry) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so every
/// clean-load assertion below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(&program(
        "wi869.control",
        "  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    ));
}

// ── `Pair`: two towers, four provisions, four conditions ─────────────

/// THE ARM THAT WAS RED. On the `pair.anthill` this ticket ships — four conditioned
/// provisions including `Ordered` — a pair of FLOATS must still compare for
/// EQUALITY. Backed out to a shared sort-level chain carrying the same ordering
/// requirement, this is the LOAD ERROR quoted in this file's header (MEASURED before
/// the fix, on this exact program).
///
/// It EVALUATES rather than merely loading, which is WI-877's other finding: the
/// pre-existing `a_pair_of_floats_loads_and_that_has_a_recorded_cost` asserted only
/// that a `Pair[Float, Int64]` DECLARATION loads and so stayed fully green through
/// the regression.
#[test]
fn a_pair_of_floats_still_compares_for_equality() {
    let src = program(
        "wi869.floateq",
        "  sort Driver\n    \
         operation same(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: 1.5, snd: 1), pair(fst: 1.5, snd: 1)) then 1 else 0\n    \
         operation diff(n: Int64) -> Int64 =\n      \
         if PartialEq.eq(pair(fst: 1.5, snd: 1), pair(fst: 2.5, snd: 1)) then 1 else 0\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi869.floateq.Driver.same", "a pair of floats must compare EQUAL"),
        1,
    );
    assert_eq!(
        eval_int(&src, "wi869.floateq.Driver.diff", "…and unequal pairs must not"),
        0,
        "an `eq` that answered `true` unconditionally would pass the arm above",
    );
}

/// THE OTHER HALF OF THE PAIR: the same value, the `Ordered` provision, REFUSED —
/// and refused NAMING the unmet component condition, which is what makes the refusal
/// actionable. Without the name the message says only that this pair has no
/// ordering; with it, the author is told the ordering is missing on `Float`.
///
/// This arm passes BOTH with and without per-provision conditions, by design: under
/// the shared chain it was refused too (for the wrong reason — the chain demanded a
/// total order of everything). What it discriminates is the `unresolved:` clause,
/// which did not exist, and what it CONTROLS is
/// [`a_pair_of_floats_still_compares_for_equality`] — a fix that simply dropped the
/// ordering from `Pair` would make that one pass and this one fail.
#[test]
fn a_total_comparison_of_a_float_pair_names_the_unmet_condition() {
    let src = program(
        "wi869.floatord",
        "  sort Driver\n    \
         operation cmp(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 1.5, snd: 1), pair(fst: 2.5, snd: 1))\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("anthill.prelude.Ordered.compare")
                && e.contains("unresolved: anthill.prelude.Ordered[T = anthill.prelude.Float]")
        }),
        "the refusal must name the unmet component condition `Ordered[Float]`; got {errs:?}",
    );
}

/// …and the ordering half is not merely present, it WORKS: lexicographic
/// `fst`-then-`snd`. The control for the arm above — a `Pair` that provided no
/// ordering at all would also refuse a float comparison.
#[test]
fn an_int_pair_orders_lexicographically() {
    let src = program(
        "wi869.intord",
        "  sort Driver\n    \
         operation fstWins(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9))\n    \
         operation sndBreaksTie(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 1, snd: 1), pair(fst: 1, snd: 9))\n    \
         operation equalPairs(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: 1, snd: 1), pair(fst: 1, snd: 1))\n  end",
    );
    assert_eq!(eval_int(&src, "wi869.intord.Driver.fstWins", "`fst` decides"), 1);
    assert_eq!(
        eval_int(&src, "wi869.intord.Driver.sndBreaksTie", "`snd` breaks a `fst` tie"),
        -1,
        "a `fst`-only comparison would answer 0 here",
    );
    assert_eq!(
        eval_int(&src, "wi869.intord.Driver.equalPairs", "equal pairs tie"),
        0,
    );
}

// ── The mechanism itself, with no prelude vocabulary ─────────────────

/// A two-floor tower and a carrier that provides both floors at two strengths. The
/// point of writing it locally is the CONTROL below: the same carrier with a SHARED
/// sort-level chain, where the strong condition poisons the weak call.
fn tower(carrier_clauses: &str) -> String {
    tower_with(carrier_clauses, "")
}

/// `extra_driver_ops` is appended to `Driver`, so the well-formed fixture stays
/// well-formed: a refusal arm adds its own bad call rather than every arm loading a
/// program that already has one.
fn tower_with(carrier_clauses: &str, extra_driver_ops: &str) -> String {
    format!(
        "\nnamespace wi869.tower\n  \
         import anthill.prelude.{{Int64}}\n\
  sort Weak\n    \
    sort T = ?\n    \
    operation weak(x: T) -> Int64\n  \
  end\n\
  sort Strong\n    \
    sort T = ?\n    \
    requires Weak[T]\n    \
    operation strong(x: T) -> Int64\n  \
  end\n\
  sort OnlyWeak\n    \
    entity ow\n    \
    provides Weak[T = OnlyWeak]\n    \
    operation weak(x: OnlyWeak) -> Int64 = 7\n  \
  end\n\
  sort Both\n    \
    entity bo\n    \
    provides Weak[T = Both]\n    \
    provides Strong[T = Both]\n    \
    operation weak(x: Both) -> Int64 = 1\n    \
    operation strong(x: Both) -> Int64 = 2\n  \
  end\n\
  enum Box\n    \
    sort A = ?\n\
{carrier_clauses}    \
    entity box(v: A)\n    \
    operation weak(x: Box) -> Int64 =\n      \
      match x\n        \
        case box(v) -> Weak.weak(v)\n    \
    operation strong(x: Box) -> Int64 =\n      \
      match x\n        \
        case box(v) -> Strong.strong(v)\n  \
  end\n\
  sort Driver\n    \
    operation weakOnWeak(n: Int64) -> Int64 = Weak.weak(box(v: ow))\n    \
    operation strongOnBoth(n: Int64) -> Int64 = Strong.strong(box(v: bo))\n\
{extra_driver_ops}  \
  end\nend\n"
    )
}

/// The one call a conditional provision must REFUSE: the strong floor over a
/// component that has only the weak one.
const STRONG_ON_WEAK: &str =
    "    operation strongOnWeak(n: Int64) -> Int64 = Strong.strong(box(v: ow))\n";

const PER_PROVISION: &str = "    provides Weak[T = Box] :- Weak[A]\n    \
                             provides Strong[T = Box] :- Strong[A]\n";

/// The pre-WI-869 spelling: ONE chain, and it must be the STRONG one because
/// `Box.strong`'s body needs `Strong[A]` evidence.
const SHARED_CHAIN: &str = "    requires Strong[A]\n    \
                            provides Weak[T = Box]\n    \
                            provides Strong[T = Box]\n";

#[test]
fn the_mechanism_on_a_local_tower() {
    let src = tower(PER_PROVISION);

    // The WEAK provision is conditioned on the WEAK goal alone, so a component that
    // provides only the weak floor is admitted.
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.weakOnWeak", "`Weak[Box[OnlyWeak]]` holds"),
        7,
        "the value comes from `OnlyWeak.weak`, so the call really reached the \
         component's own member and did not stop at `Box`",
    );
    // The STRONG provision is conditioned on the STRONG goal, so a component that has
    // both floors is admitted…
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.strongOnBoth", "`Strong[Box[Both]]` holds"),
        2,
    );
    // …and one that has only the weak floor is REFUSED, naming the unmet condition.
    let refused = load_errs(&tower_with(PER_PROVISION, STRONG_ON_WEAK));
    assert!(
        refused
            .iter()
            .any(|e| e.contains("unresolved: wi869.tower.Strong[T = wi869.tower.OnlyWeak]")),
        "the strong call on a weak-only component must be refused naming \
         `Strong[OnlyWeak]`; got {refused:?}",
    );
}

/// THE CONTROL, and it is what says the ticket changed something: the SAME carrier
/// with one shared chain refuses the WEAK call. That refusal is the shared-chain
/// over-reach in miniature — `Box` claims `Weak` for every `A`, and its one chain
/// demands `Strong[A]` at every dispatch through it.
#[test]
fn the_shared_chain_control_refuses_the_weak_call() {
    let errs = load_errs(&tower(SHARED_CHAIN));
    assert!(
        errs.iter().any(|e| {
            e.contains("wi869.tower.Weak.weak")
                && e.contains("unresolved: wi869.tower.Strong[T = wi869.tower.OnlyWeak]")
        }),
        "with ONE chain the WEAK call must fail, and fail on the STRONG goal — that \
         precise pairing is the over-reach per-provision conditions remove; got {errs:?}",
    );
}

// ── The unconditioned form is untouched ──────────────────────────────

/// A carrier with NO conditional provision must behave exactly as before — the whole
/// safety argument for this change is that `provider_dict_chain` hands back the very
/// `Rc` `direct_requires_chain_rc` does when nothing is conditioned. Driven on `Both`
/// and `OnlyWeak` DIRECTLY, not through `Box`: a call routed through the conditioned
/// carrier would be measuring the conditioned path again.
#[test]
fn a_carrier_with_no_conditional_provision_is_unchanged() {
    let src = tower_with(
        PER_PROVISION,
        "    operation bare(n: Int64) -> Int64 = Weak.weak(ow)\n    \
         operation bareStrong(n: Int64) -> Int64 = Strong.strong(bo)\n",
    );
    assert_eq!(eval_int(&src, "wi869.tower.Driver.bare", "an unconditioned `Weak`"), 7);
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.bareStrong", "…and an unconditioned `Strong`"),
        2,
    );
}

/// TWO PROVISIONS SHARING ONE CONDITION are one slot with TWO owners — the arm the
/// dedup's `conditions_for[i].push` exists for, which neither the stdlib nor any other
/// arm here reaches (`Pair`'s four provisions have four disjoint condition sets).
/// Without it the `SmallVec<[Symbol; 2]>` per slot would be speculative generality; with
/// it, the slot must stay strict for BOTH provisions, which is what the two calls check.
#[test]
fn two_provisions_sharing_one_condition_own_one_slot() {
    // Both floors conditioned on `Weak[A]` alone: the STRONG provision is now satisfied
    // by a weak-only component, and the shared slot must be demanded by both dispatches.
    let clauses = "    provides Weak[T = Box] :- Weak[A]\n    \
                   provides Strong[T = Box] :- Weak[A]\n";
    // `Box.strong` must DERIVE from the weak component, else it reads evidence this
    // spelling deliberately does not declare and the load is refused — correctly.
    let src = tower(clauses).replace(
        "case box(v) -> Strong.strong(v)",
        "case box(v) -> Weak.weak(v)",
    );
    assert_eq!(eval_int(&src, "wi869.tower.Driver.weakOnWeak", "the shared slot serves `Weak`"), 7);
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.strongOnBoth", "…and the same slot serves `Strong`"),
        1,
        "a slot recorded as owned by only the FIRST provision would be `Unavailable` \
         under the second, and `Box.strong`'s read of it would be refused",
    );
}


/// A CONDITION SLOT IS EVIDENCE, and it composes: `Pair.compare`'s component compares
/// go through the `Ordered` provision's own slots, so a pair whose component is itself
/// a pair orders RECURSIVELY. Asserted because `pair.anthill`'s header claims it, and
/// because the inner pair is where the outer provision's condition
/// `Ordered[A = Pair[Int64, Int64]]` has to resolve through `Pair`'s own provision —
/// the locality rule (058 §3.8), not a global search.
///
/// Its equality twin is a RECORDED DEFECT (WI-871, pinned in
/// `wi858_pair_orderings_test`); the ordering path is unaffected by it, which is worth
/// having measured rather than assumed from the shared shape.
#[test]
fn a_pair_of_pairs_orders_recursively() {
    let src = program(
        "wi869.nested",
        "  sort Driver\n    \
         operation innerDecides(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: pair(fst: 1, snd: 2), snd: 7),\n                      \
         pair(fst: pair(fst: 1, snd: 3), snd: 7))\n    \
         operation outerSndDecides(n: Int64) -> Int64 =\n      \
         Ordered.compare(pair(fst: pair(fst: 1, snd: 2), snd: 9),\n                      \
         pair(fst: pair(fst: 1, snd: 2), snd: 7))\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi869.nested.Driver.innerDecides", "the INNER pair breaks the tie"),
        -1,
    );
    assert_eq!(
        eval_int(&src, "wi869.nested.Driver.outerSndDecides", "…and `snd` breaks a full `fst` tie"),
        1,
        "an implementation that only compared the inner pair would answer 0 here",
    );
}

/// THE SLOT SET IS UNIFORM AND THE STRICTNESS IS PER-PROVISION — which means a body
/// CAN name evidence its provision did not earn, and doing so must be LOUD.
///
/// `Box.weak` is rewritten to call `Strong.strong` on its component. It still LOADS:
/// the `Strong[A]` slot exists in `Box`'s dictionary chain (the `Strong` provision put
/// it there), so the typer resolves the read. At eval the slot is `Unavailable` for a
/// dispatch that went through the WEAK provision, and the read is refused by name.
///
/// This is the arm that says the design is "one slot set, per-provision strictness"
/// and not "drop the slots a provision did not declare": under the dropping design the
/// frame would be short and the failure would be an out-of-range internal error
/// attributed to the wrong sort.
#[test]
fn reading_a_sibling_provisions_evidence_is_loud() {
    let src = tower(PER_PROVISION)
        .replace("case box(v) -> Weak.weak(v)", "case box(v) -> Strong.strong(v)");
    crate::common::try_load_kb_with(&src)
        .expect("the read TYPES — the slot is in `Box`'s dictionary chain");
    let err = eval_fresh(&src, "wi869.tower.Driver.weakOnWeak")
        .expect_err("…and is refused at eval, where the slot is unfilled");
    let text = format!("{err:?}");
    assert!(
        text.contains("wi869.tower.Strong.strong") && text.contains("pins no provider"),
        "the refusal must name the operation whose evidence was missing; got {text}",
    );
}

/// THE TWO COMPOSE (058 §3.8): a sort-level `requires` keeps its meaning — it
/// conditions EVERY provision — and a `:- goals` tail adds to its own. Here `Box`
/// requires `Weak[A]` outright and conditions only its `Strong` provision further, so
/// the weak call still runs and the strong one on a weak-only component is refused.
#[test]
fn a_sort_level_requires_and_a_provision_condition_compose() {
    let clauses = "    requires Weak[A]\n    \
                   provides Weak[T = Box]\n    \
                   provides Strong[T = Box] :- Strong[A]\n";
    let src = tower(clauses);
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.weakOnWeak", "the sort-level condition holds"),
        7,
    );
    let refused = load_errs(&tower_with(clauses, STRONG_ON_WEAK));
    assert!(
        refused
            .iter()
            .any(|e| e.contains("unresolved: wi869.tower.Strong[T = wi869.tower.OnlyWeak]")),
        "the provision's OWN condition still bites on top of the sort-level one; \
         got {refused:?}",
    );
}

/// A CONDITION RESTATING A SORT-LEVEL `requires` IS ONE SLOT, not two. Not cosmetic:
/// `synth_req_names` disambiguates same-named slots by the spec's hash-cons id, so two
/// entries that are equal in BOTH fields would synthesize the same name twice and the
/// second frame binding would be unreachable. Driven rather than asserted on the chain,
/// because a duplicated slot shows up as a wrong or missing dispatch, not as a count.
#[test]
fn a_condition_restating_a_sort_level_requires_is_one_slot() {
    let src = tower(
        "    requires Weak[A]\n    \
         provides Weak[T = Box] :- Weak[A]\n    \
         provides Strong[T = Box] :- Strong[A]\n",
    );
    assert_eq!(eval_int(&src, "wi869.tower.Driver.weakOnWeak", "the weak floor runs"), 7);
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.strongOnBoth", "…and so does the strong one"),
        2,
        "a duplicated `Weak[A]` slot would shift every slot after it",
    );
}

/// A CONDITION NAMING NOTHING IS REFUSED, not dropped. The whole point of the tail is
/// that it decides where a provision applies, so a typo in it that loaded clean would
/// leave the provision meaning something other than what is written.
#[test]
fn a_condition_naming_an_unknown_spec_is_refused() {
    let errs = load_errs(&tower(
        "    provides Weak[T = Box] :- NoSuchSpec[A]\n    \
         provides Strong[T = Box] :- Strong[A]\n",
    ));
    assert!(
        errs.iter().any(|e| e.contains("unresolved name 'NoSuchSpec'")),
        "the unknown condition must be named at its own site; got {errs:?}",
    );
}

// ── WI-877: the ordering `Pair` now ships, delivered with this ticket ─
//
// WI-877 ("give `Pair` its canonical ordering") depended on this one and could not be
// stated without it — its own feedback measured that the WORK section, applied to a
// shared chain, REGRESSES equality. Its acceptance is driven here because it is this
// change that satisfies it.

/// THE WHOLE COMPARISON SURFACE FROM ONE OPERATION. `pair.anthill` declares `compare`
/// and nothing else: `gt`/`gte`/`lt`/`lte` come from `PartialOrd`'s default bodies and
/// `max`/`min` from `Ordered`'s (WI-876's per-carrier host keying is what unshadowed
/// them). Every arm here reaches `Pair.compare` through a DEFAULT body, which is a
/// different frame-producer from the direct `Ordered.compare` above — the value-directed
/// bridge — and that route had to learn the dictionary chain too.
#[test]
fn the_inherited_comparison_surface_works_from_compare_alone() {
    let src = program(
        "wi877.surface",
        "  sort Driver\n    \
         operation gt(n: Int64) -> Int64 = if PartialOrd.gt(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9)) then 1 else 0\n    \
         operation lt(n: Int64) -> Int64 = if PartialOrd.lt(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9)) then 1 else 0\n    \
         operation gte(n: Int64) -> Int64 = if PartialOrd.gte(pair(fst: 1, snd: 1), pair(fst: 1, snd: 1)) then 1 else 0\n    \
         operation lte(n: Int64) -> Int64 = if PartialOrd.lte(pair(fst: 1, snd: 1), pair(fst: 1, snd: 1)) then 1 else 0\n    \
         operation maxFst(n: Int64) -> Int64 =\n      \
         match Ordered.max(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9))\n        case pair(f, s) -> f\n    \
         operation minFst(n: Int64) -> Int64 =\n      \
         match Ordered.min(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9))\n        case pair(f, s) -> f\n  end",
    );
    // Both directions of each, so an implementation that answered a constant fails.
    assert_eq!(eval_int(&src, "wi877.surface.Driver.gt", "(2,1) > (1,9)"), 1);
    assert_eq!(eval_int(&src, "wi877.surface.Driver.lt", "…and not <"), 0);
    assert_eq!(eval_int(&src, "wi877.surface.Driver.gte", "a tie is >="), 1);
    assert_eq!(eval_int(&src, "wi877.surface.Driver.lte", "…and <="), 1);
    assert_eq!(eval_int(&src, "wi877.surface.Driver.maxFst", "max reads back the winner"), 2);
    assert_eq!(eval_int(&src, "wi877.surface.Driver.minFst", "…and min the loser"), 1);
}

/// …and the ONE-ness is asserted STRUCTURALLY, not inferred from the arms above: only
/// `compare` and `eq` resolve to a member of `Pair`; every other name in the surface
/// resolves to the SPEC's own operation. A later "fix" that wrote the six one-liners
/// back into `pair.anthill` would pass the behavioural arms and fail here.
#[test]
fn pair_supplies_only_compare_and_eq() {
    let mut kb = crate::common::load_stdlib_kb();
    let pair = kb.try_resolve_symbol("anthill.prelude.Pair").expect("Pair must exist");
    for (short, expected) in [
        ("compare", "anthill.prelude.Pair.compare"),
        ("eq", "anthill.prelude.Pair.eq"),
        ("gt", "anthill.prelude.PartialOrd.gt"),
        ("gte", "anthill.prelude.PartialOrd.gte"),
        ("lt", "anthill.prelude.PartialOrd.lt"),
        ("lte", "anthill.prelude.PartialOrd.lte"),
        ("max", "anthill.prelude.Ordered.max"),
        ("min", "anthill.prelude.Ordered.min"),
    ] {
        let short_sym = kb.intern(short);
        let got = kb
            .sort_ops_lookup(pair, short_sym)
            .map(|o| kb.qualified_name_of(o).to_string());
        assert_eq!(
            got.as_deref(),
            Some(expected),
            "`Pair`'s `{short}` must resolve to `{expected}`",
        );
    }
}

/// A BRACKET-LESS `SortedSet` over pairs sorts, from both insertion directions — the
/// end-to-end consumer WI-877 named, and the one that proves the canonical order is
/// reachable with nothing written at the use site.
#[test]
fn a_bracketless_sorted_set_of_pairs_sorts() {
    const RENDER: &str = "    import anthill.prelude.String.{concat}\n    \
        import anthill.prelude.Int64.{to_string}\n    \
        operation render(l: List[T = Pair[Int64, Int64]]) -> String =\n      \
        match l\n        case nil() -> \"\"\n        case cons(h, t) ->\n          \
        match h\n            case pair(f, s) ->\n              \
        concat(concat(\"(\", concat(to_string(f), concat(\",\", concat(to_string(s), \")\")))),\n                     \
        render(t))\n";
    let pipeline = |op: &str, first: &str, second: &str| {
        format!(
            "    operation {op}(n: Int64) -> String =\n      \
             let s = SortedSet.empty[T = Pair[Int64, Int64]]()\n      \
             render(SortedSet.toList(\n        \
             SortedSet.insert(SortedSet.insert(s, {first}), {second})))\n"
        )
    };
    let src = program(
        "wi877.sorted",
        &format!(
            "  sort Driver\n{RENDER}{}{}  end",
            pipeline("forward", "pair(fst: 2, snd: 1)", "pair(fst: 1, snd: 9)"),
            pipeline("reverse", "pair(fst: 1, snd: 9)", "pair(fst: 2, snd: 1)"),
        ),
    );
    for entry in ["forward", "reverse"] {
        match eval_fresh(&src, &format!("wi877.sorted.Driver.{entry}")) {
            Ok(Value::Str(s)) => assert_eq!(
                s, "(1,9)(2,1)",
                "inserted {entry}, the set must read back in lexicographic order",
            ),
            other => panic!("{entry}: expected a rendered set, got {other:?}"),
        }
    }
}
