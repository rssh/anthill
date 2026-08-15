//! WI-869 (proposal 058 §3.8, §4) — PER-PROVISION CONDITIONAL PROVISIONS:
//! `provides X[…] :- goals`, conditions scoped to ONE provision instead of to the
//! whole sort.
//!
//! WHAT A SORT-LEVEL `requires` CHAIN COULD NOT DO. It is shared by every provision
//! the sort makes, so a provider of two floors of one tower must condition them at
//! ONE strength. `anthill.prelude.Pair` needs two: it provides `PartialEq` wherever
//! its components have the partial equality and `Eq` only where they have the lawful
//! one, `PartialOrd` wherever they are partially ordered and `Ord` only where
//! they are totally ordered. With one chain the WEAKEST condition must win (else
//! `Pair` stops being a general product — `pair.anthill`'s header carries that
//! measurement) and every stronger provision then over-claims.
//!
//! AND IT WAS NOT ONLY AN OVER-CLAIM. MEASURED at WI-877 and reproduced here before
//! the fix: adding `requires Ord[A], requires Ord[B]` to `Pair`'s chain —
//! the only spelling the implementation accepted — turned
//! `PartialEq.eq(pair(fst: 1.5, snd: 1), pair(fst: 1.5, snd: 1))` into the LOAD ERROR
//! *"anthill.prelude.PartialEq.eq.dispatch: expected matching impl for per-call
//! bindings, got no impl matches"*, because a sort's chain is threaded WHOLESALE at
//! every dispatch through the carrier. `Float` provides `PartialOrd` and not
//! `Ord`, so an ordering requirement broke EQUALITY.
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
         import anthill.prelude.{{Ord, WeakOrd, PartialOrd, PartialEq, Int64, Float, \
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
/// provisions including `Ord` — a pair of FLOATS must still compare for
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
        eval_int(
            &src,
            "wi869.floateq.Driver.same",
            "a pair of floats must compare EQUAL"
        ),
        1,
    );
    assert_eq!(
        eval_int(
            &src,
            "wi869.floateq.Driver.diff",
            "…and unequal pairs must not"
        ),
        0,
        "an `eq` that answered `true` unconditionally would pass the arm above",
    );
}

/// THE OTHER HALF OF THE PAIR: the same value, the `Ord` provision, REFUSED —
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
         WeakOrd.compare(pair(fst: 1.5, snd: 1), pair(fst: 2.5, snd: 1))\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("anthill.prelude.WeakOrd.compare")
                && e.contains("unresolved: anthill.prelude.Eq[T = anthill.prelude.Float]")
        }),
        "the refusal must name the unmet component condition; WI-1109 moved which one \
         it is — `WeakOrd requires Eq`, and `Float` fails `Eq` before it could fail any \
         ordering condition, so `Eq[Float]` is now the first unmet one and the deeper \
         reason the pair cannot be compared; got {errs:?}",
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
         WeakOrd.compare(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9))\n    \
         operation sndBreaksTie(n: Int64) -> Int64 =\n      \
         WeakOrd.compare(pair(fst: 1, snd: 1), pair(fst: 1, snd: 9))\n    \
         operation equalPairs(n: Int64) -> Int64 =\n      \
         WeakOrd.compare(pair(fst: 1, snd: 1), pair(fst: 1, snd: 1))\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi869.intord.Driver.fstWins", "`fst` decides"),
        1
    );
    assert_eq!(
        eval_int(
            &src,
            "wi869.intord.Driver.sndBreaksTie",
            "`snd` breaks a `fst` tie"
        ),
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
        eval_int(
            &src,
            "wi869.tower.Driver.weakOnWeak",
            "`Weak[Box[OnlyWeak]]` holds"
        ),
        7,
        "the value comes from `OnlyWeak.weak`, so the call really reached the \
         component's own member and did not stop at `Box`",
    );
    // The STRONG provision is conditioned on the STRONG goal, so a component that has
    // both floors is admitted…
    assert_eq!(
        eval_int(
            &src,
            "wi869.tower.Driver.strongOnBoth",
            "`Strong[Box[Both]]` holds"
        ),
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
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.bare", "an unconditioned `Weak`"),
        7
    );
    assert_eq!(
        eval_int(
            &src,
            "wi869.tower.Driver.bareStrong",
            "…and an unconditioned `Strong`"
        ),
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
    assert_eq!(
        eval_int(
            &src,
            "wi869.tower.Driver.weakOnWeak",
            "the shared slot serves `Weak`"
        ),
        7
    );
    assert_eq!(
        eval_int(
            &src,
            "wi869.tower.Driver.strongOnBoth",
            "…and the same slot serves `Strong`"
        ),
        1,
        "a slot recorded as owned by only the FIRST provision would be `Unavailable` \
         under the second, and `Box.strong`'s read of it would be refused",
    );
}

/// A CONDITION SLOT IS EVIDENCE, and it composes: `Pair.compare`'s component compares
/// go through the `Ord` provision's own slots, so a pair whose component is itself
/// a pair orders RECURSIVELY. Asserted because `pair.anthill`'s header claims it, and
/// because the inner pair is where the outer provision's condition
/// `Ord[A = Pair[Int64, Int64]]` has to resolve through `Pair`'s own provision —
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
         WeakOrd.compare(pair(fst: pair(fst: 1, snd: 2), snd: 7),\n                      \
         pair(fst: pair(fst: 1, snd: 3), snd: 7))\n    \
         operation outerSndDecides(n: Int64) -> Int64 =\n      \
         WeakOrd.compare(pair(fst: pair(fst: 1, snd: 2), snd: 9),\n                      \
         pair(fst: pair(fst: 1, snd: 2), snd: 7))\n  end",
    );
    assert_eq!(
        eval_int(
            &src,
            "wi869.nested.Driver.innerDecides",
            "the INNER pair breaks the tie"
        ),
        -1,
    );
    assert_eq!(
        eval_int(
            &src,
            "wi869.nested.Driver.outerSndDecides",
            "…and `snd` breaks a full `fst` tie"
        ),
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
    let src = tower(PER_PROVISION).replace(
        "case box(v) -> Weak.weak(v)",
        "case box(v) -> Strong.strong(v)",
    );
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
        eval_int(
            &src,
            "wi869.tower.Driver.weakOnWeak",
            "the sort-level condition holds"
        ),
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
    assert_eq!(
        eval_int(&src, "wi869.tower.Driver.weakOnWeak", "the weak floor runs"),
        7
    );
    assert_eq!(
        eval_int(
            &src,
            "wi869.tower.Driver.strongOnBoth",
            "…and so does the strong one"
        ),
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
        errs.iter()
            .any(|e| e.contains("unresolved name 'NoSuchSpec'")),
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
/// `max`/`min` from `Ord`'s (WI-876's per-carrier host keying is what unshadowed
/// them). Every arm here reaches `Pair.compare` through a DEFAULT body, which is a
/// different frame-producer from the direct `WeakOrd.compare` above — the value-directed
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
         match WeakOrd.max(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9))\n        case pair(f, s) -> f\n    \
         operation minFst(n: Int64) -> Int64 =\n      \
         match WeakOrd.min(pair(fst: 2, snd: 1), pair(fst: 1, snd: 9))\n        case pair(f, s) -> f\n  end",
    );
    // Both directions of each, so an implementation that answered a constant fails.
    assert_eq!(
        eval_int(&src, "wi877.surface.Driver.gt", "(2,1) > (1,9)"),
        1
    );
    assert_eq!(eval_int(&src, "wi877.surface.Driver.lt", "…and not <"), 0);
    assert_eq!(eval_int(&src, "wi877.surface.Driver.gte", "a tie is >="), 1);
    assert_eq!(eval_int(&src, "wi877.surface.Driver.lte", "…and <="), 1);
    assert_eq!(
        eval_int(
            &src,
            "wi877.surface.Driver.maxFst",
            "max reads back the winner"
        ),
        2
    );
    assert_eq!(
        eval_int(&src, "wi877.surface.Driver.minFst", "…and min the loser"),
        1
    );
}

/// …and the ONE-ness is asserted STRUCTURALLY, not inferred from the arms above: only
/// `compare` and `eq` resolve to a member of `Pair`; every other name in the surface
/// resolves to the SPEC's own operation. A later "fix" that wrote the six one-liners
/// back into `pair.anthill` would pass the behavioural arms and fail here.
#[test]
fn pair_supplies_only_compare_and_eq() {
    let mut kb = crate::common::load_stdlib_kb();
    let pair = kb
        .try_resolve_symbol("anthill.prelude.Pair")
        .expect("Pair must exist");
    for (short, expected) in [
        ("compare", "anthill.prelude.Pair.compare"),
        ("eq", "anthill.prelude.Pair.eq"),
        ("gt", "anthill.prelude.PartialOrd.gt"),
        ("gte", "anthill.prelude.PartialOrd.gte"),
        ("lt", "anthill.prelude.PartialOrd.lt"),
        ("lte", "anthill.prelude.PartialOrd.lte"),
        ("max", "anthill.prelude.WeakOrd.max"),
        ("min", "anthill.prelude.WeakOrd.min"),
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

// ── WI-1033: the conditions are FACTS, and they are checked ──────────

/// A local tower with an EXTRA spec nothing requires, so the unsound spelling breaks
/// ENTAILMENT and nothing else — `Ord[E]` stays declared, so `compare`'s body keeps
/// the evidence it reads and no coverage error muddies the measurement.
fn cell_tower(eq_cond: &str) -> String {
    format!(
        "\nnamespace wi1033.cell\n  \
         import anthill.prelude.{{Bool, Int64, PartialEq, Eq, PartialOrd, Ord, WeakOrd}}\n\
  sort Lawful\n    sort T = ?\n    operation witness(x: T) -> Int64\n  end\n\
  enum Cell\n    sort E = ?\n    entity cell(v: E)\n    \
    provides PartialEq[Cell] :- PartialEq[E]\n    \
    provides Eq[Cell] :- {eq_cond}\n    \
    provides PartialOrd[Cell] :- PartialOrd[E]\n    \
    provides WeakOrd[Cell] :- WeakOrd[E]\n    \
    provides Ord[Cell] :- Ord[E]\n    \
    operation eq(a: Cell, b: Cell) -> Bool =\n      \
      match a\n        case cell(x) ->\n          match b\n            case cell(y) -> PartialEq.eq(x, y)\n    \
    operation compare(a: Cell, b: Cell) -> Int64 =\n      \
      match a\n        case cell(x) ->\n          match b\n            case cell(y) -> WeakOrd.compare(x, y)\n  end\nend\n"
    )
}

/// A CONDITIONAL PROVISION CERTIFIED BY A CONDITIONAL ONE MUST ENTAIL IT. The
/// self-provision arm of `check_provider_requires` accepts `Ord[Cell]` because the
/// carrier provides the `Eq[Cell]` that `Ord` requires — and once conditions are
/// per-provision, that is only sound where `Ord[Cell]` HOLDING forces `Eq[Cell]` to.
/// The arm's original justification ("the element-conditionality is already inherited
/// from the outer provision") held by construction when a carrier had one chain; it is
/// now a claim about two independent lists.
///
/// The unsound spelling conditions `Eq[Cell]` on a spec `Ord` does not require, so
/// `Ord[Cell]` would be claimed where the `Eq` it needs does not hold.
#[test]
fn a_provision_certified_by_a_weaker_conditioned_one_is_refused() {
    let errs = load_errs(&cell_tower("Lawful[E]"));
    assert!(
        errs.iter().any(|e| {
            e.contains(
                "provides 'anthill.prelude.Ord', which requires \
                        'anthill.prelude.Eq'",
            ) && e.contains("DOES provide")
                && e.contains("`wi1033.cell.Lawful[T = wi1033.cell.Cell.E]`")
        }),
        "the refusal must name the UNENTAILED condition, and must not say the carrier \
         does not provide `Eq` — it does, just too weakly; got {errs:?}",
    );
}

/// THE CONTROL, and it is what says the check discriminates rather than refusing every
/// conditional tower: the same carrier with `Eq[Cell] :- Eq[E]` loads clean, because
/// `Ord[E]` transitively requires `Eq[E]` and so entails it.
#[test]
fn a_provision_whose_conditions_entail_the_inner_ones_loads() {
    if let Err(errs) = crate::common::try_load_kb_with(&cell_tower("Eq[E]")) {
        panic!(
            "`Ord[E]` requires `Eq[E]`, so it entails the `Eq[Cell]` condition and \
             this must load; got {errs:?}"
        );
    }
}

/// THE CONDITIONS ARE OBSERVABLE TO THE REFLECT LAYER — the point of WI-1033, and
/// asserted through an actual SLD QUERY over `anthill.reflect.typing.provides_when`
/// rather than through the Rust fact API, because "observable" means observable to
/// anthill. Before this they lived in a KB side table with exactly one Rust reader; no
/// rule and no fact-walking check could see them.
///
/// Driven on the stdlib's own `Pair`, whose four provisions carry two conditions each.
#[test]
fn a_conditional_provisions_goals_answer_a_reflect_query() {
    use anthill_core::kb::term::{Term, Var};
    let mut kb = crate::common::load_stdlib_kb();
    let pair = kb.resolve_qualified_name_term("anthill.prelude.Pair");
    let mk_var = |kb: &mut anthill_core::kb::KnowledgeBase, n: &str| {
        let sym = kb.intern(n);
        let vid = kb.fresh_var(sym);
        kb.alloc(Term::Var(Var::Global(vid)))
    };
    let (v_spec, v_cond) = (mk_var(&mut kb, "spec"), mk_var(&mut kb, "cond"));
    let functor = kb.resolve_symbol("anthill.reflect.typing.provides_when");
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: smallvec::SmallVec::from_slice(&[pair, v_spec, v_cond]),
        named_args: smallvec::SmallVec::new(),
    });
    let solutions = kb.resolve(&[goal], &Default::default());
    // `Pair` writes FIVE conditioned provisions of two goals each — WI-1109 added
    // `provides WeakOrd[Pair] :- WeakOrd[A], WeakOrd[B]` beside the other four, because
    // a lexicographic pair is weakly ordered iff both components are, a strictly weaker
    // condition than the `Ord` one. Asserted as a COUNT and not merely `!is_empty()`: a
    // rule that dropped the `provided` join would still answer, and would answer the
    // same ten rows for every spec.
    assert_eq!(
        solutions.len(),
        10,
        "`provides_when(Pair, ?spec, ?cond)` must answer once per condition of each of \
         `Pair`'s five provisions",
    );
}

/// …and the same facts, read through the Rust API, are JOINED to their own provision.
/// The control the query above cannot give: a count is blind to which condition landed
/// under which provision.
#[test]
fn each_condition_is_joined_to_its_own_provision() {
    use anthill_core::kb::term::Term;
    let kb = crate::common::load_stdlib_kb();
    let cond = kb
        .try_resolve_symbol("anthill.reflect.ProvidesConditionInfo")
        .expect("the entity must be registered");
    let base_qn = |t| match kb.get_term(t) {
        Term::Fn {
            functor, pos_args, ..
        } => match pos_args.first().map(|a| kb.get_term(*a)) {
            // A `SortView(Base, …)` wrapper carries the base in pos_args[0].
            Some(Term::Fn { functor: b, .. }) | Some(Term::Ref(b)) => {
                Some(kb.qualified_name_of(*b).to_string())
            }
            _ => Some(kb.qualified_name_of(*functor).to_string()),
        },
        Term::Ref(f) | Term::Ident(f) => Some(kb.qualified_name_of(*f).to_string()),
        _ => None,
    };
    let mut pairs: Vec<(String, String)> = kb
        .rules_by_functor(cond)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .filter_map(|rid| kb.fact_head_named_args(rid))
        .filter_map(|named| {
            let get = |k: &str| {
                named
                    .iter()
                    .find(|(s, _)| kb.local_name_of(*s) == k)
                    .map(|(_, t)| *t)
            };
            let owner = match kb.get_term(get("sort_ref")?) {
                Term::Fn { functor, .. } | Term::Ref(functor) => {
                    kb.qualified_name_of(*functor).to_string()
                }
                _ => return None,
            };
            if owner != "anthill.prelude.Pair" {
                return None;
            }
            Some((base_qn(get("provided")?)?, base_qn(get("condition")?)?))
        })
        .collect();
    pairs.sort();
    pairs.dedup();
    // Each of `Pair`'s four provisions is conditioned on its OWN floor at both
    // components — exactly the shape a shared chain could not express.
    for spec in [
        "anthill.prelude.PartialEq",
        "anthill.prelude.Eq",
        "anthill.prelude.PartialOrd",
        "anthill.prelude.Ord",
    ] {
        assert!(
            pairs.iter().any(|(p, c)| p == spec && c == spec),
            "`provides {spec}[Pair] :- {spec}[…]` must be readable as a fact; \
             found {pairs:?}",
        );
    }
    // …and NOT the cross pairing: a reader that ignored `provided` and merely listed
    // every condition of the carrier would pass the loop above and fail here.
    assert!(
        !pairs
            .iter()
            .any(|(p, c)| p == "anthill.prelude.PartialEq" && c == "anthill.prelude.Ord"),
        "each condition must be joined to ITS OWN provision; found {pairs:?}",
    );
}

// ── WI-1033 review: the entailment rule's quantifiers and pairing ────
//
// Three shapes the FIRST cut of `conditions_entail` got wrong, each measured. They are
// here rather than in prose because every one of them loaded (or refused) silently.

/// A two-parameter tower, so the check cannot pass by comparing binding values as a
/// SET. `Big[X, Y] requires Small[X, Y]`; `Hi` requires `Lo`.
fn permuted(inner_cond: &str) -> String {
    format!(
        "\nnamespace wi1033.perm\n  import anthill.prelude.{{Int64}}\n\
  sort Small\n    sort X = ?\n    sort Y = ?\n    operation sm(a: X, b: Y) -> Int64\n  end\n\
  sort Big\n    sort X = ?\n    sort Y = ?\n    requires Small[X = X, Y = Y]\n    \
    operation bg(a: X, b: Y) -> Int64\n  end\n\
  sort Lo\n    sort T = ?\n    operation lo(x: T) -> Int64\n  end\n\
  sort Hi\n    sort T = ?\n    requires Lo[T = T]\n    operation hi(x: T) -> Int64\n  end\n\
  enum C\n    sort P = ?\n    sort Q = ?\n    entity c(p: P, q: Q)\n    \
    provides Hi[T = C] :- Big[X = P, Y = Q]\n    \
    provides Lo[T = C] :- {inner_cond}\n    \
    operation hi(x: C) -> Int64 = 1\n    operation lo(x: C) -> Int64 = 1\n  end\nend\n"
    )
}

/// A PERMUTED inner condition must be REFUSED: `Big[X=P, Y=Q]` requires
/// `Small[X=P, Y=Q]`, not `Small[X=Q, Y=P]`. The first cut compared the two conditions'
/// binding VALUES as a sorted set — `{P,Q} == {Q,P}` — and accepted it, certifying `Hi`
/// on an `Lo` its own condition does not imply.
#[test]
fn a_permuted_inner_condition_is_not_entailed() {
    let errs = load_errs(&permuted("Small[X = Q, Y = P]"));
    assert!(
        errs.iter().any(|e| e.contains("do not entail")),
        "swapping the inner condition's parameters must break entailment; got {errs:?}",
    );
    // THE CONTROL: the same tower with the pairing intact loads. Without it this arm
    // would pass for a check that refused every two-parameter condition.
    if let Err(errs) = crate::common::try_load_kb_with(&permuted("Small[X = P, Y = Q]")) {
        panic!("the correctly-paired condition IS entailed and must load; got {errs:?}");
    }
}

/// AN OUTER CONDITION WITH MORE PARAMETERS THAN THE INNER still entails it:
/// `Big[X=P, Y=Q]` transitively requires `Small[X=P, Y=Q]`, so it entails a `Small`
/// condition even though the two mention different numbers of the carrier's params.
/// The set comparison refused this (`[P,Q] != [P]` for the one-param case), which is a
/// FALSE refusal of a correct program.
#[test]
fn an_outer_condition_richer_than_the_inner_still_entails_it() {
    let src = "\nnamespace wi1033.rich\n  import anthill.prelude.{Int64}\n\
  sort E1\n    sort K = ?\n    operation e1(x: K) -> Int64\n  end\n\
  sort M2\n    sort K = ?\n    sort V = ?\n    requires E1[K = K]\n    \
    operation m2(a: K, b: V) -> Int64\n  end\n\
  sort Lo\n    sort T = ?\n    operation lo(x: T) -> Int64\n  end\n\
  sort Hi\n    sort T = ?\n    requires Lo[T = T]\n    operation hi(x: T) -> Int64\n  end\n\
  enum D\n    sort P = ?\n    sort Q = ?\n    entity d(p: P, q: Q)\n    \
    provides Hi[T = D] :- M2[K = P, V = Q]\n    \
    provides Lo[T = D] :- E1[K = P]\n    \
    operation hi(x: D) -> Int64 = 1\n    operation lo(x: D) -> Int64 = 1\n  end\nend\n";
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("`M2[K=P, V=Q]` requires `E1[K=P]`, so it entails it; got {errs:?}");
    }
}

/// TWO CLAUSES PROVIDING ONE SPEC ARE ALTERNATIVES, not a conjunction. Adding a second
/// way for `Lo[D]` to hold can only WIDEN where it holds, so it must never turn a clean
/// load into a refusal — which is what grouping conditions by the provided BASE did.
#[test]
fn a_second_clause_for_one_spec_only_widens() {
    let tower = |extra: &str| {
        format!(
            "\nnamespace wi1033.alt\n  import anthill.prelude.{{Int64}}\n\
  sort SA\n    sort T = ?\n    operation sa(x: T) -> Int64\n  end\n\
  sort SB\n    sort T = ?\n    operation sb(x: T) -> Int64\n  end\n\
  sort Lo\n    sort T = ?\n    operation lo(x: T) -> Int64\n  end\n\
  sort Hi\n    sort T = ?\n    requires Lo[T = T]\n    operation hi(x: T) -> Int64\n  end\n\
  enum D\n    sort P = ?\n    sort Q = ?\n    entity d(p: P, q: Q)\n    \
    provides Hi[T = D] :- SA[T = P]\n    \
    provides Lo[T = D] :- SA[T = P]\n{extra}    \
    operation hi(x: D) -> Int64 = 1\n    operation lo(x: D) -> Int64 = 1\n  end\nend\n"
        )
    };
    // The control: one adequate clause loads.
    if let Err(errs) = crate::common::try_load_kb_with(&tower("")) {
        panic!("the adequate clause alone must load; got {errs:?}");
    }
    // …and a second, independent way for `Lo[D]` to hold must not break it.
    if let Err(errs) =
        crate::common::try_load_kb_with(&tower("    provides Lo[T = D] :- SB[T = Q]\n"))
    {
        panic!(
            "a second `Lo` clause is an ALTERNATIVE — it can only widen where `Lo[D]` \
             holds, so it cannot make the program refuse; got {errs:?}"
        );
    }
}
