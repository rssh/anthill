//! WI-1058 — the general `Expr::Apply` in a rule body is decided, and what decides it is
//! the POSITION it sits in.
//!
//! WI-1056 left this deliberately narrowed and said why: with the walk's gate widened to
//! every `Expr::Apply`, a stdlib + host-bindings load reported hundreds of errors, and
//! they were "not a backlog of small mistakes but readings the typer does not have". That
//! was right. What the ticket predicted about them was not, and the corrections are the
//! content of this ticket.
//!
//! ## The measurement, retaken 2026-08-09 (the ticket's is 2026-08-08)
//!
//! Widening `call_dispatch_shape`'s `Expr::Apply` arm with NO position awareness, on
//! stdlib + host bindings alone: **323** errors, 154 distinct. The ticket's two
//! populations were "220 unknown-functor, ~150 reflect-argument". Measured:
//!
//! | population | ticket | measured | producer |
//! |---|---|---|---|
//! | `expected List[T = Term], got <Sort>` | ~150 | **271** | ONE — the synthesized `<Sort>.induction` |
//! | `unknown apply functor: tuple` | — | **21** | the same |
//! | `<bottom>` / `match with no branches` | — | **3** | the same |
//! | `unknown apply functor: <a rule name>` | 220 | **28** | 21 hand-written rule bodies |
//!
//! **295 of the 323 come from ONE producer**, `Loader::emit_induction_rule`, whose body is
//! `ho_apply(?P, ctor(…))` and `forall_impl(tuple(binders), tuple(ihs), tuple(goal))` by
//! construction. The subgoal population is 28, not 220 — a factor of eight the other way.
//!
//! ## The readings, and why POSITION is the one idea behind all of them
//!
//! Every failure above is one name answering two questions depending on where it is
//! written, so the fix is not a list of special cases but a walk that knows the
//! difference ([`BodyPos`]):
//!
//!   * **`ho_apply`** is `BuiltinTag::HoApply` (variadic: a predicate and its arguments)
//!     in a goal, and the reflect IR ENTITY `ho_apply(predicate: Term, args: List[Term],
//!     …)` as a value. Read as the entity, `ho_apply(?P, Vec3(…))` checks a `Vec3` against
//!     `List[T = Term]`. Generalised: at goal position a resolver BUILTIN is read by the
//!     builtin.
//!   * **`tuple` / `forall_impl`** are goal CONNECTIVES, recognised through the ONE slot
//!     table (`KnowledgeBase::goal_slot_readings`) — which WI-1058 also had to teach the
//!     two readings it never carried: a discharge's ANTECEDENTS (hand-read in
//!     `assumed_body_functors` until now) and its BINDERS (written down nowhere, which is
//!     why `tuple(?f₁, …)` read as a call).
//!   * **a rule NAME applied** is a relational SUBGOAL, checked against the clauses its
//!     functor heads ([`subgoal_shape_error`]) rather than against a signature it has not
//!     got.
//!   * **a SORT-headed atom at goal position** is a TYPE or an INSTANCE CLAIM
//!     (`Modifiable[T = ?t]`), never a subgoal — its argument grammar is not a
//!     predicate's, and it is checked where it is built (`check_sort_type_args`).
//!   * **an ARROW** is a function type, minted by the pratt desugar and declared nowhere,
//!     so its whole subtree is out of the walk.
//!
//! ## What the value position taught, which the ticket had backwards
//!
//! The ticket asked for the general `Expr::Apply` to be TYPED wherever it appears. In a
//! DATA slot that is wrong three separate ways, each found by driving the suite, none
//! predicted — see [`data_functor_error`]'s doc for the citations:
//!
//!   1. it loses the EXPECTATION (`check_apply_iter`'s readings are expectation-directed;
//!      a sort name is a `Type` VALUE only in a `Type` slot) — 27 suite failures;
//!   2. it loses the SCOPE (a node under a `lambda` is typed outside its binder);
//!   3. it REWRITES the body (`holds(ite(true, 10, 20))` became `holds(10)` at LOAD, so
//!      the rule answered under `ResolveConfig { simplify: false }`).
//!
//! So a data slot gets the one check it can be given without a context: does its functor
//! NAME anything. That is exactly WI-895's remaining half, which WI-1034 handed on with
//! the words "the argument half needs its own predicate, not a wider walk" — and this is
//! that predicate, sharing `undefined_functor` with the goal half so the two positions
//! cannot disagree about which names exist. `wi894_rule_functor_scope_test`'s pin and two
//! `wi1034_undefined_rule_body_goal_test` rows were updated by this ticket, as their own
//! docs instructed.
//!
//! ## COST, measured at the acting arm (2026-08-09)
//!
//! | tier | newly decided | pre-existing | reports |
//! |---|---|---|---|
//! | stdlib + host bindings | **242** (194 data-term, 31 subgoal, 17 fact-pattern) | 33 | **0** |
//! | + `examples/` + `anthill-todo` + `anthill-testcases` | **416** (268 / 89 / 59) | 194 | **0** |
//!
//! The pre-existing column cross-checks against WI-1043's own count on the whole corpus
//! (**133** body-less spec-op sites) — the same 133, unchanged by this ticket.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each
//!
//! | test | subgoal | builtin | position walk | commitment | arrow | data check |
//! |---|---|---|---|---|---|---|
//! | `a_subgoal_with_the_wrong_arity_is_refused_naming_the_rule` | **FAILS** | ok | ok | ok | ok | ok |
//! | `a_right_arity_subgoal_and_a_multi_shape_predicate_still_load` | ok | †  | †  | ok | ok | ok |
//! | `a_subgoal_inside_a_negation_is_checked_too` | **FAILS** | ok | **FAILS** | ok | ok | ok |
//! | `a_tolerated_branch_and_a_hypothesis_are_not_shape_checked` | ok | †  | †  | **FAILS** | ok | ok |
//! | `an_induction_principle_over_a_recursive_sort_loads_and_proves` | ok | **FAILS** | **FAILS** | ok | ok | ok |
//! | `an_undefined_functor_in_a_data_slot_is_refused` | ok | †  | †  | ok | ok | **FAILS** |
//! | `a_type_application_in_a_rule_body_is_not_a_call` | ok | †  | †  | ok | **FAILS** | ok |
//! | `a_simp_redex_at_an_impossible_arity_is_refused` | ok | †  | †  | ok | ok | **FAILS** |
//! | `the_corpus_still_loads` | ok | **FAILS** | **FAILS** | ok | ok | ok |
//!
//! The six columns are the six pieces, each reverted alone: `subgoal_shape_error`
//! returning `None`; the builtin rung deleted from `call_dispatch_shape`;
//! `child_body_positions` answering `Value` for every child (no goal descent, no binder
//! row, no pattern row); `GoalCommit::checked` answering `true` everywhere;
//! `rule_body_type_term` returning `false`; `data_functor_error` returning `None`.
//!
//! **†  is COLLATERAL**: the builtin reading and the position walk are each ON THE
//! STDLIB'S LIVE PATH — 295 of the 323 reports a position-blind widening produced were the
//! synthesized induction rules alone — so backing either out stops the stdlib loading and
//! every fixture that needs a clean load breaks at the harness. That is precisely what
//! `the_corpus_still_loads` reports, and it is why that row is a real subject in two
//! columns rather than the formality it reads as. A †  cell says nothing about its column.
//!
//! THE PREDICTED TABLE WAS WRONG IN SEVEN CELLS, and one of the corrections is the most
//! useful line in this file:
//!
//!   * Six were †  cells predicted `ok` — the collateral cascade, which is easy to state
//!     and easy to forget to apply to every row that loads the stdlib.
//!   * **`the_corpus_still_loads` was predicted to FAIL under the arrow reading and does
//!     NOT.** The corpus writes no arrow type and no type application in a rule-body data
//!     slot: the whole evidence for that reading is the SUITE — 27 failures across
//!     `wi300`/`wi625`/`wi642`/`wi710`/`wi839`/`wi927`/`wi1040`/`wi1045` — exactly the
//!     shape WI-1034 met from the other side ("the corpus is silent on it; the suite is
//!     not"). Had this ticket trusted a clean corpus load as its acceptance, the reading
//!     would have shipped missing and broken every one of those programs.
//!
//! ## What the /code-review pass found, since four of the six pieces above are its work
//!
//! The first cut of this change passed the whole workspace and every corpus tier, and was
//! wrong in four ways a green suite could not show. Recorded because the SHAPE of the
//! mistakes repeats:
//!
//!   * **The type-term test was written for a design that no longer existed.** It answered
//!     `true` for any `has_kind(Sort)` functor — needed while a data slot was TYPE-CHECKED,
//!     pure width once it was not. An eponymous `sort E { entity E(…) }` and a
//!     free-standing `entity E(…)` both carry `Sort` (WI-926), so every constructor in a
//!     data slot switched the walk off for its whole subtree: `here1(K1(v: bogusB(?x)))`
//!     loaded clean beside a refused sort-nested twin, and a dot inside one stopped being
//!     dispatched — a REGRESSION, not just a missed new check. A requirement that outlives
//!     its reason reads as deliberate.
//!   * **Two exemptions were not copied from the check this one shares an authority with.**
//!     A hypothesis and a tolerated branch (`GoalCommit`) — both stated in
//!     `undefined_rule_body_goals`, both silently absent here, both refusing programs
//!     §5.3 legislates.
//!   * **The refusal named the callee as the enclosing rule**, and **`Call` still stored
//!     `type_check_node`'s rewritten node** — the third of the three reasons this file's
//!     own doc gives for not type-checking a data slot, left live in the one goal-position
//!     shape that does type-check.
//!
//! REFERENCE: WI-1056 (which measured this and stated the narrowing); WI-1043; WI-1026;
//! WI-714 (the relation arm and its rule-body gate); WI-1034 + WI-895 (the goal half of
//! the name check, and the argument half this closes); WI-710 / WI-927 (a rule-body type
//! application); `docs/kernel-language.md` §5.3;
//! `docs/design/058-implementation.md` §23.

use crate::common::{load_kb_with, try_load_kb_with};

/// The joined load errors of a source that must NOT load.
fn refusal(src: &str) -> String {
    try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal; the program loaded clean:\n{src}"))
        .join("\n")
}

// ── The SUBGOAL reading ─────────────────────────────────────────

/// THE HEADLINE. A rule-name subgoal whose ARITY no clause can match is refused, naming
/// the rule and both shapes.
///
/// Such a goal is dead: the discrimination tree hands the resolver no candidate, so the
/// conjunction silently answers nothing — indistinguishable from "the facts do not hold",
/// which is the failure mode WI-1034 closed one position over. CONTROL: before this ticket
/// the program below loaded CLEAN (`call_dispatch_shape` answered `None` for every
/// non-spec-op `Expr::Apply`, so nothing looked at it).
#[test]
fn a_subgoal_with_the_wrong_arity_is_refused_naming_the_rule() {
    let msg = refusal(
        "namespace test.wi1058.arity\n\
         \x20 import anthill.prelude.Int64\n\
         \x20 rule q1058(?x) :- ?x = 1\n\
         \x20 rule bad1058(?a, ?b) :- q1058(?a, ?b)\n\
         end\n",
    );
    assert!(
        msg.contains("q1058") && msg.contains("1 positional") && msg.contains("2 positional"),
        "the refusal must name the rule and BOTH shapes: {msg}",
    );
}

/// THE CONTROL PAIR, and the reason the check above is a rule rather than a hole: the
/// right arity loads, and so does a predicate whose clauses genuinely have DIFFERENT
/// shapes (matching any one of them is enough — the check is a proof that NO clause can
/// match, never a preference for one).
///
/// Passes with the subgoal reading backed out, by design — it is the negative control.
#[test]
fn a_right_arity_subgoal_and_a_multi_shape_predicate_still_load() {
    load_kb_with(
        "namespace test.wi1058.ok\n\
         \x20 import anthill.prelude.Int64\n\
         \x20 rule q1058ok(?x) :- ?x = 1\n\
         \x20 rule good1058(?a) :- q1058ok(?a)\n\
         \n\
         \x20 fact multi1058(1)\n\
         \x20 fact multi1058(1, 2)\n\
         \x20 rule uses_one1058(?a) :- multi1058(?a)\n\
         \x20 rule uses_two1058(?a, ?b) :- multi1058(?a, ?b)\n\
         end\n",
    );
}

/// The subgoal reading reaches inside a CONNECTIVE, which is what the position walk buys
/// over a top-level-atoms-only check. `not(…)`'s negand is a goal, so the same dead
/// subgoal written there is refused with the same message.
///
/// FAILS with the position walk backed out for a DIFFERENT reason worth naming: without
/// the goal descent the negand is DATA, and the data check finds `q1058n` perfectly well
/// declared — so nothing is reported and the assertion fails on a clean load. Two pieces,
/// two failure modes, one test. (`a_subgoal_with_the_wrong_arity…` does NOT fail there,
/// measured: a rule's top-level body atoms are seeded `Goal` by `type_rule_bodies`, so
/// only a subgoal reached THROUGH a connective needs the descent.)
#[test]
fn a_subgoal_inside_a_negation_is_checked_too() {
    let msg = refusal(
        "namespace test.wi1058.neg\n\
         \x20 import anthill.prelude.Int64\n\
         \x20 rule q1058n(?x) :- ?x = 1\n\
         \x20 fact present1058n(1)\n\
         \x20 rule bad1058n(?a) :- present1058n(?a), not(q1058n(?a, ?a))\n\
         end\n",
    );
    assert!(
        msg.contains("q1058n") && msg.contains("2 positional"),
        "a subgoal inside a negation is still a subgoal: {msg}",
    );
}

/// THE TWO POSITIONS WHERE A DEAD SUBGOAL IS *NOT* A DEFECT, both review-found, both
/// programs that §5.3 legislates and that this check refused before [`GoalCommit`].
///
/// The rule is WI-863's and WI-1034's, re-asked rather than re-decided: this walk refuses
/// a dead goal exactly where `undefined_rule_body_goals` refuses a nameless one — the
/// body's top level and inside a `not` — and tolerates it in the same three places, for
/// the same reasons. A bare `or` branch may never need to answer. A HYPOTHESIS declares
/// its own predicate, so its shape is whatever the discharge says and a same-named
/// predicate's clauses are the wrong measure entirely.
///
/// MEASURED before the fix: the discharge below was refused TWICE (antecedent and
/// consequent), and `(q | q-at-the-wrong-arity)` was refused while the same branch naming
/// NOTHING loaded clean — two dead branches, two checks, opposite verdicts.
///
/// The walk still DESCENDS into both (`an_undefined_functor_in_a_data_slot_is_refused`
/// would not fire inside one otherwise); what the position gates is the shape check alone.
#[test]
fn a_tolerated_branch_and_a_hypothesis_are_not_shape_checked() {
    load_kb_with(
        "namespace test.wi1058.tol\n\
         \x20 import anthill.prelude.Int64\n\
         \x20 fact prop1058t(1, 2)\n\
         \x20 fact seed1058t(1)\n\
         \x20 rule q1058t(?a) :- ?a = 1\n\
         \n\
         \x20 -- a HYPOTHESIS: the antecedent declares `prop1058t/1`, whatever `/2` says\n\
         \x20 rule disch1058(?a) :- seed1058t(?a), (forall(?p), prop1058t(?p) -: prop1058t(?p))\n\
         \n\
         \x20 -- a BARE disjunction branch: it may never need to answer\n\
         \x20 rule tol1058(?a) :- seed1058t(?a), (q1058t(?a) | q1058t(?a, ?a))\n\
         end\n",
    );
}

// ── The BUILTIN and CONNECTIVE readings ─────────────────────────

/// THE 295, driven rather than asserted as a clean load: a recursive sort's synthesized
/// `<Sort>.induction` is `ho_apply(?P, …)` and `forall_impl(tuple(binders), tuple(ihs),
/// tuple(consequent))`, and both the base case and the IH-using step case must still RUN.
///
/// The rule loads AND proves a property by structural induction, so a reading that merely
/// stopped erroring could not pass it. CONTROL, backing out either piece: the builtin
/// reading gone, `ho_apply(?P, i_cons(…))` types its second argument against the reflect
/// entity's `args: List[T = Term]` and this sort's induction rule is refused; the slot
/// table's `Binders` row gone, `tuple(?head, ?tail)` is data and reads as a call on a
/// functor that names nothing. Either way the STDLIB stops loading first — see this
/// file's matrix.
#[test]
fn an_induction_principle_over_a_recursive_sort_loads_and_proves() {
    let mut kb = load_kb_with(
        "namespace test.wi1058.induction\n\
         \x20 import anthill.prelude.Int64\n\
         \x20 enum IL1058\n\
         \x20   entity il_nil\n\
         \x20   entity il_cons(head: Int64, tail: IL1058)\n\
         \x20 end\n\
         \n\
         \x20 fact holds1058(il_nil)\n\
         \x20 rule holds1058(il_cons(head: ?_h, tail: ?t)) :- holds1058(?t)\n\
         end\n",
    );
    use anthill_core::kb::term::Term;
    let induction = kb
        .try_resolve_symbol("test.wi1058.induction.IL1058.induction")
        .expect("the recursive sort must have an induction rule");
    let holds = kb
        .try_resolve_symbol("test.wi1058.induction.holds1058")
        .expect("the property must be defined");
    let pred_ref = kb.alloc(Term::Ref(holds));
    let goal = kb.alloc(Term::Fn {
        functor: induction,
        pos_args: smallvec::SmallVec::from_slice(&[pred_ref]),
        named_args: smallvec::SmallVec::new(),
    });
    let solutions = kb.resolve(
        &[goal],
        &anthill_core::kb::resolve::ResolveConfig::default(),
    );
    assert!(
        !solutions.is_empty(),
        "the induction principle must PROVE `holds1058` — base case + IH-discharged step",
    );
}

// ── The DATA-slot name check ────────────────────────────────────

/// WI-895's remaining half: a compound term in a goal's ARGUMENT whose functor names
/// nothing is refused, in the goal half's voice and with its own noun ("rule-body TERM").
///
/// CONTROL: this loaded clean until this ticket, pinned by
/// `wi894_rule_functor_scope_test` (updated here) — and the second half below is what
/// makes it a scoping refusal rather than a blanket one, since the same shape with the
/// name DECLARED loads.
#[test]
fn an_undefined_functor_in_a_data_slot_is_refused() {
    let msg = refusal(
        "namespace test.wi1058.data\n\
         \x20 fact present1058d(1)\n\
         \x20 rule bad1058d(?x) :- present1058d(bogus1058(?x))\n\
         end\n",
    );
    assert!(
        msg.contains("rule-body term") && msg.contains("bogus1058"),
        "the data-slot check must name the term and say what is wrong: {msg}",
    );
    load_kb_with(
        "namespace test.wi1058.data2\n\
         \x20 entity known1058(v: anthill.prelude.Int64)\n\
         \x20 fact present1058d2(1)\n\
         \x20 rule ok1058d(?x) :- present1058d2(known1058(v: ?x))\n\
         end\n",
    );
}

/// A TYPE written in a rule body is not a call, and its interior is not values. Three
/// spellings in one fixture — a parameterized type as a goal-position instance claim, one
/// nested in a data slot, and an ARROW type — because the failure they guard against is
/// one reading applied to all three.
///
/// CONTROL, backing the arrow reading out: `arrow` / `arrow_effect` are minted by the
/// pratt desugar and declared NOWHERE, so the data-slot name check reports every arrow
/// type as a name that resolves to nothing. The two sort-headed spellings are covered by
/// a different piece — the goal-position instance-claim rung — and pass either way here;
/// they are in this fixture because a reader looking for "a type in a rule body" should
/// find all three together. This is `wi618_bare_arrow_logic_test` and
/// `wi927_bracket_surface_test`'s subject reached from the rule-body side.
///
/// THIS FIXTURE IS THE ARROW READING'S ONLY CORPUS-SHAPED WITNESS, and that is the point
/// of having it: `the_corpus_still_loads` passes with the reading backed out (measured),
/// so without this test and the 27 suite rows it protects, the whole reading would look
/// unnecessary.
#[test]
fn a_type_application_in_a_rule_body_is_not_a_call() {
    load_kb_with(
        "namespace test.wi1058.types\n\
         \x20 import anthill.prelude.{Cell, List, Int64, Bool, Modifiable}\n\
         \x20 import anthill.reflect.{is_modifiable}\n\
         \x20 rule modifiable1058(?t) :- Modifiable[T = ?t]\n\
         \x20 rule anylist1058(?t, ?b) :- eq(?b, is_modifiable(List[T = ?t]))\n\
         \x20 rule arrow1058(?t) :- ?t <=> (Int64 -> Int64)\n\
         end\n",
    );
}

/// THE ONE HOLE THE INHERITED EXEMPTION NAMED, closed. `undecidable_by_this_typer`
/// tolerates an EQUATION-INTRODUCED functor applied in a rule body (`ite` — `bool.anthill`
/// argues it cannot be an operation, since an operation evaluates both branches), and its
/// doc states exactly what that costs: *"nothing about the call itself survives, ARITY
/// INCLUDED — `rule r(?x, ?r) :- ?r = ite(?x)` loads clean against a three-argument
/// functor"*, handing the gap to this ticket by name.
///
/// A `[simp]` rewrite fires by MATCHING a stored LHS, so a redex at an arity no LHS has
/// can never fire whatever the tag says — the same proof-of-impossibility the subgoal
/// check makes, one clause source over, and `unmatchable_shape_error` is literally the
/// same function.
///
/// **THE EXEMPTION ITSELF STANDS**, and this test is not evidence that it does not:
/// deriving a redex's TYPE from its clauses is the other, much larger half, and it is not
/// delivered here — the well-formed call below still contributes no type to its enclosing
/// `=` goal. The control is the second half: a correctly-shaped `ite` still loads.
#[test]
fn a_simp_redex_at_an_impossible_arity_is_refused() {
    let msg = refusal(
        "namespace test.wi1058.eq\n\
         \x20 import anthill.prelude.{Int64, Bool}\n\
         \x20 import anthill.prelude.Bool.{ite}\n\
         \x20 rule bad1058e(?x, ?r) :- ?r = ite(?x)\n\
         end\n",
    );
    assert!(
        msg.contains("ite") && msg.contains("3 positional") && msg.contains("1 positional"),
        "the refusal must name the functor and both arities: {msg}",
    );
    // CONTROL — the well-formed redex still loads, exemption and all.
    load_kb_with(
        "namespace test.wi1058.eqok\n\
         \x20 import anthill.prelude.{Int64, Bool}\n\
         \x20 import anthill.prelude.Bool.{ite}\n\
         \x20 rule ok1058e(?c, ?r) :- ?r = ite(?c, 1, 0)\n\
         end\n",
    );
}

/// THE BLAST RADIUS, asserted rather than promised. Reads as a formality and is not: the
/// builtin reading and the position walk are each on the STDLIB's own live path — 295 of
/// the 323 reports a position-blind widening produced were the synthesized induction rules
/// alone — so this row is the real subject in two of the matrix's six columns. It is NOT a
/// subject in the one might expect: it passes with the ARROW reading backed out
/// (measured), because the corpus writes no arrow type in a rule-body data slot.
/// `a_type_application_in_a_rule_body_is_not_a_call` is that reading's witness.
///
/// The `examples/`, `anthill-todo` and `anthill-testcases` tiers were measured the same
/// way through `anthill load` (all clean); the tier this harness owns is stdlib + Rust
/// host bindings.
#[test]
fn the_corpus_still_loads() {
    load_kb_with("namespace test.wi1058.corpus\n  fact present1058c(1)\nend\n");
}
