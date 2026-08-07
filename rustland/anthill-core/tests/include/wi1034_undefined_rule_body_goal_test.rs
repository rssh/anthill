//! WI-1034 (and the goal-position half of **WI-895**) — a rule-body goal whose
//! functor names nothing is refused at LOAD, naming the goal and its span.
//!
//! Such a goal interns to a symbol with no clause, no operation record and no
//! builtin, so it can never match: the conjunction it sits in is dead and every rule
//! containing it silently answers `[]`. Nothing fails at run time — the rule just
//! never fires — which is exactly why the loader is the only site that can be loud.
//!
//! **The spec already legislated this.** §5.3 "Naming one from elsewhere": *"Without
//! one of those, a bare use is refused in an operation body (unknown functor). In a
//! rule body it is not yet refused — it interns bare and silently fails to match: a
//! known gap (WI-895), not the intended design."* So the decision here was never
//! WHETHER, only the predicate and the descent.
//!
//! ## The ticket's own triage was wrong about two of its three categories
//!
//! WI-1034 was filed off a probe that reported "20 dangling rule-body goals in stdlib
//! alone (25 with examples), over 5 distinct names", and concluded that "at least two
//! of its categories are LEGITIMATE, so a naive 'no clauses => refuse' rule is wrong".
//! The second clause is true; the first counted a naive predicate's output.
//! Re-measured through the one the KB already owns — `undefined_functor`
//! (WI-754/WI-863/WI-878), which consults `kind_of` and exempts resolver markers by
//! name AND arity — plus the discrimination-tree backstop:
//!
//! | corpus | ticket's probe | this predicate |
//! |---|---|---|
//! | stdlib + rust bindings | 20 over 5 names | **0** |
//! | + anthill-testcases | — | **0** |
//! | + anthill-todo | — | **0** |
//! | + examples | 25 | **4**, all in `webots-modelling/lf1/safety_gps.anthill` |
//!
//!   * `forall_impl` (17 of the 20) is a resolver scoping marker — exempt by the
//!     shared `is_scoping_marker`, the same authority the resolver dispatches on.
//!   * `anthill.reflect.typing.DefaultProvider` is an ENTITY. The ticket said its
//!     facts land "after this check would run"; irrelevant — a declaration answers
//!     `kind_of` whether or not any fact exists, so this needs no ordering promise.
//!   * `anthill.examples.lf1.safety.common.RealVelocity`, listed as genuinely
//!     dangling, is an entity declared 13 lines above its use. Not dangling at all.
//!   * The genuinely-dangling category was real, and the repair differed per name:
//!     `distance_at_step` is a `safety_common` rule `safety_gps` forgot to IMPORT;
//!     `observed_pose_at` was documented in `safety_common`'s comments and DECLARED
//!     NOWHERE, so `gps_drift_axiom` — that model's single physics→controller bridge
//!     — could never fire. Both fixed with the check.
//!
//! ## What the corpus could not decide, and the fixtures did
//!
//! Whether to walk a BARE `or` / `push_choice` branch and a bounded quantifier's
//! body. The wider walk was implemented and measured FIRST: identical `0` on every
//! corpus above, so the corpus is silent on it. The suite is not —
//! `push_choice_test`'s two semantics fixtures name an undefined branch on purpose,
//! which is the shape WI-863's tolerance was written for ("a branch may fail while
//! its sibling succeeds"). The descent is therefore the query walk's exactly: the
//! body's top-level atoms plus everything inside a `not`.
//!
//! ## What fails per piece — MEASURED by backing each one out, not predicted
//!
//! | test | whole check | marker exempt | hypothesis exempt | `not` descent | descent widened |
//! |---|---|---|---|---|---|
//! | `a_goal_naming_nothing_is_refused_and_located` | **FAILS** | **FAILS** | ok | ok | ok |
//! | `a_goal_inside_a_negation_is_refused_too` | **FAILS** | ok | ok | **FAILS** | ok |
//! | `one_dangling_goal_reports_once_across_a_multi_head_rule` | **FAILS** | **FAILS** | ok | ok | ok |
//! | `a_synthesized_induction_marker_still_loads` | ok | **FAILS** | ok | ok | ok |
//! | `a_functor_this_rule_assumes_still_loads` | ok | **FAILS** | **FAILS** | ok | ok |
//! | `a_bare_or_branch_and_a_quantifier_body_are_left_to_resolution` | ok | **FAILS** | ok | ok | **FAILS** |
//! | `a_defined_functor_with_no_matching_facts_still_loads` | ok | **FAILS** | ok | ok | ok |
//! | `an_undefined_name_in_a_data_slot_is_not_a_goal` | ok | **FAILS** | ok | ok | ok |
//! | `a_user_functor_named_tuple_is_not_a_conjunction_wrapper` | ok | **FAILS** | ok | ok | ok |
//! | `an_undefined_name_under_a_boolean_and_is_not_a_goal` | ok | **FAILS** | ok | ok | ok |
//! | `the_corpus_still_loads` | ok | **FAILS** | ok | ok | ok |
//!
//! Read the columns, not the rows. Only THREE tests measure the check itself; the
//! other six each own one exemption or one descent edge, which is what they are for
//! — a suite where every test failed on every back-out would tell you the check
//! exists and nothing about where its boundaries are.
//!
//! The `marker exempt` column is all-FAILS because the STDLIB stops loading without
//! it (17 synthesized `forall_impl`s), so every fixture that loads the stdlib goes
//! with it — including the controls. That is the exemption's real measurement: it is
//! not defensive, it is on the live path.
//!
//! Outside this file: `wi1026_…::a_bare_goal_naming_nothing_is_refused_at_load` (the
//! row WI-1026 pinned and handed here) fails on the whole check;
//! `push_choice_test`'s two both-branches / one-branch fixtures fail when the descent
//! is widened; `forall_impl_resolve_test::t4_assumption_does_not_leak_to_next_body_goal`
//! fails when the hypothesis exemption goes; and `anthill-smt-gen`'s
//! `cross_namespace_inline_test::unresolved_functor_is_a_loud_error` asserts the load
//! half of this refusal directly.
//!
//! Three rows have no column of their own, and each says why at its own site.
//! `an_undefined_name_in_a_data_slot_is_not_a_goal`: the walk reaches a data slot
//! through no switch, only by someone replacing `body_goal_children` with a
//! whole-subtree walk — the edit it exists to fail on, and the one the ticket's own
//! ~313-name probe took. `a_user_functor_named_tuple_is_not_a_conjunction_wrapper`
//! FAILS when the `tuple` wrapper test is applied at every node instead of only where
//! the loader puts one (**measured**, by reinstating that shape).
//! `an_undefined_name_under_a_boolean_and_is_not_a_goal` passes with `and` back in the
//! connective list, and that is the measurement rather than a gap — see its doc.
//!
//! The last three rows arrived from the `/code-review` pass, which found the wrapper
//! test applied too widely, the `and` premise, and an occurrence-only child read that
//! silently dropped a spliced connective's children (fixed by carrying `(Value,
//! SourceSpan)`; the drop would have made `assumed_body_functors` collect zero
//! hypotheses and FALSELY REFUSE). None of the three had a test before that pass.
//!
//! REFERENCE: WI-1026 (which filed this); WI-895 (the same gap, filed earlier, whose
//! ARGUMENT-position half stays open); WI-754 / WI-863 / WI-878 (the shared head
//! test); `docs/kernel-language.md` §5.3.

/// The single load-error message of `src`, which must NOT load. Panics if it loads
/// clean — "the program loaded" must never read as a pass in a suite about refusals.
fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal; the program loaded clean:\n{src}"))
        .join("\n")
}

/// THE HEADLINE. A top-level rule-body goal naming nothing is refused, and the
/// refusal carries BOTH things the author needs: the name, and where it is written.
///
/// `line:col` and not a byte offset, because the check runs at the loader and hands
/// the goal occurrence's own `SourceSpan` to `located_in_kb_source` — the WI-745
/// channel. A bare offset here would be the fallback WI-745 removed.
#[test]
fn a_goal_naming_nothing_is_refused_and_located() {
    let src = "namespace test.wi1034.headline\n\
               \x20 fact present(1)\n\
               \x20 rule answer(?x) :- present(?x), absent1034(?x)\n\
               end\n";
    let msg = refusal(src);
    assert!(msg.contains("names nothing"), "{msg}");
    assert!(msg.contains("absent1034"), "the goal must be NAMED: {msg}");
    let (loc, _) = msg
        .split_once(": ")
        .unwrap_or_else(|| panic!("expected a `line:col: message` rendering, got: {msg}"));
    let (line, col) = loc
        .split_once(':')
        .unwrap_or_else(|| panic!("expected `line:col`, got `{loc}` in: {msg}"));
    assert_eq!(line, "3", "the refusal must point at the line the goal is written on: {msg}");
    assert!(col.parse::<u32>().is_ok(), "expected a numeric column, got `{col}` in: {msg}");
}

/// THE CONTROL THIS REFUSAL MUST NOT CONSUME, and the reason a "no clauses => refuse"
/// rule is wrong: a functor that IS declared but has no matching row answers `[]`
/// legitimately, and that is the ordinary case for every fact table in the tree.
///
/// Driven, not merely loaded: the goal resolves and answers nothing, which is the
/// behaviour the refusal must leave alone. Passes with the change backed out, by
/// design — it is what a widened predicate would break.
#[test]
fn a_defined_functor_with_no_matching_facts_still_loads() {
    let ns = "test.wi1034.control";
    let src = format!(
        "namespace {ns}\n\
         \x20 fact present(1)\n\
         \x20 rule answer(?x) :- present(?x), present(99)\n\
         end\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert!(
        crate::common::query_unary(&mut kb, &format!("{ns}.answer")).is_empty(),
        "a declared functor with no matching row must still answer nothing, silently",
    );
}

/// The goal is refused wherever the SEARCH COMMITS to it, so a `not` is entered —
/// and this is the position where silence is worst. NAF over an undefined predicate
/// resolves the negand to a complete-empty search and flips it to a confident `true`,
/// asserting a negation about a name that exists nowhere. Driven as a nested `not`,
/// so the descent (and not just the top-level test) is what is measured.
#[test]
fn a_goal_inside_a_negation_is_refused_too() {
    let src = "namespace test.wi1034.naf\n\
               \x20 fact present(1)\n\
               \x20 rule answer(?x) :- present(?x), not(not(absent1034naf(?x)))\n\
               end\n";
    let msg = refusal(src);
    assert!(msg.contains("absent1034naf"), "WI-863's descent must reach it: {msg}");
}

/// …AND THE POSITIONS IT DELIBERATELY DOES NOT ENTER, driven as a matched pair with
/// the test above so the line between them is asserted and not just documented.
///
/// A bare `or` branch and a bounded quantifier's body may never run, so an unmatched
/// name there does not corrupt the answer that IS produced — WI-863's reason, which
/// transfers to a rule body unchanged. Both arms LOAD, and the `or` arm is DRIVEN to
/// its surviving sibling's answer, because "it loads" alone would pass equally if the
/// dangling branch had silently eaten the rule.
///
/// This is the arm the corpus could not choose: the wide walk reported the same zero
/// over stdlib, testcases and anthill-todo. `push_choice_test`'s two semantics
/// fixtures are what decided it, and this pins the decision where WI-1034 can be read.
#[test]
fn a_bare_or_branch_and_a_quantifier_body_are_left_to_resolution() {
    let ns = "test.wi1034.tolerated";
    let src = format!(
        "namespace {ns}\n\
         \x20 fact present(7)\n\
         \x20 rule answer(?x) :- present(?x) | absent1034or(?x)\n\
         \x20 rule quantified(?x) :- present(?x), (forall ?e in []: absent1034all(?e))\n\
         end\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    let raw = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    assert_eq!(raw.len(), 1, "exactly the surviving branch answers: {raw:?}");
    assert!(raw[0].1, "and definitely, not as a residual: {raw:?}");
    // Rendered, not matched on `Value::Int`: an `or` answer comes back through the
    // resolver as a `Value::Term` carrier, and a carrier test here would be asserting
    // which carrier the disjunction happens to use rather than what it answered.
    let rendered = match &raw[0].0 {
        anthill_core::eval::Value::Term { id, .. } => {
            anthill_core::persistence::print::TermPrinter::over(&kb).print_term(*id)
        }
        other => format!("{other:?}"),
    };
    assert_eq!(rendered, "7", "the surviving branch must answer its own row: {raw:?}");
    let vacuous = crate::common::query_unary(&mut kb, &format!("{ns}.quantified"));
    assert_eq!(vacuous.len(), 1, "a quantifier over [] is vacuously true: {vacuous:?}");
}

/// A RESOLVER SCOPING MARKER carries no clause BY DESIGN, and the loader synthesizes
/// one for every induction proof (17 in stdlib alone), so the exemption is on the
/// live path rather than defensive. Exempt through the shared
/// `resolve::is_scoping_marker` — the same authority the resolver dispatches on, so
/// the two cannot disagree about what a marker is.
///
/// Driven through a sort with a RECURSIVE constructor, because that is what makes
/// `emit_induction_rule` emit the `forall_impl` form at all; a flat enum emits plain
/// `ho_apply` goals and would exempt nothing.
#[test]
fn a_synthesized_induction_marker_still_loads() {
    let ns = "test.wi1034.marker";
    let src = format!(
        "namespace {ns}\n\
         \x20 import anthill.prelude.Int64\n\
         \x20 sort Nat1034\n\
         \x20   entity zero1034\n\
         \x20   entity succ1034(pred: Nat1034)\n\
         \x20 end\n\
         end\n"
    );
    let kb = crate::common::load_kb_with(&src);
    assert!(
        kb.try_resolve_symbol(&format!("{ns}.Nat1034.induction")).is_some(),
        "the fixture must actually emit an induction rule, else it exempts nothing",
    );
}

/// A HYPOTHESIS is a binding occurrence. `(forall(?x), P(?x) -: Q(?x))` assumes `P`
/// into the resolver's frame and discharges `Q` against it, so a predicate that
/// exists ONLY as a hypothesis legitimately carries no clause anywhere — refusing it
/// would reject the construct itself.
///
/// The exemption is per RULE and not per discharge, and this fixture is why: it
/// assumes `hyp1034` inside the discharge and asks it again OUTSIDE, which must LOAD
/// (the name exists for this rule) and must FAIL (the assumption's scope ended).
/// Narrowing the exemption to the discharge's interior refuses this program and takes
/// `forall_impl_resolve_test::t4_assumption_does_not_leak_to_next_body_goal` — the
/// only driver of the scoping invariant — with it.
#[test]
fn a_functor_this_rule_assumes_still_loads() {
    let ns = "test.wi1034.hyp";
    let src = format!(
        "namespace {ns}\n\
         \x20 sort Stub1034\n\
         \x20   entity stub1034\n\
         \x20 end\n\
         \x20 rule discharged(?d) :- (forall(?x), hyp1034(?x) -: hyp1034(?x))\n\
         \x20 rule leaked(?d) :- (forall(?x), hyp1034(?x) -: eq(1, 1)), hyp1034(?d)\n\
         end\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert!(
        !crate::common::query_unary(&mut kb, &format!("{ns}.discharged")).is_empty(),
        "the hypothesis must discharge its own consequent",
    );
    assert!(
        crate::common::query_unary(&mut kb, &format!("{ns}.leaked")).is_empty(),
        "…and must NOT leak past the discharge — the invariant the exemption preserves",
    );
}

/// A DATA SLOT is not a goal, so a name inside a goal's ARGUMENT is not walked. This
/// is the boundary between what WI-1034 closed and what WI-895 still leaves open:
/// `holds(ite(true, 10, 20))` with `ite` un-imported interns bare and never fires as
/// a `[simp]` redex, and that silence survives here.
///
/// Asserted as an EXCLUSION rather than left implicit, because the difference is one
/// walk step: the argument position is where the ticket's probe found ~313 names and
/// the goal-position count found 20, and a walk that drifted into it would refuse
/// every constructor written in an argument. Its own pin is
/// `wi894_rule_functor_scope_test::a_rule_body_does_not_yet_refuse_an_unimported_functor`.
#[test]
fn an_undefined_name_in_a_data_slot_is_not_a_goal() {
    let src = "namespace test.wi1034.dataslot\n\
               \x20 fact present(1)\n\
               \x20 rule answer(?x) :- present(absent1034data(?x))\n\
               end\n";
    crate::common::load_kb_with(src);
}

/// THE BLAST RADIUS, asserted rather than promised: the stdlib + Rust host bindings
/// load clean with the check on. That is the whole population the ticket predicted 20
/// refusals in, and it is the one measurement that would catch an over-firing
/// predicate — every unit fixture above is small enough to be wrong in the same way
/// the predicate is.
///
/// Passes with the change backed out, by design: it is a NON-regression, and the
/// thing it guards is precisely that this suite's other tests did not buy their
/// refusals with a corpus that stopped loading.
#[test]
fn the_corpus_still_loads() {
    // The `load_kb_with` harness loads stdlib + rust bindings + this source, and
    // PANICS on any load error — so a bare trivial source is the whole assertion.
    crate::common::load_kb_with("namespace test.wi1034.corpus\n  fact present1034(1)\nend\n");
}

/// ONE GOAL IN THE TEXT REPORTS ONCE. A `-:` multi-head rule desugars to one clause
/// per conclusion sharing the body, so a single dangling goal arrives at the check
/// through N `RuleId`s. These errors bypass `dedup_load_errors` (they are returned
/// straight from `load_phase_inner`), so the producer keying on (functor, span) is
/// the only thing that collapses them.
///
/// MEASURED on `safety_gps.anthill:347`, which reported twice — and, before the rule
/// name was dropped from the message, reported the two copies against
/// `anthill.prelude.PartialOrd.gte` and `.lte`, i.e. named two PRELUDE rules as the
/// broken ones. That misattribution is why the message names the goal and not the
/// citing rule.
#[test]
fn one_dangling_goal_reports_once_across_a_multi_head_rule() {
    let src = "namespace test.wi1034.multihead\n\
               \x20 import anthill.prelude.Int64\n\
               \x20 rule banded:\n\
               \x20   absent1034multi(?d)\n\
               \x20   -: gte(?d, 0), lte(?d, 9)\n\
               end\n";
    let msg = refusal(src);
    // Counting the message's OWN marker phrase, not the functor: the wording names the
    // functor twice (once as the subject, once in the repair), so a functor count
    // would read 2 for a single refusal and pass for the wrong reason.
    assert_eq!(
        msg.matches("names nothing").count(),
        1,
        "one goal, one refusal — the multi-head desugar must not multiply it: {msg}",
    );
    assert!(
        !msg.contains("PartialOrd"),
        "the message must not name the desugared conclusion's rule: {msg}",
    );
}

/// A USER FUNCTOR WHOSE LOCAL NAME IS `tuple` IS AN ORDINARY ATOM, both ways round.
/// Its own head is tested (so a genuinely undefined one is refused), and its arguments
/// are DATA, so an undefined name inside one is not.
///
/// The walk recognises the loader's conjunction wrapper by the local name `tuple`, and
/// this pins that the recognition happens only where the loader PUTS one — unwrapped
/// inside the quantifier/discharge arm of `body_goal_children`, exactly as the
/// term-side walk unwraps it inside `goal_arg_termids`. Applied at every node instead,
/// the same predicate would skip this atom's head test AND walk its data as goals.
/// Review-found; both arms are asserted because the two failures are opposite (a
/// missed refusal and a false one) and a test for one would pass with the other live.
#[test]
fn a_user_functor_named_tuple_is_not_a_conjunction_wrapper() {
    // ARM 1 — the head IS tested. `tuple` is only ever minted by the loader, so a
    // user's bare `tuple(…)` goal names nothing and must be refused like any other.
    let undefined = "namespace test.wi1034.usertuple\n\
                     \x20 fact present(1)\n\
                     \x20 rule answer(?x) :- present(?x), tuple(?x)\n\
                     end\n";
    let msg = refusal(undefined);
    assert!(msg.contains("names nothing") && msg.contains("tuple"), "{msg}");

    // ARM 2 — its arguments are DATA. A declared `tuple` predicate whose argument
    // names nothing must LOAD: the argument is a constructor position, not a goal.
    let declared = "namespace test.wi1034.usertuple2\n\
                    \x20 fact tuple(1)\n\
                    \x20 fact present(1)\n\
                    \x20 rule answer(?x) :- present(?x), tuple(absent1034tup(?x))\n\
                    end\n";
    crate::common::load_kb_with(declared);
}

/// `and` IS NOT A GOAL CONNECTIVE, and its arguments are not goals. Both walks listed
/// it beside `or` as "the kernel disjunction / conjunction RULES" — MEASURED FALSE:
/// `kernel.anthill:48` defines only `or`, there is no `BuiltinTag::And`, and the
/// surface `a & b` (`parse/pratt.rs`) lowers to `anthill.prelude.Bool.and`, a boolean
/// OPERATION over VALUES. Walking its arguments would be the same category error as
/// walking a constructor's fields, so `and` was removed from both connective lists.
///
/// THIS TEST PASSES WITH `and` PUT BACK, and that is not a weakness of the test — it
/// is the measurement. The descent gate declines a BARE connective either way, so the
/// only position where the two differ is inside a `not`; and `not(a & b)` cannot be
/// written today — MEASURED, it parses clean, loads clean, and the rule simply DOES
/// NOT EXIST afterwards (`try_resolve_symbol` on its head returns `None`). So the
/// removal is a correctness cleanup with no reachable behavioural difference, and
/// saying so here is the honest alternative to a fixture that pretends otherwise.
///
/// What IS observable is pinned, with the CONTROL that attributes it: a top-level `&`
/// carrying a dangling operand LOADS (not this ticket's refusal), and the same rule
/// with BOTH operands present ALSO answers nothing. The rule is dead either way, so
/// the death is not about the missing name — it is the lowering, **WI-1046**, which
/// owns both this and the vanishing-rule measurement above. Refusing the dangling name
/// here would report a symptom of WI-1046 under WI-1034's message and leave the row
/// with no missing name at all still silently dead.
#[test]
fn an_undefined_name_under_a_boolean_and_is_not_a_goal() {
    let ns = "test.wi1034.boolean_and";
    let src = format!(
        "namespace {ns}\n\
         \x20 import anthill.prelude.Bool\n\
         \x20 fact left1034(1)\n\
         \x20 fact right1034(1)\n\
         \x20 rule dangling(?x) :- left1034(?x) & absent1034and(?x)\n\
         \x20 rule both(?x) :- left1034(?x) & right1034(?x)\n\
         end\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert!(
        crate::common::query_unary(&mut kb, &format!("{ns}.dangling")).is_empty(),
        "not refused here, and dead — WI-1046, not this ticket",
    );
    assert!(
        crate::common::query_unary(&mut kb, &format!("{ns}.both")).is_empty(),
        "THE CONTROL: both conjuncts hold and the rule STILL answers nothing, so the \
         dangling row above is not dead because of the missing name — `&` in a goal \
         position is dead however this walk treats it (WI-1046)",
    );
}
