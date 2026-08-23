## Attributes

- id: WI-20260822-K88TN-an-undetermined-type-level
- created: 2026-08-22T20:23:23Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-23T08:24:36Z

- acceptance: cargo-test

## Description

AN UNDETERMINED TYPE-LEVEL OBLIGATION FLOATS OUT OF A POLYMORPHIC WRAPPER AND IS NEVER RE-ASKED, so a contract-less wrapper launders exactly the flow 9PGCM just started gating.

MEASURED, and pinned as a test that must FLIP when this lands: `wrapper_swallows_the_obligation_pending_propagation` in `rustland/anthill-core/tests/include/wi9pgcm_type_level_precondition_test.rs`. Given `send(body: Text[L = ?l]) requires flows_to(?l, Public)`, a direct `send(fetch())` is now REFUSED (9PGCM), while

  operation relay(t: Text[L = ?m]) -> Unit = send(t)
  operation leak() -> Unit = relay(fetch())

loads CLEAN. Two frames, two decisions, and neither is wrong on its own: inside `relay` the label is undetermined, and 9PGCM floats an undetermined obligation because deciding it by absence would refuse every label-polymorphic declaration (WI-067/WI-292 — act on a decided obligation, never on an undetermined one). At `relay(fetch())` the label IS decided, but the typer checks only `relay`'s OWN `requires`, and `relay` declares none. The obligation is dropped between the two.

THIS IS THE PROPAGATION HALF, and 9PGCM's site comment names it as the stopping point rather than leaving it implicit (`kb/typing.rs`, the `UNDETERMINED ⇒ FLOAT` block in `check_apply_iter`).

WHAT MUST BE DECIDED FIRST, because the implementation follows from it and not the other way round. An operation whose body floats an obligation over a variable its OWN signature binds is in one of two regimes and the ticket must pick:

 (a) DECLARE-OR-REFUSE. `relay` must write `requires flows_to(?m, Public)` or the body is a load error naming the callee, the goal, and the variable that carried it out. Sound and explicit; it is also a NEW REFUSAL over source that loads today, so its blast radius is the whole corpus and must be measured before it is chosen.
 (b) INFER ONTO THE SIGNATURE. The floated obligation is added to `relay`'s own effective `requires`, checked at `relay`'s call sites. Nothing new is refused at the declaration and the leak still closes; the cost is a contract no reader can see in the source, which is the objection §5.4 already makes to invisible slots.

EITHER WAY, ONE PREREQUISITE IS THE SAME and it is missing today: an operation's own `requires` is NOT in its body's Γ. `FlowEnv::empty()` is Γ₀, so even under (a) a DECLARED `requires flows_to(?m, Public)` cannot discharge the `send(t)` obligation — the check would refuse the very source it just demanded. Proposal 050's Hoare reading says a precondition is an ASSUMPTION inside the body; seeding Γ₀ with the operation's own value preconditions is that reading, and it is a prerequisite for both branches. NOTE THE ORDERING TRAP: 9PGCM's undetermined gate runs BEFORE Γ is consulted (deliberately — consulting the resolver with a free variable is what made the obligation vacuous, since a free variable is witnessed EXISTENTIALLY off any unrelated fact). So a Γ₀ seed alone changes nothing; the gate must learn to try Γ ALONE — structural match against the assumed clause, never a resolver query — before it floats.

ACCEPTANCE: `wrapper_swallows_the_obligation_pending_propagation` flips to `is_err` (rename it), OR — under (b) — a new test shows `relay(fetch())` refused while `relay(banner())` loads. State which regime was chosen and why, in the spec (§5.4's WI-9PGCM paragraph ends on exactly this open question and must be closed there too).

CONTROLS: every other test in `wi9pgcm_type_level_precondition_test.rs` keeps its verdict — in particular `undetermined_label_floats_rather_than_failing` must stay clean under (b) and must be RE-STATED under (a), since (a) refuses precisely that shape. `wi539_call_site_contracts_test.rs` and `wi557_rule_body_precondition_scope_test.rs` unchanged: a value precondition over value parameters is not this ticket. The guardians suite still passes 16/16. Under (a), report the corpus measurement — how many existing declarations the new refusal hits — before landing it; a double-digit count is itself an argument for (b). Say at each site which tests fail when the change is backed out and which pass either way by design.

ACCEPTANCE IS `cargo-test` ONLY. The filed default carried `scaland-sbt-test` too, which can never pass — this is a typer change and scaland has no typer. The parent 9PGCM carries the identical correction; `add` hardcodes both and the filer must strip the one that cannot apply.

RELATION TO 062. Same keyword, adjacent level: 062 proves a `requires` over a SORT's type parameters at load, and this proves an operation's over a variable its own signature binds, at the frame that binds it. Neither depends on the other; if both land the keyword means one thing wherever it is written.

## Changes

### 2026-08-23T06:44:08Z — feedback — claude

MEASURED 2026-08-23 against the loader at 9cb362a2 (9PGCM + 59CDQ + 1MAGR). Two of this ticket's own claims move, and the regime question is answered by a distinction the codebase already draws. Nothing implemented yet — this is the state the next session should start from.

USER'S READING, and it is the right one: if `relay` declares no `requires`, then `?m` is RIGID in `relay`'s body — it is the CALLER's choice, universally quantified — so the obligation at `send(t)` is `∀m. flows_to(m, Public)`, which is decided FALSE (only `Public` flows to `Public`). It should refuse, and the repair is to declare the clause. That is regime (a), and it follows from WI-1059 rather than from a preference: "GROUND MEANT TWO THINGS, and a skolem is the value that separates them — `rigid_ok = false` CONCRETE … `rigid_ok = true` DETERMINED: nothing is left for a later pass to decide, and a skolem is fully determined". A rigid `?m` is DETERMINED. The gate is asking the CONCRETE question where it should ask the DETERMINED one.

THE GATE MAKES NO SUCH DISTINCTION TODAY. `value_carries_logical_var` (`typing.rs:44589`) bottoms out in `view_carries_logical_var`, whose head arm is `ViewHead::Var(_) => true` — ANY variable, skolem or unsolved inference var alike. That is the one line the regime turns on.

CLAIM 1 OF THIS TICKET IS FALSE, MEASURED. The ticket states: "an operation's own `requires` is NOT in its body's Γ. `FlowEnv::empty()` is Γ₀, so even under (a) a DECLARED `requires flows_to(?m, Public)` cannot discharge the `send(t)` obligation — the check would refuse the very source it just demanded." IT DOES NOT REFUSE IT. Three shapes, run through `anthill load`:

    relay WITH `requires flows_to(?m, Public)`, no caller          -> loads
    … + `operation leak() -> Unit = relay(banner())`               -> loads
    … + `operation leak() -> Unit = relay(fetch())`                -> REFUSED,
        "type mismatch in k6.relay.requires: expected precondition
         `flows_to(Untrusted, Public)` provable at the call site,
         got unsatisfied precondition"

So the DECLARED form already behaves exactly as regime (a) wants — the contract propagates and is checked at the call site. What is missing is only the refusal of the UNDECLARED wrapper. That is a much smaller change than the ticket describes.

CLAIM 2, AND IT IS WHY CLAIM 1 IS NOT GOOD NEWS. The declared form loads for the WRONG REASON. `send(t)` is not proved from the declared `requires` — Γ₀ really is `FlowEnv::empty()` — it is SKIPPED, because the float's `continue` (`check_apply_iter`, `typing.rs:14757`) runs BEFORE `precondition_proved` on the line below it. So today the declared version passes by accident. This makes the ticket's own ORDERING TRAP paragraph the real prerequisite and the Γ₀ seed insufficient alone: if the undeclared wrapper is refused on RIGIDITY, the declared one must be accepted on PROOF, or the pass decides two neighbouring programs by two different criteria.

THE JUSTIFICATION FOR FLOATING OVERSTATES ITS POPULATION. The site comment says deciding by absence "would refuse every label-polymorphic wrapper". Under the rigid reading it refuses only a label-polymorphic operation that CALLS A CONSTRAINED OPERATION WITHOUT DECLARING THE CONSTRAINT. One that calls nothing constrained is untouched, and for the rest the repair is one `requires` line that already works (above). The corpus count this ticket demands before choosing (a) is therefore still owed, but the predicted number should be much smaller than "every polymorphic declaration".

SHAPE OF THE FIX, three coupled pieces — none of them alone is a fix:
 1. SPLIT THE GATE at `typing.rs:14757`: a clause carrying a FLEXIBLE var floats (unchanged); one carrying a RIGID var is DECIDED and must be discharged or refused. WI-1059's `rigid_ok` is the existing precedent and `type_value_is_ground_g` is the existing shape.
 2. SEED Γ₀ with the operation's own value preconditions (proposal 050's Hoare reading: a precondition is an ASSUMPTION inside the body).
 3. AT THE GATE, try Γ ALONE for a rigid clause — STRUCTURAL match against the assumed clause, never a resolver query. The ticket's ordering note gives the reason and it holds: a resolver query with a free variable is witnessed EXISTENTIALLY off any unrelated fact, which is the vacuity 9PGCM removed.

THE REPRO, self-contained, so the next session need not rebuild it. Load each as one file with `anthill load`; the prelude is shared and the last operations are what varies.

    enum k.Level
      entity Untrusted
      entity Public
    end

    enum k.Text
      import anthill.prelude.{String}
      sort L = ?
      entity mk(raw: String)
    end

    namespace k
      import anthill.prelude.{Unit, String}
      import k.Level.{Untrusted, Public}
      import k.Text
      import k.Text.{mk}

      -- the lattice. NOTE WHAT IS ABSENT: flows_to(Untrusted, Public).
      fact flows_to(Public, Public)
      fact flows_to(Untrusted, Untrusted)

      operation fetch()  -> Text[L = Untrusted]
      operation banner() -> Text[L = Public]

      operation send(body: Text[L = ?l]) -> Unit
        requires flows_to(?l, Public)

      -- … one of the six tails below …
    end

    TAIL                                                     TODAY      WANTED
    1  operation leak() = send(fetch())                       REFUSED    same
    2  operation ok()   = send(banner())                      loads      same
    3  operation relay(t: Text[L = ?m]) = send(t)             loads      REFUSED  <- (a)
    4  3 + operation leak() = relay(fetch())                  loads      REFUSED  <- the leak
    5  3 + operation ok()   = relay(banner())                 loads      same
    6  relay WITH `requires flows_to(?m, Public)`, + 4's tail  REFUSED    same, but
                                                                          PROVED not skipped

Rows 3 and 6 are the pair that separates the regimes: under (a) row 3 flips and row 6 must keep its verdict for a NEW reason. Row 5 is the control that says the fix gates rather than refuses. Rows 1/2 are 9PGCM's and must not move.

ACCEPTANCE UNCHANGED otherwise, with one correction: `wrapper_swallows_the_obligation_pending_propagation` (row 4) flips to `is_err` under BOTH regimes, so it does not distinguish them — row 3 is what does. And `undetermined_label_floats_rather_than_failing` IS row 3, so under (a) it is not merely "re-stated": it inverts, and the ticket should say so in those words.

STILL OWED BEFORE LANDING (a): the corpus census the ticket asks for — how many existing declarations the new refusal hits. Not run in this session.

### 2026-08-23T07:40:46Z — feedback — claude

DELIVERED as REGIME (a), DECLARE-OR-REFUSE, chosen by the user after weighing (b) in
session. Measured against 627d0fbc. The two claims the previous feedback moved are
confirmed, and the regime question turned out to be settled by the spec ALREADY —
this ticket only made the `requires` check obey a rule §"Expansion during unification"
had stated for the type check.

WHY (a), AND (b) IS NOT MERELY LESS PREFERRED — it does not survive its own costs:

 1. `?m` IS ALREADY RIGID IN THE BODY, measured, not read: `narrow(t: Text[L = ?m]) ->
    Text[L = Public] = t` is refused `expected Text[L = Public], got Text[L = ?m]`,
    while `keep(t: Text[L = ?m]) -> Text[L = ?m] = t` loads. So the TYPE half already
    checks `relay` in isolation against a universally quantified `?m`; only the
    `requires` gate did not. §"Expansion during unification" states the rule ("Inside
    a body, then, an unwritten parameter is rigid … At a *call* it is flexible again")
    and WI-1FKR2 spells out the WRITTEN-variable family `?m` belongs to.
 2. (b) AS WHOLE-PROGRAM re-checks a callee's BODY at each call. Call sites read the
    SIGNATURE only today; the two body-walkers reachable from a call-ish site are the
    WI-418 / WI-1095 requirement-slot readers, and both are documented as bounded and
    refusal-withholding ("Cross-sort calls are NOT followed"). Recursive expansion per
    call site is the cost the user named, and it is a new one.
 3. (b) AS SIGNATURE-SUMMARY (Haskell's inferred context) still needs (a)'s refusal:
    `f() = send(pick())` over `pick() -> Text[L = ?k]` floats a clause naming a
    variable NO signature binds, so there is nowhere to infer it to. Measured: that
    program loaded clean before this change and is refused after. (b) = (a) + an
    inference step, not an alternative to it.
 4. THE DECIDING PRECEDENT: the other half of the same clause list already runs (a).
    `operation relay(x: Int64) -> Unit = emit(x)` against `emit effects Modify[Console]`
    is refused `expected declared: [], got undeclared effect: Modify[T = Console]`,
    compared against `declared_canon` under the same `op.rigidify`. (b) would have made
    two halves of one `OperationClause` list obey opposite disciplines.

SHIPPED — two coupled pieces, and NEITHER ALONE reproduces the behaviour:
 1. THE GATE SPLIT. `value_carries_logical_var` → `value_carries_undecided_var`;
    `ViewHead::Var(_) => true` → `ViewHead::Var(v) => !v.is_rigid()`. One caller, so no
    shared-predicate hazard. This is WI-1059's DETERMINED reading where the old line
    asked the CONCRETE one.
 2. THE Γ₀ SEED. `op_requires_gamma` assumes the op's own VALUE preconditions into its
    body's Γ₀ (proposal 050's Hoare reading), walked through `op.rigidify` so producer
    and consumer name the same skolem. `Env::new` → `Env::with_gamma`; every other
    entry now passes `FlowEnv::empty()` explicitly.

THE TICKET'S PRESCRIBED ITEM 3 WAS NOT NEEDED, and the departure is measured. It asked
for "Γ ALONE — structural match against the assumed clause, never a resolver query".
A rigid clause goes to the full prover instead, which is SOUND because the existential
vacuity 9PGCM removed is a FLEX hazard specifically: `unify_concrete` refuses to bind a
skolem ("a skolem must never bind … unifies only with another Rigid carrying the same
id"), so `flows_to(!m, Public)` finds no witness off `flows_to(Public, Public)`. It is
also BETTER: a genuinely universal obligation needs no declaration. MEASURED, with its
own control — `rule anything(?x) :- true` + `wrap(t: Text[L = ?m]) = strict(t)` LOADS;
replacing the rule with `fact anything(Public)` REFUSES it. Γ-membership alone would
have refused both and demanded a contract that says nothing.

MEASURED ROWS (`anthill load`), superseding the previous feedback's table. Row 5 as the
ticket wrote it is inconsistent with its own row 3 — row 5 EMBEDS the undeclared relay,
so under (a) it must refuse too. The real gating control is the DECLARED form, added
here as 3' and 5':

    ROW                                                   BEFORE     NOW
    1  send(fetch())                                      REFUSED    same
    2  send(banner())                                      loads      same
    3  relay = send(t), undeclared                         loads      REFUSED
    3' relay WITH `requires flows_to(?m, Public)`          loads      loads, but PROVED
    4  3 + leak() = relay(fetch())                         loads      REFUSED
    5  3 + ok()   = relay(banner())                        loads      REFUSED (embeds 3)
    5' 3' + ok()  = relay(banner())                        loads      loads
    6  3' + leak() = relay(fetch())                        REFUSED    same, at
                                                                      relay.requires
    R  f() = send(pick()), pick() -> Text[L = ?k]          loads      REFUSED

TWO BACK-OUTS, because there are two axes; each test names the one it measures.
MEASURED, not predicted:
  * GATE SPLIT reverted (`!v.is_rigid()` → `true`): 5 tests fail —
    rigid_label_obligation_is_decided_and_refused,
    the_wrapper_no_longer_swallows_the_obligation,
    the_obligation_propagates_through_two_wrappers,
    an_obligation_no_signature_binds_is_refused,
    mixed_conjunct_over_a_rigid_label_is_decided_whole.
  * Γ₀ SEED reverted (`gamma0` → `FlowEnv::empty()`): 3 tests fail —
    declaring_the_clause_discharges_it_from_gamma,
    a_declared_wrapper_gates_its_own_callers,
    mixed_conjunct_declared_discharges_and_still_gates.
    THIS IS THE PROVED-vs-SKIPPED CONTROL the previous feedback demanded: those three
    programs ALSO loaded before this ticket, by the float's `continue` running ahead of
    `precondition_proved`. Under the back-out they are refused at `send.requires`
    (inside the body) instead of `relay.requires` (at the call) — the wrong reason made
    visible.
  * a_universally_true_obligation_needs_no_declaration passes under BOTH by design; its
    control is the rule-vs-fact swap in its own body.

CORPUS CENSUS — the measurement the ticket demanded before landing (a), and the answer
is the opposite of its fear ("a double-digit count is itself an argument for (b)"):
ZERO new refusals across 212 `.anthill` files. The single file reporting a
requires-refusal is `docs/measurements/guardians/d2c_callsite.anthill`, which is row 1
— 9PGCM's own guardian, designed to refuse, and refusing both before and after. The
stdlib loads clean. The site comment's "would refuse every label-polymorphic wrapper"
overstated its population exactly as the previous feedback predicted: the refusal
reaches only a polymorphic operation that CALLS A CONSTRAINED ONE WITHOUT DECLARING THE
CONSTRAINT, and the repair is one line that works.

DIAGNOSTIC — a second `PreconditionFailure` case, not a suffix (WI-1049's shape). The
call-site message's advice ("establish it with an enclosing `if`/`match` guard, a prior
`ensures`, or a KB fact") is wrong for this case: nothing at the call can establish a
goal quantified over a variable the caller picks. The wrapper case names the repair and
quotes the line to write, in SOURCE spelling — `flows_to(?m, Public)`, not the `!m` a
rigid prints as, since `requires allowed(!m, n)` is not a line anthill parses
(`unrigidify_for_display`, the same argument `goal_in_source_spelling` already makes for
`var_ref`). The ground call-site message is byte-unchanged.

TESTS: 15 in `wi9pgcm_type_level_precondition_test.rs` (was 12) — 3 inverted and
renamed, 6 new. Full suite 8317 passed / 0 failed across 36 binaries. Guardians 16/16.

SPEC: §5.4's WI-9PGCM paragraph closed — it ended on "propagating it onto the enclosing
contract is not yet decided", now replaced by the quantifier rule, the declare-or-refuse
statement, and why (b) was rejected. §"Expansion during unification" gained the parallel
at its own rigidity paragraph: a body that pins a rigid through a `requires` is refused
for the reason a body that pins it through a type is.

acceptance was `cargo-test` only, as the ticket corrected; scaland has no typer.

### 2026-08-23T08:15:16Z — feedback — claude

/code-review ROUND — THREE FINDINGS, ALL THREE REAL, all three verified independently
before acting and all three fixed. Two of them were reachable from NEITHER the ticket's
six rows nor my own controls, and one was a REGRESSION I introduced. Recording them
because the pattern is the point.

CORRECTION FIRST: the previous feedback's "8317 passed" is a mis-parse of my own awk.
Computed consistently across both runs the suite is 5581 → 5583 passed, 0 failed, 36
binaries — the delta is exactly the two tests added this round. Guardians 16/16 and the
corpus census are unchanged (1 file, 9PGCM's own guardian, refusing before and after).

FINDING 1 — A REGRESSION, and the one I am least happy to have shipped. A match-arm
GUARD is checked through a NESTED `type_check_node_gated` rather than a work-stack
`Visit`, and that entry hard-coded Γ₀ to `FlowEnv::empty()`. Invisible while a rigid
obligation FLOATED; a false refusal the moment it became DECIDED. So a wrapper that
CORRECTLY declared its contract was refused for calling the constrained operation in a
guard, while the identical call in the arm BODY loaded. MEASURED three ways: loads on
HEAD, refused with my change, loads again with `arm_flow` threaded.

THE LESSON, and it is one I have written down before under another name: a Γ SEED MUST
REACH EVERY POSITION THE OBLIGATION IS JUDGED IN, and I threaded it into ONE — the body
driver — having censused `FlowEnv::empty()` call sites but not asked which of them sit
INSIDE a body. The guard is the only re-entrant position in the walk, so the census had
exactly one miss and it was the whole hole. `type_check_op_body_gated` is now
`type_check_node_gated_in_gamma` with both callers, because the name encoded my wrong
belief that the op body was the only supplier.

FINDING 2 — A REFUSAL WHOSE PRESCRIBED REPAIR DOES NOT WORK. `Var::Rigid` HAS TWO
PRODUCERS WITH OPPOSITE QUANTIFIERS and I keyed on the kind alone:
  * `rigidify_op_type_params` / `rigidify_unwritten_sort_params` — ∀, a signature's own
    parameter. Declarable. The ticket's case.
  * `open_existential_return` — ∃, a FRESH ρ per use, witnessing a variable in a
    callee's RETURN (`pick() -> Text[L = ?k]`). Bound by nothing.
For the second my message said "declare it on the enclosing operation". MEASURED: apply
that repair and you get the BYTE-IDENTICAL error, because `?k` written in `f`'s
`requires` is a new flex variable of `f`'s own that never meets ρ. A loop, not a
diagnostic — and my OWN test `an_obligation_no_signature_binds_is_refused` says in its
comment that there is "no slot to infer a contract ONTO", so the message contradicted
the test sitting beside it.

The REFUSAL was right either way (nothing may be assumed about an opaque witness), so
the fix is a third `PreconditionFailure` case, not a verdict change.
`clause_rigid_kind` now splits on membership in `TypingEnv::param_rigids`, and that list
is the precise question for a reason already written at `constrained_param_receiver_type`:
it holds "exactly the parameters in scope", and such a variable "IS a parameter a
`requires` clause can name and a call can instantiate" — which is verbatim the property
the message needs. A clause carrying BOTH kinds answers witness, since a declaration
could name the parameter half and still not the witness.

THE LESSON: A REFUSAL NEEDS A REPAIR YOU HAVE RUN. I had this written down from J38JE
and did not apply it — I verified the refusal fired and never applied its own advice.
The new test DRIVES the repair rather than asserting the message text, which is the
only form of this test that would have caught it.

FINDING 3 — ATTRIBUTION. `type mismatch in k.send.requires` named the CALLEE while the
repair is on the enclosing operation, so the header said "send's contract is wrong" when
send's contract is fine and `relay`'s is missing. The span already pointed inside
`relay`'s body, so header and span disagreed. `entity_name` is now the enclosing
operation for that case only; the other two keep the callee (an unsatisfied obligation IS
the callee's `requires`, and for an opaque witness there is no declaration to name).

FOUR BACK-OUT AXES NOW, all MEASURED, none predicted:
  (A) gate split reverted  -> 6 fail   (was 5; + a_guard_still_gates_an_undeclared_wrapper)
  (B) Γ₀ seed reverted     -> 4 fail   (was 3; + a_declared_clause_discharges_in_a_match_guard_too)
  (C) guard Γ reverted     -> 1 fail   (a_declared_clause_discharges_in_a_match_guard_too)
  (D) witness/param split reverted -> 1 fail (an_obligation_no_signature_binds_is_refused)
(C) is the regression's control and (D) changes NO verdict — only which repair is
printed — which is why it needs its own axis. One test appears in both (B) and (C), and
correctly: the guard needs the seed to exist AND the threading to reach it.

TESTS: 17 (was 12 before the ticket, 15 after my first pass). Suite 5583/0 across 36
binaries; guardians 16/16; corpus census unchanged at 1 file.

NOTED, NOT FIXED — a cross-reference worth having and too small for a ticket, so it is
recorded here instead: `proof_verify.rs:613` seeds Γ from the same op's value
preconditions with the same `is_value_precondition_clause` filter, differing only in the
substitution it walks through (σ_value skolemization vs `op.rigidify`). Two
implementations of one idea; if either grows a rule the other should get it.

