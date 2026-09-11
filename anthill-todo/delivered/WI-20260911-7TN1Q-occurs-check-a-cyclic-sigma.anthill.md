## Attributes

- id: WI-20260911-7TN1Q-occurs-check-a-cyclic-sigma
- created: 2026-09-11T14:39:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-11T16:40:53Z

- acceptance: cargo-test, scaland-sbt-test

## Description

OCCURS CHECK: a cyclic sigma binding through a SortAlias is not seen, and the typer
does not terminate — `occurs_in` is structural over `Term::Var` while `walk_type` chases
`Term::Ref` through the alias chain.

MEASURED 2026-09-11 at b7896119 (before WI-20260911-RS2G4) and again after it. This is a
PRE-EXISTING defect; RS2G4 is named only because it gives a second spelling the same path.

THE PROGRAM. A call-site bracket whose VALUE mentions the enclosing sort's own type
parameter, written inside that sort:

    sort Box[T]
      entity box(v: T)
      operation empty() -> Option[T = T] = none()
      operation probe() -> Option[T = T] = Box.empty[T = Option[T = T]]()
    end

  `anthill load` does not return. It aborts:

    thread 'main' has overflowed its stack
    fatal runtime error: stack overflow, aborting

  The same shape with `[T = List[T = T]]` and `[T = Box[T = T]]` aborts identically.

THE TABLE, both spellings, both commits:

    inside `sort Box[T]`                     at b7896119        with RS2G4
      Box.empty[T = Box[T = T]]()   callee   stack overflow     stack overflow
      Box[T = Box[T = T]].empty()   recv     loads clean        stack overflow

  The callee spelling has aborted since WI-841 gave a bracket the enclosing sort's scope.
  The receiver spelling loaded clean at b7896119 only because the bracket was DROPPED
  (the W6JH0 channel was read once and late); RS2G4 makes it bind, so it reaches the
  callee spelling's behaviour, crash included. RS2G4 therefore adds no defect and removes
  none — it widens the reach by one spelling, and says so in
  `wi_rs2g4_receiver_bracket_binds_sort_params_test`'s header.

THE CAUSE, located rather than guessed. Three measurements, all with temporary probes
that were then removed:

  * A depth tripwire in `unify_types` never fired; the same tripwire in `walk_type_deep_g`
    fired immediately and repeatedly on the SAME `T`. The loop is the deep sigma walk.
  * Tripwires on `Substitution::bind_term` and `bind_value`, asserting
    `occurs_in` / `occurs_in_view` of the incoming value, NEVER fired. No single binding is
    cyclic.
  * At the seeding site the receiver's value is `Value::Term`-carried and
    `occurs_in_view(vid, value)` answers FALSE.

  So the written inner `T` does not lower to `Term::Var(?T_Box)` — it lowers to
  `Term::Ref(Box.T)`, the parameter's SYMBOL. `occurs_in` walks `Term::Var` and `Term::Fn`
  and has no `Term::Ref` arm, so it sees nothing; `walk_type` DOES resolve `Ref(Box.T)`
  through `resolve_sort_alias` back to `Var(?T_Box)`. The binding
  `?T_Box := Option[T = Ref(Box.T)]` is therefore cyclic THROUGH THE ALIAS, lands in sigma
  unrefused, and `walk_type_deep` chases it until the stack ends.

THE FIX, and why it was not taken inline. `occurs_in` gains a `Term::Ref(s)` arm that
resolves `s` through `resolve_sort_alias` (already `&KnowledgeBase`, already indexed) and
compares the target to `Var::Global(vid)`. Perhaps eight lines. What makes it its own
ticket is the BLAST RADIUS, not the size: `occurs_in` guards `bind_resolved` — the var arm
of every `unify_types` — and `unify_parameterized_with_sort_ref`'s canonical-parameter
bind. Widening it makes both REFUSE bindings they accept today, across the whole typer,
and a widening of a hot type relation reaches machinery it was never on. It needs its own
census: how many bindings in `stdlib/`, `examples/`, the `anthill-todo` code and the test
corpus are newly refused, and whether any of them is a legitimate program.

ACCEPTANCE.
  * The four programs above (`[T = Box[T = T]]`, `[T = Option[T = T]]`,
    `[T = List[T = T]]`, each in BOTH spellings) are a LOAD ERROR naming the parameter and
    the value that mentions it — not an abort, and not silence.
  * The test is a LOAD test, not an eval one, and it must not be written as a row whose
    failure mode is an abort: a crashing test takes the whole binary with it, which is why
    RS2G4 recorded this in prose rather than as a row.
  * `Box[T = T].empty()` inside `sort Box[T]` — the value that IS the parameter, not one
    that mentions it — keeps loading. That is the control, and it separates "cyclic" from
    "self-referential at all".
  * A CENSUS of what the widened `occurs_in` newly refuses, over the three corpora and the
    full suite, reported before and after.
  * cargo-test green via rustland/scripts/test.sh.

REFERENCE: `occurs_in` / `occurs_in_view` and `bind_resolved` (typing.rs);
`resolve_sort_alias` + `build_sort_alias_index` (WI-659); `walk_type` / `walk_type_deep_g`;
WI-841 (the bracket's sort scope, which made the callee spelling reachable);
WI-20260911-RS2G4 (the receiver spelling, and the header note that records this).

## Changes

### 2026-09-11T14:40:30Z — feedback — claude

RUST-ONLY: scaland loads no operations, so it has no call-site bracket and no twin to keep in step.

### 2026-09-11T16:40:47Z — feedback — claude

DELIVERED. `occurs_in` is alias-aware, and the callee bracket no longer swallows the
refusal. Rows: `wi_7tn1q_occurs_check_sort_alias_test` (8), whose header carries the
back-out table and the census.

THE TICKET NAMED ONE HALF OF THE FIX. `occurs_in`'s `Term::Ref` arm ends the abort, as
predicted — but with the binding refused the CALLEE spelling then LOADED CLEAN, because
`seed_op_type_args` discards `unify_types`' verdict. That is silence, which the acceptance
forbids, so the callee leg now reads the verdict for this ONE fault (gated on `prior` so
WI-367 / WI-379's already-pinned discard is untouched) and both channels render from one
builder. The receiver spelling needed no new message: RS2G4 had already written one against
exactly this refusal, which could not fire until now.

THE CENSUS, zero everywhere. A temporary probe logged every firing of the new arm: stdlib +
an empty program 0, `examples/github-todo` 0, `rustland/anthill-todo/anthill` 0, full
workspace suite 6877 passed / 0 failed / 0 firings. Nothing that exists was newly refused,
so there was no legitimate program to judge. Final suite after the review fixes: 6885
passed, 0 failed.

FIVE BACK-OUTS, each measured separately — (A) the predicate off: the BINARY ABORTS; (B)
`occurs_in`'s `Term::Ref` arm alone off: the same abort, which is what says the cycle runs
through the `TermId` reader; (C) `occurs_in_view`'s bare-head arm alone off: 5 red, no
abort; (D) the callee leg off: 4 red; (E) the vid comparison dropped: 1 red, and that row
is the only thing between this check and one that refuses a legitimate program.

ONE CLAIM OF MINE WAS WRONG AND IS CORRECTED IN PLACE. I wrote that the
`is_sort_param_symbol` gate keeps the arm narrow "or it would refuse bindings across the
whole stdlib" — inherited from `walk_type`'s doc, not measured. Forced open, the three
corpora load with identical fact/rule counts and `anthill-core`'s 6045 tests pass. The gate
stays for the CORRESPONDENCE with `walk_type`, which is the arm's whole justification, and
`sort_param_ref_is_var`'s doc now says that instead.

`/code-review` (high) found five things; three were mine and are fixed here:
  * the receiver leg inferred "the value mentions the parameter" from the verdict alone,
    so a correct binding could be blamed for a cycle whenever sigma already carried the
    STICKY contradiction flag. It now reads the fact, exactly as the callee leg does. No
    program reaches that state, and the header says so rather than crediting a row.
  * a `debug_assert!(false, ...)` arm failed OPEN in release, letting a refused binding
    type at whatever the context wanted. The tripwire stays; the refusal does not depend
    on it.
  * the bare refusal read as "you wrote something illegal". `Box.empty[T = List[T = T]]()`
    is a well-formed INTENT — the same operation at another instance — unexpressible only
    because a bracket binds the ENCLOSING sort's canonical variable, so the callee's `T`
    and this instance's `T` are one variable. The message now says that, pinned by
    `the_refusal_says_why_it_is_a_representation_limit`. Giving the callee's parameters
    fresh variables is what would make the family expressible; that is a design change and
    is not in this ticket.

The fourth was folded in INLINE rather than filed, because the change is a one-line
deletion: `bind_or_refine_member_param`'s third conjunct
`(prior_flag || !trial.is_contradiction())`. The review read it as losing a conflict
detail; it never could — every writer reachable inside the trial pushes a detail BEFORE
setting the flag, so a trial that raises the flag anew has grown the count the SECOND
conjunct checks, and a dedup hit means the flag was already in sigma, making the
disjunction a tautology. Measured with a probe at the site: `flag set, no detail` fired 0
times across 6046 tests. Removed with the proof in its place, because a guard that cannot
fire reads as protection.

The fifth is filed as WI-20260911-6B67S: a receiver-bound requirement slot skips
`validate_instance_selection`, so `check_selection_bindings` says a witness PROVIDES the
spec when it provides nothing. Pre-existing in RS2G4, out of this ticket's diff.

RUST-ONLY, now measured rather than inherited: `scaland/core/.../load/Loader.scala:397`
states it emits no `SortAlias` fact and has no typer, and scaland's `occursIn` is the
resolution-path check in `subst/Substitution.scala`. There is no alias to be cycle-aware
about and no type walk to overflow.

