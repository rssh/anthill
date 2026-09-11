## Attributes

- id: WI-20260911-7TN1Q-occurs-check-a-cyclic-sigma
- created: 2026-09-11T14:39:50Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T14:39:50Z

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

