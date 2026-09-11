## Attributes

- id: WI-20260911-0V0F7-a-raise-that-escapes-a-bridged
- created: 2026-09-11T12:52:42Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T12:52:42Z

- acceptance: cargo-test

- tags: effects

## Description

A RAISE THAT ESCAPES A BRIDGED OPERATION IS REPORTED AS "NO SOLUTIONS" — `bridge_op_to_eval`
turns every `EvalError` into `None`, so a goal whose callee RAN AND RAISED is
indistinguishable from one that merely could not be folded, and the empty answer set reads
as a relation with nothing in it.

MEASURED, with a control, on an operation whose effect row is EMPTY so nothing else warns:
`rule answer(?r) :- guardExhaustible(0, ?r)` — a guard-exhaustible `match`, so the raise
rides the HOST `Error[MatchFailed]` channel — answers `no solutions` with `stats.errors`
empty, while `guardExhaustible(5, ?r)` answers `?r = 5`.

  operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 -> k

THE ARGUMENT MUST BE A LITERAL. Spelled `guardExhaustible(0 - 5, ?r)` the operand reaches the
bridge UN-REDUCED, so the guard compares a `Node` against an `Int64` and the bridge answers
`TypeMismatch { expected: "Ord scalars of matching type", got: "Node and Int64" }` — a
DIFFERENT defect presenting as the same silent `no solutions`. Only a probe inside the
bridge's `Err` arm told them apart; two fixtures were written wrong before that.

PRE-EXISTING, not a consequence of proposal 027.4's narrowing: it predates that work and is
reached through the host channel, not through `reify`. `BuiltinResult::Error(ResolveError)`
(227f83b9) is now the right home — its own doc draws the line: "`Failure` claims the answer
is no, `Unknown` that there is no answer, `Delay` that the answer is not available yet. This
claims nothing about the goal at all — it says the resolver could not ask it."

A FIRST ATTEMPT WAS BUILT AND REVERTED, and what it found is the actual content of this
ticket: the producer is easy, and every CONSUMER needs a decision first.

FOUR CONSUMERS ASSUME FAULTS ARE RARE AND SPECIFIC. Each was written when the only producer
was `builtin_cmp`'s no-order arm; a bridged raise is far more common, and each of these turns
that into a behaviour change no test currently covers:
 * `extent.rs` `read_facts_resolved` returns `Err(SearchFaulted)` on ANY non-empty
   `stats.errors`, before collecting rows and regardless of `truncated`. One raising row would
   fail a whole extent read — the public 057 seam, used by anthill-todo's store, the CLI's
   entry discovery and cpp-gen's realization rows.
 * `typing.rs` `prove_from_gamma_verdict` takes `stats.errors.first()` BEFORE the refutation
   check, and its own comment concedes the list is per-STREAM. An unrelated branch's raise
   would mask a genuine contract violation and name an operation the conjunct never mentions.
 * `anthill-stl` `SearchStreamAdapter::split_first` turns non-empty errors into a TERMINAL
   `Err` and stores no continuation. A query that answers perfectly well via a sibling
   candidate would die at the first pull, with the good answer discarded.
 * `record_error` sets `truncated`, which makes `eval_negation_guard` / `eval_forall_guard` /
   the counting guard return `Undecidable`, and `GuardCheck::Undecidable` is LOAD-BLOCKING.
   `constraint c :- no ?x: p(?x), eq(?x, f(1))` with a raising `f` would stop loading.

THE DECIDERS DO NOT READ `errors` AT ALL, WHICH IS THE CRUX. Nothing in the resolver decides
on the message list; `step_naf`, `eval_negation_guard`, `eval_forall_guard` and the counting
guard all key on `truncated` / `residual` / `definite`. So `note_error` alone NARRATES the
raise and changes no verdict: `not(p(?r))` over a callee that ran and raised still SUCCEEDS
definitely, because the sub-search came back complete-and-empty. But `record_error` sets
`truncated`, which is what makes those guards `Undecidable` — and `GuardCheck::Undecidable`
is load-blocking. The choice is therefore not a matter of taste between two recorders: one
leaves the defect in place, the other can stop a previously-loading program. That decision
has to be made deliberately, per consumer, and it is the real content of this ticket.

The reverted attempt had it BOTH WAYS at once, which is its own evidence: the goal-call route
used `note_error` while the four operand routes went through `BuiltinResult::Error` ->
`record_error`, so one raise got opposite completeness verdicts depending on whether it was
reached as a goal or as an operand.

WHICH `EvalError`s THE BRIDGE CAN ACTUALLY SEE, audited, since `bridge_disposition()` needs
it: `Raised` is the only raise-shaped variant reachable — `raise_error` produces it whenever
no `Error` handler is installed, and the bridge interpreter's effect registry is EMPTY by
construction. `UnhandledEffect` has no producer in the crate at all, and `MacroRejected` is
the compile-time conversion `simp_rewrite` makes before the bridge. So the partition is over
`Raised` (by CAUSE, since `raise_relation_floundered` and `raise_load_failed` ride the same
variant and are not faults), `Overflow`, `StepsExhausted`, the ambiguity verdicts, and the
requirement-dictionary gap.

AND `unify_terms`'s CATCH-ALL IS A TRAP. `_ => TermUnification::NoUnifier` absorbs any new
`UnifyOutcome` variant, so routing a raise through `unify_values` turns it into the DEFINITE
claim "these terms do not unify" — handing `reflect.unify` a `none()` for a callee that
raised. That reopens exactly the mapping WI-20260910-FDPJ8 closed, and its own fixtures use a
non-raising callee so nothing goes red.

THE SHAPE TO BUILD, from the review's altitude angle rather than the reverted attempt:
 * `reduce_op_value(..., faults: &mut Vec<ResolveError>)` — a SINK that is appended to and
   never merged, so a fault cannot be dropped at a `from_bridge` exit and a stale one cannot
   be composed onto a bridge that SUCCEEDED (both were real bugs in the attempt). Removes the
   four types the attempt added (`Reduced`, `Bridged::Faulted`, `EqOperands::Faulted`,
   `UnifyOutcome::Faulted`) whose only job was carrying one optional error past ten sites.
 * `EvalError::bridge_disposition() -> Fault | Schedule | Truncation`, beside its `Display`,
   so a newly added variant must PICK A SIDE instead of defaulting to silence. The attempt
   tested the CHANNEL (`EvalError::Raised`) rather than the cause, which wrongly swept in
   `raise_relation_floundered` (WI-737, an undecided sub-search) and `raise_load_failed`
   (WI-SPGBP).
 * Render the payload with `eval::error::render_raised_payload`, not `operand_label` — the
   latter is a SORT labeller, so `Error.raise("disk full")` printed "RAISED `String`".
 * The diagnostic must not advise "declare the label and call it from a context that can":
   `effect_row_admits_relational_view` requires an empty row or all-parametric members, and
   `effect_member_is_parametric` refuses `Error[T = P]` by design — so declaring it makes the
   WI-938 hook not fire at all, giving 0 solutions with `stats.errors` EMPTY. Strictly worse
   than the state being fixed. `Error.reify` is the sound remedy.

ALSO WORTH SETTLING HERE: `builtin_arith`'s zero-divisor arm returns `Failure` — a positive
refutation, so `not(div(1, 0, ?q))` SUCCEEDS — while the same division through an operation
body would become a loud fault. One condition, two opposite readings decided by which door it
came through. `builtin_cmp`'s no-order arm was converted from exactly this shape.

ACCEPTANCE: `rule answer(?r) :- guardExhaustible(0, ?r)` reports a fault naming the raised
PAYLOAD (not its sort) in `stats.errors`, with `guardExhaustible(5, ?r)` answering `?r = 5`
and reporting none; plus a row per consumer above showing what it now does with a bridged
raise, each with the control that passes either way.

