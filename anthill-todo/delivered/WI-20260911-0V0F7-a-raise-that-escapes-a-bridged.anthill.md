## Attributes

- id: WI-20260911-0V0F7-a-raise-that-escapes-a-bridged
- created: 2026-09-11T12:52:42Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-11T19:44:04Z

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

## Changes

### 2026-09-11T19:43:44Z — feedback — claude

DELIVERED. A raise that escapes a bridged operation is a FAULT on `ResolveStats::errors`
and marks the search INCOMPLETE, where it was a silent `no solutions`. Measured with
`anthill query` on the ticket's own pair:

  answer(?r)  -> warning: `probe.bridged.guardExhaustible` could not be evaluated by the
                 resolver: raised match_failed(occurrence: var_ref(name: n), scrutinee: 0).
                 An empty answer set here is NOT a refutation — the call produced no
                 value. Handle it inside the operation — `Error.reify` turns a raise into
                 a `Result` the rule can read.
                 + `no solutions` + a note that the search is INCOMPLETE
  control(?r) -> `?r = 5`, nothing reported.

THE PER-CONSUMER DECISION NARROWED TO ONE CONSUMER, which is what measuring it produced
and is the only part of the ticket's plan that changed. `read_facts_resolved`,
`prove_from_gamma_verdict` and reflect's `split_first` all read `stats.errors` BEFORE any
`truncated` check, so `note_error` and `record_error` are INDISTINGUISHABLE at three of
the four. The choice moves only the fourth — the load-blocking guards — and it is settled
by UNIFORMITY rather than taste: `builtin_cmp`'s no-order arm, the channel's only other
producer, already records a fault as incomplete, and `resolver_error_channel_test` already
pins that seam (a PRODUCING site records; `step_naf`'s fold onto a DECIDED outer answer
only notes). A fault is therefore incomplete-by-construction — `ReduceFaults::fault` sets
both — so the drain has one behaviour rather than two and the "both ways at once" the
reverted attempt had is unrepresentable.

WHAT SHIPPED.
 * `EvalError::bridge_disposition(&kb) -> Schedule | Truncation | Fault`, beside the
   variants and EXHAUSTIVE, so a new variant must PICK A SIDE instead of inheriting the
   `Err(_) => None` silence. `Raised` is partitioned BY CAUSE: `relation_floundered`
   (WI-737) and `load_failed` (WI-SPGBP) are `Schedule`, keyed by SYMBOL through the
   qualified-name table (WI-897), with an unresolved name degrading to the LOUD side.
 * `Truncation` IS A THIRD SIDE AND IT CLOSED A SECOND HOLE. `Suspended { truncated: true }`
   was matched as `Suspended { .. }` and returned `None`, so a truncation that
   `bridge_eq_op_to_eval` reads through (WI-628) died at THIS bridge — the WI-628 hole one
   bridge over, found only by having to give the variant a side.
 * BOTH BRIDGES, not one. `sem_eq_dispatch`'s carrier-`eq` arm read `Err(_) =>
   BuiltinResult::delay()` — "re-ask me once something binds", false twice over for a
   ground pair whose callee raised. It takes the same partition, and the sentence has ONE
   owner (`bridge_fault_message`) so a reader cannot tell which door a raise came through
   from its wording. Driven: `Colour.eq(green, red)` over `operation eq(a, b) = match a
   case red() -> true` now names `bru.eqr.Colour.eq ... raised match_failed(scrutinee:
   green)` where it said nothing.
 * The sink is `ReduceFaults`, not the ticket's bare `Vec<ResolveError>`: it carries
   `truncated` beside the messages, because the WI-628 distinction runs through this
   boundary and a bridged sub-search cut at its cap has the flag and nothing to say.
   Threaded through `reduce_op_value` / `reduce_operand` / `reduce_dispatched_goal_call` /
   the six reducing builtins / `unify_terms`, drained at two sites in `step_init`. The
   drain is an ASSOCIATED FUNCTION over the two fields, not a `&mut self` method: the
   frame is a shared borrow of `self.stack` across the dispatch, and routing through
   `record_error` would have meant cloning the goal list and σ before every builtin.
 * `render_raised_payload` now READS a `Term` / `Node` payload field through `TermView`
   instead of naming the carrier kind. Not cosmetic: `raise_match_failed` puts the
   scrutinee on those carriers, so the first working version of this fault line read
   `match_failed(occurrence: Node, scrutinee: Node)` — neither the payload nor its sort,
   which is the thing that function exists to stop printing. Every consumer of a raise
   gets it (the `anthill run` runner prints these to users).
 * `EvalError::UnhandledEffect` ACQUIRED ITS PRODUCER. `invoke_effect_handler` raised
   `Internal("no handler registered for effect …")`, which is wrong twice: the bridge
   `debug_assert`s on `Internal`, so a program that merely instantiated a parametric
   effect row with a real effect — the case `docs/kernel-language.md` admits into the
   `Bool` relational view BECAUSE the bridge residualizes it — ABORTED a debug build; and
   in release it read as a fault rather than the capability gap the bridge's own contract
   says it is. Now `UnhandledEffect`, and `Schedule`.
 * The CLI's truncation note stops blaming `--max-depth` alone: `truncated` has two
   causes now and `ResolveStats` carries one bit for both, so the line names both and
   points at the stderr warnings rather than at "the reason above" (which was on a
   different stream, and many rows earlier on a non-empty answer).
 * `unify_terms`'s `_ => TermUnification::NoUnifier` catch-all is EXHAUSTIVE, which the
   ticket named as a trap: it absorbed any new `UnifyOutcome` variant into the DEFINITE
   claim "these terms do not unify", at the one face whose `none()` is documented to mean
   exactly that.

THE ARITH ITEM WAS BUILT, MEASURED AND BACKED OUT, with the reason recorded at
`builtin_arith`'s doc rather than left as an unremarked inconsistency.
`division_by_zero_is_no_solution_not_a_refusal` and
`min_over_negative_one_yields_no_solution_not_a_crash` both go red, each with
`1 solution(s), 1 conditional` where the pin reads `no solutions`. Reading those WI-863
pins again is what changed the answer: THE TWO DOORS ASK TWO DIFFERENT QUESTIONS. Eval
asks what the VALUE is and there is none, so it must raise. A goal asks whether a TUPLE IS
IN A RELATION, and `div(1, 0, ?q)` is in it for no `?q` — which the resolver KNOWS, unlike
`builtin_cmp`'s no-order arm, where it has no order to answer with at all. Making it a
fault trades a TRUE answer for "undecided" and marks the enclosing search incomplete over
a condition that was decided. USER DECISION IF IT SHOULD GO THE OTHER WAY; the patch is
one function.

`/code-review` (high) FOUND SIX, FOUR FIXED HERE AND TWO RECORDED.
 * FIXED, and it was a hole of the same shape as the ticket's: `run_in_bridge_interp`'s
   `?` returned `None` BEFORE the disposition block, so hitting `BRIDGE_REENTRY_CAP` left
   the stream marked COMPLETE — while the sibling `bridge_eq_op_to_eval` calls the
   identical cut `Undecided { truncated: true }`. One line above where the new
   `Truncation` arm is applied.
 * FIXED: the unhandled-effect classification above.
 * FIXED: the fault sentence appended `Error.reify` to EVERY variant, including this
   ticket's own `TypeMismatch` row, where both of its clauses are false. The repair now
   rides with the cause.
 * FIXED: the CLI note above.
 * RECORDED, NOT CHANGED: `stats.errors` is per-STREAM and `read_facts_resolved` aborts
   the whole read on `first()`, so one raising candidate row fails an extent read that
   would otherwise return its other rows. That is the DECISION, not an oversight — the
   same discipline that function already applies to truncation ("a missing answer is
   undecided, not refuted"), and returning the rest while dropping one silently is the
   skip this repo's rules forbid. Nothing in the corpus reaches it (full suite green).
 * RECORDED, NOT CHANGED: the reflect face still answers `Ok(None)` for a fault on a
   branch that yielded NOTHING — see below.

FOUND WHILE DRIVING, BOTH RECORDED AT THEIR SITES, NEITHER IN SCOPE.
 * A FAULT ON A BRANCH THAT YIELDS NOTHING IS INVISIBLE AT THE REFLECT FACE, and that
   arm's own comment claimed otherwise — "reachable only under `definite_only` … this face
   resolves with it off, so every fault reaches the arm above". MEASURED FALSE: `rule bad
   :- rank(green(), 1)` over a raising `rank` faults and yields nothing with
   `definite_only` OFF, because the WI-938 hook falls through to ordinary candidate
   selection on an undecided reduction and `rank` heads no clauses — so the branch FAILS,
   `split_first` takes `self` by value, and the fault dies with the stream. Closing it
   needs `SearchStream::split_first` to hand the exhausted stream back (a signature change
   on the resolver's public door; `step` is private to that module). The comment is
   corrected and `a_fault_on_a_branch_that_yielded_nothing_is_invisible_here` pins the gap.
 * `bridge_op_to_eval`'s `debug_assert` IS REACHABLE FROM A CLEAN PROGRAM under a KB with
   no Rust host bindings: a guard-exhaustible `match n case k | k > 0 -> k` routes through
   `PartialOrd.gt`, whose `requires` slot that KB cannot fill, so the bridged run dies
   `Internal("DeferToRequirement: requirement param `__req_weakord` not bound in caller
   frame")` — a debug-build ABORT. The IDENTICAL fixture passes in `anthill-core`'s rows,
   so the difference is the host-binding set and not the language. Recorded at the
   `anthill-stl` fixture that found it, which uses a non-exhaustive `sort` match instead.

THE COST OF THE `Err` ARM IS PINNED RATHER THAN DISCOVERED. A fault is checked before the
row is built and wins over it, and the continuation is not stored — so a query whose
SIBLING candidate proves cannot be drained at all. That trade was argued at the site when
the arm was written; a bridged raise does not change the argument, it changes how often the
trade is taken. `a_faulted_branch_costs_a_sibling_candidates_answer` measures it
order-independently (which clause runs first is discrimination-tree order, and a single
pull would have passed by luck under one of the two).

DRIVEN, WITH THE BACK-OUT MEASURED AND NOT ASSERTED. `wi_0v0f7_bridged_raise_test` (12
rows) plus 4 in `anthill-stl`'s `reflect::bridge::tests`. Forcing `bridge_disposition` to
`Schedule` for every variant — the `Err(_) => None` it replaces — gives **5 passed, 7
failed**: the seven are every row about a fault being REPORTED, the five are the five
controls, one per consumer. `the_raise_partition_is_by_cause_not_by_channel` is the row
that separates the CAUSE read from a channel test.

`docs/kernel-language.md` §5.3 gained the rule beside the relational-view paragraph whose
"the bridge catches it, and the goal residualizes as before" was the sentence this changes.

SUITE: 6862 passed / 2 failed across 36 binaries, the two being `m5_unhandled_effect_errors_cleanly`
and `m5_modify_handler_taken_is_none` — which PINNED the `Internal` classification the
review asked to change, and were rewritten onto `UnhandledEffect` after that run started;
`eval_tests` re-run alone afterwards is 119 / 119. So 6864 / 0.

