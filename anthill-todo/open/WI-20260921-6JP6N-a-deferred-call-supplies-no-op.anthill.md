## Attributes

- id: WI-20260921-6JP6N-a-deferred-call-supplies-no-op
- created: 2026-09-21T14:17:31Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T14:17:31Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A DEFERRED CALL SUPPLIES NO OP-SCOPED `requires`, SILENTLY. Found by /code-review during WI-20260921-28TAT; an inline fix was attempted, MEASURED WRONG, and reverted. The site carries the attempt and its refutation so the premise is not re-derived.

WHAT IT IS. An operation-level `requires` is an input the caller owes the callee. WI-20260921-28TAT made that a `NodeOccurrence` stamp (`op_dicts`) written by one function (`stamp_op_scoped_dicts`) and read on every apply route, which closed the hole for the UNCLASSIFIED arm — `Error.reify`'s own clause, which had loaded clean and measured `reqs=[]` at dispatch. The two `CallClass::DeferToRequirement` arms (typing.rs, around the `enclosing_requires[slot]` reads) call `classify()` DIRECTLY rather than through `classify_pin_or_apply_within`, so they stamp nothing; and 28TAT's own gate at the spec-op exit is `occ.classification_is_none()`, which — seeing a classification — skips them too. `start_apply_deferred` installs the SORT half alone, before and after.

SO: a spec operation carrying a `requires` of its own, reached through a requirement slot, enters without it. A body reading the slot raises `__req_* not bound` at eval; a body that does not read it is fine, which is why nothing has caught this. It is PRE-EXISTING and 28TAT did not widen it.

THE OBVIOUS FIX IS WRONG, AND IT WAS RUN. Stamping at the defer arms for the SPEC op (`fn_sym`) looks right — §8.7 forbids an override from STRENGTHENING a clause, so the spec's chain reads like the one both ends share. It is not: the impl is chosen at run time and lays out its OWN op-scoped chain. Measured, `wi456_sorted_set_collection_test::generic_consumer_keeps_the_carriers_ordering` failed outright with eval's count guard doing its job — `Internal("op-scoped frame push: the call site supplied 1 slot(s) for `anthill.prelude.PersistentCollection.insert`, but dispatch landed on `anthill.prelude.SortedSet.insert`")`. "Not strengthened" does not mean "same layout".

WHAT IT ACTUALLY NEEDS. The callee's identity, which on this route exists only AFTER the frame slot is read — i.e. the op-scoped dictionary would have to be built at DISPATCH, from the impl's own chain, rather than stamped at the call site. The stamp holds `TermId`s built from the CALLER's substitution against the SPEC's chain; nothing at eval can re-key them onto a different declaration. So this is a dispatch-time construction, not a plumbing change.

WORTH CHECKING FIRST whether the shape is reachable from source at all: it needs a spec op that BOTH declares its own `requires` AND is dispatched through a requirement slot. If no such operation exists today, the right delivery may be a load-time REFUSAL of that combination rather than a builder — which is 28TAT's "an operation with an op-level `requires` that the call site never builds should not load clean", one route over.

ACCEPTANCE:
 - the reachability probe, with its count, recorded either way;
 - if reachable: a deferred call to an op with its own `requires` supplies the dictionary, DRIVEN by a body that READS the slot and answers, plus the control that fails when the supply is backed out;
 - if not reachable: the load refusal, DRIVEN with its message, and the probe recorded as the reason;
 - `wi456_sorted_set_collection_test::generic_consumer_keeps_the_carriers_ordering` still answers — it is the row that refuted the spec-keyed shortcut;
 - the note left at the spec-op-exit gate in typing.rs is replaced by what actually landed;
 - full workspace green via rustland/scripts/test.sh; scaland `sbt testFull`.

