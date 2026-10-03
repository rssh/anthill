## Attributes

- id: WI-20261003-FFY4R-a-call-s-witness-pin-spec-op
- created: 2026-10-03T12:31:41Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T12:31:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CALL'S WITNESS PIN (`Spec.op[Spec = W](…)`) IS READ BY ONE DISPATCH ROUTE ONLY. With `sort Holder { sort C = ?; operation size(c: C) -> Int64; operation size2(c: C) -> Int64 = size(c) }`, `sort Box { sort V = ?; entity box(v: V) }`, `sort OptIntBoxH { provides Holder[C = Box[V = Option[T = Int64]]]; operation size(c: Box[V = Option[T = Int64]]) -> Int64 = 42 }` and `sort OptStrBoxH { provides Holder[C = Box[V = Option[T = String]]]; operation size(c: Box[V = Option[T = String]]) -> Int64 = 7 }`: (a) `Holder.size2[Holder = OptIntBoxH](box(v: none))` — a DEFAULTED spec operation — is refused "type mismatch in Holder.size2.type_arg: expected declared type-param name, got unknown type-param 'Holder'" on every build (MEASURED), so a pin cannot be written where the default body's own calls must dispatch; (b) the same bracket on the non-defaulted `Holder.size` runs to 42 since WI-20260929-0RP29's tenth pass (`narrowed_to_named_witness`, part 120 of `wi_0rp29_review9_regressions_test`) and died "ambiguous dispatch of `Holder.size` on carrier `Box`: 2 implementations are supplied" at run time before it (MEASURED: the trees before the ticket and the eighth review saw). The tenth pass re-dispatches at the named witness in ONE place — `check_apply_iter`'s carrier-parameter route, after the first `dispatch_spec_op_cached` answers `NoCandidates` — because `resolve_at_goal` returns `NoCandidates` as a permissive fall-through before its step 0 reads the pin. The defaulted-operation tree in `check_apply_iter`, WI-606's `PinNow` and the defaulted route in call_class.rs do not, and a pinned call reaching them over a slot no type decides is left to the run time, whose value-directed dispatch reads no bracket. FIX: (1) inside `resolve_at_goal`, a pinned spec with no candidates resolves at the named witness's covering instance (`covering_witnesses_named`, the helper dispatch and projection already share) or returns step 0's loud `NoMatch`, and `narrowed_to_named_witness` with its re-dispatch goes; (2) the witness bracket is accepted on a defaulted spec operation and reaches the default body's dictionary. ACCEPTANCE: (a) runs to 42, and to 7 with `[Holder = OptStrBoxH]`; (b) still runs to 42; a pin naming a witness that does not cover the receiver refused at load; no pin over two covering witnesses still refused loudly (say where: load or run time); full workspace green via rustland/scripts/test.sh.

