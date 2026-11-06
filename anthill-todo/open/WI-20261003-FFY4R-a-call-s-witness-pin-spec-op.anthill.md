## Attributes

- id: WI-20261003-FFY4R-a-call-s-witness-pin-spec-op
- created: 2026-10-03T12:31:41Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T12:31:41Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261105-P0QGF-proposal-073-stage-3-a-value

- tags: typing, proposal-073

## Description

A CALL'S WITNESS PIN (`Spec.op[Spec = W](…)`) IS READ BY ONE DISPATCH ROUTE ONLY. With `sort Holder { sort C = ?; operation size(c: C) -> Int64; operation size2(c: C) -> Int64 = size(c) }`, `sort Box { sort V = ?; entity box(v: V) }`, `sort OptIntBoxH { provides Holder[C = Box[V = Option[T = Int64]]]; operation size(c: Box[V = Option[T = Int64]]) -> Int64 = 42 }` and `sort OptStrBoxH { provides Holder[C = Box[V = Option[T = String]]]; operation size(c: Box[V = Option[T = String]]) -> Int64 = 7 }`: (a) `Holder.size2[Holder = OptIntBoxH](box(v: none))` — a DEFAULTED spec operation — is refused "type mismatch in Holder.size2.type_arg: expected declared type-param name, got unknown type-param 'Holder'" on every build (MEASURED), so a pin cannot be written where the default body's own calls must dispatch; (b) the same bracket on the non-defaulted `Holder.size` runs to 42 since WI-20260929-0RP29's tenth pass (`narrowed_to_named_witness`, part 120 of `wi_0rp29_review9_regressions_test`) and died "ambiguous dispatch of `Holder.size` on carrier `Box`: 2 implementations are supplied" at run time before it (MEASURED: the trees before the ticket and the eighth review saw). The tenth pass re-dispatches at the named witness in ONE place — `check_apply_iter`'s carrier-parameter route, after the first `dispatch_spec_op_cached` answers `NoCandidates` — because `resolve_at_goal` returns `NoCandidates` as a permissive fall-through before its step 0 reads the pin. The defaulted-operation tree in `check_apply_iter`, WI-606's `PinNow` and the defaulted route in call_class.rs do not, and a pinned call reaching them over a slot no type decides is left to the run time, whose value-directed dispatch reads no bracket. FIX: (1) inside `resolve_at_goal`, a pinned spec with no candidates resolves at the named witness's covering instance (`covering_witnesses_named`, the helper dispatch and projection already share) or returns step 0's loud `NoMatch`, and `narrowed_to_named_witness` with its re-dispatch goes; (2) the witness bracket is accepted on a defaulted spec operation and reaches the default body's dictionary. ACCEPTANCE: (a) runs to 42, and to 7 with `[Holder = OptStrBoxH]`; (b) still runs to 42; a pin naming a witness that does not cover the receiver refused at load; no pin over two covering witnesses still refused loudly (say where: load or run time); full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-06T07:20:43Z — feedback — claude

PLACED UNDER PROPOSAL 073 WITH THE USER 2026-11-06 (docs/proposals/073-abstract-values-are-instances.md §3: a spec's default body is typed once, and each call in it takes the instance the body runs at, the one its call passes). RE-RUN on 96766de8 over the description's program: `Holder.size2[Holder = OptIntBoxH](box(v: none))` still refused at load "unknown type-param 'Holder'" ((a), and the same with `OptStrBoxH`); `Holder.size[Holder = OptIntBoxH](box(v: none))` 42 and `[Holder = OptStrBoxH]` 7 ((b)); unpinned `Holder.size(box(v: none))` and `Holder.size2(box(v: none))` refused at load ("nothing here fixes `T` of `Option`"); `Holder.size[Holder = OptStrBoxH](box(v: some(1)))` refused at load (the witness does not provide the spec as instantiated); `Holder.size(box(v: some(1)))` 42. FOUND BESIDE IT: `Holder.size2(box(v: some(1)))`, the defaulted operation at a type fully known (`T = Int64`) and unpinned, ends UNDECIDED at run time, "ambiguous dispatch of `Holder.size` on carrier `Box`: 2 implementations are supplied": the default body's `size(c)` is dispatched by value on the head `Box` and the two witnesses tie. By 073 §3 that call passes `Holder`'s instance at `C = Box[V = Option[T = Int64]]` (`OptIntBoxH`'s) and the body reads it, 42; the row goes to WI-20261105-P0QGF. FIX (2) here is the same mechanism with the instance named by the bracket: `Holder.size2[Holder = OptStrBoxH](box(v: none))` passes `OptStrBoxH`'s, 7. FIX (1) (`resolve_at_goal` reads the pin when there are no candidates; `narrowed_to_named_witness`'s re-dispatch goes) is decided at load and stands as written. ORDER, decided: this ticket depends on 073 stage 3 (WI-20261105-P0QGF), which makes a default body take its call's instance; doing this first would pull that change in. The description's "left to the run time, whose value-directed dispatch reads no bracket" has no run-time route left after stage 3: a pinned call is decided at load or refused there. Tagged proposal-073.

