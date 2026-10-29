## Attributes

- id: WI-20261015-809JN-proposal-050-1-stage-1-a-write
- created: 2026-10-15T13:36:05Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T13:36:05Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-050.1, typing

## Description

Proposal 050.1, stage 1: a write through a let- or pattern-bound name is charged to the memory the name reaches, not dropped by the binder's kind — regions and alias classes in Γ, the re-key where a name's scope ends, and memory clauses read at calls.

PROGRAMS (measured on 5da88f1f; docs/proposals/050.1-memory-alias-and-maybe-connected.md, "The problem" and §8 D), over put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c]:
- operation f(p: Cell[V = Int64]) -> Int64 = let x = p, then put(x, 7); and operation g(l: List[T = Cell[V = Int64]]) -> Int64 = match l case nil() -> 0 case cons(h, rest) -> put(h, 8). Both load declaring nothing and write their argument: a go() over two fresh cells answers 7878. So does match p case x -> put(x, 1).
- viaBox(p: Cell[V = Int64]) = let b = box(c: p), then match b case box(c) -> put(c, 6): writes p, declaring nothing.
- readOnly(c, f), its slot g: (x: Cell[V = Int64]) -> Int64 @ {Eff, -Modify[x]} handed f above, moves the cell from 1 to 7 (answers 17).
- let k = kb(), then KB.assert(k, t, Thing), loads in an operation that declares nothing; KB.assert(kb(), t, Thing) is refused, "the call kb(…) produces a fresh value", even under effects Modify[kb].

EXPECTED (the proposal's §7 stage 1, by §1–§4 and §8 D):
- A memory half of Γ beside FlowEnv, forked and joined with it: the alias classes, joined by meet, and the regions — a persistent union-find a store unites and a join keeps every union of; a place holds region ids, never a copied set. Its fact view answers memory_alias / memory_maybe_connected to the Γ bridge as a computed relation.
- Producers: let x = y (an alias), let x = y.f (an alias of the path), a construction (it lies in its parts' own regions), a pattern (the whole scrutinee: an alias; a part: the scrutinee's regions), a lambda's captures, and at a call the callee's memory clauses — §4's caller half: memory_maybe_connected unites regions, memory_alias makes an alias.
- The drop — declare_local_resource / external_effects at a match arm's end and at the operation boundary — is replaced by §3's re-key where a name's scope ends: an alias of a parameter or an ambient resource, or of a field path off one, onto that one alone; any other name onto every parameter or ambient resource its regions belong to; a fresh region the operation returns is Modify[result]; one it does not return adds nothing. Every other scope end (a let body, an if branch, a lambda body) is measured for what reaches it.
- The stdlib package anthill.memory (stdlib/anthill/memory/) declares rule memory_alias(?a, ?b) and rule memory_maybe_connected(?a, ?b). kb() declares ensures memory_alias(result, kb), so k aliases kb and the write is Modify[kb]; an argument that is such a call names the resource, so KB.assert(kb(), t, Thing) loads under effects Modify[kb].
- kernel-language §5.6 states the rule: the proposal's §6 text.

ROWS: each program above refused with nothing declared and running once its write is declared (f with effects Modify[p] answers 7), in its spellings through a let, a pattern and a construction; the kb() pair; WI-314's local-state rows unchanged (a fresh cell written and not returned adds nothing; returned, Modify[result]); the suites' rows that wrote through a name without declaring it — refused now, measured and listed.

NOT IN THIS STAGE — the proposal's later stages, filed when this one delivers: a call's result that shares with an argument with no clause to say so (viaCall: first(l) matched and its cell written) — the body-side checks of the clauses, the stdlib census and a function value's inferred sharing are stage 3; the kill and the two cases, stage 4; the flow facts retired, stage 5; conditions at joins, stage 6. WI-20261014-7EZS6 (the application) depends on this ticket, and WI-20261014-6T5C6 on 7EZS6.

## Changes

### 2026-10-15T13:48:38Z — feedback — user

The proposal's later stages are filed as the sequence tagged proposal-050.1 (list --tag proposal-050.1): WI-20261014-7EZS6 (the application) and WI-20261014-6T5C6 (an arrow names its own parameter wherever written) depend on this ticket; stage 3 WI-20261015-X57XR (the clauses checked, the stdlib census, a function value's sharing) after 6T5C6; stage 4 WI-20261015-169VS (the kill by regions, and the two cases) after stage 3; stage 5 WI-20261015-038RQ (the flow facts retired) after 7EZS6; stage 6 WI-20261015-PTT6D-proposal-050-1-stage-6-planned (conditions at joins) after stage 4, PreOpened.

### 2026-10-29T19:01:18Z — feedback — claude

STAGE 1 IMPLEMENTED (2026-10-29). Decided with the user on the way: the kb() pair as written cannot hold — WI-20260902-JB6RS retired ambient places, so Modify[kb] is refused at its declaration; kb() and KB.loaded instead declare ensures memory_maybe_connected(result, kb_storage) over a pool sort KBStorage in anthill.reflect, and a write reaching it is refused at load (0 suite rows refused, counted with a recorder over the full gate and the families). The record is one per body with a branch per connection (equivalent to copies merged at the join); a scope end charges only its own names (arm, lambda body, operation). MEASURED: the ticket's f, g, match p case x, viaBox refused with nothing declared and run declared (7, 8, 6); readOnly(k, f) refused at the slot; the kb() writes refused in every binding spelling; KB.assert(kb(), …) stays refused by the place rule; WI-314's rows unchanged; no suite row wrote through a name without declaring it. The fact view answers both relations to the Γ bridge (connected / separate / unknown); outside an operation body a relation is an error. Rows: wi_809jn_memory_regions_test (20), each part backed out alone failing a row. NOT DONE HERE: scaland testFull (an sbt server another session holds); the viaCall hole stays stage 3. Filed beside it: WI-20261029-627CM (a body held to its own guarded row), which depends on this ticket.

