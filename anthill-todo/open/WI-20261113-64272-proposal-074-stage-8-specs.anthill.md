## Attributes

- id: WI-20261113-64272-proposal-074-stage-8-specs
- created: 2026-11-13T23:02:01Z

- status: Open
- status_agent: claude
- status_at: 2026-11-13T23:02:01Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1, WI-20261113-FCMJA-proposal-074-stage-6-x-t-read

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 8 — SPECS OVER A TYPE CONSTRUCTOR (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§6; H1–H5, G1–G3). An operation's higher-kinded parameter, `lift[F[T]]` (H2), fixed by a call's bracket, an argument or the expected type; a sort filling a constructor slot by its unwritten parameters in order (H4), `provides Monad[M = Box]` loading; a requirement's constructor read through it (`requires Monad[M = F]` making `M[T = A]` read `F[T = A]`, refused today); `m.M[Int64]` off a dictionary parameter (H1); §5.4's member spelling at a higher-kinded member (H3, which loads and dies today); a constructor's dictionary a sub-dictionary of a provider over it (H4's `OptionTMonad`); `TypeValue` at a sort with unwritten parameters (H5, with stage 6's value read); a row parameter by use (G1–G3). Depends on stages 1 and 6. Rows: H1–H5 and G1–G3 driven to their answers. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-13T23:07:50Z — feedback — claude

H5 REVISED AFTER REVIEW (proposal 074 §6, decided with the user 2026-11-13). TypeValue at a sort with unwritten parameters keeps one sub-dictionary per declared parameter in declaration order — the layout kb/type_value_derive.rs states and eval::builtins::type_value_of_self reads by position and counts — and an unwritten parameter's is an open-slot dictionary, Dictionary(impl: …Unwritten), whose type_value() leaves the parameter unwritten. One sub-dictionary per WRITTEN argument (the first draft) made Pair[A = Int64] and Pair[B = Int64] one dictionary. A parameter inference leaves free is one left unwritten (the user: an inferred type and a written one behave the same): this refines the 2026-11-03 rule that a free type variable owing a requirement is refused at load — written or inferred alike, the requirement is answered where its spec has an answer at an open slot, which TypeValue alone has, and refused otherwise. ROWS: TypeValue.type_value[T = Pair[A = Int64]]() is Pair[A = Int64] and not Pair[B = Int64], and the reverse; tyOf(none) over tyOf[B](x: B) -> Type requires TypeValue[T = B] = B answers Option, as tv[X = Option]() does (both refused today, measured on 4f606100: "TypeValue[T = Option] cannot be supplied"); a requirement of Additive at a free slot and at an unwritten one refused alike.

### 2026-11-13T23:23:19Z — feedback — claude

ROW ADDED AFTER THE THIRD REVIEW (proposal 074 §6, H2, decided with the user 2026-11-13): where a call's types fit two constructors, the call is refused at load, naming both and the bracket that picks one. let p: Pair[A = Int64, B = Int64] = lift(7) over lift[F[T]](x: Int64) -> F[T = Int64] requires Monad[M = F] fits F = Pair[A = Int64] and F = Pair[B = Int64]: refused, lift[F = Pair[A = Int64]](7) loading. Kinds count: let e: Eff[E = {}, T = Int64] = lift(7) has one solution, F = Eff[E = {}], E being a row. Neither the last parameters nor the providers of the clause choose.

### 2026-11-24T23:00:29Z — feedback — user

PART 1 OF 6 DELIVERED (2026-11-24, d9f5f26a9): H4's rule. The stage was split with the user into six parts, one ticket, a commit per part: (1) constructor fill and order; (2) a requirement's constructor read through it and a constructor's provider held inside another (UseM, H4's OptionTMonad); (3) an operation's higher-kinded parameter (H2, H3, the two-constructor refusal, H3's silent ?_); (4) a provider at a higher-kinded spec and m.M[Int64] off it (H1, G2); (5) TypeValue at unwritten parameters (H5); (6) rows by use (G1, G3). MEASURED at the start (today's tree): Monad.pure[M = Option](7) typed M[T = Int64]; H3 answered ?_ silently (the proposal measured a run-time death); the rest as the proposal's table. Part 1 decisions with the user: a provider at its own parameters (Monad[M = Self], Option[T = T], Result[E = E, T = T]) is refused naming the constructor, the stdlib's three provisions and twelve fixture files rewritten; where an argument fits two constructors a spec's own parameter is fixed by its provisions (Result[Boom, Int64] takes Result[E = E]'s), an operation's own parameter keeps H2's refusal. Rows wi_64272_constructor_slot_test (10); back-outs 4 pieces over anthill-core, a fifth removed for failing no row; gate 12735 / 0, families green on both carriers, scaland green. Found, not fixed, not ticketed: 8 higher-kinded rows fail under ANTHILL_TEST_NODE_CARRIER=1 on the parent commit too.

### 2026-11-25T07:40:57Z — feedback — user

PART 2 OF 6 DELIVERED (2026-11-25, 4a834bfc5): a requirement's constructor read through it (UseM, OptionTMonad). Decided with the user 2026-11-25: a sibling call at another instance than the body's, which ran the body's provider at the wrong types (WI-80ZV8's known issue (a), plain and higher-kinded alike), is refused at load unless a requirement hands a provider at that instance, on both routes (self-recursive and own-carrier); census: no other row relied on it. The node carrier's deep walk keeps a higher-kinded head (four wi_xgrkz rows that failed there before the stage now pass; four wi_cxr5b two-application rows still fail there, as before). Rows wi_64272 13 in all; back-outs over anthill-core, two removed for failing nothing; gate 12740 / 0, families both carriers, scaland green.

