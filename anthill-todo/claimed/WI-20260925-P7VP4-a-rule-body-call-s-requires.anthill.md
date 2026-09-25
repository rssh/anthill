## Attributes

- id: WI-20260925-P7VP4-a-rule-body-call-s-requires
- created: 2026-09-25T13:01:52Z

- status: Claimed
- status_agent: claude
- status_at: 2026-09-25T13:02:08Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A RULE-BODY CALL'S `requires` BECOME CONDITIONS OF THE CLAUSE — requirement-channel.md §5, "The call site drives it; `require[X]` is only the explicit form" (recorded 2026-08-07, never built).

TODAY. A rule-body call to an operation gets its dictionary INSIDE the call: the typer builds it at a concrete carrier (WI-415, `build_concrete_dispatch_dict`); otherwise the SLD bridge derives it per call from the argument values (`resolve_bridge_requirements`). It is not a condition of the clause, so a citation cannot supply it. The weave, `req_insertion::run`, walks `kb.op_bodies` only. 060-implementation §8.9 recorded the user's call (2026-09-09) — "A rule needs no restatement of a requirement its callee declares" — and §8.10 then says "§8.9's question has no stage": that is how it fell through.

DESIGN (requirement-channel.md §5). One `find_dictionary` goal per callee slot, immediately before the call, carried by `apply_within(fn = op, args, requirements = [...])`. A written `require[X]` pre-binds one and meets the generated goal in check mode. Nothing is emitted where the typer already pinned the dictionary. The generated reads are the clause's implicit parameters (op-to-rule-requirement-channel.md §0), so a citation routes them (060-implementation §7.3, S2).

DECISION (user, 2026-09-25): INFER. The callee's `requires` become the clause's conditions automatically; writing `require[X]` is how an author names or shares one. Load errors stay for what inference cannot cure: a concrete carrier with no provision (WI-20260917-NR6FJ, `check_rule_body_operation_requires`), a read no anchor grounds, two supplies for one entry. op-to-rule §7 step 1's refusal (`a(?x: A) :- b(?x)` with `a` holding no `Eq[A]`) narrows to a concrete carrier with no provision.

FIRST, the census: rule-body calls whose callee `requires` sit at a non-concrete carrier, in stdlib, examples and anthill-todo — the rows this moves.

ACCEPTANCE, driven by value: a rule calling an operation that requires `Eq[T]` at a rigid `T`, cited from an operation holding a rival `Eq`, answers through the CALLER's dictionary; uncited, it derives locally; a written `require` that disagrees with the supplied one fails loudly (WI-860). CONTROLS, stated at their sites: a concrete carrier (typer-built) is unchanged; NR6FJ's refusal is unchanged; classic-mini is unchanged (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

ORDER: built before WI-20260925-SHED7's rework, whose typed head's `SortDomain[T]` becomes the same kind of condition.

## Changes

### 2026-09-25T13:06:51Z — feedback — user

DECISION (user, 2026-09-25): A RULE SEES ITS ENCLOSING SORT'S `requires`. The user's example: `sort SortedList[T] requires Ord[T]` with `rule head(l: SortedList[T]) < head(tail(l)) :- true` — the `<` at `T` must use that `Ord[T]`. This OVERTURNS the rule `check_rule_body_requirements` documents ("A Horn rule does NOT inherit its enclosing sort's `requires` chain … so the in-body goal is the only declaration site") and 060-implementation §8.9's row I1 ≡ I3, which that doc comment was the only authority for (NR6FJ called it "settled" on that basis).

SO THIS TICKET HAS TWO SUPPLIES FOR A CLAUSE'S CONDITIONS, as an operation has: the enclosing sort's `requires` chain (the sort half) and the clause's own (written `require[X]`, and the callee demands inferred per the decision above). A callee demand at the sort's parameter is covered by the sort's slot — the call dispatches through THAT dictionary: supplied by a citation (the parent bundle at the citation's σ), else derived from the carried type of the value that pins `T` (`l` above). Row I1 flips: a rule inside `sort Holder requires Desc[T = Plain]` must not fold the spec default.

### 2026-09-25T13:50:37Z — feedback — user

INCREMENT 1 BUILT, NOT COMMITTED — a rule-body call to a SPEC OPERATION whose carrier is not known at load gets the condition its author could have written. `infer_rule_body_requirements` (typing/rule_requirements.rs), run after `install_typed_head_domain_goals` and before `record_find_dictionary_grounding`: one read `find_dictionary(Spec, op, args…, out: ?d)` per (spec, carrier arguments), placed before the goal holding the first call, every call of the group woven through `?d` (WI-1040's `weave_covered_call`). The carrier decision is `spec_op_call_carrier_outcome`, EXTRACTED from WI-642's `check_one_spec_op_requirement` so the two cannot disagree: DontFire refused there, Fire keeps its route, Suspend gets a condition here. Declined: builtin/host-implemented callees, carrier-less ones, specs nobody provides, defaulted members of a spec with no abstract member (WI-883), callees with no reader for a woven call, typer-pinned calls, specs the clause already `require`s, and EQUATIONS. Inferred reads do not count as declarations for WI-642/NR6FJ (provenance, `is_inferred_requirement_read`).

CENSUS (shipped corpus): the pass weaves ONE stdlib clause before the equation exclusion — String's inert `rule isEmpty(?s) <=> eq(length(?s), 0)` — and NONE after it; examples and anthill-todo: none. So nothing shipped changes behaviour.

TWO DEFECTS FOUND AND FIXED ON THE WAY. (1) `type_rule_bodies` re-types EVERY rule body on every later load phase and has no surface case for a woven call: one woven stdlib clause failed 138 workspace rows ("expected surface expression, got bottom / post-elaboration form") — a latent WI-1040 defect too, for any base program with a written `require`. It now skips a body holding a woven call (typed by the run that wove it). (2) Equations are excluded (an inert law is no clause).

MOVED BY DESIGN: `wi1043::an_unground_body_less_goal_binds_no_residual` — with a supplier the unground call is now woven and DELAYS (one conditional row, `?r` free) instead of answering nothing, which closes the WI-938 hook's recorded open half for that population. The row moved to a supplier-less fixture, which keeps it on WI-1057's guard (control re-measured: dropping the guard still fails it); the delay is pinned by `wi_p7vp4…::an_unground_woven_call_delays`.

ROWS (wi_p7vp4_rule_body_requirements_test.rs, 8): `cmp` with its `require` deleted answers 4/−4 under Descending/Ascending (−1 before); uncited −1; a concrete carrier keeps its own route; a second load phase over a woven clause loads and answers; no equation is woven (population); an unground woven call delays. Back-outs, each measured: inference → CASE + delay rows fail; re-typing skip → second-phase row fails; equation exclusion → equation row fails. Full workspace 7623 passed, 1 failed (the wi1043 row above, since moved and green).

THE WI-860 ACCEPTANCE ROW IS UNREACHABLE for an inferred read in a well-typed program: a citation routes a dictionary for the read's own type, so it can disagree with a UNIQUE local derivation only through a type mismatch. The written-read row stays WI-860's (`wi_5g28a…::a_projected_dictionary_is_read_and_checked`).

NEXT: builtins (`eq`, `<`) through a supplied dictionary — the user's SortedList example and stdlib Set's `PartialEq.eq` need it; the enclosing sort's `requires` as the supply; ordinary operations' own `requires` (census: no shipped call).

### 2026-09-25T13:57:17Z — feedback — user

DECISION (user, 2026-09-25): BUILTINS ARE LEFT TO WI-20260909-SM910. A rule-body `<`/`>` compares literals only and dispatches through nothing, so a supplied dictionary has nothing to reach until SM910 moves the registry behind value-directed dispatch. This ticket finishes without builtins: ordinary operations' own `requires` as conditions, and routing through the enclosing sort's `requires`. The user's SortedList `<` example waits for SM910. Builtin census, for SM910's cost question — calls whose carrier is not known at load: stdlib 1 (Set.contains's `PartialEq.eq` at `Set.T`), classic-mini 12 (`neq` 11, `eq` 1), webots 39.

### 2026-09-25T14:45:46Z — feedback — user

INCREMENT 4 BUILT, NOT COMMITTED — an ORDINARY operation's own `requires`. A rule-body call to a rule-less bodied operation with a dictionary chain, where some argument's type is not known at load, gets one SLOT read per chain slot — `find_dictionary(Spec, op, args…, slot: k, out: ?d_k)` — and is woven carrying all of them (`weave_covered_call` now takes N requirements). A slot read DERIVES NOTHING: a citation fills it (`op_slot_route` routes slot k of the callee's chain at the citation's argument types, pinning the CALLEE's parameters first and keeping a variable where `substitute_spec_via_subst` would decline one), and one left unbound is derived by the bridge as before — so an uncited clause is unchanged by construction. `reduce_op_value`'s `ApplyWithin` arm tells a slot weave from a dispatch weave by the callee (a spec op dispatches); `WovenDispatch` became an enum; `call_op_bridged` takes the supplied slots (all supplied → the frame is built from them alone; some → each stands in by frame name).

FIXED ON THE WAY: `is_inferred_requirement_read` looked the pass up with `try_resolve_symbol`, which never finds a pass name — every inferred read counted as the AUTHOR'S declaration and silenced WI-642's and NR6FJ's refusals (since increment 1). Now the intern map's `lookup`. NR6FJ's walk also reads a woven call; a ground argument (`plain()`, which carries no stamp) counts as known at load.

ROWS (13 in the file): `cite[A = Int64, WeakOrd = Descending]` over `rule viaOp(?a, ?b, ?c) :- Util.sign(?a, ?b, ?c)` answers 4/−4 (−1 before); uncited −1; an unfillable slot behind a woven call is still refused; a call whose arguments are known at load is not woven. Back-outs measured per axis (router slot branch, bridge override, intern lookup, NR6FJ woven reading, ground-argument check) — each fails its own row only. Full workspace 7629 passed, 0 failed before the last three rows; those pass in their file.

INCREMENT 2 — routing a rule's condition through its ENCLOSING SORT's `requires` — MOVED TO WI-20260925-0RRQP (user, 2026-09-25). MEASURED: in `sort Box[T] requires O: WeakOrd[T]`, a member operation sees `O = Descending` (4) while `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)` cited from it answers −1: rule-body typing ties `?x` to nothing (a per-call placeholder), so its condition cannot be matched to the `O` slot.

### 2026-09-25T16:49:11Z — feedback — user

CODE-REVIEW FIXES APPLIED, NOT COMMITTED (2026-09-25). The inference now: weaves every target in ONE pass over the original body (a nested woven call was lost and the load panicked); declines a spec-op call that does not align (`unreachable!` panicked the load); runs AFTER `record_find_dictionary_grounding` (a written `requires`'s inherited witness got woven first — "no such call"); weaves a GOAL-position call only in its functional-relation form (a declared-arity Bool goal answered nothing, WI-583's refusal was bypassed); descends through DATA positions only (a read hoisted out of a quantifier waited for ever). The slot arm hands back the WOVEN call when it must wait (a retry lost the caller's slots — goal-order-dependent answer). `op_slot_route` walks the pins to their end and refuses on a failed unification (routing depended on parameter order). The bridge derivation skips SUPPLIED slots (`resolve_bridge_requirements_except`: a tie at a slot the caller chose suspended the call). AND A LATENT 5G28A S2 DEFECT: an unrouted read's placeholder in a citation marker was `Value::Unit`, which the query lowering cannot spell — any citation with some reads routed and some not failed "cannot lower Value::Unit into a KB term"; it is an unbound variable now, skipped by `bind_citation_reads` as `Unit` was. Rows: +9 in wi_p7vp4 (20 in all), +3 in wi_shed7; every fix's back-out measured and fails its own row only. Full workspace 7641 passed, 0 failed. SKIPPED, recorded on SHED7 for its rework: the pin path's per-step term-store growth, and kernel-language.md (spec text waits for the user's review).

### 2026-09-25T20:29:44Z — feedback — user

CODE-REVIEW ROUND 2 FIXES APPLIED, NOT COMMITTED (2026-09-25). The inference: never weaves an UNPINNED BODY-LESS spec op in a VALUE slot — symbolic algebra (kernel-language §5.3); it had woven and dispatched it, so `?s <=> Shape.circle(?r)` bound the provider's result where the unwoven call binds the written term (a PINNED call is the typer's and dispatches either way); stops at DEFERRED data forms (lambda / let / match / if — a read hoisted before the goal ran for an `if` branch never taken and failed the clause); weaves a BOOL-VIEW goal (`rule less(?a, ?b) :- Util.isLess(?a, ?b)`), whose resolver gate now reads a woven head as the arity+1 hook does, so a citation's dictionary reaches it. The guard core asks BOTH provision channels (`carrier_provides_spec`): an inferred — or written — read of a witness-supplied carrier fired nothing and failed the clause silently; the load-side witness special case is gone with it. An unrouted read's marker slot is a GROUND sentinel, `__unrouted` (round 1's unbound variable made a negated, partly routed citation flounder in `step_naf`, and minted a term per evaluation). `op_slot_route` lets a SUBTYPE argument pin nothing instead of refusing the whole route. ONE undecided exit for both `ApplyWithin` arms: the DISPATCH arm too hands back the woven call when it must wait (the WI-938 hook stored the plain target and the retry re-derived a conditional provider's slots — measured by a NAR1X-shaped row with two element providers). NOT CHANGED, measured: WI-580's case split never meets a slot-woven call (an operation's own `requires` in an `eq` operand is stamped by the typer; a sort-level chain makes it a defaulted spec op). THE STATED LIMIT: a call in a `|`/`&` branch, a negand or a quantifier body keeps value dispatch — a read can only go before the top-level goal (the citation layout reads top-level reads), and there it runs whichever branch is taken (measured: hoisting out of a branch turns the other branch's definite answer conditional); pinned by `a_call_in_a_branch_keeps_value_dispatch` and `a_call_inside_a_quantifier_keeps_its_value_dispatch`. Rows: +9 in wi_p7vp4; fixtures reworked where round 1 relied on weaving a body-less op in a value slot (`below` → a defaulted `Scale.twice`). Every fix backed out, one at a time, over the domain and dictionary suites: each fails its own row(s). Full workspace 7655 passed, 0 failed.

