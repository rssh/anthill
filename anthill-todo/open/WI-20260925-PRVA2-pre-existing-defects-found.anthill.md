## Attributes

- id: WI-20260925-PRVA2-pre-existing-defects-found
- created: 2026-09-25T22:22:51Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T22:22:51Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

PRE-EXISTING DEFECTS FOUND WHILE REVIEWING WI-20260925-P7VP4 / WI-20260925-SHED7 — present before those tickets (HEAD 3bd051b4), not caused by them; each verified by code reading in the reviews of 2026-09-25, none yet driven by a test.

(a) WI-1040'S CALL-BY-CALL WEAVE LOSES A NESTED COVERED CALL. `record_find_dictionary_grounding` weaves with `weave_covered_call` one call at a time; weaving an inner covered call rebuilds its parent through `reassemble`, so the outer call's identity match misses: `debug_assert!(wove)` PANICS a debug build at load, and a release build leaves the outer call unwoven — value-dispatched, ignoring the clause's written dictionary. Example: `rule r(?a, ?b, ?s, ?r) :- ?dy = require[Desc[T]], ?dx = require[Scale[T]], Desc.describe(?a, ?s), Scale.scale(Desc.describe(?a), ?b, ?r)`. P7VP4 fixed the same defect for its own weave with the one-pass `weave_calls`; the fix is to weave WI-1040 through it and retire `weave_covered_call` (whose widened `requirements` slice has one caller).

(b) WI-670'S OPEN-TIME REFUTATION DOES NOT EXEMPT A FUNCTIONAL-RELATION GOAL. `body_refuted_by_ground_conjunct` (resolve.rs) exempts extents, Bool relations and scoping markers; an arity+1 functional-relation goal (`functional_relation_arity` — `Util.sign(?a, ?b, ?c)`), woven or not, has no clause candidates, so when a non-reorderable builtin (`ground`, `nonvar`, ho_apply) on a caller variable triggers the pre-check, the whole clause is declared REFUTED instead of delayed — the query answers nothing where a rotation would answer. (A WOVEN goal is exempt since P7VP4's third review round — `body_refuted_by_ground_conjunct` skips an `ApplyWithin`; the unwoven functional-relation goal is not.)

(c) A MULTI-PARAMETER SPEC'S GUARD DEMANDS EVERY CARRIER PROVIDE IT. `simp_guard_holds_core` asks each carrier parameter's sort to provide the spec, but a multi-parameter provision (`sort Meters provides Conv[A = Meters, B = String]`) is provided by its carrier-parameter's sort only: a rule-body `Conv.conv(?m, ?s, ?r)` with `?s: String` is DontFire — WI-642 refuses the load ("`String` provides no `Conv`") and a run-time read fails — while the operation-body twin loads and answers. P7VP4's second review round extended it to a WITNESS-provided first carrier, and its third undid that at load (the carrier filter is back) and declines to weave a call with a concrete carrier among its arguments — so today the shape loads and answers by value dispatch, and a WOVEN call with every carrier unknown at load still hits it at run time. The guard should ask the provision relation at the carrier types, not each sort alone.

(d) A BODY-LESS SPEC OP IN A VALUE SLOT IS SYMBOLIC WHEN UNPINNED, DISPATCHED WHEN PINNED — a substitution-transparency split. `rule below(?a, ?b) :- PartialEq.eq(WeakOrd.compare(?a, ?b), -1)`: `below(1, 5)` fails SILENTLY (the unreduced call is compared structurally with `-1`; `functor_leaves_an_unreduced_op_call` is false for a body-less op), and `not(below(1, 5))` SUCCEEDS, while `PartialEq.eq(WeakOrd.compare(1, 5), -1)` — its carrier known at load, the call pinned by the typer — holds. kernel-language §5.3 ("what the gate still declines") makes the unpinned reading symbolic algebra on purpose (`Set.insert`); whether a PINNED call should also stay symbolic, or an unpinned one over a ground carrier dispatch, is a SPEC question — discuss with the user before changing §5.3.

(e) `op_slot_route`'s ROUTE DEPENDS ON ARGUMENT ORDER under subtyping: `cmp2[A](x: A, y: A) requires Ord[T = A]` with citation argument types `(Circle, Shape)` (`Circle provides Shape`) routes `Ord[T = Circle]` — the one-way `unify_types` fallback accepts `Circle <: Shape` — while `(Shape, Circle)` routes nothing. `pin_type_vars` is the one-way match that pins the callee's variables with a subtype fallback on variable-free parts only.

ACCEPTANCE: each item driven by a row that fails before its fix (the example above as the fixture), or — for (d) — the user's decision recorded and the spec updated first. Full workspace green via rustland/scripts/test.sh; scaland testFull.

