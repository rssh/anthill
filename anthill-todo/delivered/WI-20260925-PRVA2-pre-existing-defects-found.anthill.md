## Attributes

- id: WI-20260925-PRVA2-pre-existing-defects-found
- created: 2026-09-25T22:22:51Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-26T12:29:52Z

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

## Changes

### 2026-09-26T08:39:53Z — feedback — user

(a) DELIVERED by WI-20260925-YNCY3 (item 1, not committed, claude 2026-09-26): WI-1040 weaves through the one-pass `weave_calls`; `weave_covered_call` is gone. Row `wi1040_require_clause_dictionary_test::a_covered_call_nested_in_another_covered_call_is_woven_with_it` — the load panicked on the call-by-call weave at 35e115c6. (b)–(e) remain.

### 2026-09-26T11:54:27Z — feedback — user

DONE, NOT COMMITTED (claude, 2026-09-26) — (b), (c), (e) and a bridge defect found on the way; (d) MOVED to WI-20260926-ACG10 (user); (e)'s refused order is WI-20260926-NEKR0 (user). /code-review (max) run over the change, its findings applied (below). Rows: wi_prva2_pre_existing_defects_test.rs (23), each back-out MEASURED and listed in its module doc.

(b) FIXED. `KnowledgeBase::functional_relation_goal` is the ONE gate of the WI-938 arity+1 hook, asked by `step_init`, by WI-670's `body_refuted_by_ground_conjunct`, and by P7VP4's weave decision (`woven_goal_has_reader`). The refutation no longer reads such a goal's zero discrim candidates as a refutation; it EVALUATES a ground one (`functional_relation_refuted`, sharing the hook's call builder `functional_relation_call`) and refutes only on a definite mismatch. `rule r(?x, ?c) :- ground(?x), Util.sign(?x, 5, ?c)` from `r(?x, ?c), num(n: ?x)` answered nothing and `-4` from the swapped conjunction; both answer `-4`. A ground FALSE conjunct (`sign(?y, 5, 0)` at `?y = 1`) is still refuted at opening; a ground TRUE one (HEAD refuted it too) delays.

(c) FIXED. `simp_guard_decision` (the guard core; `simp_guard_holds_core` is its outcome) reads every carrier once, then asks one of two questions by WHERE the carriers stand: every carrier at the spec's carrier parameter (`spec_carrier_param`; every one-parameter and self-representing spec) → the per-carrier question (`carrier_provides_spec`), now ORDER-INDEPENDENT (it returned at the first carrier it read, so `(unknown, non-provider)` waited where `(non-provider, unknown)` refused); a carrier elsewhere → the PROVISION question, `provision_admits_carriers`: a provision row that binds each such parameter at its carrier — skipping CONVERSION rows (`is_conversion_row`, now shared with the provider search `collect_provides_candidates`), a provider variable binding its parameters alike, a structural binding admitting no carrier, an unbound parameter admitting any. It refuses where the KNOWN carriers match no row and suspends otherwise. What decided a refusal (`GuardRefusal`) reaches the load check: a combination no provision binds is a new diagnostic, `NoProvisionAtCarriers` ("no provision of `Conv` binds `A = Int64, B = String`"), where the per-carrier sentence named whichever carrier was read last. The load reader no longer files a WITNESS-provided carrier as unknown (P7VP4 round 3): with (c) the filter hid a correct refusal — `Conv.conv(leaf(), "s")` beside `Meters provides Conv[A = Meters, B = String]` LOADED and answered `9`, `W.conv` run at `(Leaf, String)`. MEASURED: a woven `Conv.conv(?x, ?u, ?r)` at `(Meters, "km")` answers `7` (nothing before); both carriers known at load loads and answers `7` (refused before); `(Meters, 5)` stays refused, definitely; `require[Conv[A = Meters, B = String]], Conv.tag("km", ?r)` answers `3` (nothing before). Stdlib ops this reaches: `PersistentCollection.insert(c: C, elem: Element)` (`insert([1, 2], 3)` now loads and answers; HEAD refused it), `MutableCollection.insert`, `VectorSpace.vec_scale(c: F, v: V)`, `ModifyRuntime.set` (host-implemented, not woven). P7VP4's two affected rows re-documented (their back-outs had become false); the concrete-carrier row gained a weave-shape assertion so it still drives the decline. KNOWN LIMIT, recorded on ACG10: an unwoven rule-body call value dispatch cannot evaluate (`Conv.tag("km", ?r)` with no `require`) now loads and answers nothing, silently — HEAD refused it, for the false reason (c) removed; 068's class.

(d) MOVED to ACG10 with a measurement: there is no pinned/unpinned split — `WeakOrd.compare(1, 5) = -1` is refuted too.

(e) As stated UNREACHABLE — the typer itself refuses the `(Circle, Shape)` order (NEKR0). The reachable order had its own defect, fixed: `op_slot_route` tested a non-unifying argument against the WRITTEN parameter and routed nothing where the typer instantiates `A = Shape`. Every argument is now checked against its parameter AS PINNED, after all pins, by the typer's own `validate_arg_against_param` (both sides walked, its conversions accepted — an `Option[T = A]` parameter given a bare `A` routed nothing, pre-existing).

BRIDGE (not listed; user: fix inline). An operation evaluated FROM A RULE BODY receives operands on the resolver's carrier (WI-20260827-3ZNBC), and the eval-side query paths refused them: `lower_leaf` and `goal_value_to_term` lower through `value_to_term` (`fInt(x) = same(x).head.c` from `?r <=> Driver.fInt(3)` answered nothing, `malformed_query`; a negated parameter inside an `or` likewise), `rename_query_vars` passes a ground occurrence through (`seven.union(same(x))` was a debug-build PANIC), and `value_to_term`'s `Node` arm uses the total `try_occurrence_to_term` (a lambda or `if` operand hit `occurrence_to_term`'s `debug_assert!` — a panic, a `⊥` query in release; now a loud `malformed_query`). Also: `canonicalize_record_named_args` sorts with a linear scan (no per-call map).

REVIEW (/code-review max, 15 findings reported). Applied: every correctness finding above, the stale per-carrier comments, the weak test assertions, the hook's leftover nesting, the duplicated gate. Not applied, recorded on ACG10 (068): the body-less spec Bool goal answering nothing (NAF proves a falsehood), a newly firing @[simp] law leaving a value slot conditional, WI-670's hand-kept route list meeting 068's argument-dependent routes. Skipped: a memo for `provision_admits_carriers` (no shipped call reaches the provision question).

FULL WORKSPACE: 7697 passed, 0 failed. scaland testFull: 578 + 34 (1 skipped) + 1, all passed.

