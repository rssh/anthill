## Attributes

- id: WI-20260926-QPC89-a-run-time-dictionary
- created: 2026-09-26T08:49:07Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T08:49:07Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A RUN-TIME DICTIONARY DERIVATION RE-RESOLVES ITS PROVIDER TREE ON EVERY CALL — a rule-body query that derives one costs milliseconds. Found while measuring WI-20260925-YNCY3 (debug build, a scratch query-loop harness over the P7VP4 ORD fixture; HEAD 35e115c6 plus YNCY3's changes).

THE PROBLEM. `rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)` queried as `cmp(1, 5, ?c)` takes 3.2 ms a query, and 2.9 ms of it is ONE call: `resolve_with_rung` inside `fetch_dictionary`, deriving `WeakOrd[T = Int64]` for P7VP4's inferred read (rung `Consult`). The tree it builds is small — 5 nodes, depth 3 — so each sub-goal costs ~0.5 ms, and nothing keeps the result: the next query derives the same ground goal again. `WeakOrd[T = String]` (no rival providers) costs 2.1 ms; a leaf provision (`Desc[T = Leaf]`, 1 node) 0.02 ms. The bridged SLOT call pays the same (`viaOp(1, 5, ?c)`: 3.2 ms a query, `bridge_op_to_eval` 3.05 ms of it — `resolve_bridge_requirements` derives through `resolve`, the same `Consult` rung).

NOT A COLD CACHE (a first guess, recorded on YNCY3 and wrong): resolving the SAME goal again with no KB mutation between queries costs the same 3.2 ms, and so does `query_unary` on the KB inside a warmed interpreter. The interpreter's `plain()` (`cmp(1, 5).head.c`) answers in 0.6 ms only because its citation's argument types are known at load: the typer routes a dictionary there, and the run-time read merely CHECKS it (rung `Unranked`, which stands aside among `Int64`'s rivals at once). An uncited clause — every query, every rule goal — derives.

WHO PAYS: every uncited rule-body read that derives (P7VP4's inferred reads, WI-1040's written `require[X]`) and every bridged call that derives its frame, once per invocation. The typer already memoizes spec-op DISPATCH (`resolve_cache`, WI-226 Cache B — never invalidated after load, since `SortProvidesInfo` is constant then); the run-time routes call `resolve` / `resolve_with_rung` directly.

OPEN: memoize a ground derivation (goal ground, empty scope, keyed by rung) with a lifetime tied to the provides relation, as WI-226's Cache B is — or find why one sub-goal costs ~0.5 ms, which a memo would only hide.

ACCEPTANCE: the `cmp(1, 5, ?c)` query loop and the bridged slot call measured before and after; behaviour unchanged — full workspace green via rustland/scripts/test.sh, scaland testFull.

