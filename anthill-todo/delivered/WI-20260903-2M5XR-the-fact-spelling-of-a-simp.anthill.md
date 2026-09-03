## Attributes

- id: WI-20260903-2M5XR-the-fact-spelling-of-a-simp
- created: 2026-09-03T12:22:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-03T17:30:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE `fact` SPELLING OF A `[simp]` EQUATION LOSES THE UNBOUND-RHS-VARIABLE VERDICT, SO A MALFORMED RULE LOADS CLEAN.

MEASURED on the WI-20260903-W9D4Z tree (`zzq`, with `operation sink(r: Int64) -> Int64 = r`):

| program | errors |
|---|---|
| `rule fu(?x) <=> sink(?y) [simp]` + `operation c(n) = fu(n)` | 1 — `4:24: type mismatch in <bottom>.expr: expected surface expression, got bottom / post-elaboration form` |
| `fact fu(?x) <=> sink(?y) [simp]` + the same consumer | **0 — it loads clean** |

AND THE `fact` SPELLING GENUINELY FIRES, so this is not a dead shape: `fact dbl(?x) <=> ?x + ?x [simp]` with `operation drive(n: Int64) -> Int64 = dbl(n)` evaluates `drive(5) = 10`, exactly as the `rule` spelling does. A live firing site accepts a rule whose RHS names a variable the LHS never binds, and splices a bare `Expr::Var(Global)` where `⊥` belongs.

THE MECHANISM, READ NOT GUESSED. `simp_rewrite::bottom_out_unbound` keys on `fresh` — the rule's OWN frame, as `open_equation` opens it — and returns early on `fresh.is_empty()`. A `fact`-asserted clause reaches the KB through `assert_fact` → `assert_rule` → `assert_rule_nodes`, which sets `globals: Vec::new()` (`kb/mod.rs`), so `open_equation` hands back `fresh = []` for every `fact` equation while `match_view_oneway` still binds the head's own Globals through the WI-635 "legacy Global-var arity-0 head" path. The early return is a fast path for well-formed rules; here it is the whole population.

SO THE REPAIR IS NOT IN `bottom_out_unbound`. Removing its early return changes nothing — the walk gates on `fresh.contains(v)`, which is empty for the same reason. Either the `fact` path must record its head variables as `globals` (which reaches `with_fresh_vars`' arity-0 routing and the `head_has_vars` flag — WI-624/WI-635, so it is not a local edit), or the malformed-ness has to be decided somewhere other than the fire. It is a LOAD-TIME property: an RHS variable the LHS does not bind is visible statically, in both spellings, before anything fires. WI-20260903-FCZ3N chose a fire-time verdict deliberately (`bottom_out_unbound`'s doc says why it is not a load refusal), so moving it is a decision, not a cleanup.

WHY NOTHING CAUGHT IT. FCZ3N's `an_unbound_rule_variable_in_a_fired_rhs_is_still_refused` drives only the `rule` spelling, and `every_fireable_source_equation_keeps_its_rhs_occurrence` — the census that DOES cover both producers — asserts only that the field is populated, which it is. The corpus contains no `fact` equation with an unbound RHS variable.

ACCEPTANCE. `fact fu(?x) <=> sink(?y) [simp]` with a consumer is refused, with the same sentence the `rule` spelling gives, and `fact dbl(?x) <=> ?x + ?x [simp]` still fires and still answers 10 — drive the value, not the load. Say which rows fail when the change is backed out, and state which spelling each row exercises: the defect is precisely that one spelling was covered and the other was not, so a repair pinned on the `rule` spelling alone would measure nothing.

Raised by `/code-review` on WI-20260903-W9D4Z (finding 2 of 4), and confirmed by the measurements above rather than taken from the report. Belongs to WI-20260903-FCZ3N, which is delivered.

## Changes

### 2026-09-03T17:30:47Z — feedback — claude

DELIVERED.

THE ROOT, TRACED RATHER THAN READ OFF THIS TICKET. A probe on `simp_rewrite::open_equation` over both spellings of ONE equation: `rule fu(?x) <=> sink(?y) [simp]` opens `arity=2, fresh=2`; `fact fu(?x) <=> sink(?y) [simp]` opens `arity=0, fresh=0`. The two reach the KB by different asserters — `load_rule` through `assert_rule_debruijn_with_nodes`, which closes the clause's variables into DeBruijn slots, and `load_fact` through `assert_fact`, which leaves `arity`/`globals` at their ground-fact defaults so the variables stay `Var::Global`. `open_equation` had nothing to OPEN and answered `Vec::new()` — as though the rule had no frame, rather than a frame in the other representation. `bottom_out_unbound` keys on that set and returned immediately for every `fact` equation.

THE FIX IS ONE ARM, AND THE CODEBASE HAD ALREADY NAMED THE CONCEPT. `resolve.rs` documents that `match_view_oneway` binds "the opened `fresh` globals for a DeBruijn rule, OR the head's own `Global` vars for a legacy arity-0 head". The MATCHER had both cases; the channel carrying that set onward had one. `open_equation`'s arity-0 arm now returns `kb.collect_vars(head)`, so the two agree by construction instead of by convention.

THE OTHER TWO READERS OF `fresh`, CHECKED RATHER THAN ASSUMED:
 * `typed_pattern_bounds_hold` — UNREACHABLE with an arity-0 head, measured: `fact tp(?x: Int64) <=> …` is refused at load ("WI-582: a variable type annotation (`?x: T`) is only meaningful in a rule head pattern").
 * `open_debruijn_node` — acts only on `Expr::Var(DeBruijn)`, so a no-op on a head that has none. DRIVEN, not asserted: `a_well_formed_equation_still_fires` computes `drive(5) = 10` through it.

ACCEPTANCE, MET. Both spellings now give BYTE-IDENTICAL refusals (`4:24: type mismatch in <bottom>.expr: …`), and both still FIRE: `dbl(?x) <=> ?x + ?x [simp]` gives 10 and WI-634's projecting `pk(?q) <=> ?q [simp]` gives 7, in `rule` and `fact` alike. Asserted as an AGREEMENT rather than two expectations: the `rule` half was already right, so a row pinning only one spelling measures nothing.

BACK-OUT (`(head, Vec::new())`): EXACTLY 1 ROW, `a_malformed_equation_is_refused_in_both_spellings`, and only on its `fact` half — the defect stated exactly. The two capability rows are green under it by design; they guard the OPPOSITE risk, that a widened frame bottoms out a variable the LHS DID bind.

POPULATION, CENSUSED: 709 `open_equation` calls over `wi_tests`, 517 DeBruijn and 192 arity-0. Of those 192, **111 now receive a NON-EMPTY frame** where they got `Vec::new()` — 101 of two variables, 10 of one, 81 genuinely ground. So the change is live on a population the corpus already exercises, not just on its own fixture.

── AND `/code-review` (high) FOUND A REGRESSION IN WI-20260903-W9D4Z, WHICH IS FIXED HERE ──

The dedup that ticket shipped keyed UNLOCATED errors by their rendering alone. Two sorts in ONE file, each with an `operation div` raising an undeclared effect: the typer names the operation by its SHORT name and attaches no span, so `Money.div` and `Cash.div` render byte-identically. MEASURED: the batch went **14 errors to 8**, and `Cash`'s two findings were GONE — the author saw one `div.effects` line, could not tell which sort, and had no way to learn a second existed. That is §8.5's "a diagnostic list is never silently truncated" failing on the population W9D4Z touches.

MY FIXTURE COULD NOT CATCH IT: `a_span_less_diagnostic_raised_twice_by_one_pass_is_one` had ONE sort, so it was homogeneous on the axis that decides, and it passed while a diagnostic was dropped.

REPAIRED: an error with NO LOCATION is now kept unconditionally. A located error is pinned by its file and position; an unlocated one has only its sentence, and a sentence that does not name its subject is not an identity. The fixture's own control is inside the batch — the provider errors for the same two sorts DO name their carrier and were never at risk, which is what says the defect is the MESSAGE's. Cost: W9D4Z's second census family is no longer collapsed, so a genuine duplicate of that message prints twice. That is the smaller harm, and only the drop was silent. ROOT FILED as WI-20260903-2VPHT (qualify the op, or give the diagnostic a span).

W9D4Z's rows and axis figures moved with it: the stale row is replaced by `an_unlocated_diagnostic_is_never_collapsed` (the exemption) and `two_sorts_sharing_an_op_name_keep_both_findings` (the heterogeneous row that was missing). Axes RE-MEASURED: axis 1 (no dedup) 3 -> **2 rows**; axis 2 (drop file identity) **2 rows**, one still `wi835`'s pre-existing cross-file row; axis 3 (drop the message) 12 -> **11 rows**, TEN pre-existing across eight files.

THE REVIEW'S SECOND FINDING IS ALSO ANSWERED. `collect_vars` returns TERM-WALK order, not slot order, while `open_debruijn_node` and `typed_pattern_bounds_hold` index `fresh` POSITIONALLY. Both are unreachable here (argued above and measured), but the FAILURE MODE degraded: an out-of-range `get` used to answer `None` and both readers took their safe path, where an in-range one would now answer an ARBITRARY variable. The bounds half is now a `debug_assert` at that arm; the node half is driven by the firing row.

NO SCALAND MIRROR: scaland has no `simp_rewrite`, no `open_equation` and no typer — neither the firing machinery nor the frame exists there. `sbt test` re-run green (539 + 23 + 1, 0 failures) for the acceptance field.

TESTS: `rustland/anthill-core/tests/include/wi_2m5xr_fact_spelling_frame_test.rs` (3 rows), plus W9D4Z's file re-worked (11 rows). Full workspace suite green: 36 binaries, 0 compile errors, 0 failures, 6 369 tests.

