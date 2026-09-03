## Attributes

- id: WI-20260903-2M5XR-the-fact-spelling-of-a-simp
- created: 2026-09-03T12:22:07Z

- status: Open
- status_agent: claude
- status_at: 2026-09-03T12:22:07Z

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

