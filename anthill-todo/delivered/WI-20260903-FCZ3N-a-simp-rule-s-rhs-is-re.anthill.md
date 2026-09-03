## Attributes

- id: WI-20260903-FCZ3N-a-simp-rule-s-rhs-is-re
- created: 2026-09-03T05:43:27Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-03T10:21:07Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `[simp]` RULE'S RHS IS RE-DERIVED FROM ITS TERM, SO A CITATION SPLICED BY A FIRE LOSES ITS PROVENANCE AND ITS SPAN.

THE THIRD TERM->OCCURRENCE ROUND-TRIP. WI-20260902-2SZ88 removed one (entity constructors) and WI-20260902-2NXAC removed another (collection literals), both by building the occurrence where the PARSE NODE is instead of re-deriving it from the KB term. `simp_rewrite::subst_visit` is the same shape in a different walk: it resolves a fired rule's RHS from a TERM (`kb.walk_view(term, subst)`) and rebuilds each node with `NodeOccurrence::synthesized_expr`.

MEASURED, on the delivered 2NXAC tree — `rule trig(?x) <=> sink(zzsimp.inner.rel) [simp]` beside `rule rel(1) :- base(1)`:

  simp rule WITH `operation consumer() -> Int64 = trig(5)`   -> 3 errors, ALL at ONE offset:
      "type mismatch in zzsimp.name: expected resolved name, got unresolved"
      "type mismatch in inner.name:  …"
      "type mismatch in rel.name:    …"
  simp rule with NO consumer                                 -> 0   (so all three come from the FIRE)
  the same expression written directly in an OPERATION body  -> 1, the true one
  the same expression written directly in a RULE body        -> 1
  a ONE-SEGMENT citation in the same simp fire               -> 1   (so the fire does not lose name resolution in general)

TWO LOSSES IN ONE. The three errors are the per-leaf cascade WI-20260902-4NEKZ removed, back because the spliced node arrives with `dot_chain` clear — `loader_chain_dotted_name`'s provenance gate then refuses to read the chain as the name it cites. And they are reported AT THE REDEX (`trig(5)`), where the name `zzsimp.inner.rel` does not appear, because the rebuilt node takes the redex's span.

THE FIX IS NOT `synthesized_expr`. That constructor hardcodes `dot_chain: false` DELIBERATELY and its doc says why: a SYNTHESIS is a new node a pass decided to build — the typer's own `field_access(recv, "field")` rewrite is the case — and it is not the dot the author wrote even when it expands one. Flipping it would re-admit exactly WI-20260901-92VA4's silent acceptance by another door.

THE FIX IS FOR A `[simp]` RULE TO KEEP ITS RHS OCCURRENCE. The RHS was written by an author and loaded as an occurrence with the bit and the span already correct; the rule stores a TERM and `subst_visit` rebuilds occurrences from it. `subst_visit` already has the right instinct in one arm — `Value::Node(occ) => results.push(occ)` reuses a MATCHED child and keeps its identity and provenance — so the shape of the answer exists; what is missing is the RHS's own occurrence being available to reuse the same way.

START BY SETTLING WHERE THE RHS OCCURRENCE WOULD LIVE: the rule already carries body nodes (`KnowledgeBase::rule_body_nodes`), so the question is whether an equational rule's RHS is among them or only in the term, and what `subst_visit`'s callers would have to thread.

ACCEPTANCE. `rule trig(?x) <=> sink(ns.inner.rel) [simp]` with a consumer reports ONE error, naming the relation it cites and located at the NAME rather than at the redex — with the four controls above unchanged (0 with no consumer; 1 for each direct spelling; 1 for the one-segment citation). Say which rows fail when the change is backed out.

RELATED, SAME CLASS, ALREADY SETTLED: `substitute_occurrence`'s five explicit arms had the mirror defect and were repaired in 2NXAC by building with `rebuilt_expr`. That measured 0 of 16 chain nodes actually losing the bit (a citation has no substitutable child) — do not assume this one is inert on that basis. It is NOT: the rows above are the measurement.

Split out of WI-20260902-2NXAC, whose findings (1) (2) (3) are delivered.

## Changes

### 2026-09-03T10:20:53Z — feedback — user

DELIVERED.

WHERE THE RHS OCCURRENCE LIVES — the question the ticket said to settle first. NOT among `rule_body_nodes`, and it never could be: `KnowledgeBase::is_equation` REQUIRES an empty body, so a clause carrying its RHS in the body list is by construction not an equation and nothing fires it. It is a THIRD thing a rule carries — `RuleEntry.rhs_node`, De Bruijn-closed against the same `globals` as the head, installed after the assert exactly as `head_span` and `type_bounds` are. `open_equation` still returns the head TERM's operands; the fire opens the stored occurrence against the SAME `fresh` globals.

WHAT `subst_visit`'s CALLERS HAD TO THREAD: the rule id and `fresh`. All three firing sites already held both — `simp_rewrite::try_fire`, `typing::try_fire_dot_rule`, `resolve::fire_simp_equation` — so `instantiate_rhs` / `instantiate_rhs_verbatim` each gained two parameters and nothing else moved.

ACCEPTANCE, MET. `rule trig(?x) <=> sink(zzfc.inner.rel) [simp]` with a consumer: ONE error, `sink.r (op-arg): expected Int64, got Relation[T = Unit, …]`, at 10:21 — the written `sink(` — where it was THREE at 11:35, the redex. The four controls are unmoved (0 with no consumer; 1 for each direct spelling; 1 for the one-segment citation).

BOTH PRODUCERS ARE WIRED, not just the one the ticket names: `fact tau() <=> 7 [simp]` is a bodyless equation too and loads clean (measured), so `load_fact` installs an RHS occurrence as `load_rule` does. Censused at delivery: 192 live equations, 90 with a written RHS, and ALL 21 of the `[simp]`/`[unfold]`-tagged ones — the only ones any site fires — have one, asserted by `every_fireable_source_equation_keeps_its_rhs_occurrence`.

THREE DISJOINT BACK-OUT AXES, each measured over the whole `wi_tests` binary (4 066 tests):
 1. KEEPING THE RHS OCCURRENCE (`build_rhs_template`'s stored arm answers `None`) — 4 rows: this file's two, plus `wi873_dispatch_rewrite_completeness_test`'s two.
 2. THE PROVENANCE RE-PARENT (`reparent_spliced` without `reparented_from`) — 4 rows, all of `wi_5r2xt_macro_spliced_call_name_test`. Needed for TWO reasons: 5R2XT's chain to the surface call, AND to stop a fire splicing the stored rule's own `Rc` — and its typer stamp cells — into two call sites.
 3. THE UNBOUND-VARIABLE VERDICT (`bottom_out_unbound` returns its input) — 1 row.
Green under all three BY DESIGN: `the_four_controls_are_unmoved` (yardsticks), `a_fired_simp_rhs_still_computes` (a term-derived RHS always evaluated right — it lost provenance, not meaning; this row fails instead if the occurrence path builds a DIFFERENT tree), `a_written_field_access_in_a_simp_rhs_is_still_not_a_citation` (which fails under the WRONG fix — `synthesized_expr` stamped `dot_chain: true`, WI-20260901-92VA4's silent acceptance by another door).

WI-873 HAD PREDICTED THIS AND SAID SO. Its `a_simp_expansion_with_two_calls_is_two_entries` asserted that two calls in one `[simp]` RHS share the redex's span, with the note "if a future change gave synthesized occurrences their own spans this would fail". It did. The arm now asserts their DISTINCTNESS, and the collision `nth_at_span` exists for moved next door to `one_rule_fired_at_two_redexes_collides_on_one_span` — ONE written call spliced at TWO redexes, which cannot stop colliding. Its own back-out (`r.nth_at_span = 0`) fails it at `got 1`, measured.

/code-review (high) RAISED 5. Findings 3 (the KB-side guard checked arity while its comment claimed the connective) and 5 (a second error-emitting walk discarded for every bodied equation) are FIXED — 5 by deferring the build to the install site rather than by the suggested parse-level `r.body` gate, which would have silently dropped folded-guard and `:- true` rules. Finding 4 (the `assert_fact` dedup overwrites) is VERIFIED reachable and KEPT last-write-wins with the reason recorded: `set_rule_head_span` three lines down is last-write-wins too, so first-write-wins here alone would leave one clause reporting its head at one file and its RHS at another. Findings 1 and 2 are split out — see below.

AND THE REVIEW'S OWN AFTERMATH FOUND ONE MORE, mine. Routing σ through `node_occurrence::substitute_occurrence` (right — σ over an occurrence must have ONE owner) silently DROPPED a verdict: that walk is the resolver's, where a surviving free variable is ordinary, so `rule fu(?x) <=> sink(?y) [simp]` went from 1 error to 0 — a malformed rule loading clean. Restored as `bottom_out_unbound`, keyed on the rule's OWN frame so a projecting redex variable (`pick(?q, 7) -> ?q`, WI-634) is untouched, and now reporting at `?y` itself.

SPLIT OUT, each measured on this tree:
 * WI-20260903-H054K — a rule variable in a TYPE position of a `[simp]` RHS is never instantiated. UNMOVED by this ticket (0 before, 0 after) while its GROUND twin went 0 -> 1; the block is `apply_subst` being term-world while the typer's fire binds `Value::Node`. 0 of 21 tagged equations carry a type position at all.
 * WI-20260903-W9D4Z — one authored mistake fired at N sites is reported N times, byte-identical. The consequence of moving the location to where the author wrote it; collapsing identical diagnostics is a whole-channel question.
 * WI-20260903-FC2X4 — a lambda in a rule head or body builds a malformed `Expr::Lambda` (its `param` is a reflect `Expr::Apply`, not a `NodeKind::Pattern`). PRE-EXISTING: a plain RULE BODY, a walk this ticket does not touch, reports the identical error. This ticket only made the `[simp]` RHS agree with it.

NO SCALAND MIRROR: scaland has no typer, no `simp_rewrite` and no `NodeOccurrence` module (WI-4NEKZ's finding). `sbt test` re-run green (539 + 23 + 1) to satisfy the acceptance field.

TESTS: `rustland/anthill-core/tests/include/wi_fcz3n_simp_rhs_occurrence_test.rs` (7 rows). Full suite green: 36 binaries, 0 compile errors, 0 failures; `wi_tests` 4 066.

