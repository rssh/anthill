## Attributes

- id: WI-20260910-7NBZX-bug-the-2-1-sigil-free-head
- created: 2026-09-10T06:16:03Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-10T08:17:05Z

- acceptance: cargo-test

- tags: vvm1r

## Description

BUG: the §2.1 sigil-free head parameter reaches only a rule's head ATOM in a CLAUSE — two other head shapes take the sigil spelling and silently disagree with it.

MEASURED 2026-09-10 on the tree delivering WI-20260909-C7ANM. Both rows are the same invariant that ticket exists for — one character apart, one answer — and neither is in its scope: C7ANM is about where a parameter's COLUMN lands, and these are about whether the reclassifier RUNS at all.

(1) AN EQUATIONAL HEAD — a silently DEAD rule. DRIVEN to a value, not inferred:

  rule pk: pick(?a: Red, ?b) <=> 7 [simp]   -- pick(red(), 1) simplifies to 7
  rule pk: pick(a: Red, ?b)  <=> 7 [simp]   -- pick(red(), 1) STANDS. loads clean.

`convert_rule_head_with_params` matches the head atom's `Term::Fn`; an equation's head is the CONNECTIVE (`Fn{<=>, [lhs, rhs]}`, no named args), so it declines at the first match and never descends into the LHS. `a: Red` stays a named argument, the LHS is arity-1-plus-a-key, and nothing can ever match it.

(2) A BODY-LESS HEAD — an "accepted and ignored" that its own refusal says must not exist. `rule f(?d, ?x: Red)` with no body is refused, citing that a DECLARATION stores no clause for the bound's one enforcer to run in. `rule f(?d, x: Red)` loads clean and declares `f`, its written parameter enforcing nothing. `declaration_clause_carrier` asks `head_carries_typed_column`, which detects only the minted `?x: T` marker; a parameter is a plain named argument it cannot see.

WHY ONE TICKET. One root — the reclassifier reaches only a head atom in a clause — and the two repairs land on the same function's admission. Filing them apart invites fixing one and leaving the invariant half-true.

WHAT TO VERIFY BEFORE BUILDING, and none of it is a diagnosis (WI-741's rule). For (1) the hook is the head-conversion call site, but the reclassifier would touch a `[simp]` LHS for the first time: `Rule::head_captures`' `...?args` index is computed off that same LHS, and the bound-refusal switch routes an equation through `is_directional_equation` rather than the relational arm. Measure both. For (2) the decider is a pure parse-level function while the §2.1 discriminator needs the KB (it resolves the type name to a sort) — so the repair is to move WHERE the refusal is decided, not to restate a weaker predicate there, which is the drift trap.

ACCEPTANCE. Driven, by value and by refusal, each against its sigil twin as the control: `pick(red(), 1)` must rewrite to `7` in both spellings; the body-less parameter head must be refused as its sigil twin is. Say which rows fail when each repair is backed out, separately — they are two axes. The controls that must pass either way: the two sigil spellings, and a `[simp]` equation with NO annotation (untouched). cargo-test green via `scripts/test.sh`.

BOTH GAPS ARE ALREADY RECORDED in `docs/kernel-language.md` §2.1 ("Where the two spellings do NOT yet agree"), written there by C7ANM because a gap parked only in a ticket rots. That text is the one to update when this lands.

## Changes

### 2026-09-10T08:17:00Z — feedback — user

DELIVERED. The baseline was RICHER than the ticket recorded — THREE divergences, not two, and the third was on the same axis as the first:

  SHAPE                 SIGIL                        SIGIL-FREE (before)
  `[simp]` equation     rewrites to 7                INERT (dead rule)
  UNTAGGED equation     refused, "nothing fires it"  LOADS CLEAN (bound silently ignored)
  body-less head        refused                      LOADS CLEAN (lone parameter too)

The untagged row is the ticket's (1) seen from the other side: the same missed reclassification that left the rule dead also let it escape the WI-903 refusal its twin gets. And the body-less row hits the LONE parameter, so it was never about columns.

TWO AXES, each backed out separately against the eleven rows of `wi_7nbzx_head_parameter_reach_test`:

 1. THE EQUATION-LHS PRE-PASS. At the head-conversion site, an equality-family head's LHS is handed to the reclassifier before the head is built. RUN FOR ITS EFFECTS, not rebuilt: the reclassifier memoizes into `term_map`, which `convert_term_inner` reads FIRST, so the ordinary connective walk picks the rebuilt LHS up on its own — no second copy of that walk. Order is the sigil form's: the LHS's parameters enter `rule_param_vars` before the RHS converts, so an RHS reading one bare gets the clause variable (driven — `idr(a: Red) <=> wrap(a)` rewrites `idr(red())` to `wrap(red)`). 4 of 11 fail on back-out.
 2. THE SHARED CLASSIFICATION at the declaration refusal. `declaration_clause_carrier` asked `head_carries_typed_column`, a parse-level test that sees only the minted `typed_var` node. Rather than restate §2.1's four gates beside it — the drift trap the ticket names — the converter's gates were SPLIT OUT as `classify_rule_head_params` and both readers now call it. 1 of 11 fails.

THE GATE IS THE WHOLE EQUALITY FAMILY, and that was /code-review's find, not mine. My first cut used `parse_equation_lhs` — "is this a DEFINING equation" — which is `<=>` alone since WI-888. A GUARDED `=` is a firing rewrite (WI-20260820-8RJK8) and three ship in the stdlib; MEASURED, `idr(?a: Red) = wrap(?a) :- g [simp]` rewrote and `idr(a: Red) = wrap(a) :- g [simp]` did not. The right gate is no harder than the SIGIL form's, which tests no connective at all: `?a: Red` lowers wherever it sits, and the connective decides only what the install site does with the bound afterwards. `===` needs no carve-out — it fires in NEITHER spelling. That arrangement is measured as a THIRD back-out: the narrow gate fails exactly one row, which is that row's whole reason to exist.

FOUR MORE /code-review FINDINGS, all fixed here:
 * THE BOUND WAS NEVER ASSERTED. My headline row proved the rule FIRES, not that the bound is ENFORCED — a reclassification that installed no bound would have passed every equation row. `the_bound_on_a_reclassified_lhs_is_ENFORCED` drives `pick(blue(), 1)` and asserts it STANDS, in both spellings.
 * The bail-out rollback used a length MARK, which would also drop a `?x: T` bound pushed by the NON-parameter branch's `convert_term` — and the fallback cannot re-collect it, because `convert_term_inner` returns on the memo before the `typed_var` strip. Parameter bounds are STAGED and appended only on success, so no other writer is touched.
 * GATE (1) IS STRUCTURALLY INERT ON AN EQUATION LHS: an operation is neither a constructor nor a sort, so every `name: Sort` there is a parameter and 055's "a sort is a legal argument VALUE" reading has no spelling on such a head. NOT A NEW POLICY — a relational predicate head already reads `rule p(?v, kind: Int64)` the same way, and MEASURED all four rows (relational/equation x sigil/sigil-free) agree. Corpus scan 2026-09-10: no `.anthill` file writes such a head, so the loss is latent. Stated at the classifier, since the 87-head census it carries counted HEAD-NODE named args and an equation's head is the connective.
 * The §2.1 doc block was left anchored on `classify_rule_head_params` by my own split — my recorded footgun, "a doc insert anchored on a `fn` line steals its doc". The build half now has its own.

ONE FINDING DECLINED, with its reason at the site: the carrier refusal outranks the located WI-20260821-TTHRK "nothing was minted here" message inside a `provides … language … end` block. BOTH ARE LOUD — nothing is silently accepted, which is the property this ticket is about — and putting the more fundamental refusal first means restructuring an arm whose final branch is where a VALID declaration lands.

CONTROLS, each stated at its site and each naming a widening that would satisfy every failing row: an unannotated `[simp]` equation still fires (fire everything), an untagged unannotated one still loads (refuse every untagged equation), a body-less head with nothing to enforce still declares (refuse every declaration), an entity-constructor CLAUSE head is untouched (reclassify by spelling), and a `===` head is unchanged in both spellings (make `===` define).

SPEC: `docs/kernel-language.md` §2.1's "where the two spellings do NOT yet agree" list — written by C7ANM — is replaced by what now holds, and proposal 060 §2.1 step 2 says the classification is asked at every head that has one.

WORKSPACE: 36 binaries, 6777 passed, 0 failed via scripts/test.sh. `/code-review` run twice; every finding of both passes is fixed here or declined with a reason at the site.

