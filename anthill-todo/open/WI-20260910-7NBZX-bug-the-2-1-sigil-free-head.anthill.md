## Attributes

- id: WI-20260910-7NBZX-bug-the-2-1-sigil-free-head
- created: 2026-09-10T06:16:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-10T06:16:03Z

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

