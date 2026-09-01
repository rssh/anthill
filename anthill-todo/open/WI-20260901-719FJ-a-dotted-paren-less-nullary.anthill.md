## Attributes

- id: WI-20260901-719FJ-a-dotted-paren-less-nullary
- created: 2026-09-01T12:24:10Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T12:24:10Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DOTTED PAREN-LESS NULLARY CITATION IS A `field_access` CHAIN, IN EVERY POSITION -- so as a
RULE HEAD it silently drops the whole rule, and as a GOAL it answers a residual.

MEASURED (rustland, WI-20260821-P85Z7's tree, with P85Z7 delivered):
  fact b(1)
  namespace nsx  rule tgt() :- b(1)  end
  rule nsx.tgt :- b(1)          -- loads clean; `nsx.tgt` holds ONE clause, not two
  rule nsx.tgt() :- b(1)        -- the twin: TWO clauses, the reference lands
and in GOAL position, `anthill query 'nsx.shared_pl'` answers
`conditional / residual: eq(field_access(nsx, shared_pl), true)` where
`nsx.shared_pl()` answers `true`. Both spellings of one nullary citation, opposite
programs -- P85Z7's shape, one segment over.

MECHANISM, CONFIRMED. The converter folds a multi-segment `name` into a MINTED
`field_access(object, Ident(field))` chain (parse/convert.rs, the `"name" | "absolute_name"`
arm). `head_subject_name`'s `is_minted` guard therefore refuses it -- correctly, since
the functor is `field_access` and not the source's -- so the head introduces nothing AND
references nothing: its clause is stored under `field_access`. P85Z7 fixed the BARE
spelling by reading `Term::Ident`; the dotted one is a different node.

WHY IT IS NOT A ONE-LINE PATCH, and why P85Z7 left it. The SAME chain is what a dotted
paren-less citation lowers to in EVERY position, and proposal 052 §6.7 gives it a MEANING
there: `try_qualified_rule_ref` reads `Sort.rule` with no trailing `(...)` as the
`Relation[T]` VALUE, deliberately, so a head cannot simply be re-read as a qualified goal
without saying what the goal position and the operation body do. Three positions, one
chain, and today only the value reading is decided.

CORPUS: ZERO sites of the head spelling (censused over every `.anthill` in the tree).
This is a correctness hole, not a migration.

ACCEPTANCE: drive it. `rule nsx.tgt :- b(1)` must either land its clause on `nsx.tgt`
(two clauses, the goal answering both) or be REFUSED naming the spelling -- not load
clean holding one. The control is `wi_p85z7_paren_less_nullary_head_test::a_dotted_paren_less_head_still_lands_no_clause`,
which PINS today's `Some(1)` and must be moved by this ticket. Say what the GOAL position
and an OPERATION BODY do with the same spelling, and drive whichever reading is chosen in
all three. cargo-test green via rustland/scripts/test.sh.

