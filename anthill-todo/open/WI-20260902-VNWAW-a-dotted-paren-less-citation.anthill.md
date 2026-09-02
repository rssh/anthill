## Attributes

- id: WI-20260902-VNWAW-a-dotted-paren-less-citation
- created: 2026-09-02T11:59:36Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T11:59:36Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DOTTED PAREN-LESS CITATION IN A GOAL POSITION MISSED CZJ2N'S TWO READINGS — and `not` of one answers ONE.

MEASURED BY ME on the delivered tree (found by /code-review during WI-20260902-8K4RB,
reproduced independently, one file, six rules):

  namespace zzdot.inner
    operation flag() -> Bool = true
    rule ctrlBare(1)  :- flag          -- CONTROL, unqualified, same namespace
    rule ctrlParen(1) :- flag()
    rule ctrlNot(1)   :- not(flag)
  end
  namespace zzdot.outer
    rule dotBare(1)  :- zzdot.inner.flag
    rule dotParen(1) :- zzdot.inner.flag()
    rule dotNot(1)   :- not(zzdot.inner.flag)
  end

  goal          unqualified      dotted
  bare               1              0     <- silently empty
  paren              1              1
  not(bare)          0              1     <- WRONG ANSWER

`not(zzdot.inner.flag)` SUCCEEDS: negation-as-failure over a goal that cannot run, the
exact class WI-20260902-CZJ2N removed for `:- flag` and WI-20260902-8K4RB removed for an
equation subject. The dotted spelling kept it. The program loads clean, exit 0.

THE MECHANISM, as the reviewer traced it (NOT re-traced by me — verify before fixing):
WI-20260901-719FJ's dotted-citation branch in `build_body_atom_occurrence_inner`
(load.rs ~22852) returns a bare `Expr::Ref`/`Expr::Ident`. The ONE-SEGMENT `Term::Ref` /
`Term::Ident` arms ~45 lines above it (~22792 / ~22808) later gained two readings from
CZJ2N — `nullary_op_call_or_ref` (a nullary OP goal becomes an `Expr::Apply`, so it
REDUCES rather than being matched) and `bare_entity_goal_occurrence` (§8.3's all-fields-
fresh pattern). The dotted branch got neither. The reviewer reports the entity half too:
with `fact acct(n: 1)` stored expanded, `:- zzent.inner.Acct.acct` answers nothing where
the bare `:- acct` answers.

WHY IT IS ITS OWN TICKET rather than folded into 8K4RB: different site, different
mechanism, and the fix carries its own back-out table — CZJ2N's own commit message
records that adding `nullary_op_call_or_ref` needed a measured pair (canon in, hook out)
to show the WI-580 hook fired identically, and the same is owed here per reading.

ACCEPTANCE: the 3x2 table above answers 1/1/0 in BOTH columns; and the ENTITY half has
its own pair (a dotted bare entity goal answers exactly as the unqualified one does).
CONTROLS: the DATA-slot reading must not move — CZJ2N's rule is that a bare fielded entity
is §8.3's pattern in a LOGICAL position and a REFERENCE in a data slot, so a fixture that
only drives the goal position would pass with the data reading broken; and the
parenthesised dotted spelling must keep answering, which it already does, so a fixture
asserting only IT measures nothing. Say at the site which rows each back-out fails.

