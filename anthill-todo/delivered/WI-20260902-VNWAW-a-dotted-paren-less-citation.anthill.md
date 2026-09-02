## Attributes

- id: WI-20260902-VNWAW-a-dotted-paren-less-citation
- created: 2026-09-02T11:59:36Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-02T13:56:54Z

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

## Changes

### 2026-09-02T13:56:48Z — feedback — user

DELIVERED. Both halves of the ticket's table answer 1/1/0 in both columns, and the entity
half answers cell-for-cell what the one-segment spelling answers.

THE TICKET'S TRACE WAS RIGHT and I verified it before fixing: 719FJ's dotted branch in
`build_body_atom_occurrence_inner` returns before the one-segment `Term::Ref` /
`Term::Ident` arms, so neither of CZJ2N's readings ran. The fix forwards to
`bare_entity_goal_occurrence` then `nullary_op_call_or_ref`, in the arms' own order.

THE OTHER FOUR LOGICAL POSITIONS DID NOT NEED IT, checked rather than assumed:
`convert_subject_term` (rule head, fact head, sort-body pre-scan, proof step) and
`convert_query_term` already call the expansion on THEIR dotted branches. Only the
rule-body goal had forked.

WHAT THE TICKET DID NOT PREDICT, all measured here:
 * A THIRD WRONG-ANSWER ROW. `not(fact-less entity)` answered 1 dotted and 0 for its own
   APPLIED dotted twin — the two dotted spellings disagreed with each other, not only with
   the unqualified column.
 * THE DATA-SLOT CONTROL THE TICKET ASKED FOR IS NOT THE ONE IT DESCRIBED. It asked that a
   dotted citation in a data slot keep the `field_access` chain; measured, a rule-body data
   slot resolves it to the NAME (`Fn{acct,[],[]}` for an entity, `Ref(f)` for a predicate,
   an operation or a namespace), because that walk falls back to `convert_term`, where
   052 §6.7 / WI-714 already read it as the name. Unmoved by this change — identical with
   it backed out. The control now asserts what carries content: no field arguments (the
   expansion did not leak), and the three walks still agree.
 * BACK-OUT 1 FELLS A ROW I HAD NOT PREDICTED. The entity reading's back-out fells the
   goal-connective test on `dOrEnt`, so that row MEASURES the entity reading inside a
   connective branch rather than merely controlling for it. Header corrected.

MEASUREMENTS: corpus census ZERO (instrumented at the branch, 234 `.anthill` files + 1 292
`anthill-todo` documents, positive control fired all three arms) — new code only. Two
back-outs, present-but-wrong, each over the whole 4 041-row binary: entity reading -> 2
rows, operation reading -> 3, separable. rustland 6 333 / 36 binaries, scaland 539 — green.

NO SCALAND MIRROR, MEASURED NOT ASSUMED: neither reading exists there for EITHER spelling
(operation bodies dropped at load, WI-1007; `entityFieldNames` has no reader), so both
columns already agree at 0. `DottedGoalReadingTest` pins both boundaries with a PREDICATE
control answering 1 in all four spellings, so the zeros are about the missing readings.

FIVE TICKETS FILED, none of them this one's, each with my own measurement:
 * WI-20260902-VZC2C — a nullary Bool op is dropped as a `|` / `&` branch in all four
   spellings (the loader routes the slot as a goal; the entity branch answers, so the gap
   is the operation's relational view).
 * WI-20260902-T8H1W — scaland has no partial-entity expansion at all.
 * WI-20260902-JB6RS — CZJ2N's Sort exemption is TermId-only; the heads are identical, so
   `holdsS(Shape())` now matches `fact holdsS(Shape)`. Its stale `map_arena.rs` invariant
   comment is corrected inline in this commit.
 * WI-20260902-TBZ4T — a dotted nullary op in a rule-body DATA slot binds the SYMBOL where
   the other three spellings compute (65BTX's dotted sibling; cannot be fixed as a term).
 * WI-20260902-4NEKZ — a dotted citation as an `=` operand is refused three times, once per
   segment of a name that resolves.
The last three came from `/code-review high` on this diff's range; I re-measured every one
of them, and each with this change backed out, before filing.

A CORRECTION TO MY OWN WORK, recorded because the fixture nearly shipped: a first reading
that "an op branch under `|` is dropped" was measured on a fixture whose helper predicate
was FALSE, so every branch correctly answered 0 and the table said nothing. A clean
fact-based fixture pinned the real boundary.

