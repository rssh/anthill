## Attributes

- id: WI-20260924-DG57J-a-rule-body-requirement-whose
- created: 2026-09-24T15:53:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T15:53:27Z

- acceptance: cargo-test, scaland-sbt-test

- tags: resolver

## Description

A RULE-BODY REQUIREMENT WHOSE ONLY PROVIDER IS A WITNESS SORT IS NOT FOUND, SILENTLY — requires(Score[T]) and ?d = require[Score[T]] both make the clause answer nothing, while the same call without the requirement answers.

MEASURED 2026-09-24 on HEAD, with sort ByHeat { provides Score[T = Colour]; operation score(x: Colour) -> Int64 = 3 } and Colour providing nothing itself:
  rule plain(?r) :- Score.score(red(), ?r)                          3
  rule guarded(?r) :- requires(Score[T]), Score.score(red(), ?r)    no solutions
  rule bound(?r) :- ?d = require[Score[T]], Score.score(red(), ?r)  no solutions
Control, with the CARRIER providing its own spec (sort Hue { entity teal; provides Score[T = Hue]; score = 7 }): ?d = require[Score[T]], Score.score(teal(), ?r) answers 7, and ?d's impl is Hue. So the rule-body requirement resolution — WI-300's check-only guard and WI-1040's read alike, both find_dictionary — misses a provision filed under a WITNESS, where operation dispatch (plain) finds it. There is no warning and no residual: the guard's failure reads as a refutation.

WANTED: the rule-body resolution finds a witness provision as operation dispatch does (one provider: its dictionary, impl ByHeat). Where it genuinely cannot decide — two rival witnesses and nothing selecting one — the goal RESIDUALIZES, per kernel-language.md's 'a rule body reaching the operation through the resolver delays on the tie instead'. Never an empty answer set.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): guarded and bound answer 3, and ?d's impl is ByHeat; with a second witness ByName beside it and no selection, both answer one CONDITIONAL row, not none. Controls, passing either way by design: plain, and the carrier-own Hue row.

FOUND BY WI-20260911-5G28A's demo2 (060-implementation §7.3, S5), whose top reads require[Score[T]] over two witnesses (wi_5g28a_rule_dictionary_test.rs, demo2_the_count_answers_zero).

