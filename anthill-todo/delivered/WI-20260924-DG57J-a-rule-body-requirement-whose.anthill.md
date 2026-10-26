## Attributes

- id: WI-20260924-DG57J-a-rule-body-requirement-whose
- created: 2026-09-24T15:53:27Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-26T21:25:47Z

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

## Changes

### 2026-10-26T21:25:39Z — feedback — claude

DELIVERED (claude, 2026-10-26). RE-MEASURED on main at 18c03b73 before any edit: the ticket's program answers — guarded and bound give 3, ?d's impl is ByHeat; plain 3 and the carrier-own Hue row 7 as before. CLOSED BY WI-20260925-P7VP4 (18cca07a, 2026-09-25): the guard core simp_guard_decision asks carrier_provides_spec (the carrier's own provisions and one another sort files for it) where it asked sort_provides alone. MEASURED with the CLI built at 18cca07a^ (guarded, bound: no solutions) and at 18cca07a (3, impl ByHeat).

THE TWO-WITNESS HALF IS SUPERSEDED, not delivered as written: with ByName beside ByHeat and no selection, plain, guarded and bound are each REFUSED AT LOAD ("ambiguous dispatch … the call selects none"), per kernel-language §5.4 (WI-20260922-0DK3H: a rule-body goal no route discharges is refused at load) — not a conditional row. Never an empty answer set, which was the ticket's point.

FOUND AND FIXED INLINE: that refusal advised `[Score = ByHeat]` in the call's bracket list wherever the call stood, and two positions refuse a bracket — a rule's own term (goal or value slot: "call-site type arguments … are not supported here") and a dot call ("not supported on a dot call"), e.g. `red().score()` in an operation body. The refusal now carries the call's BracketChannel (dot: read off the synthesized call's source, a DotApply; rule_own_term: TypingEnv::in_rule_own_term, RuleText::Term/Fragment), and TieRepair::BracketElsewhere says where the bracket goes: on the call inside a `let` or in an operation's body the rule calls; for a dot, on the applicative spelling `Score.score[Score = …](…)`. Each advised program is run and answers. Under a compound expression (let, lambda) the call's own bracket is read, and the advice there is unchanged.

ROWS: wi_dg57j_witness_only_requirement_test (11). Back-outs measured in one build with temporary switches: the guard core asking sort_provides alone fails the three written-requirement rows (no answer) and every row with an applicative Score.score call in a rule (a second load refusal, "Colour provides no Score", the typer's check asking the same core); BracketChannel reading no rule's own term fails the three rule-term refusal rows; reading no dot fails the two dot rows; the own-spec carrier row passes under all three. Stale text updated: 060-implementation §7.3 (the probe row, its paragraph, S5) and the demo2 row's comment in wi_5g28a_rule_dictionary_test. NOT DONE, asked: kernel-language §5.4's sentence on which repair the tie message offers does not mention the call's position.

