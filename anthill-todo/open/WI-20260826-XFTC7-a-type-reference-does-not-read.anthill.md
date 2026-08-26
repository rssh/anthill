## Attributes

- id: WI-20260826-XFTC7-a-type-reference-does-not-read
- created: 2026-08-26T05:45:40Z

- status: Open
- status_agent: user
- status_at: 2026-08-26T05:45:40Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a TYPE reference does not read the dotted ladder: `Mid.Inner` reached through a `provides` conversion is 'type Mid has no member Inner', while the term and citation positions resolve it — the same spelling with two answers, one reader over from WI-752's

## Changes

### 2026-08-26T05:46:10Z — feedback — user

MEASURED, WITH ITS CONTROL, while delivering WI-20260825-X9RRN — and found by a UNIFORMITY row rather than by reading the code. Adding the provision rung to `resolve_dotted_in_kb`, the natural next step was to extend `wi752_dotted_ladder_test`'s "same spelling, every position" claim to it. Two of the three positions passed and the type one did not:

  sort Base { sort T = ?  sort Inner { entity inner(v: Int64) }  operation f() -> Int64 = 41 }
  sort Mid  { sort T = ?  provides Base[T = T] }

  TERM      `Mid.f()`             -> LOADS and answers 41
  CITATION  `Mid.rel.isEmpty`     -> LOADS and binds the relation (extent {7})
  TYPE      `x: Mid.Inner`        -> "type mismatch in Mid.Inner (entity-field): expected a
                                      well-formed type projection, got type 'probe.tp.Mid'
                                      has no member 'Inner'"
  TYPE      `x: Base.Inner`       -> LOADS                          <- THE CONTROL

So the difference is the CONVERSION and not the spelling, and it is not a hole in the rung: a `Sort.Member` in type position never reaches the dotted ladder at all. It is read as a TYPE PROJECTION by a separate check with its own member table, which is why the message is about projection well-formedness rather than about a name.

WHY X9RRN DID NOT ABSORB IT — a different QUESTION, not the same one at a second site. The ladder answers "what does this dotted NAME denote"; a projection asks "does this TYPE have this member". A spec's `provides` is documented throughout as a VALUE-level conversion — "hold a `Mid[T]` and you can obtain a `Base[T]`", `eq.anthill`, 058 §3.4 — and a dictionary is not a claim that a nested SORT is reachable through it. Answering yes is a type-level inheritance claim the language has not made anywhere else.

WHAT TO DECIDE, and it is the whole ticket: whether a conversion conveys a nested sort. If YES, the type-projection reader gains the same provision hop and the two readers agree; if NO, the asymmetry is a RULE and belongs in kernel-language.md §8.6 beside the rung, because "the term position resolves it and the type position does not" is exactly the position-dependence WI-752 exists to abolish and must not be left as an accident.

THE HAZARD IF IT IS WIDENED, stated so it is not rediscovered: the type-member table is where WI-751's field over-hit lived (`data.user.name` capturing a FIELD through head-qualification), and `resolve_dotted_in_kb`'s `not_a_field` gate is the repair. A second reader gaining a member hop needs its own version of that gate, measured, not inherited by analogy.

NOT SILENT, which is why this is a ticket and not a bug: the refusal names the head and the missing member. The cost is that one spelling has two answers.

PINNED: `wi_x9rrn_provided_member_address_test::the_type_position_reads_a_different_table` asserts BOTH halves — the `Base.Inner` control loads, the `Mid.Inner` refusal fires — so whichever way this is settled, the row fails and has to be updated deliberately. `wi752_dotted_ladder_test::wi752_provided_member_resolves_in_every_position` carries the same finding at its doc, and covers the two ladder positions only.

