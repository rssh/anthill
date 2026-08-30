## Attributes

- id: WI-20260830-DQD5W-a-spec-operation-s-relational
- created: 2026-08-30T14:29:01Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T14:29:01Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A SPEC OPERATION'S RELATIONAL VIEW DOES NOT DERIVE, SO `isEmpty(?xs)` IS A SILENT NO-SOLUTIONS GOAL WHERE `contains(?xs, ?x)` DECIDES.

MEASURED, one file, one `List`, four goals:

    entity Box(items: List[T = String])
    fact Box(items: ["a", "b"])
    fact Box(items: [])

    rule has_a(?b) :- Box(items: ?ls), contains(?ls, "a")        -> 1 solution
    rule len2(?b)  :- Box(items: ?ls), eq(length(?ls), 2)        -> 1 solution
    rule empty(?b) :- Box(items: ?ls), isEmpty(?ls)              -> NO SOLUTIONS
    rule full(?b)  :- Box(items: ?ls), nonEmpty(?ls)             -> NO SOLUTIONS

`contains` and `length` are `List`'s OWN operations, declared with bodies on the carrier. `isEmpty` and `nonEmpty` are `anthill.prelude.Iterable` SPEC operations with default bodies (`isEmpty(c) = Stream.isEmpty(iterator(c))`), reached by `List`'s provision. Both spellings import cleanly and neither is a name error -- the goal simply has no clauses to try and fails.

WHY THIS IS A DEFECT RATHER THAN A GAP IN A FEATURE NOBODY USES. WI-580 derives an operation's equational and relational views FROM ITS BODY on demand, and `list.anthill`'s own comment at `contains` states the contract: "its RELATIONAL view (a bare `contains(l, x)` goal) is derived from it on demand -- the resolver routes it to `eq(contains(l, x), true)`, so a ground call decides via the eval bridge and an unground one suspends to a WI-519 residual". Nothing in that statement is about WHERE the body lives. A reader who has read it will write `isEmpty(?xs)` in a rule body and get silence.

THE FAILURE MODE IS THE BAD ONE. A goal with no clauses is FALSE, not an error, so a constraint or rule built on it does not fail loudly -- it quietly decides the opposite way. Measured consequence, and the reason this was found: `constraint c: forall ?ls: Verdict(labels: ?ls) -: nonEmpty(?ls)` LOADS and then fires on EVERY verdict including well-formed ones, because the `-:` body can never hold. From the acceptance test's side that is indistinguishable from a constraint that works, and the honest repair (a structural test against `nil`) is only reachable once you know the goal is inert.

LIKELY SHAPE OF THE CAUSE, to be confirmed rather than assumed: the relational-view derivation keys on the operation's OWN clause/body on the carrier, and a spec operation reached through `provides` has its body on the SPEC. So the derivation finds nothing to route. If that is right, the fix is to resolve the goal through the same dispatch the eval bridge uses before concluding there are no clauses.

SCOPE. Make a bare goal at a spec operation the receiver's carrier provides decide the same way a goal at the carrier's own operation does. If that is out of reach, the fallback is a LOUD refusal -- a bare goal at an operation with no derivable relational view should be a load error naming the operation, not zero solutions. Either beats today; silence is the one outcome that must go.

ACCEPTANCE: `rule empty(?b) :- Box(items: ?ls), isEmpty(?ls)` yields the empty Box, and `nonEmpty` yields the other one. CONTROLS, each of which passes today and must keep passing: `contains` and `length` as rule-body goals (`wi939_contains_rename_test::list_contains_as_a_rule_body_goal` is the existing row); an unground call still suspends as a WI-519 residual rather than deciding.

FOUND FROM: examples/guardians -- see docs/design/measured.md C11, which records the inert-constraint consequence and is the reason `verdict_is_not_silent` is written structurally against `nil`. Closing this does NOT require rewriting that constraint: `nil` is the more direct spelling for a list either way.

