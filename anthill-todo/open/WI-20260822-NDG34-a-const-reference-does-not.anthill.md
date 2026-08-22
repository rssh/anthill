## Attributes

- id: WI-20260822-NDG34-a-const-reference-does-not
- created: 2026-08-22T06:16:53Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T06:16:53Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `const` REFERENCE DOES NOT FOLD IN A RULE BODY — it folds in an operation body, and
the same reference one context over is silently inert. A rule that reads a named
constant loads clean and answers NOTHING, with no diagnostic anywhere.

MEASURED (rustland, current tree, after WI-20260822-J38JE):
  const nn: Int64 = 5
    operation big() -> Bool = Int64.gt(nn, 3) ;  rule p(1) :- big()   -> 1   FOLDS
    operation big() -> Bool = Int64.gt(5, 3)  ;  rule p(1) :- big()   -> 1   control
    rule p(1) :- Int64.gt(nn, 3)                                      -> 0   DOES NOT
    rule p(1) :- Int64.gt(5, 3)                                       -> 1   control
  const flag: Bool = true
    rule p(1) :- flag = true                                          -> 0
    rule p(1) :- flag            (goal position)                      -> 0

THE SPLIT IS EVAL vs SLD, not value-vs-goal: the third row's `nn` sits in a VALUE slot of
a builtin goal, exactly where the first row's `nn` sits inside the operation body, and
only the operation body folds it. So this is not the goal-position question
WI-20260822-J38JE answered — it is one level under it.

WHY IT IS FILED RATHER THAN INLINED. J38JE item 1 settled that goal position is CLOSED:
a term with no goal reading is a load error. A `const` reference in goal position is
exactly such a term, and the refusal was DELIBERATELY WITHHELD there because there is no
repair to point at — the obvious one, `:- flag = true`, is the row that answers 0 above.
Refusing the goal while the repair is equally broken would only move the author's dead
end. Fix the folding, then the refusal follows.

WHAT THIS TICKET MUST DECIDE:
 1. WHERE the fold belongs. A `const` is a MEMOIZED value (proposal 039 / WI-084 gates
    its body for purity precisely so one value can be shared), so the candidates are (a)
    fold at LOAD, rewriting a rule body's const references to their values — which makes
    a const in a rule body identical to the literal, and reuses the purity gate that
    already exists; or (b) fold at RESOLVE, giving a const reference a reading in
    `step_init` beside J38JE's boolean-constant arm. (a) keeps the resolver ignorant of
    consts and makes the discrimination tree index the VALUE, which is what a rule-body
    reference wants; (b) is lazier and survives a const whose body is not yet loaded.
    Say which, and say what a const referencing another const does under it.
 2. THE ARITY SPELLING. `flag` folds nowhere and `flag()` is a DIFFERENT error — measured,
    `rule p(1) :- flag() = true` is refused as "flag.apply: expected known operation or
    arrow-typed variable, got unknown functor", while the bare `flag` loads and is inert.
    One of the two spellings must be the reference and the other must say so.
 3. THE GOAL-POSITION REFUSAL that J38JE withheld. Once a Bool const folds, `:- flag`
    has a repair (`:- flag = true`) and can be refused under §5.3's closed reading — or
    given the search reading directly, if the fold makes it a boolean constant by the
    time `step_init` sees it. Decide which, and update §5.3's "not yet enforced"
    paragraph, which names this ticket's outcome as its precondition.

ACCEPTANCE: drive every row of the table above and assert the ANSWER COUNT, in both
polarities — a `const` in a rule-body value slot answers what the literal answers, and a
`false`-valued one answers what `false` answers. CONTROLS THAT MUST STAY GREEN: the
operation-body rows keep folding (they already work, and a load-time rewrite must not
double-fold them); proposal 039's const purity gate still refuses an effectful body; and
`what_the_closed_reading_still_does_not_reach` in `wi_j38je_boolean_goal_test.rs` is
written to FAIL when this lands — update it rather than deleting it, since its other two
rows pin J38JE's own reading. Say at each site which rows fail on a back-out.
cargo-test green via rustland/scripts/test.sh.

