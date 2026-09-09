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

## Changes

### 2026-09-09T04:11:53Z — feedback — user

TWO MEASUREMENTS FROM WI-879, one that WIDENS the table and one that INVALIDATES a row of it. (1) A HOST-SUPPLIED CONST BEHAVES IDENTICALLY, so it is this ticket's and not a neighbour's. `const_map` (WI-889, 2026-07-31 — it predates this ticket) gives `Float.infinity` / `nan` / `pi` a value source that is a host function rather than an anthill body, and the split is exactly the same one measured here. Side by side, one program, today: `operation hbody() -> Bool = PartialOrd.gt(infinity, 1.0)` reached from a rule answers `true`, and `rule host_const(?r) :- Float.gt(infinity, 1.0, ?r)` answers a RESIDUAL — beside `const nn: Int64 = 5` whose `operation obody() -> Bool = Int64.gt(nn, 3)` answers `true` and whose `rule user_const(?r) :- Int64.gt(nn, 3, ?r)` answers a residual, with both literal controls answering `true`. Same eval-vs-SLD split, same direction, no difference between a host-backed const and a bodied one. IT DOES CHANGE DECISION 1, THOUGH, and the ticket's two options are not equally available for it: option (a) FOLD AT LOAD has to obtain the value at load time, and a host const's value comes from the runtime's own function at first demand (`force_const`, eval-side), so folding it at load means INVOKING a host function during the load — which the purity gate the option leans on (proposal 039 / WI-084) does not cover, because there is no anthill body to gate. Option (b) FOLD AT RESOLVE has no such problem. Whichever is chosen, say what it does for a const whose value source is the host's, and say it for the `language cpp` case too, where this runtime cannot call it at all. (2) ROW 3 OF THE TABLE HAS AGED — re-measured in the ticket's OWN spelling (2-ary goals, `p(1)`-shaped heads) today: `rule r1(1) :- big()` = 1 (unchanged, "1 FOLDS"); `rule r3(1) :- Int64.gt(nn, 3)` = **ONE NON-DEFINITE ROW**, where this ticket recorded **0** ("DOES NOT"); `rule r4(1) :- Int64.gt(5, 3)` = 1 (unchanged, control); `rule r5(1) :- flag = true` = 0 (unchanged). WI-879 is why: `builtin_cmp` used to return `BuiltinResult::Failure` for any operand pair it could not compare, and now returns an UNDECIDED delay with `truncated: true` — an unfolded const reference rides as a `Value::Node` that is not a literal, so it lands in exactly that arm. THE DEFECT IS UNCHANGED (the const still does not fold, and the rule still does not answer what the literal answers); what changed is the SHAPE of not answering, from a silent refutation to a withheld verdict. This ticket's acceptance says "drive every row of the table above and assert the ANSWER COUNT", so measuring row 3 against 0 would now be measuring a stale baseline — assert one non-definite row, and note that the count goes to 1 DEFINITE when the fold lands. NOTE ALSO THAT THE TABLE NOW HOLDS TWO FAILURE SHAPES: rows 3/4 go through `builtin_cmp` (WI-879's arm, residual) while row 5's `flag = true` goes through `PartialEq.eq` / `BuiltinTag::SemEq`, which WI-879 did not touch and which still answers 0. The acceptance should say which row expects which, or a single "answers nothing" assertion will pass for two different reasons.

