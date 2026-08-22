## Attributes

- id: WI-20260822-J38JE-a-boolean-expression-in-goal
- created: 2026-08-22T00:27:29Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T07:07:23Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BOOLEAN EXPRESSION IN GOAL POSITION MUST MEAN WHAT LOGIC SAYS — `:- true`, `:- false`
and any Bool-valued expression. Today `true` means one thing at the top of a body and
another one level down, `false` fails only by accident, and a non-Bool constant is
silently dead.

USER POSITION (2026-08-22): `x :- true`, `x :- false` and `x :- <any boolean expression>`
need special handling to match logic semantics.

MEASURED (rustland, current tree, after WI-20260821-FQC85):
  rule ptrue(1)    :- true                     -> 1 solution
  rule pfalse(1)   :- false                    -> 0, BY ACCIDENT (see below)
  rule pint(1)     :- 42                       -> LOADS CLEAN, 0 solutions, no diagnostic
  rule pstr(1)     :- "hello"                  -> LOADS CLEAN, 0 solutions, no diagnostic
  rule nottrue(1)  :- not(true)                -> 1   <-- logic says 0
  rule notfalse(1) :- not(false)               -> 1
  rule mixed(1)    :- base(7), true            -> 1
  rule ortrue(1)   :- base(9) | true           -> 0   <-- logic says 1 (base(9) fails)
  rule pop(1)      :- Box.isbig(box(n: 5))     -> 1   (a Bool OPERATION call: WORKS)
  rule pop2(1)     :- Box.issmall(box(n: 5))   -> 0   (and it is not vacuous)
  rule pand(?b)    :- Bool.and(?b, ?b)         -> REFUSED, located (§6.6 / WI-1046)

BY ACCIDENT is the load-bearing word. `false` does not FAIL, it never becomes a goal: a
boolean literal is a `Term::Const`, so it resolves to no clause and no builtin, and
WI-1034's "rule-body goal `x` names nothing" refusal cannot reach it because a CONSTANT
NAMES NO NAME. `42` and `"hello"` fall through the same hole and are equally silent —
which means a typo that lands a constant in goal position is indistinguishable from a
deliberate `false`, and a clause that can never fire loads with no word said.

PART OF THIS IS FQC85's DOING, and it should be read that way. 061 gave the TOP-LEVEL
`true` a meaning — the empty conjunction, which is what `fact` desugars to (§6.1) — and
left every other constant, and every nested position, alone. Before that change `:- true`
also answered 0: uniformly wrong rather than position-dependent. `not(true) -> 1` is the
row that shows the seam, and §6.6 already says where the seam should not be: the boolean
operators are redirected "at every GOAL position (the body's atoms, AND THE GOAL SLOTS OF
THE CONNECTIVES ABOVE THEM)". The constants must get their reading in the same places, or
`not(true)` stays wrong however `true` is spelled at the top.

WHAT THIS TICKET MUST DECIDE:
 1. THE READING. Is a Bool-valued expression in goal position a CONDITION — succeeds iff
    it evaluates to `true` — or is goal position closed to expressions, with only `true`
    and `false` given constant readings? §6.6 settles the OPERATORS the other way and
    says so as a design rule: in a rule body `not`/`or` are the resolver primitives, not
    the `Bool` value ops, and `and` has no goal reading at all, so `a & b` is REFUSED
    naming the comma. An evaluated-condition reading has to say how it does not reopen
    exactly what WI-1046 closed. The Bool-OPERATION rows above are the awkward evidence:
    `Box.isbig(box(n: 5))` already evaluates in goal position, through WI-938's derived
    relational view at the operation's own arity — so "a boolean expression as a goal" is
    half-delivered already, by a different mechanism, and the two readings meet here.
 2. WHERE THE MEANING IS ATTACHED. Today it is a strip over the body's TOP-LEVEL goal
    list (`is_empty_conjunction_goal`, kb/load.rs), which by construction cannot reach a
    goal nested under `not` or `|`. Attaching it where a GOAL is built instead is what
    makes `not(true)` and `base(9) | true` agree with the top level.
 3. `false` AND THE DEAD CLAUSE. Is `p(1) :- false` legal-and-dead, or refused? It is the
    honest way to disable a clause, and it is also exactly the never-fires shape this repo
    refuses elsewhere. Whichever way, it must stop being an accident.
 4. A NON-BOOL CONSTANT IN GOAL POSITION (`:- 42`, `:- "hello"`) must become a located
    error — the loud counterpart of WI-1034 for the population that names no name. This
    is the half of the ticket with no design question in it.
 5. WHAT `fact`'S DESUGARING BECOMES. §6.1 now reads `fact H` as `H :- true`, and the
    loader makes that the EMPTY body — which is what makes the two spellings the same
    clause (FQC85 drove it). If `true` becomes an evaluated condition, the desugaring must
    still produce an empty body: a clause carrying one always-succeeding goal is a
    different clause (a different `is_equation`, and it misses the WI-624 ground-fact
    fast path).

ACCEPTANCE: drive every row of the table above, in both polarities, and assert the
ANSWER COUNT — not that it loads. `not(true)` answers 0 and `not(false)` answers 1;
`base(9) | true` answers 1 and `base(9) | false` answers 0; a non-Bool constant goal is a
located load error naming its position. CONTROLS THAT MUST STAY GREEN: the Bool-operation
rows keep answering 1 and 0 (WI-938's derived view); WI-1046's `and`-in-a-goal refusal
still fires with its §6.6 message; and `fact H` and `rule H :- true` remain the SAME
clause with the same empty body (wi_fqc85_rule_declaration_test's own row). Say at each
site which rows fail on a back-out. cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-08-22T00:30:39Z — feedback — user

USER DECISION (2026-08-22): `x :- true` is a SUCCESSFUL search and `x :- false` an
UNSUCCESSFUL one. So `false` is legal-and-DEAD, not refused — decision 3 above is
settled in favour of the goal that always fails, and `true` is the goal that always
succeeds. Both readings hold at EVERY goal position, which is what §6.6 already says for
the operators: `not(true)` must answer 0 and `base(9) | true` must answer 1, where today
they answer 1 and 0.

Still open after this decision: item 1 (whether a general Bool-valued EXPRESSION in goal
position is an evaluated condition, given that §6.6 sends the operators the other way and
WI-938's derived view already evaluates a Bool operation call), item 4 (a NON-Bool
constant in goal position — `:- 42` — which this decision does not reach), and item 5
(`fact`'s desugaring must keep producing the EMPTY body, not a clause carrying one
always-succeeding goal).

### 2026-08-22T00:37:13Z — feedback — user

THE DECIDED HALF IS IMPLEMENTED (2026-08-22); THE TICKET STAYS OPEN for items 1 and 4,
which are its own remaining scope.

WHAT SHIPPED. A boolean constant in goal position is now a SEARCH, read in
`SearchStream::step_init` (kb/resolve.rs) rather than in the loader: `true` drops the
goal and continues, `false` pops the frame. Every row now matches logic, including the
two that did not:
    :- true            1 -> 1        :- not(true)         1 -> 0
    :- false           0 -> 0        :- not(false)        1 -> 1
    :- base(7), true   1 -> 1        :- base(9) | true    0 -> 1
    :- base(7), false  0 -> 0        :- base(7) | false   1 -> 1

IN THE RESOLVER, NOT THE LOADER, and that is the whole of why `not(true)` was wrong: 061's
`:- true` reading is a strip over the body's TOP-LEVEL goal list, which by construction
cannot reach a goal nested under `not` or `|`. §6.6 already states the placement for the
boolean OPERATORS — "at every GOAL position (the body's atoms, and the goal slots of the
connectives above them)" — and the constants now get their reading in the same places.

ITEM 5 IS SETTLED BY THE IMPLEMENTATION: BOTH readings stay. The loader strip is what
keeps a top-level `:- true` body EMPTY, and only an empty body makes `fact H` and
`rule H :- true` ONE clause (`is_equation` and WI-624's ground-fact fast path both read
body-emptiness). The resolver arm answers every `true` the strip cannot see. Measured:
with the strip backed out, all 44 rows of wi_j38je + wi_fqc85 + wi980 still pass EXCEPT
the one that asserts the body — because the arm answers the goal instead. That also means
061's own "empty conjunction" back-out, which felled 24 rows when it shipped, now fells
none; wi_fqc85's back-out list has been corrected rather than left to rot.

STILL THIS TICKET'S SCOPE, and neither is touched by "true succeeds, false fails":
 * ITEM 1 — is a general Bool-valued EXPRESSION in goal position an evaluated CONDITION?
   The tension is unchanged and now has a pinned witness: `Box.isbig(box(n: 5))` in a goal
   answers 1 and `Box.issmall(...)` answers 0 (WI-938's derived relational view), while
   §6.6 sends the OPERATORS the other way and `Bool.and` in a goal is refused outright.
   Two mechanisms meet at this position and only one of them is written down.
 * ITEM 4 — a NON-Bool constant goal (`:- 42`, `:- "hello"`) still loads clean and
   silently never matches. Pinned in `what_this_decision_does_not_reach`, which is written
   to FAIL when the located error lands.

TESTS: `wi_j38je_boolean_goal_test.rs`, 5 rows, every one driving the goal. Both stated
back-outs RUN over 44 rows: the goal reading fells exactly 1 row
(`the_reading_holds_at_every_goal_position`) and the loader strip exactly 1
(`a_top_level_true_is_still_erased_at_load`). My first draft predicted 2 for the goal
reading and was wrong — `false` answers 0 under both readings, so no count of its own can
separate them; `not(true)` is what does.

kernel-language.md §5.3 states the rule beside 061's, with item 4 named as open.

### 2026-08-22T07:07:15Z — feedback — claude

ITEMS 1 AND 4 ARE DELIVERED (2026-08-22); THE TICKET'S SCOPE IS CLOSED.

ITEM 1 — THE READING: GOAL POSITION IS CLOSED. A term written where the resolver
expects a goal is read by one of an ENUMERATED set of readings, and a term that fits
none of them is a LOAD ERROR — never a silently-dead clause. Now a table in §5.3: a name
carrying clauses (resolution); a resolver builtin or scoping marker (its own goal
semantics); `not` / `or` (the primitives, `and` refused naming the comma); a
Bool-returning OPERATION at its declared arity (an evaluated CONDITION,
`eq(op(…), true)`); the same operation at arity+1 (the functional-relation view);
`true` / `false` (a search); a variable (higher-order — read once bound, by whichever
row its binding matches).

THE TENSION THE TICKET NAMED IS NOT ONE, and MEASURING is what settled that rather than
argument. §6.6's redirection is a NAME-level rule that fires at a goal position UPSTREAM
of any classification, so it does not contradict the condition reading — the two already
coexist in the shipped tree:
    Box.isbig(box(n: 5))    -> 1        a Bool op call IS a condition (WI-583/WI-938)
    Box.issmall(box(n: 5))  -> 0        …and not vacuous
    Bool.and(true, true)    -> REFUSED, located (§6.6 / WI-1046)
    Box.size(box(n: 5))     -> REFUSED, located (§5.3: a non-Bool op has no reading)
A user's own `myand(?a, ?b) -> Bool` in a goal is a condition while `Bool.and` is
refused: that is ONE rule applied in order, not two rules in tension. §5.3 had already
legislated the operation half ("A Bool-returning operation may be used directly as a
rule-body goal … a non-Bool operation … is a load error"), so the decision item 1
actually needed was whether to GENERALIZE evaluation to ANY Bool-valued expression. The
answer is NO: the admissions stay enumerated. Generalizing would make WI-1046's refusal
indefensible (under it `Bool.and(a, b)` IS a Bool expression and would have to evaluate),
and it would owe an account of how an arbitrary expression SUSPENDS — a question §5.3
can answer for an operation call only because there is an arity to key the residual on.

THE READING IS NOT DERIVED FROM A TYPE, and one measurement forces that. A
`field_access` in goal position already HAS a goal reading of its own — it asks whether
the PROJECTION succeeds, not whether the field is `true`. Measured: `:- b.flag` answers
1 for `flag: true` AND for `flag: false`, and `:- b.n` on an `Int64` field answers 1 too
(`builtin_field_access` returns `Success` at arity 2 whenever the projection lands). A
type-directed reading would have to OVERRULE a builtin's own goal semantics; the closed
reading does not, and the condition is spelled `b.flag = true` — measured 1 and 0.

ITEM 4 — A NON-BOOLEAN CONSTANT IN GOAL POSITION IS A LOCATED LOAD ERROR, which is that
rule's corollary rather than a policy of its own. It lands in the typer's WI-583 pass,
renamed `check_rule_body_goal_readings` / `check_goal_atom_reading` because the question
it now answers is one question with two shapes: IS THIS TERM READABLE AS A GOAL AT ALL?
The `Expr::Const` arm was the hole — every goal-position gate keys on a FUNCTOR (this
pass's op record, WI-1034's `undefined_functor`), and a constant has none, so a literal
fell through all of them. That arm's own comment claimed a literal never arrived there;
it did, as `Expr::Const`, which is what let `:- 42` through.

    :- 42        loads, 0, NO DIAGNOSTIC   ->  3:16: constant `42` in a rule-body GOAL …
    :- "hello"   loads, 0, no diagnostic   ->  refused, quoting `"hello"` AS WRITTEN
    :- 1.5       loads, 0, no diagnostic   ->  refused
    :- not(42)   loads, answers ONE        ->  refused   <- the loudest row
    :- base(9) | 42                        ->  refused
    :- base(7), 42                         ->  refused

THE DESCENT IS THE PASS'S OWN AND IS WIDER than `undefined_rule_body_goals`' (WI-863 /
WI-1034 tolerate a name that means nothing in a bare `or` branch). Not a drift: the two
answer different questions. A NAME in a failing branch may mean something in another
program, and refusing it would reject a program that computes the right answer
(`push_choice_test` names undefined branches on purpose). A constant has no such
defence — `42` is not a goal in any program, in any branch, under any binding. Stated at
`check_goal_atom_reading`.

AND THE DESCENT ITSELF WAS WRONG BY OMISSION — found by /code-review, not by me, and it
was THIS TICKET'S OWN DEFECT one connective further out. The pass descended through a
hand-written allowlist of three symbols (`reflect.not`, `kernel.or`,
`kernel.push_choice`), so a BOUNDED QUANTIFIER's body and a DISCHARGE's consequent —
goal positions the resolver runs — were never entered, while `step_init`'s boolean arm
answered `true` / `false` inside them perfectly well. Measured before the repair:
    (forall ?x in [1]: 42)      loads clean, answers 0, NO DIAGNOSTIC
    (forall ?x in [1]: true)    -> 1        (forall ?x in [1]: false)  -> 0
That is "one spelling, two readings, decided by DEPTH" — the exact shape this ticket was
opened to remove, and my own spec text ("at every goal position") already contradicted
it. The allowlist is retired: the descent now reads the ONE slot table WI-1058 built for
this (`goal_slot_readings`, filtered to `SlotReading::Proved`), which typing.rs'
`child_body_positions` already read — so this was the LAST hand-written copy of "which
arguments are goals", and its hole is what a hand-written copy is for. Corpus impact of
the widening: ZERO, over the full workspace.

WHAT THE WIDENING DELIBERATELY DOES NOT REACH: a discharge's ANTECEDENT slot
(`SlotReading::Assumed`). A hypothesis DECLARES the predicate its consequent proves
against, so the slot binds rather than proves, and every walk that refuses a dead goal
has left it alone with that reason recorded. Widening it would have moved WI-583's op
check into a position nobody has legislated. Pinned and measured
(`(forall(?x), 42 -: base(?x))` loads, and the live discharge beside it answers 1), and
§5.3 now says which positions "a goal the resolver expects" means.

TWO SMALLER THINGS CAME WITH IT. (a) The pass's errors are now TAGGED with the
`SourceId` of the occurrence they were raised on, so they render `path:line:col`; the
late whole-KB passes around them push untagged errors, and without the tag this one
reported `at 98..100`, a byte offset naming no file — which for a constant is the WHOLE
diagnostic, since a constant names nothing to cite a rule by. WI-583's existing
`NonBoolOpInGoalPosition` is located by the same change. (b) `write_literal` is hoisted
out of `TermPrinter` (which now delegates) so the diagnostic quotes the constant in
`.anthill` SURFACE spelling — `"hello"` with its quotes, `1.5` with its point — from the
one renderer rather than a second copy.

WHAT IS DELIBERATELY NOT REFUSED, and why it is not a hedge: a `const` REFERENCE in goal
position (`:- flag`) still loads and silently never matches. Refusing it would strand the
author, because THERE IS NO REPAIR TO POINT AT — a `const` does not fold ANYWHERE in a
rule body. Measured, with `const nn: Int64 = 5`:
    :- Int64.gt(nn, 3)  -> 0        :- Int64.gt(5, 3)  -> 1   (the control)
    :- flag = true      -> 0        with `const flag: Bool = true`
So const FOLDING in rule bodies is the defect to fix first, and the goal-position
refusal follows it rather than leading. Both rows are pinned in
`what_the_closed_reading_still_does_not_reach`, which is written to FAIL when either
lands. Filed as WI-20260822-NDG34 — a resolver/loader change with its own design question
(fold at load or at resolve), not an inline one, and it names §5.3's "not yet enforced"
paragraph as the thing it retires.

MEASUREMENT. Corpus impact of the refusal AND of the widened descent: ZERO. The whole
workspace (35 test binaries) runs green, and the ONE row that moved on the way in was
`what_this_decision_does_not_reach` — the row the previous pass wrote to fail when item
4 landed. FIVE back-outs, each RUN over the full 3283-row `wi_tests` binary, not
predicted:
    the constant refusal   -> exactly 3 fail   (the three refusal rows)
    the descent widening   -> exactly 1 fails  (the position row's last two sub-rows)
    the localization tag   -> exactly 1 fails  (the position row; the message survives)
    the goal reading       -> exactly 2 fail   (was 1; the second is this pass's control)
    the loader strip       -> exactly 1 fails  (unchanged — `wi_fqc85`'s claim still holds)
The refusal and the descent are TWO AXES of one fix and get two back-outs: with the
descent narrowed the constant arm still fires everywhere it used to, so one back-out
would have measured only half. The goal-reading count MOVED because the file grew, not
because the reading did, and the new row says so at its own site: it is a control for
item 4 and a driver for the reading, and it passes under the descent back-out precisely
because the RESOLVER answers a boolean constant inside a quantifier whatever the loader
checks — which is how the two readings came apart in the first place.

TESTS: `wi_j38je_boolean_goal_test.rs`, 10 rows, every one driving a goal or a load.
Two controls are their own namespaces and their own loads — a control sharing a fixture
with a refusal arm dies of the arm's load error and proves nothing, and each refusal arm
is its own load for the same reason. One trap on the way: a fixture predicate named
`neg` collides with `Numeric.neg` and answers NOTHING, which faked a failure that had
nothing to do with the change; the rows are `p`-prefixed now and say why.

kernel-language.md §5.3 carries the closed-reading table and item 4's rule.

ONE MORE THING THE REVIEW FOUND, off this ticket's path and filed rather than fixed:
061's `is_typed_column` is a bare name test, so a body-less `rule p(typed_var(1))` — a
user functor that happens to be named `typed_var` — is FALSELY REFUSED citing a typed
column the source does not contain. The repair is at the converter (`mark_minted` the
`typed_var_arg` node, then pair the name with `is_minted`), but `is_minted` has ten
readers asking different questions, so it is a censused change: WI-20260822-AK2AJ, with
the census carried in it, and a note at the site.

### 2026-08-22T07:45:48Z — feedback — claude

USER DECISION (2026-08-22), REVERSING ITEM 1 AS DELIVERED: "of course any bool expression. How can be other?"

A Bool-VALUED expression in goal position IS an evaluated CONDITION — it succeeds iff it
evaluates to `true`. That is the ticket's own opening position ("x :- <any boolean
expression>"), and the closed/enumerated reading I shipped narrowed it without being
asked to. The reading is TYPE-DIRECTED, not a list of admitted shapes.

WHAT THAT MAKES OF §6.6, since the delivered feedback claimed the two were in tension and
they are not: `not` and `or` at a goal position resolve to the RESOLVER PRIMITIVES
before anything is typed, so they never become Bool expressions there at all — §6.6 is
untouched. WI-1046's `and` refusal is the part that has to move: it refuses `a & b` in a
goal unconditionally, but its measurement was `l(?x) & r(?x)`, where the operands are
GOALS and so not Bool values. Where the operands ARE Bool values (`Bool.and(?b, ?b)` with
`?b: Bool` — the ticket's own `pand` row) the expression is a condition and must answer.

STILL TO DO under the corrected decision — the population measured while delivering the
narrow one, all of which now needs the condition reading:
  * a Bool FIELD ACCESS. `:- b.flag` answers 1 for `flag: true` AND for `flag: false`
    (and `:- b.n` on an Int64 field answers 1 too) — `builtin_field_access` at arity 2
    reports that the PROJECTION succeeded. Under the decision a Bool-typed one must
    instead mean `eq(b.flag, true)`, which is measured to answer 1 and 0 correctly.
  * a Bool CONST reference. `:- flag` answers 0 — and so does `:- flag = true`, because a
    const folds in an operation body and nowhere in a rule body (WI-20260822-NDG34). The
    condition reading needs that folding underneath it.
  * `Bool.and` / `&` at Bool operands, per above.
  * the two shapes already delivered stay as they are, because both are instances of the
    corrected rule rather than exceptions to it: `true`/`false` (a constant evaluates to
    itself) and a Bool OPERATION call at declared arity (WI-583's `eq(op(…), true)`).

Item 4 is UNAFFECTED: a NON-Bool constant in goal position has no truth to denote, so it
stays a located load error, as does a non-Bool operation (§5.3, WI-583).

### 2026-08-22T08:06:50Z — feedback — claude

IMPLEMENTED UNDER THE CORRECTED DECISION (2026-08-22).

"WHAT IS THE PROBLEM TO HAVE ANY BOOL EXPRESSION IN RHS?" — THERE IS NONE, and the
delivered feedback's claim that there was is withdrawn. I took §6.6's refusal of `a & b`
as evidence that goal position had to be closed to expressions. It is not evidence of
that: §6.6 redirects three NAMES (`not` / `or` / `and`) to the resolver primitives before
anything is typed, so those names never reach the question. I generalized a rule about
NAMES into a rule about TERMS and then defended the result. §5.3 now states the reading
type-directed: a Bool-valued expression in goal position is a CONDITION — it evaluates,
and the goal succeeds iff the value is `true`.

WHAT THAT CHANGED IN THE CODE. A bare dot projection is a Bool expression and now reads
as one. `b.flag` lowers to `field_access(b, flag)` at arity 2, whose BUILTIN goal reading
was "the projection landed":
    :- box(n: 1, flag: true).flag     1 -> 1
    :- box(n: 1, flag: false).flag    1 -> 0     <-- a WRONG answer, not a missing one
    :- not(box(n: 1, flag: false).flag)   0 -> 1
    :- box(n: 5).n   (an Int64 field)     1 -> 0
It is routed in `step_init` to `eq(field_access(…), true)` — the SAME rewrite WI-580
applies to a Bool operation's bare goal, one shape further out, so the declared `Eq`
decides it and an under-determined receiver suspends to a WI-519 residual instead of a
verdict being invented. Reusing that route is the whole point of the corrected decision:
"is this expression true" gets ONE answer however the expression is spelled. Corpus
impact: ZERO.

WHAT IS BLOCKED, AND ON WHAT — this is the real finding, and it is not a design question.
Two Bool expressions still do not condition, for ONE reason: A RULE BODY REDUCES A BODIED
OPERATION AND A RESOLVER BUILTIN, AND NOTHING ELSE.
    operation f() -> Bool = Bool.and(true, true)  ; :- f()          -> 1   REDUCES
    operation f() -> Bool = Bool.and(true, false) ; :- f()          -> 0
    :- Bool.and(true, true) = true                                  -> 0   DOES NOT
    :- Int64.gt(2, 1) = true                       (control)        -> 1
    :- Int64.gt(2, 1)                              (control)        -> 1
`Int64.gt` answers because it is a resolver BUILTIN; `Box.isbig` answers because it has a
BODY. `Bool.and` / `or` / `not` are declared body-less in `prelude/bool.anthill` ("backed
by a host builtin") and their Boolean-algebra `<=>` laws are UNTAGGED, so by WI-881/884/888
they are inert and cannot stand in for the reduction either. A `const` reference is the
same shape: folds in an operation body, folds nowhere in a rule body. Filed as
WI-20260822-ZJZS7 (host-backed ops) beside WI-20260822-NDG34 (consts); they may share a
fix, since both are "the eval bridge is reachable from an operation body and not from a
rule body" for a construct carrying no anthill body.

SO `a & b` IN A GOAL STAYS REFUSED, and the MESSAGE is what changed rather than the
verdict. It used to assert that `&` "has no meaning in a rule-body GOAL position", which
is now false as design. It now separates the two things that were conflated: operands
that are GOALS (WI-1046's own measured case, `l(?x) & r(?x)`) are not Bool values and the
comma is the repair; operands that ARE Bool values are a condition by §5.3, which the
evaluator cannot yet deliver — named, with ZJZS7. Admitting it instead would make it
answer 0 silently, which is strictly worse than a located error.

ITEM 4 IS UNAFFECTED and stays as delivered — a non-Bool constant denotes no truth, so it
is a located load error. One NEW residue of the same kind is pinned rather than fixed: a
non-Bool DOT projection (`:- b.n`) now answers 0 instead of 1, because `eq(5, true)` is
false. Correct as logic, but SILENT where its two siblings are loud; the refusal wants the
field's declared type, which the typer already stamps on that goal node.

MEASURED: 35 binaries green, corpus impact zero. The new back-out (neutralize the
`BuiltinTag::FieldAccess` arm) RUN over the full wi_tests binary fells exactly 2 rows —
`a_bool_expression_in_goal_position_is_a_condition` on the `false` field, and
`what_the_condition_reading_cannot_yet_reduce` on the non-Bool dot row going 0 -> 1. One
arm decides both, so a back-out that fell only the Bool row would have left half of it
unmeasured. Tests: `wi_j38je_boolean_goal_test.rs`, 11 rows.

### 2026-08-22T08:53:28Z — feedback — claude

HOST-BACKED OPS ARE CALLABLE FROM RULES, AND `and` HAS A GOAL READING (2026-08-22).
Both from user direction, and both were things I had written up as design when they were
missing mechanism.

1. "OPERATIONS IMPLEMENTED IN THE HOST LANGUAGE ARE NOT CALLED FROM RULES?" — they were
not, and there was no reason. The gate `bare_bodied_bool_relation` read
`op_body_node(f).is_some()` — "has a runnable ANTHILL body" — so a body-less host-backed
op was inert in a rule body while working in an operation body. It now reads
`op_reducible_in_rule_body`: a body OR `is_interpreter_mapped_op`, the same question
`op_is_interpretable` already asks the typer's side and `reduce_op_value` asks before
building a scratch interpreter. ONE LINE, measured:
    :- Bool.not(false)   nothing -> 1        :- Bool.not(true)   nothing -> 0
    :- Bool.or(false, true)  nothing -> 1
`Int64.gt` looked like a counterexample to the diagnosis and is not: it is a resolver
BUILTIN (it carries a `BuiltinTag`), a third supplier — `String.concat` is host-backed
like `Bool.and` and was equally inert. The effect-free and rule-less clauses of both
callers are untouched.

WHAT DID NOT MOVE, measured, so ZJZS7 keeps two NEGATIVES rather than a hypothesis: the
arity+1 functional-relation view on a host op (`String.concat("a","b",?r)`) still answers
nothing, and widening `functional_relation_arity` the same way changes NOTHING — nor does
opening `reduce_op_value`'s body-less arm beside it. Whatever blocks that is further in
and is neither of those two gates. Both experiments were run and reverted; the
`functional_relation_arity` gate carries the negative at its site.

2. `push_and` AND A GOAL READING FOR `and`. §6.6 refused `a & b` in a goal because "there
is no `kernel.and`" — a MISSING PRIMITIVE stated as a rule about the language, since
`not` and `or` each had one to be redirected to. Added `operation push_and(a, b)` beside
`push_choice` in `anthill.kernel` (a `BuiltinTag`, special-cased in `step_init`: splice
both goals into the same frame, no choice point — a conjunction has no branch to
backtrack into), plus `rule and(?a, ?b) :- push_and(?a, ?b)` and an `and` row in
`POSITION_DIRECTED_BOOLEANS`. WI-1046's refusal is deleted. Measured, on WI-1046's own
program:
    l(?x) & r(?x)     0 -> 1      and the COMMA control answers 1
    l(?x) & absent(?x)           REFUSED, as `l(?x), absent(?x)` already was
    true & true  -> 1            true & false -> 0        Bool.and(true, false) -> 0
    not(true & false) -> 1       (false & true) | true -> 1     l(?x) & r(?x) & true -> 1
    operation f() -> Bool = true & false ; :- f()  -> 0   (the op-body direction intact)
The conjunction reading SUBSUMES the value one wherever both apply — a Bool expression in
goal position is a condition, so "?a succeeds" is "?a is true" — and it resolves the
UNGROUND case, which no value reading can. That is why `and` needed no host call.

A CONJUNCT IS AS COMMITTED AS A COMMA-SEPARATED GOAL, and that did not come for free.
`GoalCommit::child` relaxed every non-`not` connective to `Tolerated`, so the first cut
left `l(?x) & absent(?x)` LOADING while `l(?x), absent(?x)` was refused — `&` would have
been a quieter comma. A conjunction now passes its commitment through
(`is_goal_conjunction`, read by both walks), which is the same rule and not a fourth: a
bare `or` branch is tolerated because it may never need to answer, and a conjunct always
does.

WHAT THIS COSTS, stated rather than buried: THE PRECEDENCE TRAP IS QUIET AGAIN. `&` binds
looser than `=`, so `?r = ?a & ?b` parses as `and(eq(?r, ?a), ?b)` — the `&` is the goal
conjunction and `?b` is a CONJUNCT. That misreading was a LOAD ERROR while `and` was
refused; it is now a legal program that computes something else. It is not refusable by
shape — `and(eq(…), g)` is an ordinary conjunction to write once `and` has a goal reading
(`(?x = 1) & p(?x)`) — so it is PINNED in
`the_equals_versus_ampersand_precedence_trap_is_a_silent_zero` with both polarities, and
§6.6 keeps the precedence warning in prose.

A MEASUREMENT DEFECT OF MY OWN, caught by the user's question "= is Eq here?". IT IS: `=`
is `PartialEq.eq`, a semantic equality TEST that NEVER BINDS (§8.3). So every fixture of
the form `?r = <expr>` with `?r` free SUSPENDS, and the helper counting `.len()` reported
the residual as an answer. Measured: `?r = (?a & ?b)` is `total = 1, definite = 0`, and
my first draft of the precedence row asserted that 1 as a success. Two repairs, both
driven: the J38JE helper now counts DEFINITE solutions only — which immediately turned
`a_constant_in_a_value_position_is_untouched`'s `?x = 42` row RED, a control that had
been blessing a suspension, now rewritten with a ground operand and both polarities
(`?n = 42` answers 1, `?n = 43` answers 0) — and the precedence row drives the PARSE
through ground operands instead of a binding.

MEASURED: 35 binaries, 5476 tests green; corpus impact zero for both changes.

