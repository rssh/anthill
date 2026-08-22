## Attributes

- id: WI-20260822-T70A2-a-sort-s-type-parameter-cannot
- created: 2026-08-22T14:33:36Z

- status: Open
- status_agent: claude
- status_at: 2026-08-22T17:14:36Z

- acceptance: cargo-test

## Description

A SORT'S TYPE PARAMETER CANNOT BE RESTRICTED TO A SET OF ADMISSIBLE TYPES, so every `S[T]` accepts every `T` and a parameter's declared name is documentation rather than a constraint.

MEASURED. Given

  enum Text
    sort Trust = ?
    entity text(raw: String)
  end

this loads clean:

  operation nonsense(t: Text[Int64]) -> Unit

`Int64` is not a trust level and never could be, but `sort Trust = ?` is unconstrained and admits it. The slot's NAME carries the intent and nothing enforces it.

A `requires` CLAUSE DOES NOT HELP, also measured. Declaring a marker spec and requiring it on the sort --

  sort IsLevel      sort T = ? end
  fact IsLevel[T = Untrusted]
  fact IsLevel[T = Public]

  enum Text
    sort Trust = ?
    requires IsLevel[T = Trust]
    entity text(raw: String)
  end

-- still admits `Text[Int64]`. So the obvious spelling for "this parameter ranges over these types" does not bind.

WHY IT MATTERS, AND WHY IT IS NOT A SECURITY HOLE. examples/guardians puts an information-flow label in a type parameter: `Text[Public]` and `Text[Untrusted]` are different types, and `send_email(body: Text[Public])` is what refuses the article's exfiltration. That works, because a sink demands a LITERAL label and `Text[Int64]` cannot reach it. What does NOT work is the claim one level up -- that the parameter ranges over a LATTICE. It ranges over everything. The lattice is a convention held up by the particular pairings the author happened to write, and a typo (`Text[Publik]`, a sort that exists for another reason) is a fresh type rather than an error.

RELATED, AND NOT THE SAME THING: variance IS declarable (`fact Covariant(sort, param)`, stdlib/anthill/reflect/typing.anthill) and `type_compatible` has a `provides` arm, so ORDERING between labels is expressible today -- a provides-chain of level sorts plus a covariant parameter gives widening in one direction and refuses the other (measured). Ordering the admissible values and CONSTRAINING WHICH VALUES ARE ADMISSIBLE are different questions; this ticket is the second.

WHAT DEPENDS ON IT. examples/guardians/lib/vocabulary.anthill declares `sort Trust = ?` on `Text` and on `Message`, and `lib/llm.anthill` on `Prompt`. The parameter itself is not a workaround -- it is the only way an inner label becomes visible to a signature, and removing it removes the ability to write `Text[Public]` at all. What is a workaround is the `= ?`: those declarations want a BOUNDED parameter and settle for an open one. When this is fixed they should read as the bounded form, and the comment at that declaration cites this ticket so the change is not forgotten.

ACCEPTANCE: `Text[Int64]` against a parameter declared to range over the level sorts is a load error naming the parameter, the offending argument, and what was admissible. CONTROLS: `Text[Public]` and `Text[Untrusted]` still load; the guardians suite still passes, in particular fixtures/agent/rejected/leak.anthill still refused (the label must still be ENFORCED, not merely constrained); and an unbounded `sort T = ?` elsewhere -- List, Option, every prelude sort -- keeps admitting any argument, since the bound must be opt-in.

## Changes

### 2026-08-22T17:09:30Z — feedback — user

DESIGNED, NOT IMPLEMENTED. This produced docs/proposals/062-bounded-sort-parameters.md
and docs/design/062-implementation.md; no code, grammar or test changed. Acceptance here
is cargo-test, which a design cannot satisfy, so the ticket goes back to Open pending
review of 062.

THE TICKET'S PREMISE IS TRUE BUT FOR THE WRONG REASON. "A `requires` clause does not
help" reproduces exactly. The cause is not that the clause fails to bind — it is that the
only use-site enforcement that exists, `check_use_site_requires_eq` (WI-644/WI-835), is
hard-wired to `anthill.prelude.Eq` and reads NEGATIVELY (fire on a witnessed `NonEq`),
both for documented `Eq`-specific reasons that do not generalize. The substrate under it
IS general: `take_parameterized_type_sites()` records every written instantiation with
span and already-mapped bindings, and `Map[K = Float]` already prints the diagnostic shape
this ticket's acceptance asks for.

WHAT THE DESIGN BECAME, AND WHY IT IS NOT A BOUND. A parameter does not carry a bound; a
sort carries a GOAL over its parameters, entering the substitution as a constraint. The
governing rule is that a substitution is well-formed only if every constraint it carries is
satisfied, proved statically at load. That is smaller than a bound and settles nothing
about variance, transitivity or higher-kinded parameters.

THREE SPELLINGS REFUTED BY MEASUREMENT, recorded in 062 §History so they are not proposed
again. (1) A marker spec works mechanically — a positive check DOES discriminate,
`fact Marked[T = Int64]` refused where `[T = Public]` loads — but its rows cannot be
derived (`rule IsLevel[T = ?x] :- is_entity_of(?x, Level)` supplies no instance; spec
resolution never reads the SLD path), so the admissible set becomes a hand-maintained
second source of truth restating `EntityOf`. That is this ticket's own complaint one level
down. (2) `sort Trust <: TrustLevel` is the wrong RELATION — `types_compatible` is a union
of four arms and three raise the questions this ticket needn't answer. Naming the param
after the bound fails twice: 13 sorts in the tree have 2+ params, which would collide under
WI-764, and the name would shadow the enum inside the body it bounds. (3) A sort-body
`constraint` is inert AND resolves nothing — replacing both names with garbage loads
identically, 2675 facts either way. That last one is a separate defect: the WI-1034/WI-1058
"names nothing" refusals do not reach constraint bodies.

DECIDED (062 §Decisions, do not re-litigate): the keyword is `requires` with a
parenthesised goal, on WI-840's existing op-clause overload; no decidable-subset
restriction, since `max_depth` plus WI-628's truncation flag already handle a looping goal
by refusing rather than forbidding; the goal is a reflect relation
`SortGoalInfo(sort_ref, goal)` — two fields, NO `param`, because which parameters a goal
constrains is derivable from the goal and a field would make `requires flows_to(From, To)`
inexpressible; and the obligation is proved at load, not merely recorded.

BLOCKED ON A DISCHARGE PATH. `Constraint::Type` — the substrate slot this needs — has NO
producer and NO consumer outside `subst.rs`'s unit tests, whose values are placeholders
(`Value::Int(7)`). The live kind, `Constraint::Lacks`, does not use the generic wakeup
either: it is checked by a hand-rolled path at `bind_row_tail`, which is why every bind in
typing.rs can be `bind_value` and still honour it. `bind_value` has NO loud-on-bypass
assertion (`bind_compressed` does), so wiring a producer first would enforce nothing,
silently. Two shapes are written up in the design doc §2 with their costs; either must land
first, and both belong to constrained-term-substrate.md rather than here.

SPUN OUT: C2 of examples/guardians/docs/design/measured.md — an operation's `requires` over
a type-level variable loads clean and gates nothing, while WI-539's value preconditions do
gate. Same defect class, one level over; wants its own ticket.

### 2026-08-22T17:14:26Z — feedback — user

NOT A GUARDIANS PREREQUISITE — measured. The guardians suite passes on main with `sort Trust = ?` unbounded: 15/15, including exfiltrating_agent_is_refused_by_the_label. The security property rests on a sink demanding a LITERAL label, which an unconstrained parameter does not weaken. Nor would 062 close C7 — that laundering ends by binding the label to `Public`, an entity of TrustLevel, so 062's constraint is SATISFIED and the flow still goes through. C7 is a hole in the FLOW, 062 constrains the VOCABULARY. So guardians can launch without this, and C7 (held shut today only by the `bodies_of` projection discipline) is the one on the critical path.

