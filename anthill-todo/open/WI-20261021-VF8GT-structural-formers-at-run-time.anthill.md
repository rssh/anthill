## Attributes

- id: WI-20261021-VF8GT-structural-formers-at-run-time
- created: 2026-10-21T17:48:52Z

- status: Open
- status_agent: user
- status_at: 2026-10-21T17:48:52Z

- acceptance: cargo-test

- tags: typing, proposal-065

## Description

STRUCTURAL FORMERS AT RUN TIME — A NAMED TUPLE AND AN ARROW ARE TESTED, FILLED AND READ AS A TYPE VALUE AS A SORT IS. Proposal 065 §7 step 2 deferred them ('BUILT for SORTS (2026-09-20); FORMERS deferred — a named tuple or arrow has no sort to carry a provision, so it needs a structural reading rather than a provision row'; WI-20260919-HXGXF's delivery note; WI-20260919-N31XX's WHAT REMAINS; the `TypeValue` comment in reflect.anthill), and no ticket owned them. Filed with the user 2026-10-21 from WI-20261013-GGXCX: narrowing a value of a rigid 'some type' to a type is defined by the run-time type test (`domain(?x, T)`, the typed head's guard), which decides every ground value of a sort, a primitive and a parametric sort, and this ticket owns the formers. MEASURED 2026-10-21 on bb99c630. (1) AN ARROW IS NOT DECIDED: over `operation inc() -> (Int64) -> Int64 = lambda (n: Int64) -> n + 1`, `rule hf(?f) :- ?f <=> inc()`, the typed head `rule ff(?x: (Int64) -> Int64) :- hf(?x)` and the goals `hf(?x), domain(?x, (Int64) -> Int64)` and `… (String) -> Int64)` are each conditional, residual `domain(<spliced>, …)`: a closure carries no type. (2) `TypeValue` AT A FORMER IS REFUSED AT LOAD, honestly: `TypeValue.type_value[T = (a: Int64, b: String)]()` — 'a tuple or an arrow carries no provision itself … the derived instances cover sorts only'. `SortDomain` likewise has no instance at a former; a typed head at one is its `domain` test alone. (3) A TUPLE TYPE WRITTEN AS A VALUE IN A RULE BODY IS A TUPLE OF VALUES (kernel-language §5.4's alias paragraph: 'read as written in a data slot, where a tuple written is a tuple of values'), so `ht(?x), domain(?x, (a: Int64, b: String))` and `domain(?x, TP)` over `sort TP = (a: Int64, b: String)`, with `ht` binding `(a: 1, b: "s")`, answer NOTHING, silently, and `not(domain(…))` over them holds — where the typed heads `?x: (a: Int64, b: String)` and `?x: TP` hold, `?x: (a: String, b: String)` is refuted and `?x: (Int64, String)` holds of `(1, "s")`. So the tuple TEST is decided; what is missing is a spelling of the tuple type as a value in a data slot, or a load error where a tuple of values stands in `domain`'s type slot. CONTROLS, decided correctly today: `1`, `"a"`, an entity, a constant constructor, `[1, 2]` at `List[T = Int64]` and refuted at `List[T = String]`, `[]` and `none` at every instance; a spec as the type is refused at load with advice. TO BUILD: a closure carries the arrow type its lambda or operation was typed at, and `domain` decides it by the arrow subtyping rule (parameters contravariant, result covariant, the row); `TypeValue` and `SortDomain` read a former structurally; DECIDE with the user what (3) becomes — the type slot reading a written tuple as its type, or a load error. ACCEPTANCE (cargo-test, driven): the arrow rows decided both ways; `type_value` at a tuple and an arrow answers the type; (3) as decided, with no silent empty answer left; the controls unchanged; each back-out named at its row.

## Changes

### 2026-10-21T17:49:12Z — feedback — user

CORRECTION to the description's (3): the paragraph quoted is kernel-language §5.1's 'An alias in a name is read through', not §5.4.

### 2026-10-22T03:49:24Z — feedback — user

MEASURED 2026-10-22 on 619d6caf (the parent of WI-20261013-WF14Z's first part), FROM WF14Z: A CLOSURE BOUND BEFORE THE CLAUSE RUNS IS REFUTED BY AN ARROW-TYPED HEAD, NOT LEFT UNDECIDED. Over `operation inc() -> (Int64) -> Int64 = lambda (n: Int64) -> n + 1` and `rule viaW2(?f: (Int64) -> Int64, ?r) :- ?r <=> 1`: `viaW2(lambda (n: Int64) -> n + 1, ?r)` and `hf(?f), viaW2(?f, ?r)` over `rule hf(?f) :- ?f <=> inc()` each answer NOTHING, silently — where the description's (1) measured the same bound conditional when the body binds the variable after the guard (`rule ff(?x: (Int64) -> Int64) :- hf(?x)`). The closure is bound when the head matches, so the generated `domain(?f, (Int64) -> Int64)` reads a value with no type and refutes it. Since WF14Z a type written on the variable reaches the clause's typing, so a thunk bound by a typed head now LOADS where it was refused for its `ErrorTag` (`rule viaW(?f: () -> Int64 @ {Error[Boom]}, ?r) :- Error.reify(?f, ?r)` called with a lambda), and answers nothing for this reason. To decide with this ticket's arrow test, both ways.

### 2026-10-25T13:57:03Z — feedback — claude

From WI-20261025-27050 (user, 2026-10-25): a type pattern at a named tuple or an arrow — an `Error.reify` boundary catching by a former's pattern, and `type_admits` judging two formers, which it leaves unjudged today — belongs here ("We have ticket about sort for tuple, and TypePattern will go there"). 27050 makes TypePattern answer at every sort, a spec included (is a subtype of an instance, or the carrier's own provision of one); this ticket extends it to the formers.

