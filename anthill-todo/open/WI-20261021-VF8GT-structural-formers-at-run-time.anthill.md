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

