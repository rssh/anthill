## Attributes

- id: WI-20261030-4BXDW-a-dotted-operation-name-in-a
- created: 2026-10-30T19:39:02Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-01T09:06:28Z

- acceptance: cargo-test

- tags: typing

## Description

A DOTTED OPERATION NAME IN A FUNCTION-TYPED ARGUMENT OF A RULE-BODY CALL IS NEITHER APPLIED NOR TYPED: a goal loads clean and is undecided at run time, and the value-slot spelling is refused with the typer's internal-defect text. MEASURED on 2c0ae33e, over `operation apply1(f: (n: Int64) -> Int64, n: Int64) -> Int64 = f(n)`, `operation apply2(f: (a: Int64, b: Int64) -> Int64, a: Int64, b: Int64) -> Int64 = f(a, b)` and `sort S  operation twice(n: Int64) -> Int64 = n * 2  end`, in `namespace probe.dn`: (1) the goal `rule r(?r) :- apply1(S.twice, 3, ?r)` loads clean and is undecided, 'unknown operation: probe.dn.apply1.f' — the argument reaches the call as the `field_access(S, twice)` chain, unclassified and untyped, which the apply path (WI-20261023-Y6QW2, `applied_operation_name`) does not read as an operation; (2) the value slot `rule r(?r) :- ?r <=> apply1(S.twice, 3)` is refused, twice at one span, 'type mismatch in probe.dn.S.reference: expected a type value recorded where the sort is written (proposal 055 §1), got a plain reference to the sort — a defect in the walk that built this occurrence, not an error in the program'; (3) the goal `apply2(Int64.max, 3, 9, ?r)` loads clean and is undecided, where its one-segment twin (`import anthill.prelude.Int64.{max}`, `apply2(max, 3, 9, ?r)`) is refused at load: `max` carries no body, so no bare reference to it is a function value. CONTROLS, answering 6: the operation body `operation g() -> Int64 = apply1(S.twice, 3)`, and `import probe.dn.S.{twice}` with `apply1(twice, 3, ?r)`. A query writing the name (`probe.dn.apply1(probe.dn.S.twice, 3, ?r)`) holds the same chain. WHICH READING is WI-20261017-FTV0Q's decision (b), not taken yet: whether a dotted operation name in a data slot is its symbol. Today's verdicts are wrong under either answer — as its symbol, the clause types it as the one-segment name is (an eta at the slot's arrow, refused for a body-less operation) and runs it; as the chain, the argument is no function and the call is refused at load at the argument, as a type mismatch. Take (b) with the user first, or ask which reading this ticket implements. ACCEPTANCE: a row per program above, each clause verdict the operation body's answer or a load error located at the argument, never the internal-defect text; the goal and value-slot spellings agree; back-outs measured; full gate green.

## Changes

### 2026-11-01T09:06:25Z — feedback — user

Delivered in a3565677 (merged with origin/main in 55e228b6). Reading: the user's, 2026-11-01, WI-20261017-FTV0Q (b) type-directed — at a function-typed parameter a dotted operation name is the operation, typed and run as its one-segment name is; a relation's argument and a fact's column keep the chain. The ticket's three programs: goal and value apply1(S.twice, 3) answer 6, apply2(Int64.max, 3, 9, ?r) is refused at the argument as max is; never the internal-defect text. With it: a generic function parameter, a form (if, lambda), a body-less spec operation, an alias receiver read at its bindings, a member named like an imported operation or const (both walks read a chain's member as a name), ?r <=> idv(S.seven) (was the chain), ?f <=> S.seven beside applyThunk(?f) refused as ?f <=> seven is. Inline (user, 'Fix inline'): a fact pattern's Term field holds an operation's name as the term; a query makes a dotted name the operation at a function parameter and its one-segment node elsewhere, and refuses a call that does not fill its parameters by the typer's verdict (typing::query_call_arity_error), plus a left-out default and a goal's result: label. Rows: wi_4bxdw_dotted_operation_name_test (26; 17 pieces backed out, each failing its rows). Full workspace 11,337 passed before the merge, 11,360 on the merged tree; fresh-load and two-step 10,283; families green. Left, same on HEAD: a chain's member symbol depends on the scope it is written in (a query qualified path vs a fact beside an import); ?x <=> [S.seven, 1] keeps the chain inside a list (§6.7 data).

