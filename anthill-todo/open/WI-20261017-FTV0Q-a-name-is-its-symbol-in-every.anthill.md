## Attributes

- id: WI-20261017-FTV0Q-a-name-is-its-symbol-in-every
- created: 2026-10-17T20:57:03Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T20:57:03Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A NAME IS ITS SYMBOL IN EVERY SPELLING AND POSITION, AND A NAME NOTHING DECLARES IS NO VALUE IN A CLAUSE. User, 2026-10-17: 'it should be no difference between reference to red as qualified name or as name (which should be reference to symbol)'. Delivered for an entity constructor by 7d53438d (WI-20260908-9WVT7; §6.7; rows tests/include/wi_9wvt7_qualified_constructor_test.rs and scaland QualifiedConstructorTest): `Colour.red` and `red` are one term in a fact, a goal, a query and an operation body. Two classes are left, MEASURED on 7d53438d. (1) THE DOTTED NAME OF ANOTHER KIND. A nullary OPERATION: in an operation body `operation go() -> Int64 = Box.zero` is refused ('zero.name: expected resolved name, got unresolved'), where the one-segment `zero` in Box's own body (`two() = zero + 2`) is the call and the rule body's `?y <=> Box.zero` binds 0 — pinned by dotted_nullary_op_call_test::an_operation_body_is_not_widened, an earlier rule ('in an operation body the bare Box.zero names no operation') to revisit with the user. In a data slot `fact fz(Box.zero)` holds the field_access chain (`fz(?x)` answers `Box.zero`) while `fact inBox(zero)` written inside Box holds the symbol (`zero`), so `sameZ(?x) :- fz(?x), Box.inBox(?x)` answers nothing. A RULE name: §6.7's own example `fact holds(nsx.tgt)` keeps the chain, which a goal writing `tgt` in nsx's scope does not meet (the data-slot exception now names a const and a constructor only). (2) A NAME NOTHING DECLARES. `fact other(nosuchname)` loads and `other(?x)` answers `nosuchname`; `rule r :- other(nosuchname)` loads; and a nested sort's constructor written by its one-segment name where it is not in scope — `fact plainM(sketch)` at namespace level, `sketch` declared in `Colour.method` — loads and holds an unresolved name that no goal writing `Colour.method.sketch` finds. An operation body refuses a name nothing declares. DECISIONS TO TAKE WITH THE USER BEFORE IMPLEMENTING: (a) whether `Box.zero` in an operation body is the call, as `zero` is; (b) whether a dotted operation or rule name in a data slot is its symbol (changes §6.7's example and the 719FJ / 4NEKZ rows built on it); (c) whether a name nothing declares in a clause's data slot is refused at load, or is an atom by design. ACCEPTANCE: rows driving each decided reading in every walk that builds the term (operation body, clause term, rule body, query, and scaland's reallocTerm where it applies), back-outs measured; full gate green.

## Changes

### 2026-10-30T19:39:15Z — feedback — claude

MEASURED 2026-10-30 on 2c0ae33e: decision (b) has a function-slot case, filed as WI-20261030-4BXDW. A dotted operation name handed to a rule-body call's arrow-typed parameter (`apply1(S.twice, 3, ?r)`, `apply2(Int64.max, 3, 9, ?r)`) loads clean and is undecided at run time, and the value-slot spelling `?r <=> apply1(S.twice, 3)` is refused with the typer's internal-defect text, where the operation body's `apply1(S.twice, 3)` and the imported one-segment `twice` answer 6 (one-segment names passed as data are applied since WI-20261023-Y6QW2, 4903165d). Whichever reading (b) takes decides that ticket's fix.

