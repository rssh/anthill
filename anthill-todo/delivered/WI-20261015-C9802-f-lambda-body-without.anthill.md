## Attributes

- id: WI-20261015-C9802-f-lambda-body-without
- created: 2026-10-15T20:50:56Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-23T17:57:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

`?f <=> lambda () -> body` WITHOUT PARENTHESES PARSES AS A FUNCTION TYPE, and the body is evaluated where it stands.

MEASURED 2026-10-15 on cc3d1a7d, and the same before WI-20260908-9WVT7 (found by its review), over `operation plus1(n: Int64) -> Int64 = n + 1` and `operation applyThunk(f: () -> Int64) -> Int64 = f()`: `rule bareOnly(?f) :- ?f <=> lambda () -> plus1(1)` answers `?f = arrow(lambda, 2)`; `rule bare(?r) :- ?f <=> lambda () -> plus1(1), applyThunk(?f, ?r)` faults ("unknown operation: probe.h.applyThunk.f") and leaves `applyThunk(arrow(lambda, 2), ?_)`; parenthesised, `?f <=> (lambda () -> plus1(1))`, it answers 2. So `lambda () -> e` on the right of `<=>` is read as the arrow type `lambda -> e`, and `e` is reduced as an operand.

TO DECIDE: the precedence of `lambda` against the arrow type in a term position (tree-sitter-anthill/grammar.js; scaland's fastparse follows), or a load refusal of a bare `lambda` as an arrow's domain.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; tree-sitter corpus): `bareOnly` answers a closure, or the program is refused naming the parenthesis; `bare` answers 2.

## Changes

### 2026-10-23T17:57:41Z — feedback — claude

DELIVERED (2026-10-23): REFUSED AT LOAD, NAMING THE PARENTHESES. kernel-language §4.8 already decides the question this ticket left open: an infix operand, a dot receiver, a `match` scrutinee, an `if` condition and a set element are `Term` positions, where an `Expr` is parenthesized; there `lambda` is not the keyword (§2.5), which is why `lambda ()` read as a call under the arrow-type operator. So no precedence change: `LoadError::LambdaInTermPosition`, raised at the `lambda` for a `lambda` written as a name (a call `lambda(…)` or bare) under a pratt-minted arrow and `NotFound` in scope — in a clause (`check_bare_arrow_typo`, through one walk with WI-618's leaf witness, `find_arrow_witness`) and in an operation body or a const (the WI-605 site). `bareOnly` and `bare` are refused at 5:31 and 5:27 ("a lambda written where a term is expected … is put in parentheses: `(lambda … -> …)`"); `?f <=> (lambda () -> plus1(1)), applyThunk(?f, ?r)` answers 2, and the closure handed out through a column answers 2. Before: five shapes loaded silently (the two rules here, a set element, an open body `lambda () -> ?y`, a `@[simp]` right-hand side) and ten were refused advising the `lambda` keyword or naming `lambda`/`arrow` as nothing. A `lambda` the program declares is that declaration (§2.5): `operation lambda(x: Int64) -> Int64 = x + 40` and `?t <=> lambda(1) -> Int64` answer `arrow(41, Int64)`; a field or a binder named `lambda`, and one two imports reach (reported ambiguous, only), are not refused. Rows in wi_c9802_lambda_in_term_position_test with their back-outs; a corpus entry in tree-sitter-anthill expressions.txt. R1W5A's `a_function_value_and_an_open_row_load` wrote the bare form and measured `arrow(lambda, now())`; it is parenthesized. Full gate 10598/0, families, corpus 236/236, scaland 747+47. WI-20261023-2F9HY is this defect, found by R1W5A. NOT DONE: a query (`anthill query '?f <=> lambda () -> plus1(1)'`) still binds the arrow term — a query lowers no lambda at all (WI-20261023-Y6QW2, noted there); scaland has no WI-605/618 check, so the bare form loads there.

### 2026-10-23T18:46:19Z — feedback — claude

SUPERSEDED IN PART BY WI-20261023-2F9HY (user, 2026-10-23: "change 4.8"): a lambda AFTER an infix operator needs no parentheses now (kernel-language §4.8) — `?f <=> lambda () -> plus1(1), applyThunk(?f, ?r)` answers 2, as its parenthesized twin does. The refusal delivered here stays for the positions where a lambda is still parenthesized: before an operator, the operand of `not`, a dot receiver, a `match` scrutinee, an `if` condition, a set element.

