## Attributes

- id: WI-20261023-2F9HY-bare-at-a-side-of-in-a-rule
- created: 2026-10-23T17:13:08Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-23T18:46:21Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Bare at a side of `<=>` in a rule body, `lambda () -> e` is read as the arrow term `arrow(lambda, e)`, not a lambda, so the variable it is bound to holds a term. MEASURED 2026-10-23 (38a260a6): over `operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()` and `rule cc(?f, ?r) :- applyThunk(?f, ?r)`, the clause typing reads `rule bare(?r) :- ?f <=> lambda () -> now(), cc(?f, ?r)` as `unify(?f, arrow(lambda, now()))`, and it loads where its parenthesized twin `?f <=> (lambda () -> now()), cc(?f, ?r)` is refused (a function handed to `cc` performs `Clock`, WI-20261013-R1W5A); `rule swallowed(?r) :- ?f <=> lambda () -> 1, ?r <=> 2` binds `?f` to the term. In a call's argument (`cc(lambda () -> now(), ?r)`) and parenthesized, it is a lambda. Likely the infix desugaring reads `->` as the type arrow there. ACCEPTANCE: the bare and the parenthesized spelling are one clause at a side of `<=>` and of `=` (the bare `bare` refused as its twin is), in both parsers; a rows file driving each spelling.

## Changes

### 2026-10-23T17:59:27Z — feedback — claude

MET BY WI-20261015-C9802 (01424c91) UNDER KERNEL-LANGUAGE §4.8, NOT BY THIS TICKET'S READING: the bare spelling at a side of `<=>` or `=` is refused at load naming the parentheses ("a lambda written where a term is expected … is put in parentheses"), so `rule bare(?r) :- ?f <=> lambda () -> now(), cc(?f, ?r)` and `swallowed` no longer load and no variable is bound to the arrow term; it is not read as the parenthesized lambda. §4.8 makes an infix operand a `Term` position where an `Expr` is parenthesized, so one clause for the two spellings would change the spec. scaland unchanged (it has no WI-605/618 check, and the bare form loads there).

### 2026-10-23T18:46:20Z — feedback — claude

DELIVERED (2026-10-23), §4.8 CHANGED (user: "change 4.8"; decided: lambda only, every infix operator, and after a `requires`/`ensures` clause `=` stays the body separator). A lambda after an infix operator needs no parentheses: tree-sitter `infix_term` takes `choice(_atom_term, lambda_expr)` after an operator (4199 → 5019 parse states; admitting it only after the last operator measured 5273), the Rust converter visits that operand as an expression body, scaland's `term` and `clauseTerm` take `infixOperand = lambdaExpr | atomWithFieldAccess`. The bare and parenthesized spellings are one clause: `?f <=> lambda () -> plus1(1), applyThunk(?f, ?r)` 2, `lambda (x)`, `lambda (x: Int64)` 2, `lambda x -> x + 10` 11 (the body is the rest of the chain, the `,` ends it), `?f = lambda …` the twin's residual; `rule bare(?r) :- ?f <=> lambda () -> now(), …` and its `=` spelling are refused as their twins are (R1W5A rows `handsBoundBare`, `handsEq`, `handsEqBare`); a lambda through a column 2, as an `@[simp]` right side 5, and after `requires x > 0 =` as the body 6. After an operator `lambda` is now the keyword (§2.5): a parameter named `lambda` there is a syntax error, and over a declared `operation lambda` `lambda(1) -> Int64` is a lambda over the pattern `1`. Rows in wi_c9802_lambda_in_term_position_test; shared parity case `accept/lambda_as_infix_operand`; scaland `ParserParityTest`; tree-sitter corpus. Full gate 10600/0, families, scaland 748+47, corpus 236/236.

