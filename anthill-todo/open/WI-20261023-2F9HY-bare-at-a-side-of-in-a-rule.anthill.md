## Attributes

- id: WI-20261023-2F9HY-bare-at-a-side-of-in-a-rule
- created: 2026-10-23T17:13:08Z

- status: Open
- status_agent: claude
- status_at: 2026-10-23T17:13:08Z

- acceptance: cargo-test, scaland-sbt-test

## Description

Bare at a side of `<=>` in a rule body, `lambda () -> e` is read as the arrow term `arrow(lambda, e)`, not a lambda, so the variable it is bound to holds a term. MEASURED 2026-10-23 (38a260a6): over `operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()` and `rule cc(?f, ?r) :- applyThunk(?f, ?r)`, the clause typing reads `rule bare(?r) :- ?f <=> lambda () -> now(), cc(?f, ?r)` as `unify(?f, arrow(lambda, now()))`, and it loads where its parenthesized twin `?f <=> (lambda () -> now()), cc(?f, ?r)` is refused (a function handed to `cc` performs `Clock`, WI-20261013-R1W5A); `rule swallowed(?r) :- ?f <=> lambda () -> 1, ?r <=> 2` binds `?f` to the term. In a call's argument (`cc(lambda () -> now(), ?r)`) and parenthesized, it is a lambda. Likely the infix desugaring reads `->` as the type arrow there. ACCEPTANCE: the bare and the parenthesized spelling are one clause at a side of `<=>` and of `=` (the bare `bare` refused as its twin is), in both parsers; a rows file driving each spelling.

