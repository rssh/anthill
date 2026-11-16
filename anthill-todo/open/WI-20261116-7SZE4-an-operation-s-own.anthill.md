## Attributes

- id: WI-20261116-7SZE4-an-operation-s-own
- created: 2026-11-16T10:13:06Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T10:13:06Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN OPERATION'S OWN PRECONDITION NAMING A SPEC'S MEMBER DOES NOT DISCHARGE ITS CALLEE'S. PROGRAM: sort Pred { sort T = ?  operation ok(x: T) -> Bool } (ok has no body), sort Leaf { entity leaf(v: Int64)  provides Pred[T = Leaf]  operation ok(x: Leaf) -> Bool = match x case leaf(v) -> v > 2 }, operation f(x: Leaf) -> Int64 requires Pred.ok(x) = 1, operation g(y: Leaf) -> Int64 requires Pred.ok(y) = f(y). MEASURED on 7c63d768, and before WI-20261105-CBRD2 typed a contract's member goals (b01147f4): g is refused, 'expected precondition ok(y) provable at the call site, got unsatisfied precondition'. With a Bool operation that has a body (operation big(x: Leaf) -> Bool = ...; f requires big(x); g requires big(y) = f(y)), g loads: the assumed precondition answers the callee's. WANTED: g's own requires Pred.ok(y) answers f's at f(y), as a bodied Bool operation's does. ACCEPTANCE: a row for g loading, and a control where g assumes Pred.ok of another parameter and is refused; full workspace green via rustland/scripts/test.sh.

