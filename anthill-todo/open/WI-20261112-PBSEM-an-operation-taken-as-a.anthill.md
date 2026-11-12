## Attributes

- id: WI-20261112-PBSEM-an-operation-taken-as-a
- created: 2026-11-12T05:12:09Z

- status: Open
- status_agent: claude
- status_at: 2026-11-12T05:12:09Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, proposal-073

## Description

AN OPERATION TAKEN AS A FUNCTION VALUE WHOSE CARRIER A LATER ARGUMENT FIXES IS GIVEN NO DICTIONARY — proposal 073 §5.4 (stage 2, WI-20261105-89J6K) says such a value is the lambda that calls it, typed at the instance the value is used at. PROGRAM: `sort Desc { sort T = ?  operation describe(x: T) -> Int64 }`, provided at `Leaf` (`describe = 7`) and `Pebble` (`9`); `operation useS[P](x: P) -> Int64 requires Desc[T = P] = Desc.describe(x)`, `operation app[X](f: (x: X) -> Int64, x: X) -> Int64 = f(x)`, `operation main() -> Int64 = app(useS, leaf)` — 073's own §5.4 example. MEASURED on c7ad2ef0 (which changes no dictionary path; the no-projection twin over `Storage`, `app(g2, memStore)` beside a second provider, was measured the same on 218fb292): `main` and `app(useS, pebble)` LOAD and stop at run time, "DeferToRequirement: requirement param `__req_desc` not bound in caller frame (running `useS` …; frame binds [])". The sort's own clause, `sort Sp { sort P = ?  requires Desc[T = P]  operation t(x: P) -> Int64 = Desc.describe(x) }` with `app(Sp.t, leaf)`, is refused at load: "expected `Sp.t` used as a function value to have a satisfiable `requires` … got unsatisfiable `Sp` requirement for bare operation `Sp.t` (WI-420)". TWINS, each runs to 7: the direct calls `useS(leaf)` and `Sp.t(leaf)`; the annotated lambdas `app(lambda (x: Leaf) -> useS(x), leaf)` and `app(lambda (x: Leaf) -> Sp.t(x), leaf)`; a slot that fixes the carrier where the value is written, `applyLeaf(useS)` and `applyLeaf(Sp.t)` over `applyLeaf(f: (x: Leaf) -> Int64)`. The un-annotated lambda `app(lambda (x) -> useS(x), leaf)` is refused at load, "`useS`.type_arg: expected a type for 'P', got unconstrained". With ONE provider of the spec the op-clause program runs (WI-20261104-KBZ4F's `app(g, memStore)` answers 7). MECHANISM, not traced past the first step: the dictionary is chosen where the reference is typed (`attach_eta_dispatch_dict`: `eta_op_scoped_dicts` stamps the op half, the sort half is refused there), from the expected arrow, whose `A` is still the call's own variable when the argument is typed; the call that later fixes it hands the value nothing. EXPECTED: `app(useS, leaf)` 7, `app(useS, pebble)` 9, `app(Sp.t, leaf)` 7; at a carrier no provision answers, refused at load as the direct call is. ACCEPTANCE: rows for both clause kinds and both carriers, driven to their values; back-outs measured; full gate green.

