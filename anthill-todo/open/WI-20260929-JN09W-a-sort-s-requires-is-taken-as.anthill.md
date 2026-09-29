## Attributes

- id: WI-20260929-JN09W-a-sort-s-requires-is-taken-as
- created: 2026-09-29T20:16:48Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:16:48Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SORT'S `requires` IS TAKEN AS SUPPLIED BY AN ARGUMENT OF THE RIGHT SORT AT ANOTHER BINDING, SO A CALL NO PROVIDER CAN SUPPLY LOADS CLEAN AND DIES AT RUN TIME. `sort U { requires Store[State = Buf[T = Int64, N = String]]; operation use(s: Buf[T = Int64, N = String]) -> Int64 = Store.peek(s) }`, the only provider `CB` at `Buf[T = Int64, N = Bool]`, called `U.use(buf(v: 1))` (from `main` or from a namespace-level operation alike): loads, and `anthill run` fails "internal evaluator error: DeferToRequirement: requirement param `__req_store` not bound in caller frame (running `U.use` …; frame binds [])". The same requirement with `use(n: Int64) = Store.peek(buf(v: n))`, called `U.use(1)`, is refused at load "requirement … cannot be supplied". Also with a holder in scope: `User requires Store[State = S]; go(s: S) = Store.peek(s)`, `run(b: Buf[T = Int64, N = Bool], c: Buf[T = String, N = Bool]) = User.go(b)`, providers at `Buf[T = Int64, N = String]` and `Buf[T = String, N = Bool]` — loads and dies the same way, and is refused without `c`. MEASURED on both builds of WI-20260929-WBHTM, typed and value-in-type spellings alike. MECHANISM (from WBHTM's review, V11): route 4's holder gate (`names_holder`, dict.rs ~2506) compares the holder's BASE SORT only, so an argument or local of sort `Buf` counts as naming a provider at any `Buf` binding; the pin gate is skipped, the dep is discharged with no dictionary, and the callee's frame lacks `__req_store`. The same route discharges WI-20260929-PFAGY's two-hop chain once its key is dropped. FOUND by WI-20260929-WBHTM's /code-review. ACCEPTANCE: both programs refused at load naming the requirement, as the `Int64`-parameter and no-holder twins are; full workspace green via rustland/scripts/test.sh.

