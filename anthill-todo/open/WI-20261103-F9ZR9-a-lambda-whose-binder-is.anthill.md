## Attributes

- id: WI-20261103-F9ZR9-a-lambda-whose-binder-is
- created: 2026-11-03T09:49:44Z

- status: Open
- status_agent: user
- status_at: 2026-11-03T09:49:44Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LAMBDA WHOSE BINDER IS WRITTEN THROUGH A LET ALIAS IS REFUSED IN ITS BODY WHEN APPLIED TO A CALL'S RESULT: over `sort State { sort P = ?; requires DataProvider[P = P]; entity state(provider: P) }` (`DataProvider { sort P = ?; sort K = ? }`), with `get(s: State, k: s.provider.K) -> s.provider.K = k` and `check(s: State, k: s.provider.K) -> Int64 = 42`, `operation fwd(st: State, j: st.provider.K) -> Int64 = let t = st / let h = lambda (k: t.provider.K) -> check(st, k) / h(get(t, j))` is refused "type mismatch in check.k (op-arg): expected st.provider.K, got t.provider.K" AT `check(st, k)` IN THE LAMBDA'S BODY — on HEAD 9c60680a and with WI-20261103-SG16K, measured 2026-11-03. Each half alone runs to 42 at `go()` (`let st: State[P = MemStore] = state(provider: mem(n: 1))`, `fwd(st, 41)`): the same lambda applied to `j` (since SG16K; `a_compound_receiver_through_an_alias_is_the_path_it_names`), the binder written `st.provider.K` applied to `get(t, j)`, and the `let` spelling `let k: t.provider.K = get(t, j)` / `check(st, k)` (WI-0RP29's `a_let_annotation_through_an_alias_names_its_target`). MEASURED with a debug print in `bind_and_label_pattern`: the visit binds the lambda's `k` at `st.provider.K` and `h` at `st.provider.K -> Int64`, so the `t`-keyed type `check` is handed is not the binder's type as the visit binds it — how the call's result `get(t, j)` (the callee's `s.provider.K` keyed to the argument `t`) reaches the body is not known. WHAT: measure first where `k` takes `t.provider.K` — the application's unification of the arrow with the argument, a later pass over the body, the call's re-key of its result through the alias — and read the call's result as the path the alias names there, as the `let` path does. ACCEPTANCE: the program runs to 42; a lambda `(k: t.provider.K) -> check(u, k)` for another `u: State` stays refused; full workspace green via rustland/scripts/test.sh.

