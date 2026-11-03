## Attributes

- id: WI-20261103-F9ZR9-a-lambda-whose-binder-is
- created: 2026-11-03T09:49:44Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-03T12:46:16Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LAMBDA WHOSE BINDER IS WRITTEN THROUGH A LET ALIAS IS REFUSED IN ITS BODY WHEN APPLIED TO A CALL'S RESULT: over `sort State { sort P = ?; requires DataProvider[P = P]; entity state(provider: P) }` (`DataProvider { sort P = ?; sort K = ? }`), with `get(s: State, k: s.provider.K) -> s.provider.K = k` and `check(s: State, k: s.provider.K) -> Int64 = 42`, `operation fwd(st: State, j: st.provider.K) -> Int64 = let t = st / let h = lambda (k: t.provider.K) -> check(st, k) / h(get(t, j))` is refused "type mismatch in check.k (op-arg): expected st.provider.K, got t.provider.K" AT `check(st, k)` IN THE LAMBDA'S BODY — on HEAD 9c60680a and with WI-20261103-SG16K, measured 2026-11-03. Each half alone runs to 42 at `go()` (`let st: State[P = MemStore] = state(provider: mem(n: 1))`, `fwd(st, 41)`): the same lambda applied to `j` (since SG16K; `a_compound_receiver_through_an_alias_is_the_path_it_names`), the binder written `st.provider.K` applied to `get(t, j)`, and the `let` spelling `let k: t.provider.K = get(t, j)` / `check(st, k)` (WI-0RP29's `a_let_annotation_through_an_alias_names_its_target`). MEASURED with a debug print in `bind_and_label_pattern`: the visit binds the lambda's `k` at `st.provider.K` and `h` at `st.provider.K -> Int64`, so the `t`-keyed type `check` is handed is not the binder's type as the visit binds it — how the call's result `get(t, j)` (the callee's `s.provider.K` keyed to the argument `t`) reaches the body is not known. WHAT: measure first where `k` takes `t.provider.K` — the application's unification of the arrow with the argument, a later pass over the body, the call's re-key of its result through the alias — and read the call's result as the path the alias names there, as the `let` path does. ACCEPTANCE: the program runs to 42; a lambda `(k: t.provider.K) -> check(u, k)` for another `u: State` stays refused; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-11-03T12:45:48Z — feedback — claude

Delivered as rows, no source change. Measured with the CLI: the program is refused "type mismatch in check.k (op-arg): expected st.provider.K, got t.provider.K" on 9c60680a, and loads and runs to 42 on a9fefc9d (SG16K) and on 833ebfda; the refusal recorded on the SG16K tree was measured on an earlier draft of it. Two steps carry it: the binder read through the alias (read_written_annotation, SG16K) and the call reading its argument through it (call_arg_paths), so get(t, j) is st.provider.K; each backed out fails the new row. Rows: wi_sg16k_lambda_binder_projection_test a_call_result_through_an_alias_meets_the_binder_through_it. A binder among several given get(u, ju) loads; that is WI-20261103-2N4QH.

