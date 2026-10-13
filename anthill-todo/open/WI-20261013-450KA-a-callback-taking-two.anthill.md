## Attributes

- id: WI-20261013-450KA-a-callback-taking-two
- created: 2026-10-13T19:29:42Z

- status: Open
- status_agent: user
- status_at: 2026-10-13T19:29:42Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A CALLBACK TAKING TWO PARAMETERS IS JUDGED TWO WAYS AT A SLOT WHOSE ROW IS PROJECTED OFF A RECEIVER AND HOLDS THE CALLER'S OWN ROW — the lambda written at the call is refused, the same lambda held in a `let` loads and runs. Found by the generated family c-callback-row (WI-20261002-E1WN0), which lists the two programs as its exception to one-verdict-for-two-spellings under this ticket. THE PROGRAM: `sort Src { effects E = ?; entity src(n: Int64) }`; `operation run(s: Src, p: Cell[V = Int64], f: (k: Cell[V = Int64], u: Int64) -> Int64 @ {s.E}) -> Int64 effects {s.E} = f(p, 5)`; `operation use[R](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {R}) -> Int64 effects {Modify[q], Modify[r], Error[String], R}` = `let s: Src[E = {Modify[q], Modify[r], Error[String], R}] = src(n: 0)`, then the call. MEASURED (2026-10-13): (1) `run(s, q, lambda (k: Cell[V = Int64], u: Int64) -> h(u))` is refused "type mismatch in run.f (op-arg): expected … @ {Error[T = String], Modify[T = q], Modify[T = r], ?R}, got … @ {?R}"; (2) `let g =` that lambda, `run(s, q, g)` loads and `go()` runs; (3) the same split with the body `put(k, u)`, whose row is `{Modify[k]}` — the call refuses it, the `let` runs and writes the cell; (4) with a ONE-parameter callback `(k: Cell[V = Int64])` both spellings are refused as (1) is; (5) at that slot a callback that is pure, raises `Error[String]` or writes `r` is admitted in every spelling, so of the rows inside the slot's only `{R}` — the caller's own row, which the slot's row holds — is refused; (6) with `E = {}` every spelling of a writing callback is refused "which the closed row does not admit": nothing unsound was found. TO DECIDE, two questions the measurements leave: whether a callback whose row is the caller's own `R` conforms to a slot row holding `R` (subset says yes; (1) and (4) say no), and which reader lets the two-parameter `let` through — (2) is right if the answer is yes, (3) only if the slot admits a callback writing the cell it is handed, which its row does not say. ACCEPTANCE: each program above has one verdict in both spellings and at both arities, stated in kernel-language.md's callback-row paragraph if it is not there; family c-callback-row's exception removed and its verdict file re-written by the change; rustland/scripts/families.sh green; full workspace green via rustland/scripts/test.sh.

