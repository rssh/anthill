## Attributes

- id: WI-20261121-204T6-a-lambda-whose-parameter
- created: 2026-11-21T00:21:51Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T00:21:51Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LAMBDA WHOSE PARAMETER PROJECTS A SIBLING PARAMETER PANICS THE TYPER: over `sort State { sort P = ?; requires DataProvider[P = P]; entity state(provider: P) }` (`DataProvider { sort P = ?; sort K = ? }`, `MemStore` providing it at `K = Int64`) and `check(s: State, k: s.provider.K) -> Int64 = 42`, the body `operation fwd(u: State, ju: u.provider.K) -> Int64 = let h = lambda (s2: State, k: s2.provider.K) -> check(s2, k); h(u, ju)` stops a build with debug assertions at load, "the holder `s2` was opened at `State` and is read at `State[P = s2.P]`: a re-key gave a path another value" (`PathOpenings`, kb/typing/elaborate.rs, whose doc says a release build opens such a path afresh, unrecorded), and so does the same body with the lambda never applied (`h(u, ju)` replaced by `42`) — measured on d75028d1 with the debug CLI, 2026-11-21; no `let` alias is involved (found beside WI-20261103-FV92R, whose fix this is not). The body's record keys a path by the binder symbol, and the lambda's `s2.provider` is opened at two types of one binder: `State` as written, and `State[P = s2.P]` with its unwritten slot named. WHAT: measure which two readings disagree — the read env `visit.rs` builds for a lambda whose parameter projects a sibling (`projects_sibling`, binding the written parameter types) against the binder check / the parameter's own reading after `rigidify_unwritten_sort_params` — and make them read the holder at one type, so the path is opened once. ACCEPTANCE: the program runs to 42 at `go()` (`let st: State[P = MemStore] = state(provider: mem(n: 1))`, `fwd(st, 41)`); `h(u, ju)` where `k`'s key is another state's (a second `w: State`, `h(w, ju)`) is refused at the application; the unapplied lambda loads; full workspace green via rustland/scripts/test.sh.

