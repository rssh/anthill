## Attributes

- id: WI-20260930-ZS9NZ-an-effect-whose-projection
- created: 2026-09-30T12:27:43Z

- status: Open
- status_agent: user
- status_at: 2026-09-30T12:27:43Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN EFFECT WHOSE PROJECTION GROUNDS TO A ROW WITHOUT ONE IS RE-KEYED A SECOND TIME, SO A SELF-RECURSIVE CALL RENAMES WHAT IT INCURS. `sort Strm { sort T = ?; effects E = ?; operation obs(s: Strm) -> Bool effects s.E = true }`, `sort Producer { operation eff_stream(p: Producer) -> Strm[T = Int64, E = {Modify[p]}] }`, `operation rec(s: Strm, p: Producer, q: Producer, stop: Bool) -> Bool effects {s.E, Modify[q]} = if stop then Strm.obs(s) else rec(Producer.eff_stream(p), q, q, true)` LOADS, though the recursive call incurs its argument's `s.E` = `{Modify[p]}` and `Modify[p]` is undeclared. The same call passing `p, q` is refused naming `Modify[T = p]`, and so is a non-recursive `outer(p: Producer, q: Producer) -> Bool effects {Modify[q]} = rec(Producer.eff_stream(p), q, q, true)`. CAUSE: `check_apply_iter`'s per-effect re-key (`pre_substituted`, typing/apply.rs) skips an effect only while its ELIMINATED form still holds a projection; `s.E` grounded to `{Modify[p]}` — already the caller's vocabulary — is then re-keyed callee-to-caller, and in a self-recursive call the caller's `p` IS the callee parameter `p`, renamed to the `q` the call passes for it. The return re-key and the WI-606 fallback ask the DECLARED type since WI-20260929-0RP29; this site does not. MEASURED identically before that ticket. CAUTION: the effect map also carries WI-506's projection-argument heads and drops WI-20260823-4GBQV's placeless arguments, which the elimination's `arg_syms` does not — gating on the declared effect must not lose either for a `denoted` sharing an effect element with a projection. ACCEPTANCE: the program above is refused naming `Modify[T = p]`; declaring `Modify[p]` as well loads; the WI-459 `count(rest)` rows still pass; full workspace green via rustland/scripts/test.sh.

