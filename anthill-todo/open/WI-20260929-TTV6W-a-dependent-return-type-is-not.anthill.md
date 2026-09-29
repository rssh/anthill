## Attributes

- id: WI-20260929-TTV6W-a-dependent-return-type-is-not
- created: 2026-09-29T20:17:21Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:17:21Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A DEPENDENT RETURN TYPE IS NOT INSTANTIATED AT THE CALL, SO ITS UNINSTANTIATED VALUE PASSES AN ARGUMENT CHECK AT ANOTHER VALUE. `mk(n: Int64) -> Buf[T = Int64, N = n] = buf(v: n)`, `use(s: Buf[T = Int64, N = 3]) -> Int64 = Store.peek(s)`, providers `C3` at `N = 3` (`s.v + 30`) and `C4` at `N = 4` (`s.v + 40`): `use(mk(4))` LOADS and runs C3 on a value built at `N = 4` (34). The literal twin `use(mk4())` with `mk4() -> Buf[T = Int64, N = 4]` is refused "type mismatch in use.s (op-arg): expected Buf[T = Int64, N = 3], got Buf[T = Int64, N = 4]", and `let b: Buf[T = Int64, N = 3] = mk(3)` is refused "expected Buf[T = Int64, N = 3], got Buf[T = Int64, N = n]" — the dependent type is never instantiated with the argument. MEASURED on WI-20260929-WBHTM's build (before it, `use`'s body was refused outright, so nothing ran). MECHANISM: `mk(4)`'s type stays `Buf[T = Int64, N = denoted(Ref(mk.n))]` — the callee's own parameter place, re-keyed symbol to symbol but never replaced by the argument — and the op-arg check accepts that against `N = 3`. FOUND by WI-20260929-WBHTM's /code-review (V12). ACCEPTANCE: `use(mk(4))` refused at load as `use(mk4())` is (or `mk(n)`'s type instantiated at the argument, `N = 4`), and `use(mk(3))` runs C3; full workspace green via rustland/scripts/test.sh.

