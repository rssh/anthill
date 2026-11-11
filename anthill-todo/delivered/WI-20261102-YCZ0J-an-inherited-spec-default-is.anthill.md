## Attributes

- id: WI-20261102-YCZ0J-an-inherited-spec-default-is
- created: 2026-11-02T07:07:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-11T20:51:11Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN INHERITED SPEC DEFAULT IS NOT REACHABLE THROUGH ITS PROVIDER'S NAME: `List.isEmpty([1, 2])` is refused at load, "unknown functor — no rule, fact, operation, entity, const or builtin is declared under that name. Fix the spelling, or import the namespace that declares `List.isEmpty`", where `[1, 2].isEmpty()` and `Stream.isEmpty([1, 2])` answer `false`. Found on WI-20260925-SHED7.

MEASURED on 5476eece, the same on f0d38c95. With `sort Mk { sort C = ?; operation e() -> C; operation viaDefault() -> C = e(); operation viaRecv(c: C) -> Int64 = 5 }` and `sort A { entity a(n: Int64); provides Mk[C = A]; operation e() -> A = a(n: 1) }`: `A.viaRecv(a(n: 9))` and `A.viaDefault()` are refused the same; `a(n: 9).viaRecv()` answers 5 and `Mk[C = A].viaDefault()` answers `a(n: 1)`. kernel-language §8.7: "the sort gains all operations defined in the spec. Defaulted operations (a spec-level `operation … = body`) carry over automatically".

TO DECIDE with the user: does `Carrier.op` name a default the carrier inherits — `List.isEmpty(xs)` the spec's member at `List`'s instance, `A.viaDefault()` the default run at `A`'s — or is the spec's spelling the only one, and then the refusal says so (names the spec and its spelling) instead of "unknown functor … Fix the spelling".

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): as decided — either `List.isEmpty([1, 2])` answers `false` and `A.viaDefault()` answers `a(n: 1)`, or each refusal names the spec's spelling; the working spellings unchanged.

## Changes

### 2026-11-11T20:51:10Z — feedback — claude

DECIDED with the user 2026-11-11: `Carrier.op` names the member the carrier's own provisions lend, called at its instance — the member a dot on a value of the carrier reaches, chosen by §8.7's coherence order. Delivered: `A.viaDefault()` answers `a(n: 1)`, `List.isEmpty([1, 2])` answers false, in every spelling (paren-less, path, alias, `let`, bracketed receiver, eponymous sort, rule body, `@[simp]` side); `List.isEmpty(some(1))` refused at the hold on `Self`; a witness's default refused (row on WI-20261003-FFY4R); an effect guard keeps the name it spells (§5.5). Found beside it and fixed: `Numeric[T = String].add(1, 2)` loaded and answered 3, the receiver's bracket dropped.

