## Attributes

- id: WI-20261016-5CDN5-071-d-a-raise-carries-its-type
- created: 2026-10-16T14:51:31Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-24T17:56:50Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261016-YM8HD-071-c-error-reify-requires

- tags: proposal-071

## Description

071 (d): A RAISE CARRIES ITS TYPE — `raise … requires TypeValue[T = T]`, AND THE BOUNDARY ADMITS BY FULL TYPE. Proposal 071 §1.3. Delivers WI-20260911-3MV2C.
THE CHANGE: `operation raise(error: T) -> Nothing effects Error[T] requires TypeValue[T = T]`; the raised error travels with that evidence, and the boundary calls `admits` with its `type_value()`. A monomorphic raise's evidence is static; a generic raiser states the clause (`raiseAt[P](p: P) requires TypeValue[T = P]`); a host raiser (`division_by_zero`, `match_failed`, `evaluation_failure`, …) supplies its payload sort's derived evidence. A raise at a tuple or arrow payload is refused at load (065 §2: no instance yet).
MEASURED (2026-10-16): `caughtS(n) -> Result[E = Boom[Reason = String], T = Int64] effects {Error[Boom[Reason = Int64]]} = Error.reify(lambda () -> both(n))`, inside an outer boundary, answers "inner" for `boom(5)` where "outer" is right — the runtime compares head sorts. Census: no `Error[(…)]` label outside tests; six in three test files (`wi_9wvt7_reify_rule_body_test`, `wi_9wvt7_error_reify_test`, `wi_n31xx_type_value_read_rule_test`), all fixtures of the tuple refusal, which move from the reify to the raise.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh, scaland sbt testFull): 3MV2C's nested boundaries at `Box[V = Int64]` / `Box[V = String]` answer through the outer for a `Box[V = String]` raise and the inner for a `Box[V = Int64]` one, the two-distinct-sorts row passing either way; the "inner"/"outer" row above answers "outer"; `1 / 0` inside a reify at `DivisionByZero` still caught; a tuple raise refused at load naming the former.

## Changes

### 2026-10-16T17:56:10Z — feedback — claude

CORRECTION to the census above: seven in three test files, not six. Besides the six labels at a tuple, `wi_n31xx_type_value_read_rule_test`'s `raisesOpt` declares `Error[Option[T = (a: Int64, b: String)]]`, a sort holding a tuple, which has no `TypeValue` either (a sort's holds only where each type argument has one), so `raise … requires TypeValue[T = T]` refuses it too. The stage's rule covers a sort holding a former as well as a bare one; 071 §1.3 says so.

### 2026-10-24T17:56:48Z — feedback — claude

Delivered 2026-10-24 (619218f7). Proposal 071 stage (d): `Error.raise` requires `TypeValue[T = T]`, the raised error carries that dictionary (`RaisedType::Evidence`), and a boundary asks its pattern about the type it names — built only where some boundary may ask (071 open question 4, answered so). Delivers WI-20260911-3MV2C: nested boundaries at `Box[V = Int64]`/`Box[V = String]` route by the argument, `narrowR` answers "outer".

DECIDED WITH THE USER (2026-10-24), revising 071 §1.3's host-raiser sentence: a raise's type is THREADED, never read off its payload. A host operation that raises declares `requires TypeValue[T = X]` for its `Error[X]` (Int64/BigInt division, `Divisible.div`, `EuclideanDomain.mod`/`rem`, `KB.loaded`, `KB.execute`); a builtin keeps its call's channel (`Interpreter::running_builtin`), and a slot no route stamped is filled from the arguments at the raise. A load rule refuses a `@[host_implemented]` op raising a written `Error[X]` without the clause, two `Error` labels, or `Error[T = ?]` written out (the typer discharges that at a specific boundary where it refuses the bare `Error` — follow-up filed). Bare `Error` = `Error[T = ?]`: its host function's raise carries the unknown type (WI-20260910-6ARRN's), caught only by a boundary whose pattern is `?` (none until stage (e)). Raises with no operation behind them (`MatchFailed`, `RelationFloundered`, `ResolveStreamFailure` at a pull) carry constants `ErrorLayer` checks at start. `Error.raise` has no dispatch of its own: it is a builtin like `Int64.div`. Spec: kernel-language §5.4, §8.7 (approved); 071 status line.

ALSO: `HandlerAction::Rethrow` — the `Error` handler's answer that lets a raise continue (the default answers it); a handler's `Throw` is typed by the operation it performs, the `Error` handler's as unknown. A projected row's (`effects s.E`) host raise is refused (`RaiseTypeUnread`). A resolver repair: a dictionary-reading callee is not bridged on an argument still a call (`Result.reflect(Error.reify(…))` in a folded body ran on the `reify` term).

TWO /code-review ROUNDS, 30 findings. Fixed: the channel on every builtin route, lazily; bridged supplied slots; a handler's own raise typed by `Error.raise` (unsound, measured); a closure-holding payload's rethrow lost its type under the standard handler (structural compare → `Rethrow`); projected rows; bare beside written; sort-level clause; canonical payload compare; doc placement; weak rows. Refuted by measurement: a direct rule-body `keep(Error.reify(…))` (answers 7); the wrong-slot route through a spec dictionary (the dispatch hands the member its own channel). Kept, with reasons: the σ-walk limit for a call nested in a constructor argument (WI-880's, not widened); the per-`/` stamp evaluation (an op-scoped requirement's ordinary cost); `ErrorLayer`'s three dictionaries per construction.

ROWS: tests/include/wi_5cdn5_raise_carries_its_type_test.rs (15); re-pointed: wi_9wvt7_error_reify (the unreadable-payload row is now a throwing Clock handler), wi_9wvt7_reify_rule_body (a rule-body thunk raising at an open payload is refused at the raise; the generic catcher is refused at load), wi_9wvt7_review5/7, wi_n31xx (tuple thunks declare-only), wi_ym8hd (`narrowR` → "outer"), wi_2858g, wi_jpsdh, wi_0rp29. BACK-OUTS, each alone, measured: 16 parts, every one failing its rows (the header of the new file lists them).

RUNS on the final tree: rustland/scripts/test.sh 10747 passed, 0 failed; anthill-core under ANTHILL_TEST_FRESH_LOAD=1 and ANTHILL_TEST_TWO_STEP_LOAD=1 9713 passed each; scripts/families.sh holds; scaland sbt testFull 1 + 47 + 758 passed.

