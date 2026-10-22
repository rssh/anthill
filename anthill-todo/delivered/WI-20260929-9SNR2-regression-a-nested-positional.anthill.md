## Attributes

- id: WI-20260929-9SNR2-regression-a-nested-positional
- created: 2026-09-29T16:04:17Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-22T17:42:17Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

REGRESSION: A NESTED POSITIONAL ARGUMENT IN AN OPERATION-LEVEL `requires` IS DROPPED. `operation needs(x: Int64) -> Int64 requires Store[State = Buf[Int64]] = x + 41`, with `Carrier provides Store[State = Buf[T = Int64]]`, is refused "requirement `Store[State = Buf[]]` cannot be supplied … its carrier is `Buf[]`, a STRUCTURAL FORMER" — the positional `Int64` is gone — where the Sep 20 build (593e64f5) ran it and printed 42. The named spelling `Buf[T = Int64]` works. FOUND by WI-20260924-F3FYJ's review (a side note of verifier V3); MEASURED independent of F3FYJ — a build with every F3FYJ part backed out refuses it identically — and the op-requires path (the parser's `convert_term` / `convert_type_value`, then the loader's term lowering) never reaches `assemble_binding_value`. The introducing commit lies between 593e64f5 and HEAD and is not yet bisected. ACCEPTANCE: the positional spelling loads and runs like the named one, pinned by a row that fails with the fix backed out; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-10-22T17:42:16Z — feedback — user

DELIVERED (0873dca1). REPRODUCED first on 586f1733, where the ticket's literal program already printed 42 — only because its body never reads the requirement: with the body calling through it (`Store.peek(buf(v: x)) + 41`) the requirement was `Store[State = Buf[]]`, loaded, and died at run time ('the argument types pin `Store[State = Buf[]]`'); `requires Store[State = Buf[String]]`, which no provision covers, loaded clean where `Buf[T = String]` is refused. The same drop in a named slot (`requires s: Store[…]`) and in `ensures` (`ensures KVStore[C, K = String, V = Buf[Int64]]` refused against a provider at `V = Buf[T = Int64]`, printed `V = Buf(Int64)`). Read the positional before as after: a sort's `requires`, a call's bracket, a rule body's `require[…]`, a rule head's bound. CAUSE: `convert_term_inner` normalized a nested bracket (`normalize_type_args`, cef5913b) only in a clause's data slot; a contract clause converts with const folding off. FIX: it normalizes wherever the walk builds the application, but in a rule head's bound (its own reader) and a quoted `Term` field; an operation body and a `@[simp]` equation, also reached, read the positional alike before and after (measured). No spec change: §5.1 already binds a positional to the next declared parameter. Tests: wi_9snr2_contract_clause_positional_test (12 rows; 9 fail with the fix backed out, 3 pass either way by design). /code-review (xhigh): 3 findings, fixed. Full workspace green via rustland/scripts/test.sh (10409 passed, 17 ignored); scaland sbt testFull green (714 + 47 + 1); families: no verdict moved. NOT BISECTED: the Sep 20 build ran the literal program, which does not read the requirement, so it does not show that build read the positional.

