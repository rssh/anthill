## Attributes

- id: WI-20260929-9SNR2-regression-a-nested-positional
- created: 2026-09-29T16:04:17Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T16:04:17Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

REGRESSION: A NESTED POSITIONAL ARGUMENT IN AN OPERATION-LEVEL `requires` IS DROPPED. `operation needs(x: Int64) -> Int64 requires Store[State = Buf[Int64]] = x + 41`, with `Carrier provides Store[State = Buf[T = Int64]]`, is refused "requirement `Store[State = Buf[]]` cannot be supplied … its carrier is `Buf[]`, a STRUCTURAL FORMER" — the positional `Int64` is gone — where the Sep 20 build (593e64f5) ran it and printed 42. The named spelling `Buf[T = Int64]` works. FOUND by WI-20260924-F3FYJ's review (a side note of verifier V3); MEASURED independent of F3FYJ — a build with every F3FYJ part backed out refuses it identically — and the op-requires path (the parser's `convert_term` / `convert_type_value`, then the loader's term lowering) never reaches `assemble_binding_value`. The introducing commit lies between 593e64f5 and HEAD and is not yet bisected. ACCEPTANCE: the positional spelling loads and runs like the named one, pinned by a row that fails with the fix backed out; full workspace green via rustland/scripts/test.sh.

