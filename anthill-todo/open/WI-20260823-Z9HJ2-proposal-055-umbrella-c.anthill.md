## Attributes

- id: WI-20260823-Z9HJ2-proposal-055-umbrella-c
- created: 2026-08-23T09:40:05Z

- status: Open
- status_agent: user
- status_at: 2026-08-23T09:40:05Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260823-ZF3AK-proposal-055-umbrella-a

- tags: proposal-055

## Description

Proposal 055 umbrella C — COMPLETE THE PUBLIC TYPE-REFLECTION AND PROFILE BOUNDARY. Implement proposal 055 §§3, 5, 8 plus docs/design/055-implementation.md §5 after umbrella A: add/complete type_value[T]() now that WI-708 is delivered; require it for structural tuple and arrow type values whose surfaces overlap value syntax, while nominal type values remain implicit; move the Type cluster from anthill.prelude to anthill.reflect and update engine/scaland references; consolidate and document extract/term_as_sort peers; add an early full-versus-compile-only profile fence so reflect-less generated targets reject runtime Type signatures or reflect calls with a profile diagnostic rather than an incidental missing mapping; add the -> T [Meta] redirect diagnostic; update docs/kernel-language.md. ACCEPTANCE: a generic body's type_value[T]() substitutes per call; tuple and arrow type reifiers evaluate to canonical Type values; structural type syntax without the reifier is loudly redirected; nominal implicit controls stay accepted; reflect-capable execution succeeds while a reflect-less target refuses at the specified boundary; no stale anthill.prelude.Type references; tests identify back-out failures and controls; full workspace via rustland/scripts/test.sh. This is an umbrella and may be split along namespace/reifier/profile seams while retaining the combined public-boundary acceptance.
