## Attributes

- id: WI-20261003-QV5W5-implement-proposal-069
- created: 2026-10-03T10:06:09Z

- status: Open
- status_agent: user
- status_at: 2026-10-03T10:06:09Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-069

## Description

Implement proposal 069 declaration-site defaults end to end. Add operation value-parameter defaults, entity-constructor field defaults in construction positions only, explicit operation type-parameter defaults, and sort/effect-row parameter defaults in Rust, Scala, and tree-sitter. Type inference must solve without defaults first, install defaults once for omitted still-free parameters in declaration order, then resume solving before validation; explicit ? suppresses a default. Resolve the kernel-language 4.4/8.1 contradiction by declaring Function.E default {}, while Function[A, B, ?] stays open. Preserve full runtime arity, make spec declarations own operation defaults, reflect and persist defaults, replace WI-850 refusal tests with driven controls, and cover dependent defaults, wrong kinds, forward references, constructor expression versus pattern omission, function-value full arity, and Function purity. Acceptance: rustland/scripts/test.sh passes, scaland sbt testFull passes with the expected full test count, and npx tree-sitter test passes.

