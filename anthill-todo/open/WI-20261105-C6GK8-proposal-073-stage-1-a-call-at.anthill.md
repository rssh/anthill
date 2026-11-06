## Attributes

- id: WI-20261105-C6GK8-proposal-073-stage-1-a-call-at
- created: 2026-11-05T22:17:34Z

- status: Open
- status_agent: claude
- status_at: 2026-11-05T22:17:34Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-073

## Description

PROPOSAL 073 STAGE 1 — A CALL AT A TYPE THE PROGRAM KNOWS IS DECIDED AT LOAD, through any chain of provisions (docs/proposals/073-abstract-values-are-instances.md §1). `add(1, n)` at `n: Int64` is `Int64.add`, reached through `Numeric provides Additive[T = T]`. Today the typer leaves `Additive.add` unclassified there — the transitive-provision arm of the spec-operation dispatch (WI-496, kb/typing/apply.rs) defers it — and the interpreter finds `Int64.add` from the value `1` (`dispatch_resolved_operation` step 3b in eval/eval.rs, and its host-entry copy in eval/mod.rs). The abstract-spec carrier arm (WI-598) defers in the same place. MEASURED on 62882ef0 with a trace at each value-directed step over the full workspace: 1,527 of 11,714 tests reach step 3b, most of them `Additive.add` / `Multiplicative.mul` at `Int64` (`List.length`'s `add(1, length(xs))`) and `Stream.splitFirst` in `Stream`'s default bodies (that part is stage 3's). WHAT: both arms go, and such a call is classified at load — pinned, or applied within the dictionary the provisions build. After this stage step 3b serves only calls at an abstract type, which stage 3 removes. ACCEPTANCE: rows driving such calls to their values — `List.length([1, 2, 3])` in an operation body and from a rule, a `Multiplicative.mul` at `Int64`, a call reached through a two-step provision chain of a program's own sorts — each asserting the call is decided at load and failing with its arm backed out; the step-3b census run again, listing only calls at an abstract type; full workspace green via rustland/scripts/test.sh; families green on both carriers.

