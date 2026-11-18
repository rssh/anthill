## Attributes

- id: WI-20261118-GRG24-scala-bootstrap-drops-an
- created: 2026-11-18T20:22:37Z

- status: Open
- status_agent: claude
- status_at: 2026-11-18T20:22:37Z

- acceptance: cargo-test, scaland-sbt-test

- tags: scaland

## Description

SCALA BOOTSTRAP DROPS AN OPERATION'S OWN REQUIRES: the emitter (scaland/core/src/main/scala/anthill/codegen/scala/OpGen.scala, renderAbstract) reads a sort's requires into the using clause (WI-1022's evidence) and never reads Operation.requires, so a requirement an operation declares itself is silently absent from the emitted signature. MEASURED 2026-11-18 (BootstrapTest, WI-20261113-S4D63's measurement): operation sum2[X](a: X, b: X) -> X requires Additive[T = X] emits def sum2[X](a: X, b: X): X — no (using Additive[X]), so no Scala implementation of the trait can add — while a parameter typed at a spec is refused loudly (x: Additive) or emitted at the trait (x: Additive[T = P] as x: Additive[P]). Prelude operations of the shape: List.contains(l, x) requires Eq[T], Map.empty() requires Hash[T = K], Result.reflect requires TypeValue[T = P], Divisible.div requires TypeValue[T = DivisionByZero], sortedset's requires PartialEq[T]. docs/scala-forward-mapping.md says a requires is a using parameter. The named-slot twin is refused (OpGen.refuseNamedSlot, WI-840) because Bootstrap has no term-to-type path for an operation's requires goal (a conjunction of terms, which also admits value preconditions like requires neq(b, 0), WI-539); the anonymous spec goal has no refusal at all. FIX: emit (using Spec[...]) for an operation's requires goal headed by a spec the file's ScalaTypes places, or refuse it loudly as the named slot is; a value precondition stays out of the signature. ACCEPTANCE: a BootstrapTest row over sum2 asserting the emitted signature (or the refusal), the prelude emission compiling (ScalaCompile) for List.contains and Map.empty, back-out measured; scaland sbt testFull green.

