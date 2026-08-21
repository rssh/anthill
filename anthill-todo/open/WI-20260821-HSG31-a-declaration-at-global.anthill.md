## Attributes

- id: WI-20260821-HSG31-a-declaration-at-global
- created: 2026-08-21T11:25:02Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T11:25:02Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DECLARATION AT `<global>` ABSORBS A NAMESPACE'S RULE-INTRODUCED PREDICATE. WI-980
closed this for a rule HEAD written there and not for any other kind of name, so the
same harm is one respelling away.

MEASURED (rustland, current tree), the same one-line file in two spellings:
  * `rule modus_ponens(7, 8)` in a file with no namespace
      -> `anthill.logic.Constructive.Constructive.modus_ponens` = 1 clause (INTACT),
         `<global>.modus_ponens` = 1 clause. Two predicates, no capture. This is what
         WI-980 delivers.
  * `operation modus_ponens(a: Int64, b: Int64) -> Int64 = 1` in a file with no namespace
      -> `anthill.logic.Constructive.Constructive.modus_ponens` STOPS RESOLVING and the
         stdlib axiom's clause lands on the user's global predicate. Loads clean.
  * A `sort` at `<global>` does it too: `sort zqop entity zq(n: Int64) end` beside
    `namespace zdemo { rule zqop(2, 7) }` -> `zdemo.zqop` = None.

WHY THE TWO SPELLINGS DIVERGE. WI-980's rule is "`<global>` may OWN a name written at
it, and is never YIELDED TO", and it lives as one guard inside `Ownership`'s overlay
(`s != self.global`), which governs rule-head-introduced names alone. The head's OTHER
question -- `name_denotes_for_rule_head`, phase 2, the ordinary ladder -- runs FIRST,
short-circuits on a hit, and has no `<global>` rule at all. A DECLARED name at
`<global>` is on that ladder from pass 1, so a namespace's head resolves to it and
becomes a clause of it.

IT FALSIFIES A SENTENCE THE SPEC NOW CARRIES. docs/kernel-language.md §"A rule head
functor is resolved, not declared" says "a head written *inside* a namespace never
yields to it, so a name at `<global>` cannot absorb one". True for a rule head at
`<global>`; false for a declaration at `<global>`. Either the rule widens to every
name kind or that sentence has to say which kind it is about.

THE DECISION THIS NEEDS. `<global>` is the one scope nobody opts into, which is the
whole argument for the rule -- and that argument is about the SCOPE, not about how the
name got there. So the guard probably belongs on the ladder rather than in `Ownership`:
a head written inside a namespace does not yield to ANY name whose only home is
`<global>`. That is a wider change than WI-980 made and wants its own measurement --
notably against `wi754`'s top-level fixtures and anything relying on a top-level
declaration being reachable from inside a namespace.

WATCH FOR: the reverse direction must keep working -- a namespace-less program is the
language's own documented first form (kernel-language.md's `**Forms:**` block,
examples/classic-mini/ancestor), so a top-level declaration must still be usable by the
top-level code around it.

STAGED LOADS ARE A SECOND CHANNEL, same root: `load_incremental` decides each batch
against a partial program, so batch 1's `rule zq(0)` at `<global>` mints, and batch 2's
`namespace zq1 { rule zq(1) }` sees it through the ordinary ladder and yields --
`zq1.zq` never exists. One-shot `load_all` over the same two files keeps them separate.

ACCEPTANCE: the two one-line spellings above must agree -- a stdlib predicate survives a
namespace-less user file whichever kind of name it declares. Drive the goals, assert the
qualified names resolve, and keep the documented top-level form loading as a control.
cargo-test green via rustland/scripts/test.sh.

