## Attributes

- id: WI-20260821-WDCV3-a-requires-loop-is-not
- created: 2026-08-21T11:23:17Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T11:23:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `requires` LOOP IS NOT DETECTED. Spec inheritance cannot be circular, and every
circular shape loads clean today.

MEASURED (rustland, current tree), all three LOAD with no diagnostic:
  * `sort A requires rl.B` beside `sort B requires rl.A`, each with its own operation.
  * `sort A requires rl2.A` -- a spec requiring ITSELF.
  * `sort A requires rl3.B`, `sort B requires rl3.C`, `sort C requires rl3.A`.

WHY IT IS AN ERROR AND NOT A SHAPE. `requires` names a SPEC the sort must satisfy, and
the parent link it creates is what a member of the requiring sort resolves THROUGH. A
cycle says each of two sorts is defined in terms of the other, so neither has a
grounded dispatch surface; `dict_layout` bundles the spec's chain then the provider's
over the whole knowledge base (WI-857), and a chain with a loop has no fixpoint the
layout can name. Compare `import`, where a loop is LEGITIMATE and must keep working:
two modules importing each other is ordinary, and nothing about it claims one is
defined in terms of the other.

DETECTION IS CHEAP AND HAS AN OWNER ALREADY. Sub-pass 2 builds the `requires` parent
links (`wire_provides_scope_parent` / the `requires` arm of the import pass), so the
edge set is complete at the end of that pass and a DFS over `is_enclosing == false`
`requires` edges answers it before anything resolves. The self-requires case needs no
walk at all.

WHAT IT UNBLOCKS. WI-980 refuses a rule head whose name no scope introduces, which
happens when two scopes can each SEE the other and both write it. Mutual visibility has
exactly two sources: mutual wildcard imports (legitimate) and mutual `requires` (this
ticket). Closing this one leaves WI-980's refusal describing only the import case, so
its diagnostic can name a cause instead of hedging -- today it says "Mutual wildcard
imports do this" over a program containing no import at all, MEASURED on the mutual-
`requires` pair.

ACCEPTANCE: each of the three shapes above is a located load error naming the cycle's
members; a `requires` CHAIN with no loop still loads and still resolves through
(control); mutual `import` still loads (control -- it is not this rule). cargo-test
green via rustland/scripts/test.sh.

