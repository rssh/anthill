## Attributes

- id: WI-20261109-P07E8-proposal-051-phase-2-1-of-4
- created: 2026-11-09T14:15:03Z

- status: Open
- status_agent: claude
- status_at: 2026-11-09T14:15:03Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-051

## Description

PROPOSAL 051 PHASE 2 (1 of 4) — THE STRUCTURAL BUILTINS: `===` UNDER ITS OWN NAME, AND `!==` (docs/proposals/051-structural-vs-semantic-equality.md; decided with the user 2026-11-09: WI-616 left this half done — it moved the stdlib's `neq` off the structural `BuiltinTag::Neq`, deleted that tag as dead (2eeb519b), and left `===` on the structural handler under the old name, so it is completing that change, not a language feature). TODAY: `anthill.kernel.struct_eq` (`===`) is registered as `BuiltinTag::Eq` (kb/mod.rs `register_builtin_tags`), answered by `builtin_eq` (kb/resolve.rs), while the interpreter's twin is `builtin_struct_eq`; a structural inequality is written `not(a === b)`, and 051 lists a `!==` glyph as a non-goal. WANTED: (1) `BuiltinTag::Eq` -> `BuiltinTag::StructEq`, the resolver's `builtin_eq` -> `builtin_struct_eq`; (2) `!==` = `anthill.kernel.struct_neq`, declared beside `struct_eq` as `operation struct_neq[T](a: T, b: T) -> Bool @[host_implemented]`, a resolver builtin `StructNeq` and an interpreter builtin; one token lexed greedy-longest before `!=`, as `===` before `=` (tree-sitter grammar.js, parse::pratt EQUALITY_FAMILY_FUNCTORS, scaland Pratt.scala), priority 3, no associativity, origin `anthill.kernel`; it answers the negation wherever `===` decides and is UNDECIDED wherever `===` delays (`?x !== 1` with `?x` unbound never succeeds by a test that did not finish); it takes `===`'s two rules — a bodyless `!==` head (rule or fact) is refused at load naming `<=>` (WI-1090's refusal), and a namespace declaring its own `struct_neq` does not capture the operator. SPEC: kernel-language §6.6's operator table and the structural/semantic equality table gain the row; 051's non-goal line is amended; the text agreed with the user before it is written. ACCEPTANCE: rows driving `!==` in a rule body, an operation body and a query (ground pair equal and unequal, a nan pair: `nan !== nan` is false, `===` being structural), the delayed operand undecided, the head refusal, the non-capture; each part backed out alone failing the rows its header names; full workspace green via rustland/scripts/test.sh; families green on both carriers; scaland testFull green.

