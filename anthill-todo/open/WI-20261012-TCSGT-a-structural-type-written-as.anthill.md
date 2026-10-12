## Attributes

- id: WI-20261012-TCSGT-a-structural-type-written-as
- created: 2026-10-12T06:16:03Z

- status: Open
- status_agent: claude
- status_at: 2026-10-12T06:16:03Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

A STRUCTURAL TYPE WRITTEN AS AN ENTRY OF A BRACKET IN A TERM IS READ AS A NAME SPELLED WITH ITS TEXT — over `sort Box[V] { operation tag() -> Int64 = 7 }` and `operation nm(t: Type) -> Int64 = 1`, in an operation body `nm(Box[V = (Int64) -> Int64])`, `nm(Box[V = () -> Int64])`, `nm(Box[V = (a: Int64, b: Int64)])`, `nm(Box[V = (Int64, String)])`, the nested `nm(Box[V = Box[V = (Int64) -> Int64]])`, `let t = Box[V = (Int64) -> Int64]`, the result `operation ty() -> Type = Box[V = (Int64) -> Int64]` and the receiver `(Box[V = (Int64) -> Int64]).tag()` are refused with "unresolved name '(Int64) -> Int64' in scope …" and "type mismatch in (Int64) -> Int64.name: expected resolved name, got unresolved". So are a fact and a rule's data slot — `fact holds(Box[V = (Int64) -> Int64])` and the goal `holds(Box[V = (Int64) -> Int64])` — and in a rule body the receiver, `?x <=> (Box[V = (Int64) -> Int64]).tag()`, which adds "has an argument that names no type here". The written companion call `Box[V = (Int64) -> Int64].tag()` answers 7 in both bodies, its bracket being lowered as a type, and a nominal entry answers: `nm(Box[V = anthill.prelude.Function[A = Int64, B = Int64]])` is 1. Measured 2026-10-12 on 711c2289; found with WI-20261008-A3FY2.

WHY. A bracket written in a term position is converted by `convert_type_value` (parse/convert.rs), whose last arm reads: other shapes — "function calls, tuples, arrows" — "collapse to `Ref(Name)`". The entry becomes a reference to a symbol named with the type's source text. An effect row went the same way (`Ref("{}")`) until WI-366 B1 carried its `TypeExpr` through `ParseAux` for the loader to lower; a tuple type and an arrow type were left on the default arm. Proposal 055 §5 keeps a structural type from being classified implicitly as a value, its surface being a value's too, but an entry of a nominal type's bracket is a type position and nothing else can stand there. The reifier 055 gives a structural type standing alone, `type_value[…]()`, is umbrella C's (WI-20260823-Z9HJ2) and is not delivered: `type_value[(Int64) -> Int64]()` is refused today.

WHAT. Carry a tuple type and an arrow type written as a bracket's entry as the type they are — the effect row's route is the precedent — and lower them where each walk meets the entry: the term walk (a fact, a rule's head and data slot), the rule-body occurrence walk, and the operation-body walk, whose `Term::ParseAux` arm takes an effect row only. The type value's typing and its denoted type (`type_value_denoted_type`) then read the entry as they read a nominal one. Check how a type holding such an entry is compared where it is matched as data; WI-20260929-12NKG is about that comparison under an arrow.

CONTROL. One fixture per row: an arrow, a nullary arrow, a named tuple and a positional tuple, each as an argument at a `Type` parameter (evaluated, the value asserted), in a `let`, as a result, in a parenthesized receiver in both bodies beside the written companion call, one bracket down, and in a fact matched by a goal. Fences: an effect-row entry, a nominal entry, a variable entry, a constant entry (`Vec[Int64, 3]`). Say which rows fail with the change backed out.

DONE WHEN: a bracket holding a structural type is one type value in every position above, and its parenthesized receiver answers as its companion call does; the gate is green.

