## Attributes

- id: WI-20261025-27050-provision-lookup-and-type
- created: 2026-10-25T12:11:25Z

- status: Open
- status_agent: claude
- status_at: 2026-10-25T12:11:25Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

PROVISION LOOKUP AND TYPE PATTERNS ANSWER "MAY A STAND WHERE B IS EXPECTED" WITH THE TYPER'S RELATION, WHERE THE SPEC GIVES THEM THE SAME ONE — the subtype relation has three implementations (the typer's `types_compatible`, provision lookup's `match_candidate_against_goal`, the type pattern's `type_pattern_admits`), and the compatibility matrix (docs/design/compatibility-question-map.md, 153 programs, measured 2026-10-25 on d6a28558 and unchanged on 1373e04f) has the typer's six positions agreeing on every pair while the other two disagree with it in three rows of their own.

  C2 — a provision at a spec over a parameter answers its provider. `sort W provides Desc[T = Tagger]` with `operation d(x: Tagger) -> Int64 = 5` answers `Desc.d(mkA())` at `mkA() -> Bk`, `Bk provides Tagger[C = Bk]`: runs 5, and the member receives a value kernel-language §8.2 says is no `Tagger` ("wherever a type is written for a value … a member that backs a spec operation"); every typing position refuses a `Bk` at `Tagger`.
  C6 — a `requires` refinement with written arguments is not climbed. With `sort Dog { requires Wide[W = Int64]; entity rex }`, a provision at `Wide[W = Int64]` does not answer `Desc.d(rex)` ("Dog provides no Desc"), while one at bare `Wide` does (and one at a parameterless `Animal` for `Dog requires Animal`). The typer admits a `Dog` at `Wide[W = Int64]` in every position; the clause's arguments are dropped on the way up (WI-20261020-G37HS is the same drop on the typer's side, the other way: it admits `Wide[W = String]`).
  C5 — a type pattern has no provider leg (user, 2026-10-25: "If we want catch Stream … we should catch List"). `type_admits(Stream[T = Int64, E = {}], List[T = Int64])` is false, and `Error.reify[T1 = Stream[T = Int64, E = {}]](lambda () -> boom())` over `boom() effects {Error[List[T = Int64]]}` is refused at load (the label discharge: "the closed row does not admit Error[T = List[T = Int64]]"); at `T1 = List[T = Int64]` it catches (7). §8.2: "a `List` is a `Stream`". `type_pattern.rs`'s header records the leg as left out because "the run-time boundary never read it" — that reason is retired by this decision. Both readers change: the label discharge at load and the boundary's `TypePattern.admits` at run time.

THE READING TO HOLD (§8.2, provider admissibility): a pattern or a provision head at a spec admits a provider where the typer does — a spec whose operations receive on itself is its providers' (`List` at `Stream`), a spec over a parameter is not (`Bk` at `Tagger`). Where the spec gives provision lookup a rule of its own it keeps it: a tuple or an arrow binding is compared by its parts (§5.2, "a tuple with a component more is another binding … though it conforms to it as a type"), and variance in a provision head is WI-20261017-DYX5E's question. Type arguments in a provision head are WI-20260929-05ZQE's.

WHAT. Provision lookup's head match and `type_pattern_admits`' head and argument legs ask the typer's relation for a sort-headed type — one predicate, carrier-neutral, that the typer's positions already agree on — and the type pattern keeps what it was built for (pure, bounded, an error for what it does not judge). Not by adding a provider leg to each reader: by each reading the one the typer reads.

ACCEPTANCE: the generated family `g-compatibility` (rustland/anthill-core/tests/families/compatibility.rs): the exceptions it lists under this ticket cleared — C2's provision admitted nowhere a typed position refuses, C6's provision answering where the typed positions admit, C5's `type_admits` answering what they answer — and no other verdict moved; the `Stream` boundary above catches a raised `List` (a row, both at load and at run time); the full gate green; the families green on both carriers.

