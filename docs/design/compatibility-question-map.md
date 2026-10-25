# May a value of type A stand where B is expected — the readers of one question

## Status: measurement, 2026-10-25, on `d6a28558`; unchanged, every one of its 153 programs, on `1373e04f`. The second map of "one answer per question" (`docs/process/converging.md` §3.10, q18), after `supplier-question-map.md`. Tracked by WI-20261025-27050 (C2, C5, C6); guarded by the family `g-compatibility`. Nothing here is implemented.

## The question

*Is A compatible with B* — the subtype relation, asked wherever a value meets a type.
`docs/kernel-language.md` states it in several places: a constructor is below its sort, one
level (§8.2); a spec whose operations receive on itself admits its providers (`List` is a
`Stream`), and a spec over a parameter does not (a `B` that provides `Tagger[C = B]` is no
`Tagger`), "wherever a type is written for a value" (§8.2); a `requires` clause refines; a slot
left out is open; an alias is its expansion; tuples subtype by name, width and permutation
included, while order is their identity (§4.5); an arrow is `Function[A, B, E]`; `List`,
`Option`, `Stream` and `Pair.A` are declared covariant and `Permission` contravariant
(`stdlib/anthill/reflect/typing.anthill`).

Provision lookup asks a related question, and for tuples and arrows a different one on
purpose (§5.2, "A binding that is an arrow or a tuple is compared by its parts"): a tuple with a
component more "is another binding than the narrower one, though it conforms to it as a type",
an arrow's parameters must be the provision's and its rows the same row.

## The matrix

One program per (pair, position), 153 in all (`compatibility-question-map/gen.py`). The value
always comes from `mkA() -> A`, so its static type is A and no constructor is classified at the
expectation (§8.2, *Which sort a constructor application is classified at*). The positions:
an operation's argument, an annotated `let`, a return, an entity field, a list element, a lambda's
argument, a provision at B answering `Desc.d(mkA())`, and the run-time `type_admits(B, A)`. A bold
cell contradicts the spec.

| A at B | §8 says | argument | let | return | field | list-element | lambda-argument | provision | type-admits |
|---|---|---|---|---|---|---|---|---|---|
| variant-to-sort | yes | yes | yes | yes | yes | yes | yes | yes | — ² |
| sort-to-variant | no | no | no | no | no | no | no | no | — ² |
| sibling-variant | no | no | no | no | no | no | no | no | — ² |
| self-carrier | yes | yes | yes | yes | yes | yes | yes | yes | **no** |
| param-spec | no | no | no | no | no | no | no | **yes** | no |
| refinement | yes | yes | yes | yes | yes | yes | yes | **no** | yes |
| refinement-other-args | no | **yes** | **yes** | **yes** | **yes** | **yes** | **yes** | no | no |
| open-slot | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| slot-mismatch | no | no | no | no | no | no | no | **yes** | no |
| alias | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| alias-reverse | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| tuple-width | yes | yes | yes | yes | yes | yes | yes | no ¹ | |
| tuple-permutation | yes | yes | yes | yes | yes | yes | yes | no ¹ | |
| tuple-order | no | no | no | no | no | no | no | no | |
| covariant-list | yes | yes | yes | yes | yes | yes | yes | yes | yes |
| no-variance-fact | ? | no | no | no | no | no | no | yes ³ | no |
| arrow-parameter-wider | yes | yes | yes | yes | yes | yes | yes | no ¹ | |
| arrow-parameter-narrower | no | no | no | no | no | no | no | no | |
| arrow-fewer-effects | yes | yes | yes | yes | yes | yes | yes | no ¹ | |
| arrow-more-effects | no | no | no | no | no | no | no | no | |

¹ Provision lookup's own rule for tuples and arrows (§5.2), as the spec states it.
² A variant's type written bare as a value (`Colour.red`) reads as a construction with no field;
the matrix has no spelling for it. Tuples and arrows are not asked of `type_admits`, which leaves
them unjudged by design.
³ `Box` declares no variance, and every typing position reads it as invariant; provision lookup
reads the whole head covariantly — the question of WI-20261017-DYX5E (PreOpened).

`refinement`: `sort Narrow { requires Wide[W = Int64]; entity narrow }`, with `WP provides
Wide[W = Int64]`; `refinement-other-args` asks `Narrow` at `Wide[W = String]`.

## What it says

**The typer's six positions are one answer.** Every row agrees across argument, `let`, return,
field, list element and lambda argument; the one wrong row is wrong in all six alike
(`refinement-other-args`, WI-20261020-G37HS: the typer's refinement through `requires` ignores
the clause's arguments).

**The two other readers disagree with it, each in its own way.**

- **Provision lookup** (`match_candidate_against_goal`):
  - **C2 — a provision at a spec over a parameter answers its provider.** A provision at `Tagger`
    answers `Desc.d(mkA())` at `Bk`, where `Bk provides Tagger[C = Bk]`, and its member `d(x:
    Tagger)` receives a value §8.2 says is no `Tagger` — a rule that holds for "a member that
    backs a spec operation" by name. No open ticket.
  - **C3 — type arguments are not compared.** A provision at `Box[V = String]` answers a call at
    `Box[V = Int64]`: WI-20260929-05ZQE. A provision at `Box[V = Colour]` answers one at `Box[V =
    Colour.red]`: DYX5E (³).
  - **C6 — a `requires` refinement with written arguments is not climbed.** A provision at
    `Wide[W = Int64]` does not answer a call at a `Dog` that `requires Wide[W = Int64]`; a provision
    at bare `Wide` does (15), and so does one at a parameterless `Animal` for `Dog requires
    Animal`. It is G37HS seen from the other side — the clause's arguments dropped, here so that
    the instance the clause gives no longer matches. No open ticket.
- **`type_admits`** (`type_pattern_admits`):
  - **C5 — no provider leg.** `type_admits(Stream[T = Int64, E = {}], List[T = Int64])` is false
    where every typing position admits a `List` at that `Stream`. The module header records the
    leg as left out because "the run-time boundary never read it". Decided by the user on
    2026-10-25: a boundary at `Stream` catches a raised `List` ("If we want catch Stream … we should
    catch List"), as §8.2's "a `List` is a `Stream`" reads. Today it is refused before it runs —
    the typer's label discharge reads the same relation:

    ```anthill
    operation boom() -> Int64 effects {Error[List[T = Int64]]} = Error.raise([1, 2])
    operation caught() -> Int64 =
      match Error.reify[T1 = Stream[T = Int64, E = {}]](lambda () -> boom())
        case Result.ok(v) -> v
        case Result.err(e) -> 7
    ```

    is "the closed row does not admit `Error[T = List[T = Int64]]`"; at `T1 = List[T = Int64]` it
    prints 7.
  - It is right where the typer is wrong: `Narrow` at `Wide[W = String]` is 0.

## The readers

| reader | where | what it is for | its rule |
|---|---|---|---|
| `types_compatible` | `kb/typing/subtype.rs:49` | the typer's subtype test; 76 call sites in 16 files | directional; two bodies by carrier — `types_compatible_term_dispatch` (hash-consed) and `types_compatible_view_structural` — held together by the node-carrier control |
| `unify_types` | `kb/typing/unify.rs:175` | identity with binding; 74 call sites in 23 files | symmetric |
| `match_candidate_against_goal` | `kb/typing/candidates.rs:1116` (432 lines) | provision lookup and ranking (`head_answers_at`, `candidates.rs:2200`) | its own: calls neither of the two above; covariant on the whole head; tuples and arrows by their parts (§5.4) |
| `type_pattern_admits` | `kb/typing/type_pattern.rs:124` (module 781 lines) | `TypePattern.admits` at run time, and the typer's `Error`-label discharge (071 stage e) | its own, pure and bounded by design ("a full `types_compatible` descent once overflowed the stack"); nominal head by `sort_sym_compatible`, arguments by declared variance, refinement by `instances_through_requires`; no provider leg |
| `sort_sym_compatible` | `kb/typing/subtype.rs:2267` | the head climb both the typer and `type_pattern_admits` read | itself, an entity's sort, what it refines through `requires` |
| `bare_sort_compatible` | `kb/typing/subtype.rs:2178` | the typer's head test | `sort_sym_compatible` plus the provider leg |

So the subtype relation has three implementations: the typer's, provision lookup's and the type
pattern's, sharing the head climb and nothing below it. Unlike the supplier question, the typer's
own positions do not disagree — the consolidation this question asks for is of the other two
into the typer's relation, where the spec gives them the same one, and only there: provision
lookup keeps its own rule for tuples and arrows, which the spec states, and its variance is
DYX5E's open question.

## The family

`g-compatibility` (`rustland/anthill-core/tests/families/compatibility.rs`, 150 programs,
`scripts/families.sh g`) is this matrix less the CLI: the six typing positions, the provision at
a sort-headed pair and `type_admits` are one question; at a tuple or an arrow the provision is an
option of its own, held to §5.2's rule. Its judge reads an answer as admitted or not. Its
exceptions are C2, C5 and C6 under WI-20261025-27050, and the known rows under G37HS, 05ZQE and
DYX5E; run without them it names exactly those programs. Green on both carriers.

## Reproduce

From the repository root, with `rustland/target/debug/anthill` built (the judge is the supplier
map's):

```bash
python3 docs/design/compatibility-question-map/gen.py /tmp/compat/progs
cut -f1,5 /tmp/compat/progs/manifest.tsv | xargs -P 12 -n 2 sh -c 'docs/design/supplier-question-map/judge.sh /tmp/compat/progs $0 $1' > /tmp/compat/verdicts.tsv
python3 docs/design/compatibility-question-map/table.py /tmp/compat
```
