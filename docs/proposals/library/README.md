# Library proposals

This directory holds **stdlib-library design proposals** — collection sorts, abstract typeclasses, container algebras, and other library-level constructs that live in `stdlib/anthill/` and that downstream code depends on.

Library proposals are distinct from **kernel-language proposals** (in the parent `docs/proposals/` directory), which propose changes to the language itself — syntax, type system, effect machinery, evaluator semantics. A kernel proposal extends what anthill *is*; a library proposal extends what anthill *gives you out of the box*.

## Conventions

- **Filenames** are digit-prefixed (`001-map.md`, `002-list.md`, …) with a descriptive slug after the number. The number sequence is local to this directory — it runs independently of the kernel-proposal sequence in the parent directory, so library `001` and kernel `001` are unrelated.
- **Structure** mirrors the kernel proposals: §Status, §Motivation, §Design, §Migration / phasing, §Interaction with other proposals, §Open questions, §Phasing.
- **Cross-references** to kernel proposals use the parent-directory path (e.g. `[027.1-alloc-effect](../027.1-alloc-effect-and-allocator-revision.md)`).
- **Implementation status** is tracked in workitems (`anthill-todo/workitems.anthill`) under the relevant WI; the proposal documents the *design*, not the progress.

## Current proposals

| File | Status | Subject |
|---|---|---|
| [`001-map.md`](001-map.md) | Draft 2026-05-28 | Split `Map` into three sorts: `MapReadable` (typeclass for read-only ops), `PersistentMap` (functional update), `MutableMap` (in-place mutation per 027.1). Effect-polymorphic iteration via `Stream[T, E]`. |
| [`002-iteration-collection.md`](002-iteration-collection.md) | Draft 2026-05-29 | The same split for sequences: `Iteration` (consume) + new shared `Iterable` (produce, `iterator -> Stream`) as the read layer; `PersistentCollection` (rename of `Collection`) and new `MutableCollection` both `requires Iterable`. Map is the keyed instance. |
| [`003-finite-collection.md`](003-finite-collection.md) | Draft 2026-06-29 | Finiteness as a type. Eager consumers (`count`→`size`, `collect`, `foldLeft`, `foldRight`) diverge on infinite streams; move them off `Stream`/`Iterable` onto new `FiniteCollection` (consume capability), with new `FiniteStream` (a `Stream` whose tail is finite) so a lazy `map`/`filter` over a finite source stays consumable. |
| [`004-partial-vs-total-equality-and-ordering.md`](004-partial-vs-total-equality-and-ordering.md) | Draft 2026-07-06 | Split the conflated `Eq` into `PartialEq` (partial — `eq`/`neq`; `Float` provides, IEEE) + `Eq` (requires `PartialEq` + a **checked** reflexivity law; `Float` does not provide), and `Ordered` into `PartialOrd`/`Ord`. Makes `requires Eq[T]` non-vacuous and closes the interpreter↔codegen Float-`NaN` soundness gap. Driver WI-644. |

## Candidate / planned proposals

These follow naturally from `001-map.md` and other in-flight work. Each is a separate proposal when the time comes; this section is the holding pen so the design space is visible without scattered TODOs.

| Slug | Subject | Driver |
|---|---|---|
| `list.md` | `ListReadable` / `PersistentList` / `MutableList` split. Persistent list is already the stdlib shape (`anthill.prelude.List` with `nil` / `cons`); mutable variant is the gap. | Same template as Map. Pattern validation across containers — once Map lands, the template is known good. |
| `set.md` | `SetReadable` / `PersistentSet` / `MutableSet` split. | Set semantics differ from Map only in dropping the V parameter; otherwise identical. Cheap follow-up after Map. |
| `vector.md` or `indexed-seq.md` | Indexable random-access sequences. `IndexedSeqReadable[T]` with `nth` / `slice`; `PersistentVector[T]` (RRB-tree); `MutableVector[T]` (resizable array). | `stdlib/anthill/prelude/indexed_seq.anthill` already exists with the Readable shape — needs the persistent and mutable concrete sorts. |
| `numeric-tower.md` | Int64 / BigInt / Float / Rational relationships, conversion operations, when `+` widens vs errors, the `Numeric` / `Ordered` / `Field` algebra layering. | Currently fragmented across `int.anthill`, `bigint.anthill`, `float.anthill`. No single document explains the tower. Drivers: webots-modelling (float arithmetic for proofs), simp-rewrite (rewriting numeric expressions). |
| `error-handling.md` | `Result[T, E]` vs `Option[T]` vs the `Error` effect — when each is the right shape, what the conversion operations look like, how `Result` interacts with the `Error[E]` effect's typed variant. | Today's stdlib has `Option`, the `Error` effect, and ad-hoc `Result` mentions; the conventions for choosing between them are folklore. |
| `string.md` | String algebra — concatenation laws, substring, char-vs-byte semantics, UTF-8 commitments, format operations. | `string.anthill` exists with primitive ops; deeper algebra (regex, split, join, format) is missing or scattered. |
| `time-and-duration.md` | `Instant`, `Duration`, `Clock` sorts; arithmetic; effects for reading the current time. | Currently absent from stdlib. Needed for any real-world application; today's examples reach into host APIs. |

## Naming conventions for split sorts

When a library proposal splits a container into readable + persistent + mutable variants, the convention from `001-map.md` applies:

- **Readable** — typeclass / abstract spec with read-only operations; named with the `Readable` suffix. Effect parameter `E` for iteration effect. Concrete sorts `requires` this typeclass.
- **PersistentX** — functional-update variant. Verbs: `empty()`, `with(c, …)`, `without(c, …)`. No declared effects on update operations. Two empties denote the same value.
- **MutableX** — in-place-mutation variant. Verbs: `new() effects Modify[result]`, `set(c, …) effects Modify[c]`, `delete(c, …)`, `clear(c)`. Allocator follows 027.1.

Operation names never collide between Persistent and Mutable. Generic code parameterises over the Readable typeclass; mutation code is sort-specific.

## Out of scope for this directory

Library proposals do not propose kernel-language changes. If a library design needs a new language feature, the kernel proposal lives in the parent directory and the library proposal references it as a dependency. Examples:

- Effect-polymorphic iteration in `MapReadable` depends on proposal 045 (effect sets and expressions).
- Persistent/Mutable allocator effects depend on proposal 027.1.
- Future "associated iter carrier" promotion (map.md Open Q 6) may need new kernel machinery if the existing `requires` mechanism turns out insufficient — that would surface as a kernel proposal first.

Library proposals also do not propose *example applications* (those live in `examples/`) or *codegen profiles* (those are in `docs/rust-forward-mapping.md` and the realization stdlib).
