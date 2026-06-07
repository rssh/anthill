# Anthill TODO

Project-wide follow-up tracking.

## Sort as Proper Type / Lattice

### Architecture

- Sort and Term are **separate types**. Term is the representation (model) of Sort.
- `sort_as_term` / `term_as_sort` are the reification/reflection boundary (not subsort coercions).
- `can_be_sort(t: Term) -> Bool` — not every term is a valid sort representation.
- Sort's `eq`, `lub`, `glb` are Rust builtins that internally operate on term representations, but the anthill-level API is Sort → Sort.
- `lub` is the **primitive** — `less` and `eq` derive from it via lattice laws:
  - `less(A, B)  ⟺  lub(A, B) = B`
  - `eq(A, B)    ⟺  less(A, B) ∧ less(B, A)`
- `type_compatible` in typing.anthill IS `less` for Sort. The connection is via spec-directed dispatch: `fact Lattice[T = Sort]` routes `less` to `type_compatible`.
- Sort equality is structural (functor + parameter bindings), not TermId comparison (standardize-apart produces fresh variable IDs).
- Sort-specific rules beyond plain unification: named tuple compatibility, Nothing as bottom, parameterized sort equality (`List[T=Int64]` ≠ `List[T=String]`).

### Implementation tasks

- [ ] Rust builtins for `sort_as_term`, `term_as_sort`, `can_be_sort` in resolve.rs
- [ ] Rust builtin for Sort `lub` (graph walk over entity_of/refines + tuple rules)
- [ ] Spec-directed dispatch: `fact` declarations route spec operations to implementations (rules or builtins)
- [ ] Codegen for Lattice/BoundedLattice specs

## Language / Parser

- [ ] Extensible operator dictionary (currently hardcoded in pratt.rs) — Proposal 016
- [ ] Unit sort `()` — relationship to Nothing and tuples

## Custom Show / Pretty-printing

- [ ] Custom `Show` for sorts (e.g. List as `[a, b, c]` instead of `cons(head: a, tail: cons(...))`)
- [ ] Requires host-language FFI mechanism: how to link anthill operations to builtin Rust functions
- [ ] Design spec-directed dispatch for `Show` (similar to how `Eq[T=Sort]` routes to builtins)
- [ ] Consider: `show` as an operation on sorts, with builtin implementations registered per functor

## Stdlib

- [ ] Wire stdlib loading via `include_str!()` into binary
