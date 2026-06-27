# Typed-term carrier — merged

> **Merged 2026-06-27 into [`constrained-term-substrate.md`](./constrained-term-substrate.md)**,
> now the single live "Typed terms" design. This note was the origin of the carrier idea —
> `TypedTerm = (type, term)`, the structural-kernel-is-type-blind rule, and the hash-consing
> argument (the type cannot live *on* a shared `TermId`, so it rides alongside). All of that is
> carried forward there, re-centered on the `typed(value, env) → typed-value` primitive (the
> generalization of this note's `with_min_sort : Term ⇒ TypedTerm`), with `min_sort` removed.
> See that doc.
