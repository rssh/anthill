# Typed-term carrier — how `min_sort` rides on a term

## Status: design (started 2026-06-20)

**Relates to:** proposal [049](../proposals/049-equality-and-unification.md) (the `min_sort`
guard for type-specific simp). **Foundation:** WI-502 (terms carry types). **Consumer:**
WI-292 (resolver-side `min_sort` builtin + guard). WI-502 *is* the foundation WI-292 stands on.

Type-directed `[simp]` firing (proposal 043 §4) needs the resolver to read a term's
`min_sort`. The split today — the typer fires via `simp_fire_guard_holds`, the resolver
`equation_is_requires_guarded`-skips — exists only because the resolver holds type-erased
terms. This note settles **how the type is carried** so the resolver can read it, without
re-derivation and without breaking hash-consing.

## The type cannot live *on* the term

`min_sort` is a property of a term **in an environment**, not of the structurally-shared
term. `nil` is `List[?T]`; `?x` is whatever its context constrains. Hash-consing shares one
`TermId` across every environment, so a type slot *on* the term would have to hold every
environment's type at once — i.e. **unshare** the term. Rejected.

## The carrier: `TypedTerm = (type, term)`, `TermView`-blind to the type

Pair the type **alongside** the term instead of annotating it:

- **hash-consed `Value::Term`** → an external `(type, TermId)` pair: the `TermId` stays the
  one shared thing, the pair is the per-environment wrapper.
- **Rc'd `Value::Node` occurrence** → its existing `inferred_type: Option<Value>` slot
  (`node_occurrence.rs:522`) is the same idea on a carrier that isn't shared.

Unify them as: *a carrier may carry a type sidecar.* The load-bearing rule:

> `TypedTerm`'s `TermView` projects to the **term component**. Every structural operation —
> discrim insert/query, `builtin_unify`, `match_view`, the substitution walk — sees only the
> term and is **unchanged and type-blind** (the resolver is already carrier-agnostic over
> `TermView`, WI-342/348/349). Exactly one consumer reads the sidecar: the `min_sort`
> builtin (WI-292).

So delivering `min_sort` to the resolver is **additive** — a new reader of a sidecar — not a
change to the structural engine.

## `with_min_sort`, computed once — carried, not recomputed

The constructor is `with_min_sort: Term ⇒ TypedTerm` (not `min_sort: Term → Term`): it runs
the typer **once**, at the typing boundary, and pairs the result on. Thereafter the type is a
**term**, so it travels by the same mechanical operations the term already undergoes:

- **De Bruijn opening** opens the type's vars alongside the term's.
- **substitution** applies σ to the type as to the term — refining it when σ binds a shared
  type-var.

Neither is a re-run of inference. The WI-502 bug is only that opening/subst currently **drop**
`inferred_type`; the fix is *carry it*. (Where `with_min_sort` cannot link the type's vars
into the same frame, σ cannot refine the type — a **known refresh boundary**, surfaced
loudly, never silent drift.)

## Relation to proposal 049

This is the carrier under two things 049 already states:

- *Structural ops are transparent to `T`* ("`<=>` erases `T`") = `TermView`-to-term-component
  here.
- *Type-specific simp = structural selection + a `min_sort` guard* (049 "Where `<=>` sits")
  = the single sidecar reader here.

049 stays the unify **operator**; this note is the typed **carrier** it reads `T` from.
