# The operation-call model

## Status: Draft

## Tracks: WI-204 (port cmd_X via spec ops), WI-218 (static-dispatch rewrite), WI-210 (spec/impl call-site dispatch via fact)

## Relates to: spec-instance-dispatch.md (the WI-210 design); proposal 030 (specialization witnesses); proposal 036 (Domain Store Sorts)

## Problem

Today anthill has three syntactic shapes for an operation call:

1. **Bare name in a monomorphic context** — `commit(s, w)` where `s : Cell[V = WIS]`. The type-checker can resolve which impl's `commit` to invoke based on per-call substitution: `WIS` is a ground sort, so dispatch to `FileBasedWorkitemStore.commit`.

2. **Bare name in a generic body** — `foo(x)` where `x : T` and `T` is the enclosing sort's own type-param. The dispatch decision can't be made at the body's typing time because `T` is open.

3. **Qualified impl name** — `C1.foo(x)`, `FileBasedWorkitemStore.commit(s, w)`. No dispatch needed; the impl is named directly.

WI-210 introduced dispatch-via-fact for shape (1). WI-218 added the static rewrite (replace `<Spec>.<op>` with `<Impl>.<op>` at typing time) so the eval invokes the impl body directly. Both work for shape (1) and don't apply to shape (3).

**The current implementation fails shape (2)** in two distinct ways:

- **Open-T case**: the per-call subst's value for the spec's type-param is a `Term::Var` (the enclosing sort's open T). `find_unique_impl_op` sees the Var, walks `SortProvidesInfo` records, and silently picks the first universally-quantified candidate. The body gets rewritten to a specific impl that may be wrong for the eventual instantiation.
- **Ground-via-require case**: the spec op is reached through a `requires` clause whose target binding is concrete at B's site (e.g. `requires A[T = String]`). The per-call subst is fully ground. `find_unique_impl_op` proceeds and picks whichever impl satisfies `A[T = String]`. But that choice is **the future instantiator's** — D, the sort that asserts `fact B[T = …]` and supplies (or declines to supply) the matching A satisfaction. If two A[T = String] impls exist (or one exists today and another is added later), B.bar's locked-in choice is wrong.

Both failures share a common root: **the dispatch decision needs information not available at B.bar's typing site**. The first wants the type-arg ground value; the second wants the bound's resolver. Either way, B is the wrong scope to commit.

### Concrete example

```anthill
sort A
  sort T = ?
  operation foo(x: T) -> String
end

sort B
  sort T = ?
  requires A
  operation bar(x: T) -> String =
    String.concat("B", foo(x))      -- shape (2): generic body
end

sort C1
  sort T = ?
  fact A[T = T]
  operation foo(x: T) -> String = "c1"
end

sort C2
  fact A[T = String]
  operation foo(x: String) -> String = String.concat("c2", x)
end

sort ClientCall
  operation callFoos(x: String) -> String =
    let x1 = C1.foo(x)              -- shape (3): qualified
    let x2 = C2.foo(x)              -- shape (3): qualified
    String.concat(x1, x2)
end
```

When the typer checks `B.bar`'s body, the `foo(x)` call has per-call subst `A.T → Var(B.T)` — `B.T` is open. The current WI-218 rewrites it to `C1.foo` (because `C1`'s candidate binding `T = T` matches anything per `is_type_param_value`, and `C2`'s `T = String` doesn't match a Var).

But `B.bar` is meant to work for any `T`. If a user writes `D[T = String] satisfies B`, the dispatch should pick `C2`. If they write `D[T = Int] satisfies B`, it should pick `C1` (or whichever satisfies `A[T = Int]`). The decision belongs to D, not B.

### Why "deferred / dynamic" alone isn't enough

A natural fix is "leave it generic, dispatch at runtime via vtable." Java does this. But anthill commits to **static dispatch** for two reasons:

- **Codegen target alignment.** Rustland's codegen emits Rust traits; rustus and the cpp/scala targets do similar monomorphization. A vtable-only model loses the static-dispatch property the codegen depends on.
- **Proof-record specialization** (proposal 030) is keyed on (spec sort, impl sort) pairs. Dispatch must be statically resolvable so the witness records can be cited at compile time.

So the dispatch must be resolved **before runtime**. The question is *when*: at the body's site (impossible — too early) or at the instantiation site (correct — the generic's T becomes ground).

## Taxonomy

| Shape | Where T is bound | When dispatch resolves | Mechanism |
|-------|------------------|------------------------|-----------|
| (1) Monomorphic | Ground at body site | Body typing | WI-218 rewrite (today) |
| (2) Generic-via-Self-bound | Bound at outer instantiation site | Instantiation typing | **Monomorphization** (this doc) |
| (3) Qualified impl | n/a — direct lookup | n/a | Direct |

The three shapes are tied by a shared mental model: every operation call has a *resolution scope* — the smallest scope where all spec-T's become ground. Shape (1)'s resolution scope is the call site itself; shape (2)'s is the outer instantiation; shape (3) doesn't go through dispatch.

## The "require" clause is a Self-bound

`sort B { requires A; ... }` declares that B's instances must also satisfy A. In Rust this is `trait B<T>: A<T>`. The require clause IS the bound that makes B.bar's `foo(x)` resolvable — at B's instantiation site (the sort that asserts `fact B[T = X]`), that sort must also have an A binding for X.

So the resolution path for B.bar's `foo(x)` is:

```
B.bar's body                        -- generic, T is B.T (open Var)
  └─ foo(x) referenced through `requires A`
       at instantiation `D { fact B[T = Int]; fact A[T = Int] }`:
       └─ D's A[T = Int] satisfaction → A's impl at T = Int
            └─ rewrite foo to that impl's foo
```

The rewrite happens in a **monomorphized copy** of B.bar specialized to D — not in B.bar itself.

## Design

### Operation-call kinds

Each apply term in an operation body gets classified into one of three **call kinds** at typing time:

```
enum CallKind {
  Direct,                                 -- shape (3): qualified, fn = impl op
  Monomorphic { impl_op: Sym },           -- shape (1): rewritten to impl op via WI-218
  Generic { spec_op: Sym, via: Source },  -- shape (2): defers to monomorphization
}

enum Source {
  OpenTypeParam { spec_param: VarId },     -- per-call subst's value is a Var
  RequiresChain { bound: SortRef, ... },   -- reached via the enclosing sort's `requires`
}
```

A call is **Generic** iff *either* condition holds:

1. **Open-T**: at least one per-call binding value resolves to a `Term::Var` that is the enclosing sort's own open type-param. The dispatch needs the future instantiator's type-arg ground value.
2. **Via-Requires**: the spec op is reached through a `requires` clause on the enclosing sort. Even if the requires' binding is concrete at this site (e.g. `requires A[T = String]`), the dispatch decision is the future instantiator's responsibility — they pick which `A[T = String]` impl B uses, not B itself.

A call is **Monomorphic** only when neither condition holds: the spec op is reached *not* through a `requires` chain (so the enclosing sort itself is committing to a binding for the spec, not delegating), AND every per-call binding is ground.

A call is **Direct** when the fn symbol is already an impl op — no dispatch needed.

The two `Generic` triggers correspond to the two failures in the Problem section. The classification has to detect both; the open-T check alone is not sufficient.

### Why the require-chain check is required

In the example:

```anthill
sort B { requires A[T = String]; operation bar(x) = ... foo(x) ... }
```

B's operation body references `foo` (an A op). Per-call subst is ground (T = String). But B's own `requires A[T = String]` is the bound; it tells the typer "B will be satisfied by something that ALSO satisfies A[T = String]." Which sort actually satisfies A[T = String] is up to whoever asserts `fact B[T = …]` — call them D. D's pick (C2a vs C2b) is the dispatch target for foo inside B.bar's specialization.

If B were to commit to one of the candidates at its own typing time, D's freedom to pick differently would be silently overridden. So the require chain is itself a form of "open-ness" — not in the type-arg, but in the impl identity.

### Why the open-T check is required

In the example:

```anthill
sort B { sort T = ?; requires A; operation bar(x: T) = ... foo(x) ... }
```

Even without a concrete binding on the requires (just `requires A`), B's own T is open. `foo(x)` has `A.T → Var(B.T)`. We can't pick A's impl without knowing what B.T will be at instantiation. (Once D writes `fact B[T = Int]`, T is ground and we can pick A[T = Int]'s impl — that's the monomorphization point.)

The two cases together: anything reachable through a `requires` chain stays Generic; anything with an open Var in the subst stays Generic. Only calls that are neither — direct impl-sort references with all-ground bindings — get the WI-218 monomorphic rewrite.

### Monomorphization pass

When a fact `X { fact B[T = Bind] }` is loaded with all of `Bind` ground, the loader queues a monomorphization task: copy B's generic operation bodies into X's namespace, substituting `B.T → Bind`.

For each generic op `B.bar`:

1. **Clone the body** with substitution `{B.T → Bind}` applied bottom-up. The clone produces a new TermId tree where `var_ref` to `B.T` becomes `Bind`.
2. **Re-run dispatch classification** on the cloned body. `foo(x)` in the clone now has `A.T → Bind` (ground) — it's a Monomorphic call. WI-218 rewrites apply.
3. **Register a specialized OperationInfo** under `X.bar` (or `B[T = Bind].bar`, depending on how the namespace is encoded) with the monomorphized body. The eval finds it directly.

The clone-and-rewrite pass is the runtime view of "B.bar specialized for X". Each `(generic spec, ground binding)` pair gets one specialized body. Code-size grows with the number of distinct bindings, same as Rust's monomorphization.

### `requires` chains drive the dispatch graph

The bound on B (`requires A`) tells the monomorphization pass **what to look for** at the instantiation site. When monomorphizing B.bar for X's `fact B[T = Int]`:

1. Walk B's `requires A` chain.
2. At X's namespace, look up `A` impls satisfying `A[T = Int]`. (X must have a fact for that — checked at X's load time per WI-210 coherence.)
3. Bind A's resolution in the monomorphization context.
4. Inside the cloned body, `foo(x)` is now a Monomorphic call against the bound A impl. Rewrite via WI-218.

The chain composes recursively. If B requires A, A requires Eq, …, the monomorphization walks the whole chain at the outermost instantiation.

### What about polymorphic recursion / unbounded specialization?

Generic-recursive instances (`List[T = List[T = Int]]`) are handled by Rust via finite expansion + dynamic dispatch fallback for genuinely-recursive cases. Anthill should:

- Permit finite monomorphization for non-recursive bindings.
- For recursive cases (sort F where F.body refers to F[T = F[T = Int]]), require explicit `dyn` annotation or compile-error. **This is the only place vtable-style late binding has to enter the picture, and only as an explicit user opt-in.**

In the v0 of this design we can skip the recursive case entirely (compile-error at the outer fact load) and add the `dyn` escape later.

### Coherence (multi-impl)

WI-210 already specifies coherence for monomorphic dispatch (priority table or reject-as-ambiguous). The same rules apply at monomorphization:

- If X picks `A` ambiguously (two `fact A[T = Int]` candidates), reject at X's load time.
- If a generic-body call's monomorphization context has no candidate for the required A binding, reject at X's load time (not at B's body).

The `requires` chain pins coherence at the outer site, where the user has the most context to disambiguate.

## What this means for surface syntax

Mostly nothing. The three existing call shapes stay:

- Shape (1) and (3) work as today.
- Shape (2) works **after monomorphization lands**. Until then, generic bodies that reference spec ops compile-error with a clear message ("call to `foo` from generic body requires monomorphization, not yet implemented").

No new syntax needed for the primary path. The recursive-case `dyn` annotation is a future extension.

## Implementation roadmap

| Phase | Scope | Status |
|-------|-------|--------|
| **WI-218 patch (soundness)** | In `find_unique_impl_op`, return a new `Deferred` outcome (skip rewrite) when *either* condition holds: (a) per-call subst contains a Var that's the enclosing sort's own type-param; (b) the spec op is reached through a `requires` chain on the enclosing sort. The body retains the spec-op call; eval errors loudly until monomorphization lands. Generic bodies become unsound-but-explicit (clear error) instead of unsound-and-silent (current state). | Open. ~50 lines: subst-shape check + requires-chain detection. |
| **Generic-call classification** | Extend `dispatch_origin` (or add `dispatch_kind: HashMap<TermId, CallKind>`) so each apply records its call kind at typing time. Generic calls store the spec op + bound info for later use. | Open. Modest. |
| **Monomorphization pass** | At fact load (`fact Spec[T = Bind]` with ground Bind), clone+substitute generic bodies, re-classify and rewrite. Register specialized OperationInfo facts. | Open. Substantial — this is the bulk of the work. |
| **Recursive-case handling** | Detect cycles in monomorphization expansion; reject or require explicit `dyn` annotation. | Open. Small once detection lands. |
| **Dynamic dispatch (escape hatch)** | `dyn Spec` annotation; vtable-style late binding for genuinely-runtime-decided cases. | Future, optional. |

## Soundness invariants

After this design lands, the invariants are:

1. **No silent dispatch**: every `apply` term whose `fn` is a spec op either gets resolved at typing time (Monomorphic / Generic-via-bound after monomorphization) or is rejected with a clear diagnostic.
2. **Static dispatch preserved**: every dispatched call's resolution is known at compile time. The eval reads `dispatch_rewrites` for the rewrite, never resolves dispatch at runtime.
3. **Coherence at outermost site**: ambiguity in `requires` chains is rejected at the instantiation that introduces the choice, with the user-visible context to fix it.

## Open questions

- **Where does `dispatch_kind` live?** Side-table on the KB (consistent with `dispatch_origin`), or a structural field on apply terms? The WI-218 discussion landed on side-table; same logic applies here.
- **Where do specialized bodies live?** Sub-namespace of the impl sort (`X.B.bar`)? Or a flat namespace with mangled names? Affects reflection, debug, and codegen. Rust uses mangled names; that's probably right for anthill too.
- **How does the loader know when to monomorphize?** Eagerly at fact-load time (one pass over all `fact Spec[T = Bind]` facts), or lazily on first use? Eager is simpler and aligns with Rust; lazy saves work for unused specializations.
- **Interaction with proposal 030 (specialization witnesses)**: the witness records should reference the monomorphized body, not the generic one. Need to thread monomorphization through the witness emission.

## Migration path from current state

WI-218 today is sound for shape (1), unsound for shape (2). The unsound behavior bites only when generic bodies call spec ops via `requires` chains. **No code in the current tree triggers it**: store.anthill's `FileBasedWorkitemStore.commit` body is not generic over a spec; the bundle's `cmd_X` bodies are not inside generic sorts.

So current code is safe. The unsoundness is latent — a hazard for anyone writing generic specs with `requires` chains.

The phased migration:
1. **Land the WI-218 soundness patch** — turn the latent unsoundness into an explicit error. Small, immediate.
2. **File a new WI** for monomorphization with this doc as the design.
3. **Decide** lazy vs eager monomorphization, body-namespace mangling, and `dispatch_kind` storage shape — open questions above.
4. **Implement** the monomorphization pass.
5. **Re-port** B.bar-style generic bodies (and anything that hit the WI-218 generic-body limitation) once mono is in.

## Acceptance for the design (this doc)

- This doc lands. Discusses the three call shapes, their resolution scopes, and the monomorphization-as-real-solution position.
- A new WI is filed for the monomorphization pass with this doc as the design reference.
- WI-218 is amended with a soundness-patch follow-up note.

The implementation acceptance lives in the per-phase WIs.
