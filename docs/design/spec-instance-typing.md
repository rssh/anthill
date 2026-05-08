# Sort-level type-parameter instantiation at call sites

## Status: Draft (WI-211)

## Tracks: WI-203 (operation bodies in `FileBasedWorkitemStore`), proposal 036 (Domain Store Sorts)

## Relates to: WI-186 (free-standing parametric ops; same shape, different binding site), WI-209 (parametric effect substitution; lands the call-site rewrite of `Modify[c] → Modify[s]`), WI-079 (typing-pass parity), WI-210 (call-site dispatch via fact — orthogonal but built on the same instantiation machinery)

## Goal

Make polymorphic operations defined inside a sort (`Stream.head`, `Option.map`, `Map.get`, …) propagate their argument's sort-level type-parameter bindings into the result type and the effect row. Today an op declared with bare-sort param types like

```anthill
sort anthill.prelude.Stream
  sort T = ?
  sort E = ?
  operation head(s: Stream) -> Option[T = T] effects E
end
```

reports `Option[T = T]` (with `T` unbound) and `effects E` (with `E` unbound) at the call site `Stream.head(retrieve_result)` — even when `retrieve_result : Stream[T = Term, E = Error]`. The unify pass succeeds (sort_ref-vs-parameterized of same base is "compatible") without binding T or E in the substitution; the existing shallow `walk_type` then can't substitute the still-bound `Var(vid_T)` nested inside `Option[T = …]`.

The fix: make `unify_types` bind sort-level params when one side is a parameterized form and the other a bare sort_ref of the same base, and make `walk_type` (or a deep companion) recurse through `Term::Fn` so the bindings propagate into the return type and effects.

## Background — the existing representation is correct

Worth saying upfront because it shapes the design: anthill's loader **already** emits sort-level type parameters as unification variables, not symbolic references. The fix lives entirely in `unify_types` + `walk_type`; no schema changes, no loader rewrite.

### `sort T = ?` registration

`load.rs:455-456`, scan pass 1: when `Item::AbstractSort` with `s.definition = TypeExpr::Variable { … }` is encountered inside a sort/enum scope, the scope's `type_params` set gains `"T"` and `type_params_ordered` gets the name appended (so positional bindings later — `Stream[Int, Error]` → `[T = Int, E = Error]` — work).

### `T` references in operation signatures

`load.rs:3567-3589`, `type_expr_to_term` for `TypeExpr::Simple("T")` inside Stream's scope:

```rust
if self.kb.symbols.is_type_param(self.current_scope.raw(), &short_name) {
    let key = (self.current_scope.raw(), short_name.clone());
    if let Some(&cached) = self.type_param_vars.get(&key) {
        return cached;
    }
    let vid = self.kb.fresh_var(var_sym);
    let var_tid = self.kb.alloc(Term::Var(Var::Global(vid)));
    self.type_param_vars.insert(key, var_tid);
    return var_tid;
}
```

Two consequences:
1. **All references to `T` within Stream's scope share one `Var(Global(vid_T))`.** The cache makes the loader idempotent: every time `T` appears in a param type, return type, or effect row of an operation in Stream's body, it resolves to the same `vid`.
2. The Var is `Global`, not `DeBruijn` — so `Substitution::bind(vid, ...)` operates on it directly (no opening pass needed at call time).

### What gets stored in `OperationInfo`

For `Stream.head`'s signature:

| Position | Stored term |
|---|---|
| `params[0].type_name` | `sort_ref(Stream)` — bare; no parameterization |
| `return_type` | `parameterized(Option, [(T_field, Var(vid_T))])` |
| `effects` | `[Var(vid_E)]` |

Note `T_field` is the *field name* `T` of `Option`'s sort-level parameter (interned independently); `vid_T` is the unification variable for `Stream`'s `T`. They're different things — the field name is a Symbol, the binding value is a Var.

### Var vs Ref — the distinction

| | `Term::Ref(Symbol)` | `Term::Var(Var::Global(VarId))` |
|---|---|---|
| Meaning | Reference to a *named entity* (a sort, function, enum variant, …). | A *unification variable*. |
| Equality | Symbol equality. | VarId equality. |
| Substitution interaction | Constant — never bound. | The thing `Substitution::bind` operates on; resolved by `walk_type`. |
| When emitted in type-expr lowering | When the name resolves to a Sort / Operation / Entity (anything that's not a type-param of the current scope). | When the name is a registered `type_param` of the current scope. |

So `Stream` in `s: Stream` lowers to `sort_ref(Stream)` (a Term::Fn whose `name` field is a `Ref(Stream-symbol)`); `T` in `Option[T = T]` lowers to `Var(Global(vid_T))`. The loader gets this right.

## The two bugs

Stream.head call site: `Stream.head(retrieve_result)` where `retrieve_result` has type `parameterized(Stream, [T = Term, E = Error])`.

### Bug 1 — `unify_types` fails to bind sort-level params

`typing.rs:1369-1403`. Trace:
- a = `parameterized(Stream, [T = Term, E = Error])` (arg type)
- b = `sort_ref(Stream)` (param type)
- `walk_type(a) → a` (top-level Fn, no Var, no alias)
- `walk_type(b) → b` (sort_ref, but Stream isn't a SortAlias to a Var)
- `a == b`? No.
- Either side a Term::Var? No.
- `a_functor = "parameterized"`, `b_functor = "sort_ref"` — **don't match the `(parameterized, parameterized)` arm**, fall through to `types_compatible`.
- `types_compatible` returns `true` (sort_ref of Stream is compatible with parameterized(Stream, …)).

Result: unification *succeeds* (return value true) but the substitution stays empty. T and E are never bound.

### Bug 2 — `walk_type` doesn't recurse into `Term::Fn`

`typing.rs:1397-1423`. The function handles only:
- Top-level `Term::Var(Var::Global(vid))` → resolve via subst.
- Top-level `sort_ref(name)` where `name` aliases to a `Var` → resolve via subst.

For `parameterized(Option, [(T_field, Var(vid_T))])`, `walk_type` returns the term unchanged: it's a Term::Fn with functor "parameterized", which doesn't match either arm.

Even if Bug 1 were fixed and `subst` had `vid_T → Term`, `walk_type(return_type)` wouldn't substitute the nested `Var(vid_T)`.

### Empirical confirmation

WI-209 attempted a `deep_walk_type` (recursive into `Term::Fn`) and ran the bundle. The error message changed from `Option[T = T]` to `Option[T = TermId(N)]` — meaning the deep walk reached the inner `Var(vid_T)`, but vid_T resolved to itself (unbound), so display fell back to the raw `TermId` formatter. That's Bug 1 in the open: deep walk works mechanically, but Bug 1 left the subst empty. The fix needs both.

## Design — call-time binding via the shared Vars

The existing representation makes the design near-trivial: at every reference to `T` in Stream's signature, the term is the same `Var(vid_T)`. So **`unify_types` needs to bind `vid_T` once**, and a deep walk threads the binding everywhere it occurs.

### Why call-time binding (not load-time freshening)

A textbook Hindley-Milner instantiation step would freshen the operation's signature at each call site (substitute every type-var with a fresh metavar), then unify. Anthill *doesn't* need that — the loader's caching already gives every reference to `T` within Stream's body the same `Var(vid_T)`, which acts as Stream's "single canonical" type parameter. Per call, `unify_types` binds `vid_T → arg's T binding` in the per-call subst; the binding lives only for the duration of that `check_apply` call. Different calls don't interfere because each gets a fresh `Substitution`.

The freshening alternative (allocate fresh vars per call, rewrite the signature) would actively break the existing sharing. Worse, it would require knowing where in the signature term tree the type-param vars are — information already encoded by the loader's `type_param_vars` cache.

### The unify_types extension

Add a new arm before the fallthrough to `types_compatible`:

```
match (a_functor, b_functor) {
    (Some("parameterized"), Some("parameterized")) => unify_parameterized(...),
    (Some("parameterized"), Some("sort_ref")) =>
        unify_parameterized_with_sort_ref(kb, subst, a, b),
    (Some("sort_ref"), Some("parameterized")) =>
        unify_parameterized_with_sort_ref(kb, subst, b, a),
    (Some("arrow"), Some("arrow")) => unify_arrow(...),
    (Some("named_tuple"), Some("named_tuple")) => unify_named_tuple(...),
    _ => types_compatible(...),
}
```

`unify_parameterized_with_sort_ref` does:
1. Extract Base symbol from both sides; check equality. Mismatch → `types_compatible` (covers width / alias subtyping).
2. Extract `parameterized` side's bindings: a list of `(param_field_sym, value_term)`.
3. Look up Base's declared `type_params_ordered` (already on `Scope`). For each declared param name `P`:
   - Find the Var the loader cached for `(Base-scope, P)` — this is `Base`'s canonical type-param Var.
   - If `parameterized` has a binding for `P`, unify the cached Var with the bound value (which adds `cached_var → value` to subst).
   - If `parameterized` has no binding for `P`, leave the Var unbound (consistent with bare-sort_ref semantics: caller didn't constrain `P`).
4. Return `true`.

The cached Var is the same one referenced throughout `Stream.head`'s signature, so binding it once is enough — every occurrence in `params[i].type_name`, `return_type`, and `effects` will resolve via the same vid.

Edge cases handled by step 3:
- **Width subtyping** — `parameterized(Stream, [T = Term])` (only T bound) vs `sort_ref(Stream)` accepts and binds only T. E stays unbound. Subsequent `walk_type` of `effects = [Var(vid_E)]` returns `Var(vid_E)` unchanged; the type checker's downstream effect-row matcher must tolerate "param free" effects (it already does — see `external_effects`).
- **Alias** — `sort Foo = Stream`. `walk_type(sort_ref(Foo))` already resolves through SortAlias if Foo aliases to a Var; if it aliases to another sort, the parameterized arm reduces to the same Base. Need to verify a sort-name alias (`sort Foo = Stream`) walks to `sort_ref(Stream)` via `resolve_sort_alias`. Probably works today.

### The walk_type extension

Make `walk_type` recurse into `Term::Fn` children. Allocate a fresh term only when a child changed (to keep hash-consing tight). The implementation already exists from WI-209's reverted attempt; just re-apply.

```rust
fn walk_type(kb: &mut KnowledgeBase, subst: &Substitution, ty: TermId) -> TermId {
    let resolved = walk_type_shallow(kb, subst, ty);  // current logic
    match kb.get_term(resolved).clone() {
        Term::Fn { .. } => kb.map_fn_children(resolved, |kb, child| {
            walk_type(kb, subst, child)
        }),
        _ => resolved,
    }
}
```

(`map_fn_children` was bumped to `pub(crate)` for WI-209 already.)

Note that **deep walk_type changes the signature: it now needs `&mut KnowledgeBase`** (allocating substituted terms). Current call sites:
- `check_apply` (`typing.rs:729`) — already has `&mut`. ✓
- `unify_types` itself (`typing.rs:1370-1371`) — has `&mut subst` but `&KnowledgeBase`. Either:
  - Pass `&mut KnowledgeBase` through. Cascading change but small.
  - Keep the shallow walk inside `unify_types` (the recursive structural arms — `unify_parameterized`, etc. — already do per-child unification, which subsumes deep walk). Use deep walk only at the top of `check_apply` for the final return type / effects.
- `check_operation_bodies` (`typing.rs:2333`) — needs `&mut`. Verify.

The cleanest split: keep `walk_type` shallow (current behavior), add `walk_type_deep` for use at call-site final-resolve points. Mirrors the WI-209 approach but this time gap 1 is also fixed, so `Option[T = TermId(N)]` doesn't surface.

## Worked example — Stream.head(retrieve(b, WorkItem(id: id)))

Signatures (before instantiation):
- `retrieve : (s: QueryableStore, p: Term) -> Stream[T = Term, E = Error] effects Error`
- `Stream.head : (s: Stream) -> Option[T = T] effects E`

Inside the impl body:
1. Type-check `retrieve(b, ...)` — returns `Stream[T = Term, E = Error]`, effects `[Error]`.
2. Type-check `Stream.head(<above>)`:
   - param_type = `sort_ref(Stream)` (Stream.head's signature)
   - arg_type = `parameterized(Stream, [T = Term, E = Error])`
   - **(new)** `unify_parameterized_with_sort_ref` binds `vid_T → Term`, `vid_E → Error` in subst.
   - **(new)** Effects walk: `walk_type_deep(subst, [Var(vid_E)]) = [Error]`. ✓
   - **(new)** Return walk: `walk_type_deep(subst, parameterized(Option, [T = Var(vid_T)])) = parameterized(Option, [T = Term])`. ✓
3. Result: type `Option[T = Term]`, effects `[Error]`.

Matches the spec's declared `lookup(...) -> Option[T = Term] effects Error`.

## Open questions

### 1. What about operations *not* declared inside the sort's body?

Free-standing ops like `apply(s: Stream, n: Int) -> ...` declared at namespace level. Inside this op, `Stream` references would lower to `sort_ref(Stream)` via the non-type-param path (`Stream` isn't a type_param of the namespace). The op's signature uses bare `Stream` as a "polymorphic over T and E" shape — but there's no shared Var to bind.

Two stances:
- **(a) Reject as ambiguous** at load time: bare-sort references to a parametric sort outside the sort's body must specify bindings (positional or named). Forces `apply(s: Stream[T = ?T, E = ?E], n: Int)` syntax.
- **(b) Allow; freshen at load time**: create a fresh Var per occurrence per op (or shared per op's signature like the in-body case, but per-op rather than per-sort). At call time, unify normally.

This collides with WI-186 (free-standing parametric ops). Coordinate: probably (b), and the freshening machinery should land once and serve both. **Open: confirm with WI-186 implementer.** Out of WI-211's strict scope.

### 2. Parametric coverage of effects

Does `effects E` work the same way as `Option[T = T]`? Inspecting the loader: yes — `e.type_expr` is converted via `type_expr_to_term`, same path that creates the shared Var. Effects of an op are stored as a `Vec<TermId>`; each is a Type term, and Vars in them get walked the same way return types do. No extra work.

### 3. `parameterized(B, [...])` vs `parameterized(B, [different bindings])`

Already handled by the existing `unify_parameterized` arm. WI-211's new arm only kicks in when one side is `sort_ref` and the other is `parameterized`.

### 4. Variance

Anthill's typer treats parameterized bindings as invariant today (per `unify_parameterized`). Stream[T = Term] vs Stream[T = String] should fail; with WI-211, that path doesn't change — the new arm only handles the bare-sort case. Variance refinement is orthogonal and out of scope.

### 5. `walk_type_deep` interactions with `unify_types`'s internal `walk_type` calls

`unify_types` calls `walk_type(a)` and `walk_type(b)` at the top. If we make those calls deep, every unification recurses through Fn children — could be expensive for large types. Better to:
- Keep `walk_type` (shallow) where it is.
- Use `walk_type_deep` only at user-visible result-resolve points (`check_apply` return / effect resolution).

Internal unification recursion already handles structural descent via the per-functor `unify_parameterized` / `unify_arrow` / `unify_named_tuple` arms.

### 6. Effect-row variables that aren't resolved

If a call doesn't bind E (e.g., the param type is bare `Stream` with no E binding implied), `walk_type_deep` returns `Var(vid_E)` unchanged for the effect. Downstream:
- The op's caller may have a more specific E in scope (transitive caller). But that requires propagating *up* through `check_apply` calls — which is what subst already does.
- At the outermost op (the operation being type-checked), an unbound E is a free type variable. Today's typer treats free Vars as "compatible with anything" via `types_compatible`'s wildcard rule — likely fine. If it surfaces as a check failure, the workaround is the caller binding E explicitly.

Worth a test case but probably not a blocker.

### 7. Tests that depend on the current (broken) behavior

A search of existing tests for `Option[T = T]`-like literal expectations should turn up none — the broken case was only surfaced by WI-203's bodies, which haven't landed elsewhere. Re-running `typing_test` (134 tests) post-implementation is the canonical check; anything that flips means a latent test was sensitive to the polymorphic-instantiation behavior in some other way and we should investigate.

### 8. Interaction with WI-209's parametric effect substitution

WI-209 rewrites `Modify[c]` (param-name in effect) → `Modify[s]` (arg-var). WI-211 walks Vars through subst. They commute: WI-209 runs first (rewrites Term::Ref nodes per param-name map), then WI-211's deep walk runs (resolves Term::Var nodes through subst). Different Term variants, different operations — no conflict.

## Implementation plan

Estimated ~80 LoC in `kb/typing.rs`, plus a small helper.

1. **`type_params_of_sort_with_vars`** helper on `KnowledgeBase` (or accessible from typing): given a sort symbol, return `Vec<(Symbol, TermId)>` — the type-param field name and the loader-cached Var. Source: `Scope::type_params_ordered` + the `type_param_vars` cache (move/expose appropriately).

2. **`unify_parameterized_with_sort_ref`** in `typing.rs`: extract base, look up declared params, unify each `(field, value)` from the parameterized side with the cached Var. Add to the `unify_types` match arms (both directions).

3. **`walk_type_deep`** in `typing.rs`: shallow walk + recurse into `Term::Fn` via `kb.map_fn_children`. Takes `&mut KnowledgeBase`.

4. **`check_apply` resolve sites** (`typing.rs:729`): replace shallow `walk_type` with `walk_type_deep` for `op.return_type` and `substituted_op_effects`.

5. **Tests**:
   - Direct: invoke `Stream.head` on a `Stream[T = Term, E = Error]` value; assert inferred return type is `Option[T = Term]` and effects include `Error`.
   - Indirect: restore the WI-203 bodies (`anthill-todo/store.anthill`) — `lookup` and `by_status_of` with explicit signatures should type-check cleanly.
   - Regression: full anthill-core test suite (47 suites, 134 typing tests) must stay green.

6. **Acceptance** (matches WI-211's filed criteria):
   - `cargo-test` green workspace-wide.
   - WI-203's `next_id` / `commit` / `lookup` / `by_status_of` bodies in `anthill-todo/store.anthill` type-check cleanly under `--anthill` bundle path.
   - New typing test asserts `Stream.head(retrieve(...))` yields `Option[T = Term]`, not `Option[T = T]`.

## Out of scope

- WI-186 (free-standing parametric ops) — different binding site, same machinery in spirit. Should be coordinated but lands as its own WI.
- WI-210 (call-site dispatch via fact for spec/impl method resolution) — orthogonal; the typer pieces from WI-211 are reused but the dispatch design needs its own doc.
- Variance refinement — out of scope.
- Subtyping for parametric sorts (`Cell[Int] <: Cell[Number]`) — not how anthill works today; out of scope.

## Acceptance

Once accepted, WI-211 implementation proceeds along the plan above; design re-litigation only if implementation surfaces a structural problem with the call-time-binding model (e.g., it turns out `type_param_vars` aren't actually shared across the operation's signature in some loader path).
