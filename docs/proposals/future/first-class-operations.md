# Future: Operations as first-class function values

> **Stub** (2026-06-15) — to be extended. Unnumbered (see [README](README.md)).

## Idea

A bare operation name should denote the operation **as a first-class function
value**, and `()` should be **uniformly application/invocation**:

- `f` is the function value (the runtime already has `Value::OpRef`);
- `f(args)` applies it; a 0-arg op `g` is invoked `g()` (= apply to the unit
  tuple `()`);
- effects ride on the function value and are paid at application — no
  pure/effectful special case at the call site.

The payoff: operations become passable to higher-order operations without a
lambda wrapper — `map(xs, increment)` instead of
`map(xs, lambda x -> increment(x))` — which anthill lacks today (stdlib HOF call
sites all pass lambdas/params, never bare op names).

## Relationship to proposal 039 (term-level constants)

Surfaced during the 039 brainstorm (2026-06-15). **039 deliberately does not
depend on this.** 039 scopes to `const` as a *memoized value binding* (a bare
`const` is its value). This is the orthogonal *operation* half. They compose:

- both a `const` and a bare operation reference are *value-denoting* in term
  position, so both fall under the one bare-name candidate set and the
  "ambiguity is an error" rule 039 settled (039 Open Question B);
- 039 drops the old "parenless 0-arg-op invocation" sugar; this proposal is the
  principled replacement (a 0-arg op is invoked `g()`; the bare name is the
  function value).

## Scope / open work

- **Source-level eta:** the typer must turn a bare operation reference into a
  function value carrying the op's full arrow type **including its effect row**
  (`(A) -> B @ E`). The runtime carrier (`Value::OpRef`) exists; the typer
  wiring and eta semantics do not.
- **Dispatch:** how a first-class `OpRef` to a spec/overloaded operation
  resolves when applied (cf. WI-455 OpRef redispatch). *Scope half settled by
  WI-455 (2026-07-12):* an `OpRef` **denotes its operation** — application
  dispatches to that operation and is **not** subject to the applying frame's
  scope, so a caller-local that merely shares the op's short name cannot capture
  the call. One did: a param named `double` made `apply_it(double, triple)` run
  `triple`, and two such locals pointing at each other cycled until the host
  stack overflowed. An application therefore resolves in exactly **one hop** and
  cannot chain. **Still open:** how an `OpRef` so dispatched picks the *carrier
  impl* of a spec/overloaded op — unchanged, still the value-directed resolution
  of WI-444 / WI-350.
- **Interaction** with dot-dispatch (WI-279) and carrier-aware dispatch (WI-350).
- **Migration:** none — additive (bare operation references are not currently
  first-class), and existing `f()` call sites keep their meaning.

## Promotion

Assign a main-sequence proposal number and move out of `future/` when scheduled.
