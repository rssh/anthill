# Proposal 043 — Method-call (dot) syntax via simp rewriting

## Status: Proposal — for review.

## Relates to

- `docs/design/dot-macro-brainstorm.md` — the design exploration this proposal distills. Read it for full rationale; this doc is the implementable spec.
- **WI-139 (delivered)** — `[simp]`/`[unfold]`/`[hint]` equational-rule attributes (`anthill-core/tests/include/equational_attr_test.rs`).
- `docs/design/occurrence-as-value-type.md` — `NodeOccurrence` substrate.
- `docs/design/interpreter-ir.md` — downstream consumer; shares the equation-defined-operation concern (see §Interactions).

## Goal

Give Anthill method-call syntax: `?xs.map(?f).filter(?p)` instead of `filter(map(?xs, ?f), ?p)`. The mechanism is **simp rewriting**: a `dot_apply` parse node, rewritten during type-checking by `[simp]` equational rules that resolve the operation through the receiver's sort.

## Layering

Method dispatch *is* simp rules, so the simp **rewriting engine** is the shared foundation. The work splits into two parts on that foundation:

- **Part 1 — simp engine + dispatch.** The engine (typer fires `[simp]` rules bottom-up on expression occurrences) plus the dispatch rules (`default_dot`, `dot_field`). Dispatch guards are *type-level* only, so Part 1 needs no value folding. Dispatch either fires or errors. Structurally terminating. **This is the shippable deliverable.**
- **Part 2 — value-conditional simp.** Adds `constant_fold`/STUCK, value-conditional rules (`min`-style compile-time folding), residualization, and termination for recursive value rules. Same engine, extended guard handling. Separately scoped.

This proposal specifies Part 1 in detail and sketches Part 2.

---

## Part 1 — Simp engine + dispatch

### 1.1 The `dot_apply` node

A new `Expr` variant (reflect `Expr` constructor, snake_case per `reflect.anthill` convention — sibling to `apply`/`ho_apply`):

```
entity dot_apply(receiver: ExprOccurrence, name: Symbol, args: List[ApplyArg])
```

Rust side: a `NodeKind::Expr { expr: Expr::DotApply { receiver, name, pos_args, named_args }, … }` variant in `kb/node_occurrence.rs`.

### 1.2 Parser & converter

The grammar already parses `?x.y` (`field_access`) and `?x.y(args)` (`fn_term` with a `field_access` functor); **no grammar change**. The change is in `parse/convert.rs`:

- When a `field_access` node's `object` is a **`variable`** (value receiver) — both the bare `?x.field` form and the `?x.method(args)` call form — emit `dot_apply(receiver, name, args)` (args empty for the bare form). This is **unified**: field access and method call both become `dot_apply`; the `dot_field` rule (1.5) later splits them.
- When the `object` is an `identifier` or `instantiation_term` (sort/namespace receiver, e.g. `Foo.bar`, `Map[K=String].empty()`), keep today's behavior — flatten to a qualified `Name`. Disambiguating value-vs-sort identifier receivers needs resolution and is out of Part 1 scope (see §Open questions).

This fixes the current gap where `?x.method(args)` silently drops the receiver in `collect_field_access_segments` (`convert.rs:342`).

### 1.3 The simp engine (typer-driven firing)

The typer already exposes a per-node entry, `type_check_node(kb, occ, …)` (`kb/typing.rs:904`), a work-stack walk that classifies children before parents. The engine interposes there:

1. Walk bottom-up; children are classified first.
2. When a node is reached and its children are typed, query `by_functor` for `[simp]` equational rules whose LHS functor matches the node (per WI-139 indexing).
3. For each candidate, attempt to match the LHS and evaluate the guard via the resolver. **Part 1 guards are type-level** — they succeed (binding outputs like `?op`) or fail. No STUCK.
4. On a firing rule, build the RHS as a fresh `NodeOccurrence` with `origin: Synthesized { from: <matched occ>, by: <rule> }`, enqueue it for typing, and replace the node.
5. Re-type the synthesized node (it may contain further `dot_apply`s from nested receivers — handled by the same bottom-up pass).

**Reduction strategy: leftmost-innermost / bottom-up** — forced, because the outer dispatch needs `typeof(receiver)`, which needs the receiver reduced+typed first. Matches the typer's existing walk order.

**Termination (Part 1): structural.** `dot_apply(...)` rewrites to a non-`dot_apply` node (`apply`/`field_access`), so dispatch rules never re-fire on their own output. No general termination machinery needed in Part 1.

**Type re-checking of carried-over subterms:** reused subterms (e.g. `?x` in `dot_apply(?x,…) = apply(?op,[?x,…])`) keep their `classification`; the synthesized node is type-checked, verifying reused subterms fit their new positions. A conflict is a genuine type error, reported via the `Synthesized` chain to the source span.

### 1.4 Type-directed resolution — `find_operation_on_sort`

A new resolver builtin / KB query:

```
find_operation_on_sort(sort: Sort, name: Symbol) -> op: Symbol   (qualified)
```

- **Tier 1**: operations defined inside the sort/enum body (e.g. `length`, `member`, `append`, `map` in `enum anthill.prelude.List`). Reachable with **no import** — the qualified op name is returned, so the rewritten `apply` references it directly (riding existing Ident→Ref promotion). This is the defining property: `?l.map(?f)` needs `List`, not `import …map`.
- **Tier 2**: extension operations defined elsewhere whose first parameter matches the sort — follow normal import rules (in scope only if imported), like Rust trait methods / Scala 3 extensions.

Returns the qualified symbol on success, fails if no associated operation named `name` exists.

### 1.5 The dispatch rules (shipped in the prelude)

```
rule default_dot: dot_apply(?x, ?name, ?args) = ?op(?x, ?args)
  :- find_operation_on_sort(typeof(?x), ?name, ?op)
  [simp]

rule dot_field: dot_apply(?x, ?name, []) = field_access(?x, ?name)
  :- is_entity(typeof(?x)), has_field(typeof(?x), ?name)
  [simp]
```

- `dot_field` fires only for an entity receiver, a declared field selector, and no args → rewrites to the existing `field_access` builtin (`kb/resolve.rs:1975`), unchanged.
- `default_dot` fires otherwise → method dispatch, qualified resolution.
- **Guard-exclusive** (`has_field` vs `find_operation_on_sort`), so no firing-order policy is needed in Part 1. If a name is both a field and an operation, **field-first** (optional load-time lint flags the collision).
- `is_entity` / `has_field` are answerable from the existing `entity_fields` registry.

### 1.6 Errors

If neither rule fires on a `dot_apply` (no field, no associated operation): a type error, *"no field or method `name` on sort `S`"*, at the source span. (Delegation-chain walking is Part 2+/delegation work.)

### 1.7 Part 1 deliverable

`?xs.map(?f).filter(?p)` chains; `?p.x` field access works via the unified path; method calls resolve through the receiver's sort with no extra imports; clear errors on no-match. No `constant_fold`, no delegation, no DSLs.

---

## Part 2 — Value-conditional simp (sketch)

Builds on the Part 1 engine; adds compile-time partial evaluation.

- **`constant_fold(?const, ?source)` builtin** — the single occurrence→value bridge. Compile time: binds `?const` to `?source`'s literal value if it folds, else **STUCK**. Runtime (resolver equational fallback): identity. Phase-polymorphic; the only occurrence-aware value builtin — all other value operations stay occurrence-unaware.
- **STUCK + residualization** — when a value-conditional rule's guard STUCKs (non-constant operand), the rule does not fire and the term is left as a runtime call. Distinct from DELAY (unbound logical var; proof-time only).
- **Value-conditional rules** — e.g. `min`:
  ```
  rule min_le: min(?x, ?y) = ?x
    :- constant_fold(?xc, ?x), constant_fold(?yc, ?y), compare(?xc, ?yc) <= 0  [simp]
  ```
  `min(3,5)` folds to `3` at compile time; `min(?age, ?thr)` residualizes to a runtime `min`. One rule set, two phases (the `[simp]` equations are both `min`'s definition and its partial evaluator).
- **Termination** — recursive value rules need a strategy (LHS-size > RHS-size, or depth limit + diagnostic). Commutativity-type laws must stay bare (non-`[simp]`) or the phase loops.
- Function-macros (operations over `Expr`), AD, and DSL dispatch are later still — all on the same engine.

---

## Implementation plan (Part 1)

1. **Spike: confirm the typer interposition point.** Validate that `[simp]` rule firing can be hooked into `type_check_node`'s work loop with bottom-up order and `Synthesized` re-typing. (Typer reentrancy already holds — `type_check_node` exists.)
2. **`dot_apply` node**: add the `Expr` variant (`node_occurrence.rs`) and the reflect entity (`reflect.anthill`).
3. **Converter**: emit `dot_apply` for variable-receiver `field_access` (bare and call forms); keep sort/namespace flattening.
4. **`find_operation_on_sort`** builtin (tier 1 first; tier 2 import-scoped).
5. **Engine**: hook `[simp]`-rule firing into the typer; `Synthesized` origin; re-type.
6. **Prelude rules**: `default_dot`, `dot_field`.
7. **Diagnostics**: no-match error with source span; field-vs-method collision lint.
8. **Tests**: chaining (`xs.map(f).filter(p)`), field access (`p.x`), no-import resolution, error cases, byte-identical existing behavior for `Foo.bar` / `?x.field`-as-field.

## Interactions

- **Interpreter IR (`interpreter-ir.md`)**: independent on the compile path — rewriting completes during typing, before IR lowering, so the IR never sees `dot_apply`. Shared concern (pre-existing, surfaced by Part 2): operations defined purely by `[simp]` rules have no body to lower; the IR doc tracks this as an open question.
- **Existing `field_access`/qualified-name handling**: preserved. Part 1 reroutes only the *value-receiver* dot forms through `dot_apply`; sort/namespace receivers are untouched.

## Open questions

Carried from the brainstorm; the ones live for Part 1 are marked **(P1)**.

- **(P1) Identifier-receiver disambiguation.** `Foo.bar` where `Foo` could be a sort *or* a value — Part 1 keeps the qualified-name path; a later pass may reroute value-typed identifier receivers to `dot_apply`. Decide the resolution-time trigger.
- **(P1) Tier-2 import semantics.** Confirm `find_operation_on_sort` checks tier-2 visibility against the current scope, and when.
- **(P1) Diagnostics.** No-match error wording; later, delegation-chain walking.
- **Scope of a simp set** (global / per-namespace / named) — relevant once non-prelude `[simp]` rules proliferate.
- **Part 2**: `constant_fold` folding power (literal-only / ground / full SLD); termination strategy; rule firing specificity when multiple value rules match one redex; re-check vs re-infer for carried-over subterms.
- **Delegation** (Either elimination + effect propagation) and **DSL dispatch** — later layers on the engine.

## Non-goals

- Changing the grammar (`.` already parses).
- Delegation, DSLs, AD, function-macros, `constant_fold` — not in Part 1.
- Replacing `field_access` (Part 1 reaches it via `dot_field`, builtin unchanged).
