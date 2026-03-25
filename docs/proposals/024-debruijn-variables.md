# Proposal 024: De Bruijn Variable Representation

**Status:** Proposed
**Depends on:** Proposal 023 (KB Guards — quantifiers)
**Affects:** Term representation, loader, resolver, hash-consing, caching

## Motivation

The current variable representation uses globally unique `VarId(u32)` for all
variables. This causes two problems:

1. **Alpha-equivalent terms aren't equal.** Two patterns like
   `Delivered(agent: ?_42, at: ?_43)` and `Delivered(agent: ?_99, at: ?_100)`
   are structurally different — they can't be hash-consed together, and cache
   lookups fail.

2. **Quantifiers need proper binding.** With quantified goals in rule bodies
   (WI-027: `forall ?x in list: P(?x)`), we have nested binders. Variable
   identity must be relative to its binder, not globally named.

## Design

### Two variable kinds

```rust
enum Var {
    DeBruijn(u32),    // bound variable: index relative to enclosing binders
    Global(VarId),    // free variable during resolution: unique per instantiation
}
```

**Stored terms** (in KB) use `DeBruijn`. **Runtime terms** (during resolution)
use `Global` for opened (instantiated) variables.

### Rules as implicit binders

A rule implicitly binds its free variables. The rule:

```anthill
rule foo(?x, ?y) :- P(?x, ?y), forall ?z: Q(?z, ?y)
```

Is semantically:

```
forall ?x. forall ?y. (foo(?x, ?y) :- P(?x, ?y), forall ?z. Q(?z, ?y))
```

With de Bruijn indices (curried single-variable binders):

```
forall. forall. (foo(1, 0) :- P(1, 0), forall. Q(0, 1))
```

- Free variables become the outermost binders (N binders for N free vars)
- Explicit quantifiers (`forall ?z`) add inner binder levels
- Inside a binder, all outer indices shift up by 1

### Variable occurrence rules

| Context | `?x` (1st free) | `?y` (2nd free) | `?z` (bound by forall) |
|---|---|---|---|
| At rule level | db(1) | db(0) | — |
| Inside `forall ?z` | db(2) | db(1) | db(0) |
| Inside `forall ?z: forall ?w:` | db(3) | db(2) | db(1) |

### Resolution: opening binders

When the resolver selects a rule clause, it **opens** the outermost N binders
by replacing `DeBruijn(0..N-1)` with fresh `Global(VarId)` values:

```
Stored:    foo(db1, db0) :- P(db1, db0), forall. Q(db0, db1)
Opened:    foo(?_42, ?_43) :- P(?_42, ?_43), forall. Q(db0, ?_43)
```

- `db1` → `?_42` (fresh global for first free var)
- `db0` → `?_43` (fresh global for second free var)
- `db0` inside `forall` is NOT opened — it's bound by the inner quantifier

When the resolver enters a `forall` body, it opens that binder's `db0` to
a new fresh global.

### Anonymous variables

The anonymous variable `?` is just `DeBruijn(0)` bound by an implicit
single-use binder around the term it appears in. Each `?` occurrence is
a separate implicit binder:

```anthill
Delivered(agent: ?, at: ?)
```

Desugars to:

```
forall. forall. Delivered(agent: db1, at: db0)
```

This means two patterns with different `?` variables become structurally
identical after de Bruijn encoding — hash-consing deduplicates them.

### Hash-consing benefits

With de Bruijn indices, `Term::Var(DeBruijn(n))` is canonical:

- `P(?x, ?y)` in rule 1 and `P(?a, ?b)` in rule 2 → same `TermId`
- `Delivered(agent: ?, at: ?)` everywhere → same `TermId`
- Cache lookup by `TermId` finds alpha-equivalent goals

### Impact on existing code

#### Term representation (`kb/term.rs`)

```rust
// Current:
pub struct VarId { id: u32, name: Symbol }
enum Term { ..., Var(VarId), ... }

// New:
pub enum Var {
    DeBruijn(u32),
    Global(VarId),
}
enum Term { ..., Var(Var), ... }
```

`VarId` stays for globals (used during resolution). `DeBruijn(u32)` is new
for stored terms.

#### Loader (`kb/load.rs`)

After loading a rule/fact, convert free variables to de Bruijn:
1. Collect all variables in the rule (order of first occurrence)
2. Replace each `VarId` with `DeBruijn(N - 1 - index)` (outermost = highest index)
3. Store the arity N alongside the rule (needed for opening)

#### Resolver (`kb/resolve.rs`)

When selecting a candidate rule:
1. Read arity N from the rule
2. Allocate N fresh `Global(VarId)` values
3. Walk the rule's head and body, replacing `DeBruijn(i)` with the
   corresponding global (adjusted for nesting depth)
4. Proceed with unification as before (globals only)

When entering a quantified goal body:
1. Allocate one fresh `Global(VarId)` for the quantifier's variable
2. Walk the body, replacing `DeBruijn(0)` with the new global,
   decrementing all other `DeBruijn(i)` by 1

#### Discrimination tree (`kb/discrim.rs`)

Currently handles `Term::Var(vid)`. Needs to also handle `Var::DeBruijn(n)`.
De Bruijn variables in patterns create variable edges (match anything),
same as current `Var` handling.

#### Per-query caching

With de Bruijn, the cache key for a ground goal is its `TermId` (unique
via hash-consing). For goals with free de Bruijn vars, skip caching
(or canonicalize by treating all de Bruijn vars as equivalent wildcards).

### Migration strategy

1. Add `Var::DeBruijn(u32)` variant to `Var` enum
2. Update `TermStore` hash/eq to handle both variants
3. Update loader to convert free vars to de Bruijn after loading each rule
4. Update resolver to open de Bruijn vars to globals when instantiating rules
5. Update discrimination tree to handle `Var::DeBruijn`
6. Add per-query cache using `TermId` as key for ground goals

Steps 1-2 can be done without changing behavior (existing rules still use
`Global` until step 3 converts them). This allows incremental migration.

### Interaction with quantifiers (WI-027)

Quantifiers in rule bodies (`forall ?x: P -: Q`) create explicit binders.
The loader assigns `DeBruijn(0)` to the quantifier's variable inside its
body. The resolver opens it when evaluating the quantified goal.

This proposal is a prerequisite for WI-027: without de Bruijn indices,
nested quantifier scoping would require ad-hoc scope tracking.

## Open questions

- Should `RuleEntry` store arity explicitly, or derive it from the term?
- Should facts (zero free vars) skip de Bruijn entirely (no conversion needed)?
- Performance: opening a de Bruijn term requires a full walk. Is this
  cheaper than the current fresh-var-per-rule approach? (Likely yes —
  the current approach also walks the term to rename variables.)
