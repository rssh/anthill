# 015: Universal Type Variables (`?` in Field Types)

## Status: Proposal

## Depends on: none (composes with 014 Union Types)

## Motivation

Currently, `Term` (an abstract sort: `sort Term = ?`) serves as the universal/"top" type in reflect entities:

```anthill
entity Requires(sort_ref: Term, spec: Term)
entity EntityOf(entity: Term, parent: Term)
entity SortInfo(name: Symbol, definition: Term, ...)
```

This says nothing about what these fields actually accept. `Term` is an opaque handle — using it everywhere is like typing everything as `Object` in Java.

Anthill already has `?` (anonymous) and `?Name` (named) logical variables in sort definitions (`sort T = ?`). The same syntax should work in field types: `?` means "any type", `?X` means "named type parameter".

## Design

### Syntax

`?` and `?Name` in field type positions, operation signatures, and return types:

```anthill
-- Anonymous: each field accepts any type independently
entity EntityOf(entity: ?, parent: ?)

-- Named: type parameters scoped to the entity
entity Pair(a: ?A, b: ?B)

-- Shared: same ?T across fields means same type
entity Mapping(key: ?K, value: ?V)

-- In operations
operation identity(x: ?T) -> ?T
```

### Semantics

- `?` in type position means "any type" — the universal constraint (accepts anything). Each occurrence is independent (like `_` in pattern matching).
- `?X` in type position introduces a named type parameter scoped to the enclosing entity or operation. Multiple occurrences of `?X` within the same scope refer to the same type.

### Relationship to `sort T = ?`

This generalizes the existing mechanism:

| Current | Generalized | Meaning |
|---------|-------------|---------|
| `sort T = ?` | `field: ?` | any type |
| `sort T = ?Name` | `field: ?Name` | named type param |
| `sort T = Int` | `field: Int` | concrete type |

The `sort T = ?` declaration inside a sort body is still needed for type parameters that appear in `requires` clauses or need to be bound via `Name{T = Int}` syntax. But for simple field types, `?` eliminates the need for a separate declaration.

### Implementation Status

The grammar already supports this: `field_decl` uses `$._type` which includes `$.variable_term`. The converter handles `"variable_term"` → `TypeExpr::Variable`, and the loader handles `TypeExpr::Variable` → `Term::Var(vid)`. So `entity Foo(x: ?)` already parses and loads — the Var term unifies with anything, giving the desired "any type" semantics.

What remains:
- Verify end-to-end with tests
- Decide on scoping rules for named variables (`?X` shared within entity vs across entities)
- Compose with union types (014): `field: Ref | SortView` uses concrete union, `field: ?` uses universal variable

### Impact on reflect entities

With universal `?`, reflect entities become:

```anthill
entity EntityOf(entity: ?, parent: ?)
entity Requires(sort_ref: ?, spec: ?)   -- or spec: Ref | SortView with 014
```

## Relationship to Other Proposals

- **014 (Union Types)**: Composes naturally. `field: ? | A` mixes universal variables with unions. `field: Ref | SortView` is precise; `field: ?` is universal.
- **011 (Type Resolution)**: Type checking of `?` fields is trivial — a Var unifies with anything, so `type_compatible(X, ?)` always succeeds.
