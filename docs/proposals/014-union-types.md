# 014: Union Types (Or-Types)

## Status: Proposal

## Depends on: 011 (Type Resolution)

## Motivation

Field types in anthill entities are currently either concrete sorts (`Int64`, `String`), abstract sorts (`sort T = ?`), or the catch-all `Term`. This lacks precision for cases where a field can hold one of several specific sorts.

Concrete example: the `Requires` entity in `anthill.reflect`:

```anthill
entity Requires(
    sort_ref : Term,    -- always a sort name term
    spec     : Term     -- either Ref(sort) or SortView(sort, bindings...)
)
```

The `spec` field is typed `Term` but actually holds either a `Ref` (simple requires like `requires Eq`) or a `SortView` (parameterized requires like `requires Eq[T = Int64]`). The type `Term` says nothing about this constraint. What we want is:

```anthill
entity Requires(
    sort_ref : Term,
    spec     : Ref | SortView
)
```

This pattern appears elsewhere: any field that can hold one of a few known sorts benefits from a union type rather than the opaque `Term`.

## Design

### Syntax

Add `|` as a type operator in type expressions:

```anthill
-- In field types
entity Requires(spec: Ref | SortView)

-- In operation signatures
operation extract(t: Ref | SortView) -> Symbol

-- In sort definitions (type alias to a union)
sort SpecRef = Ref | SortView
```

The `|` operator is left-associative and has lower precedence than `Name[bindings]`:

```anthill
sort T = A | B[X = Int64] | C    -- (A | B[X = Int64]) | C
```

### Grammar

```js
_type: $ => choice(
    $.simple_type,
    $.parameterized_type,
    $.variable_term,
    $.union_type,
),

union_type: $ => prec.left(1, seq(
    field('left', $._type),
    '|',
    field('right', $._type),
)),
```

### Semantics

`A | B` is a **type constraint** — it means "this position accepts a value of sort A or sort B". No new sort is created in the KB. Union types exist only in type expressions (field types, operation signatures, sort aliases).

This is analogous to TypeScript's union types: `string | number` doesn't create a new type — it constrains what values are accepted.

#### Equivalences

- `A | A` = `A` (idempotent)
- `A | B` = `B | A` (commutative — same constraint)
- `(A | B) | C` = `A | (B | C)` (associative)
- If `entity_of(A, B)`, then `A | B` = `B` (entity is already compatible with its sort)

#### Relationship to sort-with-entities

A sort with entities is a named grouping:

```anthill
sort Color { entity red; entity green; entity blue }
```

Union types allow ad-hoc groupings without a sort declaration: `red | green` constrains to a subset of Color's entities. The difference: sorts exist in the KB as first-class names; union types are purely constraints in type expressions.

### Term Representation

`SortUnion` is a **variadic** kernel functor (like `SortView`), declared in `anthill.reflect`. The loader flattens and normalizes at construction time:

```
A | B | C  →  SortUnion(A_term, B_term, C_term)    -- positional args, sorted by qualified name
```

Flattening: nested `|` in the source is parsed as a binary tree (grammar is left-associative), but the loader collects all leaves and produces a single flat `SortUnion` with sorted positional args. This ensures:

- `A | B` and `B | A` produce the same term (commutativity via sorting)
- `(A | B) | C` and `A | (B | C)` produce the same term (associativity via flattening)
- Duplicates are removed (idempotency)

In `Term::Fn` representation:
```rust
Term::Fn {
    functor: sort_union_sym,
    pos_args: SmallVec::from_slice(&[a_term, b_term, c_term]),  // sorted, deduped
    named_args: SmallVec::new(),
}
```

### Checking

Union type checking integrates with the existing `type_compatible` rules. Since `SortUnion` is variadic, checking uses `list_contains` over the positional args:

```anthill
-- A value of type X is compatible with SortUnion(...arms) if it's compatible with any arm
rule type_compatible(?X, ?union)
    :- extract_sort_union_arms(?union, ?arms),
       list_contains(?arm, ?arms),
       type_compatible(?X, ?arm)

-- A union-typed value is compatible with T if all arms are
-- (checked via negation: no arm is incompatible)
rule type_compatible(?union, ?T)
    :- extract_sort_union_arms(?union, ?arms),
       all_compatible(?arms, ?T)

rule all_compatible(nil(), ?)
rule all_compatible(cons(head: ?arm, tail: ?rest), ?T)
    :- type_compatible(?arm, ?T), all_compatible(?rest, ?T)
```

Alternatively, for the common binary case (`A | B`), direct positional matching also works:

```anthill
rule type_compatible(?X, SortUnion(?A, ?B))
    :- type_compatible(?X, ?A)

rule type_compatible(?X, SortUnion(?A, ?B))
    :- type_compatible(?X, ?B)
```

The variadic representation makes both approaches possible; the loader just needs to ensure consistent flattening.

## Examples

### Reflect entities with precise types

```anthill
entity Requires(
    sort_ref : Term,
    spec     : Ref | SortView
)

-- extract_sort_ref works on both Ref and SortView
operation extract_sort_ref(inst: Ref | SortView) -> Symbol
```

### Domain modeling

```anthill
sort Payment {
    entity CreditCard(number: String, expiry: String)
    entity BankTransfer(iban: String)
    entity Crypto(wallet: String)
}

-- A subset union: only physical payment methods
sort PhysicalPayment = CreditCard | BankTransfer

operation process_physical(p: PhysicalPayment) -> Receipt
```

### Error handling

```anthill
sort Result {
    sort T = ?
    sort E = ?
    entity Ok(value: T)
    entity Err(error: E)
}

-- Multiple error types without a wrapper sort
operation connect(url: String) -> Result[T = Connection, E = Timeout | Refused | DnsError]
```

## Alternatives Considered

### Binary `SortUnion(A, B)` representation

The simplest representation: `A | B | C` becomes `SortUnion(SortUnion(A, B), C)`. The grammar already produces a binary tree (left-associative `|`), so the loader would translate it directly without flattening.

Pros:
- Simpler loader — no flattening/sorting pass needed
- `type_compatible` rules are straightforward (two-arg pattern matching)

Cons:
- `(A | B) | C` and `A | (B | C)` produce structurally different terms, breaking associativity at the term level. The `type_compatible` rules handle both correctly via recursion, but unification and hash-consing see them as distinct.
- `A | B` and `B | A` are different terms — commutativity requires either normalization or extra rules.

This is workable if union types are only checked via `type_compatible` rules (never unified directly). But it's fragile — any future use of union terms in unification contexts would silently break.

### General associative operation representation

The problem of representing associative-commutative (AC) operations in term stores is well-studied. Maude handles AC matching natively in its rewrite engine. A more general approach would be to let any operation declare itself associative (and optionally commutative), with the term store normalizing accordingly.

For example:
```anthill
sort SortUnion
    attribute associative
    attribute commutative
    attribute idempotent
```

This would generalize beyond union types — any AC operation (set union, multiset union, commutative addition) would benefit from canonical representations. However, this is a significant extension to the term store and unification algorithm. AC unification is decidable but substantially more complex than syntactic unification.

The variadic representation chosen for `SortUnion` is a pragmatic middle ground: it handles the specific case of sort unions with simple flattening + sorting, without requiring a general AC unification engine. A general AC framework could be a future proposal that subsumes this one.

## What This Does NOT Cover

- **Intersection types** (`A & B`) — a value that satisfies both. Orthogonal; could be a future proposal.
- **Negation types** (`~A`) — everything except A. Not planned.
- **Pattern matching exhaustiveness** — checking that a match on `A | B` covers both cases. Useful but separate from the type representation.

## Relationship to Other Proposals

- **011 (Type Resolution)**: The `type_compatible` rules need to handle `SortUnion` terms. Union types are a constraint mechanism on top of the existing type resolution.
- **005 (Extends and Inheritance)**: Named inheritance (`sort B extends A`) creates explicit relationships in the KB. Union types are complementary — they are type constraints, not KB relationships.
- **012 (Sort Defined Syntax Sugar)**: `sort S = A | B` uses the same `sort S = ...` syntax as type aliases. Union types give this definition form more expressive power.
- **015 (Universal Type Variables)**: `?` as universal type constraint in field positions. Composes with union types: `field: ? | A` or `field: Ref | SortView`. Separate but complementary.
