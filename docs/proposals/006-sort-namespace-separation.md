# Proposal 006: Sort/Namespace Separation and Sort-Based Instantiation

**Status:** Draft
**Depends on:** [001-sort-domain-unification](001-sort-domain-unification.md), [001.1-sort-members-and-kb-duality](001.1-sort-members-and-kb-duality.md)
**Affects:** Kernel Language Specification §4.4, §5.1, §5.2, §8.7, §9, §11

## Motivation

Proposal 001 unified sorts and domains syntactically: `sort X { ... }` can contain everything a domain can. But `domain` retained a dual role — algebraic specification AND namespace — creating confusion around `import ... where`:

- `import X` = load/reference a domain (visibility)
- `where { T = Int }` = instantiate sort parameters (algebraic)

These are fundamentally different operations bundled into one syntax. The `where` clause on `import` conflated file loading with parametric instantiation.

Additionally, specifications like `Eq`, `Ordered`, and `Numeric` are currently `domain` declarations but behave as sorts — they define abstract sort parameters, operations, and rules. They're algebraic specifications, not namespaces.

## Proposal

### 1. Two constructs with distinct roles

**`sort`** — algebraic structure: types, parameters, operations, rules, constructors.

**`namespace`** (replaces `domain`) — organization: grouping, visibility, scoping.

```
sort Eq {
  sort T
  operation eq(a: T, b: T) -> Bool
  operation neq(a: T, b: T) -> Bool
  rule neq(?a, ?b) = not(eq(?a, ?b))
}

namespace anthill.prelude {
  sort Eq { ... }
  sort List { ... }
  sort Option { ... }
}
```

### 2. Import is purely visibility

`import` makes names from another namespace accessible. No instantiation, no `where` clause:

```
Import ::= 'import' Name ['.' '{' NameList '}']
```

### 3. Instantiation is purely sort-level via `Name{bindings}`

The inline type expression `Name{bindings}` is the sole mechanism for sort parameter binding. It works in two positions:

**a) Type expressions** — binding sort parameters in fields and signatures:

```
entity Project(
  tools  : List{T = String},
  modules: Option{T = Module}
)
```

**b) Sort member declarations** — expressing typeclass-like requirements:

```
sort Ordered {
  sort T
  sort Eq{T = T}              -- "T has an Eq" — requirement
  operation gt(a: T, b: T) -> Bool
  ...
}

sort Money {
  sort Numeric{T = Money}     -- Money has numeric operations
  entity dollars(amount: Int)
}
```

A `sort Eq{T = T}` inside Ordered's body means: "an instance of Eq for my T is part of my structure." This is analogous to Scala's `given Eq[T]` or Haskell's `(Eq a) =>` constraint.

### 4. Typeclass-like patterns are expressible as sorts

Specifications with abstract sort parameters ARE sorts:

```
sort Eq {
  sort T
  operation eq(a: T, b: T) -> Bool
  operation neq(a: T, b: T) -> Bool
  rule neq(?a, ?b) = not(eq(?a, ?b))
}

sort Ordered {
  sort T
  sort Eq{T = T}
  operation gt(a: T, b: T) -> Bool
  operation gte(a: T, b: T) -> Bool
  operation lt(a: T, b: T) -> Bool
  operation lte(a: T, b: T) -> Bool
  rule lt(?a, ?b) = gt(?b, ?a)
  rule lte(?a, ?b) = gte(?b, ?a)
  rule gte(?a, ?b) = not(lt(?a, ?b))
  constraint antisymmetric: gt(?a, ?b), gt(?b, ?a)
}

sort Numeric {
  sort T
  sort Ordered{T = T}
  operation add(a: T, b: T) -> T
  operation sub(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T
  operation zero-val() -> T
  rule add_comm: add(?a, ?b) = add(?b, ?a)
  rule add_assoc: add(add(?a, ?b), ?c) = add(?a, add(?b, ?c))
  rule add_identity: add(?a, zero-val) = ?a
}
```

The chain `Numeric → Ordered → Eq` is expressed entirely through sort member declarations. No import-level binding needed.

### 5. Interface satisfaction is a Horn clause

"Does X satisfy Y?" can be expressed as a rule over `member` facts (from proposal 001.1):

```
rule satisfies(?X, ?Y) :-
    member(?Name, ?Kind, ?Y),
    member(?Name, ?Kind, ?X)
```

This is a KB query, not a built-in mechanism. It can be refined, extended, or overridden.

## Examples

### Banking domain

```
namespace banking {
  sort Money {
    sort Numeric{T = Money}
    entity dollars(amount: Int)
  }

  sort Account {
    entity Account(id: String, balance: Money)
    operation deposit(a: Account, m: Money) -> Account
      requires gt(m, zero-val)
      ensures eq(balance(result), add(balance(a), m))
    operation withdraw(a: Account, m: Money) -> Account
      requires gt(m, zero-val), gte(balance(a), m)
      ensures eq(balance(result), sub(balance(a), m))
    operation balance(a: Account) -> Money
  }
}
```

### Prelude list

```
namespace anthill.prelude {
  sort List {
    sort T
    entity nil
    entity cons(head: T, tail: List)
    operation length(l: List) -> Nat
    rule length(nil) = zero
    rule length(cons(?x, ?xs)) = succ(length(?xs))
  }
}
```

Usage: `List{T = Int}` in type position, or `sort List{T = Int}` as a member declaration.

### Functor / Monad

```
sort Functor {
  sort F
    sort T
  end
  operation map(c: F, f: T -> U) -> F{T = U}
}

sort Monad {
  sort M
    sort T
  end
  sort Functor{F = M}           -- Monad requires Functor
  operation return(x: T) -> M
  operation bind(m: M, f: T -> M{T = U}) -> M{T = U}
  rule bind(return(?x), ?f) = ?f(?x)
}
```

## Grammar changes

```
-- Replace:
Domain ::= 'domain' Name ...

-- With:
Namespace ::= 'namespace' Name
                Import*
                ['export' NameList]
              Body[NamespaceContent*]

NamespaceContent ::= Sort | Namespace | Rule | Operation
                   | Entity | Fact | Constraint
                   | OperationBlock | RuleBlock

-- Sort unchanged (already supports full body from 001)

-- Import simplified (no where clause):
Import ::= 'import' Name ['.' '{' NameList '}']
```

Soft keywords: replace `domain` with `namespace`.

## Relationship to existing systems

| Anthill | Maude | Scala 3 | Haskell |
|---------|-------|---------|---------|
| `sort Eq { sort T; ... }` | `fth EQ { sort T; ... }` | `trait Eq[T]` | `class Eq a` |
| `sort Eq{T=Money}` (member) | `view Eq(Money)` | `given Eq[Money]` | `instance Eq Money` |
| `Name{T=Int}` (type expr) | sort instantiation | `List[Int]` | `List Int` |
| `namespace` | `fmod` (flat module) | `package` / `object` | `module` |
| `import` | `protecting` / `including` | `import` | `import` |

## Implementation path

1. **Rename `domain` → `namespace`** in grammar, parser, converter, loader
2. **Move prelude specs from `domain` to `sort`** (Eq, Ordered, Numeric)
3. **Implement `sort X{T=Y}` as member declaration** — the loader already produces member facts; a parameterized sort reference in member position creates a requirement
4. **Resolve `Name{bindings}` at use sites** — separate resolve pass

Steps 1-2 are mechanical. Steps 3-4 require the resolve pass discussed in 001.1.

## Backwards compatibility

- `domain` keyword replaced by `namespace` — existing files need updating
- `import ... where` removed — inline `Name{bindings}` and sort member declarations replace it
- All algebraic specs (Eq, Ordered, Numeric) become sorts — no behavioral change, just keyword
