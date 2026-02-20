# Proposal 006: Sort/Namespace Separation and Sort-Based Instantiation

**Status:** Steps 1–3 implemented; Step 4 (resolve pass) pending
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

The inline type expression `Name{bindings}` is the sole mechanism for sort parameter binding in type positions:

```
entity Project(
  tools  : List{T = String},
  modules: Option{T = Module}
)
```

### 4. `requires` for sort-level constraints

The `requires` keyword already means "precondition" on operations:

```
operation withdraw(a: Account, m: Money) -> Account
  requires gt(m, zero-val), gte(balance(a), m)
```

The same keyword works at the sort level — a **precondition for instantiation**:

```
sort Ordered {
  sort T
  requires Eq{T}              -- to instantiate Ordered, T must have Eq
  operation gt(a: T, b: T) -> Bool
  ...
}
```

This is uniform: `requires` = "this must be satisfied before you can use this."

| Level | Syntax | Meaning |
|-------|--------|---------|
| Operation | `requires gt(m, zero-val)` | Precondition to **call** the operation |
| Sort | `requires Eq{T}` | Precondition to **instantiate** the sort |

Note the distinction from `sort T` (which **declares** a new abstract parameter). `requires Eq{T}` **references** an existing sort with bindings — it's a constraint, not a declaration. The punned form `Eq{T}` is shorthand for `Eq{T = T}` when the parameter name matches a type in scope.

### 5. Typeclass-like patterns are expressible as sorts

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
  requires Eq{T}
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
  requires Ordered{T}
  operation add(a: T, b: T) -> T
  operation sub(a: T, b: T) -> T
  operation mul(a: T, b: T) -> T
  operation zero-val() -> T
  rule add_comm: add(?a, ?b) = add(?b, ?a)
  rule add_assoc: add(add(?a, ?b), ?c) = add(?a, add(?b, ?c))
  rule add_identity: add(?a, zero-val) = ?a
}
```

The chain `Numeric → Ordered → Eq` is expressed entirely through `requires`. No import-level binding needed.

### 6. Interface satisfaction is a Horn clause

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
    requires Numeric{T = Money}
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

Usage: `List{T = Int}` in type position.

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
  requires Functor{F = M}           -- Monad requires Functor
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

-- Sort body gains 'requires' for sort-level constraints:
SortContent ::= ... | 'requires' TypeExpr

-- Import simplified (no where clause):
Import ::= 'import' Name ['.' '{' NameList '}']
```

Soft keywords: replace `domain` with `namespace`.

The `requires` keyword is already a soft keyword (used in operations). At sort level, `requires Eq{T}` is a sort-level constraint — a precondition for instantiation. Sort bindings support punning: `Eq{T}` = `Eq{T = T}`.

## Relationship to existing systems

| Anthill | Maude | Scala 3 | Haskell |
|---------|-------|---------|---------|
| `sort Eq { sort T; ... }` | `fth EQ { sort T; ... }` | `trait Eq[T]` | `class Eq a` |
| `requires Eq{T = Money}` | `view Eq(Money)` | `given Eq[Money]` | `instance Eq Money` |
| `Name{T=Int}` (type expr) | sort instantiation | `List[Int]` | `List Int` |
| `namespace` | `fmod` (flat module) | `package` / `object` | `module` |
| `import` | `protecting` / `including` | `import` | `import` |

## Implementation path

1. **Rename `domain` → `namespace`** in grammar, parser, converter, loader — **done** (31b05f0)
2. **Move prelude specs from `domain` to `sort`** (Eq, Ordered, Numeric) — **done** (b925da4)
3. **Add `requires` at sort level** — parse as sort-level constraint, loader emits `Requirement` facts — **done** (e005ede). Also added sort-binding punning: `Eq{T}` = `Eq{T = T}` (d7dbcb3).
4. **Validate `Name{bindings}` and `requires` constraints** — not a separate compiler pass; well-formedness checks (valid sort references, valid parameter names, arity) are expressed as constraint rules in the KB. Errors surface through the standard denial/constraint mechanism.

Steps 1–3 are complete. Step 4 is prelude content (constraint rules), not a compiler change.

## Backwards compatibility

- `domain` keyword replaced by `namespace` — existing files need updating
- `import ... where` removed — inline `Name{bindings}` and `requires` replace it
- All algebraic specs (Eq, Ordered, Numeric) become sorts — no behavioral change, just keyword
