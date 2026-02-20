# Proposal 001: Sort/Domain Unification

**Status:** Draft
**Affects:** Kernel Language Specification §4.4, §5.1, §5.2, §8.6, §11

## Motivation

The kernel language has two parallel structuring mechanisms: **sorts** (type declarations) and **domains** (modules). The same-name convention (§4.4) allows a domain and its primary sort to share a name, but this is a naming pattern, not a language rule.

This creates a gap. The inline type expression `Name{T=X}` (§4.4) is a **domain-level** mechanism — it binds abstract sorts declared within a domain. An abstract sort `sort F` has no associated domain, so `F{T=A}` is meaningless: there is no domain to look up `T` in.

This prevents expressing type constructors. A parametric type like `List` works with `{...}` because it is defined inside a domain (`domain anthill.prelude.List`). But an **abstract** type constructor — "some type `F` parameterized by `T`" — cannot be expressed, because abstract sorts are not domains.

## The Rule

**Every `sort X` declaration implicitly defines a `domain X` with the same name.**

This elevates the same-name convention from a naming pattern to a language rule:

- Sorts declared inside `sort X`'s body are sorts within `domain X` (parameters).
- Entities inside `sort X`'s body are constructors of sort `X`.
- Operations and rules inside `sort X`'s body belong to `domain X`.
- `X{T=A}` is valid inline binding because `X` is a domain with sort `T`.

## Grammar Changes

Sort declarations gain an optional body. The structure mirrors the domain grammar (§5.1): imports and exports in the header, content in the body.

```
-- BEFORE:
Sort ::= [Visibility] 'sort' Name
           ['meta' ':' Meta]
       | [Visibility] 'sort' Name '=' Body[Constructor*]
           ['meta' ':' Meta]

-- AFTER:
Sort ::= [Visibility] 'sort' Name
           ['meta' ':' Meta]                                    -- abstract (unchanged)
       | [Visibility] 'sort' Name '=' Body[Constructor*]
           ['meta' ':' Meta]                                    -- defined ADT (unchanged)
       | [Visibility] 'sort' Name                               -- NEW: sort with body
           Import*
           ['export' NameList]
         Body[SortContent*]
           ['meta' ':' Meta]

SortContent ::= Sort                    -- sub-sorts (parameters)
              | Entity                  -- constructors
              | Operation               -- methods
              | Rule                    -- laws
              | Fact                    -- ground assertions
              | Constraint             -- integrity constraints
              | OperationBlock          -- grouped methods
              | RuleBlock               -- grouped laws
              | Domain                  -- nested domains (sub-modules)
```

`SortContent` is identical to `DomainContent` (§5.1). A sort with a body IS a domain. Everything a domain can contain, a sort can contain — including nested domains and nested sorts. Imports and exports appear in the header, just as in domains.

**Note:** The `extends` clause has been removed from the domain grammar (§5.1) due to unclear semantics — `import` covers all known use cases. This proposal does not introduce `extends` for sorts either.

### Nesting

A nested `sort T` (abstract, no body) serves as a **type parameter**. A nested `sort S { ... }` (with body) is a **nested type definition** within the sort's namespace. A nested `domain D { ... }` is a **sub-module** — useful for grouping related operations without introducing a new type:

```
sort List
  sort T
  entity nil
  entity cons(head: T, tail: List)

  -- Nested domain groups operations without being a type:
  domain traversal
    operation length(l: List) -> Nat
    operation reverse(l: List) -> List
    rule length(nil) = zero
    rule length(cons(?x, ?xs)) = succ(length(?xs))
  end
end
```

### Lexical Scoping

Nested content (sub-sorts, nested domains) can reference names from enclosing scopes. This is standard lexical scoping:

```
sort List
  sort T                                    -- parameter
  entity cons(head: T, tail: List)          -- references T and List

  domain traversal
    operation head(l: List) -> T            -- references List and T from enclosing sort
  end
end
```

### Constructor Scope

An entity is a constructor of sort `X` only if it appears **directly** in `X`'s body — not inside a nested domain or nested sort:

```
sort Expr
  entity Var(name: String)                  -- constructor of Expr ✓
  entity Add(left: Expr, right: Expr)       -- constructor of Expr ✓

  domain helpers
    entity ParseError(message: String)      -- NOT a constructor of Expr (its own sort)
  end
end
```

This preserves the closed ADT property: the set of constructors is exactly what appears directly in the sort body, regardless of nested content.

## Relationship Between `sort` and `domain`

| Declaration | Has primary sort? | Usable as type? | Usable with `{...}`? |
|-------------|------------------|-----------------|---------------------|
| `sort X` (abstract, no body) | X itself | Yes | Only if has sub-sorts |
| `sort X { ... }` (with body) | X itself | Yes | Yes |
| ~~`sort X = { entity ... }` (ADT)~~ | *(removed, use `sort X { entity ... }` instead)* | | |
| `domain D { ... }` | Only by convention | Only if primary sort exists | Yes |

The `domain` keyword remains for multi-sort modules that are not themselves types:

```
domain banking                          -- not a type, just a namespace
  sort Account
  sort Money
  operation deposit(...) -> Account
end
```

- `sort` = module with a primary type.
- `domain` = module without a primary type.
- One mechanism, two entry points.

## Name Uniqueness

**A name may be declared as either a `sort` or a `domain` in the same scope, not both.** Declaring both `sort X` and `domain X` in the same scope is an error.

Rationale: since `sort X` already implicitly defines `domain X`, a separate `domain X` declaration would either conflict or require "reopening" semantics. Reopening would introduce complexity (what can be added? can constructors be added, breaking closed ADT?) without sufficient benefit.

### Separating Structure from Behavior

When a sort's definition becomes large, or when operations on a sort are defined separately (e.g., in a different file or by a different agent), use a **companion domain** — a separate domain that imports the sort:

```
-- Type structure (defines the sort and its constructors):
sort Option
  sort T
  entity none
  entity some(value: T)
end

-- Companion domain (adds operations, defined separately):
domain Option-ops
  import Option
  operation get_or(o: Option, default: T) -> T
  rule get_or(some(?x), ?d) = ?x
  rule get_or(none, ?d) = ?d
end
```

This is analogous to Scala's companion objects (`trait X` + `object X`) or Maude's extending modules. The companion domain has full access to the sort's constructors via `import`.

**Naming convention:** No fixed convention is prescribed at this stage. Projects may use `X-ops`, `X-companion`, or any other name. If a dominant pattern emerges, syntactic sugar may be introduced in a future proposal — for example, a `companion` block within a sort declaration that desugars to a separate domain with an implicit import:

```
-- Possible future sugar (not part of this proposal):
sort Option
  sort T
  entity none
  entity some(value: T)
companion
  operation get_or(o: Option, default: T) -> T
  rule get_or(some(?x), ?d) = ?x
  rule get_or(none, ?d) = ?d
end

-- Would desugar to the two-declaration form above.
```

This sugar is deferred — it can be added without breaking changes once usage patterns stabilize.

## The `= { ... }` Form (Removed)

The `sort X = { entity ... }` form has been removed. All sorts with bodies use the unified syntax:

```
sort Option {
  entity none
  entity some(value: T)
}

-- or with end-delimiter:
sort Option
  entity none
  entity some(value: T)
end
```

## Open vs. Closed Sorts

- **Closed** (has entity declarations): exactly the listed constructors exist. Pattern matching is exhaustive.
- **Abstract/open** (no entity declarations): carrier is provided by an implementation or left unbound.

```
sort Nat                                -- closed: has constructors
  entity zero
  entity succ(pred: Nat)
end

sort Scalar                             -- open: carrier TBD

sort F                                  -- open + parameterized: abstract type constructor
  sort T
end
```

## Kind Checking

With sort/domain unification, inline bindings `X{T=A}` require kind compatibility:

- If `sort X` has no sub-sorts (no parameters), `X{...}` is an error — nothing to bind.
- If `sort X` has `sort T`, then `X{T=A}` is valid when `A` has the correct kind.
- Binding a parameterized sort to another: `where { F = Option }` requires `F` and `Option` to have the same parameter structure.

Kind inference: a sort's kind is determined by its parameter declarations.

- `sort X` with no sub-sorts has kind `*`.
- `sort F` with `sort T` inside has kind `* -> *`.
- `sort G` with `sort A, sort B` inside has kind `* -> * -> *`.

The parameter name is part of the interface — `F{T=A}` requires `F`'s domain to have a sort named `T`.

## Parameter Name Coupling

The inline binding `F{T=A}` depends on the parameter name `T`. When binding `F` to a concrete sort, the parameter names must align.

**Convention (recommended):** parametric sorts use `T` for single type parameters. The prelude already follows this convention.

**Renaming in `where`:** when names differ, the `where` clause maps them:

```
-- If MyCollection uses 'Elem' instead of 'T':
import SomeSpec where { F = MyCollection { T = Elem } }
```

This is the standard Maude view mechanism — a mapping between the abstract domain's sorts and the concrete domain's sorts.

## Revised Prelude Types

With the unification, prelude definitions become self-contained sorts:

```
-- BEFORE (current spec):
domain anthill.prelude.List
  export List, nil, cons, length
  sort T
  sort List {
    entity nil
    entity cons(head: T, tail: List)
  }
  operation length(l: List) -> Nat
  rule length(nil) = zero
  rule length(cons(?x, ?xs)) = succ(length(?xs))
end

-- AFTER (unified):
sort List
  export List, nil, cons, length
  sort T
  entity nil
  entity cons(head: T, tail: List)
  operation length(l: List) -> Nat
  rule length(nil) = zero
  rule length(cons(?x, ?xs)) = succ(length(?xs))
end
```

The inner `sort List { ... }` nesting is eliminated. Entities belong directly to the sort.

```
-- Option:
sort Option
  sort T
  entity none
  entity some(value: T)
end

-- Nat:
sort Nat
  entity zero
  entity succ(pred: Nat)
end

-- Pair:
sort Pair
  sort A
  sort B
  entity Pair(fst: A, snd: B)
end
```

## Type Constructor Application

Abstract type constructors can now be declared and applied:

```
-- Declare an abstract type constructor:
sort F
  sort T
end

-- Apply it via inline binding:
F{T = Int}                              -- F applied to Int
F{T = F{T = Int}}                       -- F applied to F(Int) — nested application

-- Bind it in 'where' clauses:
import SomeSpec where { F = Option }
-- Now F{T=A} resolves to Option{T=A}
```

This is the key enabler for higher-order sort specifications (monads, functors, etc.), developed in Proposals 002 and 003.

## Example: Banking with Unified Sorts

```
sort Money
  import anthill.prelude.Numeric where { T = Money }
  -- Money is abstract — carrier provided by implementation.
  -- Numeric gives us add, sub, mul, gt, gte, lt, lte, eq, zero-val.
end

sort Account
  entity Account(id: AccountId, balance: Money)

  operation balance(a: Account) -> Money

  operation deposit(a: Account, m: Money) -> Account
    requires gt(m, zero-val)
    ensures eq(balance(result), add(balance(a), m))

  operation withdraw(a: Account, m: Money) -> Account
    requires gt(m, zero-val), gte(balance(a), m)
    ensures eq(balance(result), sub(balance(a), m))

  constraint non_negative: gte(balance(?a), zero-val)
end
```

## Backwards Compatibility

All existing syntax remains valid:

- `sort X` (abstract) — unchanged.
- ~~`sort X = { entity ... }` (defined ADT)~~ — removed, use `sort X { entity ... }` body form instead.
- `domain D { ... }` — unchanged, remains available for multi-sort modules.
- `Name{T=X}` inline binding — unchanged in syntax, now works uniformly because every sort is a domain.
- `import D where { T = X }` — unchanged, extended to support sort-constructor binding.

No existing valid program is invalidated by this change.
