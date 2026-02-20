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

Sort declarations gain an optional body. The body uses the same `Body[...]` delimiters as domains (`{ ... }` or `... end`):

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
       | [Visibility] 'sort' Name Body[SortContent*]
           ['meta' ':' Meta]                                    -- NEW: sort with body

SortContent ::= Sort                    -- sub-sorts (parameters)
              | Entity                  -- constructors
              | Operation               -- methods
              | Rule                    -- laws
              | Fact                    -- ground assertions
              | Constraint             -- integrity constraints
              | OperationBlock          -- grouped methods
              | RuleBlock               -- grouped laws
              | Import                  -- imports into the sort's domain
```

`SortContent` is identical to `DomainContent` (§5.1). A sort with a body IS a domain.

## Relationship Between `sort` and `domain`

| Declaration | Has primary sort? | Usable as type? | Usable with `{...}`? |
|-------------|------------------|-----------------|---------------------|
| `sort X` (abstract, no body) | X itself | Yes | Only if has sub-sorts |
| `sort X { ... }` (with body) | X itself | Yes | Yes |
| `sort X = { entity ... }` (ADT) | X itself | Yes | Only if has sub-sorts |
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

## The Defined ADT Form as Sugar

The existing `sort X = { entity ... }` form is sugar for a body containing only constructors:

```
sort Option = { entity none, entity some(value: T) }

-- equivalent to:

sort Option
  entity none
  entity some(value: T)
end
```

Both forms remain valid. The `= { ... }` form is concise for pure ADTs without operations or parameters.

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
  sort List = {
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

The inner `sort List = { ... }` nesting is eliminated. Entities belong directly to the sort.

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
- `sort X = { entity ... }` (defined ADT) — unchanged, now sugar for body-only-constructors form.
- `domain D { ... }` — unchanged, remains available for multi-sort modules.
- `Name{T=X}` inline binding — unchanged in syntax, now works uniformly because every sort is a domain.
- `import D where { T = X }` — unchanged, extended to support sort-constructor binding.

No existing valid program is invalidated by this change.
