# Proposal 005: Reintroducing `extends` and Sort Inheritance

**Status:** Deferred (draft for future consideration)
**Depends on:** [001-sort-domain-unification](001-sort-domain-unification.md)
**Affects:** Kernel Language Specification §5.1, §5.2, §8.1

## Background

The `extends` keyword was removed from the domain grammar due to unclear semantics — `import` covers the known use cases for bringing declarations into scope. This proposal explores reintroducing `extends` with precise semantics based on sort inheritance (subtyping).

## Proposed Semantics

`extends A` in sort/domain `B` means:

1. **All operations defined in A become operations defined in B** (as if imported, but also re-exported as part of B's interface).
2. **Sort A is a subtype of B**: `A <: B` — values of sort A can be used wherever sort B is expected.

```
sort B
  extends A
  -- all operations from A are available in B
  -- A <: B (subtyping relation)
end
```

## Open Questions

### 1. Constructors / cases

If `sort A` has constructors and `sort B` has constructors, and `B extends A`:

```
sort Animal
  entity dog
  entity cat
end

sort Pet
  extends Animal
  entity goldfish
end
```

Does `Pet` have constructors `{dog, cat, goldfish}`? Is `Animal <: Pet` (every animal is a pet)? That's semantically wrong — not every animal is a pet.

Or is the direction reversed: `Pet <: Animal` (every pet is an animal)? Then `extends` means "is a subtype of", not "inherits from". But then `goldfish` would need to be a constructor of `Animal` too, which breaks `Animal`'s closed ADT.

The OOP and algebraic traditions conflict here:
- **OOP**: `Pet extends Animal` means Pet is a subtype of Animal, Pet may add methods. Constructors are not closed.
- **Algebraic**: sorts are closed ADTs. Subtyping = subset of constructors, not extension.

### 2. Direction of subtyping

Which direction does `extends` establish?

| Reading | Subtyping | Constructors |
|---------|-----------|-------------|
| `B extends A` = "B is a refinement of A" | `B <: A` | B's constructors are a subset of A's? |
| `B extends A` = "B adds to A" | `A <: B` | B has A's constructors plus more? Breaks closed ADT |
| `B extends A` = "B inherits A's operations" | No subtyping | Just imports, same as `import A` |

### 3. Abstract sorts only?

Perhaps `extends` only makes sense for abstract sorts (no constructors):

```
sort Ordered
  extends Eq                              -- Ordered has all of Eq's operations
  sort T
  operation gt(a: T, b: T) -> Bool
  operation lt(a: T, b: T) -> Bool
end
```

Here `Ordered <: Eq` means "anything that is Ordered is also Eq." Since neither has constructors, the closed-ADT problem doesn't arise. This is the type class / algebraic specification pattern.

For defined sorts (with constructors), `extends` would be forbidden — use `import` instead.

### 4. Difference from `import`

If `extends` establishes a subtyping relation and `import` does not, that's the key distinction:

```
sort B
  import A                               -- brings A's names into scope, no subtyping
end

sort B
  extends A                              -- brings A's names into scope AND establishes B <: A
end
```

### 5. Multiple inheritance

`extends A, B` — what if A and B have conflicting operations? Diamond problem? The algebraic specification tradition (Maude) handles this via renaming in views. Need a conflict resolution mechanism.

### 6. Interaction with `where` clauses

Can `extends` have `where` bindings?

```
sort IntOrdered
  extends Ordered where { T = Int64 }
end
```

Or is this just `import Ordered where { T = Int64 }` plus a subtyping assertion?

## Possible Approaches

### Approach A: `extends` for abstract sorts only

- `extends` is only valid when the parent has no constructors.
- Establishes subtyping: `B <: A`.
- Inherits all operations and rules.
- This covers the type class hierarchy pattern (Eq → Ordered → Numeric).

### Approach B: `extends` as `import` + subtype declaration

- `extends A` desugars to `import A` plus `rule subtype(B, A)`.
- No special constructor handling — subtyping is a fact in the KB.
- The reasoning engine uses the subtype relation for type checking.

### Approach C: Defer entirely

- Continue using `import` for all cases.
- Subtyping, if needed, is expressed as explicit facts: `rule subtype(Ordered, Eq)`.
- Reintroduce `extends` only when the need is clearer.

## Recommendation

Approach C (defer). The current `import` mechanism covers all operational needs. Subtyping semantics require careful design, especially around closed ADTs and the direction of the subtype relation. This proposal documents the design space for future reference.
