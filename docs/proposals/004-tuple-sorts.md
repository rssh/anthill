# Proposal 004: Tuple Sorts

**Status:** Draft
**Depends on:** [002-arrow-sorts](002-arrow-sorts.md) (for disambiguation with arrow parameter lists)
**Affects:** Kernel Language Specification §4, §11

## Motivation

The kernel language has no anonymous product types. To group values, users must define named entities:

```
entity Pair(fst: A, snd: B)
```

This is adequate for domain-specific types where field names carry meaning (`entity Point(x: Int, y: Int)`), but verbose for transient groupings — intermediate results, multi-value returns, or generic specifications where named fields add no information.

Arrow sorts (Proposal 002) introduce parenthesized type lists in the parameter position `(A, B) => C`. Tuple sorts extend this notation to type positions: `(A, B)` as an anonymous product sort.

## Grammar

```
Type ::= ...
       | '(' Type ',' Type (',' Type)* ')'    -- tuple (2+ elements)
       | '(' ')'                               -- unit
```

A single-element form `(A)` is just parenthesization for grouping, not a tuple. Tuples require two or more elements.

## Examples

```
(A, B)                                  -- pair
(Int, String)                           -- concrete pair
(Int, String, Bool)                     -- triple
()                                      -- unit (zero elements)
(List{T = Int}, Option{T = String})     -- tuple of parameterized sorts
```

## Disambiguation

The tuple syntax `(A, B)` and the arrow parameter list `(A, B) => C` are distinguished by the presence of `=>`:

- `(A, B) => C` — arrow sort (parameter list followed by `=>`)
- `(A, B)` — tuple sort (no `=>` follows)

This is unambiguous at the grammar level — the parser looks ahead for `=>` after a closing `)`.

## Semantics

Tuple sorts are **structurally typed** anonymous products.

### Construction

Tuple values are constructed with parenthesized comma-separated terms:

```
(?x, ?y)                                -- pair value
(1, "hello", true)                      -- triple value
()                                      -- unit value
```

### Projection

Tuple elements are accessed positionally. Two options (to be decided):

**Option A — named projections:** `fst`, `snd`, or positional `_1`, `_2`, `_3`:

```
rule swap(?p) = (_2(?p), _1(?p))
```

**Option B — pattern matching only:** tuples are destructured in rule heads:

```
rule swap((?x, ?y)) = (?y, ?x)
```

Option B is more consistent with the algebraic specification tradition (pattern matching over projections) and requires no new built-in operations.

### Equivalence to Named Entities

A tuple sort `(A, B)` is equivalent to a sort with a single anonymous constructor:

```
(A, B)  ≡  sort _Tuple2 = { entity _Tuple2(_1: A, _2: B) }
```

This equivalence is semantic — the kernel may implement tuples directly or desugar them. Named entities remain preferred when field names carry domain meaning:

```
(Int, Int)                              -- anonymous: which is x, which is y?
entity Point(x: Int, y: Int)            -- self-documenting
```

### Unit

The unit sort `()` has exactly one value, also written `()`. It is the identity for products:

```
(A, ())  ≡  A
((), B)  ≡  A
```

Unit is useful as the domain of thunks `() => A` (Proposal 002) and as a placeholder return type for side-effecting operations.

## Use Cases

### Multi-value returns

```
operation divmod(a: Int, b: Int) -> (Int, Int)
  requires neq(b, 0)

rule divmod(?a, ?b) = (div(?a, ?b), mod(?a, ?b))
```

### Generic pairs in specifications

```
sort Bifunctor
  sort F
    sort A
    sort B
  end

  operation bimap(
    fab: F{A = A, B = B},
    f: (A) => C,
    g: (B) => D
  ) -> F{A = C, B = D}
end
```

### State-passing (connection to §5.6)

The state-passing interpretation of effectful operations (§5.6) uses products internally:

```
-- op_e : Env × A → (R × Env × Event list) + Error

-- With tuple sorts, expressible as:
(Env, A) => (R, Env, List{T = Event})
```

## Summary

```
-- Tuple sort (new Type forms):
Type ::= ...
       | '(' Type ',' Type (',' Type)* ')'
       | '(' ')'

-- Tuple term (new Term forms):
Term ::= ...
       | '(' Term ',' Term (',' Term)* ')'
       | '(' ')'
```

## Semantic Rules

1. `(A, B, ...)` is a sort when all components are sorts.
2. Tuple sorts are structurally typed — `(A, B)` from different declarations are the same sort.
3. `()` is the unit sort with a single value `()`.
4. Tuple values are constructed and destructured via pattern matching.

## Backwards Compatibility

No existing syntax is affected. Parenthesized expressions in the current grammar are either:

- `Fn(name, args)` — function application (head is a name, not a type)
- `(expr)` — grouping

Neither conflicts with `(Type, Type)` in type positions or `(Term, Term)` in term positions, since types and terms occupy distinct syntactic positions.

No existing valid program is invalidated by this change.
