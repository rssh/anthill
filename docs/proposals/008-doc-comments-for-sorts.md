# 008: Doc comments for sorts and declarations

## Status: Draft

## Problem

Declarations like `sort T = ?` or `sort Money = Int` lack a structured way to attach documentation. Users currently write `--` comments nearby, but these are discarded by the parser (tree-sitter treats them as `extras`).

## Proposal

Capture adjacent `--` line comments as documentation strings for declarations. Two positions are conventional:

```anthill
-- The element type for this collection
sort T = ?

sort FactId = ?  -- opaque handle returned by persist()
```

### Rules

1. A `line_comment` immediately **preceding** a declaration (no blank line between) is its **doc comment**.
2. A `line_comment` on the **same line** as a declaration (trailing) is also a doc comment.
3. Multiple consecutive preceding comments are concatenated (like `///` blocks in Rust).
4. Block comments (`{- ... -}`) are not doc comments (they're for disabling code).

### IR representation

Add a `doc: Option<String>` field to declaration structs (`AbstractSort`, `SortWithBody`, `Entity`, `Operation`, etc.).

### Converter implementation

After converting a declaration node, scan the CST:
- Walk backward through preceding siblings to collect `line_comment` nodes (stop at first non-comment).
- Check the next sibling on the same start line for a trailing `line_comment`.
- Strip the `--` prefix and leading whitespace, concatenate with newlines.

### Example

```anthill
sort Eq
  export eq, neq

  -- The type that supports equality comparison.
  -- Must be a concrete type, not a type constructor.
  sort T = ?

  operation {
    eq(a: T, b: T) -> Bool     -- structural equality
    neq(a: T, b: T) -> Bool    -- negation of eq
  }
end
```

Would produce `AbstractSort { name: "T", doc: Some("The type that supports equality comparison.\nMust be a concrete type, not a type constructor."), ... }`.

## Alternatives considered

1. **Dedicated doc syntax** (`--- doc comment` or `{-| ... -}`): Adds grammar complexity for little benefit. Reusing `--` keeps the language simple.
2. **Meta block** (`sort T = ? [desc: "..."]`): Verbose, mixes documentation with runtime metadata.
3. **String after `?`** (`sort T = ? "description"`): Conflates syntax; `?` is a keyword token, not a term.

## Impact

- No grammar changes needed (comments are already parsed as `extras`).
- Converter changes only: scan siblings, populate `doc` field.
- Loader can optionally emit `DocComment(sort_term, text)` facts into the KB.
