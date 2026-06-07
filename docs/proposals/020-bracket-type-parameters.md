# Proposal 020: Bracket Type Parameters

**Status:** Proposed
**Depends on:** None
**Affects:** Kernel Language Specification §4 (Types, Terms), Grammar, Parse Converter, Standard Library, Examples

## Motivation

Anthill currently uses curly braces for type parameterization:

```anthill
List{T = Int64}
Option{T = String}
fact Eq{Int64}
```

This overloads `{}` — it appears in three distinct roles:

1. **Type parameters / instantiation**: `List{T = Int64}`, `Eq{Int64}`
2. **Set literals**: `{a, b, c}` → `SetLiteral(a, b, c)`
3. **Block delimiters**: `sort Foo { ... }`, `namespace Bar { ... }`

Roles 1 and 2 are disambiguated by the presence of a leading `Name` — `Name{...}` is instantiation, bare `{...}` is set literal. Role 3 is statement-level and resolved by grammar precedence (`set_literal` has `prec(-2)`). This works, but the visual overload makes code harder to scan:

```anthill
sort Container {
  sort T = ?
  entity Node(value: T, children: List{T = Node})
  operation lookup(c: Container, key: String) -> Option{T = T}
}
```

Switching to square brackets for type parameters:

```anthill
sort Container {
  sort T = ?
  entity Node(value: T, children: List[T = Node])
  operation lookup(c: Container, key: String) -> Option[T = T]
}
```

This gives each bracket its own role:
- `()` — tuples, function calls, grouping
- `[]` — type parameters (and collection literals, see proposal 019)
- `{}` — set literals and block bodies

This is also more conventional — Scala 3, Python, Kotlin, and TypeScript all use `[]` for type parameters.

## Design

### Syntax change

```
-- Before:
parameterized_type  ::=  Name '{' SortBinding (',' SortBinding)* '}'
instantiation_term  ::=  Name '{' SortBinding (',' SortBinding)* '}'

-- After:
parameterized_type  ::=  Name '[' SortBinding (',' SortBinding)* ']'
instantiation_term  ::=  Name '[' SortBinding (',' SortBinding)* ']'
```

`SortBinding` is unchanged:
```
SortBinding ::= Name ('=' Type)?    -- named:     T = Int64
              | Type                 -- positional: Int64
              | VariableTerm         -- variable:   ?
```

### Disambiguation with collection literals

If proposal 019 adds `[a, b]` as a collection literal:

- `Name[...]` = type parameterization / instantiation (leading `Name`)
- `[...]` = collection literal (bare `[`, no name prefix)

This is the exact same disambiguation pattern we already use for `Name{...}` vs `{...}`. No ambiguity.

### Examples

```anthill
-- Types
sort T = ?
field items: List[T = String]
field maybe: Option[T = Int64]
operation parse(s: String) -> Result[T = AST, E = ParseError]

-- Instantiation as terms (spec satisfaction)
fact Eq[Int64]
fact Eq[T = String]
fact Ordered[T = Float]
fact Numeric[T = Int64]

-- Nested
field deps: Option[T = List[T = String]]

-- With collection literal (proposal 019)
fact WorkItem("WI-001", depends_on: ["A", "B"], status: Open)
-- depends_on has type Option[T = List[T = String]]
```

## Grammar Changes

In `grammar.js`:

```js
// Before:
parameterized_type: $ => seq(
  $.name,
  '{',
  commaSep1($.sort_binding),
  '}',
),

instantiation_term: $ => seq(
  field('name', $.name),
  '{',
  commaSep1($.sort_binding),
  '}',
),

// After:
parameterized_type: $ => seq(
  $.name,
  '[',
  commaSep1($.sort_binding),
  ']',
),

instantiation_term: $ => seq(
  field('name', $.name),
  '[',
  commaSep1($.sort_binding),
  ']',
),
```

The `set_literal` rule stays as-is — `{}` is now exclusively sets and blocks.

## Converter Changes

No logic changes in `convert.rs` — only the tree-sitter node names change if the grammar rules are renamed. The `convert_sort_binding`, `convert_type`, and `convert_instantiation_term` functions operate on the same child structure regardless of delimiter.

## Migration Scope

| Area | Estimated changes |
|---|---|
| `grammar.js` | 2 rules (`parameterized_type`, `instantiation_term`) |
| `convert.rs` | 0 logic changes (node-kind strings may update if rules renamed) |
| `load.rs` | 0 changes (works on parsed IR, not syntax) |
| Standard library (`stdlib/`) | ~100+ `{` → `[` replacements across 15+ files |
| Examples (`examples/`) | ~30 replacements in `domain.anthill` |
| Test cases (`anthill-testcases/`) | ~10 replacements |
| Documentation (`docs/`) | ~50 replacements across kernel-language.md and proposals |
| tree-sitter tests | Update test corpus for new syntax |

The stdlib/examples/docs changes are mechanical (search-replace `Name{` → `Name[`, `}` → `]` in type positions). The grammar and converter changes are minimal.

## Migration Strategy

Two options:

### Option A: Breaking change (recommended for pre-1.0)

Switch all at once. Since anthill is pre-1.0 with no external users, this is a clean cut.

### Option B: Transition period

1. Grammar accepts both `{}` and `[]` for type parameters (both rules active)
2. Linter/formatter emits warnings for `{}` form
3. After migration, remove `{}` form

Option A is simpler and avoids grammar ambiguity.

## Interaction with Other Proposals

- **Proposal 019 (Collection Literals)**: Complementary. `[]` for type params means `Name[...]` is types, `[...]` is collection literals — clean separation. If both proposals are accepted, `{}` becomes sets-only, `[]` becomes types + collections.
- **Proposal 014 (Union Types)**: No interaction — union types use `|` operator, not brackets.
- **Proposal 004 (Tuple Sorts)**: No interaction — tuples use `()`.

## Non-goals

- **Changing sort body syntax**: `sort Foo { ... }` stays with `{}` — these are blocks, not parameterization.
- **Changing set literal syntax**: `{a, b}` stays.
- **Index/subscript syntax**: `arr[i]` as array indexing is out of scope. `Name[...]` is always type parameterization; subscripting would need a different mechanism (e.g., an operation).

## Relationship of Bracket Roles

| Bracket | Role |
|---|---|
| `()` | Tuples, function calls, grouping, arrow params |
| `[]` | Type parameters `Name[T]`, collection literals `[a, b]` |
| `{}` | Set literals `{a, b}`, block bodies `sort Foo { ... }` |
| `<>` | Not used (available for future) |

Each pair has at most two roles, disambiguated by context (leading `Name` vs bare).
