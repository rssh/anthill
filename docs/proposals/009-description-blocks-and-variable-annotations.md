# 009: Description blocks and variable annotations

## Status: Mostly implemented

## Problem

The language has two overlapping mechanisms for attaching human-readable text:

1. **Comments** (`--`, `{- -}`) — discarded by the parser, invisible to the KB.
2. **Unspecified terms** (`<"text">`, `<"text", hints: [...]>`) — structural but awkward: single-line `"..."` strings, special `<" ">` delimiters, coupled to anonymous placeholders.

Additionally, logic variables (`?`, `?name`) and unspecified terms serve similar roles — both are "holes" to be filled — but are represented as distinct `Term` variants with no shared structure.

Meanwhile, proposal 008 noted that `--` comments adjacent to declarations could be extracted as documentation, but this conflates two concerns: commenting out code vs. documenting constructs.

## Proposal

### 1. Clean separation: erasure vs. annotation

Comments exist **only** for disabling code. All meaningful documentation is structural.

| Purpose | Syntax | Structural? |
|---------|--------|-------------|
| Commenting out code | `--` (line), `{- -}` (block) | No — discarded by parser |
| Description / documentation | `{< >}` (description block) | Yes — preserved as KB facts |

This eliminates the ambiguity present in most languages about whether a comment is documentation or noise.

### 2. Description block syntax: `{< >}`

A new delimiter pair for multi-line free-form text:

```anthill
{< The element type for this collection >}

{<
  The type that supports equality comparison.
  Must be a concrete type, not a type constructor.
>}
```

**Design rationale:**

- Visually distinct from comments (`{- -}`) and code blocks (`{ }`).
- Lightweight for short inline descriptions.
- Multi-line without needing string escaping or quotes.
- Closing `>}` is extremely unlikely to appear in natural-language prose (descriptions are not code with comparison operators — code disabling uses `{- -}`).

**Grammar:**

```javascript
description_block: $ => seq('{<', /[^>]*(\>+[^}][^>]*)*/, '>}'),
```

The content between `{<` and `>}` is free-form text (not parsed as terms).

### 3. Inline variable descriptions

A description block can follow a variable (or `sort T = ?`) to annotate it at the point of use:

```anthill
sort T = ? {< The element type >}

rule first: frs(?a, ? {< unused tail >}) = ?a

operation lookup(key: ?K {< must be hashable >}) -> ?V {< the stored value >}
```

### 4. The `describe` construct

A standalone statement to attach descriptions post-hoc, potentially from a different scope or file:

```anthill
sort Eq
  sort T = ?
  operation eq(a: T, b: T) -> Bool
end

-- Attach a description to T after declaration
describe Eq.T {<
  The type that supports equality comparison.
  Must be a concrete type, not a type constructor.
  Should not be a higher-kinded type.
>}
```

`describe` works with any named symbol, not just variables:

```anthill
describe Eq.eq {<
  Structural equality comparison.
  Returns true iff a and b are structurally identical.
>}

describe Account.balance {<
  The current balance in the account's currency.
  Always non-negative (enforced by constraint).
>}
```

**Grammar:**

```javascript
describe_declaration: $ => seq(
  'describe',
  field('target', $.name),
  field('text', $.description_block),
),
```

### 5. Representation: descriptions as scoped KB facts

Descriptions are **not** stored in `Term::Var` or `VarId`. They are facts in the KB, scoped to context:

```
Desc(target_term, scope, content)
```

Where `content` is structured — it can contain free text, references to other descriptions, and section headers:

```
Desc(Eq.T, Eq, content: [
  text("The type supporting equality"),
  ref(Ord.T),                          -- reference to related description
  text("Must be concrete"),
])
```

#### Description content model

Description content is a list of elements:

- **Text**: free-form prose.
- **Reference** (`@Name`): a link to another symbol's description. Rendered inline or as a hyperlink depending on context.
- **Header** (`## heading`): a named section within the description that can be referenced from outside as `@Eq.T#heading`.

```anthill
describe List.T {<
  The element type stored in the list.

  ## Constraints
  Must satisfy: @Eq.T
  See also: @Option.T
>}
```

References use `@Name` syntax inside `{< >}` blocks. This is unambiguous since `@` has no other meaning in description text.

#### Scoping and queryability

- The same variable `?T` can have different descriptions in different sorts.
- Descriptions are queryable: `by_functor("Description")` returns all documented symbols.
- `describe` from a different file/scope adds a `Description` fact in that scope.
- Inline `? {< text >}` emits a `Description` fact scoped to the enclosing rule/sort/namespace.

Example KB facts produced:

```anthill
sort Eq
  sort T = ? {< The element type >}
end
```

Emits:

```
SortAlias(Eq.T, ?)                                    -- type parameter (Var)
Description(Eq.T, "The element type", 0)              -- description fact (0-based index)
```

### 6. Merge `Term::Unspecified` into `Term::Var`

With descriptions as external KB facts, the `Term::Unspecified` variant is no longer needed:

| Before | After |
|--------|-------|
| `Term::Unspecified { text, hints }` | `Term::Var(VarId)` + `Desc(var, scope, text)` fact |
| `<"description">` | `? {< description >}` |
| `<"desc", hints: [t1, t2]>` | `? {< desc >}` (hints become a separate mechanism if needed) |

The `unspecified_term` grammar rule and `Term::Unspecified` variant can be removed.

### 7. ~~Primary description~~ (dropped)

Dropped — all descriptions of the same target are equal. Tooling can choose which to display based on context (e.g., prefer same-scope, most recent, etc.) without language-level `primary` markers.

### 8. Agent-requested descriptions

Agents can request descriptions for undocumented symbols. When an agent encounters a variable or declaration without a `Desc` fact, it can emit a **description request**:

```
DescRequest(target, requesting_agent, context)
```

This integrates with the Stage 0 workitem system — a `DescRequest` can generate a workitem for a human or another agent to provide the missing description:

```anthill
-- Agent discovers undocumented type parameter
-- System generates:
workitem describe_Eq_T {
  description: "Provide description for Eq.T"
  acceptance: Constraint(has_desc(Eq.T))
  status: Open
}
```

Once fulfilled, the `describe` statement satisfies the request:

```anthill
describe Eq.T {<
  The type that supports equality comparison.
>}
```

Agents can also **proactively describe** symbols they create or modify, using the same `describe` construct. This makes descriptions a collaborative artifact — humans and agents both contribute documentation through the same mechanism.

### 9. Description propagation through substitution

When a program transformation applies a substitution `{?T → Int64}`, descriptions don't disappear — they propagate as **references**, creating a provenance chain:

```
-- Before:
Desc(T, Eq, content: [text("The type supporting equality")])

-- Substitution: {T → Int64}
-- After (derived automatically):
Desc(Int64, Eq[T=Int64], content: [ref(Eq.T)])
```

The derived description for `Int64` is a **reference list** — not a copy of the text, but pointers back to the original descriptions. This avoids duplication and keeps the provenance chain navigable.

**Use cases:**

- **Error messages**: Instead of "Int64 does not satisfy Hashable", the system resolves the reference chain and says "Int64 (the type supporting equality) does not satisfy Hashable" — the role context explains why Int64 is there.
- **Agent reasoning**: An agent seeing `Int64` in a derived program can follow `ref(Eq.T)` to understand it was chosen to fill the role of "the type supporting equality".
- **Audit trails**: Reference chains form a navigable graph from concrete terms back through substitutions to abstract specifications.

**Composition:** When substitution binds a described variable to another described variable, the derived description collects references to all origins:

```anthill
sort List
  sort T = ? {< The element type >}
  requires Eq[T = T]
end

sort Eq
  sort T = ? {< The type supporting equality >}
end

-- After: fact List[T = Int64]
-- Derived description for Int64 in this context:
Desc(Int64, List[T=Int64], content: [ref(List.T), ref(Eq.T)])
```

Tooling resolves the references on demand: hovering over `Int64` shows "The element type (List.T); The type supporting equality (Eq.T)".

**Implementation:** The substitution engine (`apply_subst`, `reify`) should, when replacing a `Term::Var` that has `Desc` facts, emit a derived `Desc` fact whose content is a list of `ref()` elements pointing to the original descriptions. This is a KB-level operation — the term structure itself is unchanged; only the associated facts propagate.

### 10. Deprecation of `<"...">` syntax

The `unspecified_term` syntax (`<"text">`) is superseded by `? {< text >}`:

- `<"description">` becomes `? {< description >}`
- `<"desc", hints: [t1, t2]>` — the `hints` mechanism is orthogonal and can be revisited separately if needed.

The `<"...">` syntax should be removed from the grammar.

## Examples

```anthill
-- Commenting out code (discarded, not documentation)
-- sort OldStuff { ... }

{- Also commenting out code
  rule obsolete: ...
  operation deprecated(...) -> ...
-}

-- Structural descriptions (preserved in KB)
sort Eq
  sort T = ? {< The element type >}

  operation {
    eq(a: T, b: T) -> Bool     {< Structural equality >}
    neq(a: T, b: T) -> Bool    {< Negation of eq >}
  }
end

-- Post-hoc description from another file
describe Eq.T {<
  The type that supports equality comparison.
  Must be a concrete type, not a type constructor.
>}

-- Anonymous variable with description in a rule
rule project: pair(?, ?b) = ?b {< Extract second element >}

-- Multi-line description
describe Account.balance {<
  The current balance in the account's currency.

  Invariants:
  - Always non-negative (enforced by constraint non_negative)
  - Denominated in the currency specified by Account.currency
  - Updated only through deposit() and withdraw() operations
>}
```

## Implementation status

### Correction (2026-06-11): implemented fact shape

The proposal body writes descriptions as `Description(target, text)` (and sketches an
ordered content list within a single fact). The implementation stores **one fact per
`{< >}` block** with an explicit order index as a third argument:

```
Description(target, text, index)
```

- `index` is 0-based per target, in declaration order (`emit_desc_fact` in `kb/load.rs`).
- The index counter is per file (each file gets a fresh `Loader`), so a `describe` in
  another file appends further facts but restarts its index at 0 — order is encoded
  within a file, not across files.
- Multiple blocks on one target are therefore separate facts, never merged into a list;
  the stored `index` enables reassembly in declaration order. (The current readers —
  `kb_descriptions` in `anthill-stl` and the bridge `descriptions()` — do not yet read
  it: they substitute enumeration order / omit the field.)

`kernel-language.md` §4.1 documents this shape (corrected the same day). The status
bullets and the "Emits:" example below have been updated to match.

### Implemented

- **§1 Clean separation** — fully implemented
- **§2 Description block syntax** — `description_block` token in grammar, parsed and converted
- **§3 Inline variable descriptions** — fully implemented in both term and type positions. `? {< text >}` works in rules, operation params, entity fields, return types, sort bindings, and `sort T = ? {< text >}`. Variables (`?`, `?name`) are valid as types everywhere via `variable_term` in the `_type` grammar rule. Named type variables share identity within scope.
- **§4 The `describe` construct** — `describe Name {< text >}` grammar rule, parse IR (`Item::Describe`), converter, loader emitting `Description(target, text, index)` facts
- **§5 Representation** — descriptions stored as `Description(target, text, index)` KB facts, one per block (see Correction above). Content is plain text (structured content model with `@Name` references and `## heading` sections is a tooling concern — see below).
- **§6 Remove `Term::Unspecified`** — fully removed from grammar (`unspecified_term`), parse IR, converter, term store, KB operations (collect_vars, apply_subst, reify, subst_term), discrimination tree, loader, printer, codegen
- **§8 Agent-requested descriptions** — no language changes needed. Agents can already assert `fact DescRequest(target, agent, context)` and query with `by_functor("DescRequest")`. Workitem integration uses existing Stage 0 syntax.
- **§10 Deprecation of `<"...">` syntax** — fully removed
- **kernel-language.md** — updated: §4.1 rewritten, `Unspecified` removed from Term grammar, `Describe` added to namespace/sort content, appendix grammar updated, Type grammar includes `VariableTerm`
- **reflect.anthill** — `DescriptionInfo` entity and `descriptions` query operation added, `UnspecifiedRepr` removed from `TermRepr`

### Tooling concern (not kernel)

- **§5 Structured content model** — `@Name` references, `## heading` sections within description text. Description content is stored as plain text in `Description` facts. Structured parsing (`@Name` → reference links, `## heading` → addressable sections) can be done as a post-processing step by any tool that reads these facts (IDE hover, doc generation, agent prompts). No grammar or core parser changes needed.

### Dropped

- **§7 Primary description** — dropped. Multiple descriptions of the same target are all equal; tooling can choose which to display based on context.

### Deferred

- **§9 Description propagation through substitution** — derived `DescriptionRef` facts with reference chains when substitution replaces described variables. Deferred because `subst_term` has no production call sites yet — type substitution mechanics may take a different form than anticipated. Revisit when the type instantiation mechanism is designed.

### Relation to proposal 008
This proposal **supersedes** proposal 008 (doc comments for sorts). Instead of extracting `--` comments as documentation, all documentation uses the explicit `{< >}` syntax. Comments remain purely for code erasure.

## Alternatives considered

1. **`{{- -}}` delimiters**: Heavier visually, especially for short inline descriptions. `{{- desc -}}` vs `{< desc >}`. The doubled braces are bulkier and the visual relationship to `{- -}` comments could cause confusion (is it a comment or structural?).

2. **String-based descriptions** (`"text"` or `"""text"""`): Requires escaping, doesn't support multi-line cleanly, looks like data rather than documentation.

3. **Description in `VarId` or `Term::Var`**: Couples description to the term structure. Variables participate in unification, substitution, hash-consing — carrying descriptions through all of that adds complexity. KB facts are the right abstraction level.

4. **Reuse `{- -}` for descriptions after `?`**: Context-sensitive dual meaning (comment vs. structural) complicates the grammar and confuses readers.
