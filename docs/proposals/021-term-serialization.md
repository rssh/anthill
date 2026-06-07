# Proposal 021: Term Serialization to TOML/JSON

**Status:** Proposed
**Depends on:** None
**Affects:** Persistence layer, KB load pipeline, Stage 0 design

## Motivation

The anthill language is designed for **logic** — rules, queries, constraints, sort definitions. But much of what tools read and write is **data** — entity instances like tasks, tool definitions, project config. Writing data in the anthill DSL works but is verbose and requires parsing the full grammar:

```anthill
fact Task(id: "WI-AUTH-001", description: "Define auth traits",
          status: Open, depends_on: nil,
          acceptance: cons(head: ToolPasses(cargo-test), tail: nil),
          context: cons(head: "src/models/user.rs", tail: nil))
```

Standard formats (TOML, JSON) are better for structured data: tools already know how to read/write them, they have mature libraries in every language, and they're familiar to developers.

Both representations produce the same KB fact. This proposal defines the standard mapping between anthill terms and TOML/JSON, so any entity type can be serialized without custom code.

## Design

### File structure: `meta` + `data` envelope

A serialization file has two sections:
- **`meta`** — declares the entity type (fully-qualified name)
- **`data`** — one or more entity instances

**TOML:**

```toml
[meta]
entity = "anthill.stage0.Task"

[[data]]
id = "WI-AUTH-001"
status = "Open"
depends_on = []

[[data]]
id = "WI-AUTH-002"
status = "Open"
depends_on = ["WI-AUTH-001"]
```

**JSON:**

```json
{
  "meta": { "entity": "anthill.stage0.Task" },
  "data": [
    { "id": "WI-AUTH-001", "status": "Open", "depends_on": [] },
    { "id": "WI-AUTH-002", "status": "Open", "depends_on": ["WI-AUTH-001"] }
  ]
}
```

For a single entity (not a list), `data` is an object instead of an array:

```toml
[meta]
entity = "anthill.stage0.Project"

[data]
name = "my-app"
language = "rust"
build = "cargo"
```

### Multiple entity types per file

Use scoped sections. Each section has its own `meta` + `data`:

```toml
[project.meta]
entity = "anthill.stage0.Project"

[project.data]
name = "my-app"
language = "rust"
build = "cargo"

[tools.meta]
entity = "anthill.stage0.ToolDef"

[[tools.data]]
name = "cargo-test"
command = "cargo"
args = ["test"]
success = "ExitZero"
```

### Mapping rules

#### Primitives

| Anthill type | TOML type | JSON type | Example |
|-------------|-----------|-----------|---------|
| `String` | String | string | `"hello"` |
| `Int64` | Integer | number | `42` |
| `Float` | Float | number | `3.14` |
| `Bool` | Boolean | boolean | `true` |

#### Entity fields

Named fields map to keys:

```
Entity(name: "x", count: 3)  →  { name = "x", count = 3 }
```

#### Lists

`List[T]` maps to arrays:

```
cons(head: "a", tail: cons(head: "b", tail: nil))  →  ["a", "b"]
```

The loader builds the cons-list from the array. The serializer flattens cons-lists to arrays.

#### Option

`Option[T]` maps to presence/absence of the key:

```
some(value: "x")  →  key = "x"
none()             →  (key omitted)
```

#### Nullary constructors (enums)

A constructor with no fields maps to a string:

```
Open    →  "Open"
Draft   →  "Draft"
```

#### Constructors with fields

A constructor with fields maps to a table with the constructor name as key:

```
Verified(at: "2027-03-15")  →  { Verified = { at = "2027-03-15" } }
```

Single-field shorthand — omit the field name:

```
ToolPasses(tool: "cargo-test")  →  { ToolPasses = "cargo-test" }
```

#### Nested entities

Follow the same rules recursively.

### Variables

A string value starting with `?` is a variable. A literal string starting with `?` is escaped as `\?`.

```toml
assignee = "?agent"          # variable ?agent
name = "alice"               # string "alice"
note = "\\?not-a-variable"   # literal string "?not-a-variable"
```

Variable scope is **per-entry** — each `[[data]]` entry is an independent scope (like each `fact` declaration in `.anthill`). Two occurrences of `?x` within one entry share identity; across entries they are independent.

### Name resolution

The `meta.entity` field provides the fully-qualified name. The loader uses the KB's entity schema (field names, types) to interpret the structure:

- Field names must match entity field names
- Constructor names must match sort constructor names
- The KB must have entity/sort definitions loaded before loading serialized data

## Examples

### Stage 0: tasks.toml

```toml
[meta]
entity = "anthill.stage0.Task"

[[data]]
id = "WI-AUTH-001"
description = "Define User entity and auth traits"
status = "Open"
depends_on = []
acceptance = [{ Compiles = "src" }, { ToolPasses = "cargo-test" }]
context = ["src/models/user.rs", "docs/auth-design.md"]

[[data]]
id = "WI-AUTH-002"
description = "Implement JWT token generation"
status = "Open"
depends_on = ["WI-AUTH-001"]
acceptance = [{ Compiles = "src" }, { ToolPasses = "cargo-test" }]
context = ["src/auth/jwt.rs"]
```

Loads as:
```anthill
fact Task(id: "WI-AUTH-001", description: "Define User entity and auth traits",
          status: Open, depends_on: [],
          acceptance: [Compiles("src"), ToolPasses("cargo-test")],
          context: ["src/models/user.rs", "docs/auth-design.md"])
```

### Stage 0: anthill.toml (config)

```toml
[project.meta]
entity = "anthill.stage0.Project"

[project.data]
name = "my-app"
language = "rust"
build = "cargo"

[tools.meta]
entity = "anthill.stage0.ToolDef"

[[tools.data]]
name = "cargo-test"
command = "cargo"
args = ["test"]
success = "ExitZero"

[[tools.data]]
name = "cargo-clippy"
command = "cargo"
args = ["clippy", "--", "-D", "warnings"]
success = "ExitZero"
```

### Spec-satisfaction facts

```toml
[meta]
entity = "anthill.prelude.Eq"

[[data]]
T = "Int64"

[[data]]
T = "String"
```

Loads as:
```anthill
fact Eq[T = Int64]
fact Eq[T = String]
```

### JSON: MCP tool response

```json
{
  "meta": { "entity": "anthill.stage0.Task" },
  "data": [
    {
      "id": "WI-AUTH-001",
      "description": "Define User entity and auth traits",
      "status": "Open",
      "depends_on": [],
      "acceptance": [{ "Compiles": "src" }, { "ToolPasses": "cargo-test" }]
    }
  ]
}
```

TOML is preferred for files (human-readable config). JSON is preferred for machine exchange (APIs, MCP responses).

## Relationship to existing persistence

| Format | Extension | Written by | Good for |
|--------|-----------|-----------|----------|
| Anthill language | `.anthill` | Humans | Rules, sorts, operations — logic |
| Term serialization | `.toml`, `.json` | Tools | Entity data — facts in bulk |

Both formats produce the same KB facts. The loader detects the format by extension and dispatches accordingly.

## Implementation

1. **Serializer** (`kb::serialize`): `Term → TOML Value` / `Term → JSON Value`, using entity schema for field names and types
2. **Deserializer** (`kb::deserialize`): `TOML Value → Term` / `JSON Value → Term`, using entity schema for interpretation
3. **FileStore extension**: detect `.toml`/`.json` extension, dispatch to deserializer on load, serializer on persist
4. **Schema lookup**: deserializer queries KB for entity definition to interpret data correctly
5. **Variable handling**: per-entry `HashMap<String, VarId>` cache, reset between entries
