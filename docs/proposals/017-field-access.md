# 017: Field Access (Dot Projection)

## Status: Accepted / Implemented

## Motivation

Anthill currently uses dotted names exclusively for qualified symbol paths (`namespace.sort.entity`). There is no syntax for accessing a field of a value — the only way to extract a field is via pattern matching / unification:

```anthill
rule example(?env, ?fs) :-
  ?env = execution_environment(fs: ?fs),
  ...
```

This is verbose and indirect. In many practical cases — especially effect annotations, rule bodies, and operation contracts — the intent is simply "the `fs` field of `env`". Compare:

```anthill
-- today: introduce auxiliary variable + unification
effects (Error, Modify{env})

-- desired: precise effect targeting
effects (Error, Modify{env.fs})
```

```anthill
-- today: destructure to extract one field
rule uses_shell(?env, ?result) :-
  ?env = execution_environment(fs: ?fs),
  exists(?fs, "/bin/sh")

-- desired: direct field access
rule uses_shell(?env, ?result) :-
  exists(?env.fs, "/bin/sh")
```

The lack of field access also makes the effect system imprecise — `Modify{env}` overstates what `Toolchain.build` actually modifies (only the filesystem, not the platform).

## Design

### Expressions Are Terms

Anthill already represents expressions as terms. Infix expressions desugar via the Pratt parser into `Term::Fn` calls (`a + b` → `add(a, b)`). Field access follows the same principle — it is a term, not a separate expression language.

After resolution, `env.fs` is a term where both `env` (the parameter) and `fs` (the field symbol from the entity definition) are resolved names. No new AST node type is needed.

### Syntax

Field access uses the existing dot syntax: `term.field_name`.

```
field_access ::= term '.' identifier
```

This overloads the dot, which today is only used in qualified names. Chained access is allowed: `a.b.c`.

### Name Resolution

Field access is an extension to name resolution, not a new semantic concept. The resolver already turns `Term::Ident` into `Term::Ref` for known symbols. Field access extends this to dotted names where the first segment is a parameter or variable:

1. **First segment resolves to a namespace, sort, or entity** → qualified symbol path (existing behavior, unchanged).
2. **First segment resolves to a parameter** (`SymbolKind::Param`) → field access. The parameter's declared type determines the sort; the resolver looks up the entity's field definitions to resolve the second segment.
3. **First segment is a logic variable (`?name`)** → field access. Requires type context to resolve the field name.

For parameters (case 2), all type information is statically available — the operation signature declares the parameter's sort, and the sort's entity fields are in the KB. The resolver follows the chain:

```
env         → Param of sort ExecutionEnvironment
            → entity execution_environment(platform: ..., fs: Filesystem)
env.fs      → field "fs" of sort Filesystem (resolved)
```

Each segment produces a resolved symbol. The result is a term with fully resolved names — the same as any other resolved term.

### In Effect Annotations

Effect targets follow the same resolution rules. Since operation parameters have declared types, the sort of `env` and the validity of field `fs` are statically known:

```anthill
operation build(tc: Toolchain, env: ExecutionEnvironment, ...) -> ProcessResult
  effects (Error, Modify{env.fs})
```

`env` has type `ExecutionEnvironment`, which has entity `execution_environment(platform: ..., fs: Filesystem)`, so `env.fs` has sort `Filesystem`. The effect `Modify{env.fs}` is well-formed.

### Well-formedness

Field access `t.f` is well-formed when:

- `t` has a known sort `S`
- `S` has an entity with a field named `f`
- **Single-constructor sorts**: field is looked up in the sole constructor — unambiguous
- **Multi-constructor sorts**: field access is valid only if field `f` appears in **all** constructors with the same sort. Otherwise it is an error.
- **Abstract sorts** (`sort T = ?`): field access is ill-formed — no fields to project

### Chained Access

`a.b.c` means `(a.b).c` — left-associative. Each step is a projection: the resolved sort of `a.b` determines which entity provides field `c`. The resolver follows the type chain step by step, producing resolved names at each level.

## Interaction with Existing Features

### Pattern Matching

Field access and pattern matching are complementary notations for the same concept (extracting a component). Both remain valid:

```anthill
-- field access (concise, when you need one field)
exists(?env.fs, "/bin/sh")

-- pattern match (explicit, when you need multiple fields)
?env = execution_environment(platform: ?p, fs: ?fs)
```

### Qualified Names

No practical ambiguity: the resolver distinguishes by what the first segment resolves to. `SymbolKind::Param` → field access, `SymbolKind::Namespace`/`Sort`/`Entity` → qualified path. For logic variables (`?x.field`), the `?` prefix is always unambiguous.

## Open Questions

1. **Type inference for variables**: In `?x.field`, if `?x` has no type annotation, the sort must be inferred from context. For parameters this is trivial (declared type). For rule variables it requires type propagation. How far should inference go?

2. **Reflection**: Should `FieldInfo` in `anthill.reflect` be extended to support field access queries, or is the existing `fields(kb, name)` operation sufficient?

## Resolution

Implemented as a unified `field_access` operation in `anthill.reflect`:

- **Syntax**: `.` desugars to `field_access(x, y)` — same pattern as `+` → `add(x, y)`
- **Grammar**: `field_access` rule as a term atom with precedence 10 (highest, left-associative)
- **Converter**: emits `Term::Fn { functor: "field_access", pos_args: [object, Ident(field)] }`
- **Runtime dispatch** (builtin):
  - Entity fields via `entity_fields` registry (named arg lookup by short name)
  - Sort components via `by_qualified_name` scope lookup
- **Disambiguation**: `A.B(x)` → qualified `fn_term`; `A.B` alone → `field_access`; `?x.y` → always `field_access` (unambiguous due to `?` prefix)
