# Proposal 022: Typing as Facts

**Status:** Proposed
**Depends on:** Proposal 019 (Collection Literals), Proposal 011 (Type Resolution)
**Affects:** KB, Loader, Reflect stdlib, ListLiteral desugaring, Expression evaluation

## Motivation

Anthill needs a typing system for:
- Validating entity field values against declared types
- Type-directed desugaring of `ListLiteral` → cons/nil (or other collection types)
- Typing expressions (match, if, let, lambda) for evaluation
- Typing rule variables from usage context
- Verifying `requires` spec bindings

The design question: where do types live? A separate type checker? A typed AST? A typed KB?

The answer: **types are facts**. The KB stays untyped. A typing pass emits `TypeOf` facts into the same KB. Type checking, inference, and desugaring are all rules that operate on `TypeOf` facts.

## Design

### PositionedTerm: bridging parse IR and KB

The typing pass needs both structural identity (for KB queries) and source positions (for error reporting). A `PositionedTerm` pairs them:

```
PositionedTerm = (TermId, Span)
```

- `TermId` — hash-consed, used for KB operations ("what are the fields of this entity?")
- `Span` — source location, used for error messages ("type mismatch at line 15")

This pairing already exists implicitly in the parse IR — `SimpleTermStore` allocates `TermId`s and the converter tracks spans from tree-sitter nodes. The typing pass preserves this pairing instead of discarding spans at load time.

The pipeline:

```
Source → Parser → ParsedFile (terms + spans)
                      ↓
               Typing pass: walks PositionedTerms
                  ├── emits TypeOf facts (into KB, no spans)
                  ├── emits desugared terms (into KB, hash-consed)
                  └── returns errors (with spans from PositionedTerm)
                      ↓
               KB (hash-consed terms, TypeOf facts, RuleIds)
```

The KB stores results without spans. Type errors carry spans out of the typing pass (like `LoadError` carries spans out of the loader today).

### The `TypeOf` relation

```anthill
sort TypeOf {
    entity TypeOf(rule: RuleId, field: String, type: Sort)
}
```

`TypeOf(r, f, S)` means "in rule/fact `r`, the field `f` has type `S`". The `RuleId` provides occurrence identity (not hash-consed — each fact assertion gets a unique one, even for identical terms). The typing pass populates this relation by walking declarations and applying typing rules.

For top-level terms (the whole fact/rule head), `field` is empty. For subexpressions in expression bodies, a path-like field reference locates the node.

### What the typing pass does

The typing pass walks all declarations in scope order and emits `TypeOf` facts:

**Entity field types** — from the entity declaration:
```anthill
entity WorkItem(id: String, status: WorkStatus, depends_on: List[T=String])
```
Emits:
```anthill
fact TypeOf(term: WorkItem.id, type: String)
fact TypeOf(term: WorkItem.status, type: WorkStatus)
fact TypeOf(term: WorkItem.depends_on, type: List[T=String])
```

**Fact field values** — from each asserted fact:
```anthill
fact WorkItem(id: "WI-001", status: Open, depends_on: [])
```
Emits:
```anthill
fact TypeOf(term: "WI-001", type: String)        -- literal type
fact TypeOf(term: Open, type: WorkStatus)         -- constructor type from parent sort
fact TypeOf(term: ListLiteral(), type: List[T=String])  -- from field context
```

**Rule variables** — inferred from usage:
```anthill
rule open_item(?id, ?desc) :- WorkItem(id: ?id, description: ?desc, status: Open)
```
Emits:
```anthill
fact TypeOf(term: ?id, type: String)    -- from WorkItem.id field type
fact TypeOf(term: ?desc, type: Term)    -- from WorkItem.description field type
```

**Expression nodes** — each subexpression gets a type:
```anthill
operation foo(x: Int) -> Bool = gt(x, 0)
```
Emits:
```anthill
fact TypeOf(term: x, type: Int)          -- from parameter
fact TypeOf(term: 0, type: Int)          -- literal
fact TypeOf(term: gt(x, 0), type: Bool)  -- from operation return type
```

### Type context propagation

Types propagate top-down from declarations and bottom-up from literals/constructors:

**Top-down** (expected type from context):
- Entity field declaration → expected type for field value
- Operation parameter → expected type for argument
- Operation return type → expected type for expression body
- `requires` spec binding → expected type for bound parameter

**Bottom-up** (inferred type from value):
- Literal: `"hello"` → `String`, `42` → `Int`, `true` → `Bool`
- Constructor: `Open` → parent sort (`WorkStatus`)
- Constructor with fields: `cons(head: "a", tail: nil)` → `List[T=String]`

**Meeting point**: when top-down and bottom-up types meet, they must be compatible (via `type_compatible` rule from `typing.anthill`).

### Type-directed desugaring

`ListLiteral` desugaring becomes a typing rule:

```anthill
-- When ListLiteral appears where List[T] is expected, desugar to cons/nil
rule desugar_list(ListLiteral(), List[T=?t])
  :- TypeOf(term: ListLiteral(), type: List[T=?t])

-- Elements: desugar to cons(head: typed_elem, tail: rest)
rule desugar_list(ListLiteral(?h, ?rest...), List[T=?t])
  :- TypeOf(term: ?h, type: ?t),
     desugar_list(ListLiteral(?rest...), List[T=?t])
```

The temporary `build_list_with_tail` desugaring in the loader is replaced by this rule once the typing pass exists.

For other collection types (when they're added):
```anthill
rule desugar_collection(ListLiteral(?items...), Vector[T=?t])
  :- ... build vector ...
```

The typing context determines which desugaring applies.

### Typing as constraint checking

A type error is a contradiction in `TypeOf` facts:

```anthill
-- Type error: value doesn't match expected type
constraint type_mismatch
  :- TypeOf(term: ?t, type: ?actual),
     TypeOf(term: ?t, type: ?expected),
     not(type_compatible(?actual, ?expected))
```

This is a standard anthill constraint — the same mechanism used for any other invariant checking.

### No separate typed AST

The untyped AST (terms in the KB) stays unchanged. `TypeOf` facts annotate existing terms externally via `RuleId` + field path. This means:

- **Rules work on untyped terms** — no rewrites needed
- **Type info is queryable** — `TypeOf(?rule, ?field, ?type)` is a regular query
- **Gradual typing** — some facts may have `TypeOf`, others may not
- **Types are derivable** — rules can infer types, not just check them
- **Errors carry source positions** — the typing pass works on `PositionedTerm`s from parse IR, returns errors with `Span`s; the KB itself doesn't store spans

## Implementation plan

### Phase 1: TypeOf infrastructure
- Define `TypeOf` sort in `anthill.reflect`
- Add typing pass in loader (after `load_all`, before constraint checking)
- Emit `TypeOf` for entity field declarations (from `FieldInfo`)
- Emit `TypeOf` for literal constants (bottom-up)
- Emit `TypeOf` for nullary constructors (from entity parent sort)

### Phase 2: Fact typing
- Walk each asserted fact
- Match field values against declared field types (via `FieldInfo`)
- Emit `TypeOf` for each field value
- Detect type mismatches (field type ≠ value type)

### Phase 3: ListLiteral desugaring
- When `TypeOf(ListLiteral(...), List[T=?t])` is derived
- Replace `ListLiteral` with cons/nil in the KB
- Remove temporary desugaring from loader's `convert_term`

### Phase 4: Rule variable typing
- For each rule body literal, match against entity field types
- Infer variable types from field position
- Emit `TypeOf` for each variable

### Phase 5: Expression typing
- Walk expression trees (match, if, let, lambda, apply)
- Propagate types through expression nodes
- Emit `TypeOf` for each subexpression
- Enable expression evaluation with type safety

### Phase 6: Constraint integration
- Define `type_mismatch` constraint
- Run constraint checker after typing pass
- Report type errors as constraint violations

## Examples

### Well-typed fact
```anthill
entity Task(id: String, priority: Int)

fact Task(id: "T-001", priority: 3)

-- Typing pass emits:
fact TypeOf(term: "T-001", type: String)     -- matches Task.id: String ✓
fact TypeOf(term: 3, type: Int)               -- matches Task.priority: Int ✓
```

### Type error
```anthill
fact Task(id: 42, priority: "high")

-- Typing pass emits:
fact TypeOf(term: 42, type: Int)              -- but Task.id expects String ✗
fact TypeOf(term: "high", type: String)       -- but Task.priority expects Int ✗

-- Constraint fires:
-- type_mismatch: TypeOf(42, Int) vs expected String for Task.id
```

### ListLiteral desugaring
```anthill
entity WorkItem(depends_on: List[T=String])

fact WorkItem(depends_on: ["WI-001", "WI-002"])

-- Typing pass:
-- 1. Field type: TypeOf(WorkItem.depends_on, List[T=String])
-- 2. Value is ListLiteral("WI-001", "WI-002")
-- 3. Expected type is List → desugar to cons/nil
-- 4. Result: depends_on: cons(head: "WI-001", tail: cons(head: "WI-002", tail: nil))
-- 5. Emit: TypeOf("WI-001", String), TypeOf("WI-002", String)  ✓
```

### Expression typing
```anthill
sort TodoCli {
    operation next() -> Action
      = query(claimable(?id, ?desc))
}

-- Typing pass:
-- 1. next() return type: Action
-- 2. Body: query(claimable(?id, ?desc))
-- 3. query returns Action → TypeOf(query(...), Action) ✓
-- 4. claimable(?id, ?desc) → infer ?id: String, ?desc: String from rule signature
```

## Relationship to existing work

- **Proposal 011** (Type Resolution): This proposal is the concrete implementation of Proposal 011's philosophy. Path B (syntactic instantiation) is kept.
- **Proposal 019** (Collection Literals): ListLiteral desugaring moves from the loader hack to type-directed rules.
- **typing.anthill**: Existing `type_compatible`, `refines`, `is_entity_of` rules are used by the typing pass.
- **SortView**: Parameterized types (`List[T=String]`) are already SortView terms — `TypeOf` types reference them.

## Non-goals

- **Dependent types**: Types depending on runtime values. Out of scope.
- **Higher-kinded types**: `Functor[F]` where `F` is a type constructor. Future work.
- **Linear types**: Tracking resource usage. Not needed for Stage 0.
- **Effect typing**: Effect annotations on operations exist syntactically but are not checked. Future work.
