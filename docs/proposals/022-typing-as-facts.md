# Proposal 022: Typing as Facts

**Status:** Proposed
**Depends on:** Proposal 019 (Collection Literals), Proposal 011 (Type Resolution)
**Affects:** KB, TermStore, OccurrenceStore (new), Loader, Reflect stdlib, ListLiteral desugaring, Expression evaluation

## Motivation

Anthill needs a typing system for:
- Validating entity field values against declared types
- Type-directed desugaring of `ListLiteral` → cons/nil (or other collection types)
- Typing expressions (match, if, let, lambda) for evaluation
- Typing rule variables from usage context
- Verifying `requires` spec bindings
- IDE support: hover shows type at position, go-to-definition, diagnostics

Types themselves (sort definitions, field declarations) already live in the KB. The design question is: how do we represent *typing judgments* — the conclusion that expression E has type T?

A typing judgment is always about an expression *at a source position*. The same hash-consed term `gt(x, 0)` can appear at multiple positions with potentially different types. Without position, a typing judgment is either trivially derivable (literals) or ambiguous (which occurrence?). Therefore, typing judgments must reference positioned expressions — not bare terms.

The answer: **typing judgments are facts over ExprOccurrences**. We introduce `Occurrence` as the concept of a term at a source position, with its own non-hash-consed identity, and `ExprOccurrence` as a specialized occurrence that represents a positioned expression node. Each ExprOccurrence knows its *owner* — the declaration (operation, rule, fact) it belongs to, providing scope and typing context. A typing pass walks expression occurrences, checks them against declared types, and emits `TypeOf(occ, type)` facts. Type checking, inference, and desugaring are all rules that query `TypeOf` facts and navigate occurrence trees.

## Design

### Two identity layers: Terms and Occurrences

Anthill's KB has two kinds of identity, serving different purposes:

**TermId** — structural identity (hash-consed). Same structure = same id. Used for types, sort definitions, fact patterns, unification. `List[T=Int]` at line 5 and `List[T=Int]` at line 50 are the same TermId.

**OccurrenceId** — positional identity (not hash-consed). Each source position = unique id. Used for expressions, typing, error reporting. `gt(x, 0)` at line 10 and `gt(x, 0)` at line 20 are different OccurrenceIds, even though they share the same TermId.

Each Occurrence links to:
- A `TermId` — the structural content (for pattern matching, unification)
- A `Span` — the source position (for error reporting, IDE support)
- An **owner** — the containing declaration (operation, rule, or fact)

The owner connects an occurrence to its declaration context:
- For expression bodies: the operation that contains them (→ parameter types, return type, requires constraints)
- For fact field values: the fact assertion (→ entity declaration, field types via FieldInfo)
- For rule body terms: the rule (→ head variables, body scope)

This enables queries like "find all expressions in operation `foo`" and provides the typing pass with its top-down context (expected return type, parameter types, etc.) without having to re-derive it from the tree structure.

### OccurrenceStore

A new store, separate from the hash-consed TermStore:

```
TermStore       — hash-consed, structural sharing. For types, sorts, fact patterns.
OccurrenceStore — sequential ids, no deduplication. For source expressions.
                  Each entry: (OccurrenceId, TermId, Span, Owner)
                  Plus parent→child links for tree navigation.
```

Occurrences don't benefit from hash-consing — each source position is unique, so deduplication never fires. Sequential ids are simpler and faster.

### ExprOccurrence: typed occurrence

`ExprOccurrence` is a specialized occurrence whose term is an Expr node. It provides type safety — you can't pass a non-expression occurrence where an expression is expected. Leaf expressions (`int_lit`, `var_ref`, etc.) are also ExprOccurrences.

`ExprOccurrence` is the subject of typing judgments: `TypeOf(occ: ExprOccurrence, type: Sort)`.

### Occurrence as builtin

Occurrence is represented as a special sort with builtin-based querying. Like `nonvar`, `ground`, and `reify`/`reflect`, Occurrence operations are handled procedurally by the resolution engine, not stored as regular KB facts.

When the resolver encounters an Occurrence-related goal in a rule body, it routes to the OccurrenceStore instead of the regular fact index. This avoids bloating the KB with per-position facts while keeping occurrences queryable from anthill rules.

### Querying: structural + positional

Both layers are accessible in a single query:

```anthill
-- Navigate occurrence tree (positional)
rule gt_literal_in_if(?if_occ, ?lit_occ, ?val, ?type)
  :- if_expr(occ: ?if_occ, cond: ?cond_occ, then_branch: ?, else_branch: ?),
     -- Dereference occurrence to get term, then structural match
     occurrence(occ: ?cond_occ, term: apply(fn: gt, args: ?)),
     -- Navigate to child occurrence
     sub_occurrence(parent: ?cond_occ, position: 1, child: ?lit_occ),
     -- Structural match on child's term
     occurrence(occ: ?lit_occ, term: int_lit(value: ?val)),
     -- Get type from typing judgment
     TypeOf(occ: ?lit_occ, type: ?type)

-- Find all expressions owned by a specific operation
rule exprs_in_op(?occ, ?op)
  :- occurrence_owner(?occ, ?op)
```

- `occurrence(occ: ?occ, term: <pattern>)` — joins positional identity with structural matching (builtin)
- `sub_occurrence(parent: ?p, position: ?i, child: ?c)` — navigates the occurrence tree (builtin)
- `occurrence_owner(?occ, ?owner)` — links occurrence to its containing declaration (builtin)
- `TypeOf(occ: ?occ, type: ?type)` — typing judgment (KB fact)

### Reflect definitions

`Occurrence`, `ExprOccurrence`, and `Span` are added to `anthill.reflect`:

```anthill
-- Source position
sort Span
  entity span(file: String, start_line: Int, start_col: Int, end_line: Int, end_col: Int)
end

-- Opaque handle to a positioned term (not hash-consed)
sort Occurrence = ?

-- Positioned expression node — the subject of typing
sort ExprOccurrence = ?

-- Builtin operations on occurrences (in KB sort)
operation occurrence_term(occ: Occurrence) -> Term
operation occurrence_span(occ: Occurrence) -> Span
operation occurrence_owner(occ: Occurrence) -> Term
operation sub_occurrences(occ: Occurrence) -> List[T = Occurrence]
```

`Expr` is rebuilt around ExprOccurrences — each expression node's children are ExprOccurrences:

```anthill
sort Expr
  entity match_expr(scrutinee: ExprOccurrence, branches: List[T = MatchBranch])
  entity if_expr(cond: ExprOccurrence, then_branch: ExprOccurrence, else_branch: ExprOccurrence)
  entity let_expr(pattern: Pattern, value: ExprOccurrence, body: ExprOccurrence)
  entity lambda(param: Pattern, body: ExprOccurrence)
  entity apply(fn: Symbol, args: List[T = ApplyArg])
  entity constructor(name: Symbol, args: List[T = ApplyArg])
  entity var_ref(name: Symbol)
  entity int_lit(value: Int)
  entity float_lit(value: Float)
  entity string_lit(value: String)
  entity bool_lit(value: Bool)
end

entity ApplyArg(
  name: Option[Symbol],
  value: ExprOccurrence
)

entity MatchBranch(
  pattern: Pattern,
  guard: Option[ExprOccurrence],
  body: ExprOccurrence
)
```

Expr entities are stored in the OccurrenceStore and queried via builtins. Each Expr node IS an ExprOccurrence — it has an OccurrenceId, a TermId (the hash-consed structural content), a Span, and an owner (the containing declaration).

`TypedExpr` is replaced by `TypeOf`:

```anthill
sort TypeOf {
    entity TypeOf(occ: ExprOccurrence, type: Sort)
}
```

`TypeOf(occ, S)` means "the expression at occurrence `occ` has type `S`".

### The `TypeOf` relation

The typing pass emits `TypeOf` facts by walking occurrence trees and matching expressions against expected types from context (entity field declarations, operation signatures, etc.).

### What the typing pass does

The typing pass walks all declarations in scope order, operating on occurrence trees (from the parser), and emits `TypeOf` facts:

**Type context from declarations** — entity declarations establish expected types for each field position:
```anthill
entity WorkItem(id: String, status: WorkStatus, depends_on: List[T=String])
```
This declares: `id` expects `String`, `status` expects `WorkStatus`, `depends_on` expects `List[T=String]`. These expected types are already captured in `FieldInfo` in the KB. The typing pass reads them as context for typing value expressions — it does not emit `TypeOf` for field declarations themselves.

**Fact field values** — from each asserted fact:
```anthill
fact WorkItem(id: "WI-001", status: Open, depends_on: [])
```
Each field value is an ExprOccurrence (has a position in source, owned by this fact). The typing pass emits:
```anthill
fact TypeOf(occ: <occ of "WI-001">, type: String)         -- literal type, matches field context
fact TypeOf(occ: <occ of Open>, type: WorkStatus)          -- constructor type from parent sort
fact TypeOf(occ: <occ of []>, type: List[T=String])        -- from field context (collection type)
```

**Rule variables** — inferred from usage:
```anthill
rule open_item(?id, ?desc) :- WorkItem(id: ?id, description: ?desc, status: Open)
```
Each variable occurrence in the rule body gets a type from the field it appears in:
```anthill
fact TypeOf(occ: <occ of ?id in body>, type: String)       -- from WorkItem.id field type
fact TypeOf(occ: <occ of ?desc in body>, type: Term)       -- from WorkItem.description field type
```

**Expression nodes** — each subexpression occurrence gets a type:
```anthill
operation foo(x: Int) -> Bool = gt(x, 0)
```
```anthill
fact TypeOf(occ: <occ of x>,       type: Int)      -- from parameter
fact TypeOf(occ: <occ of 0>,       type: Int)      -- literal
fact TypeOf(occ: <occ of gt(x,0)>, type: Bool)     -- from operation return type
```

### Type context propagation (bidirectional)

Types propagate top-down from declarations and bottom-up from literals/constructors. This is standard bidirectional type checking (Pierce & Turner, 2000):

**Top-down** (expected type from context, derived via the occurrence's owner):
- Entity field declaration → expected type for field value (owner is the fact assertion)
- Operation parameter → expected type for argument (owner is the operation)
- Operation return type → expected type for expression body (owner is the operation)
- `requires` spec binding → expected type for bound parameter

**Bottom-up** (inferred type from value):
- Literal: `"hello"` → `String`, `42` → `Int`, `true` → `Bool`
- Constructor: `Open` → parent sort (`WorkStatus`)
- Constructor with fields: `cons(head: "a", tail: nil)` → `List[T=String]`

**Meeting point**: when top-down and bottom-up types meet at an occurrence, they must be compatible (via `type_compatible` rule from `typing.anthill`).

### Type-directed desugaring

Collection literal `[a, b, c]` is syntactically ambiguous — it could be `List`, `Array`, `Vector`, etc. Desugaring needs two things:

- **Collection type** — from top-down context (the field or parameter expects `List[T=?]` vs `Array[T=?]`)
- **Element type** — from bottom-up inference (literals, constructors) or from the collection type parameter

The collection type determines *how* to desugar:

```anthill
-- Context expects List → desugar to cons/nil
rule desugar_list(?occ, List[T=?t])
  :- TypeOf(occ: ?occ, type: List[T=?t]),
     occurrence(occ: ?occ, term: ListLiteral())

rule desugar_list(?occ, List[T=?t])
  :- TypeOf(occ: ?occ, type: List[T=?t]),
     occurrence(occ: ?occ, term: ListLiteral(?h, ?rest...)),
     sub_occurrence(parent: ?occ, position: 0, child: ?h_occ),
     TypeOf(occ: ?h_occ, type: ?t)

-- Context expects Vector → different construction
rule desugar_vector(?occ, Vector[T=?t])
  :- TypeOf(occ: ?occ, type: Vector[T=?t]),
     occurrence(occ: ?occ, term: ListLiteral(?items...))
```

Without context (no expected collection type), `[1, 2, 3]` is ambiguous — a default or an error.

The temporary `build_list_with_tail` desugaring in the loader is replaced by these rules once the typing pass exists.

### Typing as constraint checking

A type error is a contradiction between inferred type and expected type at an occurrence:

```anthill
-- Type error: inferred type doesn't match expected type at a position
constraint type_mismatch
  :- TypeOf(occ: ?occ, type: ?actual),
     expected_type(occ: ?occ, type: ?expected),
     not(type_compatible(?actual, ?expected))
```

Where `expected_type` is derived from the occurrence's owner and position — e.g., for a field value, the owner is the fact assertion and the expected type comes from `FieldInfo`; for an operation body, the owner is the operation and the expected type is its return type. This is a standard anthill constraint — the same mechanism used for any other invariant checking. Because TypeOf references ExprOccurrences, the error message includes the exact source position.

### No separate typed AST

The untyped terms (hash-consed in TermStore) stay unchanged. `TypeOf` facts annotate occurrences externally. This means:

- **Rules work on untyped terms** — structural pattern matching via `occurrence(occ: ?, term: <pattern>)`
- **Type info is queryable** — `TypeOf(occ: ?occ, type: ?type)` is a regular query
- **Gradual typing** — some occurrences may have `TypeOf`, others may not
- **Types are derivable** — rules can infer types, not just check them
- **Errors carry source positions** — TypeOf references Occurrences, which have Spans

## Implementation plan

### Phase 1: OccurrenceStore infrastructure
- Define `Occurrence`, `Span` sorts in `anthill.reflect`
- Implement `OccurrenceStore` in Rust (sequential ids, `(TermId, Span)` entries, parent→child links)
- Add builtin handlers for `occurrence(occ:, term:)` and `sub_occurrence(parent:, position:, child:)` queries
- Modify parser/converter to create Occurrences (preserving tree-sitter spans)

### Phase 2: Expr on Occurrences
- Rebuild `Expr` entities to use `Occurrence` for children
- Store Expr nodes in OccurrenceStore
- Route Expr queries through builtin occurrence handlers
- Remove old `TypedExpr` sort

### Phase 3: TypeOf infrastructure
- Define `TypeOf` sort in `anthill.reflect`
- Add typing pass (after `load_all`, before constraint checking)
- Read entity field declarations (`FieldInfo`) as type context
- Emit `TypeOf` for literal occurrences (bottom-up)
- Emit `TypeOf` for nullary constructor occurrences (from entity parent sort)

### Phase 4: Fact typing
- Walk each asserted fact's field value occurrences
- Match against declared field types (via `FieldInfo`)
- Emit `TypeOf` for each field value occurrence
- Detect type mismatches (field type ≠ value type)

### Phase 5: ListLiteral desugaring
- When `TypeOf(<occ>, List[T=?t])` is derived for a ListLiteral occurrence
- Replace with cons/nil in the KB
- Remove temporary desugaring from loader's `convert_term`

### Phase 6: Rule variable typing
- For each rule body literal, match variable occurrences against entity field types
- Infer variable types from field position
- Emit `TypeOf` for each variable occurrence

### Phase 7: Expression typing
- Walk expression occurrence trees (match, if, let, lambda, apply)
- Propagate types through occurrence nodes (bidirectional)
- Emit `TypeOf` for each subexpression occurrence
- Enable expression evaluation with type safety

### Phase 8: Constraint integration
- Define `type_mismatch` constraint
- Run constraint checker after typing pass
- Report type errors as constraint violations (with source positions from Occurrences)

## Examples

### Well-typed fact
```anthill
entity Task(id: String, priority: Int)

fact Task(id: "T-001", priority: 3)

-- Parser creates occurrences:
--   occ#1: "T-001" at line 3, col 15-22
--   occ#2: 3       at line 3, col 34-35
-- Typing pass emits:
fact TypeOf(occ: occ#1, type: String)     -- matches Task.id: String ✓
fact TypeOf(occ: occ#2, type: Int)        -- matches Task.priority: Int ✓
```

### Type error
```anthill
fact Task(id: 42, priority: "high")

-- Occurrences:
--   occ#3: 42     at line 5, col 15-17
--   occ#4: "high" at line 5, col 29-35
-- Typing pass emits:
fact TypeOf(occ: occ#3, type: Int)        -- but Task.id expects String ✗
fact TypeOf(occ: occ#4, type: String)     -- but Task.priority expects Int ✗

-- Constraint fires:
-- type_mismatch at line 5, col 15-17: expected String, got Int
-- type_mismatch at line 5, col 29-35: expected Int, got String
```

### Expression typing with occurrence navigation
```anthill
operation foo(x: Int) -> Bool = gt(x, 0)

-- Occurrence tree:
--   occ#10: gt(x, 0)  at line 1, col 32-40
--     occ#11: x        at line 1, col 35
--     occ#12: 0        at line 1, col 38
-- Sub-occurrences:
--   sub_occurrence(parent: occ#10, position: 0, child: occ#11)
--   sub_occurrence(parent: occ#10, position: 1, child: occ#12)
-- Types:
fact TypeOf(occ: occ#10, type: Bool)    -- from operation return type
fact TypeOf(occ: occ#11, type: Int)     -- from parameter declaration
fact TypeOf(occ: occ#12, type: Int)     -- literal

-- Query: "find all comparisons with literal arguments"
rule gt_with_literal(?call, ?lit, ?val)
  :- occurrence(occ: ?call, term: apply(fn: gt, args: ?)),
     sub_occurrence(parent: ?call, position: 1, child: ?lit),
     occurrence(occ: ?lit, term: int_lit(value: ?val))
-- Binds: ?call = occ#10, ?lit = occ#12, ?val = 0
```

### ListLiteral desugaring
```anthill
entity WorkItem(depends_on: List[T=String])

fact WorkItem(depends_on: ["WI-001", "WI-002"])

-- Occurrence tree:
--   occ#20: ["WI-001", "WI-002"]  at line 3, col 27-48
--     occ#21: "WI-001"            at line 3, col 28-36
--     occ#22: "WI-002"            at line 3, col 38-47
-- Typing:
--   TypeOf(occ#20, List[T=String])  -- from field context (top-down)
--   TypeOf(occ#21, String)          -- literal (bottom-up) ✓
--   TypeOf(occ#22, String)          -- literal (bottom-up) ✓
-- Desugaring: occ#20 → cons(head: "WI-001", tail: cons(head: "WI-002", tail: nil))
```

## Relationship to existing work

- **Proposal 011** (Type Resolution): This proposal is the concrete implementation of Proposal 011's philosophy ("type checking = KB querying"). The Occurrence layer adds the positional identity that 011's constraint-based approach needs. Path B (syntactic instantiation) is kept.
- **Proposal 019** (Collection Literals): ListLiteral desugaring moves from the loader hack to type-directed rules over occurrence trees.
- **typing.anthill**: Existing `type_compatible`, `refines`, `is_entity_of` rules are used by the typing pass.
- **SortView**: Parameterized types (`List[T=String]`) are already SortView terms — `TypeOf` types reference them.
- **rust-term-store-design.md**: OccurrenceStore is a new store alongside TermStore. Terms stay hash-consed and immutable. Occurrences are sequential and not hash-consed — different design trade-offs for different purposes.
- **reflect.anthill**: `Expr` sort is rebuilt with `Occurrence` children instead of `Expr` self-references. `TypedExpr` is replaced by `TypeOf(occ, type)` facts.

## Design rationale: why Occurrences?

### Why not `TypeOf(term: Term, type: Sort)`?

Hash-consed terms lose positional identity. `"hello"` is one TermId everywhere — you can't distinguish `"hello"` in a String field from `"hello"` in an Int field. TypeOf on bare terms is either trivially derivable (literals always have their natural type) or ambiguous (which occurrence?).

### Why not a separate typed AST?

A typed AST duplicates the term structure with type annotations baked in. This is rigid — you can't gradually add types, query them independently, or derive them via rules. TypeOf as facts over Occurrences is more flexible and stays within anthill's "everything is facts" philosophy.

### Why builtin-based querying?

Storing every occurrence as a regular KB fact would bloat the fact base (every subexpression at every position). Builtins route occurrence queries to the OccurrenceStore directly — efficient storage, same query interface.

## Non-goals

- **Dependent types**: Types depending on runtime values. Out of scope.
- **Higher-kinded types**: `Functor[F]` where `F` is a type constructor. Future work.
- **Linear types**: Tracking resource usage. Not needed for Stage 0.
- **Effect typing**: Effect annotations on operations exist syntactically but are not checked. Future work.
