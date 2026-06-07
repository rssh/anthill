# Proposal 019: Collection Literals

**Status:** Proposed
**Depends on:** None (complementary to Proposal 020)
**Affects:** Kernel Language Specification §4 (Terms), Grammar, Parse Converter

## Motivation

The anthill List type (`anthill.prelude.List`) is a cons-list with constructors `cons(head: T, tail: List)` and `nil`. Writing lists explicitly is verbose:

```anthill
fact parent("alice", children: cons(head: "bob", tail: cons(head: "carol", tail: nil)))
```

This is the only reason Stage 0 sugar (`workitem`, `project`, `tool`, `feedback`) exists as separate grammar productions. These keywords provide list-field convenience (among other things) for specific entity types, coupling the grammar to user-defined domain types.

With collection literals, the same fact is:

```anthill
fact parent("alice", children: ["bob", "carol"])
```

And Stage 0 entities need no special syntax:

```anthill
-- Currently requires workitem sugar:
workitem WI-AUTH-001 {
  description: "Define auth traits"
  acceptance: Compiles({ path: "src", scope: Main })
  depends_on: [WI-AUTH-002]
  status: Open
}

-- With collection literals, plain fact works:
fact WorkItem("WI-AUTH-001",
  description: "Define auth traits",
  acceptance: [Compiles(SourceRoot(path: "src", scope: Main))],
  depends_on: ["WI-AUTH-002"],
  status: Open)
```

This eliminates the need for entity-specific grammar rules, decoupling the parser from any particular domain's entity types.

## Design

### Collection literal as a general concept

Anthill already has set literals (`{a, b}`) and tuple literals (`(a, b)`). Each uses distinct delimiters and desugars to different constructors. The `[a, b]` bracket literal completes the picture for ordered sequences.

| Literal | Syntax | Representation |
|---|---|---|
| Tuple | `(a, b)` | `TupleLiteral(_1: a, _2: b)` |
| Set | `{a, b}` | `SetLiteral(a, b)` |
| **Collection** | **`[a, b]`** | **`ListLiteral(a, b)`** |

Each uses distinct delimiters — no ambiguity. All three follow the same pattern: the parser produces a literal term in the **untyped** term representation. Desugaring to concrete constructors (e.g. `cons`/`nil` for List, or target-specific constructors for other collection types) is the responsibility of the **typing process** (see Proposal 011), which transforms untyped terms into typed terms.

### Untyped vs typed representation

This proposal defines `ListLiteral` as part of the **untyped** term language — the representation produced by the parser before type resolution. The untyped term language already includes `SetLiteral` and `TupleLiteral` in the same role.

The **typing process** (Proposal 011) will:
1. Determine the target collection type from the typed term context (e.g. a field declaration `items: List[T = Int64]`, a parameter type, or a default)
2. Rewrite `ListLiteral(a, b)` into the typed term with concrete constructors (e.g. `cons(a, cons(b, nil))` for List)

How the typing process propagates expected types and resolves the target collection sort is out of scope for this proposal — it belongs to the typing process definition in Proposal 011. This proposal only defines the syntax and the untyped parse IR representation.

### Why not desugar to cons/nil directly?

A cons-list is O(n) for random access and O(n) space overhead per element. It is the right structure for recursive pattern matching in logic programs, but not the only ordered sequence type an anthill program may need. The standard library already defines:

- **List** (`anthill.prelude.List`) — cons-list, pattern-matchable
- **Stream** (`anthill.prelude.Stream`) — lazy sequence with effects
- **Map** (`anthill.prelude.Map`) — key-value associations

Future collections (vectors, arrays, deques) may also want literal syntax. By keeping `ListLiteral` as an untyped syntactic form, the parser stays neutral and the typing process chooses the target.

### Syntax

```
Term ::= ...
       | '[' ']'                                 -- empty collection
       | '[' Term (',' Term)* ']'                -- non-empty collection
       | '[' Term (',' Term)* '|' Term ']'       -- head|tail (cons destructuring)
```

Square brackets `[...]` are unambiguous in the grammar — they are not used in any other term position. (The sugar rules use `[...]` inside `depends_on`, `generates`, `args` fields, but those are sugar-specific productions, not general terms.)

If Proposal 020 (bracket type parameters) is accepted, `Name[...]` is type parameterization while bare `[...]` is a collection literal — disambiguated by the leading `Name`, same pattern as `Name{...}` vs `{...}` for instantiation vs set literals.

### Head|tail syntax and the Collection/Iteration sorts

The `[?first | ?rest]` form is element/rest destructuring, essential for recursive pattern matching:

```anthill
-- Match a workitem with at least one dependency
rule has_deps(?id)
  :- WorkItem(id: ?id, depends_on: [?first | ?rest])

-- Recursive list processing
rule all_verified([])
rule all_verified([?item | ?rest])
  :- verified(?item), all_verified(?rest)
```

This syntax is not restricted to cons-lists. Construction and destruction are separate algebraic interfaces (sorts), parameterized by an effect set (since effectful types like `Stream` also need literal syntax support):

```anthill
-- Destruction: decompose into first element and rest
sort Iteration {
  sort Iterator = ?
  sort Element = ?
  sort Effect = ?
  operation split(i: Iterator) -> Option[T = (Element, Iterator)]
    effects (Effect)
}

-- Construction: build from elements (implies Iteration)
sort Collection {
  sort Collection = ?
  sort Element = ?
  sort Effect = ?
  requires Iteration[Iterator = Collection, Element, Effect]
  operation add(c: Collection, elem: Element) -> Collection
    effects (Effect)
  operation empty() -> Collection
}
```

Naming convention: sort names are nouns/concepts (`Collection`, `Iteration`, `Equality`, `Order`). The carrier parameter names the thing (`Collection`, `Iterator`, `Equable`, `Orderable`) — it may shadow the sort name when they coincide. Sorts with entities (data types) use concrete nouns (`List`, `Stream`, `Color`). The formal sort/data keyword separation is a separate proposal.

`Collection` requires `Iteration` — if you can build a collection, you can decompose it. But not vice versa: `Stream` is iterable but not collectable (you can't `add` to it).

The `Effect` parameter is just a sort parameter like any other. Types that have effects carry them, types that don't have an empty set:

```anthill
sort List {
  sort E = ?
  entity cons(head: E, tail: List[E])
  entity nil
}

-- List is collectable, pure (empty effect set)
fact Collection[List[E], E, {}]

-- Stream is iterable (but not collectable), effectful
fact Iteration[Stream[E, Eff], E, Eff]
```

The typing process desugars literal syntax using these sorts:
- `[a, b, c]` in construction position → `add(add(add(empty(), a), b), c)` (needs `Collection`)
- `[?h | ?t]` in pattern position → `split(c) = some((?h, ?t))` (needs `Iteration`)
- `[]` in pattern position → `split(c) = none()` (needs `Iteration`)

Any data type satisfying `Collection` gains full literal syntax support. Types satisfying only `Iteration` (like `Stream`) support `[h | t]` pattern matching but not literal construction.

### Collection fields don't need Option

Types satisfying `Collection` have `empty()`, so `Option[List[...]]` is redundant — the empty list represents absence:

```anthill
entity WorkItem(id: String, depends_on: List[String], status: Status)

fact WorkItem("WI-001", depends_on: ["WI-002"], status: Open)
fact WorkItem("WI-002", depends_on: [], status: Open)
```

### Pattern matching

Collection literals in pattern position (rule bodies, queries) desugar via `Iteration.split`:

```anthill
-- Match a workitem with exactly two dependencies
rule two_deps(?id)
  :- WorkItem(id: ?id, depends_on: [?a, ?b])

-- Match a workitem with at least one dependency (head|tail)
rule has_deps(?id)
  :- WorkItem(id: ?id, depends_on: [?first | ?rest])

-- Empty collection
rule no_deps(?id)
  :- WorkItem(id: ?id, depends_on: [])
```

This works for any type satisfying `Iteration`, not just `List`.

## Grammar Changes

In `grammar.js`, add to `_atom_term`:

```js
_atom_term: $ => choice(
  // ... existing alternatives ...
  $.collection_literal,      // NEW
),

collection_literal: $ => choice(
  seq('[', ']'),                                                          // empty
  seq('[', commaSep1($._term), optional(seq('|', $._term)), ']'),        // elements [, | tail]
),
```

No new keywords. No ambiguity with existing syntax.

## Converter Changes (Untyped IR)

The converter produces `ListLiteral` as an untyped `Term::Fn` — the same representation used for `SetLiteral` and `TupleLiteral`. In `convert.rs`, add `convert_collection_literal`:

```rust
fn convert_collection_literal(&mut self, node: Node) -> TermId {
    let elements: Vec<TermId> = /* child terms */;
    let tail: Option<TermId> = /* optional tail after | */;

    // Produce ListLiteral(e1, e2, ...) — same pattern as SetLiteral
    let args: Vec<FnArg> = elements.into_iter()
        .map(|id| FnArg { name: None, value: id })
        .collect();
    let functor = self.intern("ListLiteral");
    self.terms.alloc(Term::Fn { functor, args: args.into() })
}
```

For the `[h | t]` form, the tail is stored as a distinguished named argument:

```rust
// [a, b | t] → ListLiteral(a, b, tail: t)
if let Some(tail_id) = tail {
    args.push(FnArg { name: Some(self.intern("tail")), value: tail_id });
}
```

### Reflect representation

Add to `anthill.reflect`:

```anthill
-- Collection literal syntax: [x, y, z] is represented as ListLiteral(x, y, z)
-- in the untyped term language. The typing process (Proposal 011) rewrites
-- this to concrete constructors based on the expected type.
-- Head|tail form: [x, y | t] → ListLiteral(x, y, tail: t).
entity ListLiteral
```

This mirrors the existing `SetLiteral` and `TupleLiteral` entities.

## Impact on Stage 0 Sugar

With collection literals, the Stage 0 sugar becomes redundant for most use cases:

| Current sugar | Plain fact equivalent |
|---|---|
| `workitem WI-001 { acceptance: ToolPasses(t) }` | `fact WorkItem("WI-001", acceptance: [ToolPasses("t")], status: Open)` |
| `tool lint { args: ["a", "b"] }` | `fact ToolDef("lint", command: "make", args: ["a", "b"], success: ExitZero)` |
| `depends_on: [A, B]` | `depends_on: ["A", "B"]` |

The sugar can be deprecated incrementally:
1. Add collection literals (this proposal)
2. Update examples to use plain `fact` with collection literals
3. Mark sugar grammar rules as deprecated
4. Eventually remove sugar rules from the grammar

## Non-goals

- **List comprehensions** — `[f(x) | x <- xs, p(x)]` is a future concern (note: `|` in comprehensions would use `<-` to distinguish from head|tail)
- **Typed collection literals** — `[Int64]` as a type expression is out of scope (use `List[T = Int64]`)
- **Heterogeneous collections** — the type system handles this, not the literal syntax
- **Splicing** — `[a, ...xs, b]` is out of scope
- **Map literals** — `{k: v, ...}` could be a future proposal using `{}` with `:` pairs (distinguished from set literals by the `:` separator)
