# NodeOccurrence — KB-side positional wrapper

## Status

Design. Establishes the KB-layer naming and structure for positional content
(spans, owners, classifications). Supersedes the arena+ID `OccurrenceStore`
model from `docs/design/expr-occurrences.md`.

## Summary

`NodeOccurrence` is a value-typed struct that wraps positional metadata (span,
owner) around content. Its `kind: NodeKind` enum names what kind of content
this occurrence holds — Expression, RuleHead, or future kinds. Each child slot
inside an Expr variant is itself a `NodeOccurrence` (alternating
`NodeOccurrence ⇄ NodeKind ⇄ Expr ⇄ NodeOccurrence`).

This replaces the current arena+ID model (`OccurrenceStore` + `OccurrenceId` +
`Term::Const(Literal::Handle(Occurrence, _))` wrapper).

Parse-IR layer is unchanged — `Item` enum and the existing struct types
(`Namespace`, `Operation`, `Fact`, `Rule`, etc.) stay as today. The loader is
the conversion boundary; it walks `Item`s and produces either KB-side `Term`
(hash-consed, content-position) or KB-side `NodeOccurrence` (positional,
expression-position).

## The shape

```rust
pub struct NodeOccurrence {
    pub kind: NodeKind,
    pub span: SourceSpan,
    pub owner: Option<Symbol>,
}

pub enum NodeKind {
    /// Expression content (operation bodies, lambda bodies, conditional
    /// branches, match arms, let values/bodies).
    Expr {
        expr: Expr,
        origin: OccurrenceOrigin,
        classification: Option<Box<CallClass>>,
    },
    /// Rule head — positional wrapper around a Term-shaped head pattern.
    RuleHead {
        functor: Symbol,
        pos_args: Vec<TermId>,
        named_args: Vec<(Symbol, TermId)>,
    },
    // Future kinds added here as concrete needs arise:
    //   Type { ... }, Pattern { ... }, etc.
}

pub enum Expr {
    // Compound — children are NodeOccurrences (alternating back)
    Apply {
        functor: Symbol,
        pos_args: Vec<NodeOccurrence>,
        named_args: Vec<(Symbol, NodeOccurrence)>,
    },
    HoApply {
        predicate: Box<NodeOccurrence>,
        args: Vec<NodeOccurrence>,
    },
    Constructor {
        name: Symbol,
        pos_args: Vec<NodeOccurrence>,
        named_args: Vec<(Symbol, NodeOccurrence)>,
    },
    Match { scrutinee: Box<NodeOccurrence>, branches: Vec<MatchBranch> },
    If {
        condition: Box<NodeOccurrence>,
        then_branch: Box<NodeOccurrence>,
        else_branch: Box<NodeOccurrence>,
    },
    Let {
        pattern: TermId,
        type_annotation: Option<TypeExpr>,
        value: Box<NodeOccurrence>,
        body: Box<NodeOccurrence>,
    },
    Lambda { param: TermId, body: Box<NodeOccurrence> },
    Instantiation {
        name: Symbol,
        pos_args: Vec<NodeOccurrence>,
        named_args: Vec<(Symbol, NodeOccurrence)>,
    },
    ListLit(Vec<NodeOccurrence>),
    SetLit(Vec<NodeOccurrence>),
    TupleLit {
        positional: Vec<NodeOccurrence>,
        named: Vec<(Symbol, NodeOccurrence)>,
    },

    // Post-elaboration forms (produced by req_insertion / typer rewrites)
    ApplyWithin {
        functor: Symbol,
        args: Vec<NodeOccurrence>,
        named_args: Vec<(Symbol, NodeOccurrence)>,
        requirements: Vec<NodeOccurrence>,
    },
    HoApplyWithin { predicate: Box<NodeOccurrence>, args: Vec<NodeOccurrence>,
                    requirements: Vec<NodeOccurrence> },
    ConstructorWithin {
        name: Symbol,
        pos_args: Vec<NodeOccurrence>,
        named_args: Vec<(Symbol, NodeOccurrence)>,
        requirements: Vec<NodeOccurrence>,
    },
    LambdaWithin {
        param: TermId,
        body: Box<NodeOccurrence>,
        requirements: Vec<NodeOccurrence>,
    },
    RequirementAtSort { chain: Box<NodeOccurrence>, slot: i64 },
    ConstructRequirement {
        impl_functor: Symbol,
        requirements: Vec<NodeOccurrence>,
    },
    VarRef { name: Symbol },

    // Leaves — no further alternation
    Var(Var),
    Const(Literal),
    Ref(Symbol),
    Ident(Symbol),
    Bottom,
}

pub struct MatchBranch {
    pub pattern: TermId,
    pub guard: Option<NodeOccurrence>,
    pub body: NodeOccurrence,
    pub span: SourceSpan,
}
```

Patterns remain `TermId` (current handling unchanged — minimum work; pattern
reform is a separate concern).

The `NodeOccurrence::origin` field (when kind is `Expr`) holds
`OccurrenceOrigin { Source | Synthesized { from, by } }` per WI-243's substrate.
The `from: OccurrenceId` field becomes `from: Rc<NodeOccurrence>` (pointer
identity to the source occurrence; cheap clone via Rc).

## Why eliminate the arena (OccurrenceStore + OccurrenceId)

Four reasons can justify an arena+ID pattern:

1. **Hash-consing** — items share storage by structural identity.
2. **Cross-pass identity** — pass A writes annotation at id i; pass B reads at i.
3. **Side-table cheap lookup** — `HashMap<Id, _>` hashable on a u32.
4. **Compact stack/frame stash** — 4 bytes vs `Box<T>`'s 8 bytes + heap.

After WI-243's cleanup, the actual material justifications shrank:

| Reason | Materialized? |
|---|---|
| Hash-consing | **No** — occurrences are positional by definition; no sharing. |
| Cross-pass side tables | **No** — design doc forbids them; on-entry fields preferred. Only `CallClass` channel; lives on the entry. |
| `by_term` / `by_functor` indexes | **Weak** — `by_term` has 3 callers for span lookup; `by_functor` dormant. |
| Eval stack 4-byte stash | **Real** — eval keeps `occ` on its step-stack frame for runtime errors. |

Only the last is materially load-bearing, and `Rc<NodeOccurrence>` covers it
(atomic refcount ops are cheap; clone semantics predictable).

## Which IDs survive

| ID | Justification | Stays? |
|---|---|---|
| `TermId` (KB) | Hash-consing — structurally identical terms share storage. | Yes |
| `Symbol` | Interning — every string deduplicates to a u32. | Yes |
| `VarId` | Fresh-variable allocation; cross-rule unique counter. | Yes |
| `RuleId`, `SourceId`, `FactId` | Indexes into small Vecs of long-lived entities; index = identity. | Yes |
| `OccurrenceId` (KB) | Arena handle for a value-typed concept. Translation cost without payoff. | **No** |

Parse-IR `TermId` (into `SimpleTermStore`) also stays — parse IR layer is
unchanged in this WI.

## Architecture end-to-end

```
.anthill source
     │
     ▼
parser → ParsedFile { items: Vec<Item>, terms: SimpleTermStore, ... }
                       (existing types — unchanged)
     │
     ▼
loader  (the conversion boundary)
     │
     │  Inspects each Item's content; routes based on context:
     │
     ├─ Expression-position content      ─►  NodeOccurrence { kind: Expr { ... } }
     │   (operation/lambda bodies, etc.)      (owned tree)
     │
     ├─ Rule heads                       ─►  NodeOccurrence { kind: RuleHead { ... } }
     │
     └─ KB-position content              ─►  Term (hash-consed in TermStore)
         (fact bodies, rule body atoms,        spans optionally to `fact_spans`
          type terms, query patterns)          side table if diagnostics need them
     │
     ▼
KB
  ─ TermStore (hash-consed Terms)
  ─ OperationInfo.body: Option<NodeOccurrence>
  ─ Rule head stored as NodeOccurrence
  ─ Optional fact_spans: HashMap<TermId, SourceSpan> for fact diagnostics

Resolve / Type-check / Eval
  ─ Passes walk owned NodeOccurrence trees.
  ─ CallClass classifications mutate the kind: Expr variant's classification field.
  ─ Eval frame stack carries Rc<NodeOccurrence> for runtime error spans.

Runtime values
  ─ Value::Node(Rc<NodeOccurrence>) for reflection bindings.
```

No `OccurrenceStore`, no `OccurrenceId`, no `Term::Const(Literal::Handle(Occurrence, _))` wrapper.

## reflect (anthill stdlib)

Rename and consolidate:

```anthill
sort NodeOccurrence = ?              # was: sort Occurrence (bare; confusing)

# `sort ExprOccurrence` becomes derivable as the subset of NodeOccurrences
# whose kind is Expr — either kept as an alias for clarity or eliminated.

sort Expr = ?                         # unchanged (structural variants: apply, match_expr, ...)

operation occurrence_span(occ: NodeOccurrence) -> SourceSpan
operation occurrence_owner(occ: NodeOccurrence) -> Symbol
operation occurrence_kind(occ: NodeOccurrence) -> NodeKind     # or similar dispatching op
```

Concrete entities like `match_expr`, `apply_within`, etc. (in reflect lines
318-358) take `NodeOccurrence` (was `ExprOccurrence`) — they're polymorphic
over the supertype, with the understanding that consumers verify kind=Expr.

## Migration touch-points

The migration touches:

- **~50 eval-stack sites** that today stash `occ: OccurrenceId` switch to `occ: Rc<NodeOccurrence>`.
- **3 `by_term` reverse-lookup sites** in `typing.rs` migrate to direct walking.
- **All `kb.occurrences.alloc(...)` sites** become constructor calls (`NodeOccurrence { kind: NodeKind::Expr { ... }, ... }`).
- **Loader (`load.rs`)** stops constructing Handle wrappers; instead builds NodeOccurrence trees directly during conversion.
- **Synthesizing passes** (when they exist — none today after WI-243 cleanup) construct fresh NodeOccurrences with `origin: Synthesized { from, by }`.

## What stays as-is

- **Parse IR** — `Item` enum, all variant struct types (`Namespace`, `Operation`, `Fact`, `Rule`, `Entity`, `Constraint`, ...) unchanged.
- **`Term`, `TermId`, `Symbol`, `Var`** — all KB and parse-IR types unchanged.
- **KB-position content paths** — rule body atoms, fact bodies, type terms, query patterns flow through `Term` (hash-consed) as today.
- **Patterns** — `Term::Fn{pattern_*}` form unchanged. Pattern reform is a separate concern.

## What this means for in-flight WIs

### WI-245 — superseded

Originally scoped as parse-IR `Expr` mirror. Parse IR is now staying unchanged.
The parse-side typed-occurrences direction is dropped. Close as superseded.

### WI-242 — KB-side restructuring

**Scope under this design**:
- Introduce `NodeOccurrence` + `NodeKind` + `Expr` types at KB layer.
- Loader builds NodeOccurrence trees directly (no Handle wrapper).
- `OperationInfo.body` becomes `Option<NodeOccurrence>`.
- Rule heads become `NodeOccurrence` (kind=RuleHead).
- Eliminate `OccurrenceStore`, `OccurrenceId`, `Term::Const(Literal::Handle(Occurrence, _))`.
- Migrate eval to `Rc<NodeOccurrence>`.
- Add `Value::Node(Rc<NodeOccurrence>)` runtime variant for reflection bindings.
- Migrate `by_term` callsites.
- Reflect rename: `sort Occurrence` → `sort NodeOccurrence`; rewire operations.

Estimated ~500-800 LOC across `kb/`, `eval/`, codegens, persistence, and reflect.

### WI-243 (delivered) — substrate

`OccurrenceOrigin::Synthesized { from, by }` stays as a field on
`NodeKind::Expr`'s variant. `PassId`, `register_pass` stay. The `alloc_synthesized`
API moves to a `NodeOccurrence::synthesized(...)` constructor.

### WI-238 — superseded

WI-242 subsumes it under the new design.

## Anti-pattern this doc establishes

Don't introduce an arena+ID layer for a value-typed concept just because:
- "We might want side tables later." (We didn't.)
- "It's the standard compiler pattern." (Standard for hash-consed content. Not for positional identity.)
- "4 bytes is smaller than `Box<T>`." (True, but only matters in tight loops; the eval frame stack is the only such place, and `Rc::clone` is cheap.)

If a value type maps 1:1 to a user-facing semantic concept (here:
`anthill.reflect.NodeOccurrence`), keep it as a value type. Introduce an arena
only when at least one of the four reasons (hash-consing / cross-pass identity
/ side-table dispatch / hot-path stash) is concretely load-bearing.

## Reference

- `stdlib/anthill/reflect/reflect.anthill:74-90` — reflect's `Occurrence` and `ExprOccurrence` sorts (to be renamed).
- `docs/design/expr-occurrences.md` — original arena+ID design (superseded).
- WI-243 delivery feedback — establishes `OccurrenceOrigin` substrate (still applies).
- WI-242 — open; reframed against this doc.
- WI-245 — superseded.
- WI-238 — superseded by WI-242.
