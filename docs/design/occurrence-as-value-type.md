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
        /// Typer-attached classification (WI-231). RefCell because the typer
        /// mutates this after construction while other walkers may hold
        /// shared Rc references to the same NodeOccurrence.
        classification: RefCell<Option<Box<CallClass>>>,
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
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
    HoApply {
        predicate: Rc<NodeOccurrence>,
        args: Vec<Rc<NodeOccurrence>>,
    },
    Constructor {
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
    Match { scrutinee: Rc<NodeOccurrence>, branches: Vec<MatchBranch> },
    If {
        condition: Rc<NodeOccurrence>,
        then_branch: Rc<NodeOccurrence>,
        else_branch: Rc<NodeOccurrence>,
    },
    Let {
        pattern: TermId,
        type_annotation: Option<TypeExpr>,
        value: Rc<NodeOccurrence>,
        body: Rc<NodeOccurrence>,
    },
    Lambda { param: TermId, body: Rc<NodeOccurrence> },
    Instantiation {
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },
    ListLit(Vec<Rc<NodeOccurrence>>),
    SetLit(Vec<Rc<NodeOccurrence>>),
    TupleLit {
        positional: Vec<Rc<NodeOccurrence>>,
        named: Vec<(Symbol, Rc<NodeOccurrence>)>,
    },

    // Post-elaboration forms (produced by req_insertion / typer rewrites)
    ApplyWithin {
        functor: Symbol,
        args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        requirements: Vec<Rc<NodeOccurrence>>,
    },
    HoApplyWithin { predicate: Rc<NodeOccurrence>, args: Vec<Rc<NodeOccurrence>>,
                    requirements: Vec<Rc<NodeOccurrence>> },
    ConstructorWithin {
        name: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        requirements: Vec<Rc<NodeOccurrence>>,
    },
    LambdaWithin {
        param: TermId,
        body: Rc<NodeOccurrence>,
        requirements: Vec<Rc<NodeOccurrence>>,
    },
    RequirementAtSort { chain: Rc<NodeOccurrence>, slot: i64 },
    ConstructRequirement {
        impl_functor: Symbol,
        requirements: Vec<Rc<NodeOccurrence>>,
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
    pub guard: Option<Rc<NodeOccurrence>>,
    pub body: Rc<NodeOccurrence>,
    pub span: SourceSpan,
}
```

Patterns remain `TermId` (current handling unchanged — minimum work; pattern
reform is a separate concern).

## Why Rc-linked trees throughout

Every child slot in `Expr` (and `MatchBranch`) is `Rc<NodeOccurrence>`, not bare
`NodeOccurrence` or `Box<NodeOccurrence>`. The whole tree is Rc-linked from the
start. Three benefits:

1. **Reflection bindings are cheap.** `body_of(?op, ?body)` etc. need to bind a
   Value to a NodeOccurrence in the KB. With `Rc`, the binding is one atomic
   refcount increment (`Rc::clone`); no deep tree copy. With `Box`, reflection
   would have to deep-clone every time, paying O(tree size) per query.

2. **Eval frame stack stash is free of lifetime issues.** Eval keeps `occ: Rc<NodeOccurrence>`
   on its step-stack frame for runtime error spans. The Rc owns its share, so
   the frame can outlive any borrow into the original tree. No lifetime
   annotations to thread.

3. **Cross-pass / cross-frame identity via `Rc::ptr_eq`.** When the typer's
   `Synthesized { from: Rc<NodeOccurrence>, by: PassId }` needs to compare
   "is this the same occurrence as that one?" — pointer equality on Rc is O(1).

Atomic refcount cost is negligible relative to the work each pass does per node.

## Value variant

```rust
pub enum Value {
    // ... existing variants ...
    Int(i64), BigInt(BigInt), Float(f64), Bool(bool), Str(String), Unit,
    Tuple { pos, named }, Entity { functor, pos, named },
    Term(TermId),                                // hash-consed KB content
    Closure(...), Stream(...), Lazy(...),
    Substitution(...), Map(...), Cell(...), Requirement(...),

    // NEW: positional content
    Node(Rc<NodeOccurrence>),
}
```

One variant. The `NodeKind` inside the Rc'd NodeOccurrence tells you whether
this binding is Expr-kind, RuleHead-kind, or a future kind. Reflection ops like
`body_of`, `args_of`, `head_of` all bind this same variant.

No separate Value-side arena. The four reasons that would justify one
(hash-consing / cross-pass side tables / handle-keyed lookups / 4-byte stash)
don't materialize for Value bindings — `Rc<NodeOccurrence>` covers the actual
need (shared ownership across substitutions) without introducing another store.

The `NodeOccurrence::origin` field (when kind is `Expr`) holds
`OccurrenceOrigin { Source | Synthesized { from, by } }` per WI-243's substrate.
The `from: OccurrenceId` field becomes `from: Rc<NodeOccurrence>` (pointer
identity to the source occurrence via `Rc::ptr_eq`; cheap clone via Rc::clone).

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
