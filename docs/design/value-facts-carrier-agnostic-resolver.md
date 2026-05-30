# Value facts — a carrier-agnostic SLD resolver

Tracking: **WI-348** (status Open). Filed 2026-05-30.

**Concrete consumer: `OperationInfo` must be SLD-queryable.** The reflect
introspection API (`operations(kb, sort_name) -> List[OperationInfo]`, and
`:- OperationInfo(name: ?n)`-style rules) queries `OperationInfo` against the
**search layer** — so it must be a *fact*, not a Rust-side record (a record is
invisible to SLD). And `OperationInfo` carries `denoted` (effects `Modify[c]`,
eventually denoted params/return), so that fact must carry `Value::Node`. A
queryable, Node-carrying fact **is** a value fact. So this is not speculative:
`OperationInfo`-queryability is the consumer that requires value facts.

## Problem

WI-342 made the **typer** carrier-agnostic: a `denoted`-bearing type rides as a
`Value::Node` (an `Rc<NodeOccurrence>`) and `unify_types` / `types_compatible`
walk any carrier through `TermView`. But the **KB's fact/SLD layer is still
`TermId`-only** — `assert_fact` takes a hash-consed `TermId`, the discrimination
tree indexes `TermId`, and the resolver matches `TermId` heads.

The visible symptom is **side-table proliferation**. Each piece of operation
metadata that wants to carry a `denoted` has been moved *out* of the hash-consed
`OperationInfo` fact into a Rust-side side-table keyed by op symbol:
`op_bodies` (WI-251/305), `op_effects` (WI-342 E2), and — if we keep going —
`op_param_types` / `op_return`. The reason is the **carrier rule meeting fact
storage**: a `Value::Node` cannot be a child of a hash-consed `Term` (the `Term`
enum's children are all `TermId`; an occurrence has non-structural identity and
can't be hash-consed), so a denoted-bearing field can't live in the fact and
must live elsewhere.

The question this doc answers: **does the KB need to support "value facts" —
facts whose terms may contain `Value::Node` — and what would that take?**

### Worked example: effects as `Vec<TermId>`

The concrete shape of the wall. The `OperationInfo` fact stores an operation's
effects as `effects: List[Type]` — a cons-list whose elements are `TermId`s:

```
OperationInfo(name: Cell.set, …, effects: cons(<TermId>, cons(<TermId>, nil)))
```

- A **ground** label like `Error` is `sort_ref(Error)` — a hash-consed `TermId`,
  fits the list fine.
- A **denoted-bearing** label like `Modify[c]` is
  `parameterized(Modify, [denoted(value: Ref(c))])`. The `denoted` carries an
  occurrence (`Rc<NodeOccurrence>`, identity- and span-bearing) — i.e. a
  `Value::Node`, which **cannot be a `TermId`**, so it cannot be an element of a
  `Vec<TermId>` / `List[Type]` cons-list, so it **cannot live in the fact**.

That is *exactly* why WI-342 E2 moved effects off the fact into
`kb.op_effects: HashMap<Symbol, Vec<Value>>`. The `Vec<TermId>` couldn't hold a
`Modify[c]`, so the data had to leave the hash-consed fact for a Rust-side
`Vec<Value>`. Every subsequent side-table (`op_param_types`, …) is the same
wall hit again: a `Value::Node` in a position whose fact storage is `TermId`.

If the fact layer were carrier-agnostic (value facts), `effects` could stay a
single carrier-agnostic list in the fact — `Modify[c]` as a `Value::Node`
element — and `op_effects` (and its siblings) would not need to exist.

## Two layers, by (mostly) design

There are two unification substrates, deliberately distinct:

| Layer | Carrier | Machinery |
|-------|---------|-----------|
| **Search / logic** (facts, rule heads, queries) | hash-consed `TermId` | discrimination tree (`SubstTree`), resolver matching, `Substitution` |
| **Types / metadata** (the typer) | carrier-agnostic `Value` over `TermView` | `unify_types` / `types_compatible` (WI-342) |

The principle (CLAUDE.md "Representation note"): **hash-consing is for ground,
searched structure** — O(1) structural equality, structural indexing, sharing —
and is **inappropriate for binders / occurrences**, whose identity is
context-dependent (an `Rc`/span, not structural). So denoted/occurrence content
is *not* a fact; it is value-carried metadata stored alongside.

The honest nuance: "facts are `TermId`" is **partly principled** (a Node can't be
hash-consed) and **partly just unmigrated** (the resolver/discrimination/
substitution substrate was built `TermId`-first, before the `Value`/occurrence
carrier existed, and never got its WI-342). A *value fact* is therefore possible
— its **ground** subterms still hash-cons; its **Node** subterms simply opt out
of hash-consing (which they can't participate in regardless).

## Where `OperationInfo`'s `TermId` form is actually needed

Tracing every consumer of the hash-consed `OperationInfo` fact:

- **`lookup_operation_info`** (the *only* Rust reader; typer + eval funnel through
  it) walks `by_functor(OperationInfo)` to **find the fact for an op symbol** —
  a *keyed lookup*, which a `HashMap<Symbol, _>` does directly. It uses no
  unification and no discrimination tree.
- **Persistence** does not serialize `OperationInfo` facts.
- **No live SLD rule** queries `OperationInfo`. The only anthill-side references
  are the `entity OperationInfo(...)` schema, a `operations(...) -> List[OperationInfo]`
  reflect op that is *declared but unimplemented*, and a *commented-out*
  `:- OperationInfo(name: ?n)` example.

Today only `lookup_operation_info` reads it, and the reflect API is unimplemented
— so it is tempting to conclude "make `OperationInfo` a Rust-side record and drop
the fact." **That is the trap.** The reflect API is *intended* to work (it's in
`reflect.anthill`); it is unimplemented *partly because of this very gap* — a
denoted-bearing `OperationInfo` can't be a queryable fact yet. A Rust-side record
would make `OperationInfo` **permanently un-queryable**, foreclosing the
reflection API. And "no live SLD query today" is **self-fulfilling**: every
denoted-bearing datum gets absorbed by a workaround (side-table / record) before
it ever forces the proper substrate, so the consumer never "appears."

**Conclusion: `OperationInfo` must be SLD-queryable AND it carries `denoted`, so
it must be a value fact.** The Rust-side record is the wrong target — it trades
the side-table smell for a loss of queryability. The right target is the value
fact below: one carrier-agnostic `OperationInfo` fact that is queryable *and*
holds `Modify[c]` as a `Value::Node` field, with `op_effects`/`op_bodies`
collapsing back **into the fact**, not into a record.

## Scope of the resolver migration

Surprising headline: **the resolver is already ~80% carrier-agnostic**, because
WI-246 (rule-body occurrences) + the `Substitution` Value-work + the
`TermView`-based query/match already did most of it.

### Already done (free)

- **`Substitution`** is `HashMap<VarId, Value>` with `bind_value` / `resolve_as_value`;
  the resolver already binds Value (lineage path). 0 work.
- **Resolver matching** — `query_view` / `match_view` are already generic over
  `TermView`; rule heads stay `TermId`, the *goal* drives the walk and may be a
  `Value`. 0 work.
- **Goal stream** — `Frame.goals: Vec<Value>`; goal-walking handles `Value::Term`
  (`apply_subst`) and `Value::Node` (`substitute_occurrence`).
- **Rule bodies** — already occurrence-carried (WI-246), pushed as `Value::Node`
  goals, no materialize-to-`TermId`.
- **Discrimination-tree *lookup*** (`query_node`) — already `TermView`-driven.
- **Builtins** — 24 of 29 already `TermView`-migrated through one choke point
  (`execute_builtin` → `walk_arg` → `reify_goal_value`).

So **value *goals* already flow end-to-end.** Missing = value *facts* (a
Node-carrying, indexed, queryable head).

### Remaining work — phased

- **Phase A — discrimination-tree INSERT/REMOVE → `TermView`** (the main piece;
  lookup is already `TermView`-driven). `insert_ground` / `insert_pattern` /
  `remove_walk` still walk `TermStore`/`TermId` (~500 lines of structural
  recursion); rewrite to drive off `head`/`pos_arg`/`named_arg`, carrying a
  `ViewItem` (not a `TermId`) as the "recurse into this child" pointer in
  `arg_seq`.
  **The tree uses NO hash-consing** — its keys (`DiscrimKey`) are purely
  structural (`Functor(Symbol)` / `Arity` / `NamedKey` / `Positional` /
  `Lit(Literal-value)` / `Ident` / `Ref(Symbol)` / `Bottom`); nodes hold
  `concrete: HashMap<DiscrimKey,_>`, `var_edges` keyed on `VarId`, `leaves:
  Vec<RuleId>`. No `TermId` is ever a key, stored in a node, or compared. So
  there is **no hash-cons semantics to preserve** — a `Value::Node` decomposes
  into the *same* structural keys via `TermView` (`head` → `Functor`+`Arity`; a
  `denoted` → `Functor("denoted")` whose `Ref(c)` value → `Ref(c)`; `Const` →
  `Lit`; children via `pos_arg`/`named_arg`), so a Node is **structurally
  indexed like a term**. (Indexing a Node as a wildcard/var-edge is a *sound but
  conservative fallback*, not required.) **Difficulty: MEDIUM — mechanical
  decomposition on a perf-sensitive path; the risk is the volume/correctness of
  the walk rewrite, NOT untangling a hash-cons dependency (there is none).**
- **Phase B — value-fact storage.** Add an `assert_fact_value` path; make
  `RuleEntry.head` carrier-agnostic. `by_functor` is free (`TermView::head`);
  `by_sort` / `by_domain` need a small decision on how a value fact's sort/domain
  keys; `fact_dedup` (keyed on `(TermId,TermId,TermId)`) **skips Node-headed
  facts** — a dedup-*miss*, not a correctness bug. **Difficulty: MEDIUM.**
- **Phase C — De Bruijn opening for value *rule heads*** (only if *rules*, not
  just ground *facts*, carry value heads). Bodies already handled
  (`open_debruijn_node` / `substitute_occurrence`); the gap is synthetic-binding
  extraction (`iter_terms()` filters `Value::Term`) needing a `Value::Node` arm.
  Moot for ground value facts. **Difficulty: LOW–MEDIUM.**
- **Phase D — the 5 remaining builtins** (`QualifiedName`, `ShortName`,
  `LookupSymbol`, `ResolveSortInstParam`, `FieldAccess`) → `TermView`. Op-body/
  eval-only today; needed only if a *rule body* reaches them. **Difficulty: LOW.**
- **Phase E — boundary reify points** (dedup keys, residual-goal extraction, NAF
  groundness, `Solution.residual: Vec<TermId>`). They `reify_goal_value` to
  `TermId` today — functionally fine (a Node reifies losslessly there); extend to
  `Value` only to keep Node identity through an *answer*. **Difficulty: MEDIUM;
  optional.**

### Risks / decisions

- Phase A is volume on a perf-sensitive path (the discrimination-tree walk
  rewrite), but it carries **no hidden hash-cons dependency** — the tree keys
  purely on decomposed structure (`DiscrimKey`), never on `TermId` identity, so a
  Node decomposes into the same keys via `TermView`. The risk is getting the walk
  rewrite right, not preserving hash-cons semantics.
- The genuine *semantic* decisions are in **Phase B, not the tree**:
  `fact_dedup` (keyed on `(TermId,TermId,TermId)`) and `by_sort`/`by_domain` —
  "what does dedup / sort-keying mean for a non-hash-consable head?" The answer
  for `fact_dedup` is skip-for-Node (dedup-miss, not unsound); `by_sort`/`by_domain`
  need a small key decision.

## Why the Rust-side record is the wrong fix

A tempting "cheap win" is to make `OperationInfo` a carrier-agnostic **Rust-side
record** read via `TermView`, collapsing the side-tables. It is the wrong move:

- it is **not SLD-queryable** — it abandons the reflection API requirement;
- it is **itself the workaround pattern** that keeps value facts unmotivated —
  solving every denoted case over the Rust side (records / side-tables /
  re-grounding) is exactly what guarantees the proper fact layer "never has a
  consumer." The side-table proliferation isn't an argument *for* another
  Rust-side store; it's the accumulating debt that argues *for* finishing the
  fact layer.

The value fact subsumes both goals at once: queryable **and** Node-carrying, with
the side-tables collapsing back into the fact.

## References

- `docs/design/entity-representation-term-or-value.md` — the carrier rule.
- `docs/design/occurrence-as-value-type.md` — occurrences as a value carrier.
- WI-342 — the typer carrier migration (delivered: P3/P4, effects loader flip,
  dispatch consolidation, ty-slot/arrow, collection builders, entity_field_types).
- WI-246 — rule-body atoms as occurrences (the resolver-side foundation).
- Source: `kb/discrim.rs` (SubstTree), `kb/resolve.rs` (SLD loop + builtins),
  `kb/subst.rs` (Substitution), `kb/mod.rs` (`assert_fact`, indexes,
  `with_fresh_vars`), `kb/term_view.rs` (`TermView`).
