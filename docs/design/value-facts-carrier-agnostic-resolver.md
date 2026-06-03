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

## Phase B — implementation plan (decided)

Phase A (the discrimination-tree INSERT/REMOVE → `TermView` rewrite) is delivered,
with loud guards on the un-keyable head/arg cases (functor-less / opaque heads
`panic` until value-head keying lands). This section records the Phase B decisions,
taken against the live code.

### Why the head's type must change — and to what

The head must stop being a `TermId` for the **same reason effects left the fact**:
a hash-consed `TermId` cannot hold a `Value::Node`. An occurrence carries identity
and a span, so it can't be hash-consed, can't be a `Term`'s child, and can't be an
element of a `Vec<TermId>` collection (the effects cons-list). Any position that
must carry a `denoted` Node — the effects list yesterday, the fact head now — has
to move from a TermId-only collection to a carrier that admits Nodes.

That carrier already exists: **`Value`**. `Value` is *the* carrier-agnostic union
— it has both a `Value::Term(TermId)` arm and a `Value::Node(Rc<NodeOccurrence>)`
arm (WI-109 / WI-342). So the head simply becomes:

```rust
struct RuleEntry { head: Value, /* … */ }   // common case: Value::Term(tid)
```

A bespoke `enum HeadCarrier { Term(TermId), Value(Value) }` was considered and
**rejected as redundant**: `HeadCarrier::Term(t)` is exactly `Value::Term(t)` and
`HeadCarrier::Value(v)` is exactly `v` — it re-encodes a distinction `Value`
already makes, and would be a second classification to keep in sync with the
carrier the resolver / typer / substitution layer already speak (`Substitution`
is `HashMap<VarId, Value>`; goals are `Vec<Value>`). `Value` admits non-head
shapes (`Int`, `Closure`, …) that a head never takes, but those simply never occur
as a head and `head_view()` handles any carrier uniformly — the looseness costs
nothing and matches existing goal / subst usage.

Blast radius: every reader of `head` updates from `TermId` to `Value` (or to
`head.head_view()` / a `head_term() -> Option<TermId>` accessor) —
incref/release, `by_functor`, `fact_dedup`, the `query_view` resolve closure,
`with_fresh_vars` (rules only — facts are never opened), the `rule_head` getter,
persistence / `print`, codegen, and cross-crate readers. The common `Value::Term`
case threads through unchanged behaviourally.

### Indexing

- **`by_functor`** — free: `head.head_view().head(kb)` yields the functor for both
  carriers (a `Value::Node` reads its functor through the Phase-A `TermView`).
- **`by_sort` / `by_domain`** — *no change.* They key on the fact's `sort` /
  `domain` arguments, always ground `TermId`s supplied to `assert_*`,
  independent of the head carrier. (The doc's earlier "small decision" resolves to
  *nothing to decide* — they stay TermId-keyed.)
- **`fact_dedup`** (`HashMap<(TermId,TermId,TermId), RuleId>`) — **skip when the
  head is not `Value::Term`.** A Node-bearing head has no `TermId` key; this is a
  dedup-*miss* (the same value fact asserted twice stores twice), not unsound.
  Ground facts keep their O(1) dedup. Document at the skip site.

### Discrimination tree

INSERT/REMOVE are already `TermView`-driven (Phase A); assert/retract call them
through `head.head_view()`. A `Value::Node` head decomposes into the same
`DiscrimKey`s as its term twin. No further tree work.

### Resolution — the load-bearing finding (named-arg order)

`query_view` finds candidate rules in the tree, then `resolve_leaf` walks the
**fact head** along the discrim-recorded `VarPath`s (`Positional(i)` /
`Named(sym)`) to extract variable bindings. The head passed to resolution **must
be the same carrier the tree indexed**, because **named-argument order differs by
carrier**:

- an occurrence's `named_keys` (`occ_named_keys` / `type_node_keys` /
  `effect_expr_keys`) returns a **fixed slice order** — e.g. an arrow node yields
  `[param, result, effects]`;
- a hash-consed `Term::Fn` stores `named_args` **sorted by field name** (the
  canonical-ordering invariant).

So resolving a value head's paths against a *reified `TermId` skeleton* of that
head would read the **wrong child** at named positions. A reified-skeleton
shortcut is therefore **unsound** for binding extraction — and it is why the
"keep `head: TermId` + a shadow `Value`" representation was a non-starter.

**Decision: resolution is carrier-faithful** — `resolve_leaf` walks
`head.head_view()` and returns `Value` subterms, which also preserves `Node`
identity in the answer substitution (folding in the part of Phase E that matters
for value facts). Implementation: thread a `TermView` (not a bare `TermId`)
through `SubstTree::query_resolved`'s resolve closure and the `resolve_leaf` impls
(`SmallSubst` / `SharedSubst`, `persist_subst.rs`), or add a carrier-aware sibling
selected when the matched candidate's head is not `Value::Term`.

### Refcounting

- `Value::Term(t)` head — incref/release `t`, unchanged.
- Node-bearing head — incref/release the **ground `TermId` leaves** reachable in
  the `Value` (`Value::Term` subterms) to keep them alive; the `Value::Node`
  (`Rc`) subterms are owned by the `Value` and need no `TermStore` refcount. Add a
  `Value`-walking incref/release helper.

### Retract

Mirror assert: discrim REMOVE via `head.head_view()`; `by_functor` via its
functor; `fact_dedup` skip for non-`Value::Term`; release the ground subterms.

### Staging and test

Land the substrate end-to-end: `head: Value`, `assert_fact_value`, indexing,
discrim insert/remove, carrier-faithful resolve, retract. Test by asserting a
Node-carrying value fact (a minimal `f(denoted(value: Ref(c)))` or an
`OperationInfo`-shaped head) and querying it back with **both** a ground query and
a `f(?x)` variable query, asserting the bound `?x` is the `Node` (identity
preserved through the answer). The `op_effects` / `op_bodies` → fact collapse —
building `OperationInfo` itself as a value fact — is the **payoff that follows**
once this substrate exists; it is not part of the Phase B substrate landing.

## Delivered — `op_effects` → fact collapse (the payoff)

Done. The `op_effects` side-table is **gone**; an operation's effect labels now
ride in the `OperationInfo` fact itself. The loader assembles the
`OperationInfo` named args once (single source of field set/order); when every
effect label is a ground `Value::Term` the head stays a hash-consed `Term::Fn`
(dedup-able, the universal case), and when any label is a `Value::Node` (a
`denoted` like `Modify[c]`) the effects ride as a value cons-list and the head is
a `Value::Entity` value fact via `assert_fact_value`. `lookup_operation_info`
reads the labels back from either carrier (carrier-faithful — a `Modify[c]`
label is returned as the same `Value::Node`, identity intact), so the typer/eval
see an identical `Vec<Value>` to what the side-table returned.

Every reader of the `OperationInfo` fact was made carrier-agnostic: the shared
`op_info` helpers (`head_name_ref` / `head_field_term` / `effects_of_head`, the
last three now `pub` for out-of-crate use), `typing::lookup_operation_field`,
`load::find_operation_in_scope`, the reflect `KB.operations` builtin
(anthill-stl) and the `kb_facts_of` builtin, and cpp-gen's `operations_in_sort` /
namespace classification (which now route through `lookup_operation_info`). The
dead `KbBridge` (TermId-only, can't hold a Node effect) skips value-fact heads.

**Remaining (unchanged by this phase):** `op_bodies` still rides in its own
side-table, reached via the `operation_body` builtin (WI-305) rather than a fact
field — a separate collapse. And the optional substrate phases C (De Bruijn for
value *rule* heads), D (5 remaining builtins → `TermView`), and E (boundary
reify) still lack a driving consumer.

## Delivered — consumer test + the `is_equation` carrier gap

The payoff above shipped with synthetic Phase-B substrate tests (a
`f(denoted(value: Ref(c)))` head, exercised via `kb.query`). The first
**end-to-end consumer** test — a real op with `effects Modify[c]`, whose
`OperationInfo` the loader therefore builds as a value fact, queried back via the
full SLD entry `kb.resolve` and read via `lookup_operation_info` — surfaced a
latent gap the synthetic tests could not: **`is_equation` read its head through
the term-only `head_term_id`** (which `panic!`s on a `Value::Entity`/`Value::Node`
head). The resolver calls `is_equation` on **every** matched candidate at its
unconditional eq/non-eq triage (`resolve.rs`, the `rc.retain(|rid| !is_equation)`
line), so `kb.resolve` on *any* goal whose discrimination bucket contains a value
fact (`OperationInfo`, an entity `FieldInfo`, a value-in-type fact) panicked.
`kb.query` bypasses that triage, which is why the substrate tests stayed green.

Fix: `is_equation` reads functor + positional arity via `TermView`
(behaviour-identical for the universal `Value::Term(Fn)` head; a value fact —
never `eq`-headed — returns `false` as it always should). The sibling term-only
readers `with_fresh_vars` and `unindex_functor` also use `head_term_id` but are
**not** reached by value *facts*: `with_fresh_vars` runs only on rules with a body
(value rule heads are deferred Phase C), and retract of a value fact already
routes around `unindex_functor` (the Phase-B retract mirror). The lesson: a
carrier-agnostic *storage* layer is not enough — every reader the *resolver* funnel
touches per candidate must be carrier-agnostic too, and only a `resolve`-path
consumer test (not a `query`-path substrate test) exercises that funnel.

## References

- `docs/design/entity-representation-term-or-value.md` — the carrier rule.
- `docs/design/occurrence-as-value-type.md` — occurrences as a value carrier.
- WI-342 — the typer carrier migration (delivered: P3/P4, effects loader flip,
  dispatch consolidation, ty-slot/arrow, collection builders, entity_field_types).
- WI-246 — rule-body atoms as occurrences (the resolver-side foundation).
- Source: `kb/discrim.rs` (SubstTree), `kb/resolve.rs` (SLD loop + builtins),
  `kb/subst.rs` (Substitution), `kb/mod.rs` (`assert_fact`, indexes,
  `with_fresh_vars`), `kb/term_view.rs` (`TermView`).
