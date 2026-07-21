# Extent Sources — the EDB/IDB Split (design vision)

> **Future / not-yet-scheduled design.** This is the *full* vision for virtualizing where a functor's facts live (resident / external table / oracle). It is deliberately larger than any committed spec — and a large unimplemented design is a liability, so nothing here is a build-as-written commitment. Each capability is specified **in its own small proposal when it is implemented**. The implementable slices extracted so far: **proposal 057 (extent read seam)** — being built; the **extent write seam** (WI-780) — forthcoming, written as its own proposal when built (not pre-numbered). The mechanism designs below that no slice yet covers (volatile sources + observation memo, the caching matrix, constraint delta-checking, the oracle archetype) are **direction, not spec** — cite them for intent, re-derive them against the code when their slice is written.

## Status: Draft (2026-07-19) — design settled in the WI-780 design sessions; two decisions pinned there: single-owner extents with loud refusal of source-file facts for store-owned functors, and the per-query observation memo for volatile sources. Revised 2026-07-20: the Store API is now fully defined as ONE Rust seam every module is a client of (§"The Store API"), and the `RuleId`-carrying APIs get an explicit staged retirement path (§"RuleId retirement").

## Tracks: WI-780 (the umbrella this doc is the design half of; its implementation core narrows back to store addressing + the retract seam, §"Writes" / §"The Store API"), with the decomposition in §"Decomposition". WI-665 (cache coherence deferred from 053) lands inside this design; WI-177 (epochs) is pre-existing substrate this design consumes — §"Caching" states the exact relation.

## Relates to: 007 (persistence — §2 capability/policy, §11 route rule; the 1-to-1 functor→store routing this doc promotes from *policy* authority to *extent* ownership), 026.1 Q4 Stage B (the `RouteHandler` registry, `kb/route.rs` — the read-seam prototype this trait subsumes), 036 (domain store sorts), 037 (state model — `Modify` is tracked-heap mutation; extent writes ride the same discipline), 045 (effect rows), 047 (effects as monads — the observation memo is its Filinski move applied to facts), 052 (`Relation[T]` — its access-effect row `E` is where extent effects surface), 053 (fact mutability — the monotonicity ladder *is* this doc's writability axis; "the owning store is the single authority" *is* this doc's declaration surface), 054 (`External` — the license-revocation table governs volatile sources; per-call freshness lives there, not here), WI-773 (values-first read accessor — shaped by §"Read path"), WI-774 (resolve-vs-refuse read policy — orthogonal, cited), WI-779 (interim write-side guard — subsumed by §"Writes"), WI-696 (carrier-neutral `Value` goals), WI-300 (resolve-or-suspend guard tier — the delay behavior unmet lookup modes reuse).

## Problem

Four strands, all forced by the same missing concept — *where a functor's facts live is
an architectural property of the functor*, and today the KB has no vocabulary for it:

1. **Identity.** Three identities coexist for a stored fact: the domain key
   (`IndexedFileStore.by_id`), the content (hash-consed ground head `TermId`), and the
   event (`RuleId` — an ephemeral in-process index). The identity crossing the anthill
   boundary is the ephemeral one: `FactId = Handle(HandleKind::Fact, RuleId.raw)`,
   meaningless across processes. The composed retract flow maps content→`RuleId`
   (`find_fact` bucket scan) and then `RuleId`→content again (canonical head print) —
   the durable identity was the content all along. And the store/KB ordering is a
   comment-enforced temporal protocol (`Store::retract` *before* `kb.retract`, or the
   store reads released `TermId`s).

2. **Scale.** Every fact is fully resident: a `kb.rules` Vec slot, a hash-consed head,
   and entries in `rules_by_functor`/`by_sort`/`by_domain`/discrim. Retract only
   tombstones — slots are never reclaimed — and load parses and interns the full extent
   before the first query. A custom backend with ~10⁶ rows cannot work this way: a
   million-row table must answer queries without materializing a million `RuleEntry`s.

3. **Computed extents.** There is no way to back a functor by computation — an oracle
   that answers `Sqrt(x: 2.0, y: ?)` by computing, or by consulting something genuinely
   nondeterministic (entropy, a network service). Builtins are the only computed
   relations, and they are a closed Rust-side vocabulary with no capability story: no
   way to say "this source needs `x` ground", "this source cannot be enumerated",
   "this source's answers vary between calls".

4. **Homeless semantics.** NAF and constraints over a changing external extent need a
   snapshot/closed-world discipline nobody has stated. 053 explicitly deferred cache
   coherence (WI-665). Volatile answers must be banned from equational contexts (054's
   license table) but nothing enforces it.

## Model: one extent source per functor

A functor's **extent** — its set of ground facts — is provided by exactly one **extent
source**. This is the deductive-database EDB/IDB split:

- **IDB (intensional)** — bodied rules, and with them everything derivation-shaped —
  stays resident and `RuleId`-addressed. Rules are program text; they are never
  virtualized.
- **EDB (extensional)** — ground facts — belongs, per functor, to one owning source:
  the **resident source** (the default: today's `kb.rules` + discrim path, where
  program facts, reflection, and realization tables live), an **external table** (a
  store answering by lookup — SQL, an indexed file, a service), or an **oracle** (a
  computation producing answers on demand).

Retrieval stays **one seam**. The discrim tree remains the universal candidate-lookup
structure — but it holds a node *per entry* for resident content only, never a node
per external row. A store-owned functor is **mounted** at its functor position:
retrieval reaching the mount delegates to the owning source with the goal pattern
pushed down, and the source implements the very contract the missing subtree would
have — *yield the candidates that could structurally match*. Lookup returns tagged
candidates: `Resident(RuleId)`, opened exactly as today, or ground `Row(Value)`,
entering σ via `bind_value` with no `TermStore` allocation (as `RouteHandler` rows
already do). No consumer of lookup ever branches on ownership — the WI-770 lesson
(per-consumer hand-rolled policy diverges) applied to retrieval. And the mount
enforces single ownership *structurally*: the functor position is occupied, so there
is no subtree to insert a resident entry into. (Since ownership is per-functor and
the head functor is the tree's first discrimination step, a mount and a
functor-keyed pre-check are behaviorally identical; the mount is the architectural
statement — routing lives inside the one retrieval structure, not in its callers.)

**This is not a second term mechanism beside the `TermStore`.** Semantically there is
one mechanism, already unified: `TermView` reads both carriers through one interface,
equality is the single comparator (WI-486 removed the carrier-blind one), and the
discrim tree keys on purely structural `DiscrimKey`s — never on `TermId` identity — so
an uninterned row indexes and matches identically to an interned term. What forks is
only **storage policy, chosen by lifetime**. Hash-consing is a policy for persistent,
heavily-shared, repeatedly-compared structure — O(1) equality, subterm dedup, stable
ids as index keys (`fact_dedup`, `by_sort`, `by_domain`) — and it is exactly wrong for
a transient read-once row: interning a streamed row mutates the global store on a
*read* path, grows it by entries dedup can never help (rows are pairwise distinct),
and demands the release discipline whose write-side hazard §"Writes" kills. "Load
parses and interns the full extent before the first query" is the residence bug of
§"Problem" restated in `TermStore` terms. So this design does not add a mechanism —
it *shrinks the `TermStore`'s jurisdiction to the profile where it wins*, the resident
IDB+EDB core, and bulk extents leave it entirely; they never needed it even for
identity, since the boundary identity is content or domain key (§"Writes"), not
`TermId`. Ownership is what makes the fork principled: resident owner → interned;
external owner → streamed.

### Single owner — no union extents (decided)

Ownership is **exclusive**. Today's `route.rs` behavior — handler consulted *in
addition to* the discrim lookup — is a transition artifact to remove. The motivating
divergence: a source file carries `fact WorkItem(id: "WI-001", status: open(), …)`
while the shared store's row for `WI-001` says `status: done()` (a teammate delivered
it). Union semantics yields two well-formed answers — the item is open for claiming
logic and done for reporting — with no single write that repairs it, and retract
desyncs exactly as WI-779 describes: the store updates, the resident twin persists,
the next load resurrects the stale status. This is not even a detectable
contradiction, just two facts divergently describing one domain entity.

So: **a source-file `fact` for a functor owned by an external source is a loud
`LoadError`** ("`WorkItem` is owned by store X — seed it through the store's own
channel"). No silent skip, no silent import. The refusal covers a bodied `rule` whose
**head** is the owned functor for the same reason — classical EDB discipline: an
extensional predicate never appears in a rule head. Derivation layered over an
external extent names a *view* functor instead (the `Config` shape below), which also
keeps the layering honestly IDB under the WI-773/774 read policies. An
explicitly-named seed/migration path
(loader hands seed facts *to the store*, idempotent by domain key, collision = loud
error) may be added later as a deliberate command, never as default load behavior.

Union, where genuinely wanted, is already expressible *in the language* as a rule over
two single-owner extents — which also makes it honestly IDB, subject to the
WI-773/774 bodied-rule read policies, with the override order visible:

```anthill
rule Config(key: ?k, value: ?v) :- StoredConfig(key: ?k, value: ?v)
rule Config(key: ?k, value: ?v) :- DefaultConfig(key: ?k, value: ?v),
                                    not StoredConfig(key: ?k, value: ?)
```

The override lives in the **negation**, for a reason about *modes*, not style.
A cut form *can* express "stored else default" — but only as a single-rule
if-then-else, `(StoredConfig(?k, ?v), !) ; DefaultConfig(?k, ?v)`, where the
disjunction's branches are tried in source order (`push_choice` is a deterministic,
ordered choice point), so the cut genuinely commits left-over-right. Every cut
form is nonetheless a **red cut**: with `?k` unbound it commits to the *first*
stored row and drops the rest, staying correct only when `?k` is ground on call.
`not StoredConfig(key: ?k, value: ?)` is steadfast in *every* mode, all-free
enumeration included — which is exactly what a `Config` view over two extents
must be, lookup mode being a first-class axis here (§"The capability profile").
Two traps sink the naive cut alternatives and are worth stating: two sibling
`rule Config` clauses are tried in **nondeterministic** discrim order
(`query_view` — HashMap, imposing only *facts before bodied rules*, `kb/mod.rs`),
so a cross-clause `StoredConfig(...), !` has no defined "first"; and folding it
into one body as `StoredConfig(...), !, DefaultConfig(...)` is a **conjunction** —
it demands the pair in *both* tables (cut prunes choice points, it does not skip
the following goal), yielding nothing precisely when stored should override
default.

Tests that want a few in-memory rows without standing up a store get **owner
swapping**, not union: ownership is bound at registration (like
`register_route_handler`/`register_store` today), so a test that registers no store
gets the resident default owner.

## The capability profile

Every source declares a profile; engine features are *gated* on it, refusing loudly
when a feature needs a capability the source lacks. The axes, with the three source
archetypes:

| axis | resident | table (10⁶ rows) | oracle |
|---|---|---|---|
| **lookup modes** — which args must be ground to answer | none required | any (indexes help) | per mode, e.g. `x` ground |
| **enumerable** — can stream the full extent | yes | yes (lazy cursor) | typically **no** |
| **complete** — closed world: the enumeration is the whole truth | yes | yes, per snapshot | typically **no** |
| **stability** — re-ask within an epoch agrees | stable | stable | stable *or* **volatile** |
| **writability** — 053's ladder | `monotone`/`non_monotone` | any | usually `constant` |

Derived gating:

- A goal not meeting any supported lookup mode **delays** (the WI-300
  resolve-or-suspend discipline — another goal may bind the needed args); floundering
  at the end is a loud error, never a silent failure.
- Enumeration (all-free pattern), `forall`, and NAF that requires enumerating the
  extent need *enumerable + complete*. Ground NAF is just a membership check — fine
  against any source.
- Writes follow 053 unchanged: the ladder is the writability axis; `constant` **is**
  the read-only fact. Nothing new to invent.
- Equational contexts (simp, the prover) run outside any observation, so they consult
  **resident extents only**; *reaching* an externally-owned functor there is a loud
  "extent not available in this context" error — not an empty extent, which would
  let NAF prove falsehoods silently.

**Declaration surface** follows 053 exactly: the owning source is the single
authority, answering through its trait (Rust-side), surfaced as reflect predicates.
`fact_monotonicity(functor)` gains siblings — `fact_stability(functor)`,
`fact_completeness(functor)`, lookup modes — materialized at registration the same way
`Store::owned_monotonicity` is today (the `owned()` registration authority of
§"The Store API"). No static binding fields in `.anthill`, for 053's reason:
capability is source logic, not schema.

## Read path

**Values, not addresses.** A lookup answers with rows/solutions — never `RuleId`.
Resolve answers questions; walks address facts. This is the contract WI-773's
accessor is shaped by: the public read surface neither returns nor requires `RuleId`,
because for a store-backed functor there is none to return. The loud bodied-rule
channel reports offending rules by rendered text (`TermPrinter::print_rule`), not id.

**Lazy cursors and pushdown.** The seam is invoked through the discrim mount
(§"Model") via `ExtentSource::lookup` — one call of the trait family that
§"The Store API" defines in full.

The resolver consumes one tagged candidate stream for every goal — `Resident` and
`Row` alike — replacing today's route-beside-discrim double consultation. The
current eager drain at `step_init` (memory ∝ matching rows) is replaced by lazy
per-pump advancement — with 10⁶ rows, eager conversion of every match into a
candidate substitution is not an optimization gap but a correctness-of-scale bug.
Canonical named-arg ordering pays off here: the ground fields of the goal become
the `LookupQuery.bound` equalities (§"The lookup contract"), no translation layer.

**Effect surfacing.** Consulting an external extent is an `External`-classified act in
054's sense — the answer depends on state that changes with no tracked `Modify`.
Proposal 052 reserved the slot: the access-effect row `E` of `Relation[T]` /
`LogicalStream`. A query over external extents surfaces `External` (or a refinement)
in that row; resident-only queries stay pure. The per-query snapshot (§next) is
precisely what keeps the *inside* of one query coherent even though the *act* of
querying is external.

## Volatile sources: the observation memo

The floor for participating in the fact space is **query-stability** — and a volatile
source is *made* query-stable by mandatory memoization:

> Within one resolution, the first observation of a volatile source asserts its
> answers into the query's world; the world only grows for the rest of that query.

A volatile source is thereby **monotone-within-query**: the caching matrix (§next)
applies at two scales — monotonicity × epoch across queries, observation-monotonicity
within one. This is 047's Filinski reflection applied to facts: nondeterminism is
confined at the observation boundary. Consequences, each load-bearing:

- **Both polarities freeze.** A ground NAF check `not Oracle(a, b)` memoizes its
  verdict. Otherwise NAF succeeds early, a later positive consult draws `(a, b)`
  fresh, and one query proved `¬p` and `p` in the same world.
- **Later asks filter the frozen set; the same key is never re-consulted.** The memo
  is keyed by the `LookupQuery.bound` of the source's single mode (§"The lookup
  contract"). If `Oracle(x: a, y: ?)` froze the answer set for `x = a`, a later
  `Oracle(x: a, y: b)` filters that set — re-consulting with the tighter pattern
  could draw a different world.
- **One consultable mode per volatile source (v1).** Keys from two modes (`x→y` and
  `y→x`) cannot be cheaply reconciled into one consistent world; declaring a second
  mode on a volatile source is a loud registration error. Stable sources may declare
  many — for them the memo is tabling, an optimization, not semantics.
- **Scope = the top-level resolution session**, shared by nested sub-resolutions
  (guard-tier checks, dispatch sub-proofs see the parent's world). Two `execute`
  calls are two observations — two worlds. The memo lives in resolver session state,
  never in the KB.

What this deliberately excludes: **per-call freshness is not a fact shape.** A
functor that should re-draw on every occurrence (`random()`) is not a relation over
any world; anthill already has the honest form for it — an operation carrying 054's
`External` effect. The volatility classification here governs only *cross-query*
behavior: never cached across queries, never used equationally.

## Caching: monotonicity × stability over epochs

The cross-query caching story is a *derived matrix*, not a mechanism per functor:

| monotonicity | stability | positive answers cacheable | negative answers cacheable |
|---|---|---|---|
| `constant` | stable | forever | forever |
| `monotone` | stable | indefinitely | per-epoch (a new fact can appear) |
| `non_monotone` | stable | per-epoch | per-epoch |
| any | volatile | per-query memo only | per-query memo only |

The **epoch** is the shared primitive: a local, monotonic per-functor counter
(`functor_epoch(sym)`, plus the global `kb.epoch`), with the contract *a cached
value is valid iff every counter it was stamped with is unchanged*. WI-177
introduces the registry with its first bump source — resident assert/retract — and
its first consumer, the proof cache. This design adds a **second bump source, not a
second registry**: a store-owned functor's counter bumps at the write seam's own
writes and at sync when the store reports change (the store-native token — an etag,
an LSN — is translated into a local bump at the seam and never leaks upward).
Single ownership (§"Model") makes the partition clean: every functor has exactly
one bump source.

The proof cache is not a sibling mechanism but this pattern's first *instance*: the
prover is a **dependent oracle** — a computed extent that is a deterministic
function of the KB, with no state of its own — and the proof sidecar is its
persistent cache. The one distinction to keep straight is the *direction* of the
validity token: an **independent** source (a shared table, a volatile oracle)
invalidates when its **own** state moves, reported through the seam; a **dependent**
oracle invalidates when its **inputs'** epochs move — for the prover, exactly the
resident functors the proof visited, and only those, since equational contexts
refuse external extents (§"The capability profile"), so a proof can never silently
depend on the DB. (Should open decision 2 ever admit pinned-epoch equational reads,
proof validity extends to those functors' epochs with no change in form.) Same
registry, same stamp-and-compare, opposite dependency direction.

The remaining consumer is WI-665 — 053's deferred coherence for *resident* caches
(the WI-646 simp-gate family, hot resident memos) — reading the same resident slice
as the proof cache, at the per-functor grain 053 and WI-646 already chose; a
hot-row cache over a 10⁶-row table reads the external slice, its validity exactly
`functor_epoch` equality. The matrix gives each consumer its policy; the epoch
gives it its trigger. This section is WI-665's home.

## Writes: store-native identity and the single seam

The write-side redesign — WI-780's original core — restated on this model:

- **Identity.** The boundary assert/retract is keyed by **store-native identity**:
  the domain key (primary key — `IndexedFileStore.by_id`) or the content (canonical
  ground head). `RuleId` is demoted to the *address of a resident entry*: under
  virtualization a store-backed row *has* no `RuleId`, so any API that hands one
  across the boundary is untenable, not merely inelegant. Which APIs those are —
  including the declared-API changes in `store.anthill`/`reflect.anthill`
  (`persist`'s `-> FactId` return, `NonMonotonicStore.retract`'s `id: FactId`
  parameter, `find_fact`, `KB.assert`) — and how each is retired, stage by stage,
  is pinned in §"RuleId retirement".
- **One seam.** A single `retract_persistent` (and its assert twin) owns the
  store+KB ordering internally — the comment-enforced "store reads TermIds before
  kb.retract releases them" protocol stops being caller-visible. The 053
  monotonicity guard moves *into* this seam: one choke point for resident and
  external owners alike.
- **Update — identity-preserving replace.** The third write op, and in practice
  the dominant one: every stage0 status transition (claim / deliver / verify /
  update) is a same-key replace, today spelled `find_fact` → `retract` →
  `replace_named_arg` → `persist`. Decomposed like that it breaks store-native
  identity continuity (a GitHub-backed store would close issue #N and open a
  fresh one — fatal to WI-437's issue-number allocation), exposes a transient
  absence to readers and to §"Constraints" delta checking, and runs the 053
  guard twice. So the write boundary gains
  `NonMonotonicStore.update(store, old: Term, new: Term) -> Option[T = Term]` —
  `some(canonical new row)` on success, `none()` when no row matches `old`
  (nothing written; the caller decides how loud to be). Same functor required;
  the row's **store-native identity must survive**: a backend whose native key
  disagrees between `old` and `new` answers a loud error, never a silent
  retract+persist — that *is* a retract + persist, say what you mean. The gate
  is retract's own rung, `non_monotone` (an update is compositionally a
  retraction); the default backend implementation is exactly the buffered
  retract+persist pair — the correct semantics for pure content-identity rows —
  overridden where a native form exists (SQL `UPDATE`, a GitHub issue edit, an
  in-place file-span replace). Named `update`, not `modify`, so 037's `Modify`
  effect name stays unshadowed.
- **Fact-shape refusal.** The seam addresses EDB rows only. A bodied rule whose
  ground head is content-identical to the retract target is a loud refusal (hash-
  consing makes fact `H` and `rule H :- B` share the head `TermId`; blanket refusal
  is the safe polarity per WI-772). WI-779 is the interim guard this subsumes. The
  semantic kicker stays documented: retract removes an *extent row*; if a same-head
  bodied rule still derives `H`, the statement remains provable — extent-level
  removal is not truth-level removal, and the seam's contract says so.
- **Write overlay.** Buffered writes not yet flushed must be visible to reads: a
  store-backed owner answers `backend ∪ pending asserts − pending retracts`.
  Read-your-writes survives virtualization; today it holds only by the accident of
  full residence.

## The Store API — one seam, fully defined

The declared contract stays `anthill.persistence`
(`stdlib/anthill/persistence/store.anthill`, proposal 007 §2): `Store { persist,
flush, monotonicity }`, the provision traits `NonMonotonicStore { retract }` /
`QueryableStore { retrieve }` / `BulkStore { pull }`, and `route(fact: Term) ->
Store` — that is the face programs and host bridges see, and it survives this
design with exactly two amendments (the write/identity boundary of §"Writes" —
store-native keys plus the added `update` — and the capability policy ops of
§"The capability profile"). What has never been pinned
is the **engine half**. On the Rust side the contract is realized today as four
partial, drifting surfaces: `persistence::Store` (whose eager `retrieve ->
Vec<TermId>` betrays the declared streaming), `RouteHandler` (`kb/route.rs`, a
second read path beside discrim), `IndexedStore` (`RuleId`-keyed locations), and
per-builtin glue in `eval/builtins.rs` (handle minting, the comment-enforced
store-before-kb ordering) — and they do not even share a *home*: the read
registry is a KB field, the store registry an `Interpreter` field, so "who owns
a functor's facts" is answerable in two places that cannot see each other. This
section replaces all four with **one trait
family, fully defined, that is the only road to a backend**: the builtins
realizing `anthill.persistence`, the resolver, the loader, the reflect facade,
the epoch registry, and every consumer module (CLI, `anthill-todo`, the
generators) are clients of this seam — and a backend participates by
implementing exactly this family, nothing else. No client reaches around it to
`kb.rules`/discrim for an externally-owned extent; no backend is consulted
except through it.

Measured against the declared contract, the family is mostly **conformance, not
invention**:

- `QueryableStore.retrieve` is *already declared* `-> Stream[Term, Error]`, streamed
  by its own stated rationale ("so a queryable backend can yield 1M rows without
  forcing them all into memory at once"), rows entering σ as `Value::Entity` with no
  `TermStore` allocation (the declaration cites 026.1 Q4 + 007 §11). The Rust
  realization — `Store::retrieve -> Vec<TermId>`, eager and interning — **betrays
  its own declared spec**. `ExtentSource::lookup` is that realization brought into
  conformance, plus the mode surface; `RouteHandler` retires into it. Not a new
  read API — the declared one, finally honored.
- `route` is *already the ownership declaration*; the mount is `route` finally
  consulted at resolution — the wiring 007 §11 promised and `kb/route.rs`'s header
  defers. v1 pins route to factor **per functor** (single owner, §"Model");
  content-based routing (sharding) stays expressible *inside* a composite source,
  never as two owners of one functor.
- The capability additions follow the file's own header split — **provision** =
  trait, **policy** = per-functor value: stability, completeness, and lookup modes
  join `monotonicity` as policy operations, surfaced through the reflect facade like
  `fact_monotonicity` (053's authority model, per decision Q3); enumerability rides
  the existing provision split.

The genuine anthill-API changes are then exactly three — the **`FactId`
boundary** (§"RuleId retirement", stage R3), the **added `update`** on
`NonMonotonicStore` (§"Writes"), and the **load-refusal semantics** of
§"Model"; `flush`, `monotonicity`, `pull` are untouched.

### The backend half

```rust
/// Capability profile of one owned functor (§"The capability profile"),
/// read once at registration and materialized KB-side — the reflect
/// facade and the resolver's gating answer from the materialized copy,
/// never by re-asking the backend.
pub struct ExtentProfile {
    /// Alternative input patterns `lookup` answers; each names the
    /// argument slots (`ArgKey`) that must be ground. One mode with
    /// nothing required means any pattern, enumeration included. A goal
    /// meeting no mode delays (WI-300); floundering at the end of
    /// resolution is loud.
    pub lookup_modes: Vec<LookupMode>,
    /// Can stream the full extent (the all-free `lookup`).
    pub enumerable: bool,
    /// Closed world: the enumeration is the whole truth, per snapshot.
    pub complete: bool,
    /// Stable (re-ask within an epoch agrees) or Volatile (§"Volatile
    /// sources"). Registration refuses a volatile source declaring more
    /// than one lookup mode.
    pub stability: Stability,
    /// 053's ladder. `None` = not intrinsic to this backend: the
    /// functor's policy comes from project reflect rules — exactly
    /// today's `owned_monotonicity` returning `[]` for the filesystem
    /// backends.
    pub writability: Option<Monotonicity>,
}

/// DECLARATION side (in `ExtentProfile`): one input pattern the store can
/// answer, naming the argument slots that must be ground for it — the
/// source's indexes/keys. `required_ground` empty = the all-free mode
/// (enumeration). This is the store's *pattern description*, read at
/// registration; the engine gates goals on it (§"The lookup contract").
pub struct LookupMode { pub required_ground: Vec<ArgKey> }

/// An argument slot of a fact: a named field or a positional index
/// (anthill facts carry both). Canonical named-arg ordering keeps the
/// named form stable across writers.
pub enum ArgKey { Named(Symbol), Pos(u32) }

/// CALL side (passed to `lookup`): the digested selection for one call.
/// The engine has already matched the goal to a declared `mode` and pulled
/// out `bound`, so a backend reads a typed query — never a raw goal Value.
/// This is what replaces the bare `pattern: &Value`.
pub struct LookupQuery {
    /// Which declared mode (index into `profile.lookup_modes`) this call
    /// satisfies — its `required_ground` slots are guaranteed present in
    /// `bound`; the store may switch access path on it.
    pub mode: usize,
    /// The pushed-down selection: every *fully-ground* argument slot of
    /// the goal, as a `slot = value` equality (a partially-instantiated
    /// compound arg is treated as unbound and left out). Ground equality
    /// is the entire v1 pushdown vocabulary (§"The lookup contract").
    pub bound: Vec<(ArgKey, Value)>,
}

pub enum Stability { Stable, Volatile }

pub enum ExtentError {
    /// Write half consulted on a backend whose profile refuses it — the
    /// loud backstop; plan-time gating reads the profile first (053:
    /// query the policy, never attempt-and-catch).
    NotWritable,
    /// `lookup` reached with a goal meeting no declared mode — a gating
    /// bug, since the resolver delays such goals (WI-300) before ever
    /// building a `LookupQuery`.
    NoSupportedMode,
    /// `pull` on a backend that does not serve the mirror role.
    NotBulk,
    /// Backend-native failure (I/O, SQL, service), rendered.
    Backend(String),
}

/// THE backend seam. One owner per functor, mounted at its discrim
/// functor node (§"Model") — or registered as a durability mirror for
/// resident functors. Subsumes `persistence::Store`, `RouteHandler`, and
/// `IndexedStore`. No method of this family speaks `RuleId` or `TermId`:
/// rows cross as carrier-neutral ground `Value`s in both directions.
pub trait ExtentSource {
    /// Registration authority: the functors this source serves, each
    /// with its profile. Subsumes `Store::owned_monotonicity` and keeps
    /// its key convention: the `String` is the FULLY-QUALIFIED functor
    /// name ("anthill.todo.WorkItem") — a backend exists independently
    /// of any KB, so it cannot speak `Symbol`. Registration resolves
    /// each name once (unresolvable name = loud registration error);
    /// every engine-side structure (mount, profile map) is
    /// `Symbol`-keyed from there on.
    fn owned(&self) -> Vec<(String, ExtentProfile)>;

    // ── read half (owner role) — retires `RouteHandler::retrieve` and
    //    `Store::retrieve` ──
    /// The discrimination contract for the mounted subtree: a lazy cursor
    /// over the ground rows matching `query`. `query` is a digested
    /// `LookupQuery` — the engine already walked the goal — whose `bound`
    /// equalities map straight onto a WHERE clause / index probe. The
    /// cursor must cover a **superset** of the rows satisfying `bound`;
    /// the engine re-checks each row against the full goal, so over-return
    /// is sound and only under-return is a bug (§"The lookup contract").
    fn lookup(&self, kb: &KnowledgeBase, query: &LookupQuery)
        -> Result<Box<dyn ExtentCursor>, ExtentError>;

    // ── write half (both roles; capability-gated — the profile is the
    //    plan-time authority, these defaults the loud backstop) ──
    /// Buffer one new row. Identity is content: the canonical ground
    /// row. (The `sort`/`domain` companions today's `Store::persist`
    /// threads are per-functor constants — trigger sort from the head
    /// functor, domain from the owning namespace — so a filing backend
    /// derives them from the row's functor; they are not per-call
    /// arguments.)
    fn persist(&mut self, kb: &KnowledgeBase, row: &Value,
               meta: Option<&Value>) -> Result<(), ExtentError> {
        Err(ExtentError::NotWritable)
    }
    /// Buffer removal of the row with this content; the backend maps
    /// content to its native key (`IndexedFileStore`: the `id` field →
    /// `by_id` → file span). Returns whether the row was present.
    fn retract(&mut self, kb: &KnowledgeBase, row: &Value)
        -> Result<bool, ExtentError> {
        Err(ExtentError::NotWritable)
    }
    /// Identity-preserving replace (§"Writes"): remove `old`, install
    /// `new`, as ONE buffered write. Same functor; the store-native key
    /// must agree between `old` and `new` — a differing key is a loud
    /// `ExtentError`, never a silent retract+persist. Returns whether
    /// `old` was present (`false` ⇒ nothing written). The default is
    /// the buffered retract+persist composition — correct for pure
    /// content-identity rows; backends with a native form override
    /// (SQL UPDATE, issue edit, in-place span replace).
    fn update(&mut self, kb: &KnowledgeBase, old: &Value, new: &Value,
              meta: Option<&Value>) -> Result<bool, ExtentError> {
        if self.retract(kb, old)? {
            self.persist(kb, new, meta)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
    /// Flush buffered writes to the backend.
    fn flush(&mut self, kb: &KnowledgeBase) -> Result<(), ExtentError> {
        Ok(())
    }

    // ── bulk (mirror role) — today's `BulkStore::pull` ──
    /// Rehydrate everything this source persisted, for load-time replay
    /// into the resident extent. Owner-role sources are never pulled —
    /// nothing rehydrates a mounted extent.
    fn pull(&self) -> Result<Vec<ParsedFile>, ExtentError> {
        Err(ExtentError::NotBulk)
    }

    // ── sync (owner role) — the second epoch bump source (§"Caching") ──
    /// Ask the backend whether its state moved since last asked (etag /
    /// LSN compare — store-native tokens never leak upward). `true`
    /// bumps the functor epoch of every owned functor. v1 cadence: the
    /// explicit refresh command only; the seam's own writes bump
    /// directly (open decision 3).
    fn refresh(&mut self) -> Result<bool, ExtentError> { Ok(false) }
}

/// Lazy row cursor. Rows are ground and carrier-neutral, entering σ via
/// `bind_value` with no `TermStore` allocation. Errors are per-row so a
/// fallible backend streams then fails loudly — never truncates silently.
pub trait ExtentCursor {
    fn next(&mut self, kb: &KnowledgeBase)
        -> Option<Result<Value, ExtentError>>;
}
```

### The lookup contract

The raw `pattern: &Value` was the API's soft spot: what a pattern *is* differs
per backend and was nowhere pinned, so every store would re-walk a goal `Value`
its own way and the resolver/store could silently disagree on what got pushed
down. Three statements close it — a store's *pattern description* is its declared
modes, the call payload is a *digested* `LookupQuery`, and the *soundness rule*
is fixed once for all backends:

- **Capability is declared, not inferred (the pattern description in the
  store).** What a source *can* answer is its `lookup_modes` (over `ArgKey`),
  read at registration. The engine owns goal→mode matching, once: it picks a
  satisfied mode, or delays the goal (WI-300), or flounders loud — a backend
  never re-derives groundness from a `Value`. `LookupQuery.mode` names which mode
  this call took, so the store switches access path on an integer.
- **Pushdown vocabulary (v1): ground equality only.** `LookupQuery.bound` is a
  conjunction of `slot = ground_value` and nothing else — no ranges, no
  operators, no partially-instantiated compound args. This is deliberately the
  front edge of the out-of-scope join planner: canonical arg order maps `bound`
  straight onto a WHERE clause / index probe, and a richer predicate vocabulary
  later *extends the `LookupQuery` struct* rather than re-parsing a blob — the
  reason a typed query beats a raw `Value` even before it is richer.
- **Soundness, stated once.** `lookup` must yield a cursor over a **superset** of
  the rows satisfying every `bound` equality; it MAY filter on whatever subset of
  `bound` it can index and leave the rest, because the engine unifies each
  returned row against the *full* goal (`match_view_value_pattern`, as route rows
  already are) and drops non-matches. So over-return is always sound; the single
  bug is dropping a row that satisfies `bound`. A store that ignores `bound`
  entirely and streams its extent is correct, just slow — the floor, never a
  footgun. (This is why `bound` carries *all* ground args, not just the mode's
  required ones: maximal pushdown information, and the store uses what it can.)

The conformance suite (decomposition item 0) tests exactly this boundary against
a mock: a backend that under-returns fails; one that over-returns passes because
the engine filters; a declared mode answers and an undeclared pattern delays. So
the contract is executable, not just prose.

### The engine half

**Home: the KB, not the evaluator.** Today the two halves of this seam live in
different types — `routes: RouteRegistry` is a `KnowledgeBase` field
(`kb.register_route_handler`), while `store_registry` and `store_monotonicity`
are `Interpreter` fields (`interp.register_store`). That split is itself part of
the four-drifting-surfaces problem, and unifying them forces a single home. It
is the **KB**: the mount lives *in the discrim tree*, which the KB owns and the
resolver reaches with no evaluator in scope, and the write seam's entire job is
owning the backend↔KB ordering, which means mutating KB bookkeeping. Nothing in
the seam needs the evaluator — the 053 guard (`resolve_fact_monotonicity`) only
reads the KB plus the materialized policy map, so it moves KB-side with them.

`Interpreter` is emphatically *not* the home: it is proposal 026's **expression
evaluator** — op bodies, effect handlers, builtin dispatch — and extent
ownership is a fact-space concern, not an expression-evaluation one. Its
residual role here is the thin builtin adapters (argument shaping, `Error`-effect
delivery); **no method of this seam hangs off it**, and `register_store` /
`store_monotonicity` leave it entirely.

The KB-side aggregate is `ExtentRegistry` — the field `kb.extents`, successor to
`RouteRegistry` — holding the mount table (`Symbol → SourceId`), the registered
sources, the materialized per-functor `ExtentProfile`s (subsuming
`store_monotonicity`), and the write overlay. Sources live in a slab keyed by
`SourceId` so the seam can borrow one mutably while still mutating the rest of
the KB; the seam methods are inherent on `KnowledgeBase` for that reason, not
free functions over a `&mut kb` the registry also lives inside.

The two *roles* compose by registration, not by trait — one backend, two
registrable roles, never two contracts for one requirement. Today's file stores
are the first configuration and remain exactly as legitimate; the 10⁶-row table
and the oracle are the second.

```rust
impl KnowledgeBase {
    /// Owner role: mount `source` at each `owned()` functor's discrim
    /// node (subsumes `register_route_handler`). Loud
    /// registration errors: functor already owned (by another source or
    /// by resident entries), volatile source with more than one lookup
    /// mode. From then on a source-file `fact` or same-head bodied
    /// `rule` for the functor is a `LoadError` (§"Model").
    pub fn register_extent_owner(&mut self, key: String,
                                 source: Box<dyn ExtentSource>);

    /// Mirror role: write-through durability for RESIDENT functors —
    /// `pull` rehydrates at load, the seam shadows resident writes into
    /// `persist`/`update`/`retract`/`flush`; `lookup` is never consulted
    /// (the resident subtree answers). Today's `Interpreter::register_store`
    /// becomes this, moving KB-side with the registry.
    pub fn register_mirror(&mut self, key: String,
                           source: Box<dyn ExtentSource>);

    /// THE write seam (WI-780 proper) — the only caller of a backend's
    /// write half and the only mutator of resident EDB bookkeeping. Owns
    /// internally, in order: 053 monotonicity guard → fact-shape refusal
    /// (bodied same-head rule → loud, §"Writes") → owner write
    /// (buffered) or resident write + mirror shadow → write-overlay
    /// bookkeeping → functor-epoch bump. Returns the canonical row —
    /// the identity any later retract keys by; a duplicate assert
    /// answers the existing row. Errors are seam-typed (`ExtentError` /
    /// a KB write error); the *builtin adapter* renders them into the
    /// `Error` effect, so the seam stays evaluator-free.
    pub fn assert_persistent(&mut self, row: Value, meta: Option<Value>)
        -> Result<Value, ExtentError>;

    /// The update twin (§"Writes"): one guard pass, one overlay entry
    /// (the net change — readers and delta constraints never see the
    /// transient absence of a retract+persist decomposition), one epoch
    /// bump. Same-functor is checked at the seam; key stability is
    /// enforced by the backend, which knows its key. Returns
    /// `Some(canonical new row)`, or `None` when no row matched `old`
    /// (nothing written — the caller decides how loud to be).
    pub fn update_persistent(&mut self, old: &Value, new: Value,
                             meta: Option<Value>)
        -> Result<Option<Value>, ExtentError>;

    /// The retract twin. The store-before-kb ordering that today is a
    /// comment protocol (`persistence/mod.rs`, `eval/builtins.rs`) lives
    /// inside — never caller-visible again. Returns whether a row was
    /// present.
    pub fn retract_persistent(&mut self, row: &Value)
        -> Result<bool, ExtentError>;
}
```

(`key` stays the canonical store-value string of today's `register_store` — it
is what the anthill-level `store` argument of `persist`/`update`/`retract`/`flush`
resolves to. Under single ownership the functor already binds the source, so
the argument validates rather than selects, as `Store.monotonicity` already
treats it. Computing it from a `Value` — `store_canonical_key` — is pure
value-shaping and stays evaluator-side with the adapters.)

### The resident source and the in-memory reference

Two things "store" could mean here are deliberately distinct — and pinning both
is what makes the interface *complete* rather than partial (§"Phasing"):

- **The resident source** — the default owner of every functor no external
  source claims: today's `kb.rules` + discrim path, holding program facts,
  reflection, and realization tables. It is described by a *profile* (the
  §"capability profile" `resident` column — no required modes, enumerable,
  complete, stable, writability per 053) and by its role as default, but it is
  **not a `dyn ExtentSource` in v1**: the discrim tree already *is* its lookup
  structure — that is 057's core claim, the mount is the exception — and routing
  resident reads through a trait object + cursor would reintroduce exactly the
  per-row overhead the design removes. The accessor unifies the *read* over
  resident and mounted uniformly; the branch (discrim vs `lookup`) is internal to
  it, invisible to callers.
- **The in-memory reference source** — a real, shipped `ExtentSource`: an
  enumerable + complete + stable table held in memory (`InMemoryExtentSource`).
  This is item 0's mock table **promoted from test double to a first-class
  shipped source**, because a *ready* interface needs one real owner exercising
  every method — this is it: the reference a SQL/git backend is written against,
  and a batteries-included mountable extent for embedders and tests alike.
  Registering it as a functor's owner is how a test, or a small real project,
  gets a virtualized extent without standing up an external engine — the
  owner-swap of §"Model", now a shipped source rather than a fixture. It is the
  proof the seam is whole: if nothing but a resident special-case implemented the
  trait, "complete interface" would be a claim no code backs.

### Clients — who calls what

| client | reaches extents through | never again |
|---|---|---|
| resolver | the mount → `lookup` cursor, tagged candidates (§"Read path") | `route_handler_for` beside discrim; eager drains |
| `anthill.persistence` builtins (`persist` / `update` / `retract` / `flush` / `monotonicity` / `retrieve` / `pull`) | `assert_persistent` / `update_persistent` / `retract_persistent` / seam flush; materialized profiles | handle minting; the caller-visible store-then-kb dance; `find_fact` scans |
| WI-773 read accessor — and through it CLI, `anthill-todo`, the generators | one values-first read over resident *and* mounted extents | raw `rules_by_functor` + `rule_head` walks (the ~20 WI-773 sites) |
| loader | ownership check at define time → loud refusal; (later) the explicit seed command → the seam | silent import of facts for owned functors |
| reflect facade (`fact_monotonicity` + §capability siblings) | profiles materialized at registration | per-query backend asks |
| epochs / caches (WI-177, WI-665, hot-row caches) | seam write bumps + `refresh` | store-native validity tokens above the seam |

The builtins realizing `anthill.persistence` shrink to thin adapters — argument
shaping (`store_canonical_key`) and `Error`-effect delivery. Everything they
hand-sequence today (the 053 guard, the store-before-kb ordering, handle
minting, `index_by_id` calls) is the seam's job, written once. That is the whole
of the expression evaluator's involvement: proposal 026's `Interpreter`
evaluates expressions, and after this change holds no extent state and no seam
method.

## RuleId retirement — the deprecation path

After this design, `RuleId` means exactly one thing: **the address of a resident
entry — program text**. It never denotes a fact across any boundary: resolve
answers with values (§"Read path"), the write boundary keys by store-native
identity (§"Writes"), and a store-backed row *has* no `RuleId` to denote.
"Deprecating the `RuleId` APIs" therefore decomposes per API: readers move to
the values-first accessor, writers move to content keys, and what remains — the
rule-*browse* surface — keeps `RuleId` legitimately.

**Mechanics.** Pre-stabilization kernel policy: no versioned shims, no
`#[deprecated]` grace windows. Each stage below is one atomic in-tree cutover —
the API changes and every consumer (stdlib, the bundled stage0 assets under
`rustland/anthill-todo/anthill/`, `examples/github-todo`, tests) migrate in the
same change, kept green via `scripts/test.sh`. The declared-API edits to
`store.anthill`/`reflect.anthill` are carried by this proposal's stages; after a
stage lands, a straggler fails loudly — unresolved name at load, type error at
compile — and never silently binds to a compatibility path.

Throughout the table, `Term` in a declared signature is `anthill.reflect.Term` —
the language-level term sort `store.anthill` already imports (today's `persist`
*takes* `fact: Term`; R3 makes it *return* one). Its realization at the Rust seam
is the carrier-neutral `Value` row (`ExtentSource::persist`/`retract(row:
&Value)`) — the host bridge already equates reflect `Term` with a `Value` payload
(WI-535) — so no `TermId`, and a fortiori no `RuleId`, is implied anywhere.

| surface | today | target | stage |
|---|---|---|---|
| the ~20 raw-walk fact readers (`rules_by_functor` + `rule_head*` as answers — the WI-773 list) | hold `RuleId`s | the WI-773 values-first accessor | R1 |
| `RouteHandler` (`kb/route.rs`); Rust `Store::retrieve -> Vec<TermId>` | two read seams beside discrim | retire into `ExtentSource::lookup` | R2 |
| `anthill.persistence.Store.persist -> FactId` | mints `Handle(Fact, RuleId.raw)` | `-> Term`: the canonical persisted row — the retract key | R3 |
| `anthill.persistence.NonMonotonicStore.retract(id: FactId)` | handle → `RuleId` → two-phase store+kb retract | `retract(store, fact: Term) -> Bool`, content-keyed, through `retract_persistent` | R3 |
| `anthill.reflect.find_fact(t) -> Option[FactId]` | content→`RuleId` bucket scan minting a handle for retract | **deleted** — its one job was minting retract keys, and the row a caller already holds *is* the key (a status transition = one `update(store, old, new)`, §"Writes") | R3 |
| `anthill.reflect.FactId` (`sort FactId = ?`) and `KB.assert -> Option[FactId]` | opaque handle | sort deleted; `assert -> Option[Term]`: `some(canonical row)`, `none()` still = constraint rejection (WI-546) | R3 |
| `Literal::Handle` / `HandleKind` (`kb/term.rs`) | `Fact` is the *only* kind | the whole literal variant goes with `FactId` | R3 |
| generated-bridge type map `FactId = kb::RuleId` (`anthill-stl/build.rs`) | equates the boundary id with the in-process index | entry deleted; the bridge regenerates without it | R3 |
| Rust `Store::retract(kb, RuleId)`; `IndexedStore::location_of(RuleId)`; `IndexedFileStore.by_id: String → RuleId` | `RuleId` inside store internals | `ExtentSource::retract(kb, row)`; backends map domain key → location directly (`by_id: String → Location`); `IndexedStore` dissolves into backend internals | R3 |
| `Interpreter::register_store` + fields `store_registry` / `store_monotonicity` | extent state on the 026 expression evaluator | `KnowledgeBase::register_mirror` / `register_extent_owner` over `kb.extents`; profiles subsume `store_monotonicity` | R2 |
| `KnowledgeBase::register_route_handler` / `route_handler_for` + `RouteRegistry` | KB-side read registry, the *other* half of the same question | `ExtentRegistry` (`kb.extents`) — one home for ownership | R2 |
| `KnowledgeBase::retract(RuleId)` | public; callers must order store-first | `pub(crate)` — called by the seam only | R4 |
| head-as-answer enumeration (`rules_by_functor`/`_iter` + `rule_head`/`rule_head_value` used as answers) | public | `pub(crate)` or deliberately browse-named (WI-773's ratchet) — the WI-770 class becomes unrepresentable outside kb | R4 |
| rule-browse surface: `rule_ids_by_qn` (prove lift), CLI `--match`, smt-gen `collect_rule`, `is_fact` / `is_rule_alive` | public | **stays public** — `RuleId`'s legitimate jurisdiction: addressing resident rules as program text | — |

The stages, in dependency order:

- **R1 — readers off the raw walk** (= WI-773). After R1, no fact *reader*
  outside kb traffics in `RuleId`. Independent of this design's landing;
  already filed.
- **R2 — one read seam, one home** (decomposition item 1). `RouteHandler` and
  `Store::retrieve` are deleted into `lookup` — pure deletion, both are
  in-tree-only surfaces with no declared twin — and the two registries merge
  into `kb.extents`, moving the store half off `Interpreter` (§"The engine
  half").
- **R3 — the write-boundary cutover** (decomposition item 5). The one
  declared-API break, taken atomically: the `store.anthill`/`reflect.anthill`
  signature changes, `FactId`/`find_fact`/`Handle` deletion, builtins rewritten
  over the seam, and every in-tree `.anthill` consumer migrated in the same
  change. The flows simplify: today's retract dance — resolve → head →
  `find_fact` → handle → `retract(handle)` — becomes resolve → head →
  `retract(store, head)`; today's status-transition dance — `find_fact` →
  `retract(handle)` → `replace_named_arg` → `persist` — becomes resolve →
  `update(store, old, new)` (`replace_named_arg` survives: it builds `new`).
- **R4 — the visibility ratchet** (tail of item 5; sequences after R1, since a
  type external crates traffic in cannot be privatized). With R1 and R3 landed
  the compiler enumerates any straggler; what survives is the rule-browse
  surface above.

End-state invariant, checkable at review time: **`RuleId` appears in no
signature of `ExtentSource`, the write seam, the read accessor, or any
`.anthill`-declared operation.** It addresses resident program text — exactly
the IDB of §"Model" — and nothing else. (The resolver-internal
`Resident(RuleId)` candidate tag is inside kb, not a boundary, and is untouched
by this invariant.)

## Constraints over external extents (direction, deferred)

Constraint checking needs *enumerable + complete + snapshot* — and over a 10⁶-row
extent, re-running the constraint join is unaffordable anyway. The direction is
**delta checking at the write seam**: a new (or retracted) row triggers only the
constraint instances it touches, with the goal's ground fields pushed down as usual;
`monotone` functors narrow it further (only new rows can newly violate). An
`update` (§"Writes") presents as one net change — the transient absence its
retract+persist decomposition would show is never checked. Until that
lands, a `constraint` mentioning an externally-owned functor is a loud unsupported
error — not a silently unchecked invariant.

## Out of scope

- **Join planning.** A rule joining two large external extents wants selectivity
  hints and join ordering; v1 keeps SLD's textual goal order and per-goal pushdown.
- **Builtins as sources.** The seam admits absorbing the builtin table (a builtin is
  an oracle with modes) — deliberately not attempted now.
- **`orElse` / `coalesce` surface sugar for merged views.** A union view is
  written here as an explicit rule pair (the `Config` example). Nicer surface —
  `StoredConfig(?k,?v) orElse DefaultConfig(?k,?v)` — is already expressible for a
  *keyed* lookup as the derived if-then-else `(StoredConfig(?k,?v), !) ;
  DefaultConfig(?k,?v)`, but a *steadfast per-key* merge cannot be a bare binary
  combinator: `A orElse B` cannot tell the key `?k` from the value `?v` (both are
  shared), and per-key fallback needs the key named — which is exactly what
  `not StoredConfig(key: ?k, value: ?)` encodes by keeping `?k` and anonymizing
  the value. The explicit NAF rule is correct and mode-honest but **not
  ergonomic** — the negated restatement of the stored lookup is boilerplate a
  merged view repeats, and shrinking it is the point of the sugar. A keyed
  `coalesce(?k; A; B)`, or a mode-aware `orElse` that treats the ground-on-call
  variables as the key (keyed-steadfast when called ground, coarse under
  enumeration — a mode-dependence to surface loudly), is stdlib sugar over the
  existing cut + NAF, no resolver primitive. **Deferred, not dismissed**; it
  rides along when 057's items are filed. Until it lands, 057 keeps the explicit
  rule so the mode behavior stays visible.
- **Multi-writer coherence beyond epochs.** A store's snapshot discipline is its own
  (transactions, ETags); the KB trusts the reported epoch. Cross-process epoch
  persistence stays out (WI-177 scoped it out; `state_hash` covers cross-process).

## Phasing — a complete interface, not a partial one

The seam is adopted **whole or not at all**. A caller migrated onto the read
accessor reads the *final* contract — values-first, resident **and** mounted, the
full §"lookup contract" — never a resident-only stub whose semantics shift under
it when mounts land later. *Ready when used* is the rule. The way v1 stays small
is therefore **not** a partial interface but **bounded capability behind a
complete one**, every unsupported case a **loud refusal** — the trait's refusing
write defaults, the profile's feature gating, the loud registration errors — so a
caller can never fall into a silent gap. The split is capability breadth, not
interface surface:

- **v1 — the complete interface + one real owner.** Items 0 and 1 in full:
  `ExtentSource` with *every* method, discrim mounts, `LookupQuery` + the lookup
  contract, the values-first accessor over resident **and** mounted, and one
  shipped reference source — the in-memory table (§"The resident source and the
  in-memory reference"), which is what makes "complete interface" a fact rather
  than a claim. Plus the write-seam identity redesign for resident owners and the
  `RuleId` retirement (item 5's R1–R4 core). This is the architectural
  restructure — done first, per "risky/foundational work first", not last.
- **Deferred — loud-refused capability, consumer still hypothetical.** Each is a
  refusal the *complete* interface already expresses, not a missing method:
  - the **volatile** archetype + observation memo (item 4) — declaring
    `Stability::Volatile` is a loud registration error until it lands; heavy
    semantics (both-polarity freeze, session scope) with no consumer yet;
  - the **oracle** archetype (computed extents) — defers with volatile; the first
    real external source is a table, not a computation;
  - the **cache matrix + epochs** (item 3) — correctness holds by re-query, this
    is pure perf (WI-177 is itself an optimization item);
  - **writes through an external owner** — the seam's external
    `persist`/`update`/`retract` refuse `NotWritable`; resident writes and the
    identity redesign still land, because they fix real hazards (WI-779/780) and
    shape the accessor's API;
  - **constraint delta-checking** (item 6) — a `constraint` over an
    externally-owned functor is a loud unsupported error until it lands.

Nothing above is interface-partial: the methods, the profile axes, and the error
variants all exist in v1; what a deferred item adds is a supported *value* of a
capability the interface already refuses loudly.

## Decomposition

Work items, in dependency order (numbers assigned at filing). **Testing is a
prerequisite, not a trailing step** — and a structural one here, because today
*every* fact is resident, so there is no non-resident `ExtentSource` in the tree
to exercise any of this against. Item 0 builds that substrate first (its mock
table is the shipped `InMemoryExtentSource` of §"The resident source and the
in-memory reference", not a throwaway); every later item lands with its own
conformance tests over it (the WI acceptance pattern `ToolPasses(cargo-test)`,
run through `scripts/test.sh`), and an item is not done until they are green.
This ordering also honors "risky/foundational work first": the seam and its test
doubles are the architectural core, not the last mile.

0. **Test substrate (prerequisite)** — the reference `ExtentSource`
   implementations and the conformance suite the rest is tested through, since
   nothing else can virtualize an extent yet:
   - **Reference + mock backends** — the shipped `InMemoryExtentSource`
     (enumerable + complete + stable, declaring lookup modes and a `by_id`-style
     key so the write overlay and content↔key mapping are exercised without a
     filesystem or SQL engine) is the v1 real owner *and* the table fixture
     (§"The resident source and the in-memory reference"), not a throwaway. The
     deferred-archetype doubles ride with their items, refused until then: a
     `MockOracle` (per-mode, non-enumerable, `constant`) and a `MockVolatile`
     (single-mode, volatile) land with items 3/4, so v1's `InMemoryExtentSource`
     is the sole archetype exercised end-to-end.
   - **Conformance suite** — profile-driven property tests any `ExtentSource`
     must pass: a declared lookup mode answers and an undeclared pattern
     *delays then flounders loud* (not silently empty); the §"lookup contract"
     soundness boundary — a backend that **under-returns** (drops a row
     satisfying `bound`) fails, one that **over-returns** passes because the
     engine re-filters; enumeration/`forall`/NAF refuse loudly on a
     non-enumerable source; the observation memo freezes both polarities within a
     query and re-asks never re-consult a frozen key; the write overlay shows
     read-your-writes and `update` shows no transient absence; an equational
     context reaching an external functor errors. These are written against the
     *trait*, so a real SQL/git backend later inherits them.
   - **Owner-swap harness** — the registration seam a test uses to bind a mock
     as a functor's owner (§"Model": tests get owner swapping, not union), the
     fixture every later item's tests stand on.

1. **`ExtentSource` trait + discrim mounts** — the trait family of §"The Store
   API" lands (`ExtentProfile`, `LookupMode`/`ArgKey`/`LookupQuery`,
   `ExtentCursor`, the two registration roles over the KB-owned `ExtentRegistry`)
   with its read half live (retirement stage R2): `RouteHandler` *and*
   `Store::retrieve` retire into `lookup`; the engine's goal→mode match builds
   the `LookupQuery` and enforces the §"lookup contract" (superset semantics,
   engine re-filter); store-owned functors mounted at their discrim functor node;
   one tagged-candidate retrieval path (`Resident(RuleId)` | `Row(Value)`)
   replacing route-beside-discrim; lazy cursor replacing the eager drain; loader
   refusal of source-file facts *and same-head bodied rules* for owned functors
   (the single-owner decision). The write half's methods exist from day one but
   stay wired through today's builtin path until item 5.
2. **Capability surface** — policy operations beside `monotonicity` in
   `store.anthill` (stability, completeness, lookup modes); `ExtentProfile`; gating
   in the resolver (mode delay, enumeration/completeness checks, equational-context
   refusal); reflect facade siblings of `fact_monotonicity`.
3. **Cache matrix over epochs** — WI-177 stays its own item (the registry +
   resident bump source, proof cache as first consumer); this item adds the
   seam/sync bump source for store-owned functors and the matrix-driven consumers
   (closes WI-665).
4. **Observation memo** — session-scoped world for volatile sources, both-polarity
   freezing, single-mode registration check.
5. **Write seam (WI-780 proper)** — the `assert_persistent` /
   `update_persistent` / `retract_persistent` triad (§"The Store API", engine
   half), store-native identity at the boundary, the added `update` on
   `NonMonotonicStore`, 053-guard relocation, WI-779 subsumption, write
   overlay; carries retirement
   stage R3 (the atomic declared-API cutover: `persist`'s return, `retract`'s
   key, `KB.assert`, `find_fact`/`FactId`/`Handle` deletion) and then R4 (the
   visibility ratchet, which sequences after WI-773's reader migration = R1).
   Inventory and mechanics in §"RuleId retirement".
6. **Constraint delta-checking** — separate design + implementation; until then the
   loud unsupported error from §"Constraints".

WI-773's accessor should be shaped against §"Read path" (values-first) from the
start; WI-774's resolve-vs-refuse policy is orthogonal and composes.

## Open decisions

1. **Reflect naming** for the capability siblings (`fact_stability` /
   `fact_completeness` / mode surface) — bikeshed at implementation time; the
   authority model is settled.
2. **Pinned-epoch equational access** — whether simp/prover may consult a
   `constant`+stable external extent under a frozen epoch. v1: no; revisit if a real
   proof needs a materialized view.
3. **Epoch reporting cadence** for external stores — push (store bumps at flush/sync)
   vs pull (refresh command). v1: bump at the seam's own writes + explicit refresh;
   nothing speculative.
