# 057: Extent Seam

## Status: Draft (2026-07-23). The implementable slice of the [extent-sources vision](future/extent-sources.md), extracted under its "complete interface, not a partial one" rule. **One seam, both directions:** a functor's extent — its ground facts — is owned by one source, read *and* written through it. It is one `ExtentSource` trait, one `ExtentProfile`, one identity model — read and write are two halves of one thing, so one proposal. The **value-facing read half is delivered** (WI-796/797/773/771/806/810/811/774/812 — the trait read half, mounts, the `read_facts` accessor, cpp-gen migration); lifting its Rust cursor from `Value` to `StoredRow` belongs with the **write design** (WI-780 — the write seam + store-native identity + the declared-API cutover; WI-779 — the one early resident slice, the fact-shape refusal). Written for the **end state**: the boundary identity is store-native, and no `RuleId`/`FactId` appears in any interface signature.

## Tracks: (read, delivered at the `Value` boundary) WI-773 accessor, WI-771 cpp-gen migration; (write, design) WI-780 the `StoredRow` lift, seam + cutover, WI-779 the resident fact-shape refusal. Carries `RuleId`/`FactId` retirement **R1** (readers off the raw walk — done), **R2** (one home), **R3** (declared-API cutover), **R4** (visibility ratchet).

## Relates to: [the extent-sources vision](future/extent-sources.md) (broader model — the deferred capabilities: volatile/oracle/cache/constraints; this is its implementable read+write slice), 007 (persistence — the `Store`/`NonMonotonicStore` trait + monotonicity policy this realizes, the config-in-file idea §8), 053 (the monotonicity ladder *is* the writability axis; `retract` gated on `non_monotone`), 037 (`Modify`; `update` named so as not to shadow it), 026.1 Q4 / `kb/route.rs` (the `RouteHandler` prototype this retires), WI-772 (blanket bodied-rule refusal — the safe polarity the fact-shape refusal reuses), WI-696 (carrier-neutral `Value` goals).

## The model — one owner, EDB/IDB, identity follows residence

A functor's **extent** is provided by exactly one **extent source**: the **resident** source (today's `kb.rules` + discrim — program facts, reflection, realization tables), an **external table** (SQL, an indexed file, a service), or an **oracle** (computed). This is the deductive-DB split, and it decides identity:

- **IDB (bodied rules — program text)** stays resident and **`RuleId`-addressed**. A `RuleId` is an index into `kb.rules`; that is its *only* jurisdiction — never a fact identity.
- **EDB (ground facts)** is owned per functor. A store-owned row rides as `Row(Value)` — carrier-neutral, entering σ via `bind_value` with no `TermStore` allocation — so a **10⁶-row extent answers without materializing 10⁶ `RuleEntry`s**. It has no `RuleId`, no `RuleEntry`, no hash-consed head.

So the **boundary identity is store-native** — content (the canonical ground row) or a domain/primary key — never `RuleId`, and never the `FactId = Handle(RuleId)` that wraps it. This is uniform: even the resident source's durable identity is content; its `RuleId` is a current implementation index, retired by R4.

**End-state invariant (checkable at review):** `RuleId` appears in no signature of `ExtentSource`, the accessor, the write seam, or any `.anthill`-declared operation; `FactId`/`Literal::Handle` are deleted. The only `RuleId` that survives is the resolver-internal `Resident(RuleId)` candidate tag, inside kb.

## Scope

**In.** One owner per functor, reads *and* writes; the `ExtentSource` trait (read half `owned`+`query`, write half `persist`/`retract`/`update`/`flush`); the profile; the query contract + the values-first `read_facts` accessor (delivered); the `StoredRow` Rust-carrier lift, write seam (`assert`/`update`/`retract_persistent`) + store-native identity + the fact-shape refusal (design); single-owner discrim mounts; the two registration roles (owner/mirror); declarative configuration; `RuleId`/`FactId` retirement R1–R4; one shipped reference owner (`InMemoryExtentSource`).

**Out (→ the [vision](future/extent-sources.md), loud-refused behind the complete interface).** Volatile sources + observation memo, the oracle archetype, the cache matrix + epochs, constraint delta-checking — named open problems, not designed here. External-owner *writes* through a real backend exist in the trait but loud-refuse `NotWritable` until a real writable backend lands.

"Complete interface" binds per **caller**: a value-facing read caller migrates onto the final read contract (values-first, resident + mounted) with nothing changing when writes land; the Rust cursor gains its `StoredRow` locator at the write cutover without changing that boundary. A write caller migrates once at the cutover. The trait is never larger than the code — each method-set arrives with its implementation.

## The interface

One `ExtentSource` trait; the read half is delivered, the write half designed. The Rust extent seam carries a `StoredRow`: visible `Value` content paired with an opaque, store-native `RowKey`. The resolver and value-facing accessors project the `Value`; the key never crosses into an `.anthill` signature. No `RuleId`/`FactId`/`TermId` appears anywhere.

```rust
pub trait ExtentSource {
    /// Registration authority: the (fully-qualified functor name, profile) pairs
    /// this source owns. Names resolve to Symbols once, at registration.
    fn owned(&self) -> Vec<(String, ExtentProfile)>;

    // ── read half (delivered) ──
    /// A lazy cursor over the ground rows matching `pattern` (see "the query
    /// contract"). Returns a superset; the engine re-filters.
    fn query(&self, kb: &KnowledgeBase, pattern: &QueryPattern)
        -> Result<Box<dyn ExtentCursor>, ExtentError>;

    // ── write half (design; capability-gated — the profile is the plan-time
    //    authority, these defaults the loud NotWritable backstop) ──
    fn persist(&mut self, kb: &KnowledgeBase, row: &Value, meta: Option<&Value>)
        -> Result<StoredRow, ExtentError> { Err(ExtentError::NotWritable) }
    fn retract(&mut self, kb: &KnowledgeBase, key: &RowKey)
        -> Result<bool, ExtentError> { Err(ExtentError::NotWritable) }
    /// Atomically replace the row identified by `key`. On failure the old row
    /// remains observable; there is no retract-then-persist default.
    fn update(&mut self, kb: &KnowledgeBase, key: &RowKey, new: &Value, meta: Option<&Value>)
        -> Result<Option<StoredRow>, ExtentError> { Err(ExtentError::NotWritable) }
    fn flush(&mut self, kb: &KnowledgeBase) -> Result<(), ExtentError> { Ok(()) }
}

pub struct StoredRow {
    pub row: Value,       // ground content: resolver / read_facts project this
    pub key: RowKey,      // opaque source-native locator: only the extent seam uses this
}

pub trait ExtentCursor {   // lazy, carrier-neutral, ground rows; per-row errors fail loud
    fn next(&mut self, kb: &KnowledgeBase) -> Option<Result<StoredRow, ExtentError>>;
}

/// `QueryPattern` is a digested read bound: the engine walks the goal, the store
/// never sees a raw `Term`. A source returns its own opaque `RowKey` alongside each
/// result. It may be a primary key, a file span, a remote revision token, or another
/// native locator; it is deliberately *not* required to be reconstructible from the
/// row's `Value`.
pub struct QueryPattern { pub mode: usize, pub bound: Vec<(ArgKey, Value)> }
pub struct RowKey(/* source-private, opaque store-native data */);
pub enum ArgKey { Named(Symbol), Pos(u32) }

pub struct ExtentProfile {
    // read axes
    pub query_modes: Vec<QueryMode>,       // which args can be ground (the store's pattern description)
    pub enumerable: bool,
    pub complete: bool,
    pub stability: Stability,
    // write axes
    pub lookup_key: Option<Vec<ArgKey>>,   // optional row-derived locator for content-only callers; opaque keys ride StoredRow
    pub writability: Option<Monotonicity>, // 053's ladder; None = policy from project reflect rules
}
pub struct QueryMode { pub required_ground: Vec<ArgKey> }
pub enum Stability { Stable, Volatile }
pub enum ExtentError { NoSupportedMode, NotWritable, Backend(String) }  // grows with slices
```

**The query contract (read)** — three rules: (1) capability is declared (`query_modes`, matched at registration; a goal meeting no mode delays (WI-300) or flounders loud — a backend never re-derives groundness); (2) pushdown is ground equality only (`bound = slot=value`; richer predicates extend the struct, never re-parse a blob); (3) soundness stated once — `query` returns a **superset** of the rows satisfying `bound`, the engine re-unifies each against the full goal (`match_view_value_pattern`), so over-return is sound and only under-return is a bug.

**The write contract** — the anthill surface speaks `Term` (content). Rust extent operations retain the `RowKey` returned with a `StoredRow`; they never infer that every store-native key lives in the row. A source may additionally declare `lookup_key` for a content-only caller, but that is an optimization/convenience, not the identity model:

```
operation persist(store: Store, fact: Term, meta: Meta) -> Term          -- the canonical row, store-assigned key filled in
operation retract(store: NonMonotonicStore, fact: Term) -> Bool          -- content-only adapter where a lookup_key is declared
operation update(store: NonMonotonicStore, old: Term, new: Term) -> Option[T = Term]
```

`find_fact` + the `FactId` sort are **deleted** — a source-native `RowKey`, carried with the `StoredRow`, is the Rust mutation locator. A writable source need not encode that locator in its row: SQL may use a primary key, an indexed file a span, and a service a revision token. **Minting** rides the `StoredRow` return channel: a store may return a canonical row with a visible assigned field, an opaque key, or both. **Update is atomic:** either the old row is replaced and the returned `StoredRow` names the replacement, or an error leaves the old row observable; a backend must use its native transaction/buffered replacement/rollback mechanism and may not implement update as an exposed retract followed by persist. Bulk "delete WHERE" is *not* the identity primitive — it is read-then-retract-each `StoredRow` selected by a `QueryPattern`.

## The accessor and the write seam (on `KnowledgeBase`)

The engine side: `StoredRow` in the extent seam, `Value` at its value-facing boundary. `read_facts` projects each `StoredRow.row`; resolver matching likewise sees only the row. The seam retains `StoredRow.key` for mutation instead of re-digesting it from content. `Stability::Volatile`, a non-enumerable oracle mode, and external-owner writes are loud errors/refusals until their slices land.

```rust
impl KnowledgeBase {
    // ── read (delivered) ──
    /// Rows for `functor` under the ground `selection` (= QueryPattern.bound), over
    /// resident AND mounted extents uniformly. Values, never RuleId. `policy` decides
    /// bodied candidates: `Refuse` = facts-only (a bodied candidate is a loud
    /// ExtentReadError::BodiedRule). Resolve IS SLD — the sibling `read_facts_resolved`
    /// (&mut self, WI-774) — EVALUATES bodied rules instead of refusing them.
    pub fn read_facts(&self, functor: Symbol, selection: &[(Symbol, Value)],
                      policy: BodiedRulePolicy) -> Result<Vec<Value>, ExtentReadError>;

    // ── write (design; WI-780) ──
    /// THE write seam. Owns internally, in order: 053 guard → fact-shape refusal
    /// (resident) → owner persist (which returns a `StoredRow`) or resident write +
    /// mirror shadow → write-overlay bookkeeping → epoch bump. An update/retract
    /// carries the `StoredRow.key` returned by an earlier extent read/write. The
    /// store-before-kb ordering that today is a comment protocol lives inside.
    /// `update_persistent` is one atomic store/overlay transition: readers never
    /// observe the transient absence that a retract+persist decomposition creates.
    /// Returns the canonical row and its opaque mutation locator. Errors seam-typed;
    /// the builtin adapter renders them
    /// into the `Error` effect (the seam stays evaluator-free).
    pub fn assert_persistent(&mut self, row: Value, meta: Option<Value>) -> Result<StoredRow, ExtentError>;
    pub fn update_persistent(&mut self, old: &StoredRow, new: Value, meta: Option<Value>) -> Result<Option<StoredRow>, ExtentError>;
    pub fn retract_persistent(&mut self, row: &StoredRow) -> Result<bool, ExtentError>;
}
```

The branch (resident discrim vs mount `query`; resident write vs owner buffer) is internal; value-facing callers never see a key. An empty `selection` = enumeration. `read_facts` maps the internal stream to `Vec<Value>` and keeps the accessor `RuleId`-free (R1) so the R4 ratchet can privatize the raw walk.

## Mounts, single owner, registration roles

A store-owned functor is **mounted** at its discrim functor node; retrieval delegates to `query`, yielding tagged candidates `Resident(RuleId)` | `Row(StoredRow)` on the one seam (`RouteHandler`/`Store::retrieve` retire into it — R2). The resolver binds `StoredRow.row` and keeps its key only for the write seam. Ownership is exclusive: an owner for a functor with resident entries, two owners for one functor, or a source-file `fact`/same-head bodied `rule` for an owned functor — each a loud error / `LoadError`. The registries merge into `kb.extents`, off `Interpreter` (R2). Two **roles**, composed by registration:

- **owner** (`register_extent_owner`) — the store owns the extent; reads go through the mount → `query`, the resident subtree is empty. External table / SQL / GitHub.
- **mirror** (`register_mirror`) — the functor is resident (`kb.rules` answers reads); the store is a write-through durability mirror (`pull` at load, shadow resident writes; `query` never consulted). Today's `FileStore` is exactly this.

## Configuration & bootstrap

007 §8's idea — configure the store *declaratively in the project's initial file* — but on the single-owner model, not precedence `route` rules. Today only the **backend instantiation** is hardcoded (anthill-todo's `main.rs` builds a fixed `IndexedFileStore` + `register_store`); the store *spec* (`WorkItemStore`, 036/WI-203) and the *write policy* (`rule fact_monotonicity(WorkItem) = non_monotone()`) are already anthill-declarative in the bundle. So the change is narrow:

- **Single-owner binding, not `route` rules.** A **binding fact** — `fact extent_owner(WorkItem, FileStore(root: "anthill", convention: single_file("workitems.anthill")))` — read at registration, mounts the functor. The catch-all `rule route(?)`, specific-before-default precedence, and the vestigial `route` op (zero rules/callers today) are gone.
- **Writability materializes from `fact_monotonicity`, not a new field.** `ExtentProfile.writability` stays `Option` and defers: `None` = the project's reflect rules decide (anthill-todo's file store — `WorkItem`'s `non_monotone` comes from the bundle rule, as `resolve_fact_monotonicity` already resolves: project rule → store policy → `monotone` default); `Some(_)` only for a store whose policy is intrinsic (a SQL schema).
- **A host factory** maps the declared store sort (`FileStore`/`SqlStore`) to its Rust `ExtentSource` constructor — the one piece that stays native (a backend is Rust; declarative config chooses *among* the host's compiled-in backends, it cannot load new native code). The host reads the bindings, instantiates each backend, registers it as owner or mirror.
- **Bootstrap store** (007 §8): a file store at a well-known path loads `project.anthill` first, then its declared stores mount.

anthill-todo's fixed file store becomes one such declared binding; a project can then declare a SQL/GitHub owner without a new host binary. Its `store.anthill` is the concrete **R3 migration target** — the cutover rewrites its `WorkItemStore` bodies (`find_fact` → content-keyed `forget`; the two-flush `replace` → `update`) over the seam.

## The fact-shape refusal (WI-779) — the resident IDB↔EDB core

The one write hazard that is **IDB-only, by the model**: hash-consing shares the head `TermId` between a fact `H` and a bodied `rule H :- B`, so today `find_fact` mints a retract handle for the *bodied* rule and `retract` drops it through the fact API — the store canonical-matches the printed *head*, the source line is `rule H :- B`, no match, the file keeps the rule the KB dropped, the next load resurrects it (silent desync). And a KB-side retract of `H` is a lie while `rule H :- B` still derives it.

This can only happen where facts and bodied rules coexist under one functor — the **resident** core. An EDB functor structurally cannot have a bodied head (a bodied rule on an owned functor is a `LoadError`), so a 10⁶-row extent never reaches this and needs no identity for it. So the refusal is a **content-keyed internal step of the resident write path** — keyed on the head (mirroring `read_facts(Refuse)`), O(1)-gated by `has_bodied_rule` (WI-812), refusing loud (blanket, WI-772) and naming the rule via `print_rule`. It surfaces no `RuleId`/`FactId`. **WI-779** lands exactly this, ahead of the full seam, because the desync is a live bug.

## `InMemoryExtentSource` — the reference owner

The shipped reference `ExtentSource`: an enumerable + complete + stable table, seeded at construction. Its value-facing read half is delivered (drives the read conformance suite — declared mode answers, undeclared pattern delays, under-return fails / over-return passes); its cursor gains `StoredRow` and its write half + a `by_id`-style opaque key land with the write seam (exercising the write overlay + content↔key mapping without a filesystem/SQL engine). It is the owner-swap fixture and the proof "complete interface" is a fact, not a claim. The **resident** default source stays the discrim path (not a `dyn ExtentSource` — the discrim tree already *is* its query structure), unified with mounted extents only at the accessor/seam.

## `RuleId`/`FactId` retirement — R1–R4

- **R1 — readers off the raw walk** (done): no fact reader outside kb traffics in `RuleId`; the accessor is values-first.
- **R2 — one home**: `RouteHandler`/`Store::retrieve` retire into `query`; `store_registry`/`store_monotonicity` move off `Interpreter` onto `kb.extents`; `register_store` → `register_mirror`/`register_extent_owner`.
- **R3 — the declared-API cutover** (atomic): the `store.anthill`/`reflect.anthill` signatures above; `FactId`/`find_fact`/`Handle`/`HandleKind` deletion; `IndexedStore::location_of` rekeyed to the store-internal `RowKey → Location`; `StoredRow` on every Rust extent read/write path, projected to `Value` for `read_facts` and resolver matching; the seam as the sole caller of the store write half; every in-tree `.anthill` consumer migrated together. No shims — loud stragglers.
- **R4 — the visibility ratchet**: `kb.retract(RuleId)` → `pub(crate)` (seam-only); head-as-answer enumeration privatized. Sequences after R1.

End state: `RuleId` addresses resident IDB program text only; the rule-browse surface (`rule_ids_by_qn`, CLI `--match`, `is_fact`/`is_rule_alive`) stays public.

## Decomposition

**Read (delivered):**
1. the value-row trait read half + mounts + `QueryPattern` + `RouteHandler`/`Store::retrieve` retirement (R2-read) + loader refusal;
2. `InMemoryExtentSource` + read conformance suite + owner-swap harness;
3. `read_facts` (WI-773, R1) + cpp-gen facts-only migration (WI-771).

**Write (forthcoming):**
4. **resident fact-shape refusal (WI-779)** — content-keyed, ahead of the identity cutover, fixing the live desync;
5. **one write home (R2-write)** — `store_registry`/`store_monotonicity` → `kb.extents`, registration roles;
6. **the write seam + identity cutover (WI-780, R3)** — lift the Rust cursor to `StoredRow` / opaque store-native `RowKey`, then `assert`/`update`/`retract_persistent`, `NonMonotonicStore.update`, the write overlay, `FactId`/`find_fact`/`Handle` deletion, the config binding, every `.anthill` consumer migrated (anthill-todo's `store.anthill`);
7. **ratchet + reference write impl (R4 tail)** — `kb.retract` → `pub(crate)`, `InMemoryExtentSource` write half + write conformance suite, the end-state-invariant review check.

Each lands green via `scripts/test.sh`. The deferred capabilities (volatile, oracle, cache, constraints) follow as direction in the [vision](future/extent-sources.md).
