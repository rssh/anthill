# 057: Extent Read Seam

## Status: Draft (2026-07-21). The first implementable slice of the [extent-sources vision](future/extent-sources.md), extracted under its "complete interface, not a partial one" rule. This proposal is the **complete read seam** — enough to virtualize a functor's reads through one owner and to migrate every fact-reader onto a values-first accessor — and deliberately **nothing of the write side** (that is the write seam, tracked by **WI-780** — written as its own proposal when it is built, not pre-numbered here). Self-contained: it states the read API it implements; the vision doc is background, not a dependency.

## Tracks: WI-773 (the accessor — its API *is* §"The accessor"), WI-771 (the first migration — cpp-gen realization readers). Carries retirement stages **R1** (readers off the raw walk) and **R2** (one read seam, one home) from the vision's `RuleId` plan. Does **not** carry R3/R4 (write-boundary + `RuleId` privatization) — those wait on the write seam (WI-780).

## Relates to: [the extent-sources vision](future/extent-sources.md) (broader model + rationale; this proposal is its minimal read slice, not a re-reading of it), 026.1 Q4 / `kb/route.rs` (the `RouteHandler` prototype this retires), WI-774 (the `Resolve` read policy — a *value* of this proposal's policy parameter, itself deferred), WI-696 (carrier-neutral `Value` goals).

## Scope — exactly the read seam

**In.** One owner per functor for *reads*; the `ExtentSource` trait **read half** (`owned` + `query` — the trait grows one method-set per slice, each arriving *with* its implementation, never ahead of it); discrim mounts; the query contract (`QueryPattern`); the values-first accessor over resident **and** mounted extents; one shipped reference owner, `InMemoryExtentSource` (read-only in this slice); the single-owner loader refusal on the read side.

**Out (untouched, not stubbed).** The write half of the trait, the engine write seam (`assert/update/retract_persistent`), store-native identity, `FactId`/`RuleId` retirement R3/R4, and the anthill-level `persist`/`retract`/`update` API → **the write seam (WI-780)**, *written as its own proposal when it is built*. Volatile sources + observation memo, the oracle archetype, the cache matrix + epochs, constraint delta-checking → named open problems in the [vision](future/extent-sources.md), **not designed until implemented**. The `Resolve` read policy → **WI-774**.

Why the read seam alone is *complete*, not partial: "complete interface" binds per **caller**, not per trait. A read caller (cpp-gen) migrates onto the final read contract — values-first, resident **and** mounted, the full query contract — and nothing about it changes when the write seam adds writes (writes are orthogonal to how reads answer). Write callers stay on today's `Store` path, untouched, until they migrate *once* at the write seam (WI-780) — where the write half is added *then*, with its code. The trait is never larger than what is implemented: a method signature carried "for later" is the same speculative liability this split exists to remove.

## The read interface

The trait in this slice is the **read half only** — `owned` + `query`. Write, mirror, and sync methods are *not* in it yet; each arrives in the slice that implements it (writes with the write seam, WI-780), with its caller. The trait grows with the code, never ahead of it.

```rust
/// One owner per functor, mounted at its discrim functor node.
pub trait ExtentSource {
    /// Registration authority: the (fully-qualified functor name, profile)
    /// pairs this source owns. Names resolve to Symbols once, at registration
    /// (unresolvable name = loud error); every engine structure is Symbol-keyed.
    fn owned(&self) -> Vec<(String, ExtentProfile)>;

    /// The discrimination contract of the mounted subtree: a lazy cursor over
    /// the ground rows matching `pattern` (see "The query contract").
    fn query(&self, kb: &KnowledgeBase, pattern: &QueryPattern)
        -> Result<Box<dyn ExtentCursor>, ExtentError>;
}

/// Lazy, carrier-neutral, ground rows — enter σ via `bind_value`, no interning.
/// Errors are per-row so a fallible backend fails loud, never truncates silent.
pub trait ExtentCursor {
    fn next(&mut self, kb: &KnowledgeBase) -> Option<Result<Value, ExtentError>>;
}

/// The digested selection for one call — the engine already walked the goal.
pub struct QueryPattern { pub mode: usize, pub bound: Vec<(ArgKey, Value)> }
pub enum ArgKey { Named(Symbol), Pos(u32) }

/// The read profile (this slice's axes; `writability` arrives with the write seam).
pub struct ExtentProfile {
    pub query_modes: Vec<QueryMode>,   // the store's pattern description
    pub enumerable: bool,
    pub complete: bool,
    pub stability: Stability,
}
pub struct QueryMode { pub required_ground: Vec<ArgKey> }
pub enum Stability { Stable, Volatile }
pub enum ExtentError { NoSupportedMode, Backend(String) } // grows with slices
```

**The query contract** — the three rules a backend obeys, and what makes the raw-`Value` pattern a *typed, described* one:

1. **Capability is declared.** `query_modes` is the store's pattern description, read at registration. The engine matches the goal to a satisfied mode, or delays it (WI-300), or flounders loud — a backend never re-derives groundness from a `Value`. `QueryPattern.mode` names which mode this call took.
2. **Pushdown vocabulary is ground equality only.** `bound` is every fully-ground argument slot as `slot = value`, nothing else; richer predicates extend the struct in a later slice, never re-parse a blob.
3. **Soundness, stated once.** `query` returns a **superset** of the rows satisfying every `bound` equality; the engine re-unifies each returned row against the full goal (`match_view_value_pattern`) and drops non-matches, so over-return is sound and only under-return (dropping a row that satisfies `bound`) is a bug. A source that ignores `bound` and streams its extent is correct, just slow.

`Stability::Volatile` and a non-enumerable oracle mode are **loud registration errors** until their slices land — the interface refuses a capability it has not implemented rather than pretending to it.

## Mounts, single owner, loader refusal (read side)

A store-owned functor is **mounted** at its discrim functor node; retrieval reaching the mount delegates to `query`, yielding tagged candidates `Resident(RuleId)` | `Row(Value)` on the one seam (`RouteHandler` and `Store::retrieve` retire into it — R2). Ownership is exclusive: registering an owner for a functor that already has resident entries, or two owners for one functor, is a loud error; and a source-file `fact` (or same-head bodied `rule`) for an externally-owned functor is a `LoadError`. The registries merge into the KB-owned `ExtentRegistry` (`kb.extents`), off `Interpreter`. (Rationale for single-owner exclusivity: the [vision](future/extent-sources.md) §"Model".)

## The accessor (WI-773)

The values-first read primitive every fact-reader migrates onto:

```rust
impl KnowledgeBase {
    /// Rows for `functor` under the ground `selection` (= QueryPattern.bound),
    /// over resident AND mounted extents uniformly. Values, never RuleId
    /// (values, never RuleId). `policy` decides bodied candidates.
    pub fn read_facts(&self, functor: Symbol, selection: &[(Symbol, Value)],
                      policy: BodiedRulePolicy)
        -> Result<Vec<Value>, ExtentReadError>;
}

pub enum BodiedRulePolicy {
    /// Facts-only: a bodied candidate is a loud Err reporting the rule via
    /// TermPrinter::print_rule (Result-over-panic, so CLI/codegen render it
    /// through their own error channels — not an assert-abort).
    Refuse,
    // Resolve { .. } — WI-774, a later value of this parameter.
}
```

The branch (resident discrim vs mount `query`) is internal; callers never see it. `selection` empty = enumeration. This is retirement stage R1: keep the accessor `RuleId`-free so the R4 ratchet (in the write seam, WI-780) can privatize the raw walk.

## `InMemoryExtentSource` — the reference owner

The shipped reference `ExtentSource`: an enumerable + complete + stable table, **seeded at construction**, read-only in this slice (it implements `owned` + `query`; mutation arrives with the write seam when the trait gains a write half). It exists so the mounted path is *real and tested*, not vacuous — the conformance suite mounts it and drives the query contract against it (declared mode answers, undeclared pattern delays, under-return fails / over-return passes). It is also the owner-swap fixture and a batteries-included mountable extent for embedders. The **resident** default source stays the discrim path (not a `dyn ExtentSource` — the discrim tree already *is* its query structure), unified with mounted extents only at the accessor.

## Consumers in this slice

- **WI-773** — the accessor above, with a pinned bodied-rule-policy test.
- **WI-771** — migrate cpp-gen's facts-only realization readers (`CarrierTable`/`OpImplTable`/`generated_targets`, `query_realization_facts`, the op_info readers) onto `read_facts(functor, selection, Refuse)`; the placeholder-var build, `query_view`, `is_fact` assert, and `rule_head` extraction all collapse into the accessor, and the refusal renders through `CppCodegenError`. cpp-gen reads the **resident** realization tables today; the same code reads a mounted `realization.*` store the day one is registered, unchanged — the store-API payoff. (The EffectMapping/LanguageMapping candidate readers want the `Resolve` policy = WI-774, out of this slice.)

## Decomposition

1. **Read seam** — `ExtentSource` trait (read half: `owned` + `query`), `ExtentRegistry`/`kb.extents`, discrim mounts + tagged candidates, `QueryPattern` + query-contract enforcement, `RouteHandler`/`Store::retrieve` retirement (R2), loader read-side refusal.
2. **`InMemoryExtentSource` + conformance suite** — the shipped reference owner and the trait-level property tests it is driven against; the owner-swap harness.
3. **Accessor + first migration** — `read_facts` (WI-773, R1) and the cpp-gen facts-only readers onto it (WI-771).

Each lands green via `scripts/test.sh`. The write seam, `RuleId` retirement R3/R4, and all deferred capability follow in the write seam's own proposal (WI-780) and, as direction, the [vision](future/extent-sources.md).
