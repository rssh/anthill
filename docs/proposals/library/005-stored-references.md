# Library: Stored references — `FactRef` and `StoredRef[T]`

## Status

Draft 2026-07-24. Driver: WI-780 / proposal 057's R3 extent-write cutover.
This is a library-level abstraction over a runtime-provided opaque reference; it
does not add a language identity primitive. It replaces the resident-only
`anthill.reflect.FactId` boundary with one reference type that is valid for
resident and extent-owned rows alike.

## Motivation

A value says what a row contains; it does not necessarily say how its owner
locates that row. This distinction matters for an extent source: a SQL row may
be located by a primary key, an indexed-file row by a source span, and a remote
row by an opaque revision token. None need be reconstructible from its visible
`Term`.

The current `FactId` is not such an abstraction. It is
`Handle(Fact, RuleId.raw)`: a resident-KB implementation index, invalid outside
one process and impossible for an external extent to produce. Clients therefore
perform the resident-only dance `facts_of` → `find_fact` → `FactId` → `retract`.
That prevents a client from being indifferent to whether its row is resident or
store-owned.

The library needs an opaque reference paired with its visible value. A caller
can then read, persist, update, or retract a row without learning its backing
model.

## Design

The standard library exposes two types:

```anthill
namespace anthill.reflect
  sort FactRef = ?              -- opaque runtime reference to one stored row
  entity StoredRef[T](value: T, reference: FactRef)
```

`StoredRef[T]` is an ordinary immutable pair: `value` is safe application data;
`reference` is an opaque mutation capability. Its generic form makes the
abstraction useful beyond reflection, while the first consumer is
`StoredRef[Term]` at the persistence boundary.

At the Rust extent seam the corresponding carrier is:

```rust
pub struct StoredRow {
    pub row: Value,
    pub reference: FactRef,
}
```

`FactRef` is constructed only by the KB / extent registry. Its private payload
selects the owning source and carries that source's opaque `RowKey`. A resident
reference may use a `RuleId` internally; an external reference uses its native
key. Neither representation is observable in Anthill, and `RuleId` appears in
no public signature.

### Lifetime and capabilities

`FactRef` is valid only for the KB session that produced it, until the referenced
row is replaced or retracted. It is passable to the persistence operations, but
is not serializable, printable as a durable identifier, or constructible by user
code. A backend that offers a durable domain identifier puts that identifier in
the row's ordinary `value`; it does not change `FactRef`'s session-reference
contract.

This deliberately prevents an application from persisting an in-memory rule
slot or a file span as data. A later process reads a fresh `StoredRef` from its
source.

### Internal representation: identity, not shape

`FactRef` holds a **session identity** and presents **no structure** to the term
view (`ViewHead::Opaque`). Two are equal iff they locate the same row; a
structural key is deliberately not derived from them, so the consumers that need
an injective key (`GoalKey::is_opaque_free` for fact dedup, `is_cacheable` for
the query cache) degrade to no-dedup rather than merging two rows.

This is a property of what a `FactRef` is spelled in, not of the word
"reference". A reference whose target is named by a `Symbol` has a shape worth
presenting — the runtime `OpRef` is one, and it views structurally
(`docs/design/requirement-dictionaries.md` §2.4.1). A `FactRef` instead locates
its target by a private slot index — a `RuleId`, or a source's `RowKey` — which
has no `Value` carrier and denotes nothing outside the KB that minted it.
Presenting it would mint that index as data, which is exactly what the
capabilities above forbid.

Equality here is a Rust-internal comparison of the private payload; it is not an
`Eq` instance, and it exposes nothing. Anthill code still cannot construct,
print, or persist a `FactRef` — those prohibitions live at the surface and are
unaffected.

### Uniform persistence surface

The R3 cutover changes the relevant declared operations to the following shape:

```anthill
operation persist(store: Store, fact: Term, meta: Meta) -> StoredRef[T = Term]
operation retract(store: NonMonotonicStore, reference: FactRef) -> Bool
operation update(store: NonMonotonicStore, reference: FactRef, new: Term)
  -> Option[T = StoredRef[Term]]
operation KB.assert(kb: KB, term: Term, sort: Type)
  -> Option[T = StoredRef[Term]]
```

The corresponding read operation for a caller that may mutate a selected row
returns `StoredRef[Term]` values. Values-only readers—including
`KnowledgeBase.read_facts` and resolver matching—project `.value` and do not
carry references unnecessarily.

`update` is atomic: it either returns the replacement `StoredRef` or leaves the
old row observable. A reference is therefore replaced, not mutated in place;
callers retain the returned reference for a later write.

## Migration

R3 is one atomic in-tree migration:

1. Add `FactRef` and `StoredRef[T]` to the reflection standard-library module.
2. Lift the Rust extent cursor and write results to `StoredRow`.
3. Migrate persistence/reflection clients—including `KB.assert`—from `FactId`
   to `FactRef` and use a read-with-reference operation where they select a row
   for mutation.
4. Delete `find_fact`, `FactId`, and `Literal::Handle(Fact, RuleId)`.

There is no long-lived `type FactId = FactRef` compatibility alias: it retains
the misleading resident-only name and creates a second public migration. WI-779
keeps `FactId` only as an interim compatibility boundary while it adds the
resident bodied-rule refusal; WI-780 performs this cutover.

## Interaction with extent sources

Proposal [057](../057-extent-seam.md) owns extent ownership, `RowKey`, and the
write seam. This proposal owns the reusable public pairing of a value with an
opaque reference. `RowKey` remains Rust/source-private; only `FactRef` crosses
the declared library boundary.

This supports both extent roles:

- A **mirror** produces resident references while its backing store shadows
  writes.
- An **owner** produces source-native references directly from its query cursor.

Application code receives the same `StoredRef[Term]` in either case.
