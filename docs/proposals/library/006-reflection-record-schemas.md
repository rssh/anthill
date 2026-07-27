# Library: Declared reflection record schemas

## Status

Draft 2026-07-27. Driver: WI-834; related to WI-820 and proposal
[057](../057-extent-seam.md).

This is a standard-library vocabulary correction. It makes two reflection row
shapes ordinary declared entities; it adds neither a new term representation nor
a new schema language feature.

## Motivation

The resolver can enumerate a fact relation only when it knows the relation's
complete field schema. `KnowledgeBase::read_facts_resolved` builds a full-arity
goal—one fresh variable for every unselected field—because a partial record
would silently fail to unify with a stored full record. A missing schema is
therefore correctly a loud `NoFieldSchema` error, not an empty result.

Most reflection rows already meet this contract. `SortInfo`, `OperationInfo`,
`FieldInfo`, `EntityInfo`, `SortRequiresInfo`, and `DescriptionInfo` are
declared in `anthill.reflect`; scan pass 1 registers their field names before
any rows are emitted.

Two older loader-private row shapes do not:

* `anthill.reflect.member(name, kind, parent)` is emitted as a positional
  metadata term under a qualified-only internal functor.
* `Description(target, content, index)` is emitted under the old global
  `Description` metadata functor, even though the public reflection result is
  already named `DescriptionInfo`.

The reflection readers can currently enumerate those rows only through the
non-resolving `read_facts(..., Refuse)` path. Trying to switch a reader to
`read_facts_resolved` exposes the missing schema in bootstrap and test KBs.
Recovering field names by inspecting an existing row is not a solution: an
empty relation then has no schema, a body-only relation has no resident witness,
and a malformed row becomes authority for the public contract.

## Design

Reflection metadata that has a stable record shape is declared in the
reflection library. Add the missing declaration:

```anthill
namespace anthill.reflect
enum MemberKind
    entity Constructor
    entity Operation
    entity Rule
    entity Sort
    entity Enum
    entity Namespace
    entity Const
  end

  entity MemberInfo(
    name   : Symbol,
    kind   : MemberKind,
    parent : Term
  )
end
```

`DescriptionInfo` remains the existing declaration:

```anthill
entity DescriptionInfo(
  target  : Symbol,
  content : String,
  index   : Int64
)
```

The loader emits named facts of exactly these functors:

```anthill
MemberInfo(name: Foo, kind: Constructor, parent: SomeSort)
DescriptionInfo(target: Foo, content: "…", index: 0)
```

`parent : Term` preserves the current representation of a sort or namespace
reference. It is intentionally not narrowed to `Symbol`: reflection must carry
the same term-shaped scope reference the loader already emits. `MemberKind` is
the closed representation of the declaration categories:
`Constructor`, `Operation`, `Rule`, `Sort`, `Enum`, `Namespace`, and `Const`.
A client can therefore match exhaustively instead of comparing display strings.

`Const` is deliberately distinct from `Operation`. Proposal
[039](../039-term-level-constants.md) defines a constant as a `SymbolKind::Const`
whose typed value is produced by a nullary reflect function and memoized. It is
value-denoting in term position, has no call interface, and is not a desugared
zero-argument operation. Reflection must preserve that distinction.

The declaration is the schema authority. Because the reflection library is
scanned before metadata emission, `entity_field_names(MemberInfo)` and
`entity_field_names(DescriptionInfo)` are available in every ordinary loaded,
bootstrap, and test KB. Declared field order also becomes the one canonical
order used by record construction, discrimination-tree queries, and reified
answers.

### Reader contract

Readers decode these rows by field name through `TermView`; they do not inspect
positional slots and do not infer a field set from an arbitrary resident row.
A missing required field or an incompatible carrier is a loud reader error.

This proposal supplies the prerequisite for a resolving read; it does **not**
make every reflection reader resolving. The choice remains semantic:

* a reader asking for the source-declared program inventory may retain
  `Refuse`, so a derived rule cannot manufacture source metadata;
* a reader asking for effective metadata queries a separate logical relation,
  which may combine source and derived records through resolution.

The two surfaces are deliberately separate. `MemberInfo` and
`DescriptionInfo` are the authoritative source inventory. They answer “what
did this source file declare?”, not “what does this expression dispatch to?”

The first real derived-member consumer is typing a dot call. To type
`x.member(y)`, the typer must resolve from the receiver type and the call
environment to one dispatch decision:

1. the selected member and its signature, so the arguments and result can be
   typed;
2. the dispatch source — an operation of the receiver's concrete sort, or a
   requirement dictionary; and
3. for the dictionary case, the selected requirement/dictionary slot and the
   spec operation to resolve through it.

The concrete dictionary value is not available while typing a polymorphic
operation. The typer selects the *requirement slot*; evaluation later receives
the concrete dictionary in that slot and resolves the spec operation against
its implementation. A concrete receiver can instead be pinned directly to its
operation. This is the existing dictionary-passing distinction; reflection
inventory must not erase it.

Consequently, `derivedMember` must not mean a schema-less union such as
`isMember(name, kind, parent)`. That shape loses the receiver, signature, and
dispatch evidence that the typer needs. If member selection is expressed as an
SLD relation, it needs a purpose-shaped contract — conceptually
`resolveMember(receiverType, memberName, callContext) ->
(signature, dispatchTarget)` — whose `dispatchTarget` records direct versus
requirement-dictionary dispatch. Its exact public record names belong to the
member-dispatch proposal, not this inventory-schema migration.

Such a selection relation is evaluated by normal SLD resolution, where derived
answers, ambiguity, and truncation are explicit. An inventory reader never
reads that relation accidentally; it reads `MemberInfo` under `Refuse`. The
analogous `derivedDescription` relation is added only if a real computed
description view appears.

In particular, schema availability never licenses a silent fallback from
`read_facts_resolved` to `read_facts`, nor a scan of a resident `RuleId` bucket.

## Migration

1. Declare `MemberKind` and `MemberInfo` in
   `stdlib/anthill/reflect/reflect.anthill`; retain `DescriptionInfo` as the
   sole public description-row shape.
2. Change loader emission from the private positional `member` and
   `Description` terms to named `MemberInfo` and `DescriptionInfo` facts.
   The const loader emits `MemberInfo(kind: Const, …)` when proposal 039's
   `SymbolKind::Const` lands.
3. Migrate reflection readers and bridge/builtin tests to the declared
   functors and named decoding.
4. Remove the old `member` and `Description` kernel metadata functors and their
   qualified-only/global registrations. There is no compatibility alias: an
   alias would preserve the schema-less public boundary this proposal removes.
   The loader's internal `Member` / `Description` *fact-sort buckets* are not a
   public row format; retain them for this migration, then remove them only
   after every `by_sort` / `by_domain` caller has been audited.
5. Add bootstrap and empty-relation tests proving that both functors have their
   declared field schemas before any metadata row is emitted. Add a resolver
   enumeration test for each reader that intentionally adopts the Resolve
   policy; its guard behaviour is then tested separately from source-inventory
   readers that intentionally retain Refuse.

## Non-goals

* A first-class, user-extensible `EntitySchema` reflection API. The existing
  entity declaration and KB registry are the authority here.
* Inferring a schema from a row, from symbol interning order, or from a rule
  head.
* Changing the representation of `Term`, `Symbol`, scope references, or
  resident metadata ownership.
* Choosing Resolve for all reflection operations. Source inventory stays on
  `Refuse`; derived views use separate logical relations, as above.

## Interaction with other work

* Proposal 057 requires value-oriented reads to work for resident and
  extent-owned rows alike. Declared schemas let the resolver build the same
  full-arity goal in either case.
* WI-820 identifies the schema gap as the reason STL reflection could not yet
  join the safe Refuse-to-Resolve migrations.
* WI-834 implements this proposal and then reviews each reader's policy. The
  proposal is intentionally smaller than that implementation work: it fixes the
  library contract first.

## Open questions

1. Does `const` need a `ConstInfo` record beyond its `MemberInfo` entry? The
   first consumer that needs its declared type, provenance, or foldability
   decides that shape; it must not overload `MemberInfo` with const-specific
   fields.
2. What is the public representation of a member-dispatch target: a declared
   `MemberResolution` record, or an internal typer result until a library
   consumer needs it? Either way it must preserve direct versus
   requirement-dictionary dispatch; it cannot be a `MemberInfo` row.
