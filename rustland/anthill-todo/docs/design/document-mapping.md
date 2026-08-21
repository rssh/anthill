# The item document format

An item is one file, written to be read. This section defines that file's format
and the declaration that maps a domain onto it.

## 1. File

An item file is named `<id>.anthill.md` and lives in a directory named for the
item's status. The `.anthill.md` **suffix** identifies it (`Path::extension()`
returns `md`, so the test is `ends_with`, not an extension test); `.md` makes
editors and GitHub render it, `.anthill` keeps an ordinary `README.md` in the same
tree from being read as an item.

The filename carries the item's id and the directory carries its status. Both are
also fields (§3), and the field is the source: a disagreement is a diagnostic.

**A satellite fact's key is not written in a document** — an entry in this file is
about this item, so `ChapterGroup(key:)` and `SatelliteList(key:)` fill it from the
item's own `id` (§4.3). The field itself is untouched: every fact the reader
produces carries it, so exports, query output and `orphaned.anthill` are unchanged.
Only a **document** omits it; a file that is not a document — `orphaned.anthill`
holds rows whose item has no file at all — writes it in ordinary fact syntax.

One fault class disappears with it. `MisfiledRow` — a satellite row sitting in a
file other than its item's — is unrepresentable here, because a row that does not
name an item cannot name the wrong one.

## 2. Document structure

A file is a sequence of **chapters**. One of them — named by
`DocumentFormat(attributes:)` — holds the item's own fact as data; the rest hold
prose. The reader finds it by name, at any position; the writer puts it first.

```markdown
## Attributes                            ← the item's fact, as a bullet list

## Description                           ← a prose field of that fact

## Reason                                ← another, present only when filled

## Changes                               ← a container
### 2026-08-17T09:19:35Z — feedback — user   ← an entry
```

There is no region outside a chapter. Text before the first chapter is a load
error, and so is a heading **above** the first structural level (§4.1): the
hierarchy is defined from that level downwards, and a heading above it has no
meaning in this format.

## 3. The Attributes chapter

The attributes chapter is **data**, not anthill source. It is a bullet list with
one line per field of the item's own fact, and holds nothing else — no satellite
facts, no application syntax.

### 3.1 Field lines

```
- key: value
```

`key` matches `[a-z_][a-z0-9_]*` and names a field of the functor, or an attributes
field the mapping declares (§5). Everything after `: ` is the value, with leading and
trailing whitespace removed.

### 3.2 Values

A value's spelling follows its **declared type**. The reader therefore reads the
domain's entity declarations alongside the mapping.

| declared type | written as | example |
| --- | --- | --- |
| `String` | the text, unquoted | `- created: 2026-08-17T08:43:54Z` |
| an enum with no payload | the variant name | `- status: Delivered` |
| `List[T]` | elements separated by `, ` | `- depends_on: WI-1114, WI-1120` |
| `Option[T]` | as `T`; **absent** means `none` | |
| a sort with a declared `ScalarForm` | the scalar, per §5 | `- acceptance: cargo-test` |

A value written **between backticks** is an anthill term, parsed as written:

```
- acceptance: `[FactHolds(domain: "kb", pattern: p)]`
```

That is the spelling for any value the table above cannot express — a string
containing `, `, a payload-carrying variant, an arbitrary `Term`. The writer uses
it only where the data spelling does not apply, so it never has to refuse a value.

**A data value must also be markdown-INERT**, and this is the same escape doing a
second job. A bare value sits in inline context, so a value that would render as
markup rather than as itself has no data spelling and takes the term spelling,
whose backticks are a code span and suspend inline parsing. Rendering is why this
format is `.md` at all, so a value the page shows differently from the data it
denotes is a defect, not a cosmetic issue.

**The test is whether the value renders as itself, not whether it contains a
character from a list**, and the difference is not academic: CommonMark does not
open emphasis with an intraword `_`, so `prop025_1` is inert and a
character-blacklist rule would quote it for nothing. Measured on this tracker,
exactly two values carry any candidate character — the tag `prop025_1` on WI-562
and WI-563 — and both render as themselves; every other id, timestamp, tool name
and tag is alphanumeric with `-`, `+` and `.`. A writer that cannot decide should
**over**-quote: a code span renders the literal text, so the term spelling is
always safe and only ever costs a pair of backticks.

**Length does not decide anything here; the mapping does.** Whether a field is
prose is a property of the field, not of how long one item's value happens to be,
and a threshold would give one field two shapes: on this tracker a 255-character
rule puts 35 descriptions inline and 1092 in a chapter, and moves an author's text
the moment their prose crosses the line. Length is only a **diagnostic** (§7) —
a long value in this chapter means a prose field has not been declared as one.

### 3.2.1 Satellite lists

A `SatelliteList` writes **many facts on one line**: one attributes field whose
value is the elements, separated by `, `.

```
- tags: wi437, prover
- mirrors: github:rssh/anthill=42
```

Each element writes the mapping's `fields` in order, joined by `=` when there is
more than one. Most satellites have one written field — `Tag` has `name`, and its
line is exactly what it was before elements could carry two — and the one that has
two is `MirrorEntry`, which names WHICH external system and WHICH entry there:
neither half identifies the link on its own.

**The last field takes the remainder on read.** The reader splits an element
exactly `fields.len() - 1` times from the left, so a value carrying `=` — a URL
with a query string — reads back whole in the last position. An **earlier** field
carrying one would move the boundary and re-attribute the halves, so the writer
refuses it; there is no escape at this position, the same rule and the same reason
as the `, ` between elements.

**A `ChapterGroup` is not the alternative.** Its body field is prose, so writing
an opaque external identifier through it would render an id as a paragraph and
claim to be something it is not.

### 3.3 Blank lines and field groups

A blank line separates every field line from the next, except that fields named
together in a `FieldGroup` are written **adjacent**, with no blank line between
them.

A group's fields describe one state that changes as a unit. Adjacency makes a
concurrent edit to two of them a merge conflict; a blank line makes two fields
independently mergeable. Fields that are never rewritten belong in a group for the
same reason — nothing can conflict over them.

**What the flat form has to state, and what it must not.** `status` and its
companions were one payload-carrying variant; written as independent fields they
admit an `Open` carrying a stale rejection reason. So the part of the invariant
that is still wanted is restated where the domain lives, as constraints, and a
violation is a **load error**:

```anthill
  constraint rejected_names_its_reason :-
    WorkItem(last_status_change: StatusChange(status: Rejected, reason: none))
  -- …and the same for ProposalRejected and Stale.
```

**Only that much.** It is tempting to restate the old sum's whole shape — `agent`
required on `Claimed`, forbidden on `Open`, and so on — and it would be wrong: that
distribution was IRREGULAR RATHER THAN PRINCIPLED. `agent` appeared on two of nine
variants, `Verified` carried none at all so "who verified this" was unrecorded,
`since` on two against `at` on four, and `Draft` / `PreOpened` / `Open` carried
nothing though somebody performed each of those transitions too. Restating it
faithfully would freeze a defect into the schema. Every status is a transition
somebody made at some time, so `agent` and `at` are uniform provenance, and a
reason is meaningful on any change — what is NOT acceptable is an off-ramp that
does not say why, and that is the one clause above.

They are `Option` because of HISTORY rather than doubt: 985 of 1127 items on this
tracker had already lost who claimed them, because `Delivered` overwrote `Claimed`
in place. Migration synthesizes nothing, so those rows arrive with `none` and say
so; requiring the field would mean inventing an agent for 985 items.

This is check logic where the old encoding had unrepresentability, and that is a
real loss, taken deliberately for the reading the flat form buys. What makes it
acceptable is that the check is **declarative and total** — enforced at load over
every item, not a rule the commands are trusted to keep.

**The layout guarantee reaches only fields written here.** A field of the
same state whose text lives in a prose chapter cannot be made adjacent to its
group: `status_reason` sits in `## Reason`, several chapters away from `status` and
`status_at`, and the two regions merge independently. The format does not pretend
otherwise. What keeps the pair consistent is that no command writes one without the
other — `update --status --reason` writes both in a single operation, and there is
no command that sets a reason alone — so an inconsistent pair is reachable only by
hand-editing, and is a repair for `fsck` rather than a state the layout prevents.

### 3.4 Flattened records

A field whose value is a **record** is written as sibling attribute lines rather
than as one nested value, under a `FlatRecord` declaration (§5).

It has to be. The attributes chapter is one line per datum, and a record has no
data spelling (§3.2), so written whole it would land as a single backticked term
— which is exactly the one long line this format exists to break up. Flattening
is what lets an item's state be a `StatusChange` in the domain and four
independently mergeable lines on the page.

**The naming rule, and its one deliberate exception.** The record's **first**
declared field takes `prefix` as its whole name; every other field takes
`<prefix>_<field>`. So a `StatusChange(status, agent, at, reason)` under prefix
`status` writes `status`, `status_agent`, `status_at`, `status_reason`. The
exception is there because the first field is the record's **headline** — the
value the directory mirrors and §10 checks the path against — and `status_status`
is not a name anyone would write.

**Everything else sees a flat functor.** `Chapter`, `FieldGroup`, the value
spelling and the well-formedness checks are all written against the flattened
names and none of them knows a record is involved. That is the whole of what
flattening costs: one expansion, in one place.

A flattened name that collides with a field the functor already has is refused
(§5.1) — a shadowed field would be silently unwritable.

### 3.5 Omitted fields

A field absent from the chapter is absent from the fact; an `Option` field so
omitted is `none`. The writer omits every `Option` field whose value is `none`, and
omits any field whose text lives in a prose chapter (§4.2).

**An `Option` holding an EMPTY collection is also omitted**, and this one is a
deliberate narrowing rather than a restatement: `some([])` and `none` are different
values, and writing neither means the document cannot tell them apart. It is the
right trade here — an item with no dependencies and an item with an empty
dependency list are the same item — but it is the one place the encoding is not
value-preserving, so a domain that needs the distinction cannot use this rule.

## 4. Prose chapters

### 4.1 Structural levels

A **chapter** is a named region introduced by a heading at a structural level,
running to the next heading at that level or to end of file.

`DocumentFormat(level:)` declares the first structural level.

**THE RESERVED SET IS PER CHAPTER KIND, NOT PER DOCUMENT.** This is the rule
WI-1120 recorded as that increment's worst defect, and it must not be flattened
again: a writer that reserved `level + 1` everywhere refused text the reader
accepted, so a description carrying a `###` sub-section loaded fine, round-tripped
into the fact, and then made its item permanently **unwritable** — `claim` and
`update` failing on bytes already on disk.

| inside | reserved | everything deeper |
| --- | --- | --- |
| the document | `level` (`##`) — chapters and containers | — |
| a **field** chapter | `level` only | prose, carried verbatim, `###` included |
| a **container** | `level`, and `level + 1` (`###`) for its entries | — |
| an **entry** | `level + 1`, and the `level` above it | prose, carried verbatim |

So a field chapter reserves its own level; an entry reserves its own **and** the
container level above it. A `###` under `## Description` is **prose**, which is
what keeps a hand-added sub-section alive across a `claim` that rewrites the head
and renames the file.

**Concretely, at the `level: 2` this domain declares.** The rule above is stated in
terms of `level` because the level is a parameter; this is what it comes to for the
value actually in force, since a reader wanting to know whether `Description` is an
`h1` or an `h2` should not have to derive it.

| heading | at the top of the document | inside a field chapter | inside an entry |
| --- | --- | --- | --- |
| `#` | load error | load error | load error |
| `##` | `Attributes`, `Description`, `Reason`, `Changes` | ends the chapter — demoted on write | ends the entry — demoted on write |
| `###` | an entry, inside a container | **prose** | ends the entry — demoted on write |
| `####` and deeper | — | prose | prose |

So `Description` is an `h2` and a feedback entry is an `h3`. `#` is unused: the
hierarchy runs from `level` downwards and nothing above it has a meaning, so an
`h1` is refused rather than silently classified.

**`level: 2` is DECIDED, not defaulted.** Raising the structure by one —
`Description` becoming an `h1` — is the single fact `DocumentFormat(level: 1)`, and
it buys one more level of prose depth everywhere, which is worth most in a feedback
entry, where three authored heading levels already fit exactly with nothing to
spare. It was weighed and declined: an `h1` renders too large for a page carrying
three or four of them, and four levels of heading nesting inside one feedback entry
is rare enough not to pay for that. Recorded because the parameter is cheap to
change *now* and expensive later — every heading in every file shifts, so after the
migration it is a further full-tree rewrite.

A heading **above** `level` (`#`) is a load error wherever it appears: the
hierarchy is defined from `level` downwards and nothing above it has a meaning.

A heading marker inside a fenced code block is not a heading; the scanner tracks
fences (§4.4).

**Prose that arrives with its own headings is DEMOTED, not refused.** Text written
somewhere else — a design note, a pasted document, an agent that has never heard of
this format — carries a hierarchy starting at `#` or `##`, which collides with the
levels reserved here. The writer shifts the whole hierarchy down by the **minimum**
that puts its shallowest heading below the reserved set for the chapter it is
going into, and writes that.

**It applies to every prose body, and the shift is the CHAPTER's, not the
document's.** A feedback entry is prose exactly as a description is, and arrives the
same way — written elsewhere, pasted in by someone who has never heard of this
format. Its enclosing chapter reserves one level more (`level` and `level + 1`, so
`##` and `###`), so the same text demotes one step further:

    written              in a field chapter        in an entry
    # Overview      ->   ### Overview         ->   #### Overview
    ## The id       ->   #### The id          ->   ##### The id
    ### three parts ->   ##### three parts    ->   ###### three parts

Which is also where the depth budget is tightest: three authored levels fit an
entry exactly, with nothing to spare, while a description has one level in hand. A
fourth authored level overflows in an entry and is refused (see below), and fits in
a description.

Nothing is lost, and that is why this is normalisation rather than a silent
repair: the **relative** hierarchy is preserved exactly, and the absolute level of
a heading in text written standalone says where it was written, not anything about
the item. The shift is by one amount for the whole block, so sibling sections stay
siblings.

It is **idempotent**, which is what makes it safe to apply on every write: stored
prose has no collision, so writing it back shifts nothing. A round trip is
therefore identity from the second write onward, and the first write is the only
one that changes anything.

Two things it does not touch. A `#` inside a **fenced block** is not a heading and
is left exactly as written — the shift runs over the same fence-aware scan
everything else does. And a shift that would push a heading past level 6, where
markdown has no deeper heading, cannot be represented: that is refused, naming the
heading and the depth, because there is no correct answer rather than because the
format is being strict.

### 4.2 Field chapters

`Chapter(functor, field, named)` maps one prose field of the item's fact to one
chapter with a fixed heading. The field is absent from the attributes chapter, and
this chapter's body is its text.

**A mapped field is always a chapter, however short its text.** One spelling, so
nothing has to decide per value and nothing has two homes: `description` gets a
chapter when it is the single word `test`, and `status_reason` gets one for
19 characters as readily as for 1842. The alternative — short values inline, long
values in a chapter — is a threshold to pick, two shapes for one datum, and a
writer that changes a file's structure when prose grows.

```markdown
## Description

anthill-todo backend, INCREMENT 2c of WI-437 …
```

### 4.3 Containers and entries

`ChapterGroup(functor, container, kind, key, heading, field)` maps a satellite
fact repeated 0..n to **entries** inside a **container** chapter. Nothing about
these facts appears in the attributes chapter.

**Several groups may share one container.** `kind` is the word that says which
functor an entry belongs to, written in the entry's heading between the fields
`heading` names and the rest. A container holding one kind still writes it: one
spelling, and a second kind added later is then additive.

Each entry is self-contained:

- its **heading** is the fields of `heading` joined by ` — `, with `kind`
  inserted after the first — so `at`, then the kind, then `author`. `heading` must
  name at least one field, since "after the first" is otherwise undefined;
- its **body** is the fact's `field`;
- its `key` field is the item's id, taken from the **`id` attribute of this
  document's own fact** — never from the filename. The two normally agree, and §1
  makes the field the source when they do not; taking the key from the path would
  make a hand-renamed file silently re-attribute every entry in it, while the
  filename-versus-`id` check reported the rename as a separate and apparently
  harmless fault.

```markdown
## Changes

### 2026-08-17T09:19:35Z — feedback — user

id should be minted from content, not from a counter.

### 2026-08-18T15:28:04Z — status — claude

Delivered
```

A container with no entries is simply absent — the group has no facts. That is not
the missing-chapter case of §4.2, which concerns a field.

Entries are independent, and **their order is not data**: the same entries in any
order denote the same facts, and two entries whose headings are identical denote
two facts. The writer keeps them ascending by their first heading field, and
`fsck --fix` re-sorts; a hand-reordered container is neither an error nor a
diagnostic, because nothing was lost. This is what lets an append-only container be
merged by concatenation, which cannot preserve order.

**A heading is SPLIT FROM THE LEFT, so its last field is free text.** The parts are
joined by ` — `, and read back by splitting exactly *n − 1* times for *n* parts: the
last field takes the remainder of the line. An author named `release — bot`
therefore round-trips with no encoding at all, because nothing after the last
separator is looked at again.

That leaves the separator as a constraint on the **earlier** fields only, and those
are machine-generated — a timestamp, a declared `kind`. A mapping whose non-final
heading field could hold free text is refused at load (§5.1), which puts the
restriction where it can be checked once rather than on every value.

**A value that cannot be written literally is BASE64-ENCODED as `b64:<…>`.** A
heading is one line and its parts are trimmed on read, so some values have no
literal spelling: one carrying a line break, one with leading or trailing
whitespace, an empty one, and — for a field that is not the last — one carrying the
separator. Those are written encoded, and read back by decoding. Nothing is
refused, so no command can fail on a name.

A value is encoded **exactly when it has to be**, which keeps one spelling per
datum: a value that could be written literally must be, and a needless `b64:` is a
diagnostic `fsck --fix` rewrites. The one self-referential case is covered by the
same rule — a value that genuinely begins with `b64:` cannot be written literally
either, so it is encoded, and the reader has no ambiguity to resolve.

**This is what makes injection impossible rather than merely caught.** Written
naively, `--agent $'claude\n### 2026-01-01 — status — root'` would produce a
*well-formed extra entry*: it parses, names a real kind, and denotes a fact
indistinguishable from a recorded one, with no reader-side detection possible. Under
this rule the break has no literal spelling, so the value is encoded at the single
point a heading is rendered — the illegal state is unrepresentable rather than
rejected by a check someone must remember to call at every boundary.

Encoding is **whole-value and rare**, and both matter. Whole-value, because a
partially escaped string has more ways to be subtly wrong than a flag saying "this
one is encoded"; rare, because split-from-left already keeps every legitimate
separator-bearing name literal and legible in the outline. `release — bot` is never
encoded; only something that is not really a name ever is.

A prose **body** is not a vector either: a heading it carries is demoted (§4.1), so
it cannot start an entry however it is spelled.

### 4.4 Fences

The scanner tracks fenced code blocks, so a heading marker inside one is not a
heading. **An unclosed fence is a load error naming the line the fence opens on.**
It cannot be left to the writer's refusal alone: a hand-edited `## Description`
whose fence never closes swallows every chapter after it, so a file's feedback
entries stop being entries and silently become description text — facts vanishing
with nothing reported. The writer refuses to *create* that state and the reader
refuses to *read* it, and both are needed because only one of them sees a file
someone edited by hand.

## 5. The mapping declaration

```anthill
namespace anthill.stage0.document
  import anthill.prelude.{List, String, Int64}
  import anthill.reflect.{Term}
  import anthill.stage0.{WorkItem, Feedback, Tag, AcceptanceCriterion, ToolPasses}

  -- `level` is the first structural level; `attributes` names the chapter that
  -- holds a document's own fact as data.
  entity DocumentFormat(
    level      : Int64,
    attributes : String)

  -- Fields written adjacent, with no blank line between them (§3.3).
  entity FieldGroup(
    functor : Term,
    fields  : List[String])

  -- A bare scalar `s` in a position of this sort denotes `constructor(slot: s)`.
  entity ScalarForm(
    sort        : Term,
    constructor : Term,
    slot        : String)

  -- A prose field of the item's fact: one chapter, fixed name (§4.2).
  entity Chapter(
    functor : Term,
    field   : String,
    named   : String)

  -- A repeated satellite WITH prose: one container, one entry per fact (§4.3).
  entity ChapterGroup(
    functor   : Term,
    container : String,        -- several groups may share one
    kind      : String,        -- the word discriminating this group's entries
    key       : String,        -- the field taking the item's id
    heading   : List[String],  -- fields carried by the entry heading, in order
    field     : String)        -- the field carried by the entry body

  -- A repeated satellite WITHOUT prose: one attributes field holding a list, one
  -- fact per element (§3.1). An element writes `fields` in order, joined by `=`
  -- when there is more than one (§3.2.1).
  entity SatelliteList(
    functor : Term,
    named   : String,             -- the attributes field
    fields  : List[T = String],   -- the fields each element fills, in order
    key     : String)   -- the field taking the item's id (§4.3: from the fact)

  -- A RECORD-VALUED field written as SIBLING attribute lines (§3.4).
  entity FlatRecord(
    functor : Term,
    field   : String,   -- the record-valued field of `functor`
    prefix  : String)   -- the attribute name its FIRST field takes

  fact DocumentFormat(level: 2, attributes: "Attributes")

  fact FlatRecord(functor: WorkItem, field: "last_status_change", prefix: "status")

  fact FieldGroup(functor: WorkItem, fields: ["id", "created"])
  fact FieldGroup(functor: WorkItem, fields: ["status", "status_agent", "status_at"])

  fact ScalarForm(
    sort: AcceptanceCriterion, constructor: ToolPasses, slot: "tool")

  fact Chapter(functor: WorkItem, field: "description",   named: "Description")
  fact Chapter(functor: WorkItem, field: "status_reason", named: "Reason")

  fact ChapterGroup(
    functor: Feedback, container: "Changes", kind: "feedback",
    key: "workitem", heading: ["at", "author"], field: "content")

  fact SatelliteList(
    functor: Tag, named: "tags", fields: ["name"], key: "workitem")

  -- WI-1117, and declared beside the mirror rather than here: the entity and the
  -- line it is written on belong to the same feature.
  fact SatelliteList(
    functor: MirrorEntry, named: "mirrors",
    fields: ["target", "entry"], key: "workitem")
end
```

### 5.1 A well-formed mapping

The declaration is data, so it can be wrong. These are checked when it is read, and
a failure names the offending fact — a mapping that loads wrong silently produces
documents that lose data.

- **Every field of a mapped functor has exactly one home.** For a `ChapterGroup`,
  `key`, each name in `heading`, and `field` must be distinct and together cover
  every field of `functor`; for a `SatelliteList`, `key` and every name in
  `fields` must cover it.
  A field with no home is silently dropped on write — the failure this rule exists
  for, and the one a satellite gaining a field would otherwise meet. A field may be
  left uncovered only if the declaration gives it an explicit default.
- **No field has two homes.** A field named by a `Chapter` may not also appear in
  the attributes chapter, and no field may be named by two mappings. Two writable
  places for one datum is the failure the format's governing principle exists to
  prevent.
- **Names are unique.** No two chapters or containers share a name, and no two
  groups of one container share a `kind`.
- **Only the LAST heading field may hold free text.** A heading is split from the
  left (§4.3), so every earlier field must be one the separator cannot occur in — a
  timestamp, a declared `kind`. A mapping that puts free text before the last
  position is refused, which is where that restriction is checked; it is never
  checked per value.
- **`FieldGroup` names real attributes.** Every field it lists exists on `functor`,
  is written in the attributes chapter — not moved to a prose chapter — and appears
  in no other group.
- **The attributes functor is DERIVED, and must be unique.** It is the one
  functor named by a `Chapter`, a `FieldGroup` or a `FlatRecord` and by no
  `ChapterGroup` or `SatelliteList`: a satellite has a home of its own, and the
  item's own fact is what is left. A mapping naming none, or more than one, is
  refused rather than picking.
- **A flattened field must BE a record, and must not shadow.** `FlatRecord`'s
  `field` names a field whose type is a declared entity, and the names its
  expansion produces (§3.4) must not collide with a field `functor` already has.
- **A required field mapped to a chapter must have that chapter.** §4.2's missing
  chapter yields `none`, which is only correct for an `Option`; for a required field
  it is a load error naming the file and the chapter, not a fact carrying a fresh
  variable.

## 6. Example

`anthill-todo/delivered/WI-1121.anthill.md`, complete:

````markdown
## Attributes

- id: WI-1121
- created: 2026-08-17T08:43:54Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-18T15:28:04Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-1114

- tags: wi437

## Description

anthill-todo backend, INCREMENT 2c of WI-437: ALLOCATION IS A POLICY, and
ContentHash is the local one.

### the id has three parts

Hand-added prose below the structural level rides along inside its chapter.

## Changes

### 2026-08-17T09:19:35Z — feedback — user

id should be minted from content, not from a counter.

### 2026-08-18T15:27:52Z — feedback — claude

delivered; the counter seed in `main.rs` is gone.
````

The facts this file denotes:

```anthill
fact WorkItem(
  id: "WI-1121",
  created: "2026-08-17T08:43:54Z",
  description: some(value: "anthill-todo backend, INCREMENT 2c of WI-437: …"),
  acceptance: [ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")],
  depends_on: some(value: ["WI-1114"]),
  last_status_change: StatusChange(
    status: Delivered,
    agent: some(value: "claude"),
    at: some(value: "2026-08-18T15:28:04Z"),
    reason: none))

fact Tag(workitem: "WI-1121", name: "wi437")

fact Feedback(workitem: "WI-1121", author: "user",
  at: "2026-08-17T09:19:35Z",
  content: "id should be minted from content, not from a counter.")

fact Feedback(workitem: "WI-1121", author: "claude",
  at: "2026-08-18T15:27:52Z",
  content: "delivered; the counter seed in `main.rs` is gone.")
```

`context`, `generates` and `requires_capability` are absent, so they are `none`.

## 7. Faults

**A file with this suffix will be written by hand.** `.md` is chosen so GitHub
renders it, and anything a person can read a person can also author — so an agent
that has never seen this specification will generate an `.anthill.md`, and a human
will edit one. The fault model is built for that, not for files only this writer
produced.

**Every fault is REPORTED at load and listed by `fsck`.** Not one or the other:
nothing is silent, and nothing has to be tripped over to be found. What varies is
one thing only —

> a fault **blocks** when it makes the store's routing ambiguous, because the next
> write would have to guess. Everything else is reported and does not stand between
> the user and the tracker.

— and **blocking blocks WRITES, never reads**. The store is always built and the
tracker always opens, because `fsck` needs the store before it can say anything and
raising would take down the one command written to diagnose the problem. A file the
reader cannot make sense of costs that item, not the tracker: the other 1126 load,
`list` works, and `fsck` names what is wrong.

**Read as much as can be read, and never write it back.** A fault is scoped to the
smallest thing it makes ambiguous, and everything outside that scope loads
normally: a malformed entry heading costs that **entry**, not the item; a value
with no spelling costs that **field**, not the fact; a repeated key costs the one
field whose value is a guess. Only a fault that makes the item's *identity*
ambiguous — no attributes chapter, no `id` — costs the item, because there is then
nothing to attach the rest to.

That resilience is safe **only because a blocking fault refuses writes**, and the
two halves are one design rather than two. A partial read that could be written
back would silently delete the part that could not be read — the reader drops what
it could not parse, the writer re-renders from what it holds, and the difference is
gone. Blocking is what turns "read what you can" from data loss into a repair
opportunity: the file on disk keeps everything, the KB holds what was legible, and
`fsck` names the gap.

**And nothing is reconstructed by guessing.** Where content cannot be interpreted
it is reported as unread, not repaired by heuristic: an unclosed fence swallows the
rest of the file, and the reader says exactly that rather than deciding where the
author meant it to close. A guess that lands wrong is the one outcome worse than a
gap, because it looks like data.

Only one fault is global, and it is configuration rather than data: a mapping that
is not well-formed (§5.1). Nothing can load against a mapping that does not
describe a format.

**Where the loader is too permissive today**, and a hand-authored file is how it
shows: an omitted *required* attribute is filled with a fresh variable rather than
refused, everywhere, which is the pre-existing gap §5.5 recorded. A file someone
writes without `acceptance` therefore loads a `WorkItem` holding a free variable
instead of reporting that the field is missing. That is a fault (`blocking`), not a
silent fill.

| situation | response |
| --- | --- |
| text before the first chapter | fault, blocking |
| a heading above the first structural level | fault, blocking — names file and heading |
| the attributes chapter is missing | fault, blocking — the file is not an item |
| an attributes line that is not `- key: value` | fault, blocking — names file and line |
| a key repeated in the attributes chapter | fault, blocking — which value wins is a guess |
| a key naming neither a field of the functor nor a declared attributes field | fault, blocking — writing back would drop it |
| a value with no spelling for its declared type | fault, blocking — names file, field and value |
| an unterminated backtick value | fault, blocking |
| a prose chapter the mapping names is missing | `Option` field → `none`; a REQUIRED field is a fault, blocking — never a fresh variable |
| two chapters with one name, field not declared repeated | fault, blocking — which fills the field is a guess |
| a heading at a structural level the mapping does not account for in that scope | fault, blocking — it truncates a field; the writer demotes instead (§4.1) |
| a fenced code block opened in prose and never closed | fault, blocking — names the line the fence opens on (§4.4) |
| a status field combination no variant admits | fault, NON-blocking — the fact is well-typed and routing is unaffected; repair may need a human, since a missing agent is information |
| a mapping that is not well-formed | GLOBAL — nothing loads; names the offending fact (§5.1) |
| a `###` under a **field** chapter | prose, carried verbatim — not an error (§4.1) |
| a container the mapping names, holding no entries | not an error — the group has no facts |
| an entry heading with fewer ` — ` parts than `heading` declares | fault, blocking (more parts is fine: the last field takes the remainder, §4.3) |
| a `b64:` value that decodes to something writable literally | diagnostic; `fsck --fix` rewrites it literally (§4.3) |
| a `b64:` value that is not valid base64 | fault, blocking — names file, heading and field |
| an entry heading whose kind names no group of that container | fault, blocking — which functor it is would be a guess |
| an attributes value longer than 255 characters | diagnostic naming the field — a prose field wants declaring as a chapter (§4.2) |
| a field of a `FieldGroup` separated from its group by a blank line | diagnostic; `fsck --fix` rejoins it |
| attributes, filename and directory disagree | diagnostic; `fsck --fix` repairs from the attributes |

The writer still refuses prose it could not read back, but the set is now small.
A heading at a reserved level is **demoted** (§4.1) and a heading-field value with
no literal spelling is **encoded** (§4.3); neither is refused. What remains is prose
no shift can fix: an **unbalanced fence**, which would swallow every chapter after
it, and a heading that demotion would push **past level 6**. Both fail before the
file is written, so the command fails with nothing on disk.
