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

### 3.3 Blank lines and field groups

A blank line separates every field line from the next, except that fields named
together in a `FieldGroup` are written **adjacent**, with no blank line between
them.

A group's fields describe one state that changes as a unit. Adjacency makes a
concurrent edit to two of them a merge conflict; a blank line makes two fields
independently mergeable. Fields that are never rewritten belong in a group for the
same reason — nothing can conflict over them.

**A flattened sum needs its invariant restated as constraints.** `status` and its
companions were one payload-carrying variant; as four independently optional fields
they admit `Claimed` with no agent, and `Open` carrying a stale rejection reason.
Those facts are well-typed, and `fsck` cannot repair the first — the missing agent
is information, not a formatting fault. So the invariant the sum type enforced by
construction is restated where the domain lives, as constraints, and a violation is
a **load error**:

```anthill
  -- Each status determines which companions it must have and must not.
  constraint claimed_names_its_agent :- WorkItem(status: Claimed, status_agent: none)
  constraint claimed_names_its_time  :- WorkItem(status: Claimed, status_at: none)
  constraint open_carries_no_reason  :- WorkItem(status: Open, status_reason: some(value: ?))
  -- …one pair per variant: Draft / PreOpened / Open carry none of the three;
  -- Claimed / Delivered carry agent and time; Verified carries time;
  -- Rejected / ProposalRejected / Stale carry time and reason.
```

This is check logic where the old encoding had unrepresentability, and that is a
real loss, taken deliberately for the reading the flat form buys. What makes it
acceptable is that the check is **declarative and total** — one constraint per
variant-companion pair, enforced at load over every item, not a rule the commands
are trusted to keep.

**The layout guarantee reaches only fields written here.** A field of the
same state whose text lives in a prose chapter cannot be made adjacent to its
group: `status_reason` sits in `## Reason`, several chapters away from `status` and
`status_at`, and the two regions merge independently. The format does not pretend
otherwise. What keeps the pair consistent is that no command writes one without the
other — `update --status --reason` writes both in a single operation, and there is
no command that sets a reason alone — so an inconsistent pair is reachable only by
hand-editing, and is a repair for `fsck` rather than a state the layout prevents.

### 3.4 Omitted fields

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

    written                    stored in a field chapter
    # Overview            ->   ### Overview
    ## The id             ->   #### The id
    ### three parts       ->   ##### three parts

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

The threshold is the chapter's, not the document's, so the same prose demotes
further inside an **entry** (reserved through `level + 1`) than inside a **field**
chapter (reserved at `level`).

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

**A heading-field value must be inert in a heading.** The parts are joined by a raw
` — ` and split by it on the way back, so a value containing that separator — an
author named `release — bot` — or containing a newline has no heading spelling and
does not round-trip. There is no escape: the writer **refuses** such a value
before persisting, naming the field and the value, the same way it refuses prose it
could not read back. A separator-bearing value is rare enough that refusing it
beats an escaping layer nobody would remember to apply.

An entry's body must not begin with a line the reader would take for a heading at a
structural level. The writer checks this before writing.

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
  -- fact per element (§3.1).
  entity SatelliteList(
    functor : Term,
    named   : String,   -- the attributes field
    field   : String,   -- the field each element fills
    key     : String)   -- the field taking the item's id (§4.3: from the fact)

  fact DocumentFormat(level: 2, attributes: "Attributes")

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
    functor: Tag, named: "tags", field: "name", key: "workitem")
end
```

### 5.1 A well-formed mapping

The declaration is data, so it can be wrong. These are checked when it is read, and
a failure names the offending fact — a mapping that loads wrong silently produces
documents that lose data.

- **Every field of a mapped functor has exactly one home.** For a `ChapterGroup`,
  `key`, each name in `heading`, and `field` must be distinct and together cover
  every field of `functor`; for a `SatelliteList`, `key` and `field` must cover it.
  A field with no home is silently dropped on write — the failure this rule exists
  for, and the one a satellite gaining a field would otherwise meet. A field may be
  left uncovered only if the declaration gives it an explicit default.
- **No field has two homes.** A field named by a `Chapter` may not also appear in
  the attributes chapter, and no field may be named by two mappings. Two writable
  places for one datum is the failure the format's governing principle exists to
  prevent.
- **Names are unique.** No two chapters or containers share a name, and no two
  groups of one container share a `kind`.
- **`FieldGroup` names real attributes.** Every field it lists exists on `functor`,
  is written in the attributes chapter — not moved to a prose chapter — and appears
  in no other group.
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
  status: Delivered,
  status_agent: some(value: "claude"),
  status_at: some(value: "2026-08-18T15:28:04Z"))

fact Tag(workitem: "WI-1121", name: "wi437")

fact Feedback(workitem: "WI-1121", author: "user",
  at: "2026-08-17T09:19:35Z",
  content: "id should be minted from content, not from a counter.")

fact Feedback(workitem: "WI-1121", author: "claude",
  at: "2026-08-18T15:27:52Z",
  content: "delivered; the counter seed in `main.rs` is gone.")
```

`context`, `generates` and `requires_capability` are absent, so they are `none`.

## 7. Load errors and diagnostics

| situation | response |
| --- | --- |
| text before the first chapter | load error |
| a heading above the first structural level | load error naming file and heading |
| the attributes chapter is missing | load error |
| an attributes line that is not `- key: value` | load error naming file and line |
| a key repeated in the attributes chapter | load error |
| a key naming neither a field of the functor nor a declared attributes field | load error |
| a value with no spelling for its declared type | load error naming file, field and value |
| an unterminated backtick value | load error |
| a prose chapter the mapping names is missing | `Option` field → `none` |
| two chapters with one name, field not declared repeated | load error |
| a heading at a structural level the mapping does not account for in that scope | load error naming file and heading — the reader's rule; the writer demotes instead (§4.1) |
| a fenced code block opened in prose and never closed | load error naming the line the fence opens on (§4.4) |
| a status field combination no variant admits | load error naming the item, the status and the offending companion (§3.3) |
| a mapping that is not well-formed | load error naming the offending fact (§5.1) |
| a `###` under a **field** chapter | prose, carried verbatim — not an error (§4.1) |
| a container the mapping names, holding no entries | not an error — the group has no facts |
| an entry heading with the wrong number of ` — ` separated parts | load error |
| an entry heading whose kind names no group of that container | load error naming file, heading and kind |
| an attributes value longer than 255 characters | diagnostic naming the field — a prose field wants declaring as a chapter (§4.2) |
| a field of a `FieldGroup` separated from its group by a blank line | diagnostic; `fsck --fix` rejoins it |
| attributes, filename and directory disagree | diagnostic; `fsck --fix` repairs from the attributes |

The writer still refuses prose it could not read back, but the set is now small.
A heading at a reserved level is **demoted** (§4.1), not refused. What remains is
prose no shift can fix: an **unbalanced fence**, which would swallow every chapter
after it, and a heading that demotion would push **past level 6**. Both fail before
the file is written, so the command fails with nothing on disk.
