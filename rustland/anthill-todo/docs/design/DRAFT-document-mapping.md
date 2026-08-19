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

## 2. Document structure

A file is a sequence of **chapters**. One of them — named by
`DocumentFormat(attributes:)` — holds the item's own fact as data; the rest hold
prose.

```markdown
## Attributes                            ← the item's fact, as a bullet list

## Description                           ← a prose field of that fact

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

`key` matches `[a-z_][a-z0-9_]*` and names a field of the functor, or a head field
the mapping declares (§5). Everything after `: ` is the value, with leading and
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

### 3.3 Blank lines and field groups

A blank line separates every field line from the next, except that fields named
together in a `FieldGroup` are written **adjacent**, with no blank line between
them.

A group's fields describe one state that changes as a unit. Adjacency makes a
concurrent edit to two of them a merge conflict; a blank line makes two fields
independently mergeable. Fields that are never rewritten belong in a group for the
same reason — nothing can conflict over them.

### 3.4 Omitted fields

A field absent from the chapter is absent from the fact; an `Option` field so
omitted is `none`. The writer omits every `Option` field whose value is `none`, and
omits any field whose text lives in a prose chapter (§4.2).

## 4. Prose chapters

### 4.1 Structural levels

A **chapter** is a named region introduced by a heading at a structural level,
running to the next heading at that level or to end of file.

`DocumentFormat(level:)` declares the first structural level. There are two, and
they nest:

| level | carries |
| --- | --- |
| above `level` (`#`) | nothing — a load error |
| `level` (`##`) | the attributes chapter, prose chapters, and containers |
| `level + 1` (`###`) | a container's entries |
| deeper (`####`…) | prose, carried verbatim, never interpreted |

Structural levels are **reserved**: a heading at one belongs to the mapping, and
hand-written prose uses deeper levels. A heading marker inside a fenced code block
is not a heading; the scanner tracks fences.

### 4.2 Field chapters

`Chapter(functor, field, named)` maps one prose field of the item's fact to one
chapter with a fixed heading. The field is absent from the attributes chapter, and
this chapter's body is its text.

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

- its **heading** is the first field of `heading`, then `kind`, then the
  remaining fields of `heading`, joined by ` — `;
- its **body** is the fact's `field`;
- its `key` field is the item's id, taken from the file.

```markdown
## Changes

### 2026-08-17T09:19:35Z — feedback — user

id should be minted from content, not from a counter.

### 2026-08-18T15:28:04Z — status — claude

Delivered
```

Entries are independent: their order is the file's order, and two entries whose
headings are identical denote two facts. A container's entries are written in
ascending order of their first heading field.

An entry's body must not begin with a line the reader would take for a heading at a
structural level. The writer checks this before writing.

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
    key     : String)   -- the field taking the item's id

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
| a heading at a structural level the mapping does not account for in that scope | load error naming file and heading |
| a `###` outside any container | load error |
| an entry heading with the wrong number of ` — ` separated parts | load error |
| an entry heading whose kind names no group of that container | load error naming file, heading and kind |
| a field of a `FieldGroup` separated from its group by a blank line | diagnostic; `fsck --fix` rejoins it |
| attributes, filename and directory disagree | diagnostic; `fsck --fix` repairs from the attributes |

The writer refuses prose it could not read back — a heading at a reserved level, or
an unbalanced fence — before the file is written, so the command fails with nothing
on disk.
