# Pluggable backends: the GitHub-coordinated store

**Work item:** WI-437 — split 2026-08-16 into an umbrella plus seven increments,
WI-1113…WI-1119 (tag `wi437`), one per §14 row. WI-1119 (§5.3) was inserted after the
original six, between rows 2 and 3.
**Status:** design, amended 2026-08-16 (WI-1113)
**Supersedes:** `examples/github-todo/docs/pluggable-backend.md` (the original three-line sketch)

> **Amendment, 2026-08-16 (WI-1113).** Three things in the original draft were
> overtaken or misplaced, and are corrected throughout:
>
> 1. **Configuration.** The draft introduced `fact StoreBackend(kind: BackendKind)`.
>    WI-830 has since landed `fact ExtentBinding(store:, role:, covers:)` in the same
>    `project.anthill`, doing that job plus role and coverage. Two channels for one
>    datum is the failure §7's governing principle exists to prevent, so `StoreBackend`
>    is gone: **layout is named by the store term in the extent binding**, and only
>    coordination needs a fact of its own (§3).
> 2. **Forge-neutrality.** The draft spelled the choice as a variant literally named
>    `GithubCoordinated`, and the mirror link as `fact GithubIssue`. §8.3 already argued
>    the opposite — GitHub is *one implementation* of a contract — so the config
>    vocabulary now matches: the forge is a **parameter**, not a variant, and hosting a
>    non-GitHub forge costs one entity plus one carrier implementation.
> 3. **Where the new layout lives.** The draft added `FileConvention::StateDirs` and had
>    `IndexedFileStore` grow the §5.1 relocation rule. That grafts one store's semantics
>    onto another: `IndexedFileStore` exists for *many facts share a file, addressed by
>    byte offset*, and file-per-item is the opposite model. The layout is a **sibling
>    `Store` implementation** (`ItemPerFileStore`, §5.2), selected by the same extent
>    binding. `FileConvention` is untouched by this design.
>
> A fourth constraint is now stated explicitly, because it governs the increment order:
> `anthill-todo` is the tool tracking this work, so it must stay usable at every commit
> (§14).

## 1. The problem

`anthill-todo` keeps every fact in one file. This repo's tracker is
`anthill-todo/workitems.anthill` — 4658 lines and 5.1 MB as of 2026-08-16 (3675 lines
when this was written), holding every `WorkItem`, every `Feedback`, every `Tag`. That works perfectly for one developer and fails for
several, in two distinct ways:

1. **Textual conflict.** Every mutation — `add`, `claim`, `deliver`, `feedback` —
   rewrites or appends to the same file. Two developers working on two *unrelated*
   work items still collide in git, because their edits land in the same region of
   the same file. The conflict carries no information: it is an artifact of the
   storage layout, not a disagreement about the work.
2. **Id collision.** `next_id` allocates `WI-<max+1>` from the ids visible in the
   local checkout. Two developers who both run `add` before either pushes both mint
   `WI-690`, and the collision is only discovered at merge — by which time both ids
   are referenced from commits, branches, and other items' `depends_on`.

The second failure is the sharper one: a textual conflict is loud and mechanically
resolvable, while an id collision is a *semantic* corruption of a namespace that the
rest of the system treats as a primary key.

One property of today's tracker is a constraint on any fix: **it works with no
network at all**. Facts in a git checkout answer every query and accept every
mutation from a plane, a train, or a sandbox with no credentials. A design that
makes the most common command dial out before it can succeed has traded away
something real. This document is written not to make that trade (§6.4): every
command keeps working offline, and what the network buys — globally unique
permanent ids, the mirror — is *reconciled* when access returns rather than
demanded up front.

## 2. The framing: coordinated, not backed

There are (at least) two coherent ways to bring GitHub in, and this document
describes the second one.

**A GitHub-backed store** — work items *are* issues, and the store's `retrieve` /
`persist` / `retract` go to the issue API — is entirely buildable. The
`WorkItemStore` spec (§8.1) is a storage interface like any other, and nothing in it
presumes a filesystem; an impl whose `State` is a repo handle and whose facts are
reconstructed from issue bodies would satisfy it. That backend has real advantages —
no local layout at all, no migration, and every GitHub client becomes an editor — at
the cost of putting the tracker behind a network call and a service, and of encoding
work items in a format (issue bodies) that the KB has to parse back out. It remains
available as a future store implementation, declarable through the same extent binding
(§3); it is simply not what is designed here.

**A GitHub-coordinated store** — this design — keeps the facts in git and uses GitHub
only for the two jobs git cannot do:

> **git holds the truth. GitHub coordinates. Coordination is asynchronous.**
>
> Coordination means exactly two things:
> **(a)** GitHub issue creation — atomic, totally ordered by the issue counter —
> is the allocator for permanent work-item ids, and
> **(b)** GitHub issues are a *mirror* that makes the tracker visible where a
> team already looks — read-only in its mirrored state, with two deliberate
> return channels: comments come back as tracker feedback (§7.3), and closing
> a delivered item's issue verifies it (§7.4).
>
> And it is asynchronous: no command *waits* on GitHub to succeed. A checkout
> that cannot reach it keeps working — `add` falls back to a visibly
> provisional id (§6.4) — and `sync` reconciles when access returns.

Hence the name: `github-coordinated`, not `github`. Nothing in `anthill-todo`'s data
model moves into GitHub. An issue is a pointer to a file, plus a title you can read
without cloning the repo.

What this buys, relative to the backed variant, is that work items stay facts in the
knowledge base — the same substrate the workflow rules already reason over — stay
greppable, stay reviewable in a diff, and stay editable offline. What it costs is the
on-disk layout (§4) and a migration (§11). That trade is the reason for the choice;
it is a trade, not a refutation.

The layout change (§4) is what removes textual conflicts. The issue-creation
protocol (§6) is what removes id collisions. They are independent, and land in that
order.

## 3. Configuration: two facts, two questions

Configuration lives in `anthill-todo/project.anthill`, alongside the existing
`fact Project(...)`. It answers two independent questions, and each gets exactly one
writable home:

* **Where do the rows live, and in what layout?** → `fact ExtentBinding`, already the
  channel (WI-830). Its `store` field names the backend to build.
* **Who allocates ids, and where is the mirror?** → `fact Coordination`, below.

### 3.1 Layout: the extent binding

Today's tracker declares its layout like this, and this is real, committed
configuration — not a proposal:

```anthill
fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.IndexedFileStore(
    root: ".",
    convention: anthill.persistence.filesystem.FileConvention.single_file(
      file: "workitems.anthill")),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, StoreFormat])
```

Moving to the §4 layout replaces the *store term*, not the mechanism:

```anthill
fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.ItemPerFileStore(
    root: ".", status_field: "status", id_field: "id", ref_field: "workitem"),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, StoreFormat, MirrorEntry])
```

`store` is a **`Term`, not a `Store`** — the binding names a backend to *build*, and
the host maps it to one of its compiled-in backends (§8.2). Declarative configuration
chooses *among* the host's backends; it cannot introduce native code. A declared store
this build does not provide is a **hard refusal**, not a fallback.

### 3.2 Coordination: the forge is a parameter

```anthill
fact anthill.stage0.Coordination(
  forge:  GithubForge(repo: "rssh/anthill", project: some(value: "Anthill Roadmap")),
  access: ForgeAccess.enabled())
```

The entities live in the **bundled** `anthill.stage0` domain, in a new
`rustland/anthill-todo/anthill/coordination.anthill`:

```anthill
namespace anthill.stage0

  -- WHO allocates permanent ids and holds the mirror. `forge` is a Term, on the
  -- exact `ExtentBinding.store` precedent above: it names a forge to BUILD, written
  -- where no forge exists yet, and the host resolves it to one of its compiled-in
  -- carrier implementations. `Forge` (§8.3) is the algebra a built one satisfies,
  -- which is a different thing and one a config file cannot hold.
  entity Coordination(forge: Term, access: ForgeAccess)

  -- One entity per forge, carrying that forge's own parameters. Adding GitLab,
  -- Gitea, or a plain coordination service is ONE entity here plus ONE carrier
  -- implementation (§8.3) — never a new config variant for the model, because the
  -- model is the same and only the forge differs. This is what §8.3's substitution
  -- contract is FOR, and the draft's `GithubCoordinated` variant contradicted it.
  entity GithubForge(repo: String, project: Option[T = String])

  -- Whether to TALK to the forge at all: attempt allocation on `add`, push the
  -- mirror on `sync`. The fact is the project-wide DEFAULT; a single checkout
  -- overrides it with ANTHILL_TODO_GITHUB=on|off (or --offline) — CI test
  -- jobs, air-gapped machines, and fork checkouts without write access run
  -- off. `disabled` does not disable the tracker: every command still works,
  -- `add` allocates a provisional id (§6.4), and a later `sync` from an
  -- enabled checkout reconciles. What `disabled` removes is the synchronous
  -- attempt, never the work.
  enum ForgeAccess
    entity enabled
    entity disabled
  end

end
```

Bundling the entities (rather than expecting a per-project `domain.anthill`) follows
the `StoreFormat` precedent in `version.anthill`: a project's own domain may predate
the entity, and an unresolved import fails the *whole* bundle load — on exactly the
projects that most need the new code path. See WI-505/WI-684.

**Defaults.** An absent `Coordination` fact means an uncoordinated tracker: `next_id`
counts locally, exactly as today. An absent `ExtentBinding` already defaults to
today's single-file layout (WI-830's `default_binding`). So every existing project
keeps working untouched, with no migration and no new fact.

### 3.3 What the split costs, and why it is still right

The draft deliberately made the layout↔coordination pairing *unrepresentable*: one
enum, "two variants and not three", so that nobody could configure state directories
without coordination — directories alone fix conflicts but not id collisions. Two
facts give that up, and CLAUDE.md prefers unrepresentable states to checks, so this is
a real concession.

It is the right one, for two reasons. First, the draft's own coupling was already
leaky: §8.3 makes the mirror an injectable component precisely so tests can run the
directory layout against a *null* forge, which is the forbidden combination. Second,
fusing them is only achievable by putting the forge into the store term — and the
binding asserts that `store` *supplies the rows of every functor in `covers`*, which a
mirror explicitly does not do (§13: mirrored state is never read back). That would make
the declaration state something false, which is worse than checking something true.

So the coupling becomes a **loud load check**: a `Coordination` fact present alongside
a single-file store binding is refused at load, naming both facts. Uncoordinated
directories stay reachable — that is the test configuration — but they must be *asked*
for, not fallen into.

**The check reads the EFFECTIVE binding, after defaulting — not the written one.** An
absent `ExtentBinding` defaults to the single-file layout (WI-830's `default_binding`),
so a project declaring `Coordination` and *no* binding at all is the same
coordination-on-a-single-file configuration as one declaring both, and must be refused
the same way. Reading only the written fact would let the forbidden combination through
by omission — precisely the case a project migrating in is most likely to produce, since
it adds the coordination fact first and forgets the layout. Whatever answers "which
store am I using" must answer it post-default, and the check must ask that.

## 4. On-disk layout: a directory per state, a file per item

```
anthill-todo/
  project.anthill              fact Project(...) + fact ExtentBinding(...) + fact Coordination(...)
  draft/
  pre_opened/
  open/
    WI-690.anthill
    WI-691.anthill
  claimed/
    WI-688.anthill
  delivered/
  verified/
    WI-001.anthill
  rejected/
  proposal_rejected/
  stale/
```

Each item file holds **every fact about that item**. Shown here in plain `fact` syntax,
which is what the store writes until WI-1119 lands; §5.3 keeps this content and changes
its encoding to an anthill head plus markdown chapters, so the file names below become
`WI-NNN.anthill.md` (§5.4):

```anthill
-- anthill-todo/claimed/WI-688.anthill
fact WorkItem(
  id: "WI-688",
  description: some(value: "whole-`step` direct derivation ..."),
  acceptance: [ToolPasses(tool: "cargo-test", params: none)],
  depends_on: some(value: ["WI-686", "WI-687"]),
  status: Claimed(agent: "claude", since: "2026-07-10T09:12:44Z"))

fact MirrorEntry(workitem: "WI-688", entry: 1234)

fact Tag(workitem: "WI-688", name: "prover")

fact Feedback(workitem: "WI-688", author: "user",
  content: "both deferrals landed; substrate should suffice",
  at: "2026-07-10T11:02:10Z")
```

`MirrorEntry` is a new fact (in `coordination.anthill`, next to `Coordination`), keyed
on the work-item id — the same additive shape as `Tag`. It records the mirror link
*without* touching the `WorkItem` entity, so the stage0 domain stays backend-neutral
and an uncoordinated project never sees the field.

Its name and shape are **forge-neutral**: `entry` is the forge's own identifier for
the mirrored item — a GitHub issue number, a GitLab issue iid, whatever the substitute
uses. It is `Int64` because §6.1's soundness rests on identifiers *totally ordered by
creation*, and a counter is the only thing every candidate forge offers. A forge whose
identifiers are not numeric cannot back this protocol, which §8.3 states as a
requirement rather than discovering at runtime.

**Directory names are derived, not listed.** The directory for an item is the
snake_case of its status functor's short name — `Open` → `open/`,
`ProposalRejected` → `proposal_rejected/`. The store computes it with the same
`term_functor_name` reflection that `status_short` already uses in `store.anthill`.
There is no second list of statuses anywhere, so adding a `WorkStatus` variant cannot
drift out of sync with the layout.

**The directory is an index; the fact is the truth.** `Claimed(agent, since)` carries
a payload no directory name can hold, so the status field stays authoritative and the
directory is a coarse, greppable projection of it. That redundancy must be checked,
not assumed — see §10.

## 5. A state change is a file move

`claim WI-690` does two things:

1. rewrites the `status:` field inside the item's fact, and
2. moves `open/WI-690.anthill` → `claimed/WI-690.anthill`, **carrying the item's
   feedback and tags with it** — they live in the same file.

git sees a rename plus a small content edit, which is precisely what happened. Two
developers claiming two different items touch two different files: no conflict. Two
developers claiming the *same* item produce a rename/rename conflict: loud, and
correctly so, because they genuinely disagree.

### 5.1 How the store performs the move

The `WorkItemStore` spec (`store.anthill`) already has the right seam. `replace`
buffers a retract of the old fact and a persist of the new one, and flushes **once**:

```anthill
operation replace(s: Cell[V = WIS], target: String, new_wi: WorkItem) -> Unit
  effects {Modify[s], Error}
=
  let _ = forget_buffer(s, target)
  let _ = persist_buffer(s, as_term(new_wi))
  let _ = flush_backend(s)
  ()
```

Under `IndexedFileStore` both operations resolve to the same path and the flush
rewrites one block in place. Under `ItemPerFileStore` the retract and the persist
resolve to *different* paths — and that store recognizes exactly this pattern:

> **Relocation rule.** When one flush contains a retract and a persist of the same
> primary key whose file paths differ, it is executed as a **file move**: the source
> file is renamed to the destination path and the item's fact block is rewritten in
> place. Every other block in that file (feedback, tags, the `MirrorEntry` link)
> rides along untouched.

The unit of relocation is the *file*, not the fact. This is what makes "moving the
work item also moves its feedback" fall out of the existing single-flush atomicity
guarantee rather than needing a new spec operation: `replace` remains the only
mutation the CLI performs for a state change. Failures before the flush surface
through `Error` and leave nothing written. The flush itself is two filesystem steps
however you order them — write the new file, remove the old, each individually
atomic — so a crash *between* them can leave either a file whose directory disagrees
with its status fact or the item present in two files. Both are exactly the states
the §10 load checks name loudly, and `fsck --fix` repairs. Atomic in the error
model, loud in the crash model.

### 5.2 `ItemPerFileStore` is a second store, not a convention

**Amended 2026-08-16 (WI-1113).** The draft put this layout in
`FileConvention::StateDirs` and had `IndexedFileStore` grow the relocation rule above.
That is the wrong home, and the reason is visible in `IndexedFileStore`'s own fields
(`rustland/anthill-core/src/persistence/indexed_file_store.rs`):

```rust
inner: FileStore,                                 // append into shared files
source_map: HashMap<RuleId, (PathBuf, Span)>,     // byte range of each fact
pending_span_retracts: Vec<(PathBuf, Span)>,      // "flush drops the range from the file"
by_id: HashMap<String, RuleId>,
```

Every one of those exists for a single model: *many facts share a file, and a fact is
addressed by its byte offset within it*. File-per-item is the opposite model — one
file **is** one item, it is addressed by *path*, a state change **renames** it, and a
retract can mean deleting the file outright. None of the span machinery carries over,
and `fact_path` is content-blind while this routing is content-driven (the status field
picks the directory). A "convention" that shares no mechanism with its siblings is a
second store wearing the first one's name.

So `ItemPerFileStore` is a **sibling implementation of `Store`**, and the seam for that
already exists and is small: `pub trait Store`
(`rustland/anthill-core/src/persistence/mod.rs`) is six methods — `persist`, `retract`,
`update`, `flush`, `owned_monotonicity`, `retrieve` — with byte-range addressing
isolated in a separate `trait IndexedStore: Store` that `ItemPerFileStore` simply does
not implement. `FileConvention` keeps its own meaning untouched: the filename policy of
stores that append into shared files.

This is also what makes the §14 self-hosting constraint satisfiable. The two stores
**coexist**, selected per project by §3.1's binding, so this repo's own tracker stays
on `IndexedFileStore` while the new one is built and tested against fixtures. Had the
layout been a convention *inside* `IndexedFileStore`, every increment would have been
surgery on the store the tracker was running on at that moment.

### 5.3 The item file is a document: head + chapters (WI-1119)

**Added 2026-08-16; revised the same day after review falsified three of its rules.**
§4 writes each item as a block of `fact` declarations. That is the right *content* and
the wrong *encoding*, and the measurement on this repo's own tracker says so — 1110
`WorkItem`, 1129 `Feedback` and 281 `Tag` facts, of which the volume is prose:

| | count | avg chars | max chars |
| --- | --- | --- | --- |
| `WorkItem.description` | 1110 | 2107 | 20345 |
| `Feedback.content` | 1129 | 2116 | 19915 |

Together 4,729,493 of the file's 5,115,651 characters, and 4,744,325 of its 5,130,561
bytes: **92.5% of the tracker is prose inside string literals**, in either unit. (Counts
are per fact record, with string literals stripped before matching. A plain
`grep -c 'fact WorkItem('` returns three more, because ticket prose quotes fact syntax at
itself — a small illustration of the same problem. The encoding is not self-consistent
either: 344 descriptions are written bare and 766 as `some(value: "…")`, one datum two
ways in one file.)

The grammar has no multi-line string — `string_literal: /"([^"\\]|\\.)*"/`
(`tree-sitter-anthill/grammar.js`) — so every one of those documents is stored as **one
physical line of escaped text**. The longest line is 20,616 characters (20,711 bytes);
2153 lines exceed 500; 239 feedback entries carry an escaped quote and 274 an escaped
newline. The structured half is meanwhile thin and partly dead: `acceptance` is 92% the
single value `ToolPasses(cargo-test)` across just 12 distinct values, and `context`,
`generates` and `requires_capability` are each written exactly 709 times out of 1110 —
one long-form/short-form split, not three independent fields — always `none`. All three
`ContextRef` constructors, `FileRef` the supplied-file hook included, have **zero** uses.
A work item is already a document with a small structured head, encoded as a string
literal.

**The shape.** One item file is an anthill **head** followed by markdown **chapters**.
The head is anthill syntax, not YAML: there is no second scalar language, so
`status: Claimed(agent:, since:)` needs no encoding and the head remains the single
writable home for all structure. A declared mapping (§5.4) names which prose fields leave
the head and which chapter fills each; the store learns exactly one concept, *this
field's text is the chapter named N*, and never learns stage0's schema.

**Heading vs chapter — the two are not the same thing, and the difference is what the
whole format rests on.** A *heading* is markdown syntax: a line beginning with `#`,
`##`, `###`. A **chapter** is this design's unit of meaning: a named region of prose
that fills exactly one field of one fact. A chapter is *introduced by* a heading at the
reserved level and runs to the next heading at that level, or to end of file.

So every chapter begins with a heading, but **not every heading begins a chapter**. A
`###` inside a description is just a heading — ordinary markdown, part of that chapter's
text, carried verbatim. Only headings at the reserved level (§5.4 sets it) are chapter
boundaries, which is precisely why that level has to be reserved: if any heading could
start a chapter, a user's subsection would silently cut a field in half. ("Chapter"
rather than "section" only to keep it distinct from this document's own §-sections.)

**Eligible fields are `String` and `Option[T = String]`.** Both, not just the first —
`Feedback.content` is a bare `String` but `WorkItem.description` is
`Option[T = String]` (`domain.anthill`), and a rule admitting only bare `String` would
exclude the very field this section exists for. The `Option` case is what the missing-
chapter row below describes: absent chapter, `none`.

**Where the mapping lives:** bundled with the stage0 domain, beside `Coordination`'s
entities and on the same `StoreFormat` precedent (§3.2) — **not** in `project.anthill`.
It is a property of the *schema*, not of the project, so §3 remains "two facts, two
questions" and §11 step 3 has nothing new to write.

**Out of scope, deliberately:** rendering payload-carrying variants as sections. It
would mean re-inventing term syntax in a second language.

**Feedback** is the interesting case — repeated 0..n, so several chapters mapping to one
field is *correct* here and the mapping must declare repetition.

The chapter name is the machine's key, and its only requirement is **uniqueness within
the file**. It is *derived* from the entry's timestamp for readability, with a
deterministic disambiguating suffix when that collides — because the timestamp alone is
**not** unique, measurably: `WI-599` carries two `Feedback` facts with identical `at`
*and* identical `author` (one collision in 1129 entries, but a one-time migration meets
it on real data). Worth recording as a finding about existing design, not only about this
one: §7.3 dedups ingested comments on `(workitem, author, at)`, and that key is not
unique on the data the tracker already holds.

Everything after the name in a heading — author, human-readable date — is **decoration**:
regenerated from the head, and **checked against it at load**, a mismatch being a loud
diagnostic that `fsck --fix` repairs. That is deliberately the same treatment §4 gives
the directory name, "a coarse, greppable projection" of the status fact checked in §10 —
including the loudness. A projection that were regenerated *without* being read would be
silently overwritten when a user corrected it by hand, which is the silent drop this
repo's conventions rule out.

Feedback is also **append-only** — 21 subcommands, `feedback` adds one, and nothing edits
or deletes an entry — so the store never re-serializes the 1129 feedback chapters. That
is a correctness property, not a volume one: feedback is 50.5% of the prose and
descriptions the other 49.5%, so the half that *is* rewritten is the same size. The
precise claim is the useful one — the only prose the store ever rewrites is a single
`description` chapter, via `update`.

**Chapter level is reserved.** Headings at the declared level belong to the mapping;
prose uses deeper levels. This is what closes the hole a first draft of this section
left open: with unreferenced chapters simply "legal", a user who typed a level-N heading
mid-description would end that chapter there, silently truncating the field, and the
tail would reappear as an innocuous-looking unreferenced chapter. So an unreferenced
heading at the reserved level is an **error**, and hand-added material lives *inside* a
chapter at a deeper level, where it rides along as part of that chapter's text.

**Malformed editing.** A format people hand-edit must say what it does with each way
they can get it wrong:

| situation | response |
| --- | --- |
| chapter the mapping names is missing | `Option` field → `none`; otherwise **load error** naming file and expected chapter |
| two chapters with one name, field not declared repeated | **load error** — `update` could not know which to rewrite |
| heading at the reserved level the mapping does not account for | **load error** naming file and heading — this is the truncation case, and it must not look like a note |
| heading below the reserved level | prose belonging to the enclosing chapter, carried verbatim, never interpreted |
| unknown key in the head | **load error**; the head is the machine's region |
| a heading marker inside a fenced code block | not a heading — the scanner must track fences |
| heading decoration disagrees with the head | loud diagnostic + `fsck --fix`, as for §4's directory name |
| head, filename and directory disagree | directory-vs-status is §10's existing check; **filename-vs-id is a new one this increment adds** — §10 does not have it today |

Row four is what keeps notes alive, and it holds only as a **tested invariant**:
hand-add a sub-section inside a description, run `claim` (which rewrites the head *and*
renames the file), assert the sub-section survives byte-identical. That test fails the
day the store starts reserializing a whole file from facts — the one failure mode that
would quietly eat a user's notes.

**§5.1's relocation rule needs one sentence more under this encoding.** It says the move
"rewrites the item's fact block in place"; here there is no fact block. `replace`
receives a whole `WorkItem` term, so the store must split it into head fields and chapter
fields, rewrite only the head and the chapters whose text actually changed, and leave
every other chapter byte-identical. Both the opacity invariant above and "never
re-serializes the feedback chapters" rest on that split, so it is part of the store's
contract rather than an implementation choice.

The fenced-code hazard is prospective but not impossible today: 392 descriptions and 240
feedback entries already contain backticks, and although no prose currently holds a fence
or a `#` heading, both *are* writable in a one-line literal (three backticks are
literal characters; `\n#` is an escape away — 274 entries already carry escaped
newlines). So migration must run the fence-aware scanner over all 2239 existing prose
bodies rather than assume pre-migration content is fence-free.

**Why its own increment.** No markdown dependency is needed — we never *render*
markdown, GitHub does; we find headings at the reserved level while tracking fences. The
`.anthill` glob is not the reason to split this out: `collect_files_recursive` takes its
extension list as a parameter (`anthill-core/src/fs_util.rs`) and `anthill-todo` supplies
`&["anthill"]` at its one call site, so widening it is a caller-side one-literal change.
What is genuinely `anthill-core` surface is the **reader** — parsing a head-plus-chapters
document into facts. The real reason to keep it separate from WI-1114 is §14.1: bundled,
a bug in the format would mask a bug in the store, on the tracker we are running on. It
depends on WI-1114 and blocks WI-1118, because the live tracker migrates **exactly once**
and must migrate into the final format.

### 5.4 The mapping, concretely

§5.3 states the rules; this is the artifact. Both halves are shown for the same item
§4 writes in fact syntax, so the two encodings can be read against each other.

**File name: `WI-NNN.anthill.md`.** The trailing `.md` is what makes editors and
GitHub render it; the `.anthill` before it makes an item file self-identifying, so a
`README.md` sitting in the same tree is not mistaken for one. This is a **suffix**
test, not an extension test — `Path::extension()` returns `md` for
`WI-690.anthill.md`, so `fs_util::has_extension` cannot express it and the loader
needs `ends_with`. A plain `.md` glob would sweep in every ordinary markdown file
under the project directory.

**The head is a fenced block with the `anthill` info string.** No new delimiter
syntax: markdown already has one, GitHub renders it highlighted, and it composes with
the fence tracking §5.3 requires anyway. The head is the file's first such block.

**A chapter-bearing field is simply absent from the head** — no marker in the fact,
nothing to keep in sync. The mapping is what says where it comes from:

```anthill
namespace anthill.stage0.document

  -- Headings at this level belong to the mapping (§5.3); prose uses deeper ones.
  fact DocumentFormat(level: 2)

  enum ChapterName
    entity fixed(name: String)        -- one chapter, this literal name
    entity from_field(field: String)  -- one per fact, named by that field's value
  end

  -- One fact per prose field that leaves the head.
  entity Chapter(
    functor  : Term,               -- the fact the field belongs to
    field    : String,             -- the field whose text moves out
    named    : ChapterName,
    decorate : List[T = String],   -- head fields regenerated into the heading
    repeated : Bool)

  fact Chapter(
    functor: WorkItem, field: "description",
    named: fixed(name: "description"),
    decorate: [], repeated: false)

  fact Chapter(
    functor: Feedback, field: "content",
    named: from_field(field: "at"),
    decorate: ["author"], repeated: true)
end
```

`Tag` and `MirrorEntry` need no `Chapter` fact: they carry no prose and stay in the
head as ordinary facts.

**Worked example — `anthill-todo/claimed/WI-688.anthill.md`:**

````markdown
```anthill
fact WorkItem(
  id: "WI-688",
  acceptance: [ToolPasses(tool: "cargo-test", params: none)],
  depends_on: some(value: ["WI-686", "WI-687"]),
  status: Claimed(agent: "claude", since: "2026-07-10T09:12:44Z"))

fact Tag(workitem: "WI-688", name: "prover")
fact MirrorEntry(workitem: "WI-688", entry: 1234)

fact Feedback(workitem: "WI-688", author: "user", at: "2026-07-10T11:02:10Z")
```

## description

whole-`step` direct derivation — the rewriter should reach the normal form
without the intermediate `unfold` pass.

### why the intermediate pass exists

Hand-added prose lives at a deeper level and rides along inside its chapter,
untouched by `claim`, `deliver` or a state change (§5.3).

## 2026-07-10T11:02:10Z — user

both deferrals landed; substrate should suffice.
````

Read against §4's fact block: `description` and `content` are gone from the facts and
are now chapters; everything else is unchanged. `WorkItem.description` is filled from
the chapter `fixed("description")`; the `Feedback` fact is filled from the chapter
named by its own `at`, and `— user` after the name is `decorate: ["author"]` —
regenerated, and checked at load (§5.3).

**Name collisions get an ordinal.** `from_field` is not injective — `WI-599` holds two
`Feedback` facts with identical `at` *and* `author` (§5.3) — so the second and later
chapters with one derived name take a `.2`, `.3` suffix in document order, and the
reader checks that the number of facts keyed *K* equals the number of chapters named
*K*, *K*.2, …. Deterministic on write, verifiable on read, and no domain field has to
be added to carry an identity the data does not have.

## 6. Id allocation: the issue *is* the allocation

Under a declared `Coordination`, **permanent ids come only from GitHub**, and issue
creation is the allocation event. GitHub's issue counter is a monotone,
atomically-incremented, globally-visible sequence — exactly the shared resource
git lacks. `add` itself never *waits* on GitHub, though: when the network or a
token is missing it allocates a *provisional* id and `sync` finishes the naming
later (§6.4). What is forbidden is only the §1 failure: minting a dense `WI-<n>`
from local state alone.

The direct mapping *id := `WI-<issue number>`* would be simpler, and is right for a
fresh project whose tracker owns the repo's counter from issue #1. It does not fit an
existing one: GitHub shares one counter between issues and pull requests, and this
repo already holds ~1110 dense ids that would collide with the first ~1110 fresh issue
numbers. So the issue **allocates**, its number **orders** competing claims (§6.1),
and neither **names**: the id in the title does.

### 6.1 The protocol: stake by creation

The set of issues whose title starts `WI-<n>:` is the authoritative id registry —
the working tree may be stale or shallow, but the issue list is not. Two ground
rules about reading it:

* **A claim is a title prefix, parsed strictly.** An issue claims id `n` iff its
  title matches `^WI-<n>:`. A summary that merely *mentions* another item
  ("WI-703: fix the WI-702 regression") claims only 703. Claim-parsing is
  client-side; no search-syntax subtlety participates in correctness.
* **Registry reads use the issues *list* endpoint, newest-first, open AND closed**
  (`gh issue list --state all --limit 30 --json number,title` — `--state all`
  because terminal items' mirrors are closed (§7.1) and still hold their ids).
  The list reflects live data; GitHub's *search* index is the
  eventually-consistent component — lag can be tens of seconds — and is used
  only where staleness is provably harmless (below).

And one rule about writing it, which is the heart of the protocol:

> **A claim is staked by *creating* the issue already titled with the id.**
> Issue creation is the one atomic, totally-ordered primitive GitHub offers —
> numbers are assigned in creation order — so among competing claims to the
> same id, "lowest issue number wins" is decided the moment the second issue
> exists, and every participant reads the decision the same way.

There is no placeholder state and no retitle-to-stake. (An earlier draft staked
by creating a `WI-?` issue and retitling it onto the candidate. That shape has an
unfixable interleaving: retitles are neither ordered by issue number nor forced
to precede a competitor's check, so writer A — issue #10 — can stake `WI-701`,
check, see nobody, and commit; then writer B — issue #9, created earlier but
slower — stakes the same id and *keeps* it, because "lowest number wins" tells B
that #10 loses. Both keep. No tiebreak repairs a check-once race whose stakes are
unordered; staking by creation makes the stakes themselves the ordered events.)

Every step below is tagged with the `Forge` operation (§8.3) it invokes;
`[github]` steps are network calls, `[local]` steps touch only the working tree.

```
add(description):

  ── allocate ──────────────────────────────────────────────────────────────────
  1. [github]  Forge.recent_entries(limit: 30)   -- list endpoint, newest-first,
     [local]   candidate := max( ids claimed in that page         open AND closed
                                 ∪ ids of local item files ) + 1
  2. [github]  Forge.create_entry("WI-<candidate>: <summary>", body: "(allocating)")
                                                       → issue #N    [atomic stake]
  3. [github]  claims := Forge.recent_entries(limit: 30)
                       ∪ Forge.entries_titled("WI-<candidate>:")
     [local]   if any issue #M < N claims candidate:          -- we lost the race
                   [github] Forge.retreat(N)     -- retitle off the id + close
                   candidate := max( ids in claims
                                     ∪ ids of local item files ) + 1;  goto 2
                                                                [claim committed]

  ── write (git is the truth; after this the item exists) ───────────────────────
  4. [local]   write anthill-todo/open/WI-<candidate>.anthill, containing
                   fact WorkItem(id: "WI-<candidate>", …, status: Open)
                   fact MirrorEntry(workitem: "WI-<candidate>", entry: N)
                   fact Tag(…) for each --tag

  ── reconcile (best-effort; `sync` redoes it) ─────────────────────────────────
  5. [github]  Forge.set_body(N, <pointer to the file, §7.1>)
     [github]  Forge.add_to_board(N, <the forge's configured board>) -- if configured
```

**Cost: three small calls on the happy path, none of them O(repo).** Step 1 is one
page from the list endpoint; step 3 re-reads that page and adds one exact-title
search; step 2 is `gh issue create`. The GitHub-backed `Forge` carrier (§8.3)
shells out to `gh`, so it inherits the user's existing auth and we hold no token
of our own.

**Why "lowest issue number wins" is sound here.** The winner of an id is the
lowest-numbered issue ever to claim it, and it never retreats — no lower claim
exists for it to see. Every loser finds out: its check (step 3) runs after its own
creation, which — numbers being creation-ordered — is after the winner's creation,
and a creation that has happened is visible. Two writers cannot both keep an id,
and all cannot retreat (the lowest doesn't). A lost race costs one extra round
trip and one burnt issue number, and only an actual collision pays it.

**Why step 3's two reads cover each other's blind spot.** A *recent* competitor —
the actual race — is by construction in the newest page, and the list endpoint
reads live data, so the search index's lag cannot hide it. A *stalled* competitor —
an issue created long ago whose claim sits outside the page — has by the same
token existed long enough to be search-indexed, so the exact-title search sees it.
The one claimant neither read shows would be both old and unindexed, which is not
a state a claim occupies for long; the loud duplicate-id check at load (§10) is
the backstop, not the mechanism.

**Why the page is a sound bound but not the mechanism.** A stale checkout — say
fifty items behind — still lands on a fresh candidate, because ids allocated after
the ones in its tree belong to newer issues, and the newest issues are exactly
what step 1 reads. The limit of 30 is slack: non-tracker issues interleave (PRs do
not appear in the issue list at all), and when the page under-reads anyway the
worst case is a candidate that is already taken — which step 3 catches, because
step 3 is the correctness mechanism.

The bands have different failure semantics. **Steps 1–3 either complete or `add`
falls back to a provisional id (§6.4)** — never to a locally-minted permanent
one — and an issue stranded by a mid-protocol failure is the dangling case of
§6.3. **Step 4 is the commit point** — once the file is written the item exists,
and git is its truth. **Step 5 is reconciliation**, not part of the transaction:
it is the same code `sync` runs, it is idempotent, and if it fails the item is
still correctly stored and correctly allocated — the next `sync` sets the body.

The full listing does still happen — in `sync` (§7.2), which is a batch
reconciliation run from CI or a hook, exactly where an O(repo) scan belongs. It
stays off the path of `add`.

### 6.2 Allocation becomes an explicit store operation

The GitHub calls are not a new layer bolted beside the store. They are the
`github-coordinated` **bodies of the store operations the CLI already invokes** — which
is the whole point of selecting through the `WorkItemStore` spec: `do_add` cannot tell
which backend it is talking to, and nothing above the store changes.

But the spec's allocation operation, as it stands, cannot host them:

```anthill
operation next_id(s: Cell[V = State]) -> String      -- today
  effects Modify[s]
```

Two things are wrong with it for a coordinated backend, and both point the same way.

1. **It has no summary to allocate with.** Step 2 mints an issue whose title carries the
   id and a short summary; `next_id(s)` never sees the description, so a coordinated
   body simply cannot be written against this signature.
2. **The name is the file backend's implementation, not the contract.** "next id" says
   *bump a counter*. The contract the CLI actually needs is *allocate an id that is
   globally unique, doing whatever coordination that requires* — which is a counter bump
   in one backend and an optimistic, retried stake in another.

So the spec grows an explicit allocation API, replacing `next_id`:

```anthill
    -- Allocate a fresh work-item id, unique across every writer of this
    -- store. `summary` is the short human label the allocation may need to
    -- publish (the coordinated backend mints its issue title from it); the
    -- file backend ignores it. The coordinated backend returns a PERMANENT
    -- id when GitHub is reachable and a PROVISIONAL one (§6.4) when it is
    -- not. External/Error are declared HERE, at the spec, so a coordinated
    -- impl REFINES the row rather than widening it (WI-347) — the same
    -- reason the read ops already declare `Error`. External (proposal 054,
    -- WI-698) is the generic outside-world effect; WHICH outside world is
    -- the Forge carrier's business (§8.3), not the row's.
    operation alloc_id(s: Cell[V = State], summary: String) -> String
      effects {Modify[s], External, Error}
```

| protocol | spec operation | file-backed impl | github-coordinated impl |
| --- | --- | --- | --- |
| steps 1–3 | `alloc_id(s, summary)` | ignores `summary`; reads and bumps the local counter | reads the registry, stakes the claim by creating the issue, retreats and retries on a lost race; mints a provisional id when GitHub is out of reach (§6.4) |
| step 4 | `commit(s, w)` | persist + flush | persist + flush into `<state>/<id>.anthill`, plus the `MirrorEntry` fact when the allocation produced one |
| step 5 | `commit(s, w)`, tail | — | `set_body` + `add_to_board`, best-effort |

There are two allocation sites — `do_add`, and the `--before` insertion path
(`main.anthill:1904`), which allocates and then rewrites the insertion target's
`depends_on` — and each changes by exactly one line:

```anthill
operation do_add(s: Cell[State], description: String, …) -> Int64 =
  let id = WorkItemStore.alloc_id(s, description)     -- was: next_id(s)
  let _  = WorkItemStore.commit(s, WorkItem(id: id, …, status: Open()))
  let _  = apply_tags(s, id, tags)
  …
```

(`do_add` additionally prints the sync hint when the id it gets back is provisional
(§6.4) — the one place the namespace split surfaces above the store.)

**The issue number does not appear in the spec.** `commit` must write
`fact MirrorEntry(workitem: id, entry: N)` for a freshly allocated permanent id, but
`N` is a GitHub concept and the spec is backend-neutral. It rides in the store's own
`State` instead: the coordinated impl's `alloc_id` stashes the pending
`(id, issue number)` in the cell, and its `commit` reads it back out — persisting the
`MirrorEntry` fact in the *same flush* as the item, so the two land in the item's
file together or not at all. When no pair is pending — a provisional allocation —
`commit` writes just the item, which is precisely the unreconciled state `sync`
later converts (§6.4). The file backend's `State` (`WIS`) has no such field, and the
`WorkItemStore` interface never learns that GitHub exists. This is exactly what the
`Cell[V = State]` threading is for.

Widening the effect row is the one unavoidable edit to the shared spec, and it is the
established move: `store.anthill` already declares `Error` on the read operations for
precisely this reason ("declared here so a concrete impl's `effects Error` refines
rather than widens the spec (WI-347)"). `External` joins it on `alloc_id` and `commit`.

### 6.3 What can go wrong, and what fixes it

A crash between steps 2 and 4 leaves an issue claiming an id with no file: a
*dangling allocation*. `sync` (§7.2) reports it and offers to recreate the file from
the issue or release the id — retitle the issue off the claim and close it.
Releasing is safe: a released id below the current max is never minted again
(candidates only grow), and a released id at the max gets re-minted for an item
that never existed; either way no file ever carried it. A crash between 4 and 5
leaves the item correctly stored and correctly allocated, with an unset body: the
next `sync` sets it. A crash between losing a race and retreating leaves a stray
claim on an id someone else committed — harmless to allocation (that id is below
max forever after) and reported by `sync`, which completes the retreat. All of
these are visible; none is silent.

With registry reads on the list endpoint, the residual inconsistency window is
read-replica lag — milliseconds, not the search index's seconds — and a collision
that threads it produces two files with the same id, caught by the loud
duplicate-id check at load (§10). The backstop exists; the design does not lean
on it.

### 6.4 Autonomous mode: provisional ids, reconciled by `sync`

The tracker must keep working with no GitHub at all — no network, no token, a fork
checkout without write access, a CI sandbox. Every command except `add` already
does: a state change is a git operation (§5), and the mirror is asynchronous by
design (§7.2). For `add`, the rule is:

> **Offline, `add` allocates from a different namespace, visibly.** A provisional
> id is `WI-t<6 hex digits>` — `WI-t9f3a2c` — minted from host entropy, never from
> a counter. It cannot collide with a permanent id (it is not numeric), it cannot
> plausibly collide with another checkout's provisional id (16.7M values, and even
> that collision is an add/add conflict on one filename — loud), and it cannot be
> mistaken for what it is not: the form is the notice.

This is not the fallback §10 forbids. The forbidden fallback mints a *dense* id
from local state — reproducing exactly the collision this design exists to remove,
distinguishable from a real allocation only at merge time. A provisional id is
loud by construction, excluded from the candidate computation by shape (`max`
parses `^WI-(\d+)$` and skips everything else — by design, not by accident), and
announces its own remedy: `add` prints
`added: WI-t9f3a2c (provisional — run 'anthill-todo sync' when GitHub is reachable)`.
Only unreachability and missing auth downgrade to provisional; a malformed or
unexpected GitHub response stays an error (§10).

A provisional item is a full citizen. Its file lives in the state directories like
any other, moves on `claim`/`deliver`, carries feedback and tags, appears in
`list` and `graph`, and other items may name it in `depends_on`. The only things
it lacks are a mirror issue and a permanent name.

**Reconciliation** is the first phase of `sync` (§7.2), per item, oldest first:

1. Run the §6.1 allocation with the item's summary → permanent id, issue `#N`.
2. Rewrite the item's file: the `id:` field, the `workitem:` fields of its own
   `Feedback`/`Tag` facts (they live in the same file), a new `MirrorEntry`
   fact — and rename the file to the new id, in the same state directory
   (reconciliation never changes status).
3. Rewrite every in-tree reference: other items' `depends_on` entries.
4. The ordinary mirror push (§7.2) then sets the issue body as usual.

Conversion is idempotent and resumable. A crash mid-way leaves either the
provisional file untouched (the next `sync` redoes it) or a renamed file plus
stale `depends_on` references to a `WI-t…` with no file — a dangling reference
`fsck` names loudly and a `sync` re-run repairs. Two checkouts reconciling the
*same* provisional item mint two permanent ids for it and meet as a rename/rename
conflict in git — loud, and the disagreement is real; the loser retreats its
issue, the same move as a lost §6.1 race.

**The honest cost:** references *outside* the tracker do not reconcile. A
provisional id burned into a commit message or a branch name stays there after
the rename — working offline defers naming, and a name mentioned before it is
permanent may not last. Two mitigations: reconcile before you start referencing
(the `add` notice says exactly this), and `sync --check` flags any provisional id
that reaches `main`, so the team chooses its policy — gate merges on
reconciliation, or let a token-holding CI reconcile after merge.

## 7. The mirror

### 7.1 Issue content

* **Title:** `WI-690: <short summary>` — the first line, or first ~80 characters, of
  the description. The leading `WI-<n>:` prefix is the id claim of §6.1, so it is
  load-bearing: `sync` may rewrite the summary half, never the prefix.
* **Body:** a pointer to the file, and nothing else of substance:

  ```
  Tracked in [`anthill-todo/open/WI-690.anthill.md`](https://github.com/rssh/anthill/blob/main/anthill-todo/open/WI-690.anthill.md).

  Status: Open · Depends on: WI-686, WI-687 · Tags: prover

  This issue is a **mirror**. The work item lives in the repository and is
  edited with `anthill-todo`; edits made here are not read back — but
  comments are: `sync` ingests them as tracker feedback.
  ```

  The path in the pointer changes on every state transition, which is precisely why
  the body is regenerated by `sync` rather than written once.
* **State:** the issue is open while the item is, and closed on `Verified`,
  `Rejected`, `ProposalRejected`, and `Stale`.
* **Labels** (optional, config-gated): `status:claimed`, and one label per tag.

### 7.2 Sync is reconciliation, not write-through

Only `add` talks to GitHub synchronously — and even it only *opportunistically*
(§6.4). Everything else (`claim`, `deliver`, `feedback`, `tag`, …) is a purely local
git operation, and the mirror catches up afterwards:

```bash
anthill-todo sync          # reconcile + push local state → issues; report drift
anthill-todo sync --check  # report drift, change nothing (CI gate)
```

`sync` does five jobs, in order:

1. **Reconcile provisional ids** (§6.4): allocate permanent ids for `WI-t…` items,
   rename their files, rewrite references.
2. **Repair allocation debris** (§6.3): dangling allocations (an issue with no
   file — offer recreate-or-release) and unfinished retreats from lost races.
3. **Ingest the return channels** (§7.3–§7.4): new comments on mirror issues
   become `Feedback` facts in their items' files, and a close of a `Delivered`
   item's issue becomes its `verify`. After reconciliation, so ingested feedback
   lands under permanent ids; before the push, so gestures are read before the
   mirror is re-derived.
4. **Push the mirror**: derive every mirror issue's desired title, body,
   open/closed state, and labels from the facts in the tree, and edit whatever
   differs.
5. **Tombstone deletions**: an issue whose item was deleted (`forget`) is closed,
   labelled `deleted`, and its summary marked — `WI-701: [deleted] <summary>`.
   The `WI-<n>:` prefix stays, deliberately: the id remains claimed in the
   registry and is never minted again — an id that once named a real item stays
   burnt, unlike a §6.3 release, which is safe only because no file ever carried
   the id. The marker is what distinguishes a tombstone from a dangling
   allocation in `sync`'s report.

`sync` is **idempotent** and derives the entire desired issue state from the facts
in the tree, so it is safe to run from a post-merge hook, from CI on push to
`main`, or by hand — with one caveat: it mirrors *the tree it runs in*. Run the
mutating form where that tree is `main` (CI after merge, a post-merge hook); on a
feature branch, run `sync --check`. The CI job that runs the mutating form needs a
token that can write issues (and the project board, if §3 configures one);
fork-PR CI, which has neither, is exactly the `--check` case.

This buys a real property: **the tracker works offline.** Add on a plane (§6.4),
claim on a plane, deliver on a train, push; the mirror reconciles when the branch
lands. No operation *requires* the network at the moment it runs.

Every datum has exactly **one writable home**. The mirrored state — title, body,
open/closed, labels — is written only from the tree: editing it on GitHub is
drift, overwritten by the next `sync`, never read back. Comments are the converse
(§7.3): written only on GitHub, read into the tree as `Feedback` facts,
ingest-once. Neither channel's data is writable on both sides, so the
two-sources-of-truth failure cannot arise. The line holds at *status* with one
carefully-shaped exception: a close of a `Delivered` item's issue is honored as
a verify *gesture* (§7.4) — ingested as an event and re-derived, never merged as
state. Every other out-of-band state edit is drift: overwritten and reported.

### 7.3 Comments come back as feedback

The mirror makes items visible where the team already looks, and visibility
invites replies. A reply is not drift: nothing in the tree generates comments, so
a comment is *new information authored on GitHub*, not a second copy of tracker
state — which is why ingesting it does not breach §7.2's one-way discipline.
`sync` job 3:

* Every new comment on a mirror issue becomes a `Feedback` fact in the item's
  file: `author: "github:<login>"`, `at:` the comment's `created_at`, `content:`
  the comment body verbatim. The `github:` prefix keeps GitHub identities from
  colliding with local agent names and makes the channel greppable.
* **Ingest-once, keyed on `(workitem, author, at)`** — an existence check before
  persisting, the same shape WI-432 added for feedback targets. Later edits or
  deletions of the comment do not propagate: the fact records what was said when
  it was said. This keeps `Feedback` exactly what `store.anthill` declares it to
  be — monotone, only ever persisted — so ingestion composes with the
  append-only contract instead of straining it.
* Ingestion is deterministic (same comments → same facts), so two checkouts
  syncing concurrently converge, and the existence check makes re-runs no-ops.
* `sync`'s own comments (the §7.4 drift explanations) open with a fixed
  `[anthill-todo sync]` marker, and ingestion skips marked comments — the
  mirror must not echo into the tracker it mirrors.
* **A comment is advice, never a command.** "verified!" in a comment does not
  flip status; state changes remain tracker operations — with the single §7.4
  exception, which is a close, not a comment. This is the line that keeps the
  inbox from becoming bidirectional control.
* A comment on an issue with no corresponding file falls under the
  dangling-allocation report (§6.3) rather than being silently ingested; it is
  picked up if the file is recreated.
* Like reconciliation, ingestion mutates the tree, so it lands where the
  checkout can commit — a maintainer's `sync`, or a committing CI job.
  `sync --check` reports the count of pending un-ingested comments.

### 7.4 Closing a delivered item's issue is a verify gesture

§7.3 draws the line at status: a comment is advice, never a command. There is
exactly one command worth admitting through the mirror, because it is the one
the mirror's audience most naturally performs: **a reviewer closing the issue of
a `Delivered` item**. What keeps this from becoming bidirectional state is the
same discipline as §7.3's — the close is ingested as an *event*, not merged as
state.

During job 3, for every mirror issue whose GitHub state is closed while the
tree's item is `Delivered`, `sync` applies `verify` through the ordinary store
operations — the status flips, the file moves `delivered/` → `verified/` — and
appends a provenance `Feedback` fact (`author: "github:<closer>"` when the
issue timeline yields the actor; `content: "verified by closing issue #N"`).
Job 4 then re-derives the issue's desired state, which *is* closed: the gesture
and the derivation converge, and status was only ever written in one place —
the tree.

A close on an item in any **other** state is not a legal transition and is
treated as drift, not obeyed: job 4 reopens the issue, `sync` reports it, and
posts a comment saying what would have been honored ("close verifies a
*delivered* item; this one is Open — use the tracker, or leave a comment"). A
**reopen** of a terminal item's issue is likewise drift: re-closed, reported,
and the `Verified` status stands — un-verifying is a tracker decision, not a
mirror gesture. GitHub's close *reasons* (`completed` vs `not planned`) are
ignored in v1; mapping `not planned` on a delivered item to `Rejected` is §12
material.

## 8. Realization

### 8.1 The store spec, and the two changes it needs

`anthill.todo.store.WorkItemStore` (`store.anthill`) declares the fifteen operations
the CLI needs over an abstract `State`, with `FileBasedWorkitemStore` supplying
`State = WIS` and the bodies. A second impl — `CoordinatedWorkitemStore` with its
own `State` — slots in beside it, and every read and mutation the CLI performs is
already an operation of the spec.

The spec changes in exactly two places, both described in §6.2: `next_id(s)` becomes
`alloc_id(s, summary)` with `effects {Modify[s], External, Error}`, and `External`
joins `commit`'s row (its coordinated body writes the `MirrorEntry` fact and runs the
best-effort tail). Allocation is the one thing the two backends do *differently in
kind* rather than differently in mechanism — a counter bump versus an optimistic,
retried stake — so it is the thing the interface has to be honest about. Everything
else (`replace`, `lookup`, …) keeps its signature; the coordinated impl differs only
in where its bytes land and whether it also pokes the mirror.

### 8.2 Selection: the WI-402 existential factory

Backend selection is the factory shape from `docs/design/path-dependent-types.md` §5,
and it is the **first real consumer** of WI-402's existential half (delivered):

```anthill
operation open_store(binding: ExtentBinding, coord: Option[T = Coordination])
  -> C ensures WorkItemStore[State = C]
  effects {Error}
=
  match coord
    case none()  -> open_file_store(binding)
    case some(c) -> open_coordinated_store(binding, c)
```

The `ensures` manifest roots the abstract carrier `C` back at the interface, so the
result is usable at the call site without escaping. WI-200 (multi-instance `Modify`
state) is **not** needed: one backend instance per CLI invocation, and distinct
backend sorts occupy distinct slots.

**What this is, and is not, worth.** Mechanically it is a `match` with two arms, and
the host *already* selects — `rustland/anthill-todo/src/main.rs` pins
`FileBasedWorkitemStore` into the `chain_dicts` requirement dictionary that
`call_with_requirements` consumes, and builds the `wis(backend:, id_counter:)` state
value itself. Reading the declaration there instead would be a few lines and would
match proposal 057's rule that the host factory is "the one piece that stays native."

The reason to build it in the bundle anyway is that WI-402's existential half has **no
in-tree consumer**, and acquiring one is why WI-402 was parked on this ticket. What is
load-bearing is neither the `match` nor where it lives: it is that `WorkItemStore` and
`Store` are genuine abstractions, so that a second implementation is *writable* at all.
The selection is trivia; the interface is the work.

Two consequences from WI-402's delivery notes:

* **Call sites must use the qualified form** — a bare call to a body-less spec operation
  (`lookup(s, id)`) does not resolve through an existentially-typed receiver, while
  `WorkItemStore.lookup(s, id)` does. **This is already true of the code**: 43 of
  `main.anthill`'s 44 spec-op call sites are written `WorkItemStore.op(…)`. The single
  exception was the bare `stamp_format(s, current_store_format())`. **Done (WI-1113)** —
  it is now `WorkItemStore.stamp_format(…)`, and it was the only one.
* **`main` must stop being typed on `FileStore`. Done (WI-1113).** The signature was
  `main(args, store: FileStore, wis_cell: Cell[State], agent)`, with the concrete
  `FileStore` threaded through `dispatch` into every mutating `cmd_*` — 14 parameter
  declarations, 13 call sites, two `Modify[store]` rows, and **not one body that read
  it**. You cannot swap a backend while a concrete `FileStore` sits in `main`'s type, so
  the deletion was the true prerequisite. It is now
  `main(args, wis_cell: Cell[State], agent)`.

**What that leaves, and it is worth stating precisely.** With the parameter gone, the
bundle is already backend-abstract *without* `open_store`: `sort Main` declares
`sort State = ?` and `requires WorkItemStore[State]`, every `cmd_*` takes
`Cell[State]`, and the host discharges the requirement with a dictionary. Selection was
never the missing piece — the `requires` form already does it.

What remains coupled is narrower: `main.rs` hand-builds the impl's state value,
interning `anthill.todo.store.FileBasedWorkitemStore.wis` and its `backend` /
`id_counter` fields. That is the host knowing one impl's internals, beyond the single
legitimate native step (mapping a declared store to a compiled backend). Removing
*that* is what `open_store` is for here.

### 8.2.1 `open_store` is not expressible against today's spec (WI-1113, measured)

It was attempted and it does not load. The obstruction is structural, not a syntax
detail, and it is recorded here because it is **increment 2's problem to clear**.

WI-402's existential is recognized by `detect_existential_carrier`, which looks for
`-> C ensures Spec[C, …]` with `C` in the spec application's **first positional** slot
— the *carrier*. The loader then rewrites the return type to the spec with that slot
dropped, so the body must return a value whose sort **provides** the spec. That is the
shape the delivered KVStore fixture has: `sort MemStore { provides KVStore[K = …, V = …] }`,
carrier and members distinct.

`WorkItemStore` is not that shape. Its only parameter *is* `State` (proposal 036 /
WI-203), satisfaction is spelled `fact WorkItemStore[State = WIS]`, and `WIS` is the
member value — nothing provides the spec as a carrier. Both spellings were built and run:

| Attempt | Result |
| --- | --- |
| `-> C ensures WorkItemStore[C]` | `type mismatch in open_store.return: expected WorkItemStore, got WIS` |
| `-> C ensures WorkItemStore[State = C]` | `unresolved name 'C'` — the named form is not detected as an existential at all |
| `FileBasedWorkitemStore.wis(…)` from namespace scope | `expected known operation or arrow-typed variable, got unknown functor` |

The third line matters independently: a namespace-level factory cannot construct an
impl's state even setting the existential aside, so `open_store` must live inside the
impl — where it can no longer select between impls, which was its point.

**So the factory needs the spec restructured**, giving `WorkItemStore` a carrier sort
that `provides WorkItemStore[State = …]` rather than a bare instance fact. That is a
change to the store spec itself, it only pays for itself once a *second* impl exists to
select between, and increment 2 is already opening this file to add one. It is
increment 2's scope, not a bolt-on here.

Two consequences worth keeping in view. The counter seed stays host-side for now
regardless: the bundle has no `String -> Int64` with which to recover a number from
`WI-1042`, so it cannot compute its own seed — and under coordination the parameter
disappears entirely anyway (§8.3), `alloc_id` reading the forge registry instead of
counting. And WI-402's existential half still has **no in-tree consumer**; this design
remains its intended first one, just one increment later than §14 row 1 assumed.

### 8.3 Host side

* **`ItemPerFileStore`** — a **new `Store` implementation** in `anthill-core`'s
  persistence module, *not* a `FileConvention` variant (§5.2 gives the argument, and
  the §14 self-hosting constraint is why it matters). It implements the six `Store`
  methods and does not implement `IndexedStore`; `IndexedFileStore` is untouched and
  keeps serving every project that has not moved. Its routing is **content-driven**
  where `FileStore::fact_path` is content-blind: a `WorkItem` goes to
  `<status_dir>/<id>.anthill` (the status field picks the directory), and
  `Feedback` / `Tag` / `MirrorEntry` go to the file of the item they name (an index
  lookup by the referencing field). It is parameterized —
  `ItemPerFileStore { root, status_field: "status", id_field: "id",
  ref_field: "workitem" }` — so `anthill-core` persistence stays domain-neutral and
  stage0's field names live in the todo CLI's configuration of it, not in the library.
  It owns the relocation rule of §5.1. The loader needs no change:
  `collect_anthill_files` already recurses. Host wiring does: the source-map seeding in
  `rustland/anthill-todo/src/main.rs` (`store.record_source(rule_id, path, span)`) is
  `IndexedFileStore`-specific — spans into shared files — so `build_store` grows a
  per-backend arm that associates *paths* instead, without disturbing the existing one.
* **A `Forge` carrier** — a **declared anthill `sort`** whose operations are Rust
  functions, bound through the existing realization channel rather than injected as an
  opaque host value:

  ```anthill
  provides GithubForge language rust
    artifact "rustland/anthill-todo/src/forge/gh.rs"
    operation_map { create_entry: "gh_create_entry", recent_entries: "gh_recent_entries", … }
  end
  ```

  This is exactly the shape `rustland/anthill-stl/anthill/persistence.anthill` already
  uses to bind `Store`'s six operations, and it gets the **fake** for free: a second
  `provides` block over an in-memory list, no special-casing anywhere. It remains a
  *value*, not a new effect: authority is possession (the bundle cannot touch the
  registry without holding the carrier), and the §8.2 factory decides which
  implementation a run holds. Its mutators carry `{Modify[m], External, Error}` and its
  reads
  `{External, Error}` — each row the *union over implementations* (proposal
  054 §Faking): the real carrier refines away `Modify[m]`, the fake refines
  away `External`, which is what lets tests drive `Branch` searches over the
  fake while spec-typed production code stays out of `Branch` regions
  (`Branch`×`External` is rejected — proposal 054). `External` (proposal
  054 / WI-698, a small substrate prerequisite) is the *generic* outside-world
  effect: it marks
  dependence on state outside the tracked heap — non-replayable, non-reorderable,
  never equational, and two calls may disagree with no tracked `Modify` between
  them (which is what `Error`-only cannot say about a registry read). One
  generic effect rather than one per capability, so the row vocabulary stays
  stable as backends multiply; the *which*-capability distinction is authority,
  and lives in the carrier. Operations, named forge-neutrally: `create_entry`,
  `recent_entries` (the newest page — list endpoint, open+closed), `entries_titled`
  (exact-title search: the §6.1 old-claimant leg), `retitle`, `set_body`,
  `close` / `reopen`, `entry_comments` / `close_info` (since-cursor comment
  listing + close state/actor, for §7.3–§7.4),
  `add_to_board`. §6.1's `retreat` is not a primitive of its own: it is
  `retitle` + `close`, named once for the losing-racer step that uses both.
* **Substrate prerequisite, and it blocks the carrier.** `HOST_FNS` in
  `rustland/anthill-core/src/eval/builtins.rs` is a **closed `const` slice**, and
  `register_operation_mappings` turns an unknown `host_fn` key into an
  `EvalError::Internal` that kills every interpreter built for the program. So
  `anthill-todo` **cannot name its own host functions in an `operation_map` today** —
  the binding block above is not constructible as things stand. Putting the `gh`
  shell-out into `anthill-core` would fix it in the wrong direction: the kernel would
  learn about forges. The fix is for `host_fn_by_key` to consult an
  embedder-supplied table alongside its own, which any host binding a carrier of its
  own will need. It lands as its own prerequisite work item, ahead of the carrier.
* **GitHub is one implementation of the carrier, not its definition.**
  Everything above it — the §6.1 allocator, §6.4 reconciliation, all of §7 —
  consumes only the carrier's contract, so substituting GitLab, Gitea, or a
  plain coordination service is one `Forge` config entity (§3.2) plus one carrier
  implementation, with zero change to the bundle — and, since the amendment, with no
  new *config variant* either, which is what "the forge is a parameter" buys. The
  contract a substitute must honor — §6.1's soundness consumes exactly these five things:
  **(1)** an atomic creation primitive whose identifiers are totally ordered by
  creation (the stake); **(2)** a live newest-first listing of entries with
  their current titles and open/closed state; **(3)** a title search that
  reaches arbitrarily old entries; **(4)** comments with stable
  `(author, created_at)`; **(5)** entries persist once created — closing hides
  nothing from (2)–(3). This backend ships two implementations: one shelling
  out to `gh` (inheriting the user's existing auth — no token handling of our
  own), and a **fake** over an in-memory issue list — not a test trick but the
  second implementation of a first-class seam, which is what makes §6's race
  protocol testable without a network, including the lost-race interleavings
  the fake can force deterministically — and, because the fake's rows drop
  `External`, a test may go further and *search* over whole schedule spaces
  under `Branch` (027.2 solvers: `oracle` replays one interleaving, `all`
  enumerates and checks *no duplicate ids* across every branch; proposal 054
  §Faking).
* **Provisional entropy is not a mirror concern**: `fresh_token()` is an
  ambient host operation (`{External, Error}`), available with or without any
  mirror — §6.4 mints offline, after all.
* **Counter seeding disappears.** `main.rs` currently scans the KB for the max `WI-NNN`
  to seed the `WIS` cell's `id_counter`. Under coordination that seed is exactly the
  bug (§1.2): `alloc_id` reads the registry instead, and provisional ids come from
  entropy, not a counter.

## 9. What this actually buys (conflict analysis)

| operation | today (single file) | github-coordinated |
| --- | --- | --- |
| two devs `add` | conflict at EOF **and** duplicate id | different files; ids allocated by GitHub → **no conflict, no collision** |
| two devs `add` *offline* | conflict at EOF **and** duplicate id | different files, disjoint provisional ids → **no conflict**; permanent ids assigned at reconcile (§6.4) |
| two devs claim/deliver *different* items | conflict (same file) | different files → **no conflict** |
| two devs claim the *same* item | conflict, resolved by hand, easy to resolve wrongly | rename/rename conflict → **loud, and the disagreement is real** |
| two devs add feedback to *different* items | conflict | different files → **no conflict** |
| two devs add feedback to the *same* item | conflict | **still a conflict** (both append to one file) — see §12 |
| delete | conflict-prone | delete-vs-modify → loud |

The one row that does not improve is concurrent feedback on the same item, and it is
the honest limit of "one file per item".

## 10. Loud failures

Per the repo's development principles, each of these is an error or a diagnostic, never
a silent skip or a fallback:

* **`add` never silently allocates a permanent id without GitHub.** Offline,
  unauthenticated, or with `access: disabled()`, it mints a *provisional* id (§6.4) —
  a self-announcing namespace with the remedy printed alongside — never a dense
  `WI-<n>` from local state; that fallback *is* the bug this design removes. Only
  unreachability and missing auth downgrade to provisional: a malformed or
  unexpected GitHub response is an error.
* **Directory / status disagreement** — a file in `open/` whose fact says
  `Claimed(...)` → loud load error naming both, plus `anthill-todo fsck --fix` to move
  the file to match the fact (the fact wins; §4).
* **Duplicate id** — the same id in two files → loud load error. Under §6 this
  should be unreachable; if it happens, the allocator is broken and we want to know
  immediately.
* **Dangling reference** — a `depends_on` naming an id with no file (e.g. a
  half-reconciled provisional rename, §6.4) → named by `fsck`; for the
  reconciliation case a `sync` re-run repairs it.
* **Permanent-id item with no `MirrorEntry` fact**, under a declared `Coordination` → loud
  in `sync` (migration incomplete, or an `add` died between steps 4 and 5).
  Provisional items lack the fact by definition and are reported as *unreconciled*,
  with a count — expected state, not an error.
* **Issue claiming an id with no file** → reported by `sync` as a dangling
  allocation (§6.3) — distinguished from `[deleted]`-tombstoned issues (§7.2),
  which are the *expected* end state of a deletion.

## 11. Migration

```bash
anthill-todo migrate --to github-coordinated
```

1. Explode `workitems.anthill` into one file per item under `<state>/`, each carrying
   its item's `Feedback` and `Tag` facts. Pure local rewrite; reviewable as one commit
   (a large one, and a one-time one). **The file format is whatever §5.3 has settled by
   the time this runs** — this repo's tracker migrates exactly once, so WI-1119 lands
   before this step and migration writes `WI-NNN.anthill.md` (anthill head + chapters), not an
   intermediate `.anthill` form that would have to be migrated again. Every
   `WI-NNN.anthill` spelling elsewhere in this document predates that decision and
   illustrates the layout, not the encoding — with one exception that is *not*
   illustration: §7.1's mirror-body pointer is generated output, and has been
   updated to `.md` accordingly.
2. Create one mirror issue per item, in id order, each *born* with its `WI-NNN:`
   title (§6.1 — migration is allocation where the winner is known in advance),
   then immediately closed when its item is terminal (§7.1). **Every item is
   mirrored, terminal ones included.** The GitHub view is trustworthy only if
   open/closed reflects the whole tracker: under a partial backfill a missing
   issue is ambiguous — unmigrated, deleted, or never existed — and the §10
   "permanent-id item with no `MirrorEntry` fact" check would need a permanent
   exemption for terminal items, gutting it. Full mirroring keeps one uniform
   invariant — every permanent id has exactly one issue, and the issue's
   open/closed state is the item's coarse state. The cost is one-time: ~1110
   creations here, paced under GitHub's secondary rate limits. Only 47 of them
   are create-then-close — §7.1 closes on `Verified`, `Rejected`,
   `ProposalRejected` and `Stale` only (38 + 6 + 0 + 3 today), while §7.4 keeps
   the 913 `Delivered` issues open as the verify gesture. **Resumable and idempotent**: keyed on the id in the
   title, and each item's file gets its `MirrorEntry` fact written as the issue
   is created, so an interrupted run resumes where it stopped.
3. Rewrite the `ExtentBinding` store term to `ItemPerFileStore(...)` and add `fact Coordination(...)` in `project.anthill` (§3).
4. Stamp `StoreFormat(version: 2)` through the store, the way `migrate` already
   stamps version 1 (WI-434).

Migration runs in the working tree and is pushed as one commit when it completes.
An interruption is local — step 2 resumes — and other checkouts never observe a
half-migrated state: they see the old layout or the new one, atomically, the way
git always publishes.

The two axes stay orthogonal: `ExtentBinding` says *which layout*, `StoreFormat` versions
the *schema within* it. The version check in `main.anthill`
(`check_store_versions`) keeps working unchanged.

Migration is one-way in practice. A `--to local-single-file` inverse is trivial to write
(concatenate the files, drop the `MirrorEntry` facts) and worth having as an escape hatch,
but it abandons the id registry.

## 12. Open questions

* **Concurrent feedback on one item** is the one conflict the layout does not remove
  (§9). The fix is to make the item's unit a *directory* — `open/WI-690/item.anthill`
  plus `open/WI-690/feedback/<timestamp>-<author>.anthill` — which keeps the "move the
  directory, the feedback moves with it" property while giving each feedback entry its
  own file. It is strictly better on conflicts and strictly worse on
  browsability (a tree of 700 directories). Recommendation: ship file-per-item, and
  keep this in reserve behind the *same* relocation rule (§5.1 relocates a path,
  whether it names a file or a directory), to be adopted if feedback conflicts show up
  in practice.
* **Should `sync` run automatically?** A git hook is invisible and easy to have
  uninstalled; CI on `main` is reliable but lags the push. Probably both, with
  `sync --check` as a CI gate.
* **Description in the issue body.** Keeping only a pointer means GitHub search does not
  find work items by description. Mirroring the full description makes the body large and
  makes drift visible on every description edit. Pointer-only for v1, and §5.3 strengthens that
  without settling it: once the item file *is* a markdown document, the target renders
  on GitHub and is reachable by code search. Two caveats keep this an open question
  rather than a closed one — §7.1 regenerates the pointer only on `sync`, so between a
  state change and the next reconciliation the link is stale; and code search is a
  different surface from issue search, needing repo access and not surfacing the item
  in the issue list where the mirror's audience is looking.

## 13. Non-goals

These are the boundaries of *this* backend, not of the design space. The store binding is
open, and each of them is a coherent thing to build later, as another variant over the
same store spec.

* **Work items are not GitHub issues here.** In this backend the issue is a mirror and
  an allocator ticket. A genuinely GitHub-backed store (§2) is a separate `Store` implementation.
* **No bidirectional sync of mirrored state.** Edits to an issue's title, body,
  state, or labels are not read back — two writable homes for one datum is the
  failure this backend is shaped to avoid. Comment ingestion (§7.3) is not that:
  comments have one writable home (GitHub), tracker state has one (the tree), and
  neither writes the other's. The §7.4 close-gesture is likewise an *event*,
  honored only in the one legal transition and then re-derived. (In a backed
  store the distinction would dissolve — the issue would be the only copy.)
* **No GitHub Projects automation** beyond filing the mirror issue into the configured
  board.
* **No `api` backend** yet. The third variant sketched in the original note (a
  standardized remote server) is a future `Store` implementation; this design keeps the store
  spec neutral enough to host it, but builds nothing for it.

## 14. Increments

Each is independently green and independently useful. Per the "risky work first"
preference, the substrate refactor is first, not last.

| # | WI | Increment | Ships |
| --- | --- | --- | --- |
| 1 | WI-1113 | **Store-factory substrate.** This amendment; drop the vestigial `store: FileStore` from `main`/`dispatch`; move the last spec-op call site to the dotted form. `open_store` proved not expressible against today's spec and moves to row 2 (§8.2.1). Absent declarations → today's behavior. | no user-visible change; the seam |
| 2 | WI-1114 | **`ItemPerFileStore`.** The new `Store` implementation (§5.2), the relocation rule, the per-backend host wiring arm, `fsck`, loader coverage, tests against a null forge. Plus the spec restructuring §8.2.1 names, and `open_store` on top of it — a second impl is what makes both pay. | conflict-free multi-dev on *state changes* |
| 2b | WI-1119 | **Work items are documents** (§5.3). The declared fact↔markdown mapping (§5.3 rules, §5.4 artifact): `WI-NNN.anthill.md`, anthill head in a fenced block, prose chapters, repeated chapters for feedback, eight malformed-editing rules. Separate from row 2 per §14.1 — bundled, a format bug would mask a store bug on the tracker we are running on. (Not because of the loader glob: row 2 already carries loader coverage.) Blocks row 6 — the live tracker migrates once, into the final format. | items readable and editable as documents |
| 3 | WI-1115 | **`Forge` carrier.** The embedder host-fn prerequisite (§8.3), the `Forge` sort + contract, its `provides`/`operation_map` bindings, `fresh_token`, the `gh` and fake implementations (the fake can force the §6.1 lost-race interleavings). | nothing alone; testable |
| 4 | WI-1116 | **Coordinated `add`.** The §6.1 stake-by-creation protocol, the §6.4 provisional fallback, `MirrorEntry` facts. | conflict-free **and** collision-free `add`, online or off |
| 5 | WI-1117 | **`sync`.** Provisional-id reconciliation (§6.4), allocation-debris repair, comment ingestion (§7.3), close-as-verify (§7.4), the mirror push, deletion tombstones, `--check`, CI gate. | the mirror + the return channels; autonomous mode closes the loop |
| 6 | WI-1118 | **`migrate --to github-coordinated`.** Resumable, idempotent. | this repo's own tracker moves |

### 14.1 The self-hosting constraint

`anthill-todo` is the tool tracking these increments, reading this repo's own
`anthill-todo/workitems.anthill` through the exact store layer being replaced. It must
stay usable at **every commit** — a broken build means no `claim`, no `deliver`, no
`feedback`, and no way to record that it broke. That is not a caution; it is a
constraint that shapes the design:

* **The two stores coexist.** `IndexedFileStore` is not replaced, and this repo's own
  tracker stays on it through increments 1–5. This is the concrete reason §5.2's
  sibling-store shape is *required* rather than merely tidier: a convention *inside*
  `IndexedFileStore` would have made every increment surgery on the store the tracker
  was running on at that moment.
* **The new store is built against fixtures, never the live tracker.** `anthill-todo`
  takes `-d <DIR>`; all `ItemPerFileStore` work runs against a temp project.
* **Backend before declaration, always.** The host hard-refuses a declared store this
  build does not provide (WI-830). A commit whose `project.anthill` names
  `ItemPerFileStore` while its binary lacks it leaves the tracker unusable — correctly,
  but fatally for us. The backend lands first, in its own commit; this repo's own
  declaration changes last.
* **Keep a known-good binary** aside before each increment. If a build breaks
  mid-increment it is the only way to keep recording work.
* **Increment 6 is the one commit that moves the live tracker.** Rehearse on a copy,
  verify with `sync --check`, and keep that commit atomic and alone, so a single
  `git revert` restores `workitems.anthill` if it goes wrong.
