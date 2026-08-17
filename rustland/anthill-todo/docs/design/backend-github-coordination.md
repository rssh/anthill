# Pluggable backends: the coordinated store

**Work item:** WI-437 — split 2026-08-16 into an umbrella plus increments (tag
`wi437`), one per §14 row. WI-1120 (§5.3) was inserted between rows 2 and 3;
WI-1121 (§6.5) between rows 2b and 3.
**Status:** design, amended 2026-08-17 (allocation policy)
**Supersedes:** `examples/github-todo/docs/pluggable-backend.md` (the original three-line sketch)

> **Amendment, 2026-08-17. GitHub is no longer required for anything.** The draft
> assumed one answer to "who allocates ids" — the forge's counter — because a forge
> was already present for the mirror. Allocation is now a **policy** (§3.2), and
> the default one, `ContentHash` (§6.5), mints ids locally from the item's own
> author, timestamp and description. Nothing coordinates; nothing waits.
>
> That collapses the forge's two fused roles. It was *allocator* **and** *mirror*;
> it is now only a mirror, and an optional one. §1's two problems are then both
> answered without a network: textual conflicts by file-per-item (§5, delivered),
> id collisions by local minting. The title says "coordinated", not
> "GitHub-coordinated", for that reason — §6.0–§6.4 and all of §7 remain, as the
> forge-backed *option*.

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

> **Amended 2026-08-17: job (a) is gone, and with it the name.** Ids are minted
> locally (§6.5), so GitHub coordinates nothing. Job (b) survives, demoted from a
> continuously reconciled mirror to on-demand **export / import** (§7). What is
> left of the sentence above is:
>
> > **git holds the truth. A mirror publishes it. Publishing is optional.**
>
> The asynchrony clause survives verbatim and is now trivially true: no command
> waits on a network because no command touches one. Reading this section, treat
> "coordinates" as historical — it describes the design this document started as,
> which is worth keeping because §6.0's retirement only makes sense against it.

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
`fact Project(...)`. It answers two independent questions, and each gets exactly
one writable home:

* **Where do the rows live, and in what layout?** → `fact ExtentBinding`, already the
  channel (WI-830). Its `store` field names the backend to build.
* **Is there a mirror, and where?** → `fact Mirror`, below.

**There is no configuration for id allocation, and that is the point (§6.5).**
The draft's `Coordination` fact fused "who allocates ids" with "where is the
mirror" because one forge answered both. Splitting them made allocation local, and
once it is local there is exactly one way to do it — so the field disappears
rather than becoming a seam with a single implementation. What is left describes
only the mirror, so it is named for that.

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

### 3.2 The mirror: the forge is a parameter

**Amended 2026-08-17, twice.** The draft's `Coordination` fused two questions
because GitHub answered both: *how are ids minted* and *where does the mirror
live*. Splitting them is what let allocation become local (§6.5) — and once it is
local there is one way to do it, so the allocation field went too rather than
becoming a seam with a single implementation. What remains describes only the
mirror, and is named for it.

```anthill
fact anthill.stage0.Mirror(
  forge:  GithubForge(repo: "rssh/anthill", project: some(value: "Anthill Roadmap")),
  access: MirrorAccess.enabled())
```

The entities live in the **bundled** `anthill.stage0` domain, in a new
`rustland/anthill-todo/anthill/coordination.anthill`:

```anthill
namespace anthill.stage0

  -- WHERE the mirror publishes. `target` is a Term, on the exact
  -- `ExtentBinding.store` precedent above: it names a thing to BUILD, written
  -- where no such thing exists yet, and the host resolves it to one of its
  -- compiled-in implementations. `Forge` (§8.3) is the algebra a built one
  -- satisfies, which is a different thing and one a config file cannot hold.
  --
  -- `target`, NOT `forge`, and the rename is not cosmetic. A *forge* is a
  -- repository host with issues attached — GitHub, GitLab, Gitea, sourcehut, the
  -- word descends from SourceForge. That is the right word for §6's retired
  -- allocator, which genuinely needed a forge's issue counter. Export (§7) needs
  -- far less: somewhere to put an entry and read comments back. Jira, Linear, a
  -- static site or a directory of files can all be that, and none of them is a
  -- forge. The field is named for the ROLE it fills, so the vocabulary does not
  -- promise more than the contract asks.
  --
  -- NO `Option`, and no allocation field. An absent `Mirror` fact means no
  -- mirror — that is what absence is for — so every state means exactly one
  -- thing: no fact, no mirror; fact plus `enabled`, publish; fact plus
  -- `disabled`, configured but quiet.
  entity Mirror(target: Term, access: MirrorAccess)

  -- One entity per target, carrying that target's own parameters. Adding GitLab,
  -- Gitea, or a plain issue tracker is ONE entity here plus ONE carrier
  -- implementation (§8.3) — never a new config variant for the model, because the
  -- model is the same and only the target differs. This is what §8.3's
  -- substitution contract is FOR, and the draft's `GithubCoordinated` variant
  -- contradicted it.
  entity GithubForge(repo: String, project: Option[T = String])

  -- Whether to TALK to the target at all: publish on `export`, read on `import`.
  -- The fact is the project-wide DEFAULT; a single checkout overrides it with
  -- ANTHILL_TODO_MIRROR=on|off (or --offline) — CI test jobs, air-gapped
  -- machines, and fork checkouts without write access run off. `disabled` does
  -- not disable the tracker: every command still works, and ids are minted
  -- locally either way (§6.5). What `disabled` removes is the publishing, never
  -- the work.
  enum MirrorAccess
    entity enabled
    entity disabled
  end

end
```

Bundling the entities (rather than expecting a per-project `domain.anthill`) follows
the `StoreFormat` precedent in `version.anthill`: a project's own domain may predate
the entity, and an unresolved import fails the *whole* bundle load — on exactly the
projects that most need the new code path. See WI-505/WI-684.

**Defaults.** An absent `Mirror` fact means a purely local tracker — nothing is
published, and ids are minted locally either way (§6.5). An absent `ExtentBinding` already defaults to
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

> **Retired 2026-08-17, along with its subject.** Everything in §3.3 above is
> about a `Coordination` fact that no longer exists, and the check it argues for
> must NOT be built. Its whole premise was that coordination-without-state-dirs is
> a forbidden combination, because "directories alone fix conflicts but not id
> collisions" — and §6.5 fixes id collisions *unconditionally and locally*, for
> every layout. So there is no forbidden combination left to refuse: a `Mirror`
> fact beside a single-file store is a perfectly good configuration, and publishing
> a single-file tracker to GitHub is a reasonable thing to want.
>
> The section stays as the record of a coupling that was designed, argued about,
> and then dissolved by making the thing it protected against impossible. That is
> the better outcome than the check — "make illegal state unrepresentable over
> check logic," arrived at from the far side.

## 4. On-disk layout: a directory per state, a file per item

```
anthill-todo/
  project.anthill              fact Project(...) + fact ExtentBinding(...) + fact Mirror(...)
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
which is what the store writes until WI-1120 lands; §5.3 keeps this content and changes
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

`MirrorEntry` is a new fact (in `mirror.anthill`, next to `Mirror`), keyed on the
work-item id — the same additive shape as `Tag`.

**It stays OUT of the `WorkItem` entity, and the reason has only got stronger.** A
`WorkItem` field would put a mirror concern in the stage0 domain, where it would
read `none` in 1110 of this tracker's 1112 items. As a fact it is additive: absent
means absent, and the domain stays backend-neutral.

**An item's external ids are a SET, and the relational form already is one**
(amended 2026-08-17). N `MirrorEntry` facts for one item is N rows — exactly how
`Tag` gives an item a set of tags — so multiple targets need no list field, no
schema change, and no `Option` nesting. Under §7's import/export framing that
multiplicity is the normal case rather than an exotic one: a project may publish
to a public forge and an internal tracker, or import from one and export to
another.

```anthill
entity MirrorEntry(workitem: String, target: String, entry: String)
```

Two fields changed when §6.1 was retired, and both were consequences of it rather
than free choices:

* **`entry` is a `String`, not an `Int64`.** The draft required a number because
  §6.1's soundness rested on identifiers *totally ordered by creation*, and a
  counter is the only thing every candidate forge offers. With the allocator gone
  the external id is an opaque handle, and it must be — a Jira key is `PROJ-123`,
  a Linear id is a ULID, a URL is a URL. Requiring a counter would exclude every
  target that is not a forge, which §7's amendment explicitly wants to allow.
* **`target` says WHICH external system**, which was implicit while there was
  exactly one GitHub repo and cannot stay implicit once a set is the point. It
  names a `Mirror` fact, so the two sides agree by construction.

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

#### 5.2.1 What it holds instead of offsets (WI-1114, delivered)

The paragraph above says the span machinery does not carry over. What replaced it is
worth stating, because the obvious substitute is wrong in a way that does not fail
loudly.

An item file holds **several** rows — the item, its feedback, its tags, its mirror
link — so a retract still has to name one block *inside* a file. The obvious answer is
to keep the same `(path, byte range)` map and only change the routing. That answer
breaks on the very feature this store exists for: a relocation **rewrites the whole
file at a new path**, and every offset recorded into it is then stale. Stale offsets do
not error; they drop the wrong bytes. (`IndexedFileStore` lives with the same hazard
only because a shared-file store never moves a file, and because the CLI performs one
mutation per process.)

So the store keeps a **block model** of each file: the ordered list of text stretches
the file is made of, each one either a resident row or the inter-row text around it.
The host's spans are consumed at seeding to *cut* the file and are not kept, so nothing
survives a rewrite to go stale. Rendering a file is a concatenation; the §5.1 move is a
re-key of the model plus one block replaced in place; and the comments and blank lines
between rows survive both, which a rows-only model would silently eat.

Three consequences worth knowing:

* **A row appended at runtime is not addressable until the next load.** `Store::persist`
  is handed the fact, never the `RuleId` the KB is about to mint for it, so an appended
  block has no name. A retract of such a row in the same process is a loud refusal, not
  a silent no-op — the shared-file store's content-keyed fallback would compare a
  loader-normalized canonical against source text and match nothing (WI-187).
* **Deleting an item leaves its feedback.** `Feedback` is `monotone`, so it cannot be
  retracted; the file therefore stays, holding rows that name an item no file holds.
  That is reported (§10) rather than repaired — dropping them would lose live facts.
* **Emptied directories are left behind.** `open/` survives its last item's move. Git
  does not track empty directories, so nothing is published; removing them would be a
  guess about which directories the project meant to keep.

### 5.3 The item file is a document: head + chapters (WI-1120)

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
heading below the structural level is just a heading — ordinary markdown, part of that
chapter's text, carried verbatim. Only headings at a *structural* level are chapter
boundaries, which is precisely why those levels are reserved: if any heading could start
a chapter, a user's subsection would silently cut a field in half. ("Chapter" rather than
"section" only to keep it distinct from this document's own §-sections.)

**Structural levels nest, and there are two.** A repeated fact is not a field of the
item, and the document should not pretend otherwise: feedback entries are grouped under
one `## Feedback` **container**, one `###` per entry, rather than strewn across the top
level as siblings of `## description`. So `##` carries fields and containers, `###`
carries the entries inside a container, and prose begins at `####`. The alternative —
every entry a top-level chapter named by its timestamp — needs only a single reserved
level and is marginally simpler to check, but it files an entry in a log at the same
structural rank as a field of the work item, and it gives GitHub's outline a flat run of
timestamps where it could show `description` and `Feedback`.

**Eligible fields are `String` and `Option[T = String]`.** Both, not just the first —
`Feedback.content` is a bare `String` but `WorkItem.description` is
`Option[T = String]` (`domain.anthill`), and a rule admitting only bare `String` would
exclude the very field this section exists for. The `Option` case is what the missing-
chapter row below describes: absent chapter, `none`.

**Where the mapping lives:** bundled with the stage0 domain, beside `Mirror`'s
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
| heading at a structural level the mapping does not account for *in that scope* | **load error** naming file and heading — this is the truncation case, and it must not look like a note |
| `###` outside any container | **load error** — an entry heading with no container is the same truncation case one level down |
| heading below the structural level in scope (`###` in a field chapter, `####` in an entry) | prose belonging to the enclosing chapter, carried verbatim, never interpreted |
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

  -- The two structural levels (§5.3). Fields and containers sit at `level`,
  -- a container's entries at level + 1, and prose begins below that.
  fact DocumentFormat(level: 2)

  -- A prose field of the item's own fact: one chapter, fixed name.
  entity Chapter(
    functor : Term,     -- the fact the field belongs to
    field   : String,   -- the field whose text moves out
    named   : String)   -- the chapter's heading text

  -- A satellite fact keyed to the item, repeated 0..n: one container chapter,
  -- one entry chapter per fact inside it.
  entity ChapterGroup(
    functor   : Term,              -- the satellite fact
    container : String,            -- the `##` heading grouping the entries
    field     : String,            -- the entry's prose field
    named_by  : String,            -- the field whose value names each entry
    decorate  : List[T = String])  -- head fields regenerated into the entry heading

  fact Chapter(
    functor: WorkItem, field: "description", named: "description")

  fact ChapterGroup(
    functor: Feedback, container: "Feedback",
    field: "content", named_by: "at", decorate: ["author"])
end
```

`Tag` and `MirrorEntry` need neither: they carry no prose and stay in the head as
ordinary facts. Note what the split buys — `Chapter` has no `repeated` flag to get
wrong, because repetition is not a property of a field but the whole point of a
`ChapterGroup`. Making the two illegal to confuse is cheaper than checking a boolean.

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
fact Feedback(workitem: "WI-688", author: "claude", at: "2026-07-11T08:41:02Z")
```

## description

whole-`step` direct derivation — the rewriter should reach the normal form
without the intermediate `unfold` pass.

### why the intermediate pass exists

Hand-added prose lives below the structural level and rides along inside its
chapter, untouched by `claim`, `deliver` or a state change (§5.3).

## Feedback

### 2026-07-10T11:02:10Z — user

both deferrals landed; substrate should suffice.

### 2026-07-11T08:41:02Z — claude

delivered; the `unfold` pass is gone and 3 tests pin the normal form.
````

Read against §4's fact block: `description` and `content` are gone from the facts and
are now chapters; everything else is unchanged. `WorkItem.description` is filled from
the `## description` chapter; each `Feedback` fact is filled from the `###` entry named
by its own `at`, and `— user` after the name is `decorate: ["author"]` — regenerated,
and checked at load (§5.3). `## Feedback` itself carries no field: it is a container,
and its own heading is the only structural thing in the file that maps to no datum.

**Name collisions are positional, not a naming problem.** `named_by` is not injective —
`WI-599` holds two `Feedback` facts with identical `at` *and* `author` (§5.3). Under a
container this needs no disambiguating suffix: entries are *ordered siblings*, so the
Nth `fact Feedback` in the head binds to the Nth `###` under `## Feedback`, and the
reader checks that the two counts agree. Positional binding is only safe because the
entry heading is *checked* against its fact rather than ignored — a reordered or
hand-edited entry mismatches its `at`/`author` and is a loud diagnostic, not a silent
rebinding onto the wrong entry. Drop that check and this scheme becomes the worst one
on the page. That is a second thing the container buys
over flat top-level entries, where two identically-named chapters had nothing but a
`.2` suffix to tell them apart. No domain field has to be added to carry an identity
the data does not have.

## 6. Id allocation

**Amended 2026-08-17: allocation is a POLICY, and this section describes one of
two.** The draft had exactly one answer — the forge's counter — because the forge
was already there for the mirror. It is not the only answer, and it is not the
default one: §6.5's content-hash policy mints ids locally, needs no network, and
deletes most of what §6.1–§6.4 below exist to manage. Read §6.5 first if you are
choosing; read on if you are implementing `StakeByCreation`.

What every policy must deliver is the §1 requirement and nothing more: **two
developers who both run `add` without talking must not produce the same id.**
Density is not required. A monotone global sequence is not required — it is one
way to get uniqueness, and the expensive one.

### 6.0 The issue *is* the allocation (`StakeByCreation`) — NOT PLANNED

> **Retired 2026-08-17, before implementation.** §6.5's `ContentHash` supersedes
> everything from here to §6.4, and this is kept as a **recorded alternative**, not
> as work anyone should do. Read it for the analysis — §6.1's both-keep
> interleaving, which killed an earlier retitle-CAS design, is a real result and
> would have to be rediscovered by anyone attempting forge-side allocation again.
> Do not read it as the plan.
>
> **Why retire it unbuilt.** It buys one property `ContentHash` cannot: a registry
> visible to a *stale or shallow* checkout, since local minting leaves no trace
> outside the tree. Nothing requires that — `ContentHash` handles collisions by
> detection and convergent repair (§6.6) rather than by prevention — so the price
> is ~250 lines of retry loop, lost-race retreat, provisional ids and
> reconciliation for a nicety. Deleting unbuilt spec costs nothing: no migration,
> no deprecation, no users.

Under `allocation: StakeByCreation()`, **permanent ids come only from GitHub**, and
issue creation is the allocation event. GitHub's issue counter is a monotone,
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

### 6.5 `ContentHash`: the id is minted where the item is written

**Added 2026-08-17.** The other policy, and the one to reach for by default. The
id is derived, at `add`, from facts the tracker already holds, and it has **three
parts, each doing a different job**:

```
id := "WI-" <time> "-" <hash> [ "-" <slug> ]

       WI-20260817-K7M2Q-item-per-file-store
          └───┬───┘ └─┬─┘ └────────┬───────┘
          ORDERS    IDENTIFIES   DESCRIBES
     lexicographic  25 bits,    frozen at creation,
     sort is        Crockford   decorative, may be
     chronological  base32      absent
```

Two developers who both run `add` offline, on a plane, on the same afternoon,
produce different ids without exchanging a byte — because their authors differ,
their timestamps differ to the second, and their descriptions differ. No network,
no registry, no retry loop, no losing racer.

**Only `<time>-<hash>` carries identity, and this has a sharp implementation
consequence.** The slug is a rendering; it may be absent, and it is *not* compared.
So two items whose hashes collide have **different filenames** — their slugs differ,
because their descriptions do — and a duplicate check that compares whole id
strings would therefore MISS EVERY COLLISION. The `id:` field stores the full
string and §10's `PathDisagreement` compares that; the *duplicate* predicate
compares the `<time>-<hash>` prefix alone. §6.6 turns on this.

**The alphabet is Crockford base32** — `0123456789ABCDEFGHJKMNPQRSTVWXYZ`, i.e.
0–9 and A–Z without `I`, `L`, `O`, `U` — at five characters, so 25 bits and 33.5
million values per day.

Hex was the first choice and is wrong twice over. Crockford carries 5 bits per
character against hex's 4, so the same five characters hold 32× the space; and it
does not merely *exclude* confusable glyphs but **remaps them on decode** (`i`/`l`
→ `1`, `o` → `0`), which matters because §6.5's whole reference ladder assumes
people retype these fragments out of commit messages.

**Mixed-case encodings are excluded, and not on taste.** Base58 and base64 were
the obvious denser candidates. The id goes in a FILENAME, and this project
develops on macOS, where APFS is case-insensitive by default — measured:
`WI-20260817-aB3f9` and `WI-20260817-Ab3f9` resolve to one file, and the second
write silently clobbers the first. Under case folding base58's 58 symbols collapse
to roughly 33 usable ones, landing *below* a clean base32 while looking noisier.
Bech32 passes the case test but spends six characters on a BCH checksum — more
than this payload — to solve offline validation, which we do not have: the tracker
is the authority and a mistyped fragment matches nothing about 99.997% of the time.

**So: mint in ONE canonical case, and compare ids case-insensitively.** That is
the rule that makes the filesystem's folding incapable of deciding identity, and
it holds whatever alphabet is chosen. The hash segment is written uppercase, which
also lets it announce itself against the lowercase slug.

**The slug is what makes a file-per-item tree browsable.** `ls open/` under a bare
hash shows 125 lines of noise; with slugs it is a readable table of contents. This
is the concern §12 raised against the directory-per-item variant, answered here
for free. It also restores sayability — "the item-per-file-store one" — which a
bare hash destroys.

**Slug rules**, because they must be total and deterministic: lowercase the
description's opening, keep `[a-z0-9]`, collapse every other run to a single `-`,
**cut at a word boundary at 30 characters**, drop a trailing `-`. **An empty result
is legal and the slug is then simply omitted** — a description that is entirely
non-ASCII (this project writes Ukrainian) or entirely punctuation must still yield
an id, so the slug can never be load-bearing. WI-1114's `check_segment` already
accepts this shape and refuses anything that would escape the tree.

**Thirty, measured on 772 of this tracker's own descriptions**, which is the knee:
24 leaves 10% of items sharing a slug, 30 leaves 4%, and 40 leaves 0.8% for ten
more characters. Median id 45, filename 56. SEO guidance for blog slugs (3–5 words,
50–60 characters) does not transfer, because those live in URLs where nobody reads
them in a column; these are stacked in `ls` output, and terminal width is the
binding constraint.

**A repeated slug is not a defect — it groups a family.** The largest duplicate
sets at 30 are `anthill-todo-backend` ×8 (the WI-437 increments) and
`typer-wi-447-bare-form-prereq` ×4. In an `ls` that reads as structure. The only
cost is that the ladder reports candidates for such a slug, and the candidate list
is itself informative.

**Nothing in the storage layer is close to binding.** A 56-character filename sits
far under the universal 255 component limit, and under Windows' `MAX_PATH` of 260
for the whole path — the constraint that actually binds first — a typical deep
checkout still lands around 133. And because the slug rule emits only `[a-z0-9-]`,
filenames are pure ASCII, so 255 *bytes* and 255 *characters* are the same number
here and the UTF-8 mismatch that bites ext4 never arises. (FAT32 and exFAT survive
on USB sticks and every EFI System Partition, but not as a git working tree — no
symlinks, no permission bits — and what they contribute is another case-insensitive
filesystem, which the canonical-case rule above already covers.)

**The slug goes stale, and that is accepted.** Descriptions here are rewritten for
months — WI-1114's own was corrected by an amendment days after it was filed — so
a frozen slug will eventually describe an item that has moved on. The precedent is
the Nix store path (`<hash>-<name>`), where the name is understood as *provenance*,
not current state. `list` and `show` render the live description, so the drift is
visible only in filenames and raw references. State it rather than fix it: an id
that changed when its description did would not be an id.

**What this buys, stated precisely, because the name oversells it.** The property
is *minted locally without coordination*. It is **not** verifiability: the hash
input is the description **at creation**, and descriptions are edited constantly
here (this repo's own items grow feedback and revisions for months), so the input
is not preserved and the id cannot be recomputed from the item later. Treat the id
as **opaque** — a minting rule, not an integrity check. Building a "does the hash
still match" check would be building something guaranteed to rot.

The one thing the hash gives over plain entropy (`fresh_token()`, §8.3) is
**idempotence**: an `add` retried after a partial failure re-derives the same id
and heals, where a random token would create a second item. That, and it needs no
entropy source — the bundle already reads a timestamp for `Claimed(since:)`.

**A single writer never collides, because it can look before it writes.** The
birthday bound is the wrong model here: the CLI holds the whole tracker, so it
checks whether an id is taken *before* writing a byte. The mint therefore carries
an attempt counter and re-hashes until free:

```
h := H(author, created, description, attempt)     attempt = 0, 1, 2, …
```

Local, deterministic, no coordination, and the id stays well-formed. This turns a
probability into a load factor. Measured on this repo — 78 active days, mean 9.9
items a day, **busiest day 35** — a re-hash essentially never happens; even a
hypothetical factory minting one item per second (86,400 a day) would re-hash
about 111 times out of 86,400, or 0.13% of mints, and effectively never twice.

**The attempt counter must not break idempotent retry.** When attempt 0 is
occupied, compare the occupant: same author, same `created`, same description
means it **is** this item, written by a half-finished earlier run, so the mint
succeeds with that id. Advance the attempt only when the occupant is genuinely a
different item. Both properties survive, and the check that reconciles them is one
comparison.

**The time component is a tunable partition, and that is the scaling lever.** Two
items can only collide if they share a partition, so the partition's resolution
should track the creation rate: a project filing ten a day wants `YYYYMMDD`; one
filing one a second wants `YYYYMMDDThh` or finer. This is not primarily about
collisions — at one per second the *directory* fails first, at 86,400 files in
`open/` and 31 million a year, and `ItemPerFileStore` holds a block model of each.
Widening the partition fixes both axes at once: day → hour costs three characters
and buys 24× on directory size and 24× on collision scope together. **The fix for
scale is a finer time, never a longer hash.**

**Two writers who have not synced are the only undetectable case**, and it is
§6.6's subject.

**Typing it: one resolution ladder, any fragment.** The full id is 37 characters
and nobody will type it. Every part is separately addressable, and a reference is
resolved by trying each reading and requiring exactly one match:

| you write | reading |
| --- | --- |
| `WI-K7M2Q` | hash, or any unambiguous prefix of one |
| `WI-20260817-K7M2Q` | time-hash — the stable machine handle |
| `WI-item-per-file-store` | slug, or an unambiguous prefix of one |
| `WI-20260817-K7M2Q-item-per-file-store` | the whole thing, as stored |

Ambiguity is not resolved by precedence — it is **reported**, with the candidates,
the way git reports an ambiguous object name. A slug is *not unique* (two items may
both be `fix-flaky-test`), and neither is a four-character hash prefix forever, so
one mechanism handles both and there is no rule about which reading wins.

**`WI-` is the reference marker, and that matters most in prose.** Feedback text
mentions other items constantly — this document's own tracker has thousands of such
mentions — and a bare `item-per-file-store` appearing in a sentence is a phrase, not
a citation. Keeping the prefix means a reference stays greppable and linkifiable
exactly as `WI-1114` is today, while everything after it is a resolvable fragment
rather than a fixed number. The `depends_on` field stores the full id; prose stores
whatever the author typed.

**Why the time is in it at all**, given it costs nine characters. `WI-1114` is not
valuable because it is short; it is valuable because it is **monotone** — you can
see at a glance that WI-1114 came after WI-437, and people use that constantly. A
bare hash destroys that, and putting the time first restores it *lexicographically*,
so `ls`, a sorted `depends_on`, and a plain `sort` all read chronologically with no
comparator that knows anything.

**It needs a `created` field on `WorkItem`, and that is a real prerequisite.** The
entity has none today — `status` carries `since`/`at` for some variants and `Open`
carries nothing — so there is no creation timestamp to hash, and, once ids stop
being ordered, nothing for `list` to sort by. The chronological order the tracker
shows today is an *accident* of ids being dense and ascending. Adding `created`
pays for both.

**Existing ids are grandfathered, never renumbered.** `WI-1114` appears in 4,700+
feedback texts, in commit messages, in branch names, in conversations. Renumbering
the 1110 existing items would break every one of those references to buy nothing.
So two id shapes coexist permanently, and every site that reads an id must stay
shape-agnostic — the id is already a `String`, and WI-1114's `check_segment` cares
only that it names one path component. The one site that parses digits is the
counter seed in `main.rs`, which this policy deletes outright.

**What it removes.** All of §6.1's retry loop, §6.2's `External` row on `alloc_id`
(minting becomes a pure function of values the bundle holds), §6.3's failure
taxonomy, §6.4's provisional ids, §6.4's honest cost about references escaping
before they are permanent (there is no "before"), §10's dangling-allocation check,
and §8.3's counter seeding. Of §8.3's five-point substitution contract, three
points (atomic ordered creation, title search reaching arbitrarily old entries,
live newest-first listing) exist only to serve allocation; a mirror-only forge
needs the other two.

**Correction to the above, 2026-08-17:** an earlier draft of this section claimed
it also removes §6.4's **reconciliation** — the rename plus `depends_on` rewrite.
It does not. It *demotes* it: from machinery every offline `add` needs, to a repair
run when two unsynced writers collide (§6.6). That is still a large win, and the
rare path can be far simpler than the routine one, but the machinery does not
vanish and this document should not have said it did.

**And it changes what the forge IS.** Under this policy `access: disabled()`
degrades *nothing* — today it degrades `add` to a provisional id. The forge
becomes a pure publishing channel: §7 survives whole, §6.0–§6.4 become optional,
and the null forge is a first-class configuration rather than a test fixture.

**What is lost.** Density — ids stop being consecutive, and there is no "next"
number. And the registry-as-external-truth: a stale checkout can no longer ask
GitHub what has been allocated, because allocation leaves no trace outside the
tree. That second one is the only loss with teeth, and it is the price of not
needing the network. Sayability was the third, and the slug buys it back.

### 6.6 When two unsynced writers mint the same id

**Added 2026-08-17.** §6.5 makes a single writer collision-proof. Two writers who
have not synced cannot check each other's trees, so this is the one case that
reaches disk. It is rare — the exposure is not a day's items but the handful
created independently before a merge — and everything below is about making it
*loud and convergent* rather than about making it rarer.

**Git will usually not conflict, and that is the whole difficulty.** The two items
have different descriptions, so different slugs, so **different filenames**:

```
open/WI-20260817-K7M2Q-alpha-thing.anthill.md     ← alice
open/WI-20260817-K7M2Q-beta-thing.anthill.md      ← bob
```

Git merges that perfectly cleanly. No conflict, no markers, exit 0. Nothing at the
VCS or filesystem level can notice, because at that level nothing is wrong — two
distinct paths were added. **The tracker is therefore the only possible detector**,
and it detects by comparing the `<time>-<hash>` identity prefix (§6.5), never the
whole id string, which the differing slugs would hide.

This also settles the mechanism. It cannot be a git merge driver or a merge hook:
the case that matters never reaches them, and §12 already notes that hooks are
invisible and easily uninstalled. It is the ordinary load-time check every command
already runs (WI-1114), which refuses on a blocking fault and names the remedy.

**It is a different fault from a duplicate id, with the opposite remedy.** §10's
`DuplicateId` says one file is debris from an interrupted move and refuses to pick.
A hash collision is two *real* items, and the remedy is to renumber one — so they
must be separate faults. They are mechanically distinguishable:

| the two files hold | cause | remedy |
| --- | --- | --- |
| the **same** item (same author, `created`, description) | interrupted move | delete one — cannot auto-pick |
| **different** items | hash collision | renumber the loser — *can* auto-pick |

**`fsck --renumber` proposes and applies the repair.** It is deliberately not part
of `--fix`: that verb moves a file to match its fact, where the fact is
authoritative and the direction settled, while this one changes an **identity**.
Different blast radius, different verb.

**The loser is chosen by a deterministic total order, and this is the load-bearing
requirement.** Both checkouts must reach the same answer without talking, or the
repair turns one collision into a second, worse divergence. The order is: later
`created` loses; ties break on author, then on the full description. Re-minting is
itself deterministic (§6.5's attempt counter), so two checkouts resolving
independently produce **byte-identical trees**, and git then merges the two
independent fixes with no conflict — because both sides made the same change.
`--renumber <id>` overrides which side loses, for when one has already escaped
into commit messages.

**What it rewrites, and what it refuses to.** The loser's filename, its `id:`
field, its satellites' `workitem:` fields (same file, so §5.1's relocation carries
them), and every `depends_on` entry in the tree. It does **not** rewrite prose: a
`WI-…` in feedback text or a commit message may legitimately mean the winner, so
those are *reported*, with locations. The same honest limit §6.4 states for
provisional ids, now on a rare path instead of every offline `add`.

**Where git does conflict**, the two items share a slug as well, so they share a
path and git leaves markers in the file. That file then fails to parse and is
warned-and-skipped by the loader — safe, because WI-1114's
`refuse_unknown_occupant` will not write over a file the store never read, but
unhelpful. Recognizing conflict markers specifically, and saying so, costs almost
nothing and is far more actionable than a generic parse error.

## 7. The mirror — demoted to import / export

> **Amended 2026-08-17.** §7 was written as a *continuously reconciled* mirror:
> `sync` keeps issues in step, ingests comments as feedback, honours a close as a
> verify gesture, and detects drift in every other direction. That is now a
> **future extension**, and what ships instead — when anything does — is two
> one-shot commands:
>
> * **`export`** — write the tracker's current state to the forge. Idempotent,
>   keyed by `MirrorEntry`, and **unconditionally tracker-wins**.
> * **`import`** — pull comments back in as `Feedback`, for review before they land.
>
> **What that collapses, and it is most of the section.** §7.2's
> "reconciliation, not write-through" exists because `sync` tried to be
> bidirectional-ish; export has one direction, settled, so reconciliation becomes
> a loop that overwrites. §7.4's close-as-verify — an *event* honoured in exactly
> one legal transition and re-derived otherwise, with a drift report for every
> other case — collapses entirely. §10's "permanent-id item with no `MirrorEntry`"
> check goes with it, since export creates the link as it goes and there is no
> continuous invariant to violate. §7.3's ingest-once bookkeeping softens to a
> cheap dedup on `(author, at)`, because import is reviewed rather than automatic.
>
> **What it costs** is that a GitHub reader sees the last export, not live state.
> Running `export` from CI on `main` recovers most of that for free — precisely
> *because* it is idempotent and tracker-wins, so there is no drift machinery to
> get wrong.
>
> Everything below is the continuously-reconciled design, kept as the record of
> what a future extension would have to handle. §7.1's issue *content* is the part
> that survives unchanged: export writes exactly that.

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

#### 8.2.2 It is not the *carrier* that is missing (WI-1114, measured)

Increment 2 took the restructuring above and found the diagnosis one step short. The
paragraph says `WorkItemStore` needs "a carrier sort that provides it rather than a bare
instance fact" — but **it already has one**. `sort FileBasedWorkitemStore` declares
`provides WorkItemStore[State = WIS]`; the `fact WorkItemStore[State = WIS]` spelling the
table cites is not what `store.anthill` contains. What the carrier lacks is a *value*: it
declares no `entity` of its own, only the nested `enum WIS`, so the body of
`-> C ensures WorkItemStore[C]` had nothing of that sort to return and handed back a `WIS`
— which is the measured mismatch, read correctly.

Giving it one does not help, and this is the finding. `detect_existential_carrier` rewrites
the return type to *the spec with the carrier slot dropped*, so the body must return a value
whose **sort provides the spec** — a `FileBasedWorkitemStore` token. That token carries no
state. The caller would hold a dictionary and still have nothing to put in the `Cell`, and
the host's remaining job — building the initial `wis(backend:, id_counter:)` — would be
exactly where it was. The doc's own `-> C ensures WorkItemStore[State = C]` asks for the
existential over the **member**, which is what would actually be useful here and is a
different feature from WI-402's carrier existential; it is not detected, and that is why.

Expressing it in the supported form means making `State` *be* the carrier: ops written over
`Cell[V = WorkItemStore]`, satisfaction spelled `sort WIS { provides WorkItemStore }`. That
inverts the state-parameterization proposal 036 / WI-203 chose — fifteen signatures,
`sort Main`'s `sort State = ? / requires WorkItemStore[State]`, and every `cmd_*`'s
`Cell[State]`. It is a redesign of the store spec, not an increment of one, and it would
dismantle the `requires` mechanism §8.2 correctly identifies as *already doing the
selection*.

**What shipped instead, and it removes the coupling §8.2 named.**
`FileBasedWorkitemStore.open(backend: NonMonotonicStore, next: Int64) -> WIS`. The host
calls it in place of interning `anthill.todo.store.FileBasedWorkitemStore.wis` and its
`backend` / `id_counter` field names, so the shape of the state is the impl's business
alone — which is the prerequisite for a second `WorkItemStore` impl (§8.1's
`CoordinatedWorkitemStore`) to be substitutable at all. It lives on the **impl**, not the
spec: a state factory's parameters are the impl's own, and under coordination the counter
parameter disappears entirely (§8.3), so a spec-level `open(backend, next)` would freeze
one impl's parameter list across every future one.

The host still names the impl. It always did — the same symbol it pins into `chain_dicts`
— and that is the legitimate native step, not the coupling.

**Where this leaves WI-402.** Its existential half still has no in-tree consumer, and this
design is no longer the candidate: its selection is done by `requires`, and the factory it
wanted returns a *state*, not a carrier. That is a finding about WI-402's shape — a carrier
existential fits a spec whose value IS its carrier (the `KVStore` fixture), and does not
fit a spec parameterized by the value — and it belongs on WI-402, not here.

The second change §8.1 asks for landed with it: `WIS.backend` is typed
`NonMonotonicStore`, the algebra the impl actually consumes, rather than
`IndexedFileStore`. Typed by one backend it was, that field alone made the whole impl
unusable with the second store — declarable in a binding, buildable by the host, and a
load error here. It is deliberately not `QueryableStore`: nothing in this impl calls
`retrieve` (every read goes through `facts_of(kb(), …)`), and requiring it would refuse a
good backend for an operation never performed.

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
  the file to match the fact (the fact wins; §4). **Delivered (WI-1114)**, and the check
  is on the whole path, not the directory alone: `open/WI-9.anthill` holding
  `id: "WI-10"` is the same class of disagreement and the same repair.
* **Duplicate id** — the same id in two files, holding the **same item** → loud
  load error. **Delivered (WI-1114)**; `fsck --fix` reports it and does *not* pick a
  winner, because which file is the item is a real disagreement and only whoever
  interrupted the move knows.
* **Id collision** — the same `<time>-<hash>` in two files holding **different
  items** (§6.6). A separate fault from the above, because the remedy is the
  opposite one — renumber, do not delete — and the two are told apart by whether
  the files' author / `created` / description agree. Compared on the identity
  PREFIX, never the whole id: the colliding items have different slugs, hence
  different filenames, and a whole-string comparison misses every case.
  `fsck --renumber` repairs it, convergently.
* **Unresolved merge markers in an item file** — reported as such rather than as a
  generic parse failure. The loader already warns and skips an unparseable file and
  the store already refuses to write over one it never read, so this is a
  diagnostic improvement, not a safety one.
* **A file holding several items** — the shared-file layout read by a store that gives
  each item a file. Added (WI-1114) after review found the destructive alternative: read
  as *N misplaced items*, it produced N path disagreements naming one file, and `--fix`
  renamed that whole file to the first item's path and lost the rest. It is now one
  fault about the file's SHAPE, it blocks, and `fsck` refuses it by name — splitting a
  shared file is §11's `migrate`, not a repair. This is precisely the state of a project
  that declares the binding before migrating into it, so the command it is told to run
  must not make things worse.
* **A row the store cannot place** — a hand-edited `status` that is a string rather than
  a variant, say. **Delivered (WI-1114)**, and REPORTED rather than raised: `fsck` needs
  the store built before it can say anything, so raising it while seeding would kill the
  one command written to diagnose it.
* **Dangling reference** — a `depends_on` naming an id with no file (e.g. a
  half-reconciled provisional rename, §6.4) → named by `fsck`; for the
  reconciliation case a `sync` re-run repairs it.
* **Permanent-id item with no `MirrorEntry` fact**, under a declared `Mirror` → loud
  in `sync` (migration incomplete, or an `add` died between steps 4 and 5).
  Provisional items lack the fact by definition and are reported as *unreconciled*,
  with a count — expected state, not an error.
* **Issue claiming an id with no file** → reported by `sync` as a dangling
  allocation (§6.3) — distinguished from `[deleted]`-tombstoned issues (§7.2),
  which are the *expected* end state of a deletion.

**Which of these BLOCK, and why the split is where it is (WI-1114).** A fault that
leaves the store's own *routing* ambiguous blocks every command — two files claiming one
key, a file whose path denies its fact, a row the store cannot place at all, a file that
is several items — because the next write would have to guess which one it means. A fault
that merely strands a row is reported and does not stand between the user and the
tracker: deleting an item leaves its append-only feedback behind *by design* (`Feedback`
is `monotone`, so it cannot be retracted), and refusing every later command over an
expected state would be a check punishing the thing it was written to describe.

**`fsck` validates its whole plan before moving a byte**, and refuses rather than
half-repairing: a repair that renames files cannot discover its own refusal partway
through and leave a tree nobody asked for. What it will not do — choose between two files
claiming one id, split a file holding several items, guess where an unreadable row
belongs — it says, rather than attempting.

**A backend with no layout to check refuses `fsck`, in both its forms.** Silence is a
correct answer to "is anything wrong?" (the startup gate) and a wrong answer to "check
this layout", which a shared-file store cannot do at all. Reporting `layout ok` there
would be the silent skip this section exists to prevent.

## 11. Migration

```bash
anthill-todo migrate --to github-coordinated
```

1. Explode `workitems.anthill` into one file per item under `<state>/`, each carrying
   its item's `Feedback` and `Tag` facts. Pure local rewrite; reviewable as one commit
   (a large one, and a one-time one). **The file format is whatever §5.3 has settled by
   the time this runs** — this repo's tracker migrates exactly once, so WI-1120 lands
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
3. Rewrite the `ExtentBinding` store term to `ItemPerFileStore(...)`, and add `fact Mirror(...)` in `project.anthill` if the tracker is to be published (§3).
4. Stamp `StoreFormat(version: 2)` through the store, the way `migrate` already
   stamps version 1 (WI-434).

Migration runs in the working tree and is pushed as one commit when it completes.
An interruption is local — step 2 resumes — and other checkouts never observe a
half-migrated state: they see the old layout or the new one, atomically, the way
git always publishes.

The two axes stay orthogonal: `ExtentBinding` says *which layout*, `StoreFormat` versions
the *schema within* it. The version check in `main.anthill`
(`check_store_versions`) keeps working unchanged.

**The id scheme must be settled before this runs (2026-08-17).** Step 1's file
names and step 2's issue titles both carry ids, and this repo's tracker migrates
**exactly once** — the same argument that put §5.3's file format ahead of
migration puts §6.5's id shape there too. Under `ContentHash` the existing 1110
ids are grandfathered, so migration does not renumber; what it must know is
whether a `created` field exists to write, and which shape *new* ids take
afterwards. Deciding after the migration means migrating twice.

**Migration must BACK-DATE `created` from git history, not stamp the migration
date.** Both readings write a legal field, and the difference is not cosmetic:
stamping one date puts all 1110 items in a single partition, where the §6.5
collision scope is the whole tracker at once rather than a day's work — a coin
flip at 25 bits, against 0.002% at the busiest day this project has actually had.
Back-dating is also simply *true*: those items were created across 78+ days, git
knows when each id first appeared in `workitems.anthill`, and the field should say
so. The recovered dates are approximate — a commit date, not a keystroke — and
that is fine, because `created` is used for ordering and for minting, neither of
which needs better than a day.

Migration is one-way in practice. A `--to local-single-file` inverse is trivial to write
(concatenate the files, drop the `MirrorEntry` facts) and worth having as an escape hatch,
but it abandons the id registry.

## 12. Open questions

* ~~**The slug width.**~~ **Settled at 30** (§6.5), measured on 772 of this
  tracker's own descriptions — the knee of the ambiguity curve, median id 45. The
  whole id shape is now settled: `WI-<YYYYMMDD>-<5 Crockford>-<slug≤30>`. Note the
  hash width was never irreversible either: ids are grandfathered anyway, so if
  five ever proved narrow you would mint six tomorrow and every existing id would
  keep working — the same heterogeneity the `WI-NNN` → `WI-<time>-<hash>`
  transition already requires.
* ~~**Whether the id needs a version marker.**~~ **Settled: no**, and the reasons
  are worth keeping because the impulse recurs. The purpose a marker would serve —
  knowing which rule minted an id — only pays if the rule can be re-run, and §6.5
  settled that it cannot: the hash input includes the description *at creation*,
  which drifts. Parsing does not need it either (legacy `WI-1114` is `WI-` plus
  pure digits, the new form `WI-` plus eight digits plus `-`, and any third scheme
  would be shaped distinguishably because one chooses its shape). Nor does a width
  change: a 5-character hash never equals a 6-character one, which is the right
  answer since they are different ids, and the ladder's prefix matching spans both.
  And **the date is already a soft era marker for free** — ids are chronological,
  so "everything from this date uses scheme 2" is a one-line table.

  Against it: a character in every id forever, in every filename and every
  `depends_on` entry, in the one segment this design fights to keep legible — and,
  more sharply, **a version marker on an opaque token advertises a decodability
  this design deliberately does not offer.** Stamping `v1` implies a promise to
  interpret `v1` later; there is nothing to interpret, and saying otherwise invites
  exactly the re-derivation check §6.5 warns will rot.

  **The right home for the question is `StoreFormat(version:)`** (WI-434), which
  already exists, already gates the tracker, and is already stamped by migration
  (§11 step 4). A minting-scheme change is a store-format change: one fact for the
  whole tracker, rather than a character in 1112 ids and every reference to them.
* **Whether destructive commands should echo what they resolved.** A mistyped
  fragment hits a *different* real item about once in 30,000 at 25 bits (§6.5's
  sparseness argument), which is comfortable for `show` and less so for `delete`.
  Echoing the resolved item's description before acting costs a line of output and
  removes the question; the argument against is that it makes the common case
  chattier.
* ~~**Whether `StakeByCreation` is worth keeping at all.**~~ **Settled: no,
  retired unbuilt** (§6.0). Its one irreplaceable property — a registry visible to
  a stale or shallow checkout — is a nicety, since `ContentHash` handles collisions
  by detection and convergent repair rather than prevention. Retiring spec that was
  never implemented costs nothing, and the analysis stays on the page.
* ~~**Whether `Coordination` should keep an `allocation` field.**~~ **Settled: no**
  (§3.2). One policy means the field would be a seam with a single implementation,
  and what remains describes only the mirror — so the fact is `Mirror`, and the
  field it carries is `target` rather than `forge`, because an export target need
  not be a forge. The *split* that made allocation local had already delivered its
  value; the seam was its residue.
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
| 2 | WI-1114 | **`ItemPerFileStore`. DELIVERED.** The new `Store` implementation (§5.2, §5.2.1), the relocation rule, the per-backend host wiring arm, `fsck`, loader coverage, tests against a null forge. The store-spec change came out narrower than §8.2.1 predicted and `open_store` did not survive the measurement — §8.2.2 records what shipped in its place (`FileBasedWorkitemStore.open`, and `WIS.backend` typed by the spec) and why the WI-402 existential does not fit this spec's shape. | conflict-free multi-dev on *state changes* |
| 2b | WI-1120 | **Work items are documents** (§5.3). The declared fact↔markdown mapping (§5.3 rules, §5.4 artifact): `WI-NNN.anthill.md`, anthill head in a fenced block, prose chapters, repeated chapters for feedback, eight malformed-editing rules. Separate from row 2 per §14.1 — bundled, a format bug would mask a store bug on the tracker we are running on. (Not because of the loader glob: row 2 already carries loader coverage.) Blocks row 6 — the live tracker migrates once, into the final format. | items readable and editable as documents |
| 2c | WI-1121 | **Allocation is a policy, and `ContentHash` is the local one** (§3.2, §6.5, §6.6). `fact Mirror(target:, access:)` replacing `Coordination` (no allocation field — one policy is not a seam), the `created` field on `WorkItem`, the three-part Crockford-base32 id, the attempt counter, the resolution ladder, the identity-prefix duplicate check, `fsck --renumber`, `MirrorEntry(workitem:, target:, entry: String)` as a SET, grandfathered legacy ids. **Reorders what follows**: this alone closes the §1 id-collision half with no network, so rows 3–5 stop being on the critical path to the umbrella's shipping value. Blocks row 6 — the tracker migrates once, and ids are part of what it migrates into. | collision-free `add`, offline, no forge |
| 3 | WI-1115 | **`Forge` carrier.** The embedder host-fn prerequisite (§8.3), the `Forge` sort + contract, its `provides`/`operation_map` bindings, the `gh` and fake implementations. Now serves EXPORT/IMPORT only, so it shrinks hard: create/update an entry, list entries, list comments. `fresh_token` is unneeded under `ContentHash`; `retitle`, `close`/`reopen`-for-retreat and `entries_titled` were §6.1's and go with it. | nothing alone; testable |
| ~~4~~ | ~~WI-1116~~ | ~~**Coordinated `add`**~~ — **retired unbuilt** (§6.0, §12). `MirrorEntry` moves to row 5, where the mirror is. | — |
| 5 | WI-1117 | **`export` / `import`** (§7, amended). Export writes the tracker's state to the forge, idempotent and tracker-wins, creating `MirrorEntry` as it goes; import pulls comments back as `Feedback` for review. The continuously-reconciled `sync` — drift detection, close-as-verify, tombstones, `--check` as a CI gate — is a future extension, not this row. | a published snapshot + a return channel |
| 6 | WI-1118 | **`migrate`.** Resumable, idempotent. Waits on 2b (file format) and 2c (id shape) — the tracker migrates exactly once, into the final form of both. | this repo's own tracker moves |

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
