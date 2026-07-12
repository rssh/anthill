# Pluggable backends: the GitHub-coordinated store

**Work item:** WI-437 (depends WI-009 delivered, WI-402 delivered)
**Status:** design
**Supersedes:** `examples/github-todo/docs/pluggable-backend.md` (the original three-line sketch)

## 1. The problem

`anthill-todo` keeps every fact in one file. This repo's tracker is
`anthill-todo/workitems.anthill` — 3675 lines, holding every `WorkItem`, every
`Feedback`, every `Tag`. That works perfectly for one developer and fails for
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
available as a future `BackendKind`; it is simply not what is designed here.

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

## 3. Configuration: the backend fact

The project declares its backend as a fact in `anthill-todo/project.anthill`,
alongside the existing `fact Project(...)`:

```anthill
fact StoreBackend(
  kind: GithubCoordinated(
    repo:    "rssh/anthill",
    root:    "anthill-todo",
    project: some(value: "Anthill Roadmap"),
    access:  Enabled))
```

The entities live in the **bundled** `anthill.stage0` domain, in a new
`rustland/anthill-todo/anthill/backend.anthill`:

```anthill
namespace anthill.stage0

  entity StoreBackend(kind: BackendKind)

  enum BackendKind
    -- Today's layout: every fact in one file under the project root.
    entity LocalSingleFile(file: String)

    -- State directories + file-per-item, with GitHub issue mirroring
    -- and GitHub-allocated permanent ids.
    entity GithubCoordinated(
      repo    : String,                  -- "owner/name" hosting the mirror issues
      root    : String,                  -- project dir holding the state directories
      project : Option[T = String],      -- optional GitHub Project (board) to file issues into
      access  : GithubAccess)
  end

  -- Whether to TALK to GitHub at all: attempt allocation on `add`, push the
  -- mirror on `sync`. The fact is the project-wide DEFAULT; a single checkout
  -- overrides it with ANTHILL_TODO_GITHUB=on|off (or --offline) — CI test
  -- jobs, air-gapped machines, and fork checkouts without write access run
  -- off. Disabled does not disable the tracker: every command still works,
  -- `add` allocates a provisional id (§6.4), and a later `sync` from an
  -- enabled checkout reconciles. What Disabled removes is the synchronous
  -- attempt, never the work.
  enum GithubAccess
    entity Enabled
    entity Disabled
  end

end
```

Bundling the entities (rather than expecting a per-project `domain.anthill`) follows
the `StoreFormat` precedent in `version.anthill`: a project's own domain may predate
the entity, and an unresolved import fails the *whole* bundle load — on exactly the
projects that most need the new code path. See WI-505/WI-684.

**Default.** An absent `StoreBackend` fact means
`LocalSingleFile(file: "workitems.anthill")`. Every existing project keeps working
untouched, with no migration. `init` writes the fact explicitly from now on, so new
projects state their layout rather than inheriting it.

**Why two variants and not three.** A state-directory layout *without* GitHub is a
perfectly coherent configuration, and it is what the test suite will run against.
It is deliberately not a config variant: the mirror is an injectable component
(§8.3), and tests instantiate the directory layout with a null mirror. Keeping the
user-facing config two-valued means every project that uses state directories is
also coordinated — which is the point, since directories alone fix conflicts but not
id collisions.

## 4. On-disk layout: a directory per state, a file per item

```
anthill-todo/
  project.anthill              fact Project(...) + fact StoreBackend(...)
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

Each `WI-NNN.anthill` holds **every fact about that item**:

```anthill
-- anthill-todo/claimed/WI-688.anthill
fact WorkItem(
  id: "WI-688",
  description: some(value: "whole-`step` direct derivation ..."),
  acceptance: [ToolPasses(tool: "cargo-test", params: none)],
  depends_on: some(value: ["WI-686", "WI-687"]),
  status: Claimed(agent: "claude", since: "2026-07-10T09:12:44Z"))

fact GithubIssue(workitem: "WI-688", number: 1234)

fact Tag(workitem: "WI-688", name: "prover")

fact Feedback(workitem: "WI-688", author: "user",
  content: "both deferrals landed; substrate should suffice",
  at: "2026-07-10T11:02:10Z")
```

`GithubIssue` is a new fact (in `backend.anthill`, next to `StoreBackend`), keyed on
the work-item id — the same additive shape as `Tag`. It records the mirror link
*without* touching the `WorkItem` entity, so the stage0 domain stays backend-neutral
and a `LocalSingleFile` project never sees the field.

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

Under the single-file convention both operations resolve to the same path and the
flush rewrites one block in place. Under state directories the retract and the
persist resolve to *different* paths — and the host store recognizes exactly this
pattern:

> **Relocation rule.** When one flush contains a retract and a persist of the same
> primary key whose file paths differ, it is executed as a **file move**: the source
> file is renamed to the destination path and the item's fact block is rewritten in
> place. Every other block in that file (feedback, tags, the `GithubIssue` link)
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

## 6. Id allocation: the issue *is* the allocation

Under `GithubCoordinated`, **permanent ids come only from GitHub**, and issue
creation is the allocation event. GitHub's issue counter is a monotone,
atomically-incremented, globally-visible sequence — exactly the shared resource
git lacks. `add` itself never *waits* on GitHub, though: when the network or a
token is missing it allocates a *provisional* id and `sync` finishes the naming
later (§6.4). What is forbidden is only the §1 failure: minting a dense `WI-<n>`
from local state alone.

The direct mapping *id := `WI-<issue number>`* would be simpler, and is right for a
fresh project whose tracker owns the repo's counter from issue #1. It does not fit an
existing one: GitHub shares one counter between issues and pull requests, and this
repo already holds ~690 dense ids that would collide with the first ~690 fresh issue
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

Every step below is tagged with the `Mirror` operation (§8.3) it invokes;
`[github]` steps are network calls, `[local]` steps touch only the working tree.

```
add(description):

  ── allocate ──────────────────────────────────────────────────────────────────
  1. [github]  Mirror.recent_issues(limit: 30)   -- list endpoint, newest-first,
     [local]   candidate := max( ids claimed in that page         open AND closed
                                 ∪ ids of local item files ) + 1
  2. [github]  Mirror.create_issue("WI-<candidate>: <summary>", body: "(allocating)")
                                                       → issue #N    [atomic stake]
  3. [github]  claims := Mirror.recent_issues(limit: 30)
                       ∪ Mirror.issues_titled("WI-<candidate>:")
     [local]   if any issue #M < N claims candidate:          -- we lost the race
                   [github] Mirror.retreat(N)     -- retitle off the id + close
                   candidate := max( ids in claims
                                     ∪ ids of local item files ) + 1;  goto 2
                                                                [claim committed]

  ── write (git is the truth; after this the item exists) ───────────────────────
  4. [local]   write anthill-todo/open/WI-<candidate>.anthill, containing
                   fact WorkItem(id: "WI-<candidate>", …, status: Open)
                   fact GithubIssue(workitem: "WI-<candidate>", number: N)
                   fact Tag(…) for each --tag

  ── reconcile (best-effort; `sync` redoes it) ─────────────────────────────────
  5. [github]  Mirror.set_body(N, <pointer to the file, §7.1>)
     [github]  Mirror.add_to_project(N, <cfg.project>)          -- if configured
```

**Cost: three small calls on the happy path, none of them O(repo).** Step 1 is one
page from the list endpoint; step 3 re-reads that page and adds one exact-title
search; step 2 is `gh issue create`. The GitHub-backed `Mirror` carrier (§8.3)
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
    -- the Mirror carrier's business (§8.3), not the row's.
    operation alloc_id(s: Cell[V = State], summary: String) -> String
      effects {Modify[s], External, Error}
```

| protocol | spec operation | file-backed impl | github-coordinated impl |
| --- | --- | --- | --- |
| steps 1–3 | `alloc_id(s, summary)` | ignores `summary`; reads and bumps the local counter | reads the registry, stakes the claim by creating the issue, retreats and retries on a lost race; mints a provisional id when GitHub is out of reach (§6.4) |
| step 4 | `commit(s, w)` | persist + flush | persist + flush into `<state>/<id>.anthill`, plus the `GithubIssue` fact when the allocation produced one |
| step 5 | `commit(s, w)`, tail | — | `set_body` + `add_to_project`, best-effort |

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
`fact GithubIssue(workitem: id, number: N)` for a freshly allocated permanent id, but
`N` is a GitHub concept and the spec is backend-neutral. It rides in the store's own
`State` instead: the coordinated impl's `alloc_id` stashes the pending
`(id, issue number)` in the cell, and its `commit` reads it back out — persisting the
`GithubIssue` fact in the *same flush* as the item, so the two land in the item's
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
   `Feedback`/`Tag` facts (they live in the same file), a new `GithubIssue`
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
  Tracked in [`anthill-todo/open/WI-690.anthill`](https://github.com/rssh/anthill/blob/main/anthill-todo/open/WI-690.anthill).

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
`State = WIS` and the bodies. A second impl — `GithubCoordinatedWorkitemStore` with its
own `State` — slots in beside it, and every read and mutation the CLI performs is
already an operation of the spec.

The spec changes in exactly two places, both described in §6.2: `next_id(s)` becomes
`alloc_id(s, summary)` with `effects {Modify[s], External, Error}`, and `External`
joins `commit`'s row (its coordinated body writes the `GithubIssue` fact and runs the
best-effort tail). Allocation is the one thing the two backends do *differently in
kind* rather than differently in mechanism — a counter bump versus an optimistic,
retried stake — so it is the thing the interface has to be honest about. Everything
else (`replace`, `lookup`, …) keeps its signature; the coordinated impl differs only
in where its bytes land and whether it also pokes the mirror.

### 8.2 Selection: the WI-402 existential factory

Backend selection is the factory shape from `docs/design/path-dependent-types.md` §5,
and it is the **first real consumer** of WI-402's existential half (delivered):

```anthill
operation open_store(cfg: BackendKind) -> C ensures WorkItemStore[State = C]
  effects {Error}
=
  match cfg
    case LocalSingleFile(f)     -> open_file_store(f)
    case GithubCoordinated(...) -> open_github_coordinated_store(...)
```

The `ensures` manifest roots the abstract carrier `C` back at the interface, so the
result is usable at the call site without escaping. WI-200 (multi-instance `Modify`
state) is **not** needed: one backend instance per CLI invocation, and distinct
backend sorts occupy distinct slots.

Two consequences from WI-402's delivery notes:

* **Call sites must use the qualified form** — a bare call to a body-less spec operation
  (`lookup(s, id)`) does not resolve through an existentially-typed receiver, while
  `WorkItemStore.lookup(s, id)` does. **This is already true of the code**: 43 of
  `main.anthill`'s 44 spec-op call sites are written `WorkItemStore.op(…)`. The single
  exception is the bare `stamp_format(s, current_store_format())` at `main.anthill:2837`,
  which needs one line changed. So this consequence costs a one-line fix, not a sweep.
* **`main` must stop being typed on `FileStore`.** Today's signature is
  `main(args, store: FileStore, wis_cell: Cell[State], agent)`, with the concrete
  `FileStore` threaded through `dispatch` into every `cmd_*`. It is now *vestigial* —
  no body calls `persist`/`retract`/`flush` on it any more; all mutation goes through
  the spec ops on the cell. But you cannot swap a backend while a concrete `FileStore`
  is in `main`'s type, so dropping the parameter (and its `Modify[store]` effect) is
  the true prerequisite. It is a pure deletion, and it is worth landing on its own.

### 8.3 Host side

* **`FileConvention::StateDirs`** in `anthill-core`'s `file_store.rs`, alongside
  `Flat` / `ByDomain` / `SingleFile`. This is more than a new enum variant: today's
  `fact_path(kb, sort, domain)` is *content-blind*, and StateDirs routing is
  content-driven — a `WorkItem` goes to `<status_dir>/<id>.anthill` (the status
  field picks the directory) and `Feedback` / `Tag` / `GithubIssue` go to the file
  of the item they name (an index lookup by the referencing field). So `fact_path`
  grows access to the fact term and to the store's index. The variant is
  parameterized — `StateDirs { root, status_field: "status", id_field: "id",
  ref_field: "workitem" }` — so `anthill-core` persistence stays domain-neutral and
  stage0's field names live in the todo CLI's configuration of it, not in the
  library. `IndexedFileStore` gains the relocation rule of §5.1. The loader needs
  no change: `collect_anthill_files` already recurses.
* **A `Mirror` carrier** — an opaque host sort held in the coordinated impl's
  `State`, on the `IndexedFileStore` precedent. It is a *value*, not a new
  effect: authority is possession (the bundle cannot touch the registry without
  holding the carrier), and the §8.2 factory decides which implementation a run
  holds. Its mutators carry `{Modify[m], External, Error}` and its reads
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
  and lives in the carrier. Operations: `create_issue`,
  `recent_issues` (the newest page — list endpoint, open+closed), `issues_titled`
  (exact-title search: the §6.1 old-claimant leg), `retitle`, `set_body`,
  `close` / `reopen`, `issue_comments` / `close_info` (since-cursor comment
  listing + close state/actor, for §7.3–§7.4),
  `add_to_project` (§6.1's `retreat` = `retitle` + `close`).
* **GitHub is one implementation of the carrier, not its definition.**
  Everything above it — the §6.1 allocator, §6.4 reconciliation, all of §7 —
  consumes only the carrier's contract, so substituting GitLab, Gitea, or a
  plain coordination service is a new carrier implementation plus a
  `BackendKind` variant, with zero change to the bundle. The contract a
  substitute must honor — §6.1's soundness consumes exactly these five things:
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
  unauthenticated, or with `access: Disabled`, it mints a *provisional* id (§6.4) —
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
* **Permanent-id item with no `GithubIssue` fact**, under `GithubCoordinated` → loud
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

1. Explode `workitems.anthill` into `<state>/WI-NNN.anthill`, each carrying its item's
   `Feedback` and `Tag` facts. Pure local rewrite; reviewable as one commit
   (a large one, and a one-time one).
2. Create one mirror issue per item, in id order, each *born* with its `WI-NNN:`
   title (§6.1 — migration is allocation where the winner is known in advance),
   then immediately closed when its item is terminal (§7.1). **Every item is
   mirrored, terminal ones included.** The GitHub view is trustworthy only if
   open/closed reflects the whole tracker: under a partial backfill a missing
   issue is ambiguous — unmigrated, deleted, or never existed — and the §10
   "permanent-id item with no `GithubIssue` fact" check would need a permanent
   exemption for terminal items, gutting it. Full mirroring keeps one uniform
   invariant — every permanent id has exactly one issue, and the issue's
   open/closed state is the item's coarse state. The cost is one-time: ~690
   creations here (~600 of them create-then-close), paced under GitHub's
   secondary rate limits. **Resumable and idempotent**: keyed on the id in the
   title, and each item's file gets its `GithubIssue` fact written as the issue
   is created, so an interrupted run resumes where it stopped.
3. Write `fact StoreBackend(kind: GithubCoordinated(...))` into `project.anthill`.
4. Stamp `StoreFormat(version: 2)` through the store, the way `migrate` already
   stamps version 1 (WI-434).

Migration runs in the working tree and is pushed as one commit when it completes.
An interruption is local — step 2 resumes — and other checkouts never observe a
half-migrated state: they see the old layout or the new one, atomically, the way
git always publishes.

The two axes stay orthogonal: `StoreBackend` says *which layout*, `StoreFormat` versions
the *schema within* it. The version check in `main.anthill`
(`check_store_versions`) keeps working unchanged.

Migration is one-way in practice. A `--to local-single-file` inverse is trivial to write
(concatenate the files, drop the `GithubIssue` facts) and worth having as an escape hatch,
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
  makes drift visible on every description edit. Pointer-only for v1.

## 13. Non-goals

These are the boundaries of *this* backend, not of the design space. `BackendKind` is
open, and each of them is a coherent thing to build later, as another variant over the
same store spec.

* **Work items are not GitHub issues here.** In this backend the issue is a mirror and
  an allocator ticket. A genuinely GitHub-backed store (§2) is a separate `BackendKind`.
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
  standardized remote server) is a future `BackendKind`; this design keeps the store
  spec neutral enough to host it, but builds nothing for it.

## 14. Increments

Each is independently green and independently useful. Per the "risky work first"
preference, the substrate refactor is first, not last.

| # | Increment | Ships |
| --- | --- | --- |
| 1 | **Store-factory substrate.** Drop the vestigial `store: FileStore` from `main`/`dispatch`; move spec-op call sites to the dotted form; add `fact StoreBackend` (bundled) + `open_store` via the WI-402 existential. Absent fact → today's behavior. | no user-visible change; the seam |
| 2 | **State-directory layout.** `FileConvention::StateDirs`, the relocation rule, `fsck`, loader coverage, tests against a null mirror. | conflict-free multi-dev on *state changes* |
| 3 | **Mirror carrier.** The `External` effect (proposal 054 / WI-698, prerequisite), the `Mirror` carrier sort + contract, `fresh_token`, the `gh` and fake implementations (the fake can force the §6.1 lost-race interleavings). | nothing alone; testable |
| 4 | **Coordinated `add`.** The §6.1 stake-by-creation protocol, the §6.4 provisional fallback, `GithubIssue` facts. | conflict-free **and** collision-free `add`, online or off |
| 5 | **`sync`.** Provisional-id reconciliation (§6.4), allocation-debris repair, comment ingestion (§7.3), close-as-verify (§7.4), the mirror push, deletion tombstones, `--check`, CI gate. | the mirror + the return channels; autonomous mode closes the loop |
| 6 | **`migrate --to github-coordinated`.** Resumable, idempotent. | this repo's own tracker moves |
