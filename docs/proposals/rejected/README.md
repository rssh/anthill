# Rejected proposals

Proposals that were considered and **declined**. They stay in the repository, and
they keep their text: the point of this directory is that a rejection is a
**recorded decision**, not a deletion. A proposal that simply disappears gets
re-proposed a year later by someone who cannot find out why it was dropped.

Distinct from the sibling directories:

| Directory | Meaning |
|---|---|
| `docs/proposals/NNN-….md` | committed, numbered, on the roadmap (or already absorbed by the spec) |
| `docs/proposals/future/` | not yet committed — deferred, deliberately unnumbered |
| `docs/proposals/rejected/` | **declined** — will not be built as written |
| `docs/proposals/library/` | stdlib-library proposals (own sequence) |

## The number travels with the file

A rejected proposal **keeps its main-sequence number in its filename**
(`rejected/NNN-….md`). This is the rule for a reason that is easy to discover
too late: proposals are cited **by number** — from `docs/kernel-language.md`,
from other proposals, and from roughly a thousand work-item descriptions
(`058 §4.9`, `proposal 051 Phase 2`). A number that changed meaning, or a file
that moved out from under its number, would silently falsify text nobody will
re-read.

So: **the number is retired, never reused**, and the directory carries the
verdict. A citation of `NNN` still resolves — to a file that now says, at the
top, that it was declined and why.

This is the **demotion** direction. The **promotion** direction (a `future/`
sketch becoming committed work, taking the next free number) is documented in
[`../future/README.md`](../future/README.md). A proposal moved to `future/`
rather than rejected follows the same number rule for the same reason.

## What a rejected proposal must say

A header at the top of the file, before its original text:

```markdown
> **REJECTED** (WI-NNNN, YYYY-MM-DD). <One paragraph: what was decided instead,
> and what would have to change for this to be reconsidered.>
```

The original text is **kept as written** — the repo rule that a proposal keeps
its own text applies here too. Do not rewrite the body to argue against itself;
the header carries the verdict, the body carries what was proposed.

"What would have to change" is the load-bearing half. *Rejected because the
kernel has no X today* invites the proposal back when X lands; *rejected because
it contradicts the law in §8.3* does not. Say which kind it is.

## Index

_(none yet — the first entries land with the 0.1.0 proposal review, WI-1126.)_
