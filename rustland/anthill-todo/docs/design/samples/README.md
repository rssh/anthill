# Sample items in the proposed document format (WI-K63ZV)

Seven real work items, converted by hand from the current format to the one
described in `../document-mapping.md`, so the rendered page can be judged
rather than argued about.

These are **samples, not items**. They deliberately do not carry the
`.anthill.md` suffix, so no loader will read them, and they live outside the
tracker tree.

| sample | feedback entries | shows |
| --- | --- | --- |
| `WI-714.md` | 17 | the most feedback on the tracker; 8 dependencies |
| `WI-383.md` | 16 | feedback plus a tag |
| `WI-402.md` | 10 | a typical delivered item |
| `WI-1115.md` | 1 | `ProposalRejected` — the reason as a `## Reason` chapter |
| `WI-731.md` | 9 | delivered upstream after conversion; regenerated |
| `WI-20260818-7X7NK-a-projection-over-a-1.md` | 2 | a NEW-STYLE content-hash id, and an empty `depends_on` |
| `WI-090.md` | 0 | the FLOOR: a stub, and the only file with NO `## Changes` at all |

**Nothing here is synthesized.** `## Changes` holds only recorded feedback.
Status entries do not appear because that history does not exist to migrate:
`Delivered(agent, at)` overwrote `Claimed(agent, since)` on 985 of 1127 items, and
`untag` never left a record. Entries still carry their kind — `— feedback —` — so
that status and tag entries are additive when they begin to accumulate, rather than
a fourth rewrite of every file. That is the cost this decision accepts: on WI-714,
seventeen consecutive kind words with nothing yet to distinguish them from.

Originals, for comparison:

    anthill-todo/delivered/WI-714.anthill.md
    anthill-todo/delivered/WI-383.anthill.md
    anthill-todo/delivered/WI-402.anthill.md
    anthill-todo/proposal_rejected/WI-1115.anthill.md
    anthill-todo/delivered/WI-731.anthill.md
    anthill-todo/delivered/WI-20260818-7X7NK-a-projection-over-a-1.anthill.md
    anthill-todo/rejected/WI-090.anthill.md

The conversion was checked field by field — id, created, status and its hoisted
agent/at/reason, acceptance, depends_on, tags, every feedback entry's at and
author, and the description text — and all five compare equal.

## The one field that is a data change, and it was decided

`WI-20260818-7X7NK` and `WI-090` both carry `depends_on: some(value: nil)` — an
Option holding an EMPTY list, which 692 items on the tracker write. Absent-is-absent
turns it into `none`, and `some([])` and `none` are different values, so this one
field is a data change rather than a reformat.

DECIDED 2026-08-19 (user): dropping it is fine — an item with no dependencies and
an item with an empty dependency list are the same item.

Recorded because the field-by-field check does NOT catch it, by construction: both
sides read as "no dependencies" and compare equal. No round-trip test will ever
surface this difference, so it had to be decided rather than measured.

## What the floor case shows

`WI-090` is the smallest item on the tracker — 325 bytes, a one-word description,
a 19-character rejection reason, no feedback, no tags. In the new format it spends
FOUR chapter headings on 26 characters of content, and its `## Changes` section
holds a single synthesized status entry that restates what `- status: Rejected`
and `- status_at:` already say.

It is also the only sample with no `## Changes` section at all, which exercises
the rule that a container with no entries is simply absent rather than an empty
heading.

## Notes

Chapter headings are display names (`Attributes`, `Description`, `Reason`,
`Changes`), not field names. The mapping already separated the two, so this costs
a value in `Chapter(named:)` rather than a mechanism.
