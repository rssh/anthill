# Sample items in the proposed document format (WI-K63ZV)

Six real work items, converted by hand from the current format to the one
described in `../DRAFT-document-mapping.md`, so the rendered page can be judged
rather than argued about.

These are **samples, not items**. They deliberately do not carry the
`.anthill.md` suffix, so no loader will read them, and they live outside the
tracker tree.

| sample | change entries | shows |
| --- | --- | --- |
| `WI-714.md` | 17 feedback + 1 status | the most feedback on the tracker; 8 dependencies |
| `WI-383.md` | 16 feedback + 1 status | feedback plus a tag |
| `WI-402.md` | 10 feedback + 1 status | a typical delivered item |
| `WI-1115.md` | 1 feedback + 1 status | `ProposalRejected` — the reason as a `## Reason` chapter |
| `WI-731.md` | 8 feedback | an open item, so no status entry |
| `WI-20260818-7X7NK-a-projection-over-a-1.md` | 1 feedback | a NEW-STYLE id, and an empty `depends_on` — see below |

**The `status` entries are synthesized**, from the item's current status and its
timestamp. Real history does not exist to migrate: `Delivered(agent, at)`
overwrote `Claimed(agent, since)` on 985 of 1127 items, and `untag` never left a
record at all. They are here so the `— feedback —` / `— status —` discriminator
can be judged against a mixed log, which is the only situation where it earns its
place.

Originals, for comparison:

    anthill-todo/delivered/WI-714.anthill.md
    anthill-todo/delivered/WI-383.anthill.md
    anthill-todo/delivered/WI-402.anthill.md
    anthill-todo/proposal_rejected/WI-1115.anthill.md
    anthill-todo/open/WI-731.anthill.md
    anthill-todo/open/WI-20260818-7X7NK-a-projection-over-a-1.anthill.md

The conversion was checked field by field — id, created, status and its hoisted
agent/at/reason, acceptance, depends_on, tags, every feedback entry's at and
author, and the description text — and all five compare equal.

## The one place the conversion is NOT lossless

`WI-20260818-7X7NK` carries `depends_on: some(value: nil)` — an Option holding an
EMPTY list, which 692 items on the tracker write. Absent-is-absent turns that into
`none`, and `some([])` and `none` are different values, so this one field is a DATA
change rather than a reformat.

The field-by-field check above does not catch it, by construction: both sides read
as "no dependencies", so they compare equal. It is a decision to take deliberately,
not something a round-trip test will surface.

## Notes

Chapter headings are display names (`Attributes`, `Description`, `Reason`,
`Changes`), not field names. The mapping already separated the two, so this costs
a value in `Chapter(named:)` rather than a mechanism.
