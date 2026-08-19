# Sample items in the proposed document format (WI-K63ZV)

Five real work items, converted by hand from the current format to the one
described in `../DRAFT-document-mapping.md`, so the rendered page can be judged
rather than argued about.

These are **samples, not items**. They deliberately do not carry the
`.anthill.md` suffix, so no loader will read them, and they live outside the
tracker tree.

| sample | feedback entries | shows |
| --- | --- | --- |
| `WI-714.md` | 17 | the most feedback on the tracker; 8 dependencies |
| `WI-383.md` | 16 | feedback plus a tag |
| `WI-402.md` | 10 | a typical delivered item |
| `WI-1115.md` | 1 | `ProposalRejected` — the status reason as a `## reason` chapter |
| `WI-731.md` | 8 | an open item |

Originals, for comparison:

    anthill-todo/delivered/WI-714.anthill.md
    anthill-todo/delivered/WI-383.anthill.md
    anthill-todo/delivered/WI-402.anthill.md
    anthill-todo/proposal_rejected/WI-1115.anthill.md
    anthill-todo/open/WI-731.anthill.md

The conversion was checked field by field — id, created, status and its hoisted
agent/at/reason, acceptance, depends_on, tags, every feedback entry's at and
author, and the description text — and all five compare equal.
