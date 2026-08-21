## Attributes

- id: WI-20260820-8B6W0-anthill-todo-mirror-drive-the
- created: 2026-08-20T20:56:41Z

- status: Open
- status_agent: claude
- status_at: 2026-08-20T20:56:41Z

- acceptance: cargo-test

- depends_on: WI-1117

- tags: wi437

## Description

anthill-todo mirror: DRIVE THE ENTRY'S OWN OPEN/CLOSED STATE, the one line of design backend-github-coordination.md §7.1 that WI-1117 did not ship. Today an item's status reaches the target only in the entry BODY (`Status: Verified`), so a verified item's GitHub issue stays OPEN and stays in the default listing — the thing the mirror's audience actually looks at. §7.1: the entry is open while the item is, and closed on Verified, Rejected, ProposalRejected and Stale. NOT A PARAMETER, A DESIGN INCREMENT, which is why it was left out rather than folded in: (1) export is UNCONDITIONAL (tracker-wins, no comparison), so a close/reopen per item per run is N extra API calls on every export of a four-figure tracker — a rate-limit hazard, not a cost; avoiding it means `Forge.list_entries` must report each entry's STATE (a third field on `ForgeEntry`) so export changes only what differs. (2) `gh issue edit` has no --state flag: closing is a SECOND command (`gh issue close|reopen <n>`), and what `gh` does when asked to close an already-closed issue is exactly what no test in this repo can pin — which is the whole reason the fake exists. Shipping it unverified was the alternative and was declined. WORK: state on ForgeEntry; open/closed derived from WorkStatus in the bundle (terminal = closed); create_entry/update_entry carrying it; the fake storing and reporting it; the gh backend's second command, issued only on a difference. TEST IT ON THE FAKE: export a Verified item and assert the entry is closed, export an Open one and assert it is not, and assert a re-export of an unchanged item issues NO state change (the call-count property is the point of the increment). §7.1's LABELS are a separate and smaller thing — that section already calls them optional and config-gated.

