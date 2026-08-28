## Attributes

- id: WI-20260828-C8SG5-anthill-todo-project-discovery
- created: 2026-08-28T13:33:22Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T13:33:22Z

- acceptance: cargo-test

## Description

anthill-todo project discovery does not walk up the directory tree, and the item-per-file layout makes standing inside the tracker the normal case. From <proj>/anthill-todo/claimed/ — the directory a user is naturally in while editing a WI-....anthill.md — a bare `anthill-todo list` exits 1 with 'no anthill-todo project found in .../claimed', and the remedy it suggests (`anthill-todo init`) would nest a SECOND project inside the tracker. Before WI-1118 a project had no subdirectories, so cwd-inside-the-tracker was not a place anyone stood; now init scaffolds that shape for every new project. Walking up from cwd looking for PROJECT_MARKERS appears safe rather than a return of the WI-744 footgun — it is the marker test, not the search depth, that rejects rustland/anthill-todo/ (the crate) — but this touches a documented invariant with its own history (WI-744 tightened discovery, WI-748 fixed -d), so it wants its own ticket and its own tests rather than riding along. Found by code review of the init-scaffolds-item-per-file change.

