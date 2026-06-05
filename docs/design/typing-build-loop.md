# Typing build loop — session runbook & handoff

**Purpose.** Kickoff material for a *fresh session* driving the type-system build
sequence one ticket at a time. Each session: read the live sequence, pick the
first undelivered ticket, then **either deliver it or insert a prerequisite
before it and stop** — stopping whenever a human decision is needed. One ticket
(or one stop) per session keeps context small.

The sequence is a **named list (tag)** in the tracker — `typing` — so it is
machine-readable and self-maintaining (WI-388). `anthill-todo list --tag typing`
prints it in dependency order with status and marks the ticket to pick, so **no
hand-maintained table in this doc can go stale**. The generic driver is the
`/wi-build-loop <tag>` skill, whose tracked source is `skills/wi-build-loop/`
(installed into a Claude-Code-discovered skills dir — see that file's header);
this doc is the typing-specific runbook it points back to.

## The loop (what a session does)

1. **Read the sequence.** From the repo root, build the CLI once, then print the
   tagged sequence:
   ```bash
   cd rustland && cargo build -p anthill-todo && cd ..
   ./rustland/target/debug/anthill-todo list --tag typing
   ```
   Items print in dependency (topological) order — a dependency always appears
   before its dependents — each with `[Status]`, `(blocked: …)` when a dependency
   is unmet, and `<- next` on the first undelivered item whose dependencies are
   all delivered. The design rationale lives in
   [`expansion-during-unification.md`](expansion-during-unification.md) §8 and
   [`type-parameter-scoping.md`](type-parameter-scoping.md); the tag is the
   *operational* view of that sequence.

2. **Pick the ticket.**
   - If a tagged ticket is **`Claimed`**, that is work in progress — **resume it**
     (finish or hand off); don't start a new one. (Note the `<- next` marker flags
     the first *undelivered* item in topo order, which can be a low-id `Open`
     ticket ordered ahead of an in-progress higher-id one — e.g. the convenience
     WI-374 sorts before a claimed WI-380. Resume the claimed ticket first.)
   - Otherwise pick the `<- next` ticket and claim it:
     ```bash
     ./rustland/target/debug/anthill-todo --agent claude claim WI-NNN
     ```

3. **Read its design.** `show WI-NNN` for description + feedback, plus its design
   doc if it has one (e.g. WI-387 → `effect-rows-on-cross-sort-carriers.md`). If a
   ticket's design is not yet written, **that is itself a design ticket** — write
   the doc, `deliver`, stop.

4. **Act — exactly one of:**
   - **Deliver.** If the work is scoped and verifiable: implement it, run the full
     suite green (`cd rustland && scripts/test.sh -p anthill-core`), run
     `/code-review`, commit (rules below), then:
     ```bash
     ./rustland/target/debug/anthill-todo --agent claude deliver WI-NNN
     ```
     Continue to the next ticket or stop (one-ticket-per-session keeps context small).
   - **Insert a prerequisite.** If implementing surfaces a *new primitive / gap*
     the ticket genuinely needs (not its own remaining scope), insert it before the
     current ticket in **one command** — this creates the new WI, tags it into the
     sequence, *and* makes the current ticket depend on it:
     ```bash
     ./rustland/target/debug/anthill-todo insert "PREREQ description" \
       --before WI-CUR --tag typing [--depends WI-X] [--acceptance cargo-test]
     ```
     Revert any half-work to green, **stop**. The next session re-runs step 1 and
     the prerequisite is now `<- next`.
   - **Stop for interaction.** If a *human decision* is needed (a design choice, a
     semantic change to a core model, a cascade into delivered functionality),
     **stop and ask** — do not guess. The user answers and starts a new session.

5. **Always leave the tree green and committed** before stopping.

> Distinction (matters): *insert a prerequisite* is for a genuinely new
> primitive/capability the ticket depends on. *Remaining scope of the current
> ticket* is NOT a new ticket — finish it, or record it as the ticket's own
> feedback and keep it open (memory `feedback-no-ticket-spinoff-for-open-work`).

## Tracker primitives (WI-388)

The sequence is driven entirely through these — no hand-edited status table, no
`feedback`-as-dep-edit:

| Need | Command |
|------|---------|
| See the sequence + status + next | `list --tag typing` |
| Add a ticket to the sequence | `add "desc" --tag typing [--depends WI-X]` |
| Insert a blocking prerequisite before a ticket | `insert "desc" --before WI-CUR --tag typing` (creates + tags + sets WI-CUR → depends) |
| Correct a dependency | `add-dependency WI-A WI-B` / `remove-dependency WI-A WI-B` |
| Add / drop a ticket from the sequence | `tag WI-NNN typing` / `untag WI-NNN typing` |

## Current state

**`list --tag typing` is the source of truth — read it, don't trust a frozen
table.** As of this rewrite (2026-06-05): **WI-379 ✓, WI-386 ✓, WI-387 ✓**
delivered; **WI-380** (stdlib threading rewrite) **`Claimed` / in progress** — the
concrete consumer of WI-379 and the critical-path ticket.

**Critical path (design-level, slower to go stale than status):**
WI-379 ✓ → **WI-380** → WI-368 (its acceptance falls out of WI-380). WI-376
(projection `s.T`), WI-374 (bare-ref expansion — *convenience*, threads nothing on
its own), and WI-381 (alias resolution) are fluency / robustness on top; WI-382 is
the long-horizon per-sort-unification destination. Per §8, **nothing load-bearing
depends on WI-374** — which is exactly why the CLI's `<- next` landing on WI-374 is
*not* the critical path: resume the claimed WI-380 first.

Acceptance anchors on disk, `#[ignore]`'d: `wi368_iterator_threading_test`
(WI-380/368), `wi379_inference_order_test::constructor_wrong_return_rejected`
(WI-384).

## References a session needs

- **Design:** `expansion-during-unification.md` (§8 sequence + rationale),
  `type-parameter-scoping.md` (threading rules),
  `effect-rows-on-cross-sort-carriers.md` (WI-386/387), `modify-effect-derive.md`.
- **Code:** the typer is `rustland/anthill-core/src/kb/typing.rs`; the loader
  `kb/load.rs`; parse `parse/convert.rs`; eval `eval/`. Key fns are named in each
  design doc's "Code pointers".
- **Tests:** `cd rustland && scripts/test.sh -p anthill-core` (NOT plain `cargo
  test` — see `rustland/CLAUDE.md`). Per-WI tests live in
  `anthill-core/tests/include/wiNNN_*.rs`, wired in `tests/wi_tests.rs`.
- **Memories:** `anthill-typing-build-sequence` (this work's state),
  `workflow-git-clobbers-uncommitted` (commit before any review/agent workflow —
  it can `git stash`/`checkout` away uncommitted work).

## Rules & gotchas (from `CLAUDE.md` + this work)

- **Before commit:** full suite green + run `/code-review`. **No attribution** in
  commit messages (project override). This repo commits WI work directly to `main`.
- **Commit before running any review/agent workflow** — its subagents may
  `git stash`/`git checkout` and wipe uncommitted changes (cost real work here once).
- **Loud error over silent skip** (project principle): surface unhandled cases.
- **Effect rows on cross-sort carriers are sensitive** — they touch the subtype
  check, the loader, AND the abstract/requires-coverage check, and cascade into
  delivered effect-threading WIs (wi357/wi210). That is why WI-380 was split and
  WI-387 carried FIX 3. Treat as focused work; verify wi357 + wi210 stay green.
- **Dependency edits are first-class now** — use `add-dependency` /
  `remove-dependency` (and `insert --before` for the blocking-prerequisite case).
  The old workaround of recording new deps via `feedback` is retired (WI-388).

## Kickoff prompt for a new session

> Drive the typing build loop per `docs/design/typing-build-loop.md` — or just run
> `/wi-build-loop typing`. Build the CLI, run `anthill-todo list --tag typing`,
> resume any `Claimed` ticket or claim the `<- next` one, read its design (`show` +
> design doc), and either deliver it (implement → full suite green → `/code-review`
> → commit → `deliver`) or, if it needs a new primitive, `insert` that prerequisite
> before it (`--before WI-CUR --tag typing`) and stop. **Stop and ask if any human
> decision is needed.** Leave the tree green and committed.
