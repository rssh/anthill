# Typing build loop — session runbook & handoff

**Purpose.** This is the kickoff material for a *fresh session* driving the
type-system build sequence one ticket at a time. Each session: read the design,
pick the first undelivered ticket, then **either deliver it or insert a
prerequisite before it and stop for a new session** — stopping whenever a human
decision is needed. Keep one ticket (or one stop) per session so context stays
small.

## The loop (what a session does)

1. **Read the sequence.** Build order lives in
   [`expansion-during-unification.md`](expansion-during-unification.md) §8
   ("Build sequence") and the per-ticket design docs (below). The decided
   threading rules are in [`type-parameter-scoping.md`](type-parameter-scoping.md).
2. **List undelivered tickets.** `cd` to the repo root, build the CLI once
   (`cargo build -p anthill-todo`), then
   `./rustland/target/debug/anthill-todo list` (delivered/verified are hidden by
   default). `show WI-NNN` for detail + feedback.
3. **Pick the first undelivered ticket** in the sequence whose `depends` are all
   delivered. That is the ticket for this session. `claim WI-NNN`.
4. **Read its design.** The ticket description + feedback, plus its design doc if
   it has one (e.g. WI-387 → `effect-rows-on-cross-sort-carriers.md`). If a
   ticket's design is not yet written, **that is itself a design ticket** — write
   the doc, `deliver`, stop.
5. **Act — exactly one of:**
   - **Deliver.** If the work is scoped and verifiable: implement it, run the
     full suite green (`cd rustland && scripts/test.sh -p anthill-core`), run
     `/code-review`, commit (rules below), `deliver WI-NNN`. Then either continue
     to the next ticket or stop (one-ticket-per-session keeps context small).
   - **Insert a prerequisite.** If implementing surfaces a *new primitive / gap*
     the ticket needs (not its own remaining scope), `add` a prerequisite WI
     (`--depends` on what it needs), record on the current ticket that it now
     depends on the new one (CLI has no dep-edit → use `feedback`), revert any
     half-work to green, **stop**. The next session re-runs step 3 and the
     prerequisite is now first.
   - **Stop for interaction.** If a *human decision* is needed (a design choice,
     a semantic change to a core model, a cascade into delivered functionality),
     **stop and ask** — do not guess. The user answers and starts a new session.
6. **Always leave the tree green and committed** before stopping.

> Distinction (matters): *insert a prerequisite* is for a genuinely new
> primitive/capability the ticket depends on. *Remaining scope of the current
> ticket* is NOT a new ticket — finish it, or record it as the ticket's own
> feedback and keep it open (see the memory `feedback-no-ticket-spinoff-for-open-work`).

## Current state (as of 2026-06-04)

**Critical path:** WI-379 ✓ → **WI-387 (next)** → WI-380 → WI-368 (falls out).

| WI | role | status |
|----|------|--------|
| WI-379 | bidirectional inference (args-before-expected); + BigInt-literal fix, `Modify`→`ModifyRuntime[T,V]`, let-conformance | **delivered** (commit `be5bb1d`) |
| WI-386 | design: written effect rows on cross-sort carriers (3-fix plan) | **delivered (design-only)** — doc `effect-rows-on-cross-sort-carriers.md` |
| **WI-387** | **implement** WI-386: FIX 2 (re-apply) + FIX 3 (abstract/requires-coverage) + `provides` clause + write `List.iterator` `E={}`; un-`#[ignore]` `wi368_iterator_threading_test` | **open — THE NEXT TICKET** (depends WI-386 ✓) |
| WI-380 | stdlib threading rewrite (producers write `[Elem]` + `E`) | open — depends WI-387 |
| WI-368 | `length(collect(List.iterator(xs)))` pure + element threaded | achieved by WI-387 + WI-380 |
| WI-376 | projection types `s.T` / `s.Sort` / `X.L` | open — depends WI-379 + 042 |
| WI-374 | bare-ref expansion (convenience) | open |
| WI-381 | alias resolution before expansion | open |
| WI-382 | per-sort unification framework (design) | open — depends WI-010 |
| WI-383 | HKT / structured sort params + `T.V` (sound `ModifyRuntime` tie) | open — depends WI-376 |
| WI-384 | constructor-path bidirectional inference (the WI-379 analogue) | open — `constructor_wrong_return_rejected` is `#[ignore]`'d |
| WI-385 | args/fields never type-checked against declared types (broad; staged rollout) | open |

So **the next session starts WI-387** (the WI-386 design is ready to implement).
Acceptance anchors already on disk, `#[ignore]`'d: `wi368_iterator_threading_test`
(WI-387/368), `wi379_inference_order_test::constructor_wrong_return_rejected`
(WI-384).

## References a session needs

- **Design:** `expansion-during-unification.md` (§8 sequence), `type-parameter-scoping.md`,
  `effect-rows-on-cross-sort-carriers.md` (WI-387), `modify-effect-derive.md`.
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
  commit messages (project override). Branch first only if not on a trunk-based
  flow — this repo commits WI work directly to `main`.
- **Commit before running any review/agent workflow** — its subagents may
  `git stash`/`git checkout` and wipe uncommitted changes (cost real work here once).
- **Loud error over silent skip** (project principle): surface unhandled cases.
- **Effect rows on cross-sort carriers are sensitive** — they touch the subtype
  check, the loader, AND the abstract/requires-coverage check, and cascade into
  delivered effect-threading WIs (wi357/wi210). That is exactly why WI-380 was
  split and WI-387 carries FIX 3. Treat as focused work; verify wi357 + wi210
  stay green.
- **Tracker has no dep-edit** — express new dependencies via `feedback`.

## Kickoff prompt for a new session

> Drive the typing build loop per `docs/design/typing-build-loop.md`. Read that
> runbook + the design docs it points to, run `anthill-todo list`, pick the first
> undelivered ticket whose dependencies are delivered (currently **WI-387**),
> claim it, and either deliver it (implement → full suite green → `/code-review`
> → commit → `deliver`) or, if it needs a prerequisite, file that prerequisite
> before it and stop. **Stop and ask if any human decision is needed.** Leave the
> tree green and committed.
