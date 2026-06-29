---
name: wi-build-loop
description: Drive a tagged work-item sequence (anthill-todo named list) one ticket per session — read the live sequence, resume/claim the next ticket whose deps are met, then deliver it or insert a blocking prerequisite, stopping for any human decision. Accepts a tag argument (the named list to drive; default `typing`).
user-invocable: true
argument-hint: "[tag]"
allowed-tools: Bash, Read, Edit, Write, Glob, Grep, Skill
---

# wi-build-loop

> **Install (one-time, per machine).** This tracked source lives in the repo at
> `skills/wi-build-loop/`, but Claude Code discovers skills only from
> `.claude/skills/` or `~/.claude/skills/`. Symlink it into your personal skills
> dir (matches how `anthill-todo` is installed) — run from the repo root:
> ```bash
> ln -s "$PWD/skills/wi-build-loop" ~/.claude/skills/wi-build-loop
> ```

Drive a **tagged work-item sequence** one ticket at a time, using the
`anthill-todo` tracker's named-list primitives (WI-388). Each invocation: read the
live sequence, pick the first undelivered ticket whose dependencies are all met,
then **either deliver it or insert a prerequisite before it and stop** — stopping
whenever a human decision is needed. One ticket (or one stop) per run keeps context
small.

This is the generic driver. The typing-system instance has a full runbook with
design pointers at `docs/design/typing-build-loop.md` — read it when the tag is
`typing`.

## Argument — the tag

This skill's argument (`$ARGUMENTS`) is the **tag** (named list) to drive, e.g.
`typing`. If no argument was given, default to `typing` (this repo's type-system
sequence) and say so. If the chosen tag has no items, run `list` (no `--tag`) to
show what exists and ask the user which tag to drive.

## Sync with origin first (before each run)

This repo **commits WI work directly to `main`**, and more than one machine /
session pushes to it — so sync *before* starting, or you risk building on a stale
tree or stranding commits. Two failure modes, both real:

- **Local behind / diverged.** `main` may have remote commits you lack *and*
  unpushed local commits from a prior session (the loop commits, but a session can
  end before pushing). A plain `git pull --ff-only` then **fails** ("not possible
  to fast-forward"). Reconcile with **either a merge or a rebase** — your choice.
  A **merge** matches the historical convention here (`git log --merges` shows
  repeated `Merge remote-tracking branch 'origin/main'`); a **`git rebase
  origin/main`** gives linear history and replays your local commits one at a time,
  which is handy when a WI-id collided (below) since it pauses on the offending
  commit so you can renumber *and* reword it inline:

  ```bash
  git fetch origin
  git status --short                 # must be clean; stash/commit anything first
  git merge origin/main --no-edit    # the repo's historical convention …
  # …or, for linear history:
  #   git rebase origin/main         # resolve the same conflict, then `git rebase --continue`
  cargo build -q 2>/dev/null || ( cd rustland && cargo build )   # compile-sanity afterwards
  ```

  Code conflicts are rare (tickets touch different files — typer vs eval, etc.);
  the one file that tends to conflict is `anthill-todo/workitems.anthill` (tracking
  data) — resolve by keeping **both** sides' items. If two sessions allocated the
  **same WI-id** for different tickets, keep the one with external references (a
  test file named after it, a `depends_on`) and **renumber yours** to a free id
  (rename the `WorkItem` *and* its `Tag` lines), then verify the file still loads
  (`anthill-todo … list`).

- **Local not pushed.** Unpushed commits are how the divergence above accumulates.
  **Push after every delivery** (loop step 4), and at run start confirm sync:

  ```bash
  git rev-list --left-right --count HEAD...origin/main   # want: 0  0  (ahead  behind)
  ```

## Setup — resolve the CLI (once)

Set `TAG` to the argument above (or `typing` if none). Prefer an installed
`anthill-todo`; otherwise build and use the local binary (anthill repo layout).
Always pass `-d "$PWD"` so work items resolve to the project in the current
directory.

```bash
TAG=typing                                         # ← the skill argument, or `typing` if none
TODO="$(command -v anthill-todo || true)"
if [ -z "$TODO" ]; then
  ( cd rustland && cargo build -p anthill-todo )   # anthill repo
  TODO="$PWD/rustland/target/debug/anthill-todo"
fi
"$TODO" -d "$PWD" list --tag "$TAG"
```

(If `cargo` is unavailable and `anthill-todo` is not on `PATH`, stop and tell the
user how to build/install it — don't guess a path.)

## The loop (what one run does)

1. **Read the sequence.** `list --tag $TAG`. Items print in dependency
   (topological) order — a dependency always before its dependents — each with
   `[Status]`, `(blocked: …)` for unmet deps, and `<- next` on the first
   undelivered item whose dependencies are all delivered.

2. **Pick the ticket.**
   - If a tagged ticket is **`Claimed`**, that is work already in progress —
     **resume it**, don't start a new one. (The `<- next` marker flags the first
     *undelivered* item in topo order, which can be a low-id `Open` ticket ordered
     ahead of an in-progress higher-id one — resume the claimed ticket first.)
   - Otherwise pick the `<- next` ticket and claim it:
     `$TODO -d "$PWD" --agent claude claim WI-NNN`.

3. **Read its design.** `show WI-NNN` for description + feedback, plus its design
   doc if it references one. If a ticket's design is not yet written, **that is
   itself a design ticket** — write the doc, `deliver`, stop.

4. **Act — exactly one of:**
   - **Deliver.** If the work is scoped and verifiable: implement it, run the
     project's full test suite green, run `/code-review` (via the Skill tool),
     commit per the repo's rules, **`git push origin main`** (so local never
     strands commits — see *Sync with origin*), then `--agent claude deliver
     WI-NNN`. Continue to the next ticket or stop (one-ticket-per-run keeps context
     small).
   - **Insert a prerequisite.** If implementing surfaces a *new primitive / gap*
     the ticket genuinely needs (not its own remaining scope), insert it before the
     current ticket in **one command** — creates the new WI, tags it into the
     sequence, *and* makes the current ticket depend on it:
     ```bash
     $TODO -d "$PWD" insert "PREREQ description" \
       --before WI-CUR --tag "$TAG" [--depends WI-X] [--acceptance cargo-test]
     ```
     Revert any half-work to green, **stop**. The next run re-lists and the
     prerequisite is now `<- next`.
   - **Stop for interaction.** If a *human decision* is needed (a design choice, a
     semantic change to a core model, a cascade into delivered functionality),
     **stop and ask** — do not guess.

5. **Always leave the tree green, committed, and pushed** before stopping
   (`HEAD...origin/main` = `0  0`).

> Distinction (matters): *insert a prerequisite* is for a genuinely new
> primitive/capability the ticket depends on. *Remaining scope of the current
> ticket* is NOT a new ticket — finish it, or record it as the ticket's own
> feedback (`feedback WI-NNN "…"`) and keep it open.

## Tracker primitives (the named-list ops this loop uses)

| Need | Command |
|------|---------|
| See the sequence + status + next | `list --tag $TAG` |
| Add a ticket to the sequence | `add "desc" --tag $TAG [--depends WI-X]` |
| Insert a blocking prerequisite before a ticket | `insert "desc" --before WI-CUR --tag $TAG` |
| Correct a dependency | `add-dependency WI-A WI-B` / `remove-dependency WI-A WI-B` |
| Add / drop a ticket from the sequence | `tag WI-NNN $TAG` / `untag WI-NNN $TAG` |

## Rules & gotchas

- **One ticket (or one stop) per run.** Keep context small; hand off cleanly.
- **Sync at both ends** — merge *or* rebase `origin/main` *before* starting (not
  `--ff-only`, which fails on divergence), and **push after every deliver** so local
  never strands commits. End each run with `HEAD...origin/main` = `0  0`.
- **Commit before running any review/agent workflow** — its subagents may
  `git stash`/`git checkout` and wipe uncommitted changes.
- **Loud error over silent skip:** surface unhandled cases rather than dropping them.
- **Respect the repo's commit rules** (CLAUDE.md) — e.g. this repo forbids commit
  attribution and commits WI work directly to `main`.
- **Stop and ask on any human decision** — design choices, core-model changes, or
  cascades into delivered functionality are not for the loop to guess.
