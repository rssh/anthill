---
name: anthill-todo
description: Manage project work items (add, list, show, claim, deliver) using the anthill-todo CLI. Works in any project directory.
user-invocable: true
allowed-tools:
  - Bash
  - Read
  - Edit
---

# anthill-todo

Manage structured work items for any project using the `anthill-todo` CLI.

## Usage

Always pass `-d` with the current working directory so work items go to the correct project:

```bash
anthill-todo -d "$PWD" $ARGS
```

When invoked as `/anthill-todo`, run the CLI with the user's arguments. If no arguments, show the list.

If the project has no `anthill-todo/` directory yet, run `init` first.

## Commands

```bash
anthill-todo -d "$PWD" list                              # List all work items (one line each: first line of the description)
anthill-todo -d "$PWD" list --long                       # Same listing with each item's full description text
anthill-todo -d "$PWD" list --unblocked                  # Only items whose dependencies are all satisfied
anthill-todo -d "$PWD" list --tag typing                 # Tag's items in dependency (sequence) order
anthill-todo -d "$PWD" add "description" [--depends WI-NNN] [--tag NAME]  # Add a new work item
anthill-todo -d "$PWD" insert "description" --before WI-NNN [--tag NAME]  # Insert a prerequisite before WI-NNN
anthill-todo -d "$PWD" show WI-NNN                       # Show details
anthill-todo -d "$PWD" next                              # Show next claimable item
anthill-todo -d "$PWD" --agent claude claim WI-NNN       # Claim a work item
anthill-todo -d "$PWD" --agent claude deliver WI-NNN     # Mark as delivered
anthill-todo -d "$PWD" feedback WI-NNN "feedback text"   # Add feedback
anthill-todo -d "$PWD" tag WI-NNN typing                 # Add a tag (named list)
anthill-todo -d "$PWD" untag WI-NNN typing               # Remove a tag
anthill-todo -d "$PWD" add-dependency WI-A WI-B          # Make WI-A depend on WI-B
anthill-todo -d "$PWD" remove-dependency WI-A WI-B       # Drop WI-A's dependency on WI-B
anthill-todo -d "$PWD" status                            # Show status counts
anthill-todo -d "$PWD" graph                             # Show dependency graph
anthill-todo -d "$PWD" init                              # Initialize anthill-todo/ in project
```

### What a project looks like on disk

`init` creates the configuration and nothing else:

```
anthill-todo/project.anthill        # project configuration, and which store holds the items
anthill-todo/store_format.anthill   # the data format those items are written in
```

Each item is then **its own file**, in a directory named for its status:

```
anthill-todo/open/WI-20260817-K7M2Q-item-per-file-store.anthill.md
anthill-todo/claimed/…
anthill-todo/delivered/…
```

An item file is a MARKDOWN DOCUMENT — an `## Attributes` chapter of one line per
field, then the prose fields as chapters — so it renders on GitHub and can be read
and edited by hand. Changing an item's status MOVES its file between these
directories; `anthill-todo fsck` checks the tree against the facts and reports what
disagrees.

An older project may instead hold every item in a single `anthill-todo/workitems.anthill`,
and so does a project that declares no store binding. That layout keeps working —
`anthill-todo migrate --to item-per-file` converts one to the layout above.

### Referring to a work item

An item's id is MINTED FROM THE ITEM: `WI-<YYYYMMDD>-<5 characters>-<slug>`, e.g.
`WI-20260817-K7M2Q-item-per-file-store`. Nobody types that. Every command that
takes an id accepts any unambiguous FRAGMENT of one:

```bash
anthill-todo -d "$PWD" show WI-K7M2Q                  # the 5-character digest, or a prefix
anthill-todo -d "$PWD" show WI-20260817-K7M2Q         # date-digest — the stable handle
anthill-todo -d "$PWD" show WI-item-per-file          # the slug, or a prefix of it
```

A fragment matching several items is REPORTED with the candidates rather than
resolved by a rule — give more of one of them. Older `WI-NNN` ids still work
exactly as they always did, and are never renumbered.

### Build-loop primitives (tags + ordered insert)

A *named list* (tag) plus `list --tag` gives a machine-readable, dependency-ordered
sequence: `list --tag typing` shows the tag's items topologically (a dependency
appears before its dependents) with status, marking the first Open item whose
dependencies are all satisfied with `<- next`. `insert "desc" --before WI-CUR --tag typing`
creates a new item, tags it, and makes WI-CUR depend on it — the "insert a blocking
prerequisite" step, in one command.
