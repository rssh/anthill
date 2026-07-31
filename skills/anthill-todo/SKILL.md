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
anthill-todo -d "$PWD" list                              # List all work items
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

### Build-loop primitives (tags + ordered insert)

A *named list* (tag) plus `list --tag` gives a machine-readable, dependency-ordered
sequence: `list --tag typing` shows the tag's items topologically (a dependency
appears before its dependents) with status, marking the first Open item whose
dependencies are all satisfied with `<- next`. `insert "desc" --before WI-CUR --tag typing`
creates a new item, tags it, and makes WI-CUR depend on it — the "insert a blocking
prerequisite" step, in one command.
