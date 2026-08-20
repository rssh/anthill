## Attributes

- id: WI-20260819-7TAZB-anthill-todo-backend-a-format
- created: 2026-08-19T20:59:39Z

- status: Open
- status_agent: claude
- status_at: 2026-08-19T20:59:39Z

- acceptance: cargo-test

- depends_on: WI-20260818-K63ZV-anthill-todo-backend-the-head

- tags: wi437

## Description

anthill-todo backend: A FORMAT-AWARE GIT MERGE DRIVER, so two agents appending feedback stop conflicting.

WHY THIS AND NOT LESS. WI-K63ZV bought conflict-freedom between FIELDS by giving each one a line and a blank line, and WI-1114 bought it between ITEMS by giving each a file. Both work the same way -- DISJOINT BYTES, never clever resolution. Append-into-a-shared-list is the one case that resists it, because both sides insert after the same anchor, and it is the MOST COMMON concurrent agent operation: two agents adding feedback to one item.

MEASURED on real 3-way merges (git merge-file), two branches each appending a different `### <at> — feedback — <author>` entry:

  default text merge                -> CONFLICT
  `union` via .gitattributes        -> clean, and WRONG in two ways
  a custom driver                   -> clean, ordered, blank lines intact

UNION IS NOT A STOPGAP, and the reason is structural rather than a matter of polish. Two measured defects: it does NOT order (the 08-03 entry landed before the 08-02 one) and it DROPS the blank line between joined hunks. And the decisive one: GIT GRANTS A MERGE DRIVER PER PATH, NEVER PER REGION. Union over a whole item file would union a `status:` change into TWO STATUS LINES -- a half-transition that is well-formed, silent, and wrong. So it is the custom driver or nothing.

WHAT THE DRIVER DOES. `anthill-todo merge %O %A %B %L %P`, where %O is the ancestor, %A is ours AND the file the result must be written to, %B is theirs; exit 0 is a clean merge and non-zero leaves %A as the driver wrote it. Four jobs, and the fourth is the one union cannot do at all:
  * UNION the entries of each container -- both sides' feedback is kept;
  * SORT them by their first heading field, which is `at`, so the log reads in order;
  * MERGE the attributes chapter FIELD-WISE, which is what makes a status change on one side and a description edit on the other both survive;
  * REFUSE LOUDLY on two concurrent changes to one FieldGroup. Two agents claiming the same item is a real disagreement about state, and the format already says so by writing the group adjacent; the driver must not resolve it, it must report it.

IT IS SMALL BECAUSE THE PARTS EXIST. `document::read_document` reads all three inputs, `document_facts` gives their facts, and the store's renderer writes the result -- so this is a merge over the DOCUMENT MODEL, not a text merge, and it cannot desynchronise the way a line-based one can.

REGISTRATION IS TWO HALVES AND ONLY ONE OF THEM TRAVELS. `.gitattributes` says WHICH paths use the driver (`*.anthill.md merge=anthill`) and is tracked, so it needs no per-clone step. The driver's DEFINITION -- `merge.anthill.driver = anthill-todo merge %O %A %B %L %P` -- must live in `.git/config` or `~/.gitconfig` and CANNOT be tracked: git deliberately refuses to take an executable command out of a cloned repo, because that is arbitrary code execution on `git merge`. So each clone needs one `git config` line.

THE ABSENT CASE IS THE GOOD ONE, and it was checked rather than assumed: a driver NAMED in .gitattributes but not defined in config falls back to the built-in 3-way merge, which conflicts. Loud, not silently wrong. `fsck` should nevertheless report the driver missing, so its absence is found by a check rather than by a surprise conflict at the worst moment. `anthill-todo init` should print the one-line `git config` and offer to run it.

ACCEPTANCE -- DRIVE THE MERGES, do not assert that the driver loads. Build three real checkouts of one item and run `git merge` (not merge-file) with the driver registered: (a) two different feedback appends merge clean, both entries present, ORDERED by `at`, with the blank line between them -- the CONTROL is the same three inputs under `merge=union`, which passes the first clause and fails the ordering and blank-line ones; (b) a status change against a description edit merges clean and both survive; (c) two concurrent status changes FAIL, and the message names the item and the two statuses -- the control is that the same pair merges clean under union, which is the silent half-transition this refuses; (d) with the driver NOT defined in config, (a) conflicts rather than succeeding wrongly. Then `fsck` reports the missing driver.

OUT OF SCOPE: rerere, a merge tool for humans, and anything about non-item files. The driver is independent of the format and of WI-K63ZV, which is delivered.

