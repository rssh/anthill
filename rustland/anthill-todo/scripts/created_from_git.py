#!/usr/bin/env python3
"""Derive `created` for every legacy work item from git history (WI-1121).

The tracker's ids were minted by a counter into ONE shared file, so an item's
creation time is the date of the FIRST commit whose diff of that file ADDS its
id.  Scanning the history's patches once, oldest first, is O(history); a
per-id `git log -S` would be O(items x history).

APPROXIMATE ON PURPOSE.  §6.5 uses `created` for ORDERING and for the day
partition an id is minted in, and neither needs better than a day -- which is
exactly how good a commit date is.  What it must not be is CONSTANT: stamping
every legacy item with the migration date would put all 1110 of them in one
partition, where the collision scope is the whole tracker at once.

USAGE, from the repo root:

    python3 rustland/anthill-todo/scripts/created_from_git.py created.tsv
    anthill-todo -d "$PWD" migrate --to document --created-from created.tsv

ONE-SHOT BY NATURE, and kept anyway.  It is wanted exactly once per tracker --
the conversion writes `created` into every row and `add` stamps it from then on
-- but it is kept beside the crate because a project migrating later needs it,
and because reconstructing the derivation from the design doc alone is the kind
of thing that gets done differently the second time.

IT DEPENDS ON HOW THIS TRACKER WAS STORED, and says so rather than pretending to
be general: `PATHS` names the shared file the ids used to live in and the
directory they live in now.  A project whose history is shaped differently edits
that list.
"""
import re, subprocess, sys

PATHS = ["anthill-todo/workitems.anthill", "anthill-todo/"]
ID = re.compile(r'id: "(WI-[^"]+)"')

def main(out_path):
    seen = {}
    for path in PATHS:
        proc = subprocess.Popen(
            ["git", "log", "--reverse", "--format=%x01%ad",
             "--date=format-local:%Y-%m-%dT%H:%M:%SZ", "-p", "--", path],
            stdout=subprocess.PIPE, text=True, errors="replace",
            # UTC, in `now()`'s exact spelling: `created` is compared as a STRING
            # (the listing's sort key), and mixed zone offsets do not sort.
            env={**__import__("os").environ, "TZ": "UTC"})
        date = None
        for line in proc.stdout:
            if line.startswith("\x01"):
                date = line[1:].strip()
            elif line.startswith("+") and date:
                for m in ID.finditer(line):
                    seen.setdefault(m.group(1), date)
        proc.wait()
    with open(out_path, "w") as f:
        for wid in sorted(seen):
            f.write(f"{wid}\t{seen[wid]}\n")
    print(f"{len(seen)} ids")

main(sys.argv[1])
