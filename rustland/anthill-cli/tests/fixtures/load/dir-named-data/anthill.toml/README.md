This directory is deliberately named `anthill.toml`, and exists to hold this file
so git can store the directory at all.

WI-746 review finding: the collector first probed candidates with `is_file()`,
which answers false for a directory wearing the conventional name, for a DANGLING
SYMLINK, and for any stat failure — silently dropping a data file the user had
declared. That is the precise silent skip the ticket exists to end, and it was a
regression: the old extension-walk collected such a path and let `read_to_string`
fail loudly. The collector now treats only `NotFound` as absent.

A directory is the portable way to pin this (git cannot store a dangling symlink
that survives a Windows checkout); the symlink case rides the same two lines.
