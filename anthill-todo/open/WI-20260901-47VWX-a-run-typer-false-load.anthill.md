## Attributes

- id: WI-20260901-47VWX-a-run-typer-false-load
- created: 2026-09-01T14:11:24Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T14:11:24Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `run_typer: false` LOAD NEUTRALIZES THE CLAIMS IT DROPPED, NOT THE FACTS IT CREATED --
so a later clean load is refused naming a file the partial batch was never given.

FOUND BY /code-review on WI-20260821-P85Z7's diff (kb/load.rs:12528 region).

MECHANISM, as read: `restore_load_check_marks` reinstates the PRE-LOAD
`judged_row_binding_clauses` snapshot, which is the right neutralization for a claim the
partial load DROPPED. It is not one for a clause fact the partial load ASSERTED: a
`SortProvidesInfo` / `SortRequiresInfo` / `OperationInfo` fact first written by that
batch has a fresh `RuleId` that was never in the snapshot, so restoring the snapshot
leaves it UNCLAIMED. A later full `load_all` of an unrelated clean file then walks
`all_spec_clause_views` over the WHOLE KB, judges that leftover, and fails naming a file
that load was never handed -- the exact symptom `LoadCheckMarks`' own doc says the
restore removes, and the doc's claim that the entry point is "uniformly check-free" is
what is false.

NOT YET DRIVEN -- this is the reviewer's reading of the code, and the FIRST job is to
build the failing fixture, not to patch. The route named is test-only today:
`common::load_stdlib_kb_untyped` (i.e. `load_all_with(run_typer: false)`) on a fixture
carrying a bad effect-row label, followed by a second load into the SAME KB. If that
fixture will not go red, say so and say why -- the doc still needs correcting either way,
and "the entry point is check-free" would then need the narrower true sentence.

WHY IT MATTERS BEYOND THE DOC: the two loads share a KB, and the second one's verdict is
about the first one's residue. That is a cross-load leak, and its blast radius is every
suite that loads twice into one KB.

ACCEPTANCE: drive it. A `run_typer: false` load of a dirty fixture followed by a full
load of a CLEAN unrelated file must not be refused -- the control is that today it is (or,
if it is not, the measurement that says so, plus the corrected doc sentence). If the fix
is to claim what the partial batch asserted, say at the site which rows fail on a
back-out. cargo-test green via rustland/scripts/test.sh.

