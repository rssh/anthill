## Attributes

- id: WI-20260901-47VWX-a-run-typer-false-load
- created: 2026-09-01T14:11:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-01T20:18:42Z

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

## Changes

### 2026-09-01T20:19:11Z — feedback — user

DRIVEN, and the ticket's mechanism was right about the symptom and short on the population.

THE FIXTURE WENT RED AS FILED. A run_typer:false load of a file the KB had never seen, then a full load_all of one clean unrelated sort: 4 refusals naming test.v47vwx.inc, a file that batch was never handed. restore_load_check_marks puts back claims the partial load DROPPED; a clause fact it CREATED has a fresh RuleId that was in no snapshot.

THE FIRST REPAIR WAS THE TICKET'S OWN DIRECTION AND IT LEAKED. Keying the claim on what the loader's declaration walk PRESENTED (WI-EA6KS's four-producer census) took that fixture green and left a second one leaking: typing::derive_forwarded_provisions asserts a SortProvidesInfo row through assert_fact_carrier, above the stop and through no presentation, so a forwarded provision's bad label still reached the later batch. A census of the loader's writers cannot find it -- that writer is not in the loader.

SHIPPED: typing::RowBindingRun::ClaimOnly, a run of check_written_row_bindings' OWN walk that claims every clause and judges none. Keyed on the READER's population, so no producer can escape and no census can go stale. It also subsumed the snapshot half -- measured, backing that restore out changed no row once the walk exists -- so LoadCheckMarks LOST its judged_row_binding_clauses field rather than gaining a sibling.

BACK-OUTS (call removed, one line): a_check_less_load_entry_point_... clause half 2; ...claims_the_clauses_it_wrote 5; ...claims_a_row_it_derived_too 2. With the presentation-keyed repair in its place instead: only the derived test, 1. Those two rows differing by one entry IS the measurement.

WHAT IT COSTS, stated at the site rather than hidden: a clause written by a check-less load is now judged by NOBODY, where before it surfaced in a later batch under the wrong file's name. Same trade the site half already made. A batch that RE-PRESENTS the file is refused normally, which the fourth batch of both new tests pins.

DECLINED: no kernel-language.md change. §5.5 states what the CHECK decides; run_typer:false is a library option that runs no check at all, and a spec enumerating it would describe the loader. Recorded at RowBindingRun::ClaimOnly.

/code-review (max) found 6, all acted on. Two are worth carrying: my back-out table had CARRIED a figure across instead of measuring it (1 where the measurement is 2), and the fixture was missing ProvidesConditionInfo -- a fifth clause producer -- because it was copied from a census of a DIFFERENT test's routes. Adding it measured something new: with note_metadata_fact_presented backed out the re-presented batch goes 5 -> 1, not 0, and the survivor is the condition route, whose head carries a per-scope clause index (provides_clause_seen, never reset per load) so a re-presented file mints a NEW fact instead of dedup-hitting. The neighbouring test's 'FOUR CLAUSE ROUTES, one per producer' claim was corrected: there are five.

Suite: 36 binaries, 6290 passed, 0 failed. ClaimOnly walk costs 390us on a stdlib-sized KB, debug.

