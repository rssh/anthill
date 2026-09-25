## Attributes

- id: WI-20260925-4ZZKZ-the-load-time-spec-half-slot
- created: 2026-09-25T04:50:17Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T04:50:17Z

- acceptance: cargo-test

- depends_on: WI-20260925-P5G39-provision-checks-resolve-under

- tags: typing

## Description

THE LOAD-TIME SPEC-HALF SLOT STOPS BEING SILENT. WI-857 records a spec-half sub-goal that does not resolve as `ResolvedRequiresNode::Unavailable` (synth.rs, the `i < provider_half_start` arm), and only a READ of the slot at eval is loud. Its own justification is the resolver's false 'no': 'the spec's own requires is often satisfied only LOOSELY' (`FiniteCollection requires Iterable[C = C]` at `List`, reached only via `List provides Stream provides Iterable`), and refusing broke 33 tests at the time. The absence therefore reaches run time, which the repo principle forbids, and it hides resolver bugs: WI-20260925-P5G39's 10 stdlib slots came from exactly this.

MEASURED 2026-09-25: a panic at that push fails EVERY test (772 at the first binary), because the bare stdlib itself produces 10 such slots, all from WI-20260925-P5G39's check. Once that lands, the stdlib no longer masks the population and the probe tells which programs actually depend on the silent slot.

WORK: re-run the probe (panic, tagged by site) after P5G39 and decide per surviving shape. Either fix the resolver's precision (transitive provision at the binding level; effect-row matching, cf. wi508's `FiniteCollection[C = MutableStack, E = {}]` NoMatch that runs fine) or turn the verdict into three answers (built / undecided-because-open / definitely absent), refusing 'definitely absent' at load and forwarding or deferring 'undecided' explicitly. The three RUN-TIME producers in bridge.rs (`UnderDetermined` at an entry with no caller dictionary, `NamedSlotNotCarried`, `ParamSlotNotCarried`) are listed separately: each has its own documented reason ('the body may never read the slot'), and making them loud moves the failure to the ENTRY, per 3G1YT's 'a declared requires is owed because it is declared'. Decide them explicitly, one by one.

ACCEPTANCE: no load-time `Unavailable` is produced (the synth.rs arm refuses, or is unreachable by construction); every test that depended on it is re-read and either updated with a reason or shown to rely on a resolver bug that is fixed here; the run-time producers each carry a recorded decision; full workspace green via rustland/scripts/test.sh. SOURCE: WI-883 follow-up discussion.

