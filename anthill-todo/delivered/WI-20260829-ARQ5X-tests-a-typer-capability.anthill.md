## Attributes

- id: WI-20260829-ARQ5X-tests-a-typer-capability
- created: 2026-08-29T08:03:30Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T10:07:50Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TESTS: a typer CAPABILITY MATRIX — sweep one construct across its hosts, instead of one file per defect already found.

THE SUITE HAS NO WAY TO FIND A GAP BEFORE SOMEONE TRIPS ON IT. Measured over rustland/anthill-core/tests/: 544 include files, 5987 test functions, and 499 of the 544 are per-WI — one file pinning one defect that had already been discovered by hand. Excellent regression, zero discovery. Seven files in the whole tree contain a dot inside a lambda (`lambda x -> x.field`) at all, and none sweeps one construct across several host operations. 129 files are table-driven, so the STYLE exists; the tables enumerate cases within one ticket's shape.

WHAT THAT COSTS, measured today rather than argued. WI-20260828-N2FHM fixed a field dot on an `Iterable.find` callback. Two days later four one-line probes over one two-field entity found:

  xs.find(lambda r -> r.flag)             LOADS
  xs.foldLeft(0, lambda (acc, r) -> r.a)  LOADS
  xs.filter(lambda r -> r.flag)           REFUSED
  xs.map(lambda r -> r.a)                 REFUSED

`map` became WI-20260829-9TGP7. `filter` was not known to be broken by anyone. Both sit in `stdlib/anthill/prelude/iterable.anthill` within thirty lines of the `find` that was repaired, with the same `(x: Element)` binder. The matrix's first row would have caught both the day N2FHM landed, for about the cost of typing the probes.

THE TICKET COUNT IS THE OTHER HALF OF THE ARGUMENT: ten of the twelve most recently filed items are typer gaps, all found the same way — someone wrote ordinary code in an example and it broke. Three of them (2TMB5, 5NSZY, 8Q0Q5) are the same question — a bare operation name — in three different slots.

SHAPE. Two axes, crossed, one assertion per cell.

  WHAT SITS IN THE POSITION   bare op name | lambda | inline constructor | field dot |
                              match | list/set literal | qualified call | dot call
  HOW ITS TYPE IS REACHED     written directly | from a hint | from a callee's
                              declared param | from a type parameter | through a
                              provision chain (List provides Stream provides
                              Iterable) | from a sibling projection (xs.T)

Each cell asserts ONE of three verdicts, and which one is the point:

  LOADS                  the capability works
  REFUSES, LOCATED       it is rejected, with a message naming the span
  KNOWN GAP, cites a WI  it is rejected TODAY and should not be

The third verdict is what turns an accidental discovery into a tracked one, and it must FAIL WHEN THE GAP CLOSES — so fixing 9TGP7 reds its cell, whoever fixed it flips the verdict and closes the ticket in the same commit. Today a fix can land and nothing tells anyone which other cells it just changed; that is exactly how `find` was repaired while `filter` stayed broken.

FIRST SLICE, and it should ship alone before the rest is designed: callback binders. Hosts {map, filter, find, foldLeft, foldRight} — every callback-taking operation in prelude/{iterable,finite_collection,stream,combinators}.anthill — crossed with body forms {identity, constant, field dot, match destructure, nested call, dot call}. Thirty cells, all one-liners over a shared two-field entity. It subsumes 9TGP7's whole measurement section and would have pre-empted N2FHM.

NOT A REWRITE OF THE PER-WI FILES. They stay: a matrix cell says a capability holds, a WI file says why a specific defect was possible, and the second is the thing that keeps a fix from regressing for its original reason. This adds the sweep the suite has never had.

OPEN, and worth deciding before writing code: where it lives (a new aggregator, or wi_tests.rs which is already 499 modules), and whether the fixture per cell is anthill source in a string or a file on disk — the guardians harness reads files, most WI tests build strings.

## Changes

### 2026-08-29T09:24:05Z — feedback — user

THE WORKED EXAMPLE DOES NOT HOLD AS WRITTEN, and re-measuring it makes the case
for the matrix stronger rather than weaker. Full measurement in WI-20260829-9TGP7's
feedback; the part that bears on this ticket:

  List.length(xs.filter(lambda r -> r.flag))  REFUSED -- expected List, got FilteredStream[...]
  List.length(xs.filter(lambda r -> true))    REFUSED -- expected List, got FilteredStream[...]

Byte-identical with and without the dot. The `filter REFUSED` / `map REFUSED` rows
are a LAZY-STREAM-VS-EAGER-CONSUMER gap, not a callback-dot gap. So "the matrix's
first row would have caught both the day N2FHM landed" is not right: a
callback-binder row would have shown those two cells GREEN, and the actual gap
would have gone on hiding in a row about stream consumers. The genuine N2FHM-class
refusal reproduces only in the QUALIFIED spelling (`Iterable.map(msgs, lambda ...)`)
on a receiver whose type carries a label parameter -- not in any spelling of the
plain two-field entity the probes use.

WHY THIS IS EVIDENCE FOR THE TICKET. Three independent sets of hand-written probes
-- the ones in 9TGP7, the ones here, and my own first attempt at re-measuring them
-- all attributed a consumer error to the callback dot, because none of them ran
the dot-free control beside the dot. That is precisely the failure a matrix with a
control per cell prevents, and it is a better argument than the one in the text.

SO THE SHAPE NEEDS ONE MORE THING: every cell that asserts REFUSES or KNOWN GAP
must carry the MINIMAL-PAIR control that isolates the axis it claims to vary --
the same cell with the construct-under-test swapped for the dullest thing that
fits (a constant callback, a bare binder). Without it a red cell says "this line
does not load", which is what the four probes said, and not "this CAPABILITY is
missing". A 30-cell matrix without controls reproduces the same misattribution
thirty times and looks authoritative doing it.

TWO OPEN QUESTIONS, ANSWERED:
  * WHERE IT LIVES: wi_tests.rs. rustland/CLAUDE.md is explicit that a direct child
    of tests/ costs a link and a process launch, and that consolidation took the
    workspace from 42 integration targets to 21. One more module in the aggregator
    is free; a new binary is not.
  * STRINGS OR FILES: strings, built by one `fn program(host, body) -> String` so a
    cell is a row in a table rather than a file. Files would put 30 fixtures on disk
    whose only difference is one lambda body, and the guardians harness reads files
    because it loads a whole example, which this does not.

AND THE FIRST SLICE SHOULD BE RE-DERIVED, not taken from the text: the hosts named
there are right, but the body forms should be chosen so that at least one cell is
known-red for a reason that has been measured, otherwise the slice ships all-green
and pins nothing. On today's tree the callback-dot row is green across
{map, filter, find, foldLeft} x {dot, unqualified, qualified} on a plain entity, so
the red cell has to come from the label-parameterized receiver.

