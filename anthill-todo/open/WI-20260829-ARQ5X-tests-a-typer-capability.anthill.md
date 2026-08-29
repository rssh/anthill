## Attributes

- id: WI-20260829-ARQ5X-tests-a-typer-capability
- created: 2026-08-29T08:03:30Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T08:03:30Z

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

