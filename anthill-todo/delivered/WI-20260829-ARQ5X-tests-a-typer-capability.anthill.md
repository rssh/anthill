## Attributes

- id: WI-20260829-ARQ5X-tests-a-typer-capability
- created: 2026-08-29T08:03:30Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T14:08:47Z

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

### 2026-08-29T14:08:40Z — feedback — user

THE GRID IS COMPLETE — 48 of 48 cells, `the_grid_census_is_honest` asserts `todo.is_empty()`, `built == 48` and `unspellable == 0`, and the two slices that finished it are `every_position_through_a_provision_chain` (the column that was the largest gap) and `the_row_remainders`.

THE FOUR CELLS THAT WERE `Unspellable` ARE BUILT. They were `match` in each NESTED route, unspellable because a compound expression lived in `_expr_body` alone; WI-20260829-YBBC3 widened the delimited value positions, so `the_remaining_positions_across_their_routes`' skip list is gone and `match` sweeps all five routes, with the provision-chain one in the table above.

SEVEN DEFECTS IN THE FIRST CUT OF THIS SLICE WERE FOUND BY /code-review AND REPAIRED, and they are worth listing because every one of them was a cell that was GREEN and measured nothing — which is the failure mode a census invites:
 * `list literal / from a sibling projection` held `pick(xs, 1)`. `pick`'s `e: xs.T` is `Int64`, so the slot contained an INTEGER and the cell would have stayed green with list-literal-into-a-projection broken outright. It now uses `pick_ll(xss, [1, 2])`, whose element IS a list, with `pick(xs, [1, 2])` beside it as the NEGATIVE that shows the slot discriminates.
 * The SET literal was never exercised at all, while the census marked the `list/set literal` position Built in every column on the LIST's strength. The two genuinely differ: `ti({1, 2})` REFUSES — `prelude/set.anthill` declares only `provides PartialEq[T = Set]` / `provides Eq[T = Set]`, so a `Set` has no chain to `Iterable`, where a `List` provides `Stream` / `FiniteCollection` outright. Both members are now swept per route and the refusal is a recorded cell with its reason.
 * `bare op name / through a provision chain` held `ti(mk_list())` — a NULLARY CALL, not a bare name — so two cells claimed one grid position with opposite verdicts. Relabelled "nullary call"; the genuine cell is `the_row_remainders`' `ti(inc)`, which refuses.
 * `lambda (reached through a combinator)` held `ti(Iterable.map(rs, lambda x -> x))`, where the spec-typed slot holds a QUALIFIED CALL and the lambda is one level in. Relabelled "nested call"; the genuine lambda cell is `ti(lambda x -> 7)`, which refuses because an arrow is no `Iterable`.
 * One of the three NEGATIVE rows, `ti(b.nosuchfield)`, refuses at MEMBER RESOLUTION — before the argument's type ever reaches the parameter — so it would stay red if the `Iterable` slot became permissive. Kept, relabelled as the field-dot POSITION's control; `ti(1)` and `ti(r)` are the two rows carrying the slot claim.
 * The `take_any` / annotated-let literal cells CANNOT REFUSE. Three `SilentlyAccepted` rows now say exactly what each route lets past, with a CONTROL (`takes_list(["a", 1])`, which does refuse) that keeps them from reading as "literals are unchecked".
 * A stale citation, `a_hinted_literal_never_checks_its_elements`, named a test that does not exist anywhere in the repo. It is `a_literal_is_checked_on_one_route_and_overwritten_on_the_other`, and that stale pointer is exactly what would have flagged the literal cells as sitting on a known hole.

ONE NEW DEFECT CAME OUT OF REPAIRING THEM, filed as WI-20260829-WBXGX: a collection literal's element type is its FIRST element's and every later element is unchecked. `takes_list([1, "a"])` LOADS; `takes_list(["a", 1])` REFUSES; `takes_set({1, "a"})` LOADS. It is NOT WI-20260826-7JDWY — that one is the return-hint route overwriting the elements, and this is on the ARGUMENT route 7JDWY's own table uses as its control. Three cells record it as `SilentlyAccepted` so they fail when it is fixed.

THE LESSON THIS SLICE COST, and it is the one worth keeping: a coverage census makes GREEN the goal, and green is exactly what a cell that measures nothing is. Six of the seven findings were cells whose EXPRESSION did not hold the position its LABEL named — an integer where a list literal was claimed, a call where a bare name was claimed, a qualified call where a lambda was claimed. The check that catches this is not "does the cell pass" but "does the expression in the slot contain the thing the row is named for", asked per row when the row is written.

