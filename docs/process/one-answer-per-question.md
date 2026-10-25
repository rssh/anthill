# One answer per question — consolidating the typer's decisions

A procedure for one kind of reorganization (`converging.md` §3.10, §4 q18): find a question the
implementation answers in more than one place, measure where the answers differ, decide which
answer is the language's, and make every place ask one function. Worked twice so far —
`docs/design/supplier-question-map.md` (which implementation runs a call) and
`docs/design/compatibility-question-map.md` (may A stand where B is expected).

Copied code is not the target: 5% of the typer's lines repeat a six-line block. The target is a
*decision* made twice — two readers of one question with different rules — which a clone detector
does not see and which shows as one program getting two verdicts by how it is written.

## 1. Pick the question

Signals that a question has several readers:

- a ticket that says "one program, two verdicts", "by the body it is written in", "two spellings";
- a doc comment that names another reader: "one of three readers", "two gates, because there are
  two places that decide", "eval does not take the classification's word for it";
- a family's P4 finding (one program written two ways, two verdicts);
- a gate that forks every route, like `lookup_spec_op_dispatch`'s body-less test.

State it as one sentence in the language's words — *which implementation runs a call of a spec
operation at a carrier* — not in the code's.

Skip what a proposal already owns: a rule body against an operation body is proposal 068's.

## 2. Write down the spec's answer

Quote the sections that decide it (`docs/kernel-language.md`), and for each cell of the matrix to
come, the answer they give. Where the spec gives none, write `?` and leave the cell out of every
property — it is a question for the user, not a defect.

## 3. Build the matrix

One program per cell: the configurations that supply or shape the answer, crossed with the routes
or positions that ask it. Rules learned the hard way:

- **One route per program.** A load refusal refuses the whole file, so two routes in one file
  hide each other.
- **Give the value its type through a helper** (`operation mkA() -> A = …`), so no constructor is
  classified at the expected type.
- **Hold the declarations still** across a row: every program of a row carries every helper the
  routes use, and differs only in the call.
- **Rebuild the CLI first** (`cargo build -p anthill-cli`) and compare its mtime with the last
  source commit; a stale binary measures yesterday's tree.

The generator, the per-program judge and the table script go beside the map, in
`docs/design/<question>-map/`, and run over the CLI in seconds (`xargs -P 12`).

## 4. Separate the fixture from the finding

Before a disagreeing cell is a finding, read its full message. Today's artefacts, each of which
first looked like a divergence:

- a configuration missing a declaration one route needed (`Leaf` providing `Shape` in two rows of
  seven);
- a type left with a member open, refused at a return by a rule of its own (the avoidance problem);
- a spelling the language has none for (a variant's type written bare as a value);
- a known gap of another ticket (a bracket on a call in a rule body, TC54R).

Fix the fixture and run the matrix again; mark a known gap with a footnote and its ticket.

## 5. Map the readers

For each divergence, find the function that decided each route: read the enclosing code, its doc
comments, and its callers. Grep misses calls made through a function pointer (`SupplierReader`)
or a builtin table — read the registration too. Tabulate: reader, where, what it sees, its rule
(default, tie, filter), who calls it. Say which claims are read and which traced.

## 6. Write the map

`docs/design/<question>-map.md`: the question and the spec's answer; the matrix, bold where a cell
contradicts the spec; each divergence with its program and output; the readers; what one answer
would take; how to reproduce. Measure the matrix again when the tree moves — a delivery from
another session can retire a divergence while the map is being written.

## 7. Ask, then file

- **Ask the user** wherever the spec is silent, two readers both follow a stated rule, or a reader
  records its choice as deliberate. Show the full program, run, with its output, and its working
  twin; record the answer on the ticket in the user's words. A decision may reverse an earlier one
  — restate it and confirm before anything moves.
- **One ticket per question**, after asking: the divergences, the readers, what one answer takes,
  and an acceptance that names the family. Spec wording a decision needs is drafted in the ticket
  for the user to review; nothing is written to the spec before that.

## 8. Guard it with a generated family

`rustland/anthill-core/tests/families/` (`scripts/families.sh`, `rustland/CLAUDE.md`):

- **Holes** are the matrix's axes; the routes are `spelt` as one program (P4).
- **The subject** is the file without the call, so a refusal of the declarations is one verdict
  for every route and a refusal of the call is the route's own.
- **`Program::refused`** marks what the spec refuses, so an admitted one is `UNSOUND` (P3).
- **A custom judge** only where the spec lets routes differ — a tie refused at load and one
  refused when the call runs, on the one route where only a value names the carrier — and only
  for that route. A judge that normalizes everywhere hides the regression it exists to catch.
- **Exceptions** name the wrong spelling, under the ticket that fixes it; never a whole row where
  one spelling is right. P4 calls an exception live while any spelling of its row differs, so the
  exceptions of one row come off together, and an acceptance says so.
- **Controls**, measured and stated in the family's header: run with no exceptions, it names
  exactly the programs they cover; with the custom judge backed out, it names only what the judge
  is for. Measure them again after any change to the exceptions or the expectations.
- **Both carriers**: `ANTHILL_TEST_NODE_CARRIER=1 scripts/families.sh <f>`.

Then the full gate, `/code-review`, the commit, and a line under `converging.md` q18.

## 9. Fix

The ticket's acceptance is the family: implement, run `scripts/families.sh <f>`, and the exceptions
under the ticket must excuse nothing (the run fails naming them until they are taken off) while no
other verdict moves. Bless the moved verdicts in the same commit.
