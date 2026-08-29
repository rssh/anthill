## Attributes

- id: WI-20260829-GNPG7-typing-a-bound-spec-view
- created: 2026-08-29T11:51:21Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T11:51:21Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPING: a BOUND spec-view parameter refuses the carrier that provides it, while the BARE spec name accepts it -- and `Stream` accepts both. Measured by the WI-20260829-ARQ5X capability matrix; FILED AS A QUESTION, because which side is right is a design decision I could not settle from the corpus.

MEASURED, one argument (`rs: List[T = Row]`) into five parameter spellings:

  operation ti(c: Iterable) -> Int64                                          LOADS
  operation ti(c: Iterable[C = List[T = Row], Element = Row, E = {}]) ...     REFUSED
  operation ti(c: Iterable[Element = Row]) -> Int64                           REFUSED
  operation ti(c: Stream) -> Int64                                            LOADS
  operation ti(c: Stream[T = Row, E = {}]) -> Int64                           LOADS

  refusal: type mismatch in ti.c (op-arg): expected Iterable[C = List[T = Row],
           Element = Row, E = {empty_row}], got List[T = Row]

`List provides Stream provides Iterable`, so the provision chain reaches `Iterable` either way; what changes the verdict is only whether the parameter's spec type carries BINDINGS. Note the third row: `C` is UNBOUND there and it still refuses, so this is not "naming the carrier makes a distinct view" -- ANY binding is enough.

THE TWO READINGS, and I do not know which is intended:

  (a) IT IS A GAP. `Iterable[C = List[T = Row], …]` names exactly the view `List[T = Row]`
      provides, so the argument should be admissible; the bare-spec row proves the
      provision edge is found, and `Stream[T = Row, E = {}]` proves a BOUND spec param can
      accept a carrier. On this reading the widening simply is not attempted once bindings
      are present.

  (b) IT IS THE DESIGN. A spec type with bindings is a VIEW, structurally distinct from the
      carrier, and an author who wants one writes the conversion (`Iterable.iterator(c)`,
      as `MappedStream.splitFirst` does -- combinators.anthill:83 -- with a comment saying
      `src` is an abstract Iterable view that must be turned into a Stream first). On this
      reading the bare-spec row is the anomaly, not the bound ones.

WHAT MAKES IT WORTH SETTLING RATHER THAN LEAVING: the stdlib RELIES on the permissive
direction. `MappedStream`'s field is `source: Iterable[C = Source, Element = Src, E = ES]`
and `Iterable.map(s: Stream[S, EffS], f) = mapped(s, f)` passes a `Stream` straight into
it -- which type-checks because `Source` is an unbound sort PARAM there, so the view's
bindings unify with anything. So the stdlib's working case and this refusal differ only in
whether the binding is a variable or a concrete sort, which is a thin line for a
correct/incorrect boundary to sit on and is worth being deliberate about.

CELLS: `typer_capability_matrix_test::a_spec_typed_parameter_and_its_carrier` holds all
five rows. They are recorded as MEASURED FACTS rather than as gaps -- no cell claims a
verdict is wrong -- so whichever way this is settled, the table says what changed.

