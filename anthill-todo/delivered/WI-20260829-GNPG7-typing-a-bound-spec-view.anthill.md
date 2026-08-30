## Attributes

- id: WI-20260829-GNPG7-typing-a-bound-spec-view
- created: 2026-08-29T11:51:21Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T00:09:43Z

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

## Changes

### 2026-08-30T00:09:44Z — feedback — claude

DELIVERED, AND THE TICKET'S OWN TABLE MEASURED THE WRONG AXIS.

THE QUESTION IS SETTLED AS (a), A GAP -- but not the gap the ticket described. It read
"what changes the verdict is only whether the parameter's spec type carries BINDINGS" off
five rows that ALSO differ in HOP COUNT: `List` declares `provides Stream[T, {}]` and
reaches `Iterable` only through `Stream provides Iterable`, never directly. Every refusing
row is 2-hop; the accepting `Stream` row is 1-hop. The table cannot separate the two
readings.

THE SEPARATOR, added to the capability matrix: `MutableStack` declares
`provides Iterable[C = MutableStack[T], Element = T, E = {}]` ITSELF, and a
`MutableStack[T = Row]` IS admissible at `Iterable[C = MutableStack[T = Row], Element = Row,
E = {}]` -- the fully-bound spec view NAMING ITS OWN CARRIER, which is exactly the shape
reading (b) says must be a structurally distinct view. Same spec, same binding shape,
opposite verdict from `List`. (b) is refuted; bindings were never the axis.

CAUSE: one relation, two readers. The bare-spec arms reach `sort_provides_admissibly` ->
`sort_provides` -> `sort_provides_reach`, which WALKS the chain. The bindings-carrying arms
read `provider_spec_view_bindings`, a single DIRECT fact. Both subtype sites now go through
`subtype_provider_view`. Nothing new was built -- `transitive_provider_spec_view_bindings`
already existed for this exact chain (WI-495/WI-714), its sibling's doc naming
"`List provides Stream` + `Stream provides Iterable`, with no direct fact" as its case.

TWO SITES, MEASURED SEPARATELY: `parameterized_compatible_view` (parameterized actual) and
`bare_provider_binding_precise` (bare actual, e.g. `nil()`). Backing out ONLY the first
reddens only its own test, so the pair is not one fixture twice.

FOUR OF THE TICKET'S FIVE ROWS MOVED. The fifth (`Iterable[C = List[T = Row], ...]`) is a
DIFFERENT defect with its own ticket, WI-20260829-XZMGC: `Element` and `E` compose
correctly, `C` does not, because `Stream provides Iterable[C = Stream, ...]` binds C to the
intermediate's SELF-reference and `compose_provision_views` keeps non-param values verbatim
(its own doc names that case). Not inline: substituting needs `kb.alloc`, hence `&mut
KnowledgeBase`, through two callers that are `&KnowledgeBase` and do not read C.

TWO /code-review PASSES, THIRTEEN FINDINGS, ALL REPRODUCED. The second pass caught that my
repair for the first pass's finding was ITSELF order-dependent, which is the one worth
recording:

  * PERF (1st pass). The naive routing cost 1.78x on a min-of-K stdlib load in release
    (127.7 vs 71.9 ms). My first evidence -- suite wall clock "within 1%" -- measured
    NOTHING; the suite is dominated by other work. A reachability pre-filter
    (`sort_provides` before composing) brings it back inside the noise. A second regression
    appeared when the ambiguity check below walked every route, and was fixed by splitting
    the cheap question from the expensive one. NOTE the first perf comparison was also
    invalid -- release build against debug build.
  * DETERMINISM (1st pass, then AGAIN in the 2nd). `transitive_provider_spec_view_bindings`
    returns the FIRST reaching intermediate, so swapping two `provides` lines flipped a
    type verdict. My first repair checked routes for CONFLICTS and returned one -- and two
    views with DISJOINT labels trivially "agree", so it was still order-decided, which the
    second pass drove: `Spec[Q = Bool]` loaded under one ordering and refused under the
    other, `Spec[P = Int64]` the reverse. Routes now MERGE, `None` only on a real per-param
    disagreement. The test asserts BOTH shapes in BOTH orderings plus a single-route
    control -- the earlier one asserted `!errs.is_empty()`, which any load failure
    satisfies.
  * A reaching route that cannot be composed now POISONS the answer instead of vanishing;
    route values compare canonically, not by raw TermId.

THREE FOLLOW-UPS, none of them work this ticket could absorb: WI-20260829-XZMGC (the C
self-reference), WI-20260829-9NJTX (the instantiation loop's un-rolled-back subst -- widened
here, declined because it could not be DRIVEN, and that is said plainly rather than credited
to a neighbouring guard), WI-20260829-4MHED (scaland refuses the companion-receiver bracket
kernel-language.md now states as the rule -- a BAD3V divergence surfaced reviewing this).

TESTS: rustland 36 binaries / 6132 passed / 0 failed (doc-tests included -- a fenced-block
mistake here was invisible to five targeted runs and caught only by the full one); scaland
524 / 0. Capability matrix cells updated with the MutableStack discriminator pair.

