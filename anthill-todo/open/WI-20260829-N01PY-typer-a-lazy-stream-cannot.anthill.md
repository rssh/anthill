## Attributes

- id: WI-20260829-N01PY-typer-a-lazy-stream-cannot
- created: 2026-08-29T09:50:52Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T09:50:52Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER: a LAZY STREAM cannot feed an EAGER consumer, so `xs.map(f).length()` and every shape like it is refused. Split out of WI-20260829-ARQ5X, where it was found and then mis-filed against the ticket that delivers the matrix.

MEASURED, and the CONTROL is what identifies it. `Iterable.map` / `Iterable.filter` return the lazy `MappedStream` / `FilteredStream` carriers; an eager consumer declared over `List` refuses them:

  List.length(xs.map(lambda r -> r.a))     REFUSED -- expected List, got MappedStream[...]
  List.length(xs.map(lambda r -> 7))       REFUSED -- expected List, got MappedStream[...]
  List.length(xs.filter(lambda r -> r.flag))  REFUSED -- expected List, got FilteredStream[...]
  List.length(xs.filter(lambda r -> true))    REFUSED -- expected List, got FilteredStream[...]

Byte-identical with and without a field dot in the callback, so the callback is not implicated; and the SAME calls unconsumed load clean, so it is the CONSUMPTION and not the combinator. `find`, being eager and returning an `Option`, composes with a consumer normally.

THIS IS WHAT THE FOUR PROBES IN WI-20260829-ARQ5X AND WI-20260829-9TGP7 ACTUALLY HIT. Both tickets read `xs.filter(...) REFUSED` as the callback-dot defect WI-20260828-N2FHM had just repaired one operation over. It is not: no callback-dot gap reproduces anywhere in the sweep. See the feedback on both tickets.

IT REACHES REAL CODE, not just probes. In `examples/guardians/fixtures/agent/good.anthill`, substituting the hand-written projection for the map an agent would write:

  summarize(llm, bodies_of(msgs))                        LOADS  (the workaround)
  summarize(llm, Iterable.map(msgs, lambda m -> m.body)) REFUSED -- 30:23: expected
    List[T = Text[Trust = Untrusted]], got Stream[T = Text[Trust = Untrusted], E = {...}]

`guardians/lib/vocabulary.anthill`'s `bodies_of` exists ONLY because of this — the trusted vocabulary has to supply a projection the agent cannot express. Its declaration says so.

WHAT TO DECIDE FIRST, because it is a design question and not a typo: whether the repair is (a) an eager consumer accepting any `FiniteCollection` / `Iterable` rather than a concrete `List`, (b) a materializing step the author writes (`collect`), or (c) `map`/`filter` on a finite carrier returning a finite carrier. WI-589 moved the eager drains to `FiniteCollection` precisely because an `Iterable` may be infinite, so (a) has to answer what happens on a `Stream` source and (c) has to answer it at the type level. The `MappedStreamFinite` / `FilteredStreamFinite` witnesses in `prelude/finite_combinators.anthill` are where (c) would live and are the reason it may already be close.

CELLS THAT TRACK IT: `typer_capability_matrix_test::lazy_stream_consumption`, four KNOWN GAP cells, each paired with its dot-free control. They FAIL when the gap closes, which is the signal to flip them to `Verdict::Loads` and close this item.

## Changes

### 2026-08-29T15:15:42Z — feedback — user

ONE CLAIM IN THIS TEXT IS NOW FALSE, corrected while delivering WI-20260829-9TGP7. It
does not touch the gap this ticket is about, only its stated CONSEQUENCE.

The text says: "`guardians/lib/vocabulary.anthill`'s `bodies_of` exists ONLY because of
this -- the trusted vocabulary has to supply a projection the agent cannot express. Its
declaration says so."

MEASURED, through the whole guardians checker rather than a bare load, both spellings the
ticket names now work once the stream is materialized:

  msgs.map(lambda m -> m.body).collect()                                    LOADS
  msgs.map(lambda m -> match m case message(i,f,r,s,b) -> b).collect()      LOADS

and the article's attack stays refused through both, with the taint diagnostic unchanged
("expected Text[Trust = Public], got LlmOutput[T = Text[Trust = Untrusted]]") -- so the
inlined projection preserves `Untrusted` rather than laundering it. Row:
`guardians_test::an_agent_can_inline_the_body_projection`.

Two things changed since this was written. (1) The match-destructure spelling was refused
by WI-20260829-9TGP7 (`map`'s free `Dst` used as a BOUND on a match arm rather than as a
hint), now fixed. (2) The dot spelling's `<unresolved receiver>.body` was never real: it
was a missing-`Iterable`-import artefact in the probe that reported it, already corrected
on WI-20260829-9TGP7's own feedback.

WHAT THIS TICKET STILL OWNS IS UNCHANGED, and the `.collect()` in both rows above is
exactly it: `summarize(llm, msgs.map(...))` without the materialization is still refused
with "expected List[T = Text[Trust = Untrusted]], got MappedStream[...]". The gap is real
and the four paired cells in `lazy_stream_consumption` still track it. What is no longer
true is that anything in guardians is BLOCKED by it -- `collect` is a spelling an author
can write, so the consequence to cite is ergonomic, not "the agent cannot express it".

`bodies_of` STAYS regardless, and not because of this gap. `docs/design/measured.md` settled
that under C7 before either fix: a message's body genuinely is a projection and the label
genuinely rides along it, so it earns its place as ordinary API. Its declaration comment
said the opposite and has been rewritten to say what is measured.

