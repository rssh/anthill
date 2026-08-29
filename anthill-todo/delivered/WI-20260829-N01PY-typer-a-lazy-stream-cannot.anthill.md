## Attributes

- id: WI-20260829-N01PY-typer-a-lazy-stream-cannot
- created: 2026-08-29T09:50:52Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T18:14:10Z

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

### 2026-08-29T14:22:18Z — feedback — user

`bodies_of` IS GONE (2026-08-29), so this ticket's "IT REACHES REAL CODE" paragraph
no longer describes the tree. The example now takes option (b) from WHAT TO DECIDE
FIRST — the author writes the materializing step:

  summarize(llm, msgs.map(lambda m -> m.body).collect())   LOADS

Measured against good.anthill by substituting only the summarize argument, and the
guardians suite is 35/35 with every fixture written that way. So `collect` is a
WORKING workaround at one call shape, which narrows what this ticket buys: not "the
projection is inexpressible" — it is expressible — but that `xs.map(f).length()` and
every eager consumer over a lazy carrier still needs a materializing step the author
must know to write.

WHAT THIS DOES NOT SETTLE. Taking (b) at one call site is not choosing (b) as the
design. The four `lazy_stream_consumption` cells are unchanged and still KNOWN GAP;
(a) and (c) remain open, and `MappedStreamFinite` / `FilteredStreamFinite` are still
where (c) would live.

The declaration this cites is also relocated: the mail vocabulary moved to
`examples/guardians/lib/email.anthill`, and the record of `bodies_of`'s deletion —
with the before/after measurement — is the comment between `Email.fetch` and
`Email.send` there.

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

### 2026-08-29T16:37:09Z — feedback — user

DELIVERED, and the re-measurement MOVED THE SUBJECT. Two of this ticket's three
candidate repairs were already in the tree; the third was missing for a reason the
ticket did not name, and the headline ("a LAZY STREAM cannot feed an EAGER consumer")
is refuted by the very cells that were tracking it.

WHAT THE FOUR TRACKED CELLS WERE MEASURING. `List.length` over a `MappedStream`. That
is `List`'s OWN operation and a mapped stream is not a `List` — the refusal is right and
will stay. Measured beside it, on the same fixture:

  length(xs.map(lambda r -> r.a))     REFUSED   -- expected List, got MappedStream[...]
  size(xs.map(lambda r -> r.a))       LOADS     -- (c), delivered by WI-590's witness
  xs.map(lambda r -> r.a).size()      LOADS
  collect(xs.map(lambda r -> r.a))    LOADS     -- (b), the materializing step
  xs.map(...).foldLeft(0, f)          LOADS

So (b) and (c) both already worked, and the four probes had never run the `size` row
next to the `length` one. That is this file's own lesson one level up: a PAIR whose two
members agree still says nothing when neither varies the axis that decides.

WHAT WAS GENUINELY MISSING WAS (a), and not as a design road not taken -- it was
UNWRITABLE. An eager consumer an AUTHOR declares over the spec refused the very value
`.size()` dispatches on:

  operation total(c: FiniteCollection) -> Int64 effects c.E = size(c)
  total(xs)                     LOADS
  total(xs.map(lambda r -> r.a))  REFUSED -- expected FiniteCollection, got MappedStream[...]

ROOT: TWO READERS OF ONE RELATION. `load_provides_clause` files
`SortProvidesInfo(sort_ref = <the ENCLOSING sort>)`, so a WITNESS -- which names its
carrier only in the spec's carrier BINDING (`sort MappedStreamFinite provides
FiniteCollection[C = MappedStream[...]]`) -- files under the WITNESS, not the carrier.
DISPATCH reads the spec-base bucket and matches each provision's carrier binding, so it
sees the witness. The SUBTYPE relation asked the carrier-keyed `sort_provides`, which
answers FALSE for a carrier that is fully spoken for. `provision_carriers_of_spec`'s doc
had already written that asymmetry down -- for the eq-derive reader, where WI-450 hit it
first. This is the same asymmetry at the subtype reader.

MINIMAL AND GENERAL, four rows, one axis (HOW THE PROVISION IS FILED), on a fixture with
no stdlib in it:

                            | DIRECT provision | WITNESS provision
  dot dispatch `Cap.get(x)` | LOADS            | LOADS
  spec-typed ARG `sink(x)`  | LOADS            | REFUSED  <- the gap

FIX: `witness_provides_admissibly`, a third leg on the `(parameterized, sort_ref)` arm of
`types_compatible_term_dispatch`, tried only after `sort_sym_compatible` and
`sort_provides_admissibly` have both refused (so it can only turn refusals into accepts).
It gates on a witness of the expected spec keyed on the actual's carrier -- one
`by_spec_base` bucket read, `false` for almost every pair -- then asks
`spec_resolves_at_bindings`, the resolver DISPATCH uses. Deferring to that resolver is
what keeps the witness's CONDITION enforced: a witness is a conditional instance
(`MappedStreamFinite requires FiniteCollection[C = S]` -- "finite WHEN ITS SOURCE IS"),
so accepting on the head alone would make a mapped stream over an infinite generator
eagerly consumable, the exact unsoundness FiniteCollection exists to prevent.

TWO SIMPLER SPELLINGS WERE MEASURED WRONG FIRST, each green on one arm and red on the
other -- which is what the two fixtures are for. Omitting the sibling bindings makes
`collect_provides_candidates` drop every candidate ("a type param the goal omits IS
discriminating"). A WILDCARD in the sibling slot cannot work for both candidate shapes
and that is a RULE, not an accident: against an impl-param head binding a wildcard is
accepted un-constrained (WI-507), against a CONCRETE one it must not be (WI-824 -- an
abstract per-call value must not match a concrete candidate). The goal now takes each
sibling from THAT PROVISION'S OWN HEAD, so nothing is invented.

TESTS: `n01py_witness_provision_subtype_test` (10 rows: 4 minimal + 3 stdlib + the
finite/infinite pair + the erased-`Iterable.map` boundary), and
`typer_capability_matrix_test::an_author_declared_consumer_takes_a_finite_carrier` (9
cells). `lazy_stream_consumption`'s four `KnownGap` cells are re-verdicted
`RefusesLocated("expected List")` -- the refusal is correct -- and the file's header now
records both misattributions.

BACK-OUT (full workspace, `witness_provides_admissibly` returning `false` at its first
statement): 6084 passed, 5 failed, ALL FIVE in the new file, plus the 2 matrix cells when
run with it. Nothing else in the workspace moves. The back-out also caught a flaw in MY
OWN control: `the_same_consumer_over_a_list_is_the_control` shared its program with the
two arms, so it failed on the back-out too; it has its own program now.

WHAT THIS TICKET DOES NOT COVER, stated rather than left to be rediscovered:
  * `List.length` on a lazy carrier stays refused, deliberately.
  * The BOUND spec-view parameter (`FiniteCollection[C = ?C, Element = Int64, E = ?E]`)
    still refuses everything, including a plain `List` -- that is WI-20260829-GNPG7, and
    this fix does not prejudge it: the row it changes is the BARE spec name, which GNPG7
    already measures as ACCEPTING a direct provider.
  * `Iterable.map` / `Iterable.filter` DECLARE a bare `Stream` return, erasing the source
    sort, so the named spellings still cannot feed an eager consumer while the dot
    spelling can. That is deliberate and pinned (`iterable.anthill`'s own note, and
    `wi492::lazy_map_iterator_count`) -- an `Iterable` may be infinite.
  * A witness whose condition is met only by the CALLER's own `requires` is still
    refused: the subtype relation has no call site, so the leg resolves with an empty
    `available_requires`. Narrower than dispatch, wider than before. Written down at
    `witness_provides_admissibly`.

FOUND AND NOT FIXED HERE (filed separately): `xs.map(f).map(g)` and
`xs.filter(p).filter(q)` DO NOT LOAD AT ALL -- `MappedStream.map` / `FilteredStream.filter`
are static constructors on the carrier that SHADOW the spec combinator in dot dispatch,
and their `EffS` does not ground from the receiver's provision. The MIXED chains
(`map.filter`, `filter.map`) load, because the carrier has no member of that name and
dispatch falls through to `FiniteCollection`. A different root from this one.

### 2026-08-29T16:37:50Z — feedback — user

The chaining defect named at the end of the delivery note is filed as WI-20260829-X13YV.

### 2026-08-29T18:04:06Z — feedback — user

/code-review ROUND, and it found a HARD BLOCKER plus a crash I had shipped. Both are
fixed; two more findings did not reproduce and are recorded as measurements rather than
repairs. The delivery note above stands except for the back-out figures, which it now
states wrongly -- they were taken before the second call site existed. CORRECTED: full
workspace, `witness_provides_admissibly` returning `false` at its first statement,
6085 passed / 8 FAILED, all eight in `n01py_witness_provision_subtype_test` and
`typer_capability_matrix_test::an_author_declared_consumer_takes_a_finite_carrier`.

(1) BLOCKER -- THE LEG ENLARGED `spec_carrier_param`'s POPULATION AND TRIPPED WI-954.
`wi1000_secondary_entry_content_test::a_dotted_declaration_name_is_not_the_entrys_content`
ABORTED the load: "`test.wi1000.dotp.Rec` declares `…Rec.Inner.T` as a type parameter but
no canonical variable was published for it". `published_param_var`'s own doc records that
tripwire as "LATENT, NOT LIVE ... measured, 29 binaries, 4441 tests" -- true only because
`spec_carrier_param` was asked about sorts NAMED IN PROVISIONS. My first cut asked it
BEFORE the provisions gate, i.e. about every bare expected sort in a failed compatibility
check. In a RELEASE build the `debug_assert` vanishes and the parameter is silently
dropped instead, which is the WI-384/WI-954 defect itself. FIX: the provisions scan runs
FIRST and returns on an empty result, so the population is exactly what it was.

(2) A CRASH I INTRODUCED -- STACK OVERFLOW, on a program that was a clean type error
without the leg. The leg answers a subtype question by calling `resolve`, and `resolve`
calls back into the subtype relation to match a candidate head. A provision whose carrier
binding is the SPEC ITSELF closes the loop. MEASURED both ways on a 30-line fixture.
`resolve`'s own cycle stack cannot see it -- it is allocated per `resolve` call. FIX:
`KnowledgeBase::witness_admissibility_in_flight`, keyed on the actual's `TermId` (NOT its
base symbol: base-keying would collapse `MappedStream[Source = List…]` onto
`MappedStream[Source = MappedStream…]` and suppress the feature for nested chains).
`false` at re-entry is the RIGHT answer, not a safe one: a question is not evidence for
itself, and the independent witness still answers -- the row asserts the VALUE 7, not
"no crash". Row: `a_self_carried_provision_beside_a_witness_does_not_recurse`.

(3) THE THIRD ARM, MEASURED AND LEFT -- filed as WI-20260829-2NMXA.
`types_compatible_view_structural`'s `(parameterized, sort_ref)` arm carries the contract
"mirror the term dispatch so provider admissibility stays carrier-symmetric", and with the
leg on the term side only it no longer does. A DENOTED effect row routes there:

  f(m: MappedStream[…, EF = {}])                        LOADS
  f(k: Cell[V = Int64], m: MappedStream[…, EF = {Modify[k]}])  REFUSED

I did NOT ship the leg there. `witness_provides_admissibly` asks through a `SortGoal`,
whose bindings are `TermId`s, and a denoted binding has none -- wiring it in and reading
`walk_view` was TRIED and is INERT (the actual comes back a `Value::Node`, the branch
never fires, the verdict does not move). A branch nothing can drive is not a fix. Both
rows ride as a paired KNOWN GAP: `a_denoted_effect_row_is_a_known_gap`.

(4) DID NOT REPRODUCE -- the entity->parent hop. The review read `ab =
parameterized_base_sym(actual)` as possibly a CONSTRUCTOR symbol, so a witness keyed on the
parent sort would be missed. Probed with an entity-parameterized actual (`boxed(v: 1)`
against `provides Cap[C = Box[T = T]]`): the actual arrives as the PARENT `Box[T = Int64]`
and the row LOADS. The measurement is now written at that call site.

(5) DID NOT REPRODUCE -- the unfiltered goal bindings. The review said this is the only
`SortGoal` producer not filtering keys with `is_type_param_binding`. Added the filter and
INSTRUMENTED it: it drops ZERO bindings across this file and the whole capability matrix
and changes no verdict, because `unwrap_spec_view` has already dropped every non-`TermId`
binding and an `effects E = ?` param IS a sort (WI-320), so the filter answers `true` for
the very binding it was expected to remove. A guard that refuses nothing is not shipped;
the measurement is written at the site instead. (The named sibling producer,
`declared_type_goal_bindings`, does not use that filter either -- it filters to
`Value::Term`.)

ALSO: the review found a live `eprintln!` debug probe of mine still in the tree. Removed.

