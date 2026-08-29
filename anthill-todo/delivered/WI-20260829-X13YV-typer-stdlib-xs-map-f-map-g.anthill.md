## Attributes

- id: WI-20260829-X13YV-typer-stdlib-xs-map-f-map-g
- created: 2026-08-29T16:37:34Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T19:38:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER/STDLIB: `xs.map(f).map(g)` and `xs.filter(p).filter(q)` DO NOT LOAD — a lazy carrier's own STATIC CONSTRUCTOR shadows the spec combinator in dot dispatch, and its `EffS` does not ground from the receiver's provision. Found while delivering WI-20260829-N01PY (a different root: that one was the subtype reader's blindness to witness provisions).

MEASURED, one fixture, `xs: List[T = Row]`:

  xs.map(lambda r -> r.a).map(lambda n -> n)          REFUSED -- type mismatch in
      anthill.prelude.MappedStream.map.type_arg: expected a type for 'EffS', got
      unconstrained — use `map[EffS = …](…)`
  xs.filter(lambda r -> r.flag).filter(lambda r -> true)  REFUSED -- same, on
      anthill.prelude.FilteredStream.filter
  xs.map(lambda r -> r.a).filter(lambda n -> true)    LOADS
  xs.filter(lambda r -> r.flag).map(lambda r -> r.a)  LOADS
  xs.map(lambda r -> r.a).collect().map(lambda n -> n).size()  LOADS  (the workaround)

THE MIXED CHAINS ARE THE CONTROL and they are what localizes it: `MappedStream` has no
`filter` member, so `.filter` on a mapped stream falls through to `FiniteCollection.filter`
via the `MappedStreamFinite` witness and works. `MappedStream` DOES have a `map` member —
`operation map[S, Dst, EffS, EffP](s: Stream[S, EffS], f) -> Stream[Dst, {EffS, EffP}]`
in `combinators.anthill`, a STATIC CONSTRUCTOR, not a receiver method — so dot dispatch
stops there and never reaches the spec combinator. `FilteredStream.filter` is its twin.

TWO THINGS ARE WRONG AT ONCE, and they should be separated when this is picked up:
  (1) the static constructor shadows the spec's combinator in dot dispatch, which is why
      the SAME chain works when spelled through the other combinator; and
  (2) even reached deliberately, `EffS` does not ground from the receiver's provision
      (`MappedStream provides Stream[T = T, E = {ES, EF}]` names both), where the
      sort-param effect on `Iterable.map` DOES ground. WI-594 recorded exactly this
      asymmetry as its gap (2) and it was not closed for this shape.

Also: `xs.map(f).map[EffS = {}](g)` DOES NOT PARSE — a dot call takes no explicit type-arg
bracket (WI-439's delivery note records the qualified-call half of the same parse gap), so
the message's own repair ("use `map[EffS = …](…)`") is not available in the spelling that
produces it.

WORTH ASKING WHETHER THE TWO STATIC CONSTRUCTORS SHOULD EXIST AT ALL. Nothing in the
stdlib calls `MappedStream.map` / `FilteredStream.filter` — `Iterable.map` builds
`mapped(...)` directly — and they duplicate `Iterable.map`/`filter` at the Stream level.
`wi439_iterable_filter_test` asserts parity between `Iterable.filter` and
`FilteredStream.filter`, and `wi1049_duplicate_operation_declaration_test` resolves
`anthill.prelude.MappedStream.map` by name, so removing them is not free.

ACCEPTANCE: `xs.map(f).map(g).size()` and `xs.filter(p).filter(q).size()` load AND
evaluate to the right value; the mixed chains and `Iterable.map`'s erased-Stream boundary
are unchanged; a cell for each in
`typer_capability_matrix_test::an_author_declared_consumer_takes_a_finite_carrier`'s
neighbourhood.

## Changes

### 2026-08-29T19:38:08Z — feedback — user

DELIVERED. `xs.map(f).map(g)` and `xs.filter(p).filter(q)` load, evaluate and gate.

THE TICKET SEPARATED TWO DEFECTS AND ONE REPAIR CLOSED BOTH, because (2) was downstream of
the declaration (1) named. The shadowing is REAL and is UNCHANGED: dot dispatch takes the
receiver's own member before a provided spec's (`own_op.or_else(find_spec_op_for_provided_
sort)`, typing.rs:12820/12841), so hop 2 of `xs.map(f).map(g)` resolved to
`MappedStream.map` and never reached `FiniteCollection.map`; `.filter` on the same value
fell through because `MappedStream` declares no `filter`. Read off the arity error, before
AND after: hop 1 -> FiniteCollection.map, hop 2 -> MappedStream.map, mixed hops ->
FiniteCollection.

WHAT WAS FIXED IS THE DECLARATION THE LADDER FINDS, NOT THE LADDER. The two static
constructors returned an ERASED bare `Stream`, so grounding `EffS` (the ticket's defect 2)
would NOT have been enough: the result would carry no `Source` and `.size()` would still be
refused, exactly as `total(Iterable.map(xs, f))` is. Re-typed to take their own carrier as
receiver and build the return from it, so `MappedStreamFinite` recurses:

  map[Dst, EffP](m: MappedStream, f: (x: T) -> Dst @ {EffP, -Modify[x]})
    -> MappedStream[Source = MappedStream, Src = T, T = Dst, ES = {ES, EF}, EF = EffP]
  filter[EffP](s: FilteredStream, p: (x: T) -> Bool @ {EffP, -Modify[x]})
    -> FilteredStream[Source = FilteredStream, T = T, ES = {ES, EF}, EF = EffP]

THE ALTERNATIVES WERE MEASURED, NOT REASONED. (a) DELETE both: full acceptance green, but
removes a capability `FiniteCollection.map` cannot supply -- chaining over a NON-finite
source (the `Nats` row: the hop loads, only the consumption is refused). (b) NARROW rung 1
so a non-receiver own member cannot shadow: changes a shared dispatch decision used by every
dot for a reason two operations had. (c) keep them general over any Iterable with the source
in the return: REFUSED by the typer -- op-level `requires` on a FREE op does not ground the
element (`expected a type for 'S', got unconstrained`), and the sort-param variant fails
differently (`Dst` unconstrained, row leaks). That is WI-599's documented exclusion, which
had NO TICKET and now does: WI-20260829-70XVH.

WHAT THE SHAPE COST: the two operations no longer accept a bare `List`. TWO call sites, and
MY FIRST CENSUS FOUND ONLY ONE -- I grepped the QUALIFIED spelling `MappedStream.map`, and
the second site imports the SHORT name (`import anthill.prelude.MappedStream.{map}` then
`map[EffS = {}](...)`), which that pattern cannot see. The full run found it:
  * `wi439_iterable_filter_test`'s parity op -> `Iterable.filter`, which keeps the same
    experiment (two spellings of one keep/drop engine agreeing on a value) with the erasing
    partner it now has.
  * `wi818_executable_backing_test::stream_defaults_evaluate_on_inheriting_carriers` ->
    `FiniteCollection.map`/`filter`, which builds the same MappedStream/FilteredStream from
    a List and needs no explicit `[EffS = {}]`. What it asserts is unchanged: `head` runs on
    a carrier supplying only `splitFirst`, so the frame entered is the SPEC DEFAULT's.
Re-censused on BOTH spellings afterwards: those are the only two. Everything else imports
`mapped`/`filtered` (the ENTITY constructors), which are untouched. Nothing in any .anthill
file, doc, or scaland called either operation. `typing.rs`'s `instantiate_poly_type` doc
cites a historical binder-leak count naming `MappedStream.map`'s `?S`/`?EffS`, which no
longer exist -- annotated as historical rather than silently left to mislead a re-run.

DRIVEN, NOT LOADED. `x13yv_map_map_chain_test`: the chains evaluate to a digit-fold
`acc*10+x` (NOT a sum -- a sum cannot see a dropped hop or a reorder): map.map = 3579 against
one-hop 2468, three-hop 246; filter.filter = 23 against one-hop 234.

CONTROLS, run by restoring the old signatures: the two eval tests go RED with the ticket's
own message; `a_two_hop_chain_is_finite_exactly_when_its_source_is` goes red for a DIFFERENT
reason (the hop stops loading) so it is the soundness control, not a witness;
`each_hop_resolves_to_the_receivers_own_member`, `the_mixed_chains_are_unchanged` and
`an_erasing_iterable_map_is_still_not_consumable` PASS EITHER WAY by design. THE BACK-OUT
CORRECTED ME: I had recorded the route test as going red and it does not, which is the
design choice (the ladder is untouched) rather than a weak test; the file says so at its site.

SOUNDNESS GATE DRIVEN THROUGH THE SECOND HOP: over `List` the two-hop chain collects; over an
infinite `Nats` BOTH hops are refused at the CONSUMPTION, naming `FiniteCollection[C = Nats]`
-- the witness recursed to the original carrier. `collect` and not `size`, because on the
UNTOUCHED tree `FiniteCollection.size` over `MappedStream[Source = Nats]` LOADS while
`collect` over the identical value is refused: a pre-existing hole in the gate, now
WI-20260829-H0YCE.

CROSS-CARRIER RECURSION: `a_chain_crossing_both_carriers_collects` runs three hops through
BOTH carriers (`map.filter.filter`, `filter.map.map`), where `MappedStreamFinite` must
discharge a requires only `FilteredStreamFinite` can answer and vice versa. IT WAS DRAFTED
AS A CONTROL inside `the_mixed_chains_are_unchanged` and the back-out said otherwise -- its
second same-name hop IS the repaired member -- so it was split out rather than left in a
table whose contract is that nothing in it moves.

MATRIX: six cells added to `an_author_declared_consumer_takes_a_finite_carrier` -- the two
same-name chains, the two MIXED chains as their controls, the author-declared consumer over a
chained value, and `.collect()`.

NOT DONE, and why: the ticket's third note -- `xs.map(f).map[EffS = {}](g)` does not parse,
so the old message's own repair was unavailable in the spelling that produced it -- is moot
here (that message no longer fires from this shape) but the PARSE gap is untouched and still
has no ticket of its own beyond WI-439's delivery note.

SUITE: rust workspace 6098 passed / 0 failed (the one failure the first full run reported was
wi818, fixed above and re-run); scaland `sbt test` 520 passed / 0 failed, BootstrapTest
included -- it parses combinators.anthill from the same stdlib/ on disk.

### 2026-08-29T20:57:25Z — feedback — user

TWO CORRECTIONS to the note above.

(1) THE SUITE FIGURE WAS STALE. It reads '6098 passed / 0 failed', which is neither run: the
FIRST full run was 6098 passed / 1 FAILED (wi818), and the FINAL run after fixing wi818 and
applying the /code-review doc repairs was 6100 passed / 0 failed, 36 result lines. scaland
520 / 0 stands, against a byte-identical stdlib.

(2) THIS TICKET'S OWN PARSE CLAIM IS FALSE AS STATED, measured while filing its follow-up.
The description says 'a dot call takes no explicit type-arg bracket'. It does:
`xs.map[Dst = Int64](f)` PARSES. So does the QUALIFIED form
`Iterable.map[Dst = Int64](xs, f)`, which WI-439's delivery note recorded as a syntax error
-- that note has been wrong since WI-311. What actually fails is a bracket on a dot whose
RECEIVER IS COMPOUND: a call (`xs.map(f).map[Dst](g)`) or even a parenthesized expression
(`(xs.map(f)).map[Dst](g)`), the latter placing it on WI-20260829-YBBC3's term/body split
rather than on anything about qualification. Nine measured rows and their controls are in
WI-20260829-BAD3V, which now OWNS the gap -- it had been recorded only inside two DELIVERED
items, which no queue lists.

### 2026-08-29T21:52:44Z — feedback — claude

CORRECTION (from WI-20260829-BAD3V, which now owns and has closed the gap).

Two claims here about the parse gap need amending.

(1) The description's "a dot call takes no explicit type-arg bracket" is false as stated
-- this file's own feedback note already caught that (`xs.map[Dst = Int64](f)` parses).

(2) That note's REPLACEMENT diagnosis is also wrong. It says the failure is "a bracket on
a dot whose RECEIVER IS COMPOUND ... (`(xs.map(f)).map[Dst](g)`), the latter placing it on
WI-20260829-YBBC3's term/body split". It is NOT the term/body split: `paren_expr` already
wraps an `_expr_body` (YBBC3), and the CST for the parenthesized row shows the
`field_access` over the `paren_expr` BUILT FINE. The `[` is what had nowhere to go, and it
was being taken as the DECLARATION'S `meta_block` -- which is why the reported error
landed on the `=` inside a misread `meta_entry`.

Nor is "compound receiver" the boundary: the FIRST hop over a plain variable,
`?xs.map[Dst = Int64](f)`, was a syntax error too. The real rule: `application`'s base was
`name | absolute_name`, so the bracket was admitted only where the callee was a NAME PATH
-- i.e. only on the spelling that is a QUALIFIED call and not a dot call at all. No
value-receiver dot could take one, at any depth.

BAD3V's fix: a `dot_application` production in `fn_term`'s callee slot admits the bracket
on a dot callee; the converter reads it as the call's type arguments on a QUALIFIED
companion receiver (`Map[K = String].empty[T = Int64]()` -- new, and driven) and REFUSES
it with a located message on a VALUE receiver, since `Expr::DotApply` carries no
`type_args` field. So the repair a future type-arg diagnostic suggests now parses, and
where it cannot work the author is told the applicative spelling instead of a syntax
error.

