## Attributes

- id: WI-20260826-JSFHG-8-2-says-each-constructor-name
- created: 2026-08-26T07:13:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-26T08:37:34Z

- acceptance: cargo-test, scaland-sbt-test

## Description

§8.2 says each constructor name is a sort in its own right, and the SUBTYPING works both ways — but the variant type is UNINHABITABLE: every constructor application is typed at the PARENT sort, so no expression has type `Colour.red` and any parameter or return declared with one is unsatisfiable

## Changes

### 2026-08-26T07:13:54Z — feedback — claude

FOUND BY A QUESTION, not by a test: while delivering WI-20260826-XFTC7 I wrote a test comment asserting that "an enum constructor yields the ENUM, so a `Colour.red`-typed parameter is a narrowing position with no literal to pass it" — presenting a MEASUREMENT as if it were the language's rule. The user asked "is red not a type?", and §8.2 answers it: "Each constructor name is a sort in its own right", `C₁ <: S`, "A term classified as sort `C₁` is also of sort `S`". So the comment was describing a defect.

THE TYPE IS DECLARABLE AND CORRECTLY RELATED. Both halves of the subtyping are implemented, which is what makes this a narrow gap rather than a missing feature:

  operation takeAny(c: Colour) -> Int64 = 9
  operation relay(r: Colour.red) -> Int64 = takeAny(r)      -> LOADS      `red <: Colour` holds
  operation relay(c: Colour) -> Int64 = takeRed(c)          -> REFUSED    and not the reverse

NOTHING CAN HAVE IT. Every route to a value was driven, and every one types at the PARENT:

  takeRed(Colour.red(v: 1))          -> "expected red, got Colour"   qualified constructor
  takeRed(red(v: 1))                 -> "expected red, got Colour"   bare constructor
  operation mkRed() -> Colour.red = red(v: 1)
                                     -> "expected red, got Colour"   declared return
  match c case red(x) -> takeRed(red(x))
                                     -> "expected red, got Colour"   inside a NARROWED arm

Identical for a plain `sort Colour { entity red(…) }` as for an `enum`, so it is not enum-specific. The last row is the sharpest: even where the program has already discriminated on the variant, re-constructing it yields the parent. So a signature written with a variant type is not merely awkward — it is UNSATISFIABLE, and it loads clean, which is the silent half.

THE MECHANISM IS NAMED AND DELIBERATE-LOOKING, so this needs a decision rather than a patch. `typing::constructor_value_type`'s own doc: "look up the constructor's parent sort + declared field types, unify each child type against its field's declared type … then `reconstruct_sort_params` + build `Sort[params]` (or the bare `Ref(Sort)`)". The result type is the parent by construction, and `check_constructor_iter` is its error-producing twin. Whether that is a decision (one nominal type per sort, variants being tags) or an oversight is not recorded anywhere I could find; §8.2 says the opposite, and the two have to be reconciled in one direction or the other.

WHAT TO DECIDE:
  * IF §8.2 IS THE RULE — `constructor_value_type` should return the CONSTRUCTOR's own sort ref, with the parent reached by the existing `EntityOf` subtyping (already working, per the widening row above). The census to run first is every site that compares a constructed value's type against a declared one: a narrowing that used to succeed by equality would now succeed by subtyping, and anything asking for structural EQUALITY of types would flip.
  * IF THE IMPLEMENTATION IS THE RULE — §8.2's "each constructor name is a sort in its own right" needs the qualification that no VALUE is ever classified at it, and the type position should REFUSE a variant name rather than admit an unsatisfiable one. Admitting it is the worst of the two, because the program loads.

NOT INTRODUCED BY XFTC7 AND NOT WIDENED BY IT: that ticket's kind gate admits `SymbolKind::Entity` precisely so `Enum.Entity` keeps working as it always has (it is one of the two cases `try_rigid_type_projection`'s own comment names). Narrowing the gate to `Sort` alone would have refused these signatures — which is one of the two options above, taken by accident, so it was deliberately not taken. `wi_xftc7_…::every_shape_that_is_a_type_still_passes_the_gate` asserts the signature LOADS and drives the two shapes that can carry a value, with the reason stated at the row.

### 2026-08-26T08:37:29Z — feedback — claude

DELIVERED, AND THE TICKET'S TWO OPTIONS WERE BOTH MEASURED BEFORE A THIRD WAS TAKEN.

OPTION 1 WAS BUILT AND DOES NOT FIT IN THIS TICKET. It prescribed that
`constructor_value_type` return the constructor's own sort ref. Implemented exactly, every
application types at the variant and THE STDLIB STOPS LOADING -- 16 distinct errors in FIVE
roots, each a separate reader needing its own entity->parent widening:

  * same-family conformance     expected List[T = ?T], got cons[T = ?T]
  * provider admissibility THROUGH the entity (the provision is on the PARENT, so
    `provider_spec_view_bindings(mapped, Stream)` finds nothing)
                                expected Stream[...], got mapped[Src = ?S, T = ?Dst, ...]
  * a type PROJECTION on an entity base
                                'anthill.prelude.FilteredStream.filtered' has no member 'E'
  * effect LABELS, compared by structural identity by design
                                expected Error[T = EmptyStream], got Error[T = empty_stream]
  * and the compounding one -- entity types nested inside every binding
                                got some[T = pair[A = ?T, B = mapped[...]]]

MEASURED rather than predicted: instrumented, the base check ALREADY widens (30 `cons vs
List`, 3 `mapped vs Stream` pairs pass it). What fails is UNIFY, which is EQUALITY and
cannot be taught subtyping without ceasing to be unify. That is a type-system-wide change.

OPTION 2 -- refuse the type -- deletes what 8.2 promises, and the ticket's own reading is
right that admitting an unsatisfiable type is the worst of the three.

DELIVERED: THE CHECKING DIRECTION DECIDES THE CLASSIFICATION. Where the expected type names
a constructor the application is classified there; everywhere else it keeps typing at the
parent. Both readings satisfy 8.2's own sentence, and the parent one is load-bearing rather
than legacy -- it is what lets two arms returning different constructors join at a declared
`-> Colour`. ONE predicate, `type_head_names_an_entity`, is asked at both ends of the
decision, so the two readers cannot drift.

DRIVEN TO VALUES -- the ticket's four routes, plus five positions /code-review found:

  takeRed(red(v: 41)) / takeRed(Colour.red(v: 7))   -> 41 / 7   both ctor spellings
  mkRed() -> Colour.red; takeRed(mkRed())           -> 9        declared return, and the
                                                                RESULT is still a variant
  match c case red(x) -> takeRed(red(v: x))         -> 5        narrowed-arm reconstruction
  holder(c: red(v: 12)), read back as h.c.v         -> 12       entity FIELD channel
  takeSome(some(1)) : Option.some[T = Int64]        -> 21       parametric variant, and the
  takeAny(some(1))  : Option[T = Int64]             -> 22       SAME expression still fills
                                                                a plain slot
  takeRed(red) and takeRed(red())  on `entity red`  -> 31 / 31  FIELDLESS, 8.2's own example
  takePair((a: red(v: 1), b: 23))                   -> 23       named-tuple component
  r.shout() on r: Colour.red                        -> 3        dot through a variant
  r.v where Colour also declares `operation v`      -> 5        the FIELD, not the op (99)

WHAT /CODE-REVIEW CHANGED, and it changed the shape of the delivery. It found FOUR positions
the first cut left uninhabitable, none a variation on the others -- each reaches the
classification down a different channel and each was refused for its own reason.

THE FIELDLESS BARE SPELLING NEEDED THREE FIXES FOR ONE ROW, none guessable: `check_bare_ref`
passed a hard `None` where every other route threads `expected`; the gate read
`entity_field_types`, which a FIELDLESS entity has no entry in, so it answered false for
exactly the shape 8.2 illustrates the feature with; and the bare name arrives as
`Expr::VarRef`, not `Ref`/`Ident`, so a first repair still refused it. Each arm of the gate
now borrows ITS OWN destination's predicate -- `check_constructor_iter` reads field-types,
`check_bare_ref` reads `is_constructor_symbol` -- rather than one predicate being chosen for
all three.

DOT DISPATCH was the highest-impact one: `r.shout()` reported "no such member" while the
named `Colour.shout(r)` resolved and the widening `takeAny(r)` was accepted -- one value,
two answers, the position-dependence WI-752 exists to abolish. The three rungs that search
the receiver's sort search the CONSTRUCTOR, which declares no operations. A parent rung is
added, PURELY ADDITIVE (consulted only where every rung above answered `None`) -- but that
is exactly where the frame falls through to FIELD ACCESS, so without a guard it would STEAL
an entity's own field whenever the parent declares a same-named operation. Measured: with
the guard dropped, `r.v` answers 99 (the operation) where the field says 5.

THE FOURTH WAS BUILT AND REVERTED, AND THAT IS THE CORRECTION WORTH RECORDING. A list
literal in a variant-typed argument slot looked like the same fix. With the hint in place,
`takeReds([blue(v: 1)])` -- the WRONG variant -- LOADED CLEAN: `TypeBuildFrame::ListLit`
takes `element_hint` as the element type UNCONDITIONALLY and never reads what the elements
typed as, so the hint does not CHECK the literal, it OVERWRITES it. The review was right
about the asymmetry and the direction that "works" is the broken one -- `operation mk() ->
List[T = Int64] = ["x"]` loads clean today, at every element type, nothing to do with
variants. Reverted; the hole filed as WI-20260826-7JDWY. The gap row here asserts that
`-> List[T = Int64] = ["x"]` STILL LOADS, so closing 7JDWY fails loudly at this file and
points at the argument hint that can then be restored.

TWO GATE OMISSIONS in the hint machinery had to move with the main change, neither in the
ticket: the declared param/field type was never LOOKED UP for a constructor argument
(`has_call_arg` matches only the `Expr::Apply` spelling, so the field-named build
`takeRed(red(v: 1))` matched none of the three gates and the hint was asked with `None`) --
the exact peer of what WI-206/707 added there for a sort-naming argument, and the identical
omission on the Constructor arm. Widening a shared gate is the hazard, so the CONTAINMENT is
argued at both sites: the calls newly looking `op_info` up have no hof / call / sort-naming
argument, and each older hint is gated on the argument shape whose absence defines that
case, so only the new hint can fire where it could not before.

SOUNDNESS IS A POPULATION ARGUMENT: before this ticket a slot declared with a variant type
was UNSATISFIABLE, so no loading program has one for a hint to reach. The change turns
refusals into acceptances and never the reverse -- and the corpus measures it: 5771 passed /
0 failed, which is the XFTC7 baseline of 5752 plus exactly the 19 rows added, so nothing
moved.

THE EXPECTATION IS NOT ASSUMED: `classify_sym` names OUR OWN `ctor_sym`, never the head the
hint carried, so `takeRed(blue(v: 1))` classifies at `blue` and is refused. The diagnostic
now names both variants -- it used to say "got Colour", naming the PARENT of a value the
compiler knew exactly.

MY FIRST STATEMENT OF THE CONTROLS WAS WRONG, AND THE CORRECTION IS THE METHOD. I named four
rows as passing either way; measured under the back-out, THREE failed -- each had a control
assertion sharing a fixture with a DRIVEN one. Split, so a row is either an ARM or a CONTROL
and never both. And ONE mutation cannot separate THREE claims, so there are three axes, each
measured on its own: the CLASSIFICATION (13 rows fail), the DOT RUNG (exactly 1), the
FIELD-PRECEDENCE guard (exactly 1, and by its VALUE -- Int(99) vs Int(5) -- not by loading).
19 rows: 13 arms, 4 controls, 2 known gaps.

THE RESIDUALS, ALL THREE PINNED, none silent:
  * an INFERENCE position keeps the parent (`let r = red(v: 1)`); the annotated spelling
    works. Closing it is option 1, at the cost above.
  * a LIST/SET literal in an argument slot stays refused -- deliberately, per 7JDWY.
  * the WI-408 auto-`some` coercion does not fire at an `Option.some`-typed field, where the
    wrap would produce precisely the expected type. Its recognizer reads the parent head; a
    fifth reader of the same question, and whether a slot demanding `some` should silently
    manufacture one is a design question rather than an oversight.

TWO SELF-INFLICTED DEFECTS CAUGHT IN MY OWN DIFF REVIEW: a doc insert anchored on the `fn`
line STOLE `finish_constructor_type`'s doc comment (invisible to compiler and suite), and
that function's parameter needed renaming -- it is no longer "the parent type" but "the
symbol to classify at", a caller's decision rather than the function's.

SPEC: 8.2 gains "Which sort a constructor application is classified at" -- both readings and
why neither can be dropped, the positions that admit a variant (including the fieldless bare
spelling), member reach through the variant with field precedence, the sibling refusal, and
all three residuals with their reasons.

FINAL: rustland 5771 passed / 0 failed across 36 binaries (XFTC7 baseline 5752, +19 rows);
scaland 538 passed / 0 failed -- it has no typing module at all (`kb`, `resolve`, `parse`,
`term` only), so there is no constructor classification to keep in step there.

