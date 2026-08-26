## Attributes

- id: WI-20260826-JSFHG-8-2-says-each-constructor-name
- created: 2026-08-26T07:13:24Z

- status: Open
- status_agent: user
- status_at: 2026-08-26T07:13:24Z

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

