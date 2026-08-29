## Attributes

- id: WI-20260826-7JDWY-a-hinted-list-set-literal
- created: 2026-08-26T08:24:29Z

- status: Open
- status_agent: claude
- status_at: 2026-08-26T08:24:29Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260828-5NSZY-typer-a-bare-operation-name-in

## Description

a HINTED list/set literal never consults its elements: TypeBuildFrame::ListLit takes element_hint as the element type UNCONDITIONALLY, so `operation mk() -> List[T = Int64] = ["x"]` LOADS CLEAN -- a silent type hole at every element type, and the reason a variant-typed argument slot cannot be given the hint it needs

## Changes

### 2026-08-26T08:24:57Z — feedback — claude

FOUND WHILE DELIVERING WI-20260826-JSFHG, and found by trying to USE the hole rather than by reading the build.

THE MECHANISM, named exactly. `TypeBuildFrame::ListLit` (and its `SetLit` twin) seeds the element type from the hint and then walks the elements ONLY to merge effects:

    let mut element_type: Option<Value> = element_hint;
    for r in group {
        if element_type.is_none() { element_type = Some(r.ty.clone()); }
        merge_effects_into(kb, &mut effects, &r.effects);
    }

So when a hint is present the elements' own types are never read at all. The hint does not CHECK the literal, it OVERWRITES it.

MEASURED, three rows that separate cleanly:

  operation mk() -> List[T = Int64] = ["x"]          LOADS CLEAN   <- hinted (declared return)
  operation takeInts(l: List[T = Int64]) -> Int64
  operation wrong() -> Int64 = takeInts(["x"])       REFUSED       <- unhinted (argument)
  operation takePair(p: (a: Colour.red, b: Int64))
  ... takePair((a: blue(v: 1), b: 2))                REFUSED       <- the TUPLE path, which DOES check

The first is the defect. It is not about variants and not about `Int64`: any element type behaves this way in any hinted position, which today means a declared return and a `nested_call_arg_hint` argument.

WHY JSFHG COULD NOT JUST FIX IT. That ticket needed to push a slot type down into a list literal at an ARGUMENT (`takeReds([red(v: 1)])` against `List[T = Colour.red]`). Building exactly that made `takeReds([blue(v: 1)])` -- the WRONG variant -- LOAD CLEAN, so the repair traded a correct refusal for a silent accept, and it was REVERTED. `wi_jsfhg_variant_type_is_inhabited_test::known_gap_a_list_literal_of_variants_is_refused_at_an_argument` carries all three rows above, including a positive assertion that `-> List[T = Int64] = ["x"]` still loads -- so CLOSING this hole makes that row fail LOUDLY and points at the argument-position hint that can then be restored.

WHAT TO DECIDE, since the fix is not simply "prefer the elements": the hint exists so an EMPTY literal and a polymorphic one get a type at all, and so a literal of a SUBTYPE conforms to a declared supertype element (`-> List[T = Colour] = [red(v: 1)]` must keep working -- the elements type at `Colour` there, but a mixed `[red(...), blue(...)]` needs the hint to avoid a join). So the shape is probably: use the hint as the DECLARED element type, and CHECK each element against it with the ordinary subtype relation, reporting per element at its own span rather than reporting one whole-list mismatch at the slot. That is strictly more precise than today's unhinted behavior too, which reports `expected List[T = Int64], got List[T = String]` at the argument instead of naming the offending element.

THE POPULATION TO MEASURE FIRST is every hinted literal in the corpus: a declared return whose body is a literal, and a `nested_call_arg_hint` argument that is one. Anything relying on the hint MASKING a non-conforming element is a program this would newly refuse, and each is either a real bug it just found or a variance case the check must admit.

