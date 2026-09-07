## Attributes

- id: WI-20260826-7JDWY-a-hinted-list-set-literal
- created: 2026-08-26T08:24:29Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-07T10:24:54Z

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

### 2026-09-07T10:24:48Z — feedback — claude

DELIVERED. A `[…]` / `{…}` whose position DECLARES an element type is now CHECKED against it, element by element, at the offending element's own span and position: `4:39: type mismatch in list.element 3 (collection-element): expected Int64, got String`. The ticket's own row, `operation mk() -> List[T = Int64] = ["x"]`, is refused; before it loaded clean and `List.head(mk())` answered `Str("x")` out of a slot the signature types `Int64`.

THE TICKET NAMED A SITE THAT IS NEARLY INERT, and the census is the finding. It named `TypeBuildFrame::ListLit` / `SetLit` and quoted their code; both DO have the defect and both are almost never reached. Instrumented over the whole workspace suite: the two frames are entered 4 times, every one of them with NO declared element type to overwrite. A source literal in an operation body arrives on a THIRD carrier the ticket did not name — `check_seq_literal_constructor`, the un-lowered `constructor(ListLiteral, …)` §4.6 leaves behind outside a rule/fact data slot — entered 964 times, 605 with a declaration, covering 13693 elements. A repair made only where the ticket pointed would have compiled, reviewed clean, and changed nothing an author can write. The rule now has ONE owner, `seq_literal_element_type`; a fourth, value-level, carrier (`seq_literal_value_type`) was open-coding the same `List[T = …]` build and now goes through `seq_literal_type` too.

WHAT WAS DECIDED, since "prefer the elements" is not the fix. The declaration stays the ANSWER and the elements are the CHECK — `-> List[T = Colour] = [red(v: 1), blue(v: 2)]` must keep working, and its two elements type at two different constructors that only the declared `Colour` covers. The judgement is `validate_arg_against_param`, the relation an argument already gets, so the groundness gate and the boundary conversions are the ones in force elsewhere rather than a second opinion. A `WrapSome` is REPORTED, not inserted: inserting is a new capability with an empty population (measured: zero elements reach that arm), while refusing replaces a program that loaded and left the element bare at runtime.

THE ARGUMENT-SLOT HINT IS RESTORED, which is what the ticket said closing this would buy. WI-20260826-JSFHG built it, measured `takeReds([blue(v: 1)])` loading clean, and reverted it. It is back, and the pair separates the two halves: `takeReds([red(v: 1)])` drives 17, `takeReds([blue(v: 1)])` is refused `expected red, got blue`. The classification §8.2 needs also had to reach the element — a constructor element with no expectation of its own types at its PARENT — so the constructor carrier now pushes the declared element type into its elements, as the `ListLit` frame already did.

FOUR AXES, FOUR BACK-OUTS, each a run of the whole `wi_tests` binary: the element CHECK 11 fail / 4227 pass; the element HINT at the constructor carrier 4 / 4234; the argument-slot HINT 3 / 4235; the `List`/`Set` HEAD test 1 / 4237. Two of the sets were PREDICTED WRONG before being run and the corrections are recorded at the file: the nested-literal row does not survive axis 2 (the inner literal loses its own declaration, so the reported pair changes), and axis 3 fails two rows rather than one. Three controls are green under all four.

WHAT `/code-review` (high) FOUND — five, all acted on, three of them corrections to things I had WRITTEN DOWN as reasons.
 (1) The UN-HINTED arm still reads element one and never the rest, so `takeInts([1, "a"])` loads clean. That is WI-20260829-WBXGX, open, with its own census; I did not close another item's question on a population nobody has measured. It is now stated inside the shared owner and PINNED by an assertion in the control row, so the asymmetry is a measurement rather than a comment.
 (2) `extract_type_param(expected, "T")` was blind to the expectation's HEAD, so an unrelated `T` was pushed down and then blamed on an element: `-> Option[T = List[T = Int64]] = [1]` reported `list.element 1 … expected List[T = Int64], got Int64`, about a list not in the program. One owner, `declared_element_type`, now gates on a `List`/`Set` head and feeds BOTH the push and the check so they cannot drift. Axis 4 is its back-out and fails exactly one row, which is what says it moved a message and no verdict.
 (3) The containment claim I inherited from JSFHG — "it can only turn a refusal into an acceptance, never the reverse" — is FALSE of the restored arm, because this ticket adds the check the argument was written without. Measured: `takeReds([r, c])` with `r: Colour.red, c: Colour` refuses now and loaded before, since element two was never looked at. The ARGUMENT is retired, not the behaviour, and a row owns it — a future widening of that gate must not lean on a claim that stopped being true.
 (4) My stated reason for not inserting the some-wrap did not exist: the `occ` handed to `check_seq_literal_constructor` is already a `reassemble_children` of its typed elements. Rewritten in the code doc AND in §4.6 as what it is — a decision, not an obstacle.
 (5) A fourth carrier building `List[T = …]` behind the same stringly-typed base name the new `SeqLiteral` enum exists to remove.

WHAT ELSE MOVED. `kernel-language.md` §4.6 gains the rule and §8.2 loses a bullet: a list/set literal now carries a variant to its elements, so the "three positions do not yet admit a variant" list is two. `wi_jsfhg_variant_type_is_inhabited_test`'s known-gap row is gone (its capability lives in the new file); `typer_capability_matrix_test`'s three `SilentlyAccepted` cells and `wi_q0093`'s pinned report row are now positives — that Q0093 row had written down that this is exactly how it should end, and it ended that way. `LITERAL_GAP` is re-keyed to WI-20260828-5NSZY: 7JDWY was its blocker and is closed, but the cells are still red for a narrower reason (the hint is confined to element types that MENTION AN ENTITY), recorded at the gate and in 5NSZY's own file.

VERIFICATION. Full workspace 6574 passed / 0 failed. scaland `sbt test` is 539/2/537 — the two `BootstrapTest` failures are PRE-EXISTING, verified identical on a clean HEAD worktree, and no scaland or stdlib input changed.

