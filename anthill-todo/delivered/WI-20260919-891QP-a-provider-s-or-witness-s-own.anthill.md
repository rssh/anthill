## Attributes

- id: WI-20260919-891QP-a-provider-s-or-witness-s-own
- created: 2026-09-19T13:25:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-22T14:45:23Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260919-N31XX-proposal-065-step-3-the-load

- tags: typing

## Description

A PROVIDER'S OR WITNESS'S OWN TYPE PARAMETERS ARE UNKNOWN TO A MEMBER ENTERED THROUGH A REQUIREMENT SLOT -- row (C) of WI-20260918-R541X, split out because it needs a design decision, not a local fix.

      sort TypeTermB { sort T = ?  operation valueOfB() -> Type }
      sort Box { sort V = ?  entity box(v: V)  provides TypeTermB[T = Box[V = V]]  operation valueOfB() -> Type = Box[V = V] }
      sort CrateTT { sort E = ?  provides TypeTermB[T = Crate[W = E]]  operation valueOfB() -> Type = Crate[W = E] }
      operation tagOfB[P](x: P) -> Type requires TypeTermB[T = P] = TypeTermB.valueOfB()
      tagOfB(box(boom("x")))    -- wanted Box(V: Boom)
      tagOfB(crate(boom("x")))  -- wanted Crate(W: Boom)   (the DESC_INSTANCES witness idiom)

STATUS AFTER R541X: no longer a silent wrong answer (was `Box(V: V)` / `Crate(W: E)`). Both are the LOCATED fault `EvalError::UnboundTypeParam` naming `Box.V` / `CrateTT.E`, pinned by `wi_r541x_body_read_of_type_param_test::a_providers_own_param_is_a_located_fault_not_a_wrong_answer` and `..._a_witnesss_own_...`. Those rows turn red on purpose when this lands.

WHAT IS ALREADY THERE: since R541X (A), the slot call's own channel carries the SPEC's parameter grounded (`TypeTermB.T := Box(V: Boom)`). SELECTION is argument-precise (docs/design/requirement-channel.md sec 2.1). What is missing is the selected member's FRAME learning its own sort's parameters: a `Dictionary` is `(impl, subs)` and carries no type bindings (eval/dictionary.rs).

TWO DIRECTIONS, TO BE DECIDED IN A DESIGN NOTE FIRST.
 (i) At load, compile the provision head into PROJECTION PATHS (`V := T.V`, `E := T.W`). At the spec -> provider dispatch, fill the provider member's channel from the spec-param channel values. The staging invariant holds (run time performs no typing operations). This is the tool requirement-channel.md already names for the bridge's remaining `unify_types`.
 (ii) Back a type-parameter read in VALUE position by the `TypeTermB[T = E]` sub-dictionary: dictionary passing all the way, which an ERASING backend needs regardless. It needs a way to BUILD a `Type` from computed `Type` values, and none exists: `Box[V = TypeTerm.valueOf[T = V]()]` is a syntax error, and no reflect operation returns `Type`.

ACCEPTANCE: both fixtures DRIVEN to `Box(V: Boom)` / `Crate(W: Boom)`, through one and two generic levels. The two R541X (C) rows are flipped to positive, each stating which back-out turns it red. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-19T14:54:42Z — feedback — user

DIRECTION DECIDED (user, 2026-09-19): proposal 065 (docs/proposals/065-type-value-requirement.md), neither (i) nor (ii) as written. A rigid read as a value requires 'requires TypeValue[T = B]' in scope; TypeValue (anthill.reflect, member type_value, 055 §8's spelling) is DERIVED for every sort, CONDITIONAL for a parametric one. This ticket closes through the INSTANCE context: Box's derived 'provides TypeValue[T = Box[V = V]] requires TypeValue[T = V]' serves Box.V, filled by the dictionary builder from Box[V = Boom]. Projection paths are not needed for value reads (still the tool for the bridge's unify_types). Now step 4 of 065's order of work: it waits on the census, conditional derivation (with CKD4J) and the load rule + lowering. The fixture here uses TypeTermB; under 065 the provider's member needs no hand-written clause once derivation lands.

### 2026-09-22T14:45:11Z — feedback — user

CLOSED BY WI-20260919-N31XX WITH NO SEPARATE WORK (2026-09-22, on the user's acceptance of N31XX's five changed verdicts). Proposal 065 §4 predicted this and §7 step 4 now records it.

WHAT THIS TICKET ASKED FOR: a member entered through a requirement slot could not read its PROVIDER'S or WITNESS'S own type parameters. 'Box provides TypeTermB[T = Box[V = V]]' with 'valueOfB() -> Type = Box[V = V]' reading Box's own V; likewise CrateTT's E through the DESC_INSTANCES witness idiom. R541X had already turned the silent wrong answers (Box(V: V) / Crate(W: E)) into the located fault EvalError::UnboundTypeParam.

WHY IT NEEDED NO FIX OF ITS OWN. This ticket's framing was that a Dictionary is (impl, subs) and carries no type BINDINGS, so the selected member's frame could never learn its own sort's parameters -- and it asked for a design decision about giving the dictionary those bindings. N31XX's lowering dissolved the question instead of answering it: once a value read of a rigid IS a dispatch through 'requires TypeValue[T = V]', the answer no longer NEEDS a binding, because the evidence that selected the provision IS the type. The dictionary still carries no type bindings. Nothing was added to it.

MEASURED, not predicted: wi_r541x_body_read_of_type_param_test's a_providers_own_param_answers_through_its_instance now answers Box(V: Boom) and a_witnesss_own_param_answers_through_its_instance answers Crate(W: Boom), both where they asserted UnboundTypeParam. Both rows carry their back-out at the site -- restore lower_rigid_read_to_slot's sort-half gate ('slot < chain.sort_len()' returns None) and both return to the fault this ticket described. Full workspace green at close: Rust 7287/0, scaland 614 total/0.

ONE THING THIS DOES NOT CLOSE, recorded so it is not mistaken for dead code: R541X's (D) run-time fault is still LIVE and these two rows are what drive it in a KB built WITHOUT the typer, over which no load rule has passed. It is a backstop now, not a diagnostic an author meets. kernel-language.md says so at the paragraph.

WI-20260919-H20YY, which depended on this, is unblocked.

