## Attributes

- id: WI-20260918-R541X-a-body-read-of-a-type
- created: 2026-09-18T12:52:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-19T13:25:44Z

- acceptance: cargo-test

- tags: typing

## Description

A BODY READ OF A TYPE PARAMETER DANGLES SILENTLY -- a run-time `Type` value comes back naming a type PARAMETER (`T`, `Box(V: V)`, `Crate(W: E)`, `Box(V: !P)`) where the program asked for the type it stands for. Four shapes, one class. WI-708 closed it for an operation's own bracket parameter, `collect_closed_type_args` for the enclosing generic one level up, WI-20260911-RS2G4 for a receiver bracket -- these are the rows none of them reach. It is the TYPE-ARGUMENT twin of WI-1093 (a pinned implementation entered with an EMPTY requirements channel).

WHY NOW. WI-20260911-3MV2C's direction (user, 2026-09-18) is a tag supplied by a typeclass in a requirement slot -- `TypeTerm[T]` with a nullary `valueOf() -> Type`, and `raise(error: T) ... requires ErrorTag[T]` whose DEFAULT is the type term. That default is literally shape (A) below, so this goes first. NOT a dependency edge: 3MV2C's own first step (the view-shaped boundary) consumes nothing from here.

MEASURED 2026-09-18 on 19f73ff1 with `anthill query` (no core commit since the binary was built). Every fixture LOADS CLEAN and answers SILENTLY.

(A) A SORT-PARAMETER ENTRY WHOSE WALK IS THE ENCLOSING OPERATION'S OWN RIGID IS SKIPPED.
      sort TypeTerm { sort T = ?  operation valueOf() -> Type = T }      -- the spec's DEFAULT body reads the spec's own T
      sort Boom { entity boom(why: String)  provides TypeTerm[T = Boom] }
      operation tagOf[P](x: P) -> Type requires TypeTerm[T = P] = TypeTerm.valueOf()
      tagOf(boom("x"))  answers `T`     -- wanted `Boom`. A NOMINAL carrier: this is not about type arguments.
    The same through two generic levels (`outer[Q](y: Q) requires TypeTerm[T = Q] = tagOf(y)`). And with NO DICTIONARY ANYWHERE: `sort Err2 { sort T = ?  operation tagOf(error: T) -> Type = T }`, `operation g[P](x: P) -> Type = Err2.tagOf(x)`, `g("s")` answers `T`.
    CONTROLS, correct today: the monomorphic site `Err2.tagOf(box("s"))` -> `Box(V: String)`; the UNWITNESSED constructor `Err2.tagOf(noneInt())` -> `Option(T: Int64)`, which no value walk could recover; the op-parameter twin `tagOp[T](x: T) -> Type = T` called `tagOp(x)` inside `g[P]` -> `String` (WI-708).
    CAUSE, FROM READING AND NOT INSTRUMENTED. `check_apply_iter`'s `resolved_type_args` write (kb/typing.rs, the WI-20260911-RS2G4 block) runs two loops. The op-parameter loop applies `op_own_param_ref_rewrite`: a whole entry that IS an enclosing skolem becomes `Ref(<op-scoped>)`, which `collect_closed_type_args` then grounds. The sort-parameter loop does not, and `continue`s on ANY `Term::Var` walk -- deliberately, so that an occupied key cannot disable `enter_operation`'s same-sort inheritance for the WI-424 body skolem. The enclosing OPERATION's own skolem is a different rigid and a distinguishable one (it is in `enclosing_refs`). Whether rewriting exactly those leaves the inheritance rule intact is the thing to measure FIRST.

(B) A RIGID NESTED INSIDE AN ENTRY, on either loop. `operation g[P](x: P) -> Type = tagOp(box(x))`, `g("s")` answers `Box(V: !P)`; the sort-parameter form `Err2.tagOf(box(x))` answers the same. The rewrite is WHOLE-ENTRY ONLY and says why: a skolem nested in an `effects_rows(...)` spine is a row TAIL, and a `Ref` there silently closes a row that must stay open (proposal 027.4 records the measurement). So the deep form must be KIND-AWARE, not merely deep. CONTROL: the same type written as an EXPRESSION grounds -- `operation tagExpr[P](x: P) -> Type = Box[V = P]`, `tagExpr("s")` -> `Box(V: String)`.

(C) A PROVIDER'S OR A WITNESS'S OWN PARAMETERS, ON A MEMBER ENTERED THROUGH A REQUIREMENT SLOT.
      sort Box { sort V = ?  entity box(v: V)  provides TypeTerm[T = Box[V = V]]  operation valueOf() -> Type = Box[V = V] }
      tagOf(box(boom("x")))    answers `Box(V: V)`
      sort CrateTT { sort E = ?  provides TypeTerm[T = Crate[W = E]]  operation valueOf() -> Type = Crate[W = E] }
      tagOf(crate(boom("x")))  answers `Crate(W: E)`
    The second is the `DESC_INSTANCES` witness idiom. A `Dictionary` is `(impl, subs)` and carries no type bindings (eval/dictionary.rs), and nothing at the slot dispatch derives `E` from the spec's `T`. SELECTION is argument-precise -- the requirement channel reads the carried type whole and the arguments flow to the sub-fetches (docs/design/requirement-channel.md sec 2.1) -- it is the selected member's FRAME that never learns them. CONTROL, measured: the direct receiver-bracket call `Box[V = Boom].valueOf()` -> `Box(V: Boom)` (WI-20260911-RS2G4).
    TWO DIRECTIONS, NOT DECIDED HERE. (i) Compile the provision head into PROJECTION PATHS at load (`E := T.W`) -- the tool that design doc already names for the bridge's remaining `unify_types` -- so the staging invariant (run time performs no typing operations) holds. (ii) Back a type-parameter read in VALUE position by `TypeTerm[T = E]`'s sub-dictionary where the frame channel has no entry: dictionary passing all the way, which an ERASING backend needs regardless. It needs a way to BUILD a `Type` from computed `Type` values and there is none today -- `Box[V = TypeTerm.valueOf[T = V]()]` is a SYNTAX error (a type-argument position takes type expressions) and no reflect operation returns `Type`.

(D) THE SILENT HALF, common to all three. `Expr::TypeValue`'s bare-head arm (eval/eval.rs) asks the frame channel and otherwise allocates `Ref(head)` -- for a genuine sort AND for a type parameter nothing bound. A parameter with no binding is not a type. `genuine_concrete_sort` is already the test `payload_sort_of` uses for the same question. Loud here turns every row above from a wrong answer into a LOCATED fault, and that is also what makes (A)-(C) safe to land one at a time.

ORDER. (D) and (A) first: small, local, and (A) alone is what a NOMINAL `ErrorTag` default needs. Then (B). (C) last and with its own design note -- it is the only dictionary-specific part.

ALREADY SOLVED NEARBY, so this does not start from zero. WI-20260909-S8CBV / VVM1R: S4's hand-rolled HEAD-ONLY key made `Box[E = Leaf]` and `Box[E = Other]` compare EQUAL, fixed by delegating to `unify_types` -- the same type-argument blindness, in dictionary attribution. WI-1093: the requirements-channel twin, and its note that a RECEIVER-LESS spec op has no value-directed repair applies verbatim to `valueOf()`. WI-708, WI-20260911-RS2G4 and `collect_closed_type_args`: the three sibling rows of this class.

ACCEPTANCE: every fixture above DRIVEN to the ground `Type` value -- `Boom`, `String`, `Box(V: String)`, `Box(V: Boom)`, `Crate(W: Boom)` -- through one and two generic levels; (D)'s fault asserted on a fixture that still cannot bind; and the controls named AT THEIR SITES as rows that pass either way BY DESIGN (the monomorphic site, the unwitnessed `none`, WI-708's whole-entry op parameter, RS2G4's receiver bracket, the expression form). Each positive row states which back-out turns it red. Full workspace green via rustland/scripts/test.sh.

ADJACENT, NOT THIS TICKET: an UNDECLARED requirement over a rigid is not refused at load (`bad[Q](y: Q) -> Type = tagOf(y)` with no `requires`: one provider in the program and `bad(7)` answers `Boom`; several and it dies `DeferToRequirement: ... not bound`). Recorded as a cross-reference on WI-20260909-M8QWJ; it is the RIGID complement of delivered WI-1102.

## Changes

### 2026-09-19T13:25:39Z — feedback — user

DELIVERED (A), (B), (D); (C) split to WI-20260919-891QP by decision (user, 2026-09-19). (A) two causes, not one: the sort-parameter loop skipped the enclosing operation's rigid (now rewritten like the op loop), AND a receiver-less member called under 'requires TypeTerm[T = P]' had NOTHING pin TypeTerm.T at all -- new binder bind_sort_params_from_sole_enclosing_requirement: exactly one clause over the callee's sort AND the call pins none of that sort's params (the second gate is measured: wi606, FiniteCollection.collect(rest) over a different carrier borrowed the clause's Element/E). /code-review found the sort-level clause half dropped at the channel (the sort's rigid rode out as a bare var); fixed inline by enclosing_sort_param_ref_rewrite, cross-sort callees only so WI-424 same-sort inheritance is untouched. (B) apply_enclosing_param_refs descends by type_head into Parameterized/Arrow/NamedTuple only -- never EffectsRows (row tail), neutral heads, or PolyType. (D) two halves: a bare head that is a type param and misses the channel, and a channel HIT whose value is itself Ref(<param>) the caller could not ground -> EvalError::UnboundTypeParam (bridge disposition Fault). FOUND, NOT FIXED: a receiver-less DEFAULTED spec member is typed as a plain call to the default, so a provider's override is never reached through the slot (Box overriding TypeTerm.valueOf as Option[T = V]: tagOfP(box(..)) still answered the default's Box(V: Boom)); that is why (C)'s fixtures moved to a body-less TypeTermB. Rows + measured back-outs: wi_r541x_body_read_of_type_param_test.

