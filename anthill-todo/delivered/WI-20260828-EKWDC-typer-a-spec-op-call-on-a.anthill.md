## Attributes

- id: WI-20260828-EKWDC-typer-a-spec-op-call-on-a
- created: 2026-08-28T16:14:52Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T17:34:11Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: a SPEC-OP call on a value whose carrier declares its own `requires` cannot discharge that requirement when the receiver is an INLINE construction. MEASURED: `Stream.splitFirst(mapped(xs, inc))` with `xs: List[T = Int64]` is refused with `Stream.splitFirst.dispatch: no impl matches — unresolved: Iterable[C = MappedStream.Source, Element = MappedStream.Src, E = MappedStream.ES]`. Read the unresolved requirement: it is spelled in `MappedStream`'s OWN DECLARED PARAMETERS (`MappedStream.Source` etc.), not instantiated at the receiver — even though the receiver's type is now fully ground (`MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}]`, verified by wi_bh1jz_carrier_arg_projection_test::the_carrier_param_binds_to_the_receiver_not_to_the_provisions_self_reference). So the defect is that the carrier's `requires` clause is checked in its declaration scope rather than under the receiver's own type arguments; instantiating it would ask whether `List[T = Int64]` provides Iterable, which it does. DISTINCT FROM WI-20260828-BH1JZ, which is DELIVERED and fixed the projection that grounds the construction: this failure is what BH1JZ's fix REVEALED underneath, and it is a different mechanism (requirement forwarding / instantiation at a spec-op call, cf. the WI-821 family) rather than a further gap in carrier-argument projection. NOT the same as the working path: `FiniteCollection.collect(mapped(xs, inc))` is CLEAN, because the witness supplies that op and its own `requires` is discharged against the ground carrier application; `Stream.splitFirst` instead reaches MappedStream's own declared `requires`. ACCEPTANCE: the program above loads clean; the six rows of wi_bh1jz_carrier_arg_projection_test stay green, INCLUDING an_infinite_source_is_still_refused.

## Changes

### 2026-08-28T17:34:07Z — feedback — user

DELIVERED — `Stream.splitFirst(mapped(xs, inc))` type-checks AND RUNS, and the ticket's own diagnosis was right about the mechanism.

WHAT IT WAS, confirmed rather than re-derived: a carrier's `requires` was resolved in its DECLARATION scope. A provision's sub-goals are instantiated through the substitution that matching the PROVISION HEAD against the dispatch goal produces, and a head names only the parameters the target spec is about. `MappedStream provides Stream[T = T, E = {ES, EF}]` writes neither `Source` nor `Src`, so `requires Iterable[C = Source, Element = Src, E = ES]` reached the resolver with those parameters standing as bare references into MappedStream's own declaration. Nothing provides `Iterable[C = MappedStream.Source]`, and the refusal named exactly that.

THE INFORMATION EXISTED AND COULD NOT TRAVEL. The receiver's type is fully ground (BH1JZ delivered that) — measured at the dispatch as `MappedStream[T = Int64, Source = List[T = Int64], Src = Int64, ES = {}, EF = {}]`. `SortGoal.carrier` was an `Option<Symbol>`: the sort and nothing else. It is now an `Option<GoalCarrier>` — the sort AND the type arguments the receiver's own type wrote — read once in `receiver_carrier`, where the receiver argument is in hand, and filled into the impl-param substitution by `carrier_arg_impl_subst`.

IN THE GOAL, NOT BESIDE IT, for the reason WI-350 put the sort there: the goal is the `resolve_cache` key. Two receivers of one carrier at different arguments now resolve their sub-goals differently, so a shared memo entry would answer one with the other's dictionary.

ADDITIVE: only a parameter the head match left unbound is filled, so no dispatch whose head already pinned one can move. The `Elemental` control row measures that from the other side and passes both ways.

THE SAME RULE ALREADY EXISTED ONE ROUTE OVER, which is why this is spelled as it is rather than invented: `match_candidate_against_goal`'s arm (2.5) threads a per-call instance's type arguments into `impl_subst` "keyed by the impl sort's OWN type-params so the requires-chain resolves at the concrete element" — for a self-representing carrier reached through a spec-view BINDING (`Set provides PartialEq[T = Set]` against a `Set[T = Int64]`). This is that rule on the route where the carrier is not a binding at all but `SortGoal.carrier` (WI-350). Both now read the arguments through the same `parametric_value_parts` and join by the same short name.

THE POPULATION IS TWO, censused rather than taken from the ticket, which named one: 28 `requires` clauses across stdlib + examples, of which `MappedStream` and `FilteredStream` are the only carriers whose `requires` names a parameter their `provides` head does not. Both are DRIVEN — the mapped stream to head 2 (`[1,2,3]` mapped by `+1`; an unmapped split gives 1) and the filtered one to head 3.

WHAT THE FIXTURE COST, recorded because the failure mode reads as evidence: THREE hand-written carriers passed BOTH with and without the change before I found a shape that discriminates. A provision writing only CONCRETE arguments (`provides Stream[T = Int64]`) binds no spec parameter from the carrier, so the dispatch goal stays EMPTY, resolves `NoCandidates` — the permissive fall-through — and never reaches a provision's sub-goals at all; the carrier's `requires` was checked in none of them, before or after. `Pairer` carries a second parameter (`Out`) solely to make the goal non-empty; `Src` is then the parameter the head does not name.

CONTROLS, per row, measured by mutating `carrier_arg_impl_subst` to return early:
  * the stdlib row FAILS — `expected Int64, got ?_` at both `match`es; written without the `match` in the way, the dispatch's own message is the ticket's.
  * `Pairer` over `Heavy` FAILS.
  * `Pairer` over `Light` is refused EITHER WAY — but backed out with `Tagger[T = wiekwdc.fix.Pairer.Src]`, the message IDENTICAL to the one the `Heavy` program got. One carrier, two receivers, one indistinguishable diagnostic. So the row asserts on the TEXT (`Tagger[T = wiekwdc.fix.Light]`): "an error was reported" is true both ways and would stay true if the requirement were DROPPED rather than instantiated.
  * `Elemental` passes either way BY DESIGN — a head that DOES name the parameter its `requires` constrains.

WHAT /code-review CAUGHT, all four acted on:
  * THE MEMO GATE WAS NO LONGER COMPLETE. `cacheable` asked only whether `goal.bindings` were ground — sound while `carrier` was a `Symbol` (ground by construction) and not once it carries `TermId`s off an inferred type. The carrier's arguments are now held to the same test.
  * THE ARGUMENTS WERE RESOLVED AGAINST AN OLDER σ than the bindings beside them: captured in `receiver_carrier`, used ~250 lines and one `bind_spec_params_from_carrier` later. They are now walked through σ in `sort_goal_from_subst`, at the moment the bindings are. Not a wrong dictionary — `dispatch_values_match` refuses a variable against a concrete candidate — but a resolvable goal turned into a refusal, which is this ticket's defect one substitution later.
  * A `debug_assert!(false)` ON A LEGAL SHAPE. The `Value::Node` arm was documented as a safe drop and coded as a dev-build panic; its population is every named argument of a receiver's type, and `witness_sort_goal` feeds it types read back off runtime values. It drops, and says so, and says why its sibling in `sort_goal_from_subst` may assert where it may not.
  * "HOT PATH" — MEASURED, AND THE FINDING'S PREMISE IS WRONG: 4 calls per full stdlib load. `receiver_carrier` reaches the walk only from its `Concrete` arm, and a self-receiver spec op on a statically concrete carrier is the rare shape. Timed paired, both arms alternating in ONE process (min of 9, warmup dropped): the distributions overlap and the arm that BUILDS the arguments had the lower minimum. The walk moved to `parametric_value_parts` anyway, on the one-owner argument.

NOT COVERED, stated at the site rather than ticketed: a goal reached through a provider CHAIN (`Relation provides LogicalStream provides Stream`) resolves to an `impl_sort` a hop from the receiver's sort, whose parameters the receiver's arguments do not name; filling them would need the composition `transitive_provision_view` performs. The census found no carrier in stdlib or examples in that position, so there is nothing to drive.

ALSO: `wi590_conditional_finiteness_test`'s header documented BOTH inline-construction gaps as open and attributed them to one guessed mechanism ("the construction's own sort params are grounded by nothing"); it now records that each was its own and both are closed. `docs/kernel-language.md` gains the rule beside its existing "both are discharged by resolving the spec at the goal's bindings" — the sentence the implementation did not honour.

Tests: `wi_ekwdc_carrier_requires_instantiation_test` — 4 rows, back-outs stated per row. rustland/scripts/test.sh green — 30 binaries, 36 result lines, 5979 passed, 0 failures (5975 before + 4 new). scaland `sbt test` green — 544 passed, 0 failures. All six `wi_bh1jz_carrier_arg_projection_test` rows green, including `an_infinite_source_is_still_refused`.

