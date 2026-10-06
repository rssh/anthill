## Attributes

- id: WI-20260829-2NMXA-typing-the-witness
- created: 2026-08-29T17:42:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-06T18:09:54Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPING: the WITNESS admissibility leg cannot reach a DENOTED actual, because a `SortGoal`'s bindings are `TermId`s and a denoted binding has none. Split out of WI-20260829-N01PY, where the leg was delivered for the two term-carried arms and this one measured and left.

MEASURED, a drivable pair differing ONLY in the effect row:

  operation total(c: FiniteCollection) -> Int64 effects c.E = FiniteCollection.size(c)

  f(m: MappedStream[Source = List[T = Int64], …, EF = {}])           LOADS
  f(k: Cell[V = Int64],
    m: MappedStream[Source = List[T = Int64], …, EF = {Modify[k]}])  REFUSED --
      "expected FiniteCollection, got MappedStream[… EF = {Modify[T = k], }]"

WHY THE TWO DIVERGE. `types_compatible` routes to `types_compatible_view_structural`
whenever a side is not a hash-consed term, and a DENOTED effect row is such a side. That
function's `(parameterized, sort_ref)` arm carries the contract "mirror the term dispatch
so provider admissibility stays carrier-symmetric" (WI-405 FACET A / WI-466) — and with
N01PY's witness leg on the term side only, it no longer does.

WHY IT IS NOT A ONE-LINE ADDITION, measured rather than assumed.
`witness_provides_admissibly` asks its question by building a `SortGoal`, whose
`bindings: SmallVec<[(Symbol, TermId); 2]>` cannot hold a `Value`; a denoted binding is
exactly what has no `TermId` (`unwrap_spec_view_value`'s own doc says so, and DROPS such
bindings). Wiring the leg into that arm and reading `walk_view`'s result was TRIED: the
actual comes back a `Value::Node`, the branch never fires, and the verdict does not move
— so it was removed rather than shipped as a path nothing can drive. Substituting a bare
`Ref(<base>)` is NOT the repair: it asks about a different type (the carrier with its
arguments dropped) and could answer for a witness the value does not match.

ALSO MEASURED, and it is what makes this hard to find rather than urgent: instrumented to
print every refusal of that arm, it fires ZERO times across `wi_tests`, `eval_tests`,
`guardians_test`, `builtin_tests`, `resolve_tests` and `algebra_tests`. The corpus has no
such comparison at all, so only a written fixture reaches it. That is a LOWER BOUND on
reachability, not a proof that user code cannot.

FIX DIRECTION: give `SortGoal` a carrier-agnostic binding (the WI-342 `TermView` /
`Value` treatment the subtype and unify relations already had), or a
`Value`-carrying sibling entry point for this one question. Whichever is chosen, it is a
change to the resolver's goal representation and wants its own measurement — every
`SortGoal` producer and every `goals_equal` / `resolve_cache` key reads that field.

CELLS THAT TRACK IT: `n01py_witness_provision_subtype_test::a_denoted_effect_row_is_a_known_gap`
— the refusal AND its ground-row control, which is what says this is a gap and not the
design. The refusal row FAILS when the gap closes and tells its fixer to flip it. The site
is commented at the arm in `types_compatible_view_structural`.

## Changes

### 2026-10-02T16:26:59Z — feedback — user

ADDENDUM (user, 2026-10-02; from WI-20260929-0RP29's ninth fix pass) — THE DECLARATION RULE'S READING OF A PROVISION'S BINDINGS IS THIS SAME `TermId` BOUNDARY, and is moved here rather than given a ticket of its own. A provision's bindings (σ) are what the `provides` fact stores: `ProvidesRow.spec_view: TermId` and its named bindings `(Symbol, TermId)` (typing/provides_index.rs), filtered to the spec's parameters by `spec_param_sigma` (typing/provision.rs), which answers `Vec<(Symbol, TermId)>`. They are the same bindings a `SortGoal` is matched against, so they are terms for the reason this ticket states. Every reader of σ is therefore typed by the stored term — in typing/signature.rs `check_member_signature`, `ProvisionMembers { sigma }` and `ProvisionMembers::new`, `member_narrower_than_spec`, `carrier_param_receiver_of` (it answers the receiver's binding as a `TermId`), `ProjectionReader::new(…, sigma, witness_view: Option<TermId>)` and `ProjectionReader::at_receiver(…, b: TermId, …)`, `Narrower::Circular { binding: TermId }`, `self_references_at_own_parameters(b: TermId)`, `this_instance_binding_at(binding: TermId)`, `member_params_are_a_permutation`, `render_op_signature`, `instance_binding_type_ok`; in typing/projection.rs `member_binding`, `provision_lends_binding(written: TermId)` and `lent_member(written: TermId)`; in typing/carrier.rs `witness_instantiation(view_bindings)`; in typing/provision.rs `provision_supplier` and `instance_fact_op_in_bindings`. What the rule COMPARES is carrier-neutral already (user, during that pass: a rebuilt type is not forced onto the term carrier to fit a `TermId`-typed consumer — the consumer is made carrier-neutral): the provision template is `Vec<(Symbol, Value)>`, applied by `sigma_subst_type_values`, and a binding's expansion rides whatever carrier its form takes. So today each read wraps the stored term (`Value::term(b)`), and a spec view the typer rebuilds is lowered to a term where it meets this boundary (`lower_spec_view`, typing/result.rs; `eliminate_spec_view`, typing/projection.rs — both already marked for this ticket). WHEN `SortGoal` and the stored spec view carry value bindings: σ is `&[(Symbol, Value)]` at its source (`spec_param_sigma`), the readers above take it as such, the per-read wraps and the two lowerings go, and the doc comment on `ProvisionMembers::sigma` ("STORED DATA, not the result of a substitution…") is rewritten to say what is stored then. Converting the rule's API alone, with the storage unchanged, was offered in that pass and deliberately not done: it changes no verdict and would be redone here. ACCEPTANCE, added to this ticket's: no reader of a provision's bindings takes a `TermId`, and `spec_param_sigma` answers `Value`s; WI-20260929-0RP29's rows (wi_0rp29_member_rule_test, wi_0rp29_call_binding_test) stay green unchanged — they pin verdicts, which this does not move.

### 2026-10-06T07:04:50Z — feedback — claude

WI-20261005-KSSA4 changed this ticket's pair. `total(c: FiniteCollection)` takes neither value now — a provider's value is not a value of a spec over a parameter — so the pair is written `operation total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E = FiniteCollection.size(c)`. MEASURED on that tree: the ground-row half loads, and the denoted half (`TransformEffects = {Modify[k]}`) is refused "expected a type for 'E', got unconstrained" at `total.type_arg` — the requirement's row is read off the provision at the argument's sort, and a denoted binding does not come through. The row is `n01py_witness_provision_subtype_test::a_denoted_effect_row_is_a_known_gap`, still a known gap. The leg this ticket names, `witness_provides_admissibly`, answers only where a spec stands for its providers now (a rule variable's bound), so a denoted binding is to be carried through the requirement's supply and not through that leg.

### 2026-10-06T09:56:50Z — feedback — claude

THE CALL-SITE WORKAROUND FOR THIS GAP IS GONE (WI-20261006-XQGEW, 2026-10-06). `n01py_witness_provision_subtype_test::a_denoted_effect_row_is_a_known_gap` gave `total[E = {Modify[k]}](m)` as the spelling that fixes the member-spelled program — `total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E` over a `MappedStream[… TransformEffects = {Modify[k]}]`, whose provision binds the row and is not read. It did load: the bracket key `E` bound the member's parameter by its bare name (MEASURED with the member's name interned as the parent commit had it). A call's bracket no longer names a member's parameter — the same key landed on it where the enclosing sort declares an `E` of its own — so that call is now refused, "unknown type-param 'E' — `FiniteCollection.E` is a member's parameter, which no bracket names", and the row pins both refusals. Until the denoted row is read, the member spelling of that program has no repair at the call; the spelling that can be written is the parameter in the bracket (`total[P, R](c: P) -> Int64 effects R requires FiniteCollection[C = P, E = R]`, then `total[R = {Modify[k]}](m)`), which loads (MEASURED; the same row asserts it).

### 2026-10-06T18:09:53Z — feedback — claude

DELIVERED 2026-10-06 (working tree, not yet committed). A GOAL'S AND A PROVISION'S BINDINGS ARE VALUES: `SortGoal::bindings`, `GoalCarrier::args`, what `unwrap_spec_view` / `unwrap_spec_view_value` answer, a `ProvidesRow`'s bindings (decoded when asked) and `spec_param_sigma` are `(Symbol, Value)`, and every reader takes them so — the list in the 2026-10-02 addendum, and `witness_instantiation`, `provision_supplier`, `instance_fact_op_in_bindings`, `member_binding`, `lent_member`, `provision_lends_binding`. Both lowerings are gone (`lower_spec_view` deleted; `eliminate_spec_view` leaves the view on its children's carriers) and `ProvisionMembers::sigma`'s doc says what is stored. Two readers stay in the term world by their callers and assert what is stored rather than narrow it silently: `ground_rigid_projection_if_concrete`, called inside the term walk, and the loader's pre-scan of a lowered clause. A reader that asks only a yes/no of a row reads the stored slice through the view (`ProvidesRow::stored_bindings`), so it takes any carrier and builds nothing. WI-20260929-0RP29's two named files (wi_0rp29_member_rule_test, wi_0rp29_call_binding_test) are green and unchanged. THE TICKET'S PAIR LOADS AND RUNS in all three spellings — `total(c: FiniteCollection.C) … effects FiniteCollection.E`, the bracket clause `total[P, R](c: P) … requires FiniteCollection[C = P, E = R]`, and a spec operation the provider does not override (`m.size()`) — over `TransformEffects = {Modify[k]}`: 410, where each was refused. As the 2026-10-06 note said, the row comes through the requirement's supply: the receiver's arguments are read on the carrier each rides (`parameterized_vid_bindings`) and the provision's binding is instantiated by a rewrite whose replacements may be occurrences (`rewrite_type_leaves`). THE WITNESS LEG IS ON THE VIEW ARM TOO (`types_compatible_view_structural`, `(parameterized, sort_ref)`), where it answers what it answers on the term arm: under `-Permission[Cap]` a `Permission[Buf[T = Int64, N = 3]]` is now refused as its `N = Bool` twin was, and a column bounded `?x: Cap.C` is cited with a `Buf[T = Int64, N = 3]` as with the twin. VERDICTS THAT MOVED BESIDE THE PAIR, each with a row in wi_2nmxa_denoted_provision_binding_test: a spec that receives on itself reads its default's row at a receiver that names a cell (a pure-declared operation that wrote the cell twice loaded and ran); the projection spelling `effects s.E` is grounded there; a constructor's field typed at a spec takes a provider's row that names a cell (was "undeclared effect: c.EC"); a member returning its rest at a row naming its own parameter is refused as its ground twin always was — the subtype relation's reading of the provider's view dropped an argument that was no term (this is why wi_0rp29_nested…'s re-key fixture was rewritten: its member was such a one); and `Map[K = Vec[T = Float, N = 3], V = Int64]` is refused for want of a lawful `Eq`, as `N = Bool` was (`check_use_site_requires_eq` kept term bindings only). `n01py…::a_denoted_effect_row_is_a_known_gap` is flipped and renamed `a_row_that_names_a_cell_is_read_like_a_ground_one`. /code-review ran (15 findings): fourteen taken, among them one σ walker where there were two (`sigma_subst_type` over `rewrite_type_leaves`, with a term path that allocates nothing), the child reads through the one widening the typer has (`view_named_children` / `view_pos_children`), per-carrier arms folded (`clause_named_type_param`, `entry_type_param_bindings`, `op_requires_entry_carrier_map`, `spec_binding_value`, `spec_mentions_key`, the carried type as a goal's binding), the dispatch memo no longer given goals whose identity cannot recur, and the two groundness gates made one walk that differs in a value's closedness alone; one answered by measurement and left (a `require[…]` bracket's arguments now compose into the chain it holds, where they were dropped; what was measured is at `held_view_subst_map`); and two of the smaller repairs withdrawn after measurement (a bare label wrapped on another carrier, and an undetermined receiver argument kept from overriding a projection — no program reaches either). Load time against the parent commit: 81.5 ms against 81.4 ms median (release, 4 × 60 loads alternating), where the first cut cost 1.3 %. THE LEDGER — 13 back-outs that fail rows, and 11 parts no row drives, each with its reason — is the test file's module doc; unit rows drive two of the helpers (`wi_2nmxa_value_holding_type_reader_tests`). NOT DRIVEN BY ANY PROGRAM FOUND, and left as the carrier-neutral reading: `sigma_class_terminal` following a link that is no term (no σ a test builds has one there), a `require[…]` bracket's arguments composed into the chain it holds (the demand says no type parameter), an unwritten slot of an application that holds a value, a default's row against a goal's argument, a route's pin that holds a value. FOUND WHILE PROBING, THE SAME ON THE PARENT COMMIT, NOT FIXED AND NOT FILED (to be asked): the argument check and the type-parameter join skip a type that names a cell of the enclosing operation (`consume(s: Stream[T = Int64, E = {}])` takes a `Cnt[T = Int64, EC = {Modify[k]}]`; `second[A](x: A, y: A)` over `Box[BE = {}]` and `Box[BE = {Modify[k]}]` loads declared pure); a row-shaped provision (`provides Sp[E = {BE}]`) on a spec that receives on itself loses its effects even at ground rows; a row variable is not bound from a label that holds a value (`bind_row_tail`), so the transform's row is written at `map` in the rows here; an operation-level `requires` clause holding a literal is "unresolved name '3'"; the run-time bound check of a carrier with a parameter no field determines is suspended, so the cited-column row asserts the load verdict only; and `require[FiniteCollection[C = List[T = Int64]]]` over a head variable typed `List[T = String]` loads. GATE: rustland 8694 / 0 / 14 (full `scripts/test.sh`), scaland 600 (`sbt testFull`).

