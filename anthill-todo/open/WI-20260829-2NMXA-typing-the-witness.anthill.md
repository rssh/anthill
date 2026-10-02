## Attributes

- id: WI-20260829-2NMXA-typing-the-witness
- created: 2026-08-29T17:42:20Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T17:42:20Z

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

