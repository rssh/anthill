# The readers of the single carrier parameter

Companion to [`../spec-carrier-set.md`](../spec-carrier-set.md). Every call site, in
`rustland/anthill-core/src/`, of the functions that answer "which ONE parameter is the
carrier", and the question each caller uses the answer for. Found with `grep -rnw` on
1a58f1e48, without definitions and comment lines: **114 sites**. Each was classified by
reading the site and its function's doc comment; about 25 of them were read twice
(the derivations, the witness readers, the extra ladders), and the reading agreed.

## Codes

Functions: **scp** `spec_carrier_param` · **or_sole** `spec_carrier_param_or_sole` ·
**sop** `spec_over_parameter` · **shcp** `spec_has_carrier_param` · **wdc**
`witness_dispatch_carrier` · **wdcv** `witness_dispatch_carrier_value` · **pcos**
`provision_carriers_of_spec` · **pa** `provisions_about` · **pdc**
`provision_dispatch_carrier` · **ohscp** `op_has_spec_carrier_param`.

Questions:

| | the question the caller has |
|---|---|
| D | add a provision unless one is written; or check the written ones |
| S | select the provision a goal or call asks for; a goal's key or column |
| V | which argument of an operation fixes the substituted sort |
| W | is this provision a witness or the provider's own; its supply route |
| O | overlap: coherence groups, default rows, specificity |
| M | member-signature check against the spec operation |
| P | a projection (`c.T`) or the substitution a provision's bindings give |
| K | a refusal at load that the parameter decides |
| X | text of a diagnostic only |
| SC | the spec's CLASS (does it have a dictionary), not which parameter |

## Counts

| question | sites | | function | sites |
|---|---|---|---|---|
| S | 39 | | or_sole | 39 |
| V | 17 | | scp | 24 |
| P | 12 | | sop | 14 |
| K | 10 | | wdc | 10 |
| SC | 9 | | ohscp | 8 |
| X | 6 | | shcp | 5 |
| W | 5 | | pa | 5 |
| O | 5 | | pcos | 4 |
| M | 4 | | wdcv | 3 |
| D | 4 | | pdc | 2 |
| other | 3 | | | |

Not counted above — the callers of two WRAPPERS:
- `provision_carrier_sort` (provision.rs:38, over `provision_carrier_binding`, scp):
  type_receiver.rs:465 `witness_route_only` (W), dot_rule.rs:311 and :887 (V).
- `clause_carrier_param` (carrier.rs:2594: scp, else the FIRST parameter, no class gate):
  provision.rs:2226 `instance_at_goal_carrier` (P), dict.rs:3538 `dep_completed_at_carrier`
  (S), projection.rs:4122 `instance_member_carrier` (P), carrier.rs:1576
  `enclosing_requires_licensing_clause` (V), carrier.rs:2276 and :2487 (P).

## The sites

Each row describes the code in its own words. There, "instance" means the dictionary a
call needs, which [the design](../spec-carrier-set.md) calls a substituted sort.

| file:line | function | calls | Q | what the answer is used for |
|---|---|---|---|---|
| kb/type_value_derive.rs:107 | run | pcos | D | hand-written `TypeValue` refused (`HandWrittenTypeValue`), naming the sort read |
| kb/type_value_derive.rs:167 | run | pcos | D | sorts already providing `TypeValue` are skipped by the derivation |
| kb/sort_domain_derive.rs:66 | run | pcos | D | sorts already providing `SortDomain` are skipped by the derivation |
| kb/eq_derive.rs:1322 | spoken_for | pa | D | sorts an equality provision speaks for; the derivation leaves them alone |
| kb/eq_derive.rs:600 | equality_reaching_no_eq | pa | K | which composite each `PartialEq` provision is at; refused if no `eq` answers it |
| kb/eq_derive.rs:1348 | equality_signatures | pa | K | per-composite equality record; a later load that changes it is refused |
| kb/eq_derive.rs:652 | written_spec_of | pa | X | a derived row traced to the spec its provider wrote, for the refusal |
| kb/load.rs:23438 | EqProviders::of | pa | other | does a sort provide `Eq` (own or a witness at it), for the eq index and proof_verify |
| kb/layer.rs:877 | (test) | pcos | other | `Eq`'s providers, to assert a discarded layer's row is gone |
| kb/load.rs:47999 | try_body_tvar_guard | or_sole | S | in a guard naming several head tvars, which one is the carrier |
| kb/load.rs:48117 | try_body_tvar_guard | or_sole | S | which written binding is the carrier column of the guard's requirement |
| kb/load.rs:48172 | try_body_tvar_guard | sop | K | dictionary spec ⇒ a `HeadMember` use, checked by `check_rule_sort_uses` |
| kb/defaults.rs:730 | dispatch_carrier | pdc | O | where a provision dispatches, to file 058 §3.6 default rows — **done** (CXR5B step 1: `provision_carrier`; the function is deleted) |
| kb/resolve.rs:9794 | builtin_dispatch_carrier | pdc | O | the `dispatch_carrier` builtin behind `default_provider` / `self_provides` — **done** (CXR5B step 1: `provision_carrier_of`, `own_provision_carrier_of`) |
| kb/typing/constructor.rs:1153 | bare_spec_arg_provision_projection | shcp | SC | a field's spec has a dictionary ⇒ skip the projection |
| kb/typing/arg_hints.rs:44 | spec_instance_arg_hint | sop | SC | parameter typed at a dictionary spec ⇒ hint a spec application, to refuse it |
| kb/typing/arg_hints.rs:59 | yields_spec_application | sop | SC | is a written type an application of a spec with a dictionary |
| kb/typing/dict.rs:389 | carrier_is_its_own_sole_provider | or_sole | W | each row's carrier: the carrier provides itself with no witness rival |
| kb/typing/dict.rs:409 | carrier_has_provision_row | or_sole | S | does any provision (own or witness) dispatch at this carrier |
| kb/typing/dict.rs:3920 | scope_contract_covers_dep | or_sole | S | a held `requires` covers a dependency only at its carrier element |
| kb/typing/dict.rs:4125 | defaulted_call_owes_an_instance | ohscp | V | a defaulted member taking a carrier argument owes an instance |
| kb/typing/dict.rs:4541 | sort_carrier_providing_nothing | or_sole | S | the goal's carrier binding, for "provides nothing" |
| kb/typing/dict.rs:4655 | goal_carrier_binding | or_sole | S | which goal binding is the carrier, for the unprovided-provision refusals |
| kb/typing/dict.rs:4849 | unprovided_spec_at_former | or_sole | X | the parameter name in the repair `[{param} = …]` |
| kb/typing/forms.rs:1558 | generalize_at_binding | or_sole | S | where a generalized requirement is keyed to the ∀-bound carrier |
| kb/typing/forms.rs:1601 | generalize_at_binding | or_sole | S | the same, for per-use instances moved back into a type |
| kb/typing/call_class.rs:1410 | tree_application | or_sole | S | the application a resolved instance tree is for — **done** (CXR5B step 3: `SpecApplication::of_bindings`) |
| kb/typing/call_class.rs:1940 | dispatch_to_the_clause | ohscp | V | no carrier argument ⇒ the instance comes from the sort's `requires` |
| kb/typing/slots.rs:990 | seed_provider_receiver | shcp | SC | a receiver-named provider is a carrier, not a dictionary spec |
| kb/typing/slots.rs:991 | seed_provider_receiver | scp | S | bind the callee's carrier to a receiver named as a provider (`A.viaDefault()`) |
| kb/typing/dot_rule.rs:672 | find_spec_op_for_clause_slot | or_sole | V | rule-body dot: does a slot's carrier binding equal the receiver |
| kb/typing/dot_rule.rs:834 | constraining_specs_for_param | or_sole | V | dot on a type param: which `requires` constrain the receiver |
| kb/typing/dot_rule.rs:884 | requires_edge_is_carrier_preserving | scp | V | does a `requires` edge bind the receiver's carrier, so it lends members |
| kb/typing/provider_constraint.rs:98 | type_application_goal | or_sole | S | suspend until the carrier binding is known, then resolve there |
| kb/typing/provider_constraint.rs:199 | provider_requirement_goal_with_provider | or_sole | S | keep the carrier binding, drop variable siblings, check against actual |
| kb/typing/coherence.rs:2265 | is_witness_provision | scp | W | binding at the carrier names another type ⇒ witness (backing obligation) — **done** (CXR5B step 9: not the provider's own, decision 6, and binding another type) |
| kb/typing/coherence.rs:2448 | provider_coherence_groups_with | wdc | O | witness vs self provisions into (spec, carrier) ambiguity groups |
| kb/typing/requires.rs:2021 | param_instance_requires | sop | SC | a parameter typed at a dictionary spec is an instance requirement |
| kb/typing/requires.rs:2067 | lambda_instance_requires | sop | SC | the same, for a lambda binder |
| kb/typing/requires.rs:3351 | provision_is_conversion | or_sole | W | a conversion binds the target's carrier and supplies no operation |
| kb/typing/instances.rs:128 | carrier_own_instance_goal | or_sole | S | the goal's carrier column ⇒ the carrier's own instance |
| kb/typing/instances.rs:803 | receiver_param_index | scp | V | the call's receiver argument (typed at the carrier parameter) |
| kb/typing/instances.rs:1328 | provision_carrier_slot | scp | V | the provider's carrier binding and the target's receiver index |
| kb/typing/instances.rs:1377 | spec_application_where_a_dictionary_is_expected | sop | K | refuse a spec application where a dictionary is expected |
| kb/typing/instances.rs:1704 | call_at_own_instance | scp | S | in a default body, a call at the body's carrier takes the body's instance |
| kb/typing/carrier.rs:445 | provision_binds_param_to_carrier | wdc | V | does this argument position name the carrier, through a witness |
| kb/typing/carrier.rs:464 | provisions_at_carrier | wdc | S | own and witness provisions at a carrier (the `ParameterNamedApart` tie) — now also read by `select_provision_at_carrier` (CXR5B step 2), which chooses among them by the call; the carrier itself is still the single parameter's |
| kb/typing/carrier.rs:541 | witness_provider_for | wdc | P | whose binder the view's variables belong to |
| kb/typing/carrier.rs:3323 | subtype_provider_view | scp | P | drop the composed self-referencing carrier binding of a provider view |
| kb/typing/candidates.rs:483 | bind_carrier_the_witness_says | scp | S | the open carrier to bind from a named witness `[Mk = W2]` — **done** (CXR5B step 2: every open type-var the named provider's provisions write one ground type for) |
| kb/typing/candidates.rs:503 | bind_carrier_the_witness_says | wdcv | S | the carrier value the named witness provides at |
| kb/typing/candidates.rs:786 | candidates_at | or_sole | S | the column that grounds the provider's parameters in candidate matching |
| kb/typing/candidates.rs:2764 | head_answers_at | or_sole | O | the column compared when ranking heads by specificity |
| kb/typing/candidates.rs:2902 | goal_carrier_key | or_sole | O | the goal's key for the 058 §3.6 default lookup — **done** (CXR5B step 1: the goal's substituted sort) |
| kb/typing/subtype.rs:817 | parameterized_compatible_view | scp | P | in a composed view, the carrier is checked against the actual itself |
| kb/typing/subtype.rs:1088 | provision_leaves_param_open | scp | P | a left-out parameter reads as `?`, except the carrier |
| kb/typing/subtype.rs:2571 | witness_provides_admissibly | wdc | S | witness rows at the actual type (spec standing for its providers) |
| kb/typing/subtype.rs:2583 | witness_provides_admissibly | scp | S | the slot the actual type goes in, for each witness's goal |
| kb/typing/subtype.rs:2753 | bare_provider_binding_precise | scp | P | the composed carrier binding read as `Ref(carrier)` |
| kb/typing/apply.rs:708 | check_apply_call | scp | V | which argument is at the carrier; a spec-typed value there is refused |
| kb/typing/apply.rs:709 | check_apply_call | shcp | SC | the gate: the operation's sort is a dictionary spec |
| kb/typing/apply.rs:4172 | check_apply_call | scp | S | defaulted op at a type parameter: scp first, then every parameter in turn |
| kb/typing/apply.rs:5573 | check_apply_call | scp | S | the carrier at which the reached provider is chosen |
| kb/typing/apply.rs:7696 | judged_at_the_call | ohscp | V | a rule-body call with no carrier argument is judged at the call |
| kb/typing/apply.rs:8002 | held_instance_reads_carrierless_call | ohscp | V | a carrierless call reads the clause's one held instance |
| kb/typing/projection.rs:2393 | this_instance_member | scp | P | `x.Member` in a spec's own body, x the carrier rigid |
| kb/typing/projection.rs:2433 | call_slot_member | scp | P | `s.K` is the call's unless `K` is the carrier |
| kb/typing/projection.rs:2966 | project_via_provided_spec | scp | P | a left-out member lends a fresh `?`, except the carrier |
| kb/typing/projection.rs:3069 | unowned_member_bindings | or_sole | P | a member naming the carrier and binding the provider is no member |
| kb/typing/projection.rs:3073 | unowned_member_bindings | scp | P | an unbound member that is the carrier lends nothing |
| kb/typing/projection.rs:3311 | goal_at_named_witness | scp | S | the goal binding replaced by the named witness's carrier view |
| kb/typing/projection.rs:3323 | goal_at_named_witness | wdcv | S | the named witness's carrier view at the receiver |
| kb/typing/projection.rs:3345 | witnesses_covering | wdcv | S | witness rows whose carrier view covers a receiver |
| kb/typing/signature.rs:417 | compare_member_signature | sop | X | which "narrower receiver" sentence is pushed |
| kb/typing/signature.rs:1299 | member_narrower_than_spec | sop | M | a receiver typed by the spec itself, compared as the spec's type or not |
| kb/typing/signature.rs:3070 | record_members_that_supply_nothing | wdc | other | seal: the carriers a later provision dispatches to, judged again |
| kb/typing/signature.rs:3161 | member_fits_spec_op | wdc | M | the provisions at the carrier (own or witness) the member is compared at |
| kb/typing/signature.rs:3179 | member_fits_spec_op | or_sole | M | with no provision, σ binds the carrier to the carrier's own application |
| kb/typing/signature.rs:3261 | check_override_refinement | wdc | M | each provision's witness carrier, for the refinement and signature legs |
| kb/typing/dispatch.rs:829 | carrier_the_call_binds | or_sole | S | the carrier a defaulted call's bracket or expected type binds |
| kb/typing/callable.rs:392 | provider_at_a_spec_type_error | sop | X | "B provides Tagger but is not a Tagger", naming the parameter |
| kb/typing/callable.rs:470 | spec_typed_value_at_carrier_error | sop | K | a receiver typed at a dictionary spec is refused |
| kb/typing/relation.rs:2223 | route_requirement_read | or_sole | S | a concrete carrier ⇒ build from provisions, not the caller's scope |
| kb/typing/relation.rs:2271 | route_requirement_read | ohscp | V | no carrier argument ⇒ the instance is the sort's requirement |
| kb/typing/dep_projection.rs:581 | provider_half_carrier | or_sole | S | the caller slot's carrier binding picks whose chain fills the provider half |
| kb/typing/rule_requirements.rs:569 | infer_rule_body_requirements | or_sole | S | a receiver bracket writing a concrete carrier fixes the instance |
| kb/typing/rule_requirements.rs:1248 | composed_from_guards | or_sole | S | the goal key for a dictionary composed from the clause guards |
| kb/typing/rule_requirements.rs:1532 | slot_route | or_sole | S | the slot's carrier binding decides the route |
| kb/typing/rule_requirements.rs:1645 | carried_by_a_named_slot | or_sole | S | is the call carried by a named slot at the same carrier |
| kb/typing/rule_requirements.rs:2175 | check_rule_body_operation_requires | or_sole | K | a carrier sort not providing the spec ⇒ `UnfillableOperationRequirement` |
| kb/typing/rule_requirements.rs:2896 | check_one_spec_op_requirement | ohscp | V | only an op with a carrier argument grounds its instance from its arguments |
| kb/typing/rule_requirements.rs:3022 | spec_at_an_unknown_carrier | ohscp | V | the call owes an instance at a carrier the load cannot know |
| kb/typing/rule_requirements.rs:3205 | witness_carriers_of | wdc | S | the carriers witness provisions dispatch at (memoized in the index) |
| kb/typing/rule_requirements.rs:3774 | call_args_at_spec_carrier | or_sole | V | which arguments sit at the carrier; or_sole read only with two or more parameters |
| kb/typing/rule_requirements.rs:3956 | collect_covered_calls | ohscp | V | a call is woven only with an argument at the dictionary's carrier |
| kb/typing/rule_goal_routes.rs:1919 | slot_read_at_goal | or_sole | S | the carrier binding of a woven slot's requirement |
| kb/typing/rule_goal_routes.rs:2499 | carrier_instance | or_sole | S | builds `spec[carrier = ?#slot]` |
| kb/typing/rule_goal_routes.rs:3005 | sort_requirement_for_call | or_sole | S | the instance asked of the sort's requirements, keyed at the carrier |
| kb/typing/rule_goal_routes.rs:3088 | sort_requirements_at_slot | or_sole | S | which sort requires have their carrier at this slot |
| kb/typing/rule_goal_routes.rs:3104 | sort_requirements_at_slot | or_sole | S | the instance term keyed at the carrier, per spec |
| kb/typing/value_type.rs:1510 | every_carrier_at_carrier_param | scp | V | simp guard: do all carrier arguments stand at the carrier |
| kb/typing/value_type.rs:1910 | anchor_sort_goal | or_sole | S | the parameter the anchor goal pins the type at |
| kb/typing/sorts.rs:1750 | check_type_value_against_field | sop | X | the "spec over its parameter" note of a field refusal |
| kb/typing/sorts.rs:1960 | check_value_sort_membership | sop | X | the same note, for a constructor value |
| kb/typing/provision.rs:385 | provider_conforms_to | shcp | SC | does a provider's value conform to the spec as a type |
| kb/typing/provision.rs:413 | positions_typed_at_a_spec_over_a_parameter | shcp | SC | a census of such positions (read by the wi_kssa4 test) |
| kb/typing/provision.rs:669 | check_provision_names_carrier | scp | K | a written provision must bind the carrier (`ProvisionNamesNoCarrier`) — **done** (CXR5B step 7: every type-var an operation takes, `spec_taken_type_vars`; a written `?` binds nothing) |
| kb/typing/provision.rs:811 | check_rule_sort_uses | sop | K | rule-head `Spec.member` at a dictionary spec is checked against the carrier |
| kb/typing/provision.rs:813 | check_rule_sort_uses | scp | K | the carrier the member must name: its own inline ladder (below) |
| kb/typing/provision.rs:865 | parameter_spec_written_as_type | sop | K | a dictionary spec written as a value type is refused |
| kb/typing/provision.rs:1314 | provision_supplier | wdc | W | witness vs fact/own supply route of one provision |
| kb/typing/provision.rs:1501 | spec_op_suppliers_of_provider | or_sole | W | Own vs Witness route, grouped by application — **grouping done** (CXR5B step 3: by `SpecApplication`, every type-var; a self-representing spec at its provider). The route's `about` still reads the single parameter for a spec with a dictionary |
| kb/typing/provision.rs:1599 | merged_provision_bindings | or_sole | P | merge the bindings of same-application provisions — **done** (CXR5B step 3: `SpecApplication`) |
| kb/typing/provision.rs:2490 | write_left_out_params | scp | P | σ: every left-out parameter except the carrier becomes a fresh `?` |

## Ladders that are not one of the three named functions

- `clause_carrier_param` (carrier.rs:2594): scp, else the FIRST parameter, with no class
  gate. Its own doc records a measured defect of reading the first parameter.
- `check_rule_sort_uses` (provision.rs:812-816): scp, else the sole parameter, with NO
  self-representing gate, under the sop gate.
- `op_has_spec_carrier_param` / `spec_carrier_param_of` (value_type.rs:1266, 1301): ANY
  parameter of the operation typed at ANY type-var of the spec, or at the spec itself for
  a self-representing one. This one already reads a SET.
- `registered_effect_kinds` (signature.rs:5877): `Effect`'s `T` binding, by label.
- apply.rs:4172: scp first, then every parameter in turn.
- rule_requirements.rs:3774: or_sole only when the spec has two or more parameters.

## Readers outside the named functions, moved by CXR5B

- `check_provision_binding_agreement` (coherence.rs) bucketed a provider's provisions by the
  binding of the spec's FIRST declared type-var. Step 3: a witness's provisions by
  `SpecApplication`, the provider's own in one bucket (decision 7, and the P readers'
  one view per provider).
- The instance-fact leg of `provider_coherence_groups_with`: two facts of a group are
  ambiguous only at one `SpecApplication` (step 3).
- `spec_carrier_param` (L1) counts a parameter typed at an application of a higher-kinded
  type-var (`m: M[A]` takes `M`) through `declared_type_param_head_vid` (step 4, c1); its 24
  direct callers (scp above), and the ladders built on it, then see `Monad`'s `M`.
  `declared_type_param_vid` keeps its arity pin for its other 25 callers.
- The higher-kinded branch of `check_apply_call` (WI-453) leaves a call a witness at the filled
  carrier answers, or whose bracket names another provider, to the resolution after it (step 4,
  c1).
- `check_instance_fact_op_signatures` (signature.rs, an M reader of an operation bound by
  name) passes the receiver of a self-representing spec's operation, the first parameter the
  spec types `Self` and the bound operation types the provider, as `check_member_signature`
  does (step 5).
- The `NoCandidates` arm of `check_apply_call`: for a self-representing spec something
  provides, a call naming no carrier is held to the provisions at the type-vars σ fixed
  (`a_provision_meets_fixed`, step 6, e7), beside `carriers_no_provision_binds`, which asks a
  carrier at the single parameter.
- `validate_instance_selection` (slots.rs, §4.4's check 3) and `render_instance_tie`
  (dispatch.rs) read `is_value_directed_provider` only where an operation of the spec takes a
  value that decides its dispatch (`op_has_spec_carrier_param`, L6) — step 8, c3/g4.
- `candidates_at` (candidates.rs): a goal naming its carrier that leaves out a type-var the
  carrier's row binds to its provider's own parameter is at one of its values (step 8, g4).
