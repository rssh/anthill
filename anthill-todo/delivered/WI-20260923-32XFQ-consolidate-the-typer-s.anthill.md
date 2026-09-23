## Attributes

- id: WI-20260923-32XFQ-consolidate-the-typer-s
- created: 2026-09-23T14:30:54Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-23T22:51:32Z

- acceptance: cargo-test

- tags: typing

## Description

CONSOLIDATE THE TYPER'S REMAINING STRUCTURAL DUPLICATION — about 700 lines across the provision-fact decoder, the term walkers, the leaf rewriters and the effect-row pair. Behaviour-preserving only.

WHAT EXISTS. A duplication review of kb/typing (2026-09-23, run on 10cc7d94's single-file typing.rs; the split 7706ae6c renamed no function, so every name below greps in kb/typing/) found little verbatim copy-paste — the longest exact clone is about 34 lines — and roughly 900-1000 lines of STRUCTURAL duplication. The low-risk part landed in c1872e94 (`view_ref_symbol` as the one bare-name reader, two hand-rolled `map_fn_children` copies, `sort_operation_names` onto `find_sort_info`, one label-pairing walk, one `apply_within` minter, four misplaced docs). This ticket is the rest. Each item was classified by a line-by-line comparison, and the differences listed are exactly what a merge must keep or reconcile deliberately.

1. THE `SortProvidesInfo` ROW DECODE, SPELLED 16 TIMES (~150 lines). Iterate provision rids, skip non-facts, read `sort_ref` → carrier and `spec` → view and base; every missing field silently `continue`s. Sites: `find_spec_op_for_provided_sort` (dot_rule.rs); `decoded_provision_rows` (provides_index.rs); `impl_sorts_providing_spec`, `collect_provides_candidates` (candidates.rs); `check_provider_requires`, `check_eq_noneq_exclusive`, `collect_provisions` (coherence.rs); `provisions_from_rids` (provision.rs); `check_override_refinement`, `all_spec_clause_views`, `check_instance_fact_op_signatures` (signature.rs); `directly_provided_specs`, `provider_spec_view_bindings` (carrier.rs); `provided_spec_base_syms` (projection.rs); `self_supplied_entries` (requires.rs). `build_provides_index` reads the fields independently and is not a candidate.
   `collect_provisions` already IS the full-relation decoder (`all_provisions` wraps it "rather than spelling a fourth one"). Shape: `ProvidesRow { rid, carrier, spec_view, spec_base }`, a `decode_provides_row`, and all / by-carrier / by-spec iterators with the `same_sort_canonical` re-filter BUILT IN — `self_supplied_entries` documents a real instance of that re-filter being forgotten (WI-660/672), and the sibling `ProvidesConditionInfo` relation already states the rationale. `provided_spec_base_syms` duplicates `directly_provided_specs` except raw vs canonical dedup, and its one caller takes the first match, so it can go. A second, smaller helper: `provision_sigma(kb, &row)` for the three per-site σ builders.
   KEEP OR RECONCILE DELIBERATELY: the carrier decode is spelled three ways (`load::sort_ref_functor`; a hand-rolled `Fn|Ref|Ident` in `impl_sorts_providing_spec` and `collect_provides_candidates`, which ignores the `name:` child `sort_ref_functor` prefers; a `Term::Fn` shape test on the requires side); `collect_provides_candidates` compares the spec base by RAW symbol (WI-20260923-N3W68 #10); `unwrap_spec_view` drops a bare application's bindings where `check_override_refinement` reads the raw named args (documented at `goal_from_op_requires_entry`); `all_spec_clause_views` reads `ProvidesConditionInfo` TermId-only where `decoded_condition_row` goes through the Value route.

2. "DOES THIS TERM CONTAIN X" WALKERS (~140 lines).
   * Eight TermId `Fn`-spine walkers differ only in the leaf test, with identical short-circuit order: `term_contains_callable` (callable.rs), `term_mentions_an_entity`, `type_term_has_variable` (value_type.rs), `declared_type_mentions_param` (rule_constraints.rs), `type_term_mentions_type_var`, `type_term_mentions_op_tp` (arg_hints.rs), `term_contains_functor` (rules.rs), `occurs_in` (unify.rs). One `term_any_subterm(kb, t, pred)` replaces them. No generic walker exists yet; `TermView::bears_opaque` and `type_view_is_ground_g` are the precedents.
   * `contains_type_param(t)` (provision.rs) is exactly `!type_value_is_ground(t)` (type_preds.rs), arm for arm through `type_view_is_ground_g`.
   * Seven TermView walkers share only the Functor-arm child loop: `view_contains_type_param`, `view_bears_denoted` (provision.rs), `view_references_any`, `view_carries_undecided_var` (effects.rs), `type_mentions_flex_var`, `type_view_is_ground_g` (type_preds.rs), `occurs_in_view` (unify.rs) → `view_any_child` / `view_all_children`.
   INTENTIONAL, KEEP: the node-spine walkers `node_contains_callable`, `node_type_is_ground_g`, `occ_contains_var` have per-form policies (Denoted, PolyType, Guarded, Arrow, unknown kind each answered differently and documented); the Value-carrier dispatchers pick OPPOSITE "conservative" answers by design; `view_references_any` and `view_carries_undecided_var` are documented as not twins.

3. TERM LEAF REWRITERS (~60 lines). `substitute_spec_via_subst[_term]` (dict.rs), `substitute_in_spec[_term]` (requires.rs), `apply_witness_instantiation`, `substitute_carrier_params` (carrier.rs) are "rewrite a leaf, else `map_fn_children`" → `rewrite_term_leaves(kb, t, leaf)`. CAUTION, TWO LEAF SETS: `substitute_spec_via_subst_term`, `substitute_in_spec_term` and `substitute_ref_syms_rec` treat {`Ref`, nullary `Fn`} as leaves; `substitute_impl_params_alloc`, `subst_requires_value` and `substitute_ref_terms_rec` treat `Ident` as one too (`substitute_in_spec`'s doc names `substitute_impl_params_alloc` as its model yet omits `Ident`). Merging ACROSS the two sets is a behaviour change unless `Ident` is proven absent from stored specs — that half belongs to WI-20260923-N3W68.

4. `unify_effect_rows` / `subtype_effect_rows` (effects.rs, ~65-80 lines). Identical: the fast path, the decompose, the lacks registration, the multi-tail arm, and the both-open arm (WI-334 shared tail, WI-441 rigid aliasing, the Rémy fresh tail). Exactly five differences: the pairing (`pair_present_labels` vs `cover_present_labels`); the multi-tail flag; the `(None, None)` test (`only_a` and `only_b` empty vs `only_a` empty); the `(None, Some)` arm (requires `only_b` empty, then binds vs binds unconditionally); the `(Some, None)` bind (`&only_b` vs `&[]`). Lowest-risk first step: extract `bind_both_open_tails` and the shared prologue, which are byte-identical and have no behavioural surface; then `relate_effect_rows(.., directional)` mirroring `multi_tail_rows_compat`'s existing flag, both names kept as wrappers so the ~16 call sites do not move.

5. SMALLER ITEMS (~150 lines together):
   * `expr_call_parts(&Expr)` for the Apply | Constructor | Instantiation → (functor, pos, named) extraction repeated at 9 sites (rules.rs, rule_requirements.rs, anchor.rs, rule_constraints.rs). CAUTION: `surviving_dot_apply` and `rigid_value_reads` (elaborate.rs) walk in SOURCE order (reverse push) and five other stack walkers do not — moving them to one walker changes the order of emitted diagnostics.
   * `instantiate_provider_entries` (candidates.rs) / `provider_requires_subgoals` (provision.rs) differ only in the chain source and the value substitution — pass a closure.
   * The op-requires bare-application decode shared by `goal_from_op_requires_entry` (slots.rs) and `normalize_op_requires_entry` (requires.rs) — a 30-line run; a third copy in `check_provider_requires` deviates (WI-20260923-N3W68 #9).
   * `synth_op_req_names_of` / `synth_req_names_of` (requires.rs) → one `name_slots`. The `__req_*` names are read by eval frames: the format strings are an ABI and must stay exact.
   * `value_contains_rigid` / `value_contains_projection` (projection.rs) → one `extract_type_any(kb, ty, hit)` with rigid's full descent (the hit fires before the descent, so it reproduces both). `value_contains_expr_carried` descends LESS — do not fold it in here (WI-20260923-N3W68 #6).
   * The `constrain_*` term/occurrence twins and `collect_term_type_constraints` / `constrain_application` (rule_constraints.rs): carrier-generic over the argument carrier; their docs already say the twins must stay in step.
   * The `bare_spec_arg_*` / `carrier_arg_provision_projection` prologue, receiver recognizer and effect-row wrap (constructor.rs); reuse `leaf_var_ref` (subtype.rs) at the 7+ `Ref | Ident | VarRef` recognizers.
   * `transitive_provision_view` / `transitive_provider_spec_view_bindings` (carrier.rs): the same recursion, but the visited check sits BEFORE the direct test in one and AFTER it in the other.
   * `collect_declared_spec_views` / `collect_find_dictionary_bases` (rule_requirements.rs); the carrier-parameter recognizer shared verbatim by `carrier_param_receiver_for_values` / `spec_carrier_param_candidates` (carrier.rs, whose own doc says sharing it is what keeps the answer single); `parameterized_value` / `named_tuple_value` (result.rs); `bindings_cover_named` / `bindings_cover_named_pairs` (provides_index.rs).

REVIEWED AND NOT DUPLICATION — do not merge: `more_general_type` / `more_specific_type` (named lub/glb duals); the unify/compat pairs `unify_arrow_view` / `arrow_compatible_view`, `unify_named_tuple_as` / `named_tuple_compatible_as`, `unify_arrow_params` / `arrow_params_compatible`, `unify_arrow_function_view` / `arrow_function_compatible` (unify binds and is symmetric, compat is directional with a contravariant parameter swap — they merge only under a family-wide Relation abstraction, which is a design of its own); `TypeErrorContext::entity_name` / `field_name`; `substitute_ref_syms_rec` / `substitute_ref_terms_rec`; `unwrap_spec_view` / `parametric_value_parts`; the witness-soundness gates.

ACCEPTANCE: no behaviour change. Each merged group's equivalence argued at delivery — the differing lines named, and why the merge keeps them. A merge that WOULD change behaviour (a leaf set, a descent set, a raw→canonical compare) is not done here; it moves to WI-20260923-N3W68. No new warnings: compare the SUMMARY lines of `cargo check -p anthill-core --tests` before and after, not a grep of lines starting with `warning` (file-prefixed warnings do not start with it, which is how c1872e94 first shipped two unused imports). rustdoc `--document-private-items` warnings in kb/typing no higher than before. Full workspace green via rustland/scripts/test.sh. One commit per group.

REFERENCE: the review snapshot is `git show 10cc7d94:rustland/anthill-core/src/kb/typing.rs`; the low-risk half is c1872e94; the split is 7706ae6c (typing.rs's module doc maps the files).

## Changes

### 2026-09-23T22:51:31Z — feedback — user

DELIVERED in five commits, one per group, each behaviour-preserving with its equivalence argued in the commit message (the differing lines named, and how the merge keeps them): 93416f60 (1), 5dec3c88 (2), fea80750 (3), e666bb68 (4), 756e3966 (5). Each commit: full workspace suite green (36 binaries, 7427 passed, 0 failed), `cargo check -p anthill-core --tests` summary lines and the kb/typing rustdoc (--document-private-items) warning set identical to before the ticket, /code-review (high) run and its findings fixed or stated.

1. PROVISION ROWS — `ProvidesRow` + `provides_rows` / `provides_rows_of_provider` / `provides_rows_of_spec[_in]` (provides_index.rs), the canonical re-filter built in. Sixteen readers moved: the ticket's sixteen sites less `build_provides_index` (not a candidate, as the ticket says), plus `provides_out_edges`' live arm; `provided_spec_base_syms` and `provisions_of_spec` / `provisions_from_rids` gone; `sort_clause_fields` under `all_spec_clause_views`; `spec_param_sigma` for the three symbol-keyed σ builders.
2. WALKERS — `term_any_subterm` under eight TermId walkers; `contains_type_param` → `!type_value_is_ground`; `view_any_child` / `view_all_children` under seven view walkers.
3. LEAF REWRITERS — `rewrite_term_leaves` (+ `rewrite_spec_value`) under eight σ substitutions, each keeping its own leaf set.
4. EFFECT ROWS — `relate_effect_rows(.., directional)` + `bind_both_open_tails`; exactly the five documented differences, marked in the body.
5. SMALLER ITEMS — `expr_call_parts` (10 sites), `requires_chain_goals`, `op_requires_application_bindings`, `name_slots` (the `__req_*` ABI reproduced exactly), `type_any_part`, `ConstrainedArg` + generic `constrain_application`, constructor.rs' prologue / effect-row wrap + `leaf_var_ref` at 8 sites, `compose_through_provision_chain` (+ `VisitOrder`), and the four small pairs.

KEPT APART, deliberately — each is an answer changing, not a merge, and is named at its site:
  * `provides_spec_base_sym` also reads a DOTLESS `SortView` functor (a top-level `sort SortView`) as the view wrapper; `unwrap_spec_view` does not (N3W68 #9 unified four spellings and missed this fifth). Four readers keep it.
  * `sort_ref_functor` prefers a `name:` child of the `sort_ref`; `impl_sorts_providing_spec` / `collect_provides_candidates` read the bare head (`ProvidesRow::sort_ref_head`).
  * The symbol-keyed σ (`check_override_refinement`, `check_instance_fact_op_signatures`, `requires_shadow_is_confusable`) pairs NO positional binding; `check_provider_requires`' short-name σ does.
  * `view_contains_type_param` is `!type_view_is_ground_g(v, false)` except on a child a view names and cannot serve.
  * The two transitive provision walks' visit orders (`VisitOrder`): identical answers today; different if a carrier's direct view is found but its parent hop cannot compose.
  * `all_spec_clause_views` reads `ProvidesConditionInfo` term-only.

ALSO FOUND AND FIXED, OUTSIDE THE BEHAVIOUR-PRESERVING GROUPS (its own commit, f7adb555): `projection_type_error`'s doc and `#[track_caller]` sat on `delta_failure_text` (S8CBV inserted it between them), so every projection error's WI-510 origin was the helper's own line — driven by `projection_error_origin_test`, which fails with the attribute where it was; and `build_op_scoped_dicts`' doc and `#[allow]` sat on `stamp_op_scoped_dicts` (28TAT inserted it between them) — doc/lint only.

