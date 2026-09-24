## Attributes

- id: WI-20260923-N3W68-triage-thirteen-suspected-twin
- created: 2026-09-23T14:30:59Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-23T20:27:31Z

- acceptance: cargo-test

- tags: typing

## Description

TRIAGE THIRTEEN SUSPECTED TWIN DIVERGENCES IN THE TYPER (review items #3-#15): in each pair one copy was changed and its twin was not. REPRODUCE FIRST; fix what reproduces, correct the doc where it does not.

WHAT THIS IS. The 2026-09-23 duplication review of kb/typing (run on 10cc7d94's single-file typing.rs; the split 7706ae6c renamed nothing, so the names below grep in kb/typing/) looked for pairs where a fix landed in one copy only. Items #1 and #2 are CLOSED: #1, the override return leg's carrier gate, by 87246ea2 (its WI-1MAGR sibling, `instance_binding_type_ok`, is WI-20260923-Z1Q8B); #2, WI-20260910-FDPJ8's canon reaching only one `apply_within` minter, by c1872e94. The thirteen below are REPORTED, NOT MEASURED — each was found by reading, with line-level evidence, but none has a driving program yet, and the confidence given is the reviewer's. Several are "either the code or its doc is wrong", and the reproducer decides which.

#3 (medium) TWO DIFFERENT PARAMETERIZED BINDINGS "AGREE". `provision_bindings_agree` (coherence.rs) and `provision_values_agree` (carrier.rs) fall back to the head's BASE sort (`sort_functor_of_view` / `load::sort_ref_functor`), so `List[T = Int64]` and `List[T = String]` agree; `provision_values_agree` also equates any two effect rows, arrows or tuples, since `sort_ref_functor` returns the functor of any `Term::Fn`. Both docs contradict the code ("Anything else answers `false`"; "Non-sort-ref values … fall back to `TermId` equality"). Consequence: `check_provision_binding_agreement` does not refuse two provisions binding one parameter to those two types, and `provider_spec_view_bindings`' WI-842 merge — which relies on that refusal ("a disagreement is a load error") — silently keeps the first. Probe: one carrier, two provisions of one spec, the parameter bound to `List[T = Int64]` and `List[T = String]`. A fix is STRICTER, i.e. a behaviour change: `a == b || (both bare sort refs && same_sort_canonical)`; measure the stdlib under it.

#4 (medium-low) THE OCCURS CHECK MISSES THE NULLARY-`Fn` SPELLING. `occurs_in` (unify.rs) matches only `Term::Ref(s)`, while `occurs_in_view` matches any nullary functor head (on a TermId that includes `Fn{s, [], []}`) and `walk_type`'s alias hop chases both spellings. `sort_param_ref_is_var`'s own doc says the occurs check "must refuse precisely the bindings the σ walk can chase"; the WI-359 nullary-`Fn` parameter spelling exists, and SORT-kind names are exempt from the CZJ2N `Ref` canon. Delegating `occurs_in` to `occurs_in_view(kb, v, &TermIdView(t))` is otherwise arm-for-arm identical.

#5 (medium-low; reachability unproven) `row_tail_termid` (effects.rs) LACKS the WI-20260904-02ERR `Value::Node(TypeNode::Var)` arm that `resolved_var` and `walk_value_to_resolved` gained. In `decompose_effect_row_raw` an unbound occurrence-carried variable in an effects slot then decomposes as the EMPTY row, silently (mid-algebra it hard-rejects). Producers of such a leaf exist: `value_to_type_child(_at)` with a `Value::Var`, e.g. the arrow rebuild in elaborate.rs.

#6 (medium-low) `value_contains_expr_carried` (projection.rs) DESCENDS ONLY `Parameterized` / `NamedTuple`; its wide twin `value_contains_projection` also descends `Arrow`, `EffectsRows` and `PolyType` (WI-1083, 50B2K). Its doc justifies excluding `RigidTypeProjection`, not the shallower walk. So an `x.E` nested in an arrow binding (`requires Desc[T = (a: x.E) -> …]`) escapes both S8CBV refusals (in dict.rs and bridge.rs) — the refusals that exist to stop the "loads clean, aborts a debug build" shape.

#7 (low-medium) `sort_sym_of_term` (args.rs) ACCEPTS AN ANY-ARITY `Fn` although its doc says nullary, so `dispatch_values_match` (carrier.rs) equates `List[T = Int64]` with `List[T = String]`, and any two arrows, once `types_lesseq` fails. `match_candidate_against_goal` (candidates.rs) calls its step (3) "the existing shallow check", so it may be deliberate — then the doc is what is wrong.

#8 (low; known, see the eval/mod.rs comment) `requires_chain_flat` (requires.rs) COMPUTES ONE ANSWER TWO WAYS. Warm cache: a flatten of the substituted tree, whose visited set is path-local (shared sub-requirements appear twice). Cold cache: `collect_requires_unsubstituted`, a global visited set, deduped, raw specs. `check_obligations` pushes one `MissingObligation` per chain entry, so its output count depends on cache warmth.

#9 (low) THE THIRD COPY OF THE POSITIONAL-BINDING FILL, in `check_provider_requires` (coherence.rs), silently TRUNCATES extra positionals (`zip`) where its siblings (`goal_from_op_requires_entry`, `normalize_op_requires_entry`) refuse or keep the entry as written; and it detects `SortView` with `ends_with("SortView")` without the dot, so it also matches e.g. `MySortView`. ("Is this functor SortView" is spelled four ways across the typer; one `is_sort_view_functor` would end that.)

#10 (low-medium) `collect_provides_candidates` (candidates.rs) COMPARES THE SPEC BASE BY RAW SYMBOL (`view_base_sym != goal.spec_sort`), where `provider_spec_view_bindings` warns that "a raw `==` would silently no-op" across import scopes. Its local justification covers only the raw-equal ⇒ in-bucket direction.

#11 (low) THE REQUIRES-SIDE `sort_ref` DECODE (`build_requires_index` in provides_index.rs, `collect_sort_requires` in requires.rs) uses a `Term::Fn` shape test that `decoded_condition_row`'s doc (provides_index.rs) records as wrong for a constructor owner (`make_name_term_from_sym` mints a `Ref` there); every provides-side reader uses `sort_ref_functor`. The index and the scan agree with each other, so this is consistent but narrow.

#12 (low) ONE NULLARY TERM, TWO ANSWERS (CZJ2N): `typaram_occurrence_sym` (carrier.rs) and `sort_sym_of_term` answer `Ref(Nothing)` and `Fn{Nothing, [], []}` differently — the former goes through `extract_sort_ref_sym` / `type_head` to `None` with no `Ref` arm after it, the latter hits the nullary-`Fn` arm and returns `Some`.

#13 (low) `spec_binding_head_sym` (projection.rs) EXCLUDES `Ident`, where `view_ref_symbol` — the one bare-name reader since c1872e94 — includes it; and its fallback `_ => extract_sort_ref_sym(..)` is dead for TermIds (the "deep `sort_ref(name: Ref(s))`" it claims to serve is not recognized by `type_head` at all).

#14 (low) `type_mentions_sort` (type_ctor.rs) CLAIMS TO MIRROR `value_contains_projection` "THROUGH EVERY CARRIER" but lacks the `PolyType` / `ExprCarried` / `RigidTypeProjection` descent; `return_reducible_ctors`' walk has the same gap. A `Concat` / `Without` under a ∀ in a return type is then neither reduced nor loudly refused.

#15 (low) PLACE-HEAD TWINS DIFFER (projection.rs): `term_place_head_sym` accepts `Ref` + a `field_access` chain only; its occurrence twin `occ_place_head_sym` also accepts `Ident` and `VarRef` (whose term twin is `var_ref(name: Ref(c))`). The consumer `continue`s silently on `None`.

STALE DOCS FOUND BY THE SAME REVIEW — fix with the item they touch, or on their own: `resolved_type_is_ground_g` (type_preds.rs) has no doc and the WI-385 doc sits on its wrapper; `subtype_effect_rows` says its `subst` is a scratch "allocated by `arrow_compatible_view`" — since WI-335 it is threaded; `extract_sort_ref_sym`, `walk_type` and kb/mod.rs claim `type_head` recognizes the deep `sort_ref(name: …)` form, which it does not (that form reads as `Parameterized{base: sort_ref}`); `op_info::declared_type_param_var(kb, sort, name)` and `typing::declared_type_param_var(kb, t)` are two different functions with one name.

ACCEPTANCE, PER ITEM: a reproducer driven through `load_all` or resolution — not "it loads" — with its back-out stated at the test; then the fix, or, when it does not reproduce, the doc corrected to what the code does and why. A behaviour change (#3 is stricter, #4 refuses more bindings) is named in the delivery with its stdlib and corpus impact measured. Full workspace green via rustland/scripts/test.sh. Split an item into its own ticket at pickup if it grows.

REFERENCE: the review snapshot is `git show 10cc7d94:rustland/anthill-core/src/kb/typing.rs`; the fixed pair #1 is 87246ea2, #2 is c1872e94; the structural-duplication remainder is WI-20260923-32XFQ and the WI-1MAGR sibling WI-20260923-Z1Q8B.

## Changes

### 2026-09-23T20:27:31Z — feedback — user

DELIVERED in 23f0ee37. The thirteen suspected twin divergences, each decided by a program or a census, not by reading.

WI-20260923-N3W68 — the duplication review's items #3–#15, each settled by a program or
by a census rather than by reading. Where nothing reproduced, temporary tripwires on every
divergence point at once, over stdlib + both example corpora + the workspace suite (7410
passed with them in; removed).

REPRODUCED, FIXED
  #3  `provision_bindings_agree` and its route-merge twin compared the HEAD sort, so
      `List[T = Int64]` agreed with `List[T = String]` (and, in the merge, any two
      arrows): one carrier's two provisions — or two intermediates' — loaded or refused
      by source order. One predicate now: identity, or two BARE sorts canonically.
  #6  `value_contains_expr_carried` walked a shallower tree than its wide twin; an
      `x.E` inside an effect row (`requires Desc[T = {x.E}]`) got the structural-former
      refusal instead of S8CBV's. One walk; the narrow one differs only on a rigid
      projection. (The ticket's arrow spelling does not lower in a `requires` at all.)
  #9  The positional→parameter rule was spelled at twelve sites, five pairing by RAW
      INDEX: `provides Spec2[T = C, String]` bound `T` twice, `Spec[T = Map[K = Int64,
      String]]` diverted `String` out of the binding, and an over-applied clause loaded
      clean with the argument dropped. `KnowledgeBase::positional_param_slots` owns it;
      `check_sort_type_args` and all twelve use it. A sort's provides/requires clause and
      an operation's `requires` refuse an over-applied parametric spec where written
      (`excess_positional`); a binding value runs `check_sort_type_args` like a type. An
      `ensures` and an instance claim are exempt: their leftover positional is the
      carrier (WI-402, WI-407) — a first cut that was not refused all of WI-402's
      existential returns. `is_sort_view_functor`: one discriminant for the four spellings
      (the dotless one passed `MySortView`).
  #11 A namespace's `requires` (legal per the spec) was invisible: its `sort_ref` is a
      `Ref` under the canon, and both requires readers shape-tested for `Fn`. They decode
      with `sort_ref_functor`, like every provides reader.

UNREACHABLE (census: zero), FIXED AS THE TWIN, UNIT ROW EACH
  #4  both occurs checks ask one leaf predicate of the view head (the nullary `Fn{p}`
      `walk_type` chases); the term walk stays direct — `named_keys` allocates.
  #5  `row_tail_termid` reads an occurrence-carried variable; only the top-level read was
      affected (the ticket's "mid-algebra hard-reject" does not happen).
  #12 both spellings of `Nothing` answer alike in `sort_sym_of_term` /
      `typaram_occurrence_sym`.
  #13 `spec_binding_head_sym` delegates to `view_ref_symbol`.
  #14 `type_mentions_sort` and `return_reducible_ctors` share one walk, which descends a ∀.
  #15 `term_place_head_sym` reads `Ident` and `var_ref` like its occurrence twin.
  #10 `collect_provides_candidates` compares the spec base canonically (no row: the shape
      needs two interned copies of one sort).

DOCUMENTED, BY DESIGN
  #7  `dispatch_values_match`'s head-functor fallback answered `true` 337 times for
      structured values in ~50 tests (effect-row dispatch, σ-cover flex/rigid pairs): it
      is coarse by design, with the finer verdicts layered on top.

ONE ANSWER BY CONSTRUCTION
  #8  `requires_chain_flat` answered from the tree when warm and an unsubstituted walk
      when cold — different multisets (14072 times in the suite), so `check_obligations`
      grew with the cache. Now `transitive_required_sorts`: each reachable sort once.
      Readers that need bindings use `requires_chain`.

STALE DOCS: `resolved_type_is_ground`'s carrier claim; `subtype_effect_rows`' "scratch σ"
(threaded since WI-335); the deep `sort_ref(name: …)` form claimed read by `type_head` /
`extract_type` (nothing mints it since WI-361); `canonicalize_fact_binding_value`, retired
by S8JYF; `typing::declared_type_param_var` → `denoted_type_param_var` (a different
question from `op_info`'s). kernel-language.md: the positional rule in every position.

TESTS: wi_n3w68_twin_divergence_test (12) + typing::tests wi_n3w68_* (9); every back-out
measured and stated at its test. /code-review (high): 6 findings — 3 fixed (`has_kind` in
the new gate; the binding-value check's scope documented; one `excess_positional` owner), 3
skipped (the no-slot skip in two readers stays: the loader reports first and the refused
provision still reaches them in the same load, measured; #10 has no program).

FOUND, NOT THIS TICKET:
  * rule-body calls whose requirement δ-grounds to an unprovided carrier, or names a structural former, load clean and abort a debug build (WI-NR6FJ's exemptions) — follow-up drafted, to be filed once approved.
  * `scan_sort_carrier_bindings`' `provides` branch is dead: `sort_inst_to_value` returns a SortView-headed term, which its `kind_of == Sort` gate skips, so the bare-spec sugar never narrows from a `provides` clause.
  * (unverified) nested term-form type applications in rule/contract bodies keep their positionals unpaired, and `term_backed_bindings` reads named args only.

### 2026-09-23T20:45:28Z — feedback — user

FOLLOW-UPS FILED (approved): WI-20260923-KCNA0 — a rule-body call whose requirement no provider covers, at a projection the call grounds or a structural former, loads clean and aborts a debug build. WI-20260923-ZBWMC — scan_sort_carrier_bindings' provides arm is dead, so the bare-spec sugar never narrows from a provides clause.

