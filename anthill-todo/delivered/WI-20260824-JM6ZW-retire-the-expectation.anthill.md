## Attributes

- id: WI-20260824-JM6ZW-retire-the-expectation
- created: 2026-08-24T05:05:30Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-16T23:16:28Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-Q0093-every-operation-expression

- tags: proposal-055

## Description

RETIRE THE EXPECTATION-DIRECTED CLASSIFIERS AND LAND UMBRELLA A'S DIAGNOSTICS (proposal 055 umbrella A, step 6 + §8).

Delete the expected-`Type` hint chain AS A CLASSIFIER. Expected `Type` survives only as an ordinary validation / inference input, per docs/design/055-implementation.md §10 step 6.

SITES (measured): `type_slot_arg_hint` (`typing.rs:9226`) and its gate `arg_names_sort` (`typing.rs:9252`); the `sort_app_hint` computed in `apply_arg_hints` (`typing.rs:9102`) and consumed at the Apply arm (`typing.rs:10512`); the `expects_reflect_type` call in `check_bare_ref`'s WI-206 sort arm (`typing.rs`, in the arm at ~6474); and the declared-type lookups that exist to FEED the hint (`typing.rs:10565`, `10769`, `10797`, `10817`). A lookup that also serves validation stays -- say at its site which of the two questions it is answering after this change, because that is the distinction the hint chain currently blurs.

DIAGNOSTICS (design §8) belonging to umbrella A: a wrong destination reads `expected String, got Type (Cell[Int64])` and names the DENOTED sort, never an unresolved nested name; a forgotten-parens constructor name in a `Type`-accepting position must name the denoted sort in the error or trace, so the implicit reading is visible -- proposal 055 §2 names this as the residual risk the uniform rule accepts and requires the diagnostic to cover it; the companion-versus-`Type`-member ambiguity names both routes, if WI-20260824-PAPX0 has not already landed it. NO fallback that retries a failed value resolution as a type, or the reverse: resolve the symbol once and classify loudly.

CONTROL -- THE SHARPEST IN THE UMBRELLA, and the reason this must not be folded into WAHB6. Two back-outs, stated separately: (1) restore the hints while keeping the record -- the classification tests still pass, which is what proves the hint is no longer load-bearing; if any row needs the hint back, the record did not reach that site and the finding belongs here, not in a later ticket; (2) remove the record while the hints are gone -- the WI-206 / WI-707 rows fail. A change that passes both ways measures nothing; name the rows for each direction at the test site.

ACCEPTANCE: WI-206 / WI-707 / WI-709 / WI-710 controls remain green; full Rust workspace via rustland/scripts/test.sh; run the /code-review skill before commit.

## Changes

### 2026-10-08T09:06:43Z — feedback — claude

DEPENDENCY ON WI-20260824-PAPX0 REMOVED (user's go, 2026-10-08). What this ticket waited on PAPX0 for is settled in fd1cf282: the dot split is encoded, and the diagnostic this Description lists -- "the companion-versus-`Type`-member ambiguity names both routes, if WI-20260824-PAPX0 has not already landed it" -- no longer exists. PAPX0's decided rule is that a receiver denoting a sort resolves its dot in that sort only, so no surface names both a companion member and a member of `Type` (kernel-language.md sec 5.4; design 055 sec 4 and sec 8 are corrected). PAPX0 stays open over three spelling asymmetries this ticket does not need: WI-20261008-R653S, WI-20261008-7B15V, WI-20261008-A3FY2.

### 2026-10-16T23:16:26Z — feedback — user

DELIVERED — the expected `Type` no longer classifies. `type_slot_arg_hint`, its gate `arg_names_sort`, the `sort_app_hint` and the `Apply` frame's WI-707 arm it fed, `check_bare_ref`'s WI-206 arm, the lookups that existed only to feed the hint (`has_sort_arg`, `has_sort_field`) and `expects_reflect_type` (no caller left) are gone. A sort reaching the typer without the walks' record is the loud `TypeError::UnclassifiedTypeValue`, never a retry as a type. Rows: `rustland/anthill-core/tests/include/wi_jm6zw_expectation_classifier_retired_test.rs` (10) and `simp_rewrite::tests::a_sort_in_a_term_built_rhs_is_recorded_as_a_type_value`.

THE FINDING, as the Description said it would belong here. The hint was still LOAD-BEARING, for RULE BODIES. Measured with a probe at the four retired arms over the whole workspace: every firing was a rule body (wi710, wi839, wi1058, wi927, wi_9r5hn, wi_9wvt7, wi_rxt6s); WAHB6's record covers every operation-body occurrence, the rule-body walk recorded none. With the hint gone and nothing else changed, 8 peer rows failed. The rule-body walk (`Loader::build_body_atom_occurrence_inner`) now records a bare sort in a data slot (`Loader::body_bare_type_value`) and a bracketed sort application outside a goal as the `Expr::TypeValue` the operation-body walk builds, by the same predicates (now one KB method, `KnowledgeBase::is_type_value_head`). The clause is unmoved — the node heads as the `Ref(S)` / `Fn{S,…}` it replaced (`occ_head`), pinned by `the_clause_a_rule_body_matches_is_unmoved`. That is the rule-body OCCURRENCE half of design §7's last row; `convert_term` (facts, rule heads) and declared-column validation stay umbrella B's (WI-20260823-53W12).

TWO ROLES the rule-body walk must not record in, both measured (`Loader::in_non_value_role`, consumed per node like `in_body_goal`): the spec of a bare `require[Spec]` (8 rows of wi_51w18 / wi_96ztm / wi_gfs6a / wi_mhrn1 / wi_qmfc5 fail without it) and a SEGMENT of a written dotted name (`dotted_nullary_op_call_test::an_eq_operand_is_typed_and_run_as_the_call` fails without it — `0 = Box.zero` lost its citation reading).

DIAGNOSTICS (design §8). The wrong-destination suffix was Q0093's; `wi206`'s row now asserts `got Type (Cell)`, which it had deliberately left to this ticket. FORGOTTEN PARENTHESES: the one bare name that denotes a type without a recorded `TypeValue` — a free-standing entity, or an eponymous sort — is named too, from the same predicate its typing arm uses (`denoted_type_value`): `use_leaf(Leaf)` is `expected Leaf, got Type (Leaf)`; a binder spelled `Leaf` is not. The node itself is deliberately NOT rewritten into a `TypeValue`: measured, that turns `(Ep).em()` over an eponymous `Ep` from refused into the sort's companion call (§5.4) — a language question, see below. THE REVERSE SLIP: `is_modifiable(Cell(Int64))` LOADED while the hint read parentheses as a bracket in a `Type` slot; it is refused now, `unknown functor — `Cell` names a sort, and a sort applied as a call is a construction, which `Cell` is not …; a type is written with brackets, `Cell[…]`` (surface-neutral: the node may come from a paren-less chain or a term).

CONTROL — the ticket's two directions, MEASURED over 286 rows of this file and its peers:
 (1) hints restored, record kept: 3 fail, all in the new file (the paren row and the two hand-built rows that ask the retired question directly), NOT ONE PEER ROW — the hint carries nothing.
 (2) record removed, hints gone: 93 fail, among them every WI-206 / WI-707 row that reads a type value.
 (3) only the rule-body record removed: 11 (the 8 peer rows + 3 here).
 Each review-found piece reddens its own row(s) on its own back-out; the table is the new file's header.

/code-review (high) FOUND NINE; seven repaired, two answered:
 * HIGH, REPAIRED — a whole equation RHS `rule ty() <=> Cell[V = Int64] @[simp]` was left an `Expr::Apply` by a depth gate copied from WI-710 while its bare twin was recorded; the depth test is gone from the record (`at_goal` already says "top-level atom"). Row: `a_whole_equation_rhs_is_recorded_as_its_bare_twin_is`.
 * HIGH, PARTLY REPAIRED — producers that build occurrences from TERMS: `substitute_to_occurrence` (an equation with no written RHS) now records a sort that is not its own constructor (unit row). `materialize_from_handle` / `term_body_to_nodes` (a rule asserted from terms) is LEFT, deliberately: it builds goals too, and recording there needs the goal-slot reading the walk has; such a body meets the loud `UnclassifiedTypeValue`. The probe found no tested path through it.
 * MEDIUM, REPAIRED — the advice claimed "applied with parentheses" on surfaces that were not (wi_5g28a's paren-less `Outer[…].Inner`); now surface-neutral, and the terse `unknown functor` that wi92va4 pins stays.
 * MEDIUM, REPAIRED — WI-710's argument check gated on `kind_of` beside a `has_kind` classifier: a namespace-first `Box[W = Int64]` in a relation goal loaded. Row: `a_type_value_s_arguments_are_checked_whatever_order_its_name_was_declared_in`.
 * LOW, REPAIRED — the `TypeValue` early return skipped the tail's `dot_chain` stamp; two doc comments were displaced onto the wrong functions; `UnclassifiedTypeValue` now says in its text that it is a producer defect (it keeps `TypeMismatch` as its carrier, as `BottomExpr` does: `LoadError::Other` loses the span).
 * ANSWERED — the bracket-entry CONSTRUCTOR rule of the operation-body walk is not mirrored: in a rule a constructor is a term the clause matches, the line `lowering_rule_compound_expr` already draws; the doc claimed more and is corrected.
 * ANSWERED — "another ambient flag": it is one flag for the non-value role, consumed per node as `in_body_goal` is; building the bare `require` leaf directly is the route that site's own comment rejects (it changes every `require[Spec]`).

REPORTED, NOT REPAIRED — measured, each with its control:
 (a) A rule body checks NO destination at a `<=>` operand: `?x <=> needs_int("s")` over `needs_int(n: Int64)` loads, and so does `rule r(?x: Int64) :- ?x <=> "s"`. So a type value there is validated nowhere — not a type-value question (the `"s"` control), and the reason the new file has no rule-body destination row.
 (b) `(Ep).em()` over an eponymous `sort Ep { entity Ep(…) }` is refused (`Type.em: no such member`), pinned "refused today" by `wi_rxt6s::an_eponymous_sort_by_a_path_is_refused_as_its_bare_name_is`. §6.3 says a bare `Ep` denotes the type and §5.4 says a receiver denoting a sort takes the companion dot — read together they say `Ep.em()`. Which reading stands is the user's call.

SPEC / DESIGN SYNC: design 055 §7 (the rule-body occurrence half), §8 (forgotten parentheses, the reverse slip), §10 step 6 (done). kernel-language.md unchanged — it already states the rule; this implements it in rule bodies.

ACCEPTANCE: full Rust workspace via `rustland/scripts/test.sh` — 9975 passed, 0 failed, 17 ignored (shared-base recipe); `scripts/families.sh` green, no verdict moved; WI-206 / WI-707 / WI-709 / WI-710 controls green. scaland `sbt testFull` — 738 passed (693 + 45), 0 failed; this change touches no file under `scaland/`.

