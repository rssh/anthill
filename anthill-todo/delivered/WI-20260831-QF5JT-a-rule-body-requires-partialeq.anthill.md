## Attributes

- id: WI-20260831-QF5JT-a-rule-body-requires-partialeq
- created: 2026-08-31T15:56:23Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-02T17:48:54Z

- acceptance: cargo-test

## Description

A RULE-BODY `requires(PartialEq[T])` GUARD STOPS DISCRIMINATING BY CARRIER WHEN THE RUST HOST BINDINGS ARE LOADED — it admits a carrier that provides nothing, exactly as it admits one that provides. Found while writing the guard rows of `kernel_mint_address_test` (the cut/find_dictionary address change); NOT that change's defect, and not fixed there.

MEASURED, as a CONTROL PAIR IN ONE SUITE RUN (test-run-20260831-180524.log), which is what makes it a finding rather than a broken fixture:
  `wi300_rule_body_requires_test::guard_blocks_when_carrier_has_no_provider`   stdlib only            asserts 0  -> ok
  `kernel_mint_address_test::the_guard_still_blocks_with_no_rival`             stdlib + rust bindings asserts 0  -> FAILED, left: 1
The two fixtures are near-identical: one namespace holding `sort Witheq { entity we(v: Int64) }` and `sort Noeq { entity ne(v: Int64) }`, `fact PartialEq[T = Witheq]` + `fact Eq[T = Witheq]`, and `rule related(?x, ?y) :- requires(PartialEq[T]), eq(?x, ?y)`, queried at `ne(v: …)`. The only differences are the namespace name and the LOADER: `common::load_stdlib_kb_with_source` (stdlib) vs `common::load_kb_with` (stdlib + `rustland/anthill-stl/anthill/*.anthill`). The positive arm passes in both — `Witheq` answers 1 — so the guard has not stopped working, it has stopped DISCRIMINATING.

THE OBVIOUS HYPOTHESIS IS REFUTED, and stating it saves the next person the same dead end. "The base-only guard succeeds whenever ANY carrier provides the spec" cannot be it: the stdlib ALREADY carries `provides PartialEq` for `Set`, `Map`, `Pair`, `TotalFloat`, `Type` and `EffectExpression`, and WI-300 blocks correctly against exactly that KB. Whatever the rust bindings add is more specific than "a provider".

THE LEAD, and it is a lead rather than a diagnosis: `rustland/anthill-stl/anthill/int64.anthill:50` writes `provides PartialEq[T = Int64]` and `float.anthill:90` the same for `Float`; neither has a stdlib-side counterpart, so `Int64` provides `PartialEq` ONLY when the bindings are loaded. Both fixtures' entities carry a `v: Int64` field. So the suspicion is that the WI-300 typer sweep (`record_find_dictionary_grounding`, kb/typing.rs) grounds the guard's witness to the FIELD's carrier rather than the argument's when a provider for the field type is in scope. NOT ESTABLISHED — nothing was instrumented, and the alternative (the sweep failing to rewrite at all in that configuration, leaving the base-only `find_dictionary(PartialEq)` the resolver then satisfies from any provider) has not been excluded.

FIRST STEP: instrument `record_find_dictionary_grounding` to print the goal it rewrites to, and run the SAME fixture under both loaders. If the rewritten goal differs, the sweep is the site; if it is identical and only the resolver's answer differs, it is not. Three lines of probe settle which, and the session that filed this did not take them.

WHY IT MATTERS RATHER THAN BEING A TEST-ONLY CURIOSITY: a KB that loads host bindings is what a real program has. `anthill run` / `check` / the CLI all load `anthill-stl`'s bindings, and stdlib-only is the test-harness configuration. If this reproduces outside the harness, every rule-body `requires(X)` in a host-bearing KB is admitting carriers it should refuse — a guard that silently stops guarding, which is the failure mode WI-300 exists to prevent. NOT DRIVEN OUTSIDE THE HARNESS: no CLI repro was attempted.

CONTROL, when it is fixed: the `Noeq` arm answers 0 under BOTH loaders, and the `Witheq` arm still answers 1 under both. Back the fix out and the stdlib+bindings `Noeq` arm must return to 1 — that inversion, not the mere presence of a passing test, is what says the fix reaches the real condition. `kernel_mint_address_test`'s guard rows can then move back to `common::load_kb_with` and the note at its `load_guard_kb` deleted; that note is the current record of this defect and points here.

ACCEPTANCE: the mechanism is identified by name and site; the `Noeq` arm blocks under a host-bearing KB; a row pins it with the loader as the only variable; full workspace green via rustland/scripts/test.sh. REFERENCE: WI-300 (the guard and its fixture), kb/typing.rs `record_find_dictionary_grounding` / `check_rule_body_requirements`, tests/common/mod.rs `load_kb_with` vs `load_stdlib_kb_with_source`.

## Changes

### 2026-08-31T16:05:08Z — feedback — user

A SECOND MEASUREMENT, taken while repairing the fixture, and it narrows the mechanism: the SAME fixture answers three different ways under three load recipes, so the variable is not "the bindings" alone but HOW the user file reaches the KB.

  recipe                                                     Witheq (provides)   Noeq (provides nothing)
  stdlib + rust bindings, ONE `load_all`                            1                    1   <- the defect
  stdlib only, TWO passes (`load_stdlib`, then `load`)              0                    0   <- fixture goes DEAD
  stdlib only, ONE `load_all`                                       1                    0   <- correct

All three driven on the same source, differing only in the loader; the third is WI-300's own recipe and is what `kernel_mint_address_test` ships with (16 passed / 0 failed).

WHAT THE MIDDLE ROW ADDS. A separate second-pass `load` of the user file leaves the guard unable to fire for ANY carrier — including the one that provides. So the guard's grounding depends on the user file being present in the SAME `load_all` as the stdlib, which is a fact about the typer sweep's inputs rather than about providers. Whatever explains the top row should explain this one too, and a hypothesis that only accounts for "an extra provider is in scope" does not.

THAT ALSO REFUTES A SECOND DEAD END: the top row is not simply "more providers make the base-only guard succeed". If it were, the middle row (fewer providers, still all of the stdlib's) would block correctly for `Noeq` AND fire for `Witheq`. It does neither.

WHERE THE RECIPE NOW LIVES: `common::load_kb_with_stdlib_only` (rustland/anthill-core/tests/common/mod.rs) — stdlib without `anthill-stl`'s bindings, parsed once, one `load_all`. Its doc carries both traps and points here. `wi300_rule_body_requires_test` and `cut_test` hand-roll the same sequence and were left as found.

### 2026-09-23T11:16:41Z — feedback — user

BRT4Y (2026-09-23) made the stdlib-only load a refusal, so this ticket's stdlib-only control arm no longer exists; kernel_mint_address_test and wi300_rule_body_requires_test now load the full closure and type Noeq's field by a local sort Opaque that provides nothing. MEASURED under the full closure: Noeq(v: Int64) answers 1 (the guard does not discriminate), Noeq(v: Opaque) answers 0, Witheq answers 1 in both — consistent with Noeq getting a DERIVED PartialEq from its Int64 field once Int64 provides PartialEq (eq_derive), not verified by name.

### 2026-11-02T17:48:51Z — feedback — user

DELIVERED AS NOT A GUARD DEFECT (user, 2026-11-02: deliver and record the finding). The guard never stopped discriminating. `Noeq(v: Int64)` HAS an equality: a composite whose `eq` nothing supplies derives `PartialEq`+`Eq` from its fields (kernel-language §8.3, "Closed by the load that defines the carrier"), and `Int64` provides `Eq` in the Rust host bindings (`anthill-stl/anthill/int64.anthill:50-51`), which is why the defect showed only with them loaded. `requires(PartialEq[T])` reads the provision relation, derived rows included, so it rightly admits `Noeq(v: Int64)`. The ticket's acceptance arm "Noeq blocks under a host-bearing KB" is therefore REVERSED, not met. A carrier with no equality is one whose fields give none, which is what the fixtures' `Noeq(v: Opaque)` already is.

MECHANISM BY NAME AND SITE: `kb/eq_derive.rs` `derive_total_eq` (its loop over `total_composites`) AND `derive_conditional_eq`. Either one alone derives the row: the conditional pass takes every composite the total pass leaves and derives the same pair with an empty condition list. MEASURED with a probe under the full closure: `Noeq(v: Int64)` provides PartialEq+Eq with no written clause, guard 1. Skip the fixture's sorts in BOTH passes and it provides nothing, guard 0. Skip the total loop alone and it still provides (now through the conditional pass's clause record), guard 1.

ROWS (wi300_rule_body_requires_test; the variable is the FIELD TYPE now, since BRT4Y made the stdlib-only loader a refusal):
  a_carrier_whose_fields_provide_eq_derives_it_and_passes_the_guard — `Derived(v: Int64)`: PartialEq, Eq, not NonEq; guard 1.
  a_partial_composite_passes_a_partial_eq_guard — `Partial(f: Float)`: PartialEq, NonEq, not Eq; guard 1. The guard asks the spec it NAMES. The file header said it asks `Eq`, and is corrected.
  one_field_without_eq_withholds_the_derivation_and_the_guard_blocks — `Mixed(v: Int64, o: Opaque)`: nothing; the guard leaves NO answer.
  guard_blocks_when_carrier_has_no_provider — now asserts no answer at all, not only no definite one. A suspended guard leaves one residual answer (measured), so the definite count alone could not tell a block from a suspension.
BACK-OUTS, measured over a temporary binary (wi300 + kernel_mint_address + wi1098, 37 rows), each failing exactly one row: both passes skipped for `test.wi300` -> the Derived row; total loop alone -> nothing (by design, stated); an any-field derivation in both passes -> the Mixed row (Mixed [true, true], Noeq still nothing); the guard asking `Eq` where the goal names `PartialEq` (`builtin_find_dictionary`) -> the Partial row. The Partial half of the derivation cannot be backed out under that row: a derived NonEq without its PartialEq is refused at load. The guard grounding to a FIELD's carrier (this ticket's first hypothesis) is what the Mixed row would catch; no such mutation was built. Green under the shared base, fresh, two-step and node-carrier recipes.

ALSO CORRECTED: kernel_mint_address_test's two notes (they called this a defect); wi1098's back-out note. Backing out the `derive_total_eq` call now fails ONE wi1098 row (`a_parametric_sort_derives_a_conditional_row`), not the five it recorded before CKD4J. The two-owner overlap is filed as WI-20261102-YX17K (user). The second feedback's "two passes -> Witheq 0" row can no longer be measured: the stdlib-only load is refused, and today's two-step recipe (stdlib sealed, program later) answers Witheq 1.

/code-review run; its findings applied (Eq/NonEq halves pinned, block vs suspend separated, both passes cited, header corrected, field-order requirement stated at `mk_fields`) except the pass overlap (WI-20261102-YX17K). GATE: full workspace 11,512 passed, 0 failed (rustland/scripts/test.sh, shared base).

