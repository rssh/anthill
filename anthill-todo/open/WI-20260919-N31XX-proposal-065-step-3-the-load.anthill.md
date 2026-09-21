## Attributes

- id: WI-20260919-N31XX-proposal-065-step-3-the-load
- created: 2026-09-19T15:19:37Z

- status: Open
- status_agent: user
- status_at: 2026-09-19T15:19:37Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260919-BQHGD-proposal-065-step-1-census-of, WI-20260919-HXGXF-proposal-065-step-2-derive

- tags: typing

## Description

PROPOSAL 065 STEP 3 — THE LOAD RULE AND THE LOWERING: a rigid type read as a value is well-formed only under `requires TypeValue[T = B]`, and it lowers to that slot's `type_value()`. The existing reads are migrated IN THE SAME CHANGE.

THE RULE (065, "The rule"; amends 055 §2's type-parameter bullet). A rigid read in value position with no `requires TypeValue[T = B]` among the requirements in scope is a LOAD error naming the parameter, the read's line and column, and the clause to add. Such a read is a bare `B`, a `B` inside a type expression (`Cell[V = B]`), or a `Type`-slot argument. EXPLICIT, not inferred (user decision, 2026-09-19). Untouched: type positions, concrete sorts, and rule bodies.

THE LOWERING (065 §1). The read becomes `TypeValue[T = B].type_value()` dispatched through the slot, using the ordinary `DeferToRequirement` route. The argument pump already builds `Cell[V = <computed>]`; only the leaf changes. After this, value reads no longer consult the frame type-argument channel. `Error.reify`'s `T1` still does (065 open question 2; 3MV2C decides), so the channel stays and this ticket says at its site why.

THE OVERRIDE SUBSET (065 §3). An implementation's OPERATION-level requires must be a subset of its spec operation's, and a direct call to the member does not relax it. Clauses over the provider's own sort parameters ride on the instance and are allowed. If step 1's probe found this already refused, record which leg enforces it and add a `TypeValue` row. If it loaded, add the leg to `check_override_refinement`.

MIGRATION: every site in step 1's census, in this change, so the suite never passes through a state where the rule is on and a read is unmigrated. That includes the WI-708 rows, the RS2G4 rows (a SORT parameter, so the sort gains `requires TypeValue[T = T]`) and R541X's file. R541X's (D) run-time fault stays as a backstop; say at its site that it is now unreachable from checked source.

ACCEPTANCE:
 - the load refusal DRIVEN with its message;
 - its control: the same program with the clause loads AND answers the ground type through one and two generic levels;
 - the override-subset refusal, and the instance-context control that loads;
 - every migrated row still answering what it answered before.
Each row names the back-out that turns it red. `docs/kernel-language.md`: the R541X paragraph is rewritten to the rule, and 055/065's statuses are updated. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-19T15:35:16Z — feedback — claude

FROM THE BQHGD CENSUS (065 §6), two things this ticket now owns. (1) THE OVERRIDE LEG OVER-REFUSES: check_override_refinement does not align the two operations' TYPE parameters, so a spec 'requires Eq[T = B]' restated verbatim on the override is refused as 'strengthens the precondition' (a ground 'Eq[T = Int64]' restated loads). An implementation must restate 'TypeValue[T = B]' to read B, so align them. Flip wi_bqhgd_override_requires_subset_probe_test::restating_the_specs_type_param_clause_is_refused_today to positive. (2) JUDGE READS AFTER @[simp] EXPANSION: 'dq[K]() = size(put(mkq(K), ...))' with 'rule mkq(?k) <=> Map[K = ?k, V = Int64].empty() @[simp]' passes K as an argument that inlining places in a TYPE position (wi_h054k_type_position_subst_test); judged before expansion it would be refused wrongly. MIGRATION IS FIVE TEST FILES, stdlib/anthill-stl/examples have ZERO sites: rs2g4 (8), r541x (6), wi708 (3), bad3v (1), h054k (1, the simp case, exempt once (2) holds). Every site is the resolved TypeValue form; reduce_var's WI-206 sort arm is unreached by a type-param read from checked source, which bears on whether R541X's (D) guard there stays.

### 2026-09-20T19:38:26Z — feedback — claude

PART 2 OF 3 DELIVERED AND COMMITTED (13482033): the LOAD RULE and the FULL CENSUS MIGRATION. Rust 7223/0, scaland 614 total/0 failed. STILL OPEN AND ALL THAT IS LEFT: the LOWERING (065 §1).

WHAT LANDED. The rule refuses a value-position read of a rigid with no 'requires TypeValue[T = B]' in scope, naming the parameter, the read's line:col and the clause to add. It runs in check_operation_bodies on the tree the typer WROTE BACK, not the one it was handed, because @[simp] fires DURING the node walk — measured by mutation: reading op.body_node instead takes 2 rows red, one of them wi_h054k's own, which is 065 §6's nineteenth site as a real corpus program. Switching the rule on took exactly the four files BQHGD predicted (rs2g4, r541x, wi708, bad3v; 28 rows) and NOT h054k; stdlib/anthill-stl/examples stayed green, so §6's '0 sites' is now confirmed by a refusal rather than by a count. New acceptance file wi_n31xx_type_value_read_rule_test (8 rows), three back-outs each measured on its own.

TWO THINGS THE MIGRATION MEASURED THAT 065 §3 HAD ONLY STATED, both now in kernel-language.md. (a) The §3 table's two halves are ENFORCED: 'requires TypeValue[T = V]' written on Box.valueOfB — an OPERATION-level clause over the provider's own SORT parameter — was refused 'strengthens the precondition' for both Box and CrateTT; the identical evidence on the SORT loads and answers. So a member reading its enclosing sort's parameter carries the clause on the sort, and only one reading its OWN type parameter carries it on the operation. (b) A sort-level clause must be SUPPLIABLE at every call site of its members, which turned R541X's unbracketed SHold.f() from a located run-time fault into a LOAD refusal — the ticket's 'now unreachable from checked source' arriving as a consequence rather than as an edit. (D)'s run-time fault is NOT dead: (C)'s two rows still drive it, since a provider's own parameter through a slot is step 4's (891QP).

ONE GAP PINNED, NOT ACCEPTED. A generic caller that FORWARDS a requirement without declaring it — mid[U](y: U) = tyOf(y) against tyOf[B] requires TypeValue[T = B] — still LOADS, so parametricity is only half enforced. It loads because a value read still goes through the frame type-argument channel, which carries the caller's BINDING rather than a DICTIONARY. Measured and NOT a TypeValue defect: the same shape over a plain user spec loads equally clean, so it is a pre-existing gap in operation-level requirement propagation. The row asserts both halves and flips POSITIVE when the lowering lands.

THE LOWERING'S BLOCKER, IDENTIFIED. type_value() is NULLARY, so a bare B read names no carrier and cannot pick WHICH TypeValue slot to dispatch through when several are in scope (twoReq[P, Q] has two). 065 §8's own spelling type_value[T = B]() is REFUSED today — HXGXF recorded the message — because T is the SORT's parameter and the callee bracket is not wired for that shape although 065 §8 attributes the binding to RS2G4. So part 3 is that binding PLUS the lowering, and it is the piece that also closes the forwarding gap above. The route itself is mapped: a plain Expr::Apply to anthill.reflect.TypeValue.type_value synthesized in the TypeBuildFrame::TypeValue arm reaches defer_to_op_scoped_slot and then start_apply_deferred / expand_dispatching_dict / builtin_dispatch_dict / type_value_of_self, all of which HXGXF already built and drives end to end.

SELF-REVIEW (/code-review high) found four, all fixed before commit, the two that mattered being a named binding unreadable as a TermId falling through to the positional arm (a silent wrong ACCEPT) and the spec's sole parameter name being a "T" literal rather than read off the declaration.

### 2026-09-21T09:14:49Z — feedback — claude

STAYS OPEN. The work is in (five commits, d1d89a14 / a9dca5cd / 8b80344b / 7ae08e01 / 16da9206, plus 8f7ea4ad), the workspace is green (7225/0; scaland 614 total/0), but ONE ACCEPTANCE ITEM IS NOT MET AS WRITTEN and it is the user's to judge, not mine.

'EVERY MIGRATED ROW STILL ANSWERING WHAT IT ANSWERED BEFORE' — FIVE ROWS CHANGED VERDICT.

Three now refuse at LOAD where they answered at run time:
 * wi_r541x .. an_ungrounded_receiver_is_now_refused_at_load — was EvalError::UnboundTypeParam for an unbracketed SHold.f(). SHold must declare requires TypeValue[T = E] for its member to read E, and a call pinning nothing cannot supply it.
 * wi_r541x .. two_clauses_over_one_spec_are_refused_at_load — was UnboundTypeParam. twoReq[P, Q] requires TypeTerm at both P and Q, so nothing picks which clause TypeTerm.valueOf() runs under and the evidence cannot be built.
 * wi_rs2g4 .. a_bracket_value_with_an_unwritten_slot_is_refused_where_it_is_read — was ANSWERING Box(T: List(T: ?var)). A bare [U = List] expands to List[T = ?T] (RS2G4) and the conditional derived instance wants TypeValue[T = ?T] for a ?T nothing pins.

Two now ANSWER where they faulted — 065 §4 / WI-20260919-891QP arriving:
 * wi_r541x .. a_providers_own_param_answers_through_its_instance — Box(V: Boom), was UnboundTypeParam.
 * wi_r541x .. a_witnesss_own_param_answers_through_its_instance — Crate(W: Boom), was UnboundTypeParam.

THE ARGUMENT FOR ACCEPTING THEM is 065's own: 'R541X made the unreachable cases loud; this proposal makes them UNWRITABLE'. Each of the three refusals is a program that was always ill-formed and is now reported where the author can act on it; the two flips are the step the proposal predicted. No migrated row LOST a capability. Each is documented at its site with what changed and the back-out that restores the old verdict.

THE ARGUMENT AGAINST is that the acceptance says what it says, and three programs that used to load now do not — a surface change to what the language admits, which is a decision and not a test detail.

NOTHING ELSE IS OUTSTANDING: the load rule (both the READ and the FORWARD half), the lowering for OP-level and SORT-level clauses, the census migration across five files, the §3 subset rows, kernel-language.md's R541X paragraph, and 055/065's statuses are all in. 891QP is closed by this and should be marked so once this is.

SPUN OFF, neither blocking: WI-20260920-XSVCS (the general requirement-propagation gap this narrowly closed only for TypeValue) and WI-20260921-28TAT (remove the frame type-argument channel, now down to one reader).

