## Attributes

- id: WI-20261115-0WT09-resolution-depth-counts-steps
- created: 2026-11-15T17:37:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-16T00:20:49Z

- acceptance: cargo-test, scaland-sbt-test

## Description

RESOLUTION DEPTH COUNTS STEPS, NOT DEPTH: `--max-depth` (`ResolveConfig::max_depth`, default 100) bounds the number of resolution steps taken on one branch, so the goals of a conjunction add up and a long finite computation is cut as an infinite one is. Decided with the user on WI-20261115-YR3N7 (2026-11-15): "Depth is depth. If we need step-count (like fuel), then better have other counter for this".

WHERE. One counter per frame, shared by all its goals, and every step adds 1 to it: a clause opened (`kb/resolve.rs`, the clause-expansion arm, `f.depth = depth + 1`), a builtin that succeeds, `true`, a cut, and a delayed goal moved behind the tail (`rotate_first`); `step_init` compares the total with `max_depth`. Scaland counts the same way (`resolve/SearchStream.scala`: the check at the frame's Init, `frame.depth = depth + 1` on each step). The spec says only "depth limit" (§5.2's `search_truncated`), `ResolveConfig` "resolution depth".

MEASURED on the rustland CLI of 2026-11-14 (the smallest `--max-depth` that answers, by bisection; the probes are YR3N7's):
  1 YR3N7's `q_full` needs 107, and its parts add: the untyped query 6, the check of `?s: S` about 87, the check of `?o: Order` about 14.
  2 A typed column over `S(products: [p1, …, pn], orders: [])`: 75, 91, 123, 187 for n = 1, 2, 4, 8 — 16 more per element, every element's steps added to the branch.
  3 The same holds for any conjunction: a goal's steps are charged to every goal after it on the branch, so a long body that terminates is truncated at the same budget an infinite descent is.

PROPOSED.
- DEPTH IS NESTING. Each goal carries its own depth. A goal at depth d resolved with a clause puts that clause's body goals at d + 1; the goals beside it keep their own. A goal that becomes a CALL to something else is d + 1 too: a metacall, a call evaluated in an argument, a `not` / `forall` sub-search. These cost nothing: splitting `,` and `|` (and the generated `push_and` / `push_choice`), a builtin that succeeds, a dispatch that lowers a goal to one call of a relation (`apply_domain`), and a delayed goal moved behind the tail. A goal deeper than `max_depth` is not asked, and the search is truncated, as now. Depth alone still stops every infinite derivation: a step opens finitely many goals, so an infinite derivation holds an infinitely deep chain of calls, and the steps that cost nothing cannot repeat for ever (a split breaks up a finite term; the rotation gate caps the moves).
- FUEL IS A SEPARATE COUNTER: the steps of the WHOLE search, across branches, with its own limit (`max_steps`, a `--max-steps` flag; the default set by measuring the suite) and its own verdict — `search_truncated` names the limit that was reached. It is needed because counting steps was also the only bound on work: at depth as nesting, a finite search of small depth can run exponentially long (a rule that calls itself twice per level) where the step count cut it at 100.
- Both carriers, and the spec defines both limits (kernel-language §5.2, `ResolveConfig`'s docs, the CLI's `--max-depth` help).

ACCEPTANCE (both carriers; every row driven, with the depth it needs measured as the probes above do):
  1 Siblings no longer add: a typed column over `S(products: [p1, …, pn], orders: [q1, …, qm])` needs the depth of its deepest part, not the sum — for n = 8 the same depth with m = 0 and with m = 8; row 2's 16-per-element growth is gone from the depth (it stays in the fuel).
  2 A left-recursive rule (`p :- p`) and an infinite descent (`nat(s(?x)) :- nat(?x)` called with `?x` free) are still cut by depth, truncated, never refuted.
  3 A rule that calls itself twice per level, called at a depth well under the limit, is cut by FUEL, and the verdict names fuel.
  4 Every test that sets a small `max_depth` (1, 5, 7, 8, 20 in the suites; `wi_p9qbf_lazy_truncation_test`, `forall_impl_resolve_test`, `wi767_query_resolve_default_test`) re-read for what it measures, and moved to the counter it means.
Back-out: the per-goal depth reverted to the frame's counter reddens row 1.

## Changes

### 2026-11-16T00:20:45Z — feedback — claude

BUILT (claude, 2026-11-16), decided with the user: the verdict is ONE entity naming its limit — `search_truncated(limit: SearchLimit)`, `SearchLimit = depth(max_depth: Int64) | steps(max_steps: Int64)` (`anthill.reflect`) — and the fuel's default was measured before it was chosen.

DEPTH IS NESTING. Each goal carries its own depth (`FrameGoal::depth`; scaland's `FrameGoal`), and the frame has none. A clause body is one deeper than the goal the clause answered; a quantifier's instances (`forall_in`, `some_in`, `forall_impl`'s consequents) and an unfolded operation's arms (`Nesting::Opened`) one deeper too. Everything else keeps its depth: a choice's or a conjunction's operands (`Nesting::Split`, `continue_with_goals`), a builtin's spliced goals, a lowered goal (`apply_domain`), a rotation, a wake. A negation's sub-search runs on what is left of the depth below its goal, as before.

FUEL. `ResolveConfig::max_steps` (`DEFAULT_MAX_STEPS`), checked in `SearchStream::step`; out of it every branch is abandoned (`run_out_of_fuel`), `truncated` and `out_of_fuel` set, and the end names `SearchLimit::Steps`. A negation's sub-search runs on the REMAINING fuel and is charged back (`charge_sub_search`); out of fuel there, the outer search stops too, its sub-search's faults folded in first. A carrier `eq`'s closed sub-proof keeps budgets of its own — its fuel is its old step budget, `DEFAULT_SEM_EQ_SUB_DEPTH` (100 000), so a divergent carrier `eq` costs a comparison what it did — and so does a search an operation body runs through the bridge; such a search cut below another reads there as `depth`, whichever of its own limits cut it (stated in `SearchFailure`, `reflect.anthill`, kernel-language §8.3). `ResolveStats::out_of_fuel`; the CLI's `--max-steps` (refused under `--match` and the listing modes, with `--max-depth`, in one check) and its note "search stopped at --max-steps". Scaland: `ResolveConfig.maxSteps`, `ResolveStats.truncated` / `.outOfFuel` (it had no truncation flag), and its `not(P)` over a sub-search cut at its depth is UNDECIDED now — it residualized nothing before and succeeded (`/code-review`).

SPEC: kernel-language §8.3 "A search has two limits, its depth and its fuel"; §5.2's bridge paragraph and §5.3's domain text point to it; `reflect.anthill`'s `ResolveStreamFailure` comment, `relation.anthill`'s drain notes, `ResolveConfig`'s docs, the CLI help.

MEASURED — the fuel's default. A temporary census (one line per search crossing 10^5, 10^6, 10^7, 10^8 steps; a probe confirmed it fires: `tree(s^18(z))` logged 10^5 and 10^6) over the whole workspace's suites (12 180 tests) and over this repository's own ticket store (about 1 770 items; list, list --unblocked, status, next, show, dependents, graph) logged NOTHING: no search took 100 000 steps. DEFAULT CHOSEN: 10 000 000, over a hundred times the largest, because a PROGRAM cannot raise it — the relations an operation body drains and its `execute` calls run at the default; only the CLI and a Rust caller set another. About 5 µs a step (optimized, loaded machine): a runaway search stops in under a minute.

MOVED BY DESIGN: `wi767_query_resolve_default_test::depth_truncated_search_is_flagged_undecided` — `--max-depth 1` reaches `loc`'s body now (one deeper than the query) and answers "a"; the row asks `--max-depth 0`. Nothing else in the workspace moved.

/code-review high: 9 findings, 8 fixed, 1 skipped. FIXED: the negation's stop on fuel before its faults were folded (row `a_negation_out_of_fuel_keeps_its_fault`, back-out [E]); scaland's `not(P)` over a cut search (row "a negation over a cut search is undecided", [T]); the carrier `eq`'s fuel (no row: it changes a cost, not a verdict — under either budget the comparison is undecided); the `max_steps` doc; the limit's name for a search with budgets of its own (the docs narrowed to what is built); p9qbf's forged payload made well-formed; a public doc linking a private field; the CLI's two refusals folded. SKIPPED: a rotation cycle that keeps resetting the delay count is no longer cut by depth — by design, work without depth is the fuel's, and it ends as `steps(max_steps)`; the census found no search in the suites near 10^5 steps, so none holds such a cycle.

ROWS: `wi_0wt09_depth_is_nesting_test` (7), `wi_0wt09_max_steps_test` (3, anthill-cli), `DepthIsNestingTest` (4, scaland); `wi_p9qbf_lazy_truncation_test` reads the payload's nested limit. BACK-OUTS, measured on the final tree and recorded at the rows' sites: core (17 rows with p9qbf) [D] depth counting steps, emulated — 6, [F] no fuel check — 3, [C] the negation not charged back — 2, [E] the stop before the fold — 1; CLI (12 rows with wi767) [N] the note's fuel arm — 1, [R] the refusal — 1; scaland (4 rows) [D] 2, [F] 1, [T] 1.

GATE: 12 181 passed / 0 failed / 17 ignored (the previous 12 171 and the 10 new rows); scaland testFull 1 + 51 + 804 = 856.

FOR WI-20261115-YR3N7: with depth counting nesting its row 1 already answers at the default depth (`a_typed_columns_check_is_as_deep_as_its_value`: a state of eight products fits it). What YR3N7 still owns is the COST: the check generating instead of checking — 16 steps per list element against 6 — and the case left untried behind each piece.

