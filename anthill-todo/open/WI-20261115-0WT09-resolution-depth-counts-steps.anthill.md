## Attributes

- id: WI-20261115-0WT09-resolution-depth-counts-steps
- created: 2026-11-15T17:37:18Z

- status: Open
- status_agent: claude
- status_at: 2026-11-15T17:37:18Z

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

