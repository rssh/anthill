## Attributes

- id: WI-20260827-2YHZ3-a-rule-body-can-test-an
- created: 2026-08-27T09:30:21Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T13:32:16Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN ANSWER BINDING IS READ ONE HOP AND SILENTLY TRUNCATES — so a rule-head variable bound
by a rule-body BUILTIN reads back as UNBOUND, and `anthill query` prints `?_` for an
answer the resolver got right.

RE-AIMED 2026-08-27, from "a rule body can TEST an operation's result but cannot BIND
it". That reading was an artifact of the READER; the original table is reproduced below
with what each of its rows actually measures. The id keeps its original slug tail — ids
are never renumbered.

THE MECHANISM. `resolve.rs:479` states an invariant that is FALSE: "The substitution is
always flat (path-compressed) — read a binding via `subst.resolve_as_value(vid)`
directly, no `walk` needed." Two bind paths, only one of which keeps it:

  * A FACT match binds through `bind_compressed` (resolve.rs:3146), which RE-POINTS the
    existing answer link `?a -> Var(F)` to the value. One hop then suffices.
  * A BUILTIN binds through `bind_waking` on the `SuccessWithBindings` merge
    (resolve.rs:1406). No compression, so `?a -> Var(F)` and `F -> 6` BOTH stand and a
    one-hop `resolve_as_value(?a)` stops at `Var(F)`, which renders `?_`.

The codebase already knows the true invariant and says so in the opposite place:
`reify_value` (kb/mod.rs:6381) — "recursively, so a `z -> w -> ...` chain collapses EVEN
WHEN sigma IS NOT PATH-COMPRESSED" — and `reify`'s own doc says "Read an answer binding
with this". `extent.rs:1850`'s `read_facts_resolved` does. THREE READERS DO NOT:

    anthill-cli/src/main.rs:2326        the `?x = ...` answer line
    anthill-core/src/eval/mod.rs:1970   a relation row's column drain
    anthill-cpp-gen/src/lib.rs:5424     the effect-receiver read

MINIMAL REPRODUCTION — no operation in it at all:

    rule k_u6(?x) :- ?x <=> 6
      k_u6(?a) -> `?a = ?_`   BUT   k_u6(6) -> true,  k_u6(7) -> no solutions
    rule m6(?x, ?y) :- ?x <=> 6, B(v: ?y)
      m6(?a, ?b) -> `?a = ?_, ?b = 6`      both halves of ONE solution

Resolution is right in every case; only the projection is lost. A CALLING RULE sees the
binding fine — `k_u6(?a), ?a = 6` -> 1 and `k_u6(?a), ?a = 7` -> 0 — which is why this
never showed up as a wrong proof, only as a wrong ANSWER.

WHAT THE ORIGINAL TABLE ACTUALLY MEASURED. Re-run with the CLI reader reifying
(`kb.reify_value(&binding, &sol.subst)`), same tree, same probe file:

    form in a rule body                    bodied            host
    f(3) = 6      test against a value     1                 1
    f(3) <=> 6    unify against a value    1                 —
    f(3) <=> ?r   unify into a free var    1, ?r = 6         1, ?r = some(value: 7)
    f(3, ?r)      relational view          1, ?r = 6         0 solutions

So `<=>` DOES bind, and binds the REDUCED VALUE, not the call term. The ticket's
"dangerous downstream flow" was a CORRECT answer: `twice(3) <=> ?r, Int64.gt(?r, 5)`
answers 1 because `?r` IS 6, and `Int64.gt(?r, 99)` answers 0. There is no soundness gap
at that coordinate, and nothing here is one coordinate over from WI-880.

TWO NEIGHBOURS ARE CORRECTED BY THE SAME FINDING, neither needing its own work:

  * proposal library/008 open question 1 — "why does the arity-2 `extract_sort_ref` goal
    succeed without binding?" IT DOES BIND. With the reader fixed,
    `SortProvidesInfo(sort_ref: ?c, spec: ?v), extract_sort_ref(?v, ?s)` answers
    `?s = PartialEq / Eq / FiniteCollection / Iterable / Monad / Stream`. So 008's FIRST
    CONSUMER — `guardians/lib/safety.anthill` tier 1 — is writable today, and 008 §2(a)
    plus the library README row must stop saying otherwise.
  * WI-20260822-F0HHB's "`<=>` binds the SYNTAX" row. `?r <=> Bool.and(?a, ?b)` answers
    `?r = false`, and `uni(false)` answers true. F0HHB's LIVE half is `=`, which still
    suspends honestly (`residual: eq(?_, and(true, false))`) — that `?_` is not a lie
    and F0HHB keeps it.

WHAT SURVIVES IS ONE CELL, AND IT IS ALREADY OWNED. `term_as_int(7, ?r)` — a host-mapped
op's arity+1 relational view — answers 0 SOLUTIONS rather than delaying. That is WI-938's
recorded surviving follow-up ("a call whose args are NOT ground falls through silently (0
solutions) rather than DELAYING"); the gate is `dispatched_relation_arity`
(resolve.rs:1613). NOT this ticket. For the record, the full matrix, which nothing states
today:

    op kind                        f(a) <=> ?r                   f(a, ?r)
    bodied (twice)                 ok, 6                         ok, 6
    host-mapped (term_as_int)      ok, some(7)                   0 solutions
    resolver builtin (Int64.add)   residual unify(add(1,2), ?_)  ok, 3

TWO WAYS TO FIX IT, and the ticket recommends the first:

 (a) FIX THE READERS. Deep-reify at the three sites above, as `read_facts_resolved`
     already does. Local, off every hot path, and it makes the one existing correct
     reader the only spelling. `Solution`'s doc comment then has to stop claiming
     flatness and state which bind path compresses and which does not.
 (b) RESTORE THE INVARIANT AT THE BIND. Path-compress on the `SuccessWithBindings` merge.
     SCALAND ALREADY DOES THIS — `SearchStream.scala:181` routes that merge through
     `bindCompressed`, whose doc says "Keeps the substitution always flat" — so it is a
     live design, not a hypothetical. The cost is an O(n) scan per builtin binding on a
     hot path, and rust's own answer-link note (resolve.rs:14065) records keeping
     synthetic entries OUT of sigma specifically "to avoid O(n^2) `bind_compressed`".
     It also cannot simply swap the call: `bind_waking` is there for WI-502 constraint
     wakeup and WI-1017's occurs-check, and `bind_compressed` loud-asserts on a
     constrained var.

ACCEPTANCE: the three readers named above read an answer binding by DEEP REIFICATION
(`reify` / `reify_value`), not a one-hop `resolve_as_value` — or, under (b), the merge
compresses and the readers are left alone; `Solution`'s doc comment no longer claims the
substitution is always flat and names the two bind paths; a test DRIVES `rule k_u6(?x) :-
?x <=> 6` through the fixed reader and asserts `?x = 6` — the VALUE, since the solution
COUNT is 1 both before and after and a `.len()` assertion measures nothing here; a NESTED
case (`?x <=> B(v: ?y), ?y <=> 6` -> `B(v: 6)`) is driven too, since a top-level chase
alone does not fix it; the relation-column drain (eval/mod.rs:1970) is driven with a
column bound by a builtin; and scaland's own answer for `rule k_u6(?x) :- ?x <=> 6` is
MEASURED rather than assumed from the `bindCompressed` call — if it already answers 6 it
is the cross-implementation control and the test pins it, and if it does not, it has the
same defect and gets the same fix.
CONTROLS THAT MUST STAY GREEN and pass either way BY DESIGN: every fact-bound answer
(`rule k_fact(?x) :- B(v: ?x)` -> 6, which path-compresses and never truncated); the
ground-query rows (`k_u6(6)` -> true, `k_u6(7)` -> no solutions), which decided correctly
throughout; and the HONEST unbound display — `?r = <expr>` under `=` must still show `?_`
WITH its residual, because there `?_` is the truth. Say at each site which rows fail on a
back-out. Full workspace green via rustland/scripts/test.sh.

ALSO SEEN, NOT THIS TICKET: `nonvar(?r)` on a HEAD variable behaves differently from
`nonvar` on a body-local one — `twice(3) <=> ?r, nonvar(?r)` residualizes the whole rule
when `?r` is in the head and answers 1 cleanly when it is not, and the arity+1 spelling
FAILS outright. That is the caller-var delay pre-check
(`body_builtins_delay_on_caller_vars_nodes`, resolve.rs:3263) firing conservatively; it
is unchanged by either fix above and was measured on both sides of the experiment.

## Changes

### 2026-08-27T10:06:02Z — feedback — claude

RE-AIMED 2026-08-27 at the user's direction, after the original reading failed re-measurement.

WHAT THE ORIGINAL TICKET GOT WRONG, so it is not re-derived. Its whole table — `f(3) <=> ?r` and `f(3, ?r)` leaving `?r` unbound, and `twice(3) <=> ?r, Int64.gt(?r, 5)` answering 1 DEFINITE on an unbound `?r` — was read off `anthill query`'s answer line, which truncates a var chain at one hop. Both spellings BIND, the downstream row is a correct answer over a bound 6, and `Int64.gt(?r, 99)` answers 0. So there was no succeed-with-unbound and no soundness gap: `no rule can COMPUTE anything` was false.

HOW THE MEASUREMENT SEPARATED THEM, since the two look identical from a solution count. A genuinely free var yields a CONDITIONAL with a residual (`c_gt99(1) :- Int64.gt(?r, 99)` -> `residual: gt(?_, 99)`); the ticket's rows yielded CLEAN definite solutions, so something was bound. Ground queries decide correctly either way (`k_u6(6)` -> true, `k_u6(7)` -> no solutions), and a calling rule sees the binding (`k_u6(?a), ?a = 6` -> 1, `?a = 7` -> 0) — three independent probes agreeing that only the projection was lost.

THE FIX WAS BUILT AND MEASURED, not inferred: `print_solutions` reifying via `kb.reify_value` collapses every row of the table and leaves anthill-cli green (14 + 163 passed, 0 failed). It is NOT committed — the ticket carries the acceptance, including the (a)/(b) fork and whether scaland (whose builtin merge already routes through `bindCompressed`) has the defect at all.

The original description is preserved in git history at da3bb60a.

### 2026-08-27T13:32:05Z — feedback — claude

DELIVERED. `KnowledgeBase::answer_binding` is the one correct answer read (one hop, then `reify_value`); four readers route through it — the CLI answer line, the eval relation-column drain, cpp-gen's effect receiver, and the reflect `Substitution.lookup` bridge. `Solution`'s doc no longer claims flatness and names both bind paths. Green: rustland 36 binaries / 0 failed via scripts/test.sh; scaland 520 / 0.

THE TICKET'S FIX WAS NOT SUFFICIENT, and review caught it. `answer_binding` alone resolved a chain of length <=2. `subst_var_leaf`'s `Value::Node` arm (node_occurrence.rs) SPLICED a bound occurrence in without re-substituting it, so applying sigma stopped after one Node->Node hop: `?x <=> ?y, ?y <=> ?z, ?z <=> 6` handed back `Var(?z)`. Every test written to the ticket's own examples has a chain of length one and passed straight over it. The `Value::Term` arm never had the gap (`apply_subst` is already a deep walk), so this was the ONE carrier where "apply sigma" did not mean what it says — and that asymmetry is what hid it.

SCOPE WIDENED KNOWINGLY: `subst_var_leaf` is shared resolver machinery (`substitute_occurrence` is on the body-rename and goal-substitution paths), not a reader. Fixed there rather than worked around in `answer_binding`, because the claim it breaks is the function's own. Termination rests on sigma's acyclicity — enforced at every bind site that can write one of these (`unify_bind`, the WI-1017 merge, the WI-649 non-Term fact bind) — plus the degenerate self-binding guard `reify_value`/`walk_view`/`occurs_in_value` each carry. Identity survives: `substitute_occurrence` returns `Rc::clone(occ)` unchanged, which `value_fact_full_resolver_search_binds_node_as_value` pins by `Rc::ptr_eq`.

SCALAND IS THE CONTROL, and the first version of that claim was worth less than it looked. `bindCompressed` re-points only `this.bindings` while `resolve` walks `parent`, so a one-shape test proved only the same-frame case while its failure message claimed the general one. Now drives a second shape whose link is written a frame above the bind. Both pass — scaland does not have this defect.

DELIBERATELY NOT DONE, both recorded at their sites rather than left silent: (1) `Substitution.lookup`'s NAME scan is still this-level-only, so a name held only in a parent frame is not FOUND — a separate pre-existing gap in a by-name lookup whose doc already records that it resolves loosely, and widening it changes which binding anthill-todo's `pattern_query` finds. (2) The eval drain's Node->term lowering is UNCONDITIONAL, so a reflect `Term`/`Type` column loses occurrence span/identity; the alternative puts the column's shape in charge of the carrier, which is the split WI-348 removed. Left as-is because the failure it prevents is reachable from a two-line rule and the one it admits has no constructed case.

ALSO CORRECTED: proposal library/008 (SS2(a), SS2(c), open question 1, Design A, First consumer) and the library README row — 008's first consumer, guardians tier 1, now both resolves AND displays.

### 2026-08-27T18:47:13Z — feedback — claude

FINAL SHAPE, after the delivery record above — the fix went one level deeper than 'four readers'.

CARRIER-NEUTRAL ACCESSORS ON THE INTERFACE, not a normalization helper. `TermView` gained `as_literal` plus `literal_bool` / `literal_int64` / `literal_f64` / `literal_big_int` / `literal_string`. The key fact that makes them total: a NATIVE scalar already answers `ViewHead::Const` (`Value::Bool(b)` -> `Const(Literal::Bool(b))`), exactly as a `Term::Const` and an `Expr::Const` occurrence do — so one accessor covers every carrier with no native fast path and no conversion step ahead of the guard.

TWO MISSING ARMS FIXED, measured by REMOVING the drain's conversion and seeing what broke:
  * `reflect_field_access` matched `Value::Entity` alone; it reads functor / named / positional through `TermView` now. That REMOVED a case — Entity, Term and Node all view as `ViewHead::Functor`, so one arm replaces three.
  * 21 binary scalar builtins guarded on the native variant alone. Each now reads its operands through the accessor, and the read IS the guard — no separate normalize line for a later author to forget. The first failure was `"Int64 and Term"` on the FACT-backed control, so this was never a Node gap: the numeric surface could read neither handle.

THE DRAIN KEEPS ITS CONVERSION, and that is a measured decision, not an omission. Removing it failed 76 TESTS across wi730/wi731/wi733/wi741/wi_yqb1y/wi_7x7nk/wi_9c2pz/wi751 — a relation row is read far past the builtins, by Rust-side readers and assertions matching `Value::Str`/`Value::Int` directly. And `materialize_solution`'s own doc STATES the contract those assert ('a `Relation[String]` yields `Value::Str`', WI-714), so removing it is a CONTRACT change, not a refactor. Filed as WI-20260827-3ZNBC with the failure list and that framing.

NAMING TRAP, recorded: `Value` has INHERENT `as_bool`/`as_int`/`as_str` reading the native variant only, and an inherent method WINS over a trait method — so a trait `as_bool` would silently resolve to the carrier-blind one at every `Value` call site. Hence `literal_*`.

GREEN on the final tree: rustland 36 binaries / 0 failed (wi_tests 3618 passed), scaland 520 / 0.

PROCESS NOTE for whoever reads the logs: `target/test-run-latest.log` is a SYMLINK, and `scripts/test.sh` REFUSES to start while another run is in flight. A run launched into a refusal leaves the symlink pointing at the previous run's log, which reads as a completed result for a tree that no longer exists. Pin the dated log path when watching a run.

### 2026-08-27T22:27:30Z — feedback — claude

/code-review (high) run on the final tree; seven findings, all resolved. Green after: rustland 36 binaries / 0 failed (wi_tests 3618), scaland 520 / 0.

FIXED FROM THE REVIEW:
 * `materialize_entity` collected positional children with `filter_map`, so a slot below the arity that did not read back would SLIDE every later argument down one and materialize it into the WRONG declared field — a silently wrong entity, not an error. Now a `?` refusal (repo rule: loud over silent).
 * `subst_var_leaf`'s recursion termination was ARGUED, not structural. My guard covered only the degenerate `vid -> Var(vid)`; a two-cycle or `x -> Node(f(… Var x …))` would recurse forever, and the cost is a STACK OVERFLOW on the resolver's per-step goal walk, not a wrong answer. The guard is now the occurs-check itself — if the bound occurrence mentions `vid` anywhere, splice raw as before — which covers self-binding, two-cycle and nested cycle with one question, the same one the bind sites ask.
 * THE CARRIER-NEUTRAL SET IS CLOSED, which was the review's substantive half. `int_neg`, `int_abs`, `bool_not`, `value_compare` (backing compare/gt/gte/lt/lte/max/min) and `str_operand` (15 call sites) now read through the view alongside the original 21 wrappers. The inconsistency the review named — `Int64.add(handle, 1)` succeeding while `Int64.gt(handle, 1)` refused — was an artifact of a half-done set.
 * `str_operand` returns `Cow<'a, str>`, so a native `Value::Str` still BORROWS: a filter over a long stream allocates nothing new, and only a handle carrier (previously unreadable) pays a clone. That answers the review's allocation concern about `as_literal` cloning, at the surface where it mattered.

A REVIEW FINDING I ACTED ON WRONGLY FIRST, recorded because the reasoning error is worth more than the fix. The review said the widening was an arbitrary subset with no driving test; I backed the whole thing out and cited CLAUDE.md's 'a test for a capability must DRIVE the capability' as forbidding it. THE USER CORRECTED BOTH HALVES: that rule governs what a TEST must do and is not a prohibition on code, and reading an operand through `TermView::literal_int64` rather than matching `Value::Int` is not a new capability at all — it is the existing question asked correctly, strictly widening what is accepted with no change for previously-accepted inputs, already covered by the arithmetic/string/comparison suites. Restored, and the set closed instead. The lesson: 'the set is incomplete' argues for COMPLETING it, not for reverting it, and dressing a judgement call as a cited rule hides that the call was mine.

