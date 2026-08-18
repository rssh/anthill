```anthill
fact WorkItem(id: "WI-20260818-7X7NK-a-projection-over-a-1", created: "2026-08-18T19:15:24Z", context: none, acceptance: [ToolPasses(tool: "cargo-test", params: none), ToolPasses(tool: "scaland-sbt-test", params: none)], depends_on: some(value: nil), generates: none, requires_capability: none, status: Delivered(agent: "claude", at: "2026-08-18T23:26:08Z"))

fact Feedback(workitem: "WI-20260818-7X7NK-a-projection-over-a-1", author: "claude", at: "2026-08-18T20:54:04Z")

fact Feedback(workitem: "WI-20260818-7X7NK-a-projection-over-a-1", author: "user", at: "2026-08-18T23:26:03Z")
```

## description

A projection over a 1-collapsed relation is refused by DOT DISPATCH, so the message names the wrong thing. Filed out of WI-1128 (delivered 2026-08-18), which measured it, wrote the reason at the site, and left it unowned.

MEASURED: `ages.(age)` on `rule ages(?age) :- person(age: ?age)` (schema 1-collapses to `Int64`) fails with "type mismatch in anthill.prelude.Relation.age: expected operation declared on the receiver's sort, got no such member (dot dispatch)". The author wrote a PROJECTION and is told their relation has no MEMBER called `age` — a true sentence about a question they did not ask.

WHY: kernel-language.md 6.8's single-member 1-collapse desugars `r.(f)` to `r.f` at CONVERT time, before any type exists. So a one-column receiver never builds a projection node at all: `projection_columns` (rustland/anthill-core/src/kb/typing.rs) declines because the schema is not a named tuple, the caller falls through to ordinary dot dispatch, and dot dispatch reports what it sees. `projection_columns`' own message — which WI-1128 rewrote to name the collapse and say "a one-column relation already IS that column: the projection would be the identity" — is therefore reachable ONLY from a WRITTEN `Project[T, Keep]`.

WHY IT WAS NOT FIXED INLINE: the fallthrough is load-bearing. `r.(f)` and a genuine member call `r.isEmpty` are the SAME node after the desugar, so making the decline loud would break every single-member dot call on a relation. A fix has to distinguish them, and the only signal available is the receiver's sort plus the failure — i.e. a Relation-keyed arm at the dot-dispatch failure site. That is not obviously the right shape (the typer's standing discipline is that nothing keys on an operation's identity; keying a DIAGNOSTIC on a receiver SORT is a weaker version of the same smell) and it deserves its own decision rather than being smuggled in under a ticket about `join`.

TWO CANDIDATE SHAPES, neither chosen: (a) at the dot-dispatch no-such-member site, if the receiver is a `Relation` whose schema is not a named tuple, say so and name the collapse; (b) keep a marker on the convert-time desugar recording that the node CAME FROM a `.( )` form, so the failure can report the surface the author actually wrote — more faithful, and it would also improve the multi-member case, at the cost of a node-level flag.

NOTE THE INTERACTION: if WI-20260818-YQB1Y (the 052 OQ5 split) lands, a one-column relation stops having a collapsed schema and this diagnostic becomes unreachable through THAT route — but not through a genuinely mistyped column name, which is the common case and is what shape (b) would serve. So this is not automatically closed by that ticket; check before starting.

ACCEPTANCE: `ages.(age)` reports a message naming the projection and the collapse rather than dot dispatch's "no such member", OR the shape question is decided and the current behaviour is recorded as intended with the decision at the site; `r.isEmpty` and every existing single-member dot call on a relation still work (the fallthrough is not broken — drive one, do not assert only that it loads); existing wi639 / wi732 projection tests green; cargo-test green via scripts/test.sh.

## Feedback

### 2026-08-18T20:54:04Z — claude

RE-CHECKED AFTER WI-20260818-YQB1Y LANDED (052 OQ5 option A, the 1-collapse dropped), because this ticket asked for exactly that ("check before starting"). VERDICT: STILL OPEN, and the route is unchanged.

MEASURED on the post-YQB1Y tree, both receiver arities:
  * `adults.(nosuch)` over a ONE-column relation `rule adults(?who) :- person(name: ?who, age: 30)`
  * `person_row.(nosuch)` over a TWO-column relation
Both report: "type mismatch in anthill.prelude.Relation.nosuch: expected operation declared on the receiver's sort, got no such member (dot dispatch)". Identical text, identical route.

WHAT CHANGED, AND WHY IT DOES NOT CLOSE THIS. The ticket's own mechanism paragraph is now stale in its FIRST clause and still correct in its second. `r.(f)` no longer 1-collapses at convert time — it builds the marked one-field tuple `(f: r.f)` at every arity — so a one-column receiver DOES build a projection node now, and `ages.(age)` runs (driven by `wi_yqb1y_one_column_relation_test::yqb1y_a_one_member_projection_keeps_its_key`, which uses the rename form). The example the ticket was FILED with therefore works. But the failure route for a MISTYPED column is untouched: `relation_column_access_parts` still returns None when the member does not resolve, the recognizer still declines, and the call still falls through to ordinary dot dispatch. That fallthrough is still load-bearing for the same reason (`r.isEmpty` is the same node shape after the desugar), so shape (a) vs (b) is still a real decision.

WHAT THIS MEANS FOR THE TICKET'S SCOPE: the "1-collapsed receiver" framing is gone — there is no collapsed schema left to name — so `projection_columns`' collapse-naming message is now dead prose rather than an unreachable-but-correct one, and the remaining defect is narrower and more ordinary: a projection naming a column that does not exist is reported as a MEMBER lookup. That makes shape (b) (carry the `.( )` provenance to the failure site) the only one of the two candidates that still describes a fix — shape (a) keyed on "a Relation whose schema is not a named tuple" no longer has a population, since a relation schema is ALWAYS a named tuple or `Unit` now. Worth restating the acceptance before starting.

NOT PINNED BY A TEST, deliberately: a test asserting today's dot-dispatch message would pass both before and after YQB1Y and so measures nothing about it. The measurement is recorded in the header of `wi_yqb1y_one_column_relation_test` instead, with the two spellings above.

### 2026-08-18T23:26:03Z — user

DELIVERED as shape (b) — carry the `.( )` provenance to the failure site — and the marker it was
costed with turned out to be FREE: WI-762 already marks the desugared tuple
(`Expr::Constructor::from_projection`), and the fields hang off it, so nothing new rides on a node.
Shape (a) was not chosen and could not be: as the re-check said, "a Relation whose schema is not a
named tuple" has had no population since YQB1Y.

WHERE THE SHORT-CIRCUIT ACTUALLY IS, which the ticket's mechanism paragraph did not name. It is NOT
`check_constructor_iter`'s `collect_arg_errors` — a marked projection with a failing field never
reaches that function at all. `TypeBuildFrame::Constructor` (kb/typing.rs) runs its OWN
`collect_arg_errors` before `reassemble_children`, and returns there. The new
`projection_names_no_column_error` is called immediately ahead of it. I looked in the wrong place
first (an instrumented `eprintln!` on every ctor visit showed the marked tuple never arriving), so
recording it here.

THE FIX, three gates in order: the surface-form MARK (grammar-owned, the same key
`try_relation_projection_tuple` already uses for its typing decision); the field's failure being
`DotDispatchNoMatch` FOR THAT MEMBER; and the receiver's sort being `Relation` — the SAME gate
`build_relation_projection` uses to decide projection-vs-tuple, not a new one. So the smell the
ticket flagged ("keying a DIAGNOSTIC on a receiver SORT") is not a new key at all, and it is not the
one the standing discipline is about: an op identity is an OPEN set the stdlib owns, `Relation` is
one kernel sort. Nothing here keys on a Relation OPERATION. The message is `projection_columns`'
OWN — the shared decision procedure, so "this names no column" cannot drift from the acceptance and
schema-derivation directions.

THREE DEFECTS I SHIPPED AND REVIEW CAUGHT, all with ONE blind spot: every arm I wrote names a member
that exists NOWHERE, so all of them agreed with a reading that is right only for that case.
  * The first cut fired on ANY failing field and then asserted something FALSE. Measured:
    `person_row.(takeN)` fails because `Stream.takeN` wants its `n` argument — the member IS
    reachable — and it was reported as "no member `takeN` is reachable on it either", destroying the
    arity error that said what to do. "The field failed" is not "the member does not exist". The same
    hijack covered requirement refusals, effect mismatches, and — sharpest —
    `TypeErrorContext::DotProjection`'s OWN first population (WI-759: the member resolves but its
    type does not), the context this diagnostic shares.
  * Then, having gated on the variant, it asked only the FIRST FAILING FIELD — so
    `r.(takeN, nosuch)` fell through entirely and reported `nosuch` through dot dispatch AGAIN. The
    ticket's own defect, one coordinate (field order) over, on a surface where the order is the
    author's arbitrary choice.
  * And when it did fire, its early return stood in for `collect_arg_errors` over the WHOLE list, so
    `r.(nosuch, takeN)` silently DROPPED `takeN`'s arity error — the actionable one.
The fix answers each field on its own and hands the complete list to `aggregate_errors`. The second
and third were found by a SECOND review pass, over the fix for the first.

MEASURED, per gate, each by its own back-out (mutate the site, never delete it):
  * the whole change → the 6 error arms fail, the 4 fallthrough controls pass;
  * the VARIANT gate → only `..._a_real_member_failing_for_another_reason_keeps_its_own_error`;
  * the PER-FIELD rewrite (restore the first-failing-field selection) → only
    `..._a_mixed_projection_answers_each_field_in_both_orders`, whose two arms are each other's
    control: identical assertions, only the source order differs;
  * the MARK gate → only `..._an_unmarked_constructor_arg_keeps_the_member_message`;
  * the `Relation` SORT gate → only `..._a_parameterized_non_relation_receiver_...`. NOT the entity
    arm beside it: an entity type is not parameterized, so the schema read declines anyway and its
    message is unchanged. Said at that arm's site rather than left as an assumed pair.

THE FALLTHROUGH IS INTACT, driven rather than loaded: `r.isEmpty` returns `false`, and `r.(isEmpty)`
is still the §6.8 tuple `(isEmpty: Bool)` — the arm the diagnostic could most easily have swallowed,
since it IS a marked projection over a Relation naming a non-column. It does not fire because the
field SUCCEEDS.

TWO THINGS FIXED INLINE rather than filed, both smaller than their ticket would be:
  * `projection_columns`' empty-column list rendered as "(its columns are: )". A MEMBERSHIP receiver
    reaches it for every member since YQB1Y made `Unit` mean zero columns and only zero columns, so
    it now says "it has NONE — a membership relation's schema is `Unit` …".
  * `relation_column_access_parts`' doc said a bare rule-ref receiver "needs a `let` binding first,
    the WI-443/F1 dot-access limitation `where`/`join` share". Measured false: `person_row.(name)`
    with no `let` loads and runs, and `person_row.(nosuch)` reaches the new diagnostic — which is
    reachable only through a `Some` from that function. The loader's value-rooted re-route makes it
    a `DotApply`. The `let` limitation is real for `where`/`join`; it was carried over to projection,
    where it does not hold.
  * kernel-language.md §6.8 cited "(§4.6)" for "a relation SCHEMA is the named tuple of its columns";
    §4.6 is Collection Literals. Repointed to §4.5, where named tuples are defined.

WHAT MOVED IN THE DOCS: §6.8 gains the rule (narrow on purpose — a member lookup that found NOTHING,
never a member whose USE is wrong); `TypeErrorContext::DotProjection`'s doc gains its second
population, since it said "whose member RESOLVES" and now also carries the missing-member case; and
`wi_yqb1y_one_column_relation_test`'s "WHAT THIS DID NOT CLOSE" note now names who closed it.

ACCEPTANCE: cargo-test green via scripts/test.sh — 35 suites, 0 failed, wi_tests 3112 passed;
scaland `sbt test` 499/499 (scaland has no typer, so nothing to mirror there). wi639 / wi714_project /
wi732 / yqb1y projection tests green.

