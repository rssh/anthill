## Attributes

- id: WI-20260818-7X7NK-a-projection-over-a-1
- created: 2026-08-18T19:15:24Z

- status: Open

- acceptance: cargo-test, scaland-sbt-test

## Description

A projection over a 1-collapsed relation is refused by DOT DISPATCH, so the message names the wrong thing. Filed out of WI-1128 (delivered 2026-08-18), which measured it, wrote the reason at the site, and left it unowned.

MEASURED: `ages.(age)` on `rule ages(?age) :- person(age: ?age)` (schema 1-collapses to `Int64`) fails with "type mismatch in anthill.prelude.Relation.age: expected operation declared on the receiver's sort, got no such member (dot dispatch)". The author wrote a PROJECTION and is told their relation has no MEMBER called `age` — a true sentence about a question they did not ask.

WHY: kernel-language.md 6.8's single-member 1-collapse desugars `r.(f)` to `r.f` at CONVERT time, before any type exists. So a one-column receiver never builds a projection node at all: `projection_columns` (rustland/anthill-core/src/kb/typing.rs) declines because the schema is not a named tuple, the caller falls through to ordinary dot dispatch, and dot dispatch reports what it sees. `projection_columns`' own message — which WI-1128 rewrote to name the collapse and say "a one-column relation already IS that column: the projection would be the identity" — is therefore reachable ONLY from a WRITTEN `Project[T, Keep]`.

WHY IT WAS NOT FIXED INLINE: the fallthrough is load-bearing. `r.(f)` and a genuine member call `r.isEmpty` are the SAME node after the desugar, so making the decline loud would break every single-member dot call on a relation. A fix has to distinguish them, and the only signal available is the receiver's sort plus the failure — i.e. a Relation-keyed arm at the dot-dispatch failure site. That is not obviously the right shape (the typer's standing discipline is that nothing keys on an operation's identity; keying a DIAGNOSTIC on a receiver SORT is a weaker version of the same smell) and it deserves its own decision rather than being smuggled in under a ticket about `join`.

TWO CANDIDATE SHAPES, neither chosen: (a) at the dot-dispatch no-such-member site, if the receiver is a `Relation` whose schema is not a named tuple, say so and name the collapse; (b) keep a marker on the convert-time desugar recording that the node CAME FROM a `.( )` form, so the failure can report the surface the author actually wrote — more faithful, and it would also improve the multi-member case, at the cost of a node-level flag.

NOTE THE INTERACTION: if WI-20260818-YQB1Y (the 052 OQ5 split) lands, a one-column relation stops having a collapsed schema and this diagnostic becomes unreachable through THAT route — but not through a genuinely mistyped column name, which is the common case and is what shape (b) would serve. So this is not automatically closed by that ticket; check before starting.

ACCEPTANCE: `ages.(age)` reports a message naming the projection and the collapse rather than dot dispatch's "no such member", OR the shape question is decided and the current behaviour is recorded as intended with the decision at the site; `r.isEmpty` and every existing single-member dot call on a relation still work (the fallthrough is not broken — drive one, do not assert only that it loads); existing wi639 / wi732 projection tests green; cargo-test green via scripts/test.sh.

## Changes

### 2026-08-18T20:54:04Z — feedback — claude

RE-CHECKED AFTER WI-20260818-YQB1Y LANDED (052 OQ5 option A, the 1-collapse dropped), because this ticket asked for exactly that ("check before starting"). VERDICT: STILL OPEN, and the route is unchanged.

MEASURED on the post-YQB1Y tree, both receiver arities:
  * `adults.(nosuch)` over a ONE-column relation `rule adults(?who) :- person(name: ?who, age: 30)`
  * `person_row.(nosuch)` over a TWO-column relation
Both report: "type mismatch in anthill.prelude.Relation.nosuch: expected operation declared on the receiver's sort, got no such member (dot dispatch)". Identical text, identical route.

WHAT CHANGED, AND WHY IT DOES NOT CLOSE THIS. The ticket's own mechanism paragraph is now stale in its FIRST clause and still correct in its second. `r.(f)` no longer 1-collapses at convert time — it builds the marked one-field tuple `(f: r.f)` at every arity — so a one-column receiver DOES build a projection node now, and `ages.(age)` runs (driven by `wi_yqb1y_one_column_relation_test::yqb1y_a_one_member_projection_keeps_its_key`, which uses the rename form). The example the ticket was FILED with therefore works. But the failure route for a MISTYPED column is untouched: `relation_column_access_parts` still returns None when the member does not resolve, the recognizer still declines, and the call still falls through to ordinary dot dispatch. That fallthrough is still load-bearing for the same reason (`r.isEmpty` is the same node shape after the desugar), so shape (a) vs (b) is still a real decision.

WHAT THIS MEANS FOR THE TICKET'S SCOPE: the "1-collapsed receiver" framing is gone — there is no collapsed schema left to name — so `projection_columns`' collapse-naming message is now dead prose rather than an unreachable-but-correct one, and the remaining defect is narrower and more ordinary: a projection naming a column that does not exist is reported as a MEMBER lookup. That makes shape (b) (carry the `.( )` provenance to the failure site) the only one of the two candidates that still describes a fix — shape (a) keyed on "a Relation whose schema is not a named tuple" no longer has a population, since a relation schema is ALWAYS a named tuple or `Unit` now. Worth restating the acceptance before starting.

NOT PINNED BY A TEST, deliberately: a test asserting today's dot-dispatch message would pass both before and after YQB1Y and so measures nothing about it. The measurement is recorded in the header of `wi_yqb1y_one_column_relation_test` instead, with the two spellings above.
