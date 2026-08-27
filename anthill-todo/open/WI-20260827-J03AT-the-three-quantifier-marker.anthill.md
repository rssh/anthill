## Attributes

- id: WI-20260827-J03AT-the-three-quantifier-marker
- created: 2026-08-27T04:17:47Z

- status: Open
- status_agent: claude
- status_at: 2026-08-27T04:17:47Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE THREE QUANTIFIER-MARKER ARMS ARE STILL NAME-KEYED, and carry the defect WI-20260826-XED22 fixed for the goal connectives — a USER predicate sharing the short name is classified as the marker, its DATA arguments are read as goals, and the wrong-arity refusal never runs.

THE GAP, DRIVEN. Two identical programs differing only in the head's NAME, on the built tree:

  namespace t9.marker
    fact p9(1)   fact q9(2)
    rule forall_impl(?x) :- p9(?x)
    rule r9(?x) :- forall_impl(p9(?x), q9(?x), p9(?x))
  -> LOADS CLEAN, answers `?x = ?_`, 1 solution, exit 0

  namespace t9.ctl                      (same shape, head renamed)
    rule zzz(?x) :- p9(?x)
    rule r9(?x) :- zzz(p9(?x), q9(?x), p9(?x))
  -> LOAD ERROR: "expected a term a clause of `t9.ctl.zzz` can match (1 positional), got 3 positional"

`some_in` yields a bogus undischarged residual instead of an answer. This is XED22's own separating pair, one coordinate over.

WHERE. `KnowledgeBase::goal_slot_readings` (kb/mod.rs) matches `("forall_in" | "some_in", 3)` and `("forall_impl", 3)` on `local_name_of(functor)`. `KnowledgeBase::is_discharge_functor` is the same test (`local_name_of(f) == "forall_impl"`) and decides whether `collect_undefined_goal_functors` SKIPS a subtree — so a user predicate named `forall_impl` also suppresses the undefined-goal walk beneath it. The `pos_arity` gate those tables carry stops a wrong-arity MARKER and cannot stop a right-arity WRONG SYMBOL.

WHY IT WAS NOT FIXED WITH THE CONNECTIVES, which is the whole content of this ticket rather than an excuse. `or` / `and` had somewhere to point: `anthill.kernel.or` / `.and` are declared, carry qualified names, and a cached symbol compare distinguishes them from a user's `or` in O(1). A MARKER HAS NO IDENTITY TO COMPARE AGAINST — it is minted `self.kb.intern("forall_impl")` (kb/load.rs), a bare interned symbol with no qualified name and no declaration anywhere; `grep` finds no `anthill.*forall_impl` in the stdlib or in the Rust registries. So keying it on a symbol needs the markers to HAVE an identity first, which is WI-20260825-5W3RJ's move (`parse::desugar_target`, absolute `..` addresses that no identifier can spell) applied to a table it did not cover.

TWO ROUTES, NEITHER COSTED:
 (a) give the three markers absolute addresses the way 5W3RJ gave the desugar targets theirs, then key both readers on the resolved symbol. Needs a census of every mint site (the loader's quantifier lowering, `parse/convert.rs`, the synthesized `<Sort>.induction`, query patterns) — a marker minted short at ANY of them stops being recognized, and the failure mode is a quantifier body silently read as data.
 (b) compare against the CACHED BARE interned symbol instead. A user's head is a SCOPED symbol (`t9.marker.forall_impl`) and the mint is the bare global, so the two are already distinct symbols and no addressing is needed. Cheaper, but it depends on every mint site using the same bare intern — the same census, without the migration.

CONTROL, when it is fixed: the `forall_impl` row above becomes the `zzz` error verbatim, and the `zzz` row stays as it is — the pair is what says the fix is about the KEYING and not about the arity check, which already works. Add a `some_in` row (its current answer is a residual, not a refusal, so a count alone will not catch it) and a row for `is_discharge_functor`'s skip. A genuine `(forall(?x), P(?x) -: Q(?x))` discharge and a bounded `(forall ?x in xs: p(?x))` must keep working — those are the reason the arms exist.

FOUND BY /code-review on WI-20260826-XED22, which fixed two of the five arms in that table and left three; the inconsistency is worse than either extreme, so this should not sit long. XED22's `is_goal_connective` is the shape to copy.

