## Attributes

- id: WI-20260827-J03AT-the-three-quantifier-marker
- created: 2026-08-27T04:17:47Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-22T17:05:15Z

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

## Changes

### 2026-10-22T17:05:14Z — feedback — user

Delivered in 3c575fe5. Route (a), the user's decision (2026-10-22): the three quantifier markers are minted at kernel addresses (..anthill.kernel.forall_impl / .forall_in / .some_in) and every reader keys on the builtin tag bootstrap registers on them; route (b) was measured out first, since in a namespace declaring its own forall_impl (a rule or a fact) the parser's discharge resolved to the user's symbol. Spec 5.3 and 8.6 changed with it: a bare written forall_impl(...) is the writer's own name. __pop_assumption was included on the user's answer; __within_requirements, found by /code-review (a user predicate of that name answered nothing where its clause held), was fixed the same way. NOT BUILT: a load-time refusal of a kernel marker written at another arity under an explicit import of anthill.kernel - it loads, and the resolver reports it as an error when it runs (driven by a_kernel_marker_in_another_shape_is_an_error_when_it_runs); undefined_functor cannot report it, since the bootstrap declares the symbol and the CLI asserts an undefined functor is undeclared. Rows: tests/include/wi_j03at_marker_identity_test.rs (11 of 13 fail on the parent commit; the two controls pass either way) and wi878_marker_arity_test's canonical-arity and discharge rows.

