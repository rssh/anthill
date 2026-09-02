## Attributes

- id: WI-20260902-4NEKZ-a-dotted-paren-less-citation
- created: 2026-09-02T13:45:08Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-02T15:26:42Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A DOTTED PAREN-LESS CITATION AS AN `=` OPERAND IS REFUSED THREE TIMES, each blaming one segment of a name that resolves.

MEASURED BY ME (found by /code-review during WI-20260902-VNWAW; re-measured with that
ticket's change backed out — identical, so it is pre-existing):

  namespace zzf2.inner
    fact base(1)
    rule rel(1) :- base(1)
  end
  namespace zzf2.two
    rule dRel(1) :- zzf2.inner.rel = 7
  end

  6:19: type mismatch in zzf2.name: expected resolved name, got unresolved
  6:19: type mismatch in inner.name: expected resolved name, got unresolved
  6:19: type mismatch in rel.name: expected resolved name, got unresolved

Three errors at ONE span, one per segment, and every one of them is false: `zzf2.inner.rel`
resolves. The chain fell to the `field_access` PROJECTION path and each segment was typed
as a field name.

THE ONE-SEGMENT SPELLING IS THE CONTROL AND IT BEHAVES: `rule sRel(1) :- rel1 = 7` gives
one error of the right shape — "type mismatch in eq.b (op-arg): expected Relation[T = Unit,
E = {…}], got Int64" — i.e. it reads `rel1` as the relation VALUE and complains about the
comparison, which is a real diagnosis a user can act on. So this is the same
"the qualification decides nothing" claim WI-20260901-719FJ made for logical positions,
left false at the one VALUE position that types its operands.

NEIGHBOURS THAT ARE CLEAN, measured, which is what localizes it to the `=` operand:
`holdsQ(zzf2.inner.rel)` in a fact head and in a rule body both load and match, and
`?t <=> zzf2.inner.rel` binds without complaint. Only `=` types its operands, and only
there does the chain reach the projection typing.

NOT RE-TRACED TO A SITE — verify before fixing. The symptom is the one `load.rs` already
describes near the `EquationFunctor` handling, which WI-898 closed for that kind only.

ACCEPTANCE: the dotted spelling produces the SAME diagnosis the one-segment spelling
produces — one error, naming the comparison, not three naming segments. CONTROLS: a chain
that genuinely IS a projection (`?x.f = 7`) must keep its per-field diagnosis; a chain
naming NOTHING (`zz.nosuch.rel = 7`) must still be refused, and once; and the three clean
neighbours above must stay clean.

## Changes

### 2026-09-02T15:26:37Z — feedback — user

DELIVERED, and the ticket UNDERSTATED it twice.

1. IT WAS NOT A DIAGNOSTIC DEFECT, IT WAS A REFUSAL. `rule r(1) :- ns.rel = ns.rel`
   reported SIX load errors and `ns.rel = local_rel` three — well-typed comparisons of two
   `Relation[T]` values that the one-segment spelling has always been allowed to write.
   Both load now. The three-per-operand cascade is the same defect's tail.

2. THE POPULATION IS ONE ROW OF SIX, not "the `=` operand". Comparing the OPERATION BODY
   with the RULE BODY across six name kinds, exactly one differed — a chain naming a RULE
   (1 error vs 3). A chain naming a constructor, a sort, a namespace, an entity or nothing
   reports IDENTICALLY in both positions, so those are `check_bare_ref`'s fall-through
   calling a resolved name unresolved, once per segment: filed as WI-20260902-40KSW with
   that matrix, and `the_five_other_name_kinds_still_agree_with_the_operation_body` is its
   fixture.

TWO OF THIS TICKET'S OWN CONTROLS WERE WRONG, both from false premises I wrote here:
 * "a chain that genuinely IS a projection (`?x.f = 7`) must keep its per-field diagnosis"
   — measured, `?x.f = 7` produces ZERO errors. The row is rewritten around a fixture that
   IS refused, with a non-emptiness assertion so it cannot go vacuous.
 * "a chain naming NOTHING must still be refused, and once" — it is refused THREE times,
   in both positions, before and after. That is 40KSW's, not this ticket's, and the
   fixture now asserts the two positions AGREE rather than an absolute count.

THE REPAIR IS THE TYPER'S, MEASURED NOT PREFERRED. Collapsing the chain in the rule-body
walk — the obvious fix, and what the operation body does — fells
`wi_719fj_dotted_paren_less_citation_test::a_data_slot_still_stores_the_chain_on_both_sides_of_a_match`:
a fact's argument is a TERM and a rule body an OCCURRENCE, so rewriting one side stops
them matching. `dotted_citation_relation` reads the chain in the typer and changes no
term; the run-time binding is asserted unmoved. Nor is the `Relation[T]` type a lie about
the value: `?t <=> ns.rel` and `?t <=> rel` BOTH bind the name at run time, so the dotted
spelling now says what the one-segment one already said. Spec §6.7 had already legislated
it, so no spec change.

`/code-review high` FOUND A REAL DEFECT IN MY FIRST CUT, and it was worse than what I set
out to repair: the recognizer had no PROVENANCE gate, so a hand-written
`anthill.reflect.field_access(ns, rel)` was read as the name `ns.rel`, typed `Relation[T]`
and LOADED CLEAN — WI-20260901-92VA4's defect re-introduced in the typer, a SILENT
ACCEPTANCE. I reproduced it, then measured that SHAPE CANNOT CLOSE IT: with a one-segment
receiver the written call and the desugared dot reach the typer as identical nodes, so the
reviewer's suggested "require a scope-owning receiver" repair and my own "require resolved
segments" repair both leave it open (I built the second and measured it failing). Closed
by carrying the parse term's `is_minted` bit onto the occurrence as
`NodeKind::Expr::dot_chain` — the loader is the only pass that can answer, and the four
occurrence constructors are the only places that set it. `a_hand_written_field_access_call_is_not_a_citation`
is its row, and the gate is its own back-out axis.

Also fixed from that review: a bound whose `iter().all(…)` would have gone vacuous on an
empty error list while still reading as a guard.

MEASUREMENTS: two axes, each backed out present-but-wrong over the whole 4 047-row binary
— the reading fells exactly 4 rows, the provenance gate exactly 1, and they meet in one
test on its two halves. rustland 6 339 over 36 binaries, scaland 539 — green. No scaland
mirror: the diagnosis is the typer's and scaland has none (WI-1007).

