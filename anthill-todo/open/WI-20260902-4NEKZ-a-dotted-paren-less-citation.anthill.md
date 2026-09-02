## Attributes

- id: WI-20260902-4NEKZ-a-dotted-paren-less-citation
- created: 2026-09-02T13:45:08Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T13:45:08Z

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

