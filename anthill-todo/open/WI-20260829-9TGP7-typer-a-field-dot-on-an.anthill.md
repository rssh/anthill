## Attributes

- id: WI-20260829-9TGP7-typer-a-field-dot-on-an
- created: 2026-08-29T07:52:27Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T07:52:27Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER: a field dot on an `Iterable.map` callback parameter does not resolve — WI-20260828-N2FHM's twin, one operation over.

MEASURED against examples/guardians/fixtures/agent/good.anthill, substituting ONLY the summarize argument and changing nothing else. `msgs` is `List[Message[Untrusted]]`; `Message` has a public `body: Text[Trust]` field.

  (a) msgs.map(lambda m -> m.body)
      error: type mismatch in `<unresolved receiver>.body`: expected operation
             declared on the receiver's sort, got no such member (dot dispatch)

  (b) msgs.map(lambda m -> match m case message(i, f, r, s, b) -> b)
      error: type mismatch in match.rule (rule): expected ?Dst, got Text[Trust = ?_]

  (c) CONTROL — bodies_of(msgs), the hand-written projection: loads clean.

SO BOTH SPELLINGS AN AGENT WOULD REACH FOR ARE REFUSED, including the destructuring workaround that N2FHM used for `find`.

IT IS THE SAME SHAPE N2FHM JUST FIXED. `Iterable.find[EffP](c: C, pred: (x: Element) -> Bool …)` is stdlib/anthill/prelude/iterable.anthill:41 and was repaired at cc2b996b by grounding the callback binder from the receiver's PROVISION at hint time (`bind_spec_params_for_hint`). `Iterable.map[Dst, EffP](c: C, f: (x: Element) -> Dst …)` is the same file, line 67, same `(x: Element)` binder reached only through `List provides Stream provides Iterable` — and still fails.

NOT THE UNBOUND RESULT PARAMETER, which is the obvious hypothesis and is measured FALSE: `msgs.map[Dst = Text[Untrusted]](lambda m -> m.body)` fails identically. The difference from `find` is therefore not that `Dst` is open where `Bool` is ground; `Element` is simply not grounded for `map` at all.

WHETHER (a) AND (b) ARE ONE ROOT OR TWO IS OPEN. (b) may be a consequence — if `Element` never grounds, the match arm's type has nothing to reconcile `?Dst` against — or an independent failure to ground `map`'s result parameter from a match arm. Whoever takes this should decide that first; the fix for (a) may or may not close (b).

WHY IT MATTERS BEYOND ERGONOMICS: examples/guardians/lib/vocabulary.anthill declares `bodies_of(msgs: List[Message[?t]]) -> List[Text[?t]]` and every agent fixture calls it. That operation exists ONLY because a generated agent cannot write the map itself — the trusted vocabulary has to supply what the agent cannot express. It is a workaround for this bug, its comment now says so, and it should be deleted when this is fixed.



### NARROWED — no provision chain needed, and `find` is the control

The original text reasoned that `Element` reaches the receiver only through
`List provides Stream provides Iterable`. That framing is not needed: the minimal
reproduction has no provision chain, no label parameter and no spec parameter.

```anthill
namespace probe
  import anthill.prelude.{List, Int64, Bool, Stream, Option}
  entity Row(a: Int64, flag: Bool)
  operation probe_op(xs: List[Row]) -> Stream[Int64, {}] =
    xs.map(lambda r -> r.a)
end
```

  -> type mismatch in `<unresolved receiver>.a`: expected operation declared on
     the receiver's sort, got no such member (dot dispatch)

FOUR PROBES OVER THAT ONE ENTITY, and between them they isolate it exactly:

  xs.find(lambda r -> r.flag)    dot, in FIND    LOADS CLEAN
  xs.map(lambda r -> r.a)        dot, in MAP     REFUSED, above
  xs.map(lambda r -> 1)          no dot, in MAP  LOADS CLEAN
  xs.map(lambda x -> x)          identity        LOADS CLEAN (over List[Int64])

So it is neither the lambda nor the element type. A lambda in `map` binds its
parameter well enough to return it or to ignore it, and the identical dot on the
identical entity resolves under `find`. THE ONLY VARIABLE LEFT IS WHICH OPERATION
IS BEING CALLED: `find` received WI-20260828-N2FHM's fix at cc2b996b
(`bind_spec_params_for_hint`, grounding the callback binder from the receiver's
provision at hint time) and `map` — `iterable.anthill:67`, ten lines from the
`find` at `:41`, same `(x: Element)` binder — did not.

WHAT IS DIFFERENT ABOUT `map`, and it is worth checking first: it carries an extra
type parameter, `map[Dst, EffP]` against `find[EffP]`, and its callback returns
that `Dst` where `find`'s returns a ground `Bool`. Pinning it explicitly —
`xs.map[Dst = Int64](lambda r -> r.a)` — does NOT help, so `Dst` being unresolved
is not itself the blocker; but its mere presence may route the call down a
different staging path, which is where to look.

THE FIX SHOULD CLOSE THE SECOND SPELLING TOO, or say why not. The destructuring
workaround N2FHM used for `find` also fails under `map`:

  msgs.map(lambda m -> match m case message(i, f, r, s, b) -> b)
    -> type mismatch in match.rule (rule): expected ?Dst, got Text[Trust = ?_]

That one may be a consequence of the same root — if the binder never grounds, the
match arm has nothing to reconcile `?Dst` against — or independent. Decide before
fixing.

THE `bodies_of` CONSEQUENCE stands as written above: both spellings an agent would
reach for are refused, so the trusted vocabulary must supply the projection, and
`examples/guardians/lib/vocabulary.anthill` says so at the declaration.
