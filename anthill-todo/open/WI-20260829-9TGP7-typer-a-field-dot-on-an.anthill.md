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

