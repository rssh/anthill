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

### WIDER THAN `map`, AND TWO HYPOTHESES ALREADY REFUTED

`filter` is broken too, which was not known when this was filed. One entity, one
dot, four combinators, `xs: List[Row]` where `entity Row(a: Int64, flag: Bool)`:

  xs.find(lambda r -> r.flag)             LOADS
  xs.foldLeft(0, lambda (acc, r) -> r.a)  LOADS
  xs.filter(lambda r -> r.flag)           REFUSED  <unresolved receiver>.flag
  xs.map(lambda r -> r.a)                 REFUSED  <unresolved receiver>.a

The title says `map`; read it as `map` AND `filter`, and as a question about which
combinators the N2FHM repair actually reached rather than about one of them.

**REFUTED (1): the extra type parameter.** The obvious reading — `map[Dst, EffP]`
and `find[EffP]`, so an open result parameter blocks it — does not survive
`foldLeft[Acc, EffP]`, which carries one and LOADS, next to `filter[EffP]`, which
carries none and FAILS. Pinning explicitly (`xs.map[Dst = Int64](…)`) also does
not help.

**REFUTED (2): ambiguous dispatch between two same-shaped declarations.** The
failing pair are each declared with an identical `(c: C, …)` receiver in BOTH
`finite_collection.anthill` and `iterable.anthill`, while the working pair are
declared twice with DIFFERENT receivers (`find`: `c: C` / `s: Stream`; `foldLeft`:
`c: C` / `xs: List`). That fits the literal wording `<unresolved receiver>` and is
wrong anyway: naming the declaration does not fix it.

  Iterable.map(xs, lambda r -> r.a)          REFUSED, identically
  Iterable.filter(xs, lambda r -> r.flag)    REFUSED, identically

So the split is real and reproducible, and neither of the two structural
differences visible in the signatures explains it. Whoever takes this should start
by diffing what `check_apply` does for `find` against what it does for `filter` —
the same callback shape `(x: Element) -> Bool`, the same receiver `c: C`, opposite
outcomes — since that pair holds everything else constant.

HOW THIS WAS FOUND, because it bears on WI-20260829-ARQ5X: by writing four
one-line probes over one entity. Nothing in the 544-file test suite does that —
seven files in the whole of `anthill-core/tests/include/` contain a dot inside a
lambda at all, and none sweeps one construct across several hosts.
## Changes

### 2026-08-29T09:23:27Z — feedback — user

RE-MEASURED on 0fbea4e6 (post WI-20260829-1SSXM). The NARROWED repro does not
reproduce, and the defect that IS real is narrower than the title.

1. THE NARROWED REPRO LOADS CLEAN, verbatim, through try_load_kb_with:

     namespace probe
       import anthill.prelude.{List, Int64, Bool, Stream, Option}
       entity Row(a: Int64, flag: Bool)
       operation probe_op(xs: List[Row]) -> Stream[Int64, {}] =
         xs.map(lambda r -> r.a)
     end
                                                        -> LOADS

   Also loads with typing.rs reverted to its pre-1SSXM state, so the scrutinee
   propagation is not what changed it; and the six commits cc2b996b..d635709a
   touched no rustland/anthill-core/src/ at all. The minimal shape has apparently
   never reproduced.

   Nor does any spelling of it. Minimal entity, unannotated `let` consumer:

     xs.map(lambda r -> r.a)              LOADS      xs.filter(lambda r -> r.flag)        LOADS
     map(xs, lambda r -> r.a)             LOADS      filter(xs, lambda r -> r.flag)       LOADS
     Iterable.map(xs, lambda r -> r.a)    LOADS      Iterable.filter(xs, lambda r -> ...) LOADS

2. THE REAL DEFECT REPRODUCES ONLY IN THE QUALIFIED SPELLING, AND ONLY WITH THE
   LABEL-PARAMETERIZED RECEIVER. In good.anthill, substituting only the summarize
   argument, exactly as the original text does:

     bodies_of(msgs)                         LOADS  (control)
     msgs.map(lambda m -> m.body)            REFUSED, 30:23 -- type mismatch in
       summarize.msgs (op-arg): expected List[T = Text[Trust = Untrusted]], got
       MappedStream[T = Text[Trust = Untrusted], Source = List[T = Message[...]], ...]
     Iterable.map(msgs, lambda m -> m.body)  REFUSED, 30:69 -- type mismatch in
       <unresolved receiver>.body: ... no such member (dot dispatch)

   Only the THIRD is the N2FHM class. The second one's element type came back
   Text[Trust = Untrusted] -- i.e. the callback dot RESOLVED, and what is refused
   is that summarize wants a List and map yields a lazy MappedStream. This matches
   N2FHM's own control_dot_spelling_find: the DotApply frame pre-types its receiver
   (WI-443), so the dot spelling never had the gap.

3. THE FOUR-PROBE TABLE MEASURES SOMETHING ELSE. Run each host with the dot and
   with a dot-free callback of the same shape:

     List.length(xs.filter(lambda r -> r.flag))  REFUSED -- expected List, got FilteredStream[...]
     List.length(xs.filter(lambda r -> true))    REFUSED -- expected List, got FilteredStream[...]

   Byte-identical. Same for map/MappedStream. So the `filter REFUSED` and
   `map REFUSED` rows are a lazy-stream-vs-eager-consumer gap, not a callback-dot
   gap, and "filter is broken too [the same way]" is not established by them. The
   consumer gap is real and worth its own item -- xs.filter(...).length() is
   ordinary code that does not work -- but it is a different defect.

SO: the subject is a callback binder that fails to ground in the QUALIFIED spelling
on a receiver whose type carries a label parameter. Both refuted hypotheses in the
current text (the extra type parameter; ambiguous dispatch) were reasoned from the
four-probe table, so they refute a claim the table does not actually make. The
`Iterable.map(msgs, ...)` vs `Iterable.find(msgs, ...)` pair inside guardians is
the place to diff check_apply, since that pair does hold everything else constant.

### 2026-08-29T09:51:24Z — feedback — user

CORRECTION TO MY PREVIOUS FEEDBACK — point 2 was a MISSING-IMPORT ARTIFACT, and the
conclusion I drew from it was wrong. Found by /code-review re-running the probe.

I reported that `Iterable.map(msgs, lambda m -> m.body)` in good.anthill gives
"<unresolved receiver>.body ... no such member (dot dispatch)" and concluded the
N2FHM-class defect survives in the QUALIFIED spelling. good.anthill imports
`anthill.prelude.{List, Error, External}` -- no `Iterable`. My substitution wrote a
qualified call to a sort the file does not import, and the refusal was about THAT.
Both spellings, measured side by side:

  Iterable NOT imported: 30:69 -- type mismatch in <unresolved receiver>.body:
                                  ... no such member (dot dispatch)
  Iterable IMPORTED:     30:23 -- type mismatch in summarize.msgs (op-arg): expected
                                  List[T = Text[Trust = Untrusted]], got Stream[...]

So there is NO surviving callback-dot gap in the qualified spelling, and none anywhere
else I can reach: the 60-cell sweep in typer_capability_matrix_test -- {find, filter,
map, foldLeft} x {dot, unqualified, qualified} x {constant, field dot, match
destructure, nested call, dot call} -- is green on every callback-binder cell.
/code-review also measured the label-parameterized receiver I had assumed was the
missing ingredient (a `Msg[Trust = ?t]` with a `body: Txt[Trust]` field): it loads
clean in all three spellings too.

WHAT SURVIVES OF THIS TICKET, and both halves are now tracked:

  (a) `msgs.map(lambda m -> m.body)` refused        -> WI-20260829-N01PY, the lazy
      stream / eager consumer gap. Not about dots, not about map; `summarize` wants a
      List and map yields a Stream. Four paired cells in `lazy_stream_consumption`.

  (b) `msgs.map(lambda m -> match m case message(...) -> b)` refused with "expected
      ?Dst" -> REAL, and still this ticket's. The sweep localizes it: RED for map in
      all three spellings, GREEN for every other map body form, GREEN for foldLeft's
      match destructure (`foldLeft[Acc]` carries a result parameter too), GREEN for
      find and filter. So it is `map`'s `Dst` failing to reconcile against a MATCH
      ARM's type -- not the callback binder, not the spelling, not "has a result
      parameter". Cell: `map / {dot,unqualified,qualified} / match destructure`.

THE TICKET'S OPEN QUESTION IS ANSWERED. It asks whether (b) is a consequence of (a) --
"if `Element` never grounds, the match arm has nothing to reconcile `?Dst` against" --
or independent. INDEPENDENT: `Element` grounds fine, which the green `map / field dot`
cell says directly, and `?Dst` fails anyway. Retitling to name (b) alone would now be
accurate; (a) has moved to N01PY.

