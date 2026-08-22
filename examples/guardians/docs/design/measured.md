# Every measured run, as a flow

**Status:** Measurement record, 2026-08-22. Probes ran against
`anthill load` at commit `3b980e5c`; sources in [`docs/measurements/guardians/`](../../../../docs/measurements/guardians/). Everything
here was executed — unlike [`effects.md`](effects.md), which is argument.

Each entry is written the same way: **the scenario** (what an attacker or a bad
generation is trying to do), **the flow**, **what fires**, **the control**, and
**what it would mean if it did not fire**. A run without its control measures
nothing, so the controls are not optional reading.

The eleven runs fall into three groups. Group A is data confinement — the
`Text[Trust]` label. Group B is capability confinement — the `provides` chain.
Group C is what does *not* work, which is as load-bearing as the rest.

---

# Group A — data confinement

## A1 · The label is enforced where data enters a sink

**Scenario.** The generated agent takes something that came out of the mailbox
and hands it to a sink that is only allowed public data. This is the base case
the whole design rests on; if it does not fire, nothing else matters.

**Flow.**
```
  fetch()  ──▶ Text[L = Untrusted] ──▶ sendPublic( body: Text[L = Public] )
                                                        ▲
                                                        └── mismatch here
```

```anthill
operation fetch()  -> Text[L = Untrusted]
operation sendPublic(body: Text[L = Public]) -> Unit
operation leak() -> Unit = sendPublic(fetch())
```

**Fires** — `docs/measurements/guardians/d2d_typecheck.anthill`:
```
error: type mismatch in sendPublic.body (op-arg):
       expected Text[L = Public], got Text[L = Untrusted]
```

**Control** — `docs/measurements/guardians/d2e_control.anthill`. A blatant sort mismatch,
`takesString(number())` with `number() -> Int64`, produces the same diagnostic
shape. Without it, A1 could be measuring a parse failure or a name that
resolves to nothing rather than a real type check.

**If it did not fire,** labels would be decoration and every other run in
group A would be vacuous.

## A2 · The label survives a transformation — the article's attack

**Scenario.** This is Meijer's exfiltration. The agent does not send raw mail;
it summarizes first, and sends the summary. A design that only checked direct
flows would pass this, and it is the single most important run in the record.

**Flow.**
```
  fetch()          Text[L = Untrusted]
      │
      ▼
  summarize()      Text[L = ?l] ─▶ Text[L = ?l]      ← ?l binds to Untrusted
      │                                                 by unification
      ▼
  sendPublic()     expects Text[L = Public]          ← refused HERE
```

```anthill
operation summarize(body: Text[L = ?l]) -> Text[L = ?l]
operation leak() -> Unit = sendPublic(summarize(fetch()))
```

**Fires** — `docs/measurements/guardians/d2g_leak.anthill`: the same diagnostic, at the `sendPublic`
call. The label propagated *through* the summarizer because `?l` in and `?l`
out is what "summarizing does not launder" means as a type.

**Control** — `docs/measurements/guardians/d2f_propagate.anthill` line 41:
`sendPublic(summarize(banner()))` with `banner() -> Text[L = Public]` loads
clean. The loader reports multiple errors per file and reported none at that
line, so the control genuinely passed. Without it, A2 would be consistent with
a rule that simply forbids calling `summarize` before a sink.

**If it did not fire,** an attacker would need only to insert one pure
transformation between source and sink, and every real agent has several.

## A3 · Widening is one-directional

**Scenario.** A generated agent tries to launder by routing public data through
a widening coercion and back. Widening `Public → Untrusted` is always safe;
the point is that it does not run backwards.

**Flow.** `banner()` → `widen()` → `sendPublic()`, where
`widen(Text[L = Public]) -> Text[L = Untrusted]`.

**Fires** — `docs/measurements/guardians/d2f_propagate.anthill` line 44, refused. Deliberate: the
coercion is one-way and the type checker keeps it that way.

**Control.** A2's control is this run's control too — the same file's line 41
passes, so the file is not simply rejecting everything.

**If it did not fire,** the lattice would be symmetric and therefore not a
lattice.

---

# Group B — capability confinement

These four run over the `provides` route, so they test what happens when the
generated artifact is a **sort implementation** claiming to satisfy a spec.

## B1 · A provision must actually back the member

**Scenario.** The generator emits a carrier and a `provides` clause but no
implementation — the cheapest possible way to claim success.

**Flow.**
```
  spec Agent { operation run(self: C, input: String) -> String @ {Error} }
  carrier EmptyAgent { provides Agent[C = EmptyAgent] }     ← nothing backs run
```

**Fires** — `docs/measurements/guardians/p6_missing_member.anthill`:
```
error: 'EmptyAgent' provides 'Agent' but backs no operation 'Agent.run'
       (no default on 'Agent', no own 'run' on 'EmptyAgent')
```

**If it did not fire,** "generate an implementation" would have a trivial
winning move.

## B2 · The provider's declared row may not widen the spec's

**Scenario.** The generated agent honestly declares that it reaches the outside
world, but the spec never granted that capability. This is the capability
question, separate from anything about data.

**Flow.**
```
  spec    run(...) @ {Error}
  carrier run(...) @ {Error, External}      ← declares MORE than the spec allows
          provides Agent[C = LeakyAgent]
```

**Fires** — `docs/measurements/guardians/p2_spec_wider_row.anthill`:
```
error: 'LeakyAgent' overrides 'Agent.run' but does not refine it: the override
       declares effect `External`, which is not covered by any effect the spec
       operation declares (effects must not widen)
```

**Control** — `docs/measurements/guardians/p1_spec_good.anthill`. A conforming provider with row
`{Error}` loads clean, so B2 measures the row and not a blanket refusal of
`provides`.

**If it did not fire,** the spec's effect row would be documentation, and
`-External[Commit]` — the design's strongest single claim — would mean nothing.

## B3 · The body may not exceed its own declaration

**Scenario.** The obvious evasion of B2: declare narrowly, act widely. The
generated `run` declares `{Error}` and then calls an operation that is
`External`. If this does not fire, B2 is trivially bypassed and the whole
capability story collapses.

**Flow.**
```
  carrier run(...) @ {Error}   ← declaration satisfies B2
              │
              └──▶ calls leak(...) @ {External, Error}   ← body exceeds it
```

**Fires** — `docs/measurements/guardians/p4_body_exceeds.anthill`:
```
error: type mismatch in run.effects (op-effects):
       expected declared: [Error], got undeclared effect: External
```

**Control** — `docs/measurements/guardians/p5_body_control.anthill`. The identical shape with a
callee typed `{Error}` loads clean, so B3 measures the inferred row and not the
presence of a call.

**If it did not fire,** every effect annotation in the language would be a
promise nobody checks, and B1/B2 would be theatre.

## B4 · A reshaped member does not smuggle a row past the check

**Scenario.** Backing is matched by short name (WI-935), so it is worth asking
whether a differently-shaped `run` escapes the widening rule by not lining up
with the spec's declaration.

**Flow.** A member named `run` with the wrong arity, the wrong return type, and
`External` in its row.

**Fires** — `docs/measurements/guardians/p7_sig_and_row.anthill`: refused by B2's rule, unchanged.
Name-only matching is enough for the effect check.

**If it did not fire,** WI-935 would be a security gap rather than a
correctness one, and the chain B1→B2→B3 would have a hole at the bottom.

---

# Group C — what does not work

## C1 · Signature conformance is not checked · **the gap**

**Scenario.** The generated implementation claims to provide a two-argument,
`Report`-returning spec with a one-argument, `Int64`-returning member.

**Loads clean** — `docs/measurements/guardians/p3_spec_wrong_sig.anthill`. The spec says so
outright: *"treat a provision as certifying that a member of that name exists,
not that it fits"* (WI-935).

**Why it matters here more than usual.** For hand-written code this is a latent
mis-dispatch. For **generated** code it is backwards: a bad generation is
accepted at check time and fails at the first call, when the entire premise of
the workflow is that the checker tells the generator what to fix. Not a
security hole — B4 showed the row chain is unaffected, and a member nothing can
call correctly reaches no sink — but it puts WI-935 on the critical path.

## C2 · An operation `requires` does not gate a call site

**Scenario.** Express the flow lattice as a contract —
`send(body: Text[L = ?l]) requires flows_to(?l, Public)` — and let the KB hold
the lattice as facts.

**Loads clean, gates nothing** — `docs/measurements/guardians/d2c_callsite.anthill`. Passing
`Text[L = Untrusted]` to that sink is accepted. §6.5 and §8.5 say why:
`requires` generates proof obligations tied to an `Implementation` fact, not a
static call-site check.

**Control.** `flows_to(Untrusted, Public)` correctly has **no solutions** when
queried, so the lattice facts are right and it is the *gating* that is absent,
not the data.

**Consequence.** The lattice ordering cannot ride on the operation contract,
which is one of the three closures that forced explicit coercion operations.

## C3 · A rule body cannot destructure a type argument

**Scenario.** Let policy rules read the label —
`releasable(?x) :- ?x: Text[L = ?l], flows_to(?l, Public)`.

**Syntax error** — `docs/measurements/guardians/d2h_ruleside.anthill`, at `?x:`. This is WI-742,
explicitly unimplemented in proposal 060.

**Consequence.** Labels live in the typer and are invisible to the rule layer,
so policy about labels must be expressed as operation signatures, not as rules.

## C4 · The label slot is invariant BY DEFAULT — and variance is declarable · **corrected**

**Scenario.** Get widening free from subtyping: pass `Text[Public]` where
`Text[Level]` is expected.

**Refused** — `docs/measurements/guardians/d2j_variance.anthill`:
`expected Text[L = Level], got Text[L = Public]`.

**The correction, and it matters because the original conclusion was wrong.**
That probe measured the **default**, and the default is invariant — which is
all it establishes. anthill *has* variance, declared as facts
(`Covariant(sort, param)` / `Contravariant`, `stdlib/anthill/reflect/typing.anthill`),
and `type_compatible` has a `provides` arm alongside identity, `is_entity_of`
and `refines`. So a lattice modelled as a **provides-chain** with a covariant
parameter gives the ordering directly:

```anthill
sort Untrusted end
sort Public  provides Untrusted end
fact Covariant(sort: Text, param: Trust)
```

| | |
|---|---|
| widening — `Text[Public]` into a `Text[Untrusted]` slot | **loads** |
| the dangerous direction — `Untrusted` into `Public` | **refused** |
| the same widening with the `Covariant` fact **deleted** | **refused** |

The third row is the one that matters: it shows covariance is doing the work
rather than the slot being unchecked.

**What this retracts.** The earlier entry concluded that widening needs explicit
coercions and that an *n*-point lattice costs O(*n*²) of them. Neither stands.
The `widen` operation in `lib/vocabulary.anthill` is unnecessary, and D2's
"scales to two or three levels and no further" was a conclusion drawn from a
probe that never declared the thing it was measuring the absence of.

**What survives.** The label position *is* invariant unless you say otherwise,
so a design that wants ordering must declare it — silence gives you the safe
default rather than the useful one. That is the right default and worth stating;
it just is not a limit.

**Related, and still open.** The label slot is also **untyped**: `sort Trust = ?`
accepts anything, so `Text[Int64]` loads clean, and a `requires IsLevel[T = Trust]`
does not constrain it either (both measured). Variance orders the labels; nothing
requires the argument to *be* one.

## C5 · A computed region is not admissible in `Modify[…]`

**Scenario.** State Meijer's frame condition directly —
`delete_files(fs, pattern) @ Modify[glob(pattern)]`.

**Syntax error** — `docs/measurements/guardians/d3_frame.anthill`:
```
error: syntax error near `glob`
error: a single parenthesized type is not a type
```
The region slot is a *type* position, so a parenthesized application is refused
by the type grammar.

**Control.** `Modify[no_such_thing_at_all]` is an unresolved-name error, so the
slot is genuinely name-resolved and the forms that *do* pass — `Modify[fs]`,
`Modify[pattern]` — are not passing vacuously.

**Consequence.** The `delete_file` scenario is deferred out of increment 1.
§5.6's effect-env condition really is the frame axiom; what is missing is only
the surface for writing a computed region.

## C6 · A constructor cannot carry a type argument

**Scenario.** Introduce a label at a construction site —
`mk[L = Untrusted](raw: "secret")`.

**Refused** — `docs/measurements/guardians/d2b_callsite.anthill`, with a diagnostic naming every
position where the bracket *is* read.

**Consequence, and it is a feature.** Labels can enter only through operation
signatures, so the label on a piece of data always comes from the tool that
produced it and never from code that merely handles it. The design wanted that
discipline; the language enforces it.

## C7 · A sort mismatch against a variable-containing type passes silently · **defect**

**Scenario.** Not an attack that was designed — this one was found by writing
the vocabulary out as a real file and watching the exfiltration *succeed*.

The design's whole mechanism is `summarize(body: Text[Trust = ?t]) -> Text[Trust = ?t]`.
A2 measured it refusing the leak. But A2 passes a `Text` in. Pass a **different
sort** — a `Message`, which is what `fetch_mail` actually returns — and:

```anthill
operation fetch_one() -> Message[Trust = Untrusted]
operation sum_flat(m: Text[Trust = ?t]) -> Text[Trust = ?t]
operation sink(body: Text[Trust = Public]) -> Unit
operation leak() -> Unit = sink(sum_flat(fetch_one()))
```

**Loads clean.** `docs/measurements/guardians/` reproduction in the `nest3`/`nest4` shape. `Message`
where `Text` is expected raises nothing, `?t` is never bound, and it then binds
to `Public` at the sink. The exfiltration goes through.

**Controls, and they are what make this precise.** Ground against ground *is*
checked — `send_email(to: 42)` gives `expected Address, got Int64`, and A1/A2
fire. Nesting is *not* the cause — `List[T = Text[Trust = Untrusted]]` into
`List[T = Text[Trust = ?t]]` propagates correctly and the sink refuses it. The
variable is the cause: **an argument checked against a parameter type
containing a type variable is not rejected on a sort mismatch**, and the
silent pass leaves the variable free rather than erroring.

**Why it matters more than a typical typer gap.** A free variable is not a
neutral outcome here — it is the *maximally permissive* one, because the
consumer instantiates it to whatever it wants. So the failure mode is not "a
wrong program is accepted", it is "the label is laundered", which is exactly
the property the design exists to prevent.

**How it was found, and the lesson.** `examples/guardians/vocabulary.anthill`
was written to answer "where are these definitions?". The first agent written
against it — `send_email(body: summarize(fetch_mail(box)))`, the obvious
spelling — loaded clean. The smoke tests had never caught it because they used
one sort throughout. **A vocabulary of one sort cannot exercise a sort
mismatch**, and every run in group A was written that way.

**Mitigation until it is fixed.** Every label-polymorphic operation must be
reachable only through arguments of exactly its declared sort. In the
vocabulary that means an explicit `bodies_of(List[Message[?t]]) ->
List[Text[?t]]` projection, and with it the attack is refused:
`expected Text[Trust = Public], got Text[Trust = Untrusted]`. That is a
discipline on the trusted declarations, not a fix — the typer should reject the
mismatch.

## C8 · A spec operation with `ensures` had no possible provider · **FIXED**

**Scenario.** Write the tier-2 obligation the design most wants —
`ensures mentions_all(result)` on `Triage.run` — and give it an implementation.

**Refused, and refused for every implementation:**

```
error: 'Impl' overrides 'Spec.run' but does not refine it: it weakens the
       postcondition — the override does not `ensure` a condition the spec
       operation promises
```

even when the override's `ensures` was **syntactically identical** to the
spec's. So a spec operation carrying a postcondition could not be implemented
at all.

**Isolated by one control.** An `ensures` over a **parameter** refines fine; an
`ensures` over **`result`** never does. That pinned it: `result` is defined per
operation as `<op>.result` with `SymbolKind::OpResult` (proposal 041), so the
spec's and the override's are distinct symbols, and the override-refinement
check's `align` map zipped **parameters only**. The comparison was
`Spec.run.result` against `Impl.run.result`, which are never structurally equal.

**Fixed** in `anthill-core/src/kb/typing.rs` by aligning the result binder the
same way parameters are aligned. Two controls hold: an `ensures` over a
parameter still refines (no regression), and a genuinely *different*
postcondition is still refused (the check still does its job). Scope: this
aligns the reserved name on both sides; an override that *renames* its result
binder is still not recognized, which needs the declared name the table does not
carry.

**Why it went unnoticed.** `ensures` on a spec operation is rare, and the
failure only appears once something *provides* that spec. The example's task
specification is exactly that shape, which is how it surfaced.

## C9 · A `Modify[p]` target is not compared by the refinement check

**Scenario.** While building the row-widening fixture: an override declaring
`{External, Model, Error, Modify[box]}` against a spec declaring
`{External, Model, Error}`.

**Loads clean.** A named effect (`Filesystem`) in the same position is refused
loudly, so the widening check works — it just does not treat a `Modify` target
as a widening. Not chased further; the example's fixture uses a plain label
instead, and this is recorded rather than diagnosed.

---

# Summary

| | run | verdict |
|---|---|---|
| A1 | label enforced at a sink | ✅ fires |
| A2 | label survives `summarize` — **the attack** | ✅ fires |
| A3 | widening is one-directional | ✅ fires |
| B1 | provision must back the member | ✅ fires |
| B2 | declared row may not widen the spec's | ✅ fires |
| B3 | body may not exceed its declaration | ✅ fires |
| B4 | reshaped member does not evade B2 | ✅ fires |
| C1 | signature conformance | ❌ **gap** (WI-935) |
| C7 | sort mismatch vs a variable-containing type | ❌ **defect** — launders the label |
| C8 | a spec op with `ensures` had no provider | ✅ **fixed** in `kb/typing.rs` |
| C9 | `Modify[p]` target vs the refinement check | ❌ not compared |
| C2 | `requires` gating a call site | ❌ by design (§8.5) |
| C3 | rule body reading a type argument | ❌ WI-742 |
| C4 | variance in the label slot | ⚠️ **corrected** — declarable via `Covariant` + a provides-chain |
| C5 | computed region in `Modify[…]` | ❌ type position |
| C6 | type argument on a constructor | ❌ and desirable |

**C7 is the one that changes the picture.** A1–A3 and B1–B4 are real and hold,
but A1–A3 were all written over a single sort, and C7 is invisible to any test
built that way. The design still works — with an explicit projection at every
sort boundary — but it works by *discipline in the trusted declarations* rather
than by the typer, and that is a weaker claim than the one this record made
before the vocabulary was written out. Fixing C7 is now ahead of C1.

**C8 was found by writing the design's own obligation down and fixed in the
kernel** — the postcondition it blocked, `ensures mentions_all(result)`, is the
concealment half of the article's attack, so the defect sat exactly on the path
this example most needed. It is a small argument for building examples: the gap
was invisible to a suite where no spec operation carries `ensures`.

**A1–A3 and B1–B4 together are the design.** Data confinement and capability
confinement are checked by independent mechanisms, each with an unbroken chain,
and both hold on the current loader with nothing built. C1 is the one item on
the critical path; C2–C6 shaped the design rather than blocking it.
