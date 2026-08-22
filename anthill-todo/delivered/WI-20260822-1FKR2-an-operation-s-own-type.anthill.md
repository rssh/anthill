## Attributes

- id: WI-20260822-1FKR2-an-operation-s-own-type
- created: 2026-08-22T12:29:21Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T18:10:07Z

- acceptance: cargo-test

## Description

AN OPERATION'S OWN TYPE VARIABLE DOES NOT THREAD THROUGH A CALL WHEN THE CALLER IS GENERIC IN IT, so no generic operation can be implemented in terms of another generic operation. Every one must be a primitive.

MINIMAL REPRODUCTION: docs/measurements/op-type-var-does-not-thread.anthill. Twelve lines, no specs, no dispatch, no information flow -- the identity delegating to the identity.

  namespace tv1
    operation idv(x: ?t) -> ?t
    operation via_bare(x: ?t) -> ?t = idv(x)
  end

  error: type mismatch in via_bare.return (op-return): expected ?t, got ?t
         (these render alike but are not the same type -- the difference is in
          a component this diagnostic does not print; please report it)

The diagnostic asks to be reported, which is a fair description of the state: the two types PRINT identically and compare unequal, so the difference is in a component the renderer drops.

THE NESTED FORM is the same defect one level in, and its message is the informative one:

  operation id(b: Box[?t]) -> Box[?t]
  operation via(b: Box[?t]) -> Box[?t] = id(b)

  error: expected Box[T = ?t], got Box[T = b.T]

"b.T" is the tell. The callee's variable is being resolved to a PROJECTION -- "the T of the argument b" -- rather than unified with the variable the CALLER declared. Whether the bare and nested cases share a root is the first thing to establish; the bare one prints no projection, which may mean the same mechanism with the rendering lost, or may mean two defects.

CONTROL, in the same file. The identical delegation with a GROUND caller loads clean:

  operation via_ground(b: Box[Int64]) -> Box[Int64] = id(b)

So the failure is about the CALLER's own polymorphism -- not about delegation, not arity, not the sort. Measured 2026-08-22: exactly the two marked cases fail and the control passes, which is what makes the two failures mean something.

WHERE IT WAS FOUND, AND WHY IT MATTERS BEYOND GENERICS-FOR-THEIR-OWN-SAKE. examples/guardians types information flow by putting a label in a type parameter, so the load-bearing shape is an operation that PRESERVES a label: f(x: T[L = ?l]) -> T[L = ?l]. That works at the EDGES, where a call site supplies a concrete label, and it is what makes the article's exfiltration a type error. It does not work in the MIDDLE: a library operation that is itself label-preserving and delegates to another cannot be written. So the property composes through the type checker but not through user-written library code, which is what any real pipeline is made of. `guardians.summarize` had to be narrowed from "?l in, ?l out" to monomorphic at Untrusted for exactly this reason -- a narrowing forced by this defect, not chosen.

RELATED, POSSIBLY THE SAME ROOT: WI-20260822-RKMD4 (an argument whose SORT differs from a parameter type containing a type variable is accepted silently, leaving the variable unbound). Both are a type variable in a parameter position failing to bind through a call; one is silent and one is loud. Establishing whether they are one defect is worth doing FIRST -- if they are, it is one fix.

SUPERSEDES a ticket filed earlier the same day under the framing "two label-polymorphic operations do not compose". That framing was too narrow -- this has nothing to do with labels -- and it carried a supporting claim that measurement disproved: it said the label slot is invariant and an n-point lattice needs O(n^2) coercions. anthill HAS variance, declared as facts (Covariant / Contravariant, stdlib/anthill/reflect/typing.anthill), and type_compatible has a "provides" arm, so a provides-chain lattice with a covariant parameter gives the ordering directly: widening loads, the dangerous direction is refused, and deleting the Covariant fact refuses the widening too (the third being what shows covariance is doing the work). docs/design/measured.md C4 carries the same wrong claim and needs the same correction.

ACCEPTANCE: both marked cases in docs/measurements/op-type-var-does-not-thread.anthill load. CONTROLS: the ground case in that file still loads; guardians' docs/measurements/guardians/d2g_leak.anthill is still REFUSED (the label must still be ENFORCED, not merely threaded); and guardians.summarize can be restored to "?t in, ?t out" with examples/guardians still refusing fixtures/agent/rejected/leak.anthill.

## Changes

### 2026-08-22T18:09:53Z — feedback — user

DELIVERED. ONE ROOT, BOTH CASES. The body check skolemized only TWO of the three families of type parameter that reach it — the operation's declared `[A]` brackets and its enclosing sort's parameters — so a variable the author wrote INLINE in a signature stayed a flexible `Var::Global` in the body. §5.4 ("Which variables the ∀ quantifies") already said such a variable is quantified; the implementation had never read that sentence at the body.

That one absence produced both reported symptoms, which is the answer to the ticket's first question. NESTED: a flexible variable is exactly what `SlotPosition::written_slot_is_unwritten`'s body answer reads as an OMITTED slot, so the unwritten-slot filler overwrote the author's `?t` with `UnwrittenFill::Projection`'s `b.T` while the return kept `?t` — `b.T` was the tell, and it named the mechanism. BARE: nothing rewrites a top-level variable, so the two sides stayed two distinct flexible Globals, which `types_compatible` has no arm for at all; the identical rendering was the whole diagnostic. Skolemizing RESTORES the premise `written_slot_is_unwritten`'s own doc states — "by then … nothing else is left flexible" — rather than adding a case to either reader.

WHERE: `inline_signature_type_params` (rustland/anthill-core/src/kb/typing.rs), reading the SHARED `signature_bound_vars` — the same set WI-1078 reads negatively (which return variables are existential) and WI-1083 reads positively (a ∀'s binder list). Anonymous `?` is excluded so it keeps taking the projection fill.

RKMD4 IS NOT THE SAME ROOT, checked first as the ticket asked. RKMD4 was `validate_arg_against_param` skipping a NOMINAL HEAD comparison at a call; this is the BODY check never quantifying a family of variables. They are neighbours — both "a type variable in a parameter position" — with disjoint mechanisms and disjoint fixes. RKMD4 shipped separately and its tests are untouched.

MEASURED.
* CORPUS, 194 `.anthill` files, baseline vs fixed, per-file and order-normalized: exactly ONE file changes semantically — this ticket's `docs/measurements/op-type-var-does-not-thread.anthill`, from two errors to a clean load. (`examples/guardians/lib/tasks.anthill` differs only in line numbers, from a longer comment.)
* WORKSPACE SUITE: 36 binaries, 5525 passed, 0 failed.
* BACK-OUT, as a MUTATION (`inline_signature_type_params` returning empty — every declaration still present, only the skolemization stopped): 6 of the 11 new rows fail, 5 pass either way by design. Stated at the test module's own header.
* BLAST RADIUS, instrumented rather than estimated: over all 194 corpus files exactly TWO operations reach a non-empty inline family — this ticket's own two. Every other inline-variable signature in the corpus (`LogicalStream.mplus`/`interleave`, guardians' `bodies_of`/`join_texts`/`prompt_with`) is BODY-LESS, and a body-less operation never reaches the pass.

IT IS ALSO A SOUNDNESS FIX, and this is the row that fails the OTHER way. `operation leaky(x: ?t) -> Int64 = sink(x)` with `sink(n: Int64)` LOADED CLEAN before: the body pinned the caller's universally-quantified variable, and the return type was `Int64` on both sides so nothing downstream re-asked. Now refused at `sink.n (op-arg): expected Int64, got ?t` — WI-392's "the body must hold for ALL" reaching the third family.

ACCEPTANCE.
* Both marked cases in `docs/measurements/op-type-var-does-not-thread.anthill` load; the whole file loads clean, and `wi1fkr2_op_type_var_threads_test::the_measurement_file_loads` reads that file so the record cannot drift from the loader. The file is rewritten as a REGRESSION fixture: each case keeps the diagnostic it used to give.
* GROUND CONTROL in that file still loads.
* `docs/measurements/guardians/d2g_leak.anthill` still REFUSED, unchanged: `send_email.body (op-arg): expected Text[Trust = Public], got Text[Trust = Untrusted]`.
* `guardians.summarize` restored to "?t in, ?t out": RUN, AND THE TICKET'S PREMISE THERE IS STALE. It is still refused — `summarize.return (op-return): expected Text[Trust = ?t], got Text[Trust = Untrusted]` — and correctly so, for a reason that is not this defect. The ticket says "`Llm.complete` is `Prompt[?t] -> Text[?t]`"; `lib/llm.anthill` records at length that this spelling WAS the signature for one revision, that it let a model MINT releasable text out of an empty prompt, and that the exploit is kept as `fixtures/agent/rejected/minting.anthill`. `complete` returns `Text[Untrusted]` for EVERY prompt, so a body ending in `llm.complete(p)` packs an Untrusted witness and cannot satisfy a universally-quantified `?t`. The INPUT half of the narrowing WAS forced by this defect and does now lift — `List[T = Text[?t]] -> Text[Untrusted]` loads, `good` still loads, all five rejected fixtures stay refused — and is left as written for the reason the file already gives (the summarizer only ever sees Untrusted mailbox text; `llm.anthill`'s own rule is "write no variable where no relationship exists"). The false claim in `tasks.anthill` — "two label-polymorphic operations DO NOT COMPOSE" — is corrected there with what actually forces the return.

WHAT THE FIX DOES BUY THE GUARDIANS SHAPE, since the summarize control could not show it: a label-preserving LIBRARY operation in the MIDDLE of a pipeline now type-checks (`summarize(t: Text[L = ?l]) -> Text[L = ?l] = upcase(t)`), the leak through it is still refused at the sink, and the Public flow still loads. That is the property the ticket said composes through the type checker but not through user-written library code. Recorded as C10 in `examples/guardians/docs/design/measured.md` — a record the measurement file already referenced and which did not exist.

C4 NEEDED NO CORRECTION: `examples/guardians/docs/design/measured.md` C4 already carries it, marked **corrected**, with the three-row variance measurement including the deleted-`Covariant` control. There is no top-level `docs/design/measured.md`.

/code-review (high) FOUND THREE, ALL ACTED ON, and the first was a real ONE-NAME-TWO-QUESTIONS defect I had reasoned my way into. `signature_bound_vars` also walks `OpInfoRecord::requires`, and §5.4 says that list holds TWO KINDS of item — a type precondition (`requires Ord[T]`, whose variable is a type parameter) and a VALUE precondition (`requires p(x, ?v)`, whose variable names no type), mixed within one clause since the split is per conjunct. Reading the field whole would mint a KB-lifetime rigid for a value-precondition variable and push it into `TypingEnv::param_rigids`, which `constrained_param_receiver_type` reads as its PRECISION gate. I now pass an empty `requires` slice — one argument, documented at both ends, so the three sources the two questions DO share cannot drift. Nothing is lost, measured both ways: a type precondition's variable this op could be checked against also appears in a parameter, and the requires-and-return-only shape is refused identically with and without. The other two were the doc premises the change invalidated (`TypingEnv::param_rigids`' "two scopes" and `constrained_param_receiver_type`'s "exactly the parameters in scope"), both updated. The review's fourth note — that an OUTER sort's parameter was excluded only by the coincidence that `sort A = ?` aliases mint a `?`-named var — is now structural: `enclosing_sort_param_vars` walks the whole qualified-name prefix chain. NOT DRIVEN, said at its site: instrumented, nothing produces an outer sort's canonical var in a nested member's signature (a human writes a `Ref`; WI-1082 fills only a SELF slot), so the guard replaces a coincidence rather than closing an observed hole.

DOCS. `docs/kernel-language.md` §5.4 and §"Expansion during unification" now state the rule for the WRITTEN spelling — the section stated it for an omitted slot, for `[T]` and for the enclosing sort's parameters, and stopped one spelling short. `docs/design/type-parameter-scoping.md` §2 listed TWO threading mechanisms; the third — a shared logical variable — is the one a library is written in, and is now listed with what it costs when it does not work.

RESIDUE, NOT FIXED AND NOT NEEDED HERE. `types_compatible` still has no variable arm: two distinct variables at the TOP LEVEL of a comparison answer `false` through the `_` fallthrough. The bare case is fixed by making both sides one `TermId`, which is the WI-1063 polarity design working (a parameter's variable is rigid in the body, a return-only one is opened per call, so a variable should be determined by the time it reaches the relation). Stated in the test module's "What is NOT here" so nobody reads its absence as an oversight.

