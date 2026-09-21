## Attributes

- id: WI-20260921-3G1YT-a-declared-requires-should-be
- created: 2026-09-21T14:16:49Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T14:16:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

**THE HEADLINE IS REFUTED. "A declared `requires` is owed by the caller because it is
declared" IS NOT THE RULE — measured 2026-09-21, after the ticket was filed.** What
survives is defect (1) alone, restated: the channel must stop being inferred from the
callee's BODY. The proposed mechanism — delete the `if !reads { continue; }` gate — is
wrong and must not be implemented.

DEFECT (2) IS CLOSED (28TAT, no live site). **DEFECT (3) IS FIXED** — the per-spec
exemption it named is deleted and replaced by a general rule, after two wrong attempts
that are recorded in its section because each looked right. The original text is kept
under THE ORIGINAL CLAIM so the refutation can be read against it.

### The measurement that refutes it

Gate removed on the current tree (28TAT and 159S9 have since landed): **6362 passed / 25
FAILED**, not the 4808/21 the ticket recorded.

`report_unsuppliable_requirements` instrumented to dump every parked refusal, whole
`anthill-core` suite, `--nocapture`: **142 parked, 100 dropped by the gate, 42 reported.**
The 100 dropped are NOT one shape, and 84 of them are three stdlib operations:

| callee | n | signature | slot |
|---|---|---|---|
| `anthill.prelude.FiniteCollection.size` | 37 | 35 construction + 2 unconstrained | Sort |
| `anthill.prelude.MappedStream.map` | 31 | unconstrained | Sort |
| `anthill.prelude.FilteredStream.filter` | 16 | unconstrained | Sort |

The remaining 16 are singletons across fixtures, including one the new rule would catch
CORRECTLY (`wi999.req.Poly.add` declares `requires Ring[T = R]` with no `Ring` provider
anywhere) and one it would catch wrongly (`wi999.prov.Impl` both requires AND provides
`Show[T = Impl]`; construction is reported cyclic).

### Why those 84 are not owed: no dictionary exists at that call

TRACED, not assumed, on `operation total(c: FiniteCollection) -> Int64 = size(c)`:

  * the call classifies `ConcreteApplyWithin target=FiniteCollection.size dict=false`,
    with `enclosing_sort = None` (a free operation);
  * so eval's `start_apply_same_sort` takes `inherit = false`, `dispatch_dict = None`,
    `op_dicts = []` and falls to `start_apply_with_op_slots`, which installs **no
    requirements channel at all**;
  * `size`'s body reaches `Iterable` by VALUE-DIRECTED dispatch — `collect(c)` and
    `Iterable.iterator` both classify `UnresolvedSpecOp`.

No dictionary is built, installed or read. The parked refusal is about a channel the
call does not use. `map` and `filter` are the same picture and their bodies say so at a
glance: `mapped(s, f)` and `filtered(s, p)`, single entity constructions
(`combinators.anthill`).

### The two roles, which "declared ⇒ owed" collapses

THE TICKET ALREADY CONTAINED THE CONTRADICTION. Its prescribed repair is "the repair for
such a body is to delete the clause it does not use", and of this very clause it says
"The clause is not noise — a mapped stream's source genuinely must be iterable — so it
cannot be deleted." Both cannot hold.

A `requires` clause has TWO ROLES:

  1. a STATIC CONSTRAINT that licenses the body's calls and types the value the body
     constructs — `FiniteCollection requires Iterable` is what makes `collect(c)` inside
     `size` well-typed, and `MappedStream requires Iterable` is what makes a `mapped(…)`
     value readable by `MappedStreamFinite`;
  2. a RUNTIME DICTIONARY the caller supplies and the callee reads by `__req_*`.

The read gate SEPARATES them and is therefore right about the 84: role 1 holds, role 2
is absent. "Declared ⇒ owed" collapses them and refuses all 84, prescribing the deletion
of three real constraints.

### Defect (2) closed, defect (3) FIXED; only (1) survives

**(2) — a body-less callee answers "reads nothing" — IS CLOSED.** WI-20260921-28TAT fixed
the OP half (`native_backing_reads_slots`, keyed on `Error.reify` exactly as the
interpreter keys its own boundary). The SORT half's arm still carries the refuted premise
IN ITS COMMENT ("a body-less op is also not a target this route reaches"), but it has NO
LIVE SITE: exactly ONE parked refusal in the suite has a body-less callee, and it is
`test.wi201.infer_explicit.useExplicit` — precisely the case 28TAT decided to withhold.
MEASURED: forcing that arm to `true` gives **6387 passed / 0 FAILED**, i.e. it changes
nothing. It is a comment defect, not a behavior defect.

**(3) — "the rule needed a per-spec exemption carved out of it" — IS FIXED, 2026-09-21,
after TWO WRONG ATTEMPTS.** N31XX's `type_value_forward_unsuppliable` was a bare
`dep.required_sort == anthill.reflect.TypeValue`. The ticket called that a wrong-rule
smell and was RIGHT; both attempts below are recorded because each looked like a
refutation of that and neither was.

ATTEMPT 1 — GENERALIZE ON NULLARITY, and it is genuinely refuted. The candidate general rule was "the dictionary is the
only carrier ⇒ no operation of the spec takes a receiver a value could be dispatched on",
read through eval's own `spec_call_runtime_carrier` pair (`self_receiver_param_index` /
`spec_carrier_param_candidates`) so load and eval could not disagree. MEASURED on
`-p anthill-core`, two cuts:
 - as stated — **42 FAILED**, sweeping up every MARKER spec (no operations ⇒ no
   receiver): all 16 `wi_9wvt7_error_reify_test` rows refusing `ErrorTag[T = <tuple>]`,
   and `eval_test::m3_float_comparison_and_max` refusing an ordinary `Eq[T = Float]`;
 - narrowed to exclude markers — **6 FAILED**, and those six are the refutation proper:
   `test.xsvcs.fwd.TT`, `wi1102.witnessrow.Lawful` and `nx4fd_disc.Marked` are non-marker
   specs with no value-directed route whose callers' bodies legitimately never read the
   evidence. NULLARITY DOES NOT IMPLY THE READ; THE LOWERING DOES.

ATTEMPT 2 — DELETE THE ARM OUTRIGHT, AND THIS ONE NEARLY SHIPPED.
MEASURED with it disabled: **6385 passed / 2 FAILED**, and both failures assert MESSAGE
TEXT while their programs stay refused — on which evidence the arm decided no verdict. It
does decide one. DRIVEN, the case no row covered:

```
operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
rule names(?x, ?t) :- ?t = tyOf(?x)
```

With the arm, REFUSED. Without it, LOADS CLEAN and dies at eval on an unbound
`__req_typevalue`. The suite stayed green at 7248/0 because **a refusal that becomes
silent fails no test.**

AND THEN THE USER ASKED THE RIGHT QUESTION: if `TypeValue` needs this, the same defect
must exist for any other typeclass. IT DOES. MEASURED — a USER typeclass of identical
shape:

```
sort Stamp
  sort T = ?
  operation stamp() -> Int64        -- nullary, exactly TypeValue's shape
end
operation stampOf[B](x: B) -> Int64 requires Stamp[T = B] = Stamp.stamp()
rule names(?x, ?n) :- ?n = stampOf(?x)
```

LOADED CLEAN, while the byte-identical `TypeValue` spelling was refused. Nothing is
special about `TypeValue` except that someone wrote a check for it.

### The general rule, and the pass order that shapes it

THE RULE. `OpSlotParkSite::for_call` exempts a RULE-body site on WI-945's reason — such a
goal reaches eval through the SLD bridge, which resolves provider dictionaries from the
CONCRETE ARGUMENT VALUES and suspends when it cannot. **That premise is value-directed,
and it fails exactly where no value can name the carrier.** So the exemption is lifted for
a dep whose spec has no operation taking its own carrier
([`spec_has_value_directed_route`], whose two readers are eval's own
`self_receiver_param_index` / `spec_carrier_param_candidates`, so a spec cannot be
dispatchable at eval and refused at load).

RAISED, NOT PARKED, AND THE PASS ORDER IS WHY. Widening the park gate did NOT work, and
the instrumentation is the record: `report_unsuppliable_requirements` runs BEFORE rule
bodies are typed, so a rule-body park lands in an already-drained queue and is dropped in
silence. `check_sorts`' own `debug_assert!` states the same constraint from the other side
("nothing may park after it") and cannot catch the case, because it runs before the
offending push.

WHICH IS ALSO WHY RAISING IS SOUND RATHER THAN BLUNT: parking exists because a callee may
be typed after its caller, and a RULE body is typed after EVERY operation body — so
`op_body_reads_op_requirement_slot` already has its answer at that site. A callee that
never reads the slot still loads, which is what keeps `test.xsvcs.fwd.TT`,
`wi1102.witnessrow.Lawful` and `nx4fd_disc.Marked` green.

A MARKER SPEC ANSWERS "HAS A ROUTE" and is benign. `Eq` and `ErrorTag` declare no
operations at all; the question is "can the bridge recover a provider?", and a marker has
nothing to recover — it is a proof obligation. Without that arm, 42 rows fail (all 16
`wi_9wvt7_error_reify_test` rows on `ErrorTag[T = <tuple>]`, and
`eval_test::m3_float_comparison_and_max` on an ordinary `Eq[T = Float]`).

THE SORT HALF IS NOT DONE, and /code-review caught the attempt. Deleting its arm too is a
REGRESSION: a SORT-level `requires TypeValue[T = U]` reached from a rule body is refused
at HEAD and LOADS CLEAN without it, and the workspace stayed green at 7252/0 because no
row covered that shape. The generic rule cannot be applied there yet — it needs the
CALLEE'S OP to ask `op_body_reads_sort_requirement_slot`, and
`build_dispatching_dict_from_chain` is handed the callee's SORT; raising on the spec
property alone over-refuses (6 rows, measured at the op half). So ONE hardcode remains,
with its own call-site note, and `wi_n31xx …a_sort_level_rule_body_forward_is_refused_too`
pins it. The sort half's OWN generic gap is PRE-EXISTING: a sort-level
`requires Stamp[T = U]` at a nullary user typeclass loads clean before and after.

REMAINING WORK, and it is the natural follow-up: plumb `callee_op` through
`build_concrete_dispatch_dict` / `build_dispatching_dict_from_chain` so the sort half can
ask the same two questions the op half now does, and delete the last hardcode.

WHAT LANDED — full workspace **7253 passed / 0 failed**:
 - the OP half's `type_value_forward_unsuppliable` call site DELETED and replaced by the
   general rule; `TypeValue` is an instance of it there. The SORT half's call site stays,
   for the reason above;
 - `wi_n31xx …a_user_typeclass_of_the_same_shape_is_refused_too` — the generic row, and
   `…a_user_typeclass_with_a_receiver_still_loads` — its control, which fails if the
   predicate is made to answer `false` for everything;
 - `wi_n31xx …a_rule_body_forward_is_refused_too` (+ its control), the `TypeValue`
   spelling of the same site, whose ABSENCE made the first deletion look safe;
 - the two rows that asserted 065's wording now assert the general wording, each saying
   what it asserted before;
 - an unbound var in type position renders `?` rather than `<term#23484>`
   (`format_term_for_goal`) — the reader was shown an interning id where the UNDETERMINED
   ELEMENT is the defect;
 - two dead-code removals found on the way: `SynthKey::Ref` (its producing head was
   retired by WI-20260902-CZJ2N; injectivity unaffected) and an unused `witness: Symbol`
   parameter. `anthill-core` builds warning-free.

### The restated change

STOP DECIDING THE CHANNEL FROM THE BODY. "Is this requirement consumed as a dictionary?"
must become a property of the DECLARATION, or be read off the call's already-computed
`CallClass`, rather than recovered by walking the callee's body in
`op_body_reads_sort_requirement_slot` / `op_body_reads_op_requirement_slot`. That is
stable under body edits — which is defect (1) — and it does not refuse the 84, because a
value-directed call is classified as one.

AND 37 OF THE 84 ARE WI-20260921-R10KC'S, not this ticket's. R10KC — "a spec default body
must receive its provision's dictionary, and must resolve a body-less sibling member by
PROJECTION out of it rather than by value-directed dispatch" — names exactly the
`FiniteCollection.size` population: `collect` is declared body-less ("Body-less; each
carrier provides it", `finite_collection.anthill`) and `size(c: C) = List.length(collect(c))`
is the spec default body calling it. R10KC's blast-radius paragraph says that route works
today only where the rebuild has a unique answer, "not because evidence travelled". If it
lands, those bodies receive the dictionary and this ticket must be RE-MEASURED: the 37
either read a slot that is then suppliable, or stop being parked at all. PREDICTED from
reading R10KC, NOT measured — it cannot be until R10KC lands.
The remaining 47 (`MappedStream.map`, `FilteredStream.filter`) are NOT R10KC's: their
bodies are `mapped(s, f)` / `filtered(s, p)`, entity constructions that read no
dictionary and never will. That half is this ticket's own residue.

ACCEPTANCE:
 - the decision is read from the declaration or the classification, not from a body walk,
   and the two body-walk predicates are gone or reduced to that reading;
 - a callee whose body is EDITED to stop reading a slot does not silently admit callers
   that were previously refused — DRIVEN, with the two bodies in one test;
 - its control: the same pair under today's rule, showing which verdict moved;
 - the 84 stdlib rows answer what they answer today, and the test says so by name;
 - the stale premise in the sort-half body-less arm's comment is corrected to what 28TAT
   measured;
 - kernel-language.md §8.7 states the two roles and which one the check is about;
 - full workspace green via rustland/scripts/test.sh; scaland `sbt testFull`.

### THE ORIGINAL CLAIM (refuted — kept for the record)

A DECLARED `requires` SHOULD BE OWED BY THE CALLER BECAUSE IT IS DECLARED, not because
the callee currently reads it. Decided by the user, 2026-09-21, during WI-20260921-28TAT.

THE RULE TODAY (kernel-language.md §8.7, last sentence of "Where the ambiguity error is
raised"). An unpinnable requirement at a call site is PARKED and reported only where the
callee will actually miss the dictionary — `report_unsuppliable_requirements`' `if !reads
{ continue; }` (typing.rs), asking `op_body_reads_sort_requirement_slot` /
`op_body_reads_op_requirement_slot`. It rests on a measurement recorded at the site: 29
stdlib bodies declare a chain and NEVER READ IT.

WHY IT IS WRONG. That measurement establishes those clauses are UNREAD, not that they are
UNOWED — and the repair for such a body is to delete the clause it does not use. Three
defects follow: (1) a caller admitted on the strength of the callee's PRESENT body breaks
when that body changes, with nothing at the call site having moved; (2) the "does the body
read it" test is a walk of the callee's body, so it answers "reads nothing" for a callee
that HAS no body — WI-20260921-28TAT hit exactly that with `Error.reify`, which is
body-less and implemented by the interpreter, and 23 unevidenced reify call sites passed
in silence; (3) the rule already needed one per-spec exemption carved out of it (N31XX's
"an unfilled `TypeValue` slot is NEVER benign"), which is usually the sign of a wrong rule
rather than a special case.

THE CHANGE. Delete the `if !reads { continue; }` gate, so every parked refusal is
reported. That also kills the machinery behind it — `op_body_reads_sort_requirement_slot`,
`op_body_reads_op_requirement_slot`, `SlotToRead`, and 28TAT's
`native_backing_reads_slots` — roughly 250 lines.

> Refuted above: defect (2) is closed, and deleting the gate refuses 84 calls that
> consume no dictionary. The ticket's own reading of the blocker — "SO THIS DEPENDS ON
> INFERENCE THAT PINS A RECEIVER'S SORT PARAMETERS FROM THE RECEIVER'S TYPE" — was also
> wrong twice over: for `map`/`filter` the sort params are pinned by the RETURN type, not
> the receiver's, and pinning them would not make the refusal right, because the callee
> reads no dictionary either way.
