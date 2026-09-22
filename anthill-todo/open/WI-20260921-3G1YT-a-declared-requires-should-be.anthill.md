## Attributes

- id: WI-20260921-3G1YT-a-declared-requires-should-be
- created: 2026-09-21T14:16:49Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T14:16:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

**THE ORIGINAL CLAIM STANDS: a declared `requires` IS owed by the caller because it is
declared.** It was refuted twice on the way, and BOTH refutations were wrong; they are
kept below because each looked decisive and a later reader will reach for them again. What
is left is to implement the claim. Defects (2) and (3) of the original text are DELIVERED
(see their section); defect (1) is what remains, and it dissolves under the rule rather
than needing a language change.

### The rule

An obligation is DISCHARGED by any of FOUR routes, and every one is readable from the
signature and the call site — none needs the callee's body:

 1. **the caller's own `requires`** — the ordinary forward;
 2. **value-direction** — the spec has an operation taking its own carrier, so a runtime
    value can name a provider ([`spec_has_value_directed_route`]);
 3. **resolver search** — the call pins a concrete element, so a goal built from it can
    match a provider fact ([`dep_has_searchable_pin`]);
 4. **A SPEC-TYPED PARAMETER** — a parameter typed at a spec CARRIES that spec's `requires`
    chain, by the spec's own contract. `operation total(c: FiniteCollection) = size(c)`
    owes `Iterable[…]` and HOLDS it, because `c`'s type says so. NOT YET IMPLEMENTED.

A call is refused when a clause is declared and NO route discharges it. No body walk, and
no marker — see the two dead ends below.

### The body walk is an EXCUSE, not information

`op_body_reads_sort_requirement_slot` / `op_body_reads_op_requirement_slot` walk the
CALLEE's body to decide whether THIS call is legal. The cost is stated exactly by
`wi_xsvcs`'s own fixture, two bodies under ONE signature:

```
operation tyOf[B](x: B) -> Type requires TT[T = B] = TT.valueOf()   -- refused
operation tyOf[B](x: B) -> Type requires TT[T = B] = Boom           -- loads, answers
operation mid[U](y: U) -> Type = tyOf(y)                            -- the caller
```

`mid` should be refused BOTH times. The second `tyOf` declares a clause it never uses; the
repair is to DELETE the clause, and MEASURED, that repair loads clean (4237 facts, 433
rules). The walk exists only to excuse that declaration, and its price is that a callee's
body decides its callers' obligations — which is defect (1).

### What is measured, and what blocks it

On `-p anthill-core`, from the delivered tree:

 - **both body walks removed, no fourth route — 28 FAILED.**
 - **plus a LOOSE fourth route — 19 FAILED.** The whole `n01py` family and several
   `x13yv` rows are DISCHARGED rather than excused, which is the shape of route 4 exactly.

TWO KNOWN BLOCKERS, and the probe is in the scratchpad (`typing.fourthroute.rs`):

 1. **The cover must be BINDING-AWARE.** The probe matched on the spec SORT alone, and 2
    of its 19 are that looseness biting — `wi456 …an_undeclared_ordering_is_refused_at_load`
    and `…the_refusal_names_the_repair_and_not_a_witness_choice` are refusals it wrongly
    silences. The contract must be shown to cover THIS dep, bindings included.
 2. **The dep's carrier binds to the SPEC VIEW, not to the value's carrier.** At `size(c)`
    the dep reads `Iterable[C = FiniteCollection[C = XC, …], …]` where `XC` is
    `ExprCarried[value = c, member = C]`. `FiniteCollection`'s own chain instantiated at
    `c` is `Iterable[C = XC, …]`. They do not match, so even a binding-aware cover fails
    until the admission of a spec-view value at its own carrier parameter binds `C` to the
    value's carrier rather than to the view.

### TWO REFUTATIONS THAT WERE THEMSELVES WRONG

**"The 84 dropped refusals prove declared ⇏ owed."** They do not. They are OWED AND HELD,
by route 4 — the evidence is in the parameter's type and the search never looked. The
census stands (143 parked, 100 dropped; `FiniteCollection.size` 37, `MappedStream.map` 31,
`FilteredStream.filter` 16) but its reading was wrong.

**"A `requires` has TWO ROLES — a static constraint and a runtime dictionary — and the gate
separates them."** RETRACTED. That framing was built on the misreading above and on a trace
showing no dictionary is installed at those calls. No dictionary is installed because
value-direction supplies the capability, which is a route DISCHARGING the obligation, not
evidence that none was owed.

**AND A MARKER IS NOT NEEDED.** A signature-level marker distinguishing "consumed" from
"constraint only" was designed and costed (26 sorts declare a sort-level clause, 3 consume
it; 24 ops declare an op-level one, 7 consume it). It is unnecessary: the distinction it
would draw exists ONLY because the body walk excuses unused clauses. Remove the excuse and
there is nothing for a marker to say.

### Defects (2) and (3): DELIVERED

Both are done and committed; kept here because each was refuted once before it was fixed,
and because (3)'s rule is the one route 4 completes. Defect (1) is NOT in this section —
it dissolves under "the rule" above: once a caller's verdict follows from the four routes,
a callee's body no longer decides it, and there is nothing left to declare.

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

THE SORT HALF IS DONE TOO (2026-09-22). An earlier cut left it hardcoded because the
general rule needs the CALLEE'S OP to ask `op_body_reads_sort_requirement_slot` and
`build_dispatching_dict_from_chain` is handed the callee's SORT. A `rule_body_callee:
Option<Symbol>` parameter now plumbs that op through — `Some` at a RULE-body site and
`None` at the three that cannot act on the verdict (an operation-body site PARKS instead;
the eta route's `Ok(None)` is already a load error; the Direct path is diagnostic-only).
BOTH hardcodes are deleted and `type_value_forward_unsuppliable` is gone.

AND THE RULE NEEDED A THIRD CONDITION, which the FULL WORKSPACE caught after every
targeted test passed. "No value-directed route" is not enough: the SLD bridge resolves a
GOAL, and a goal can be answered from a pinned ELEMENT even where no value names a
carrier. `nx4fd_disc.Marked` declares only the nullary `code()`, yet
`Ghost.probe(alpha(), ?x)` pins `M = Alpha` and the resolver completes `N = Beta` off
`Alpha provides Marked[M = Alpha, N = Beta]`. So the dep must ALSO carry nothing
searchable — `dep_has_searchable_pin`, read at `rigid_ok = false`, because a `Var::Rigid`
is determined but ABSTRACT and no provider fact can match it. That is precisely the
contrast with `Stamp[T = B]` at the caller's own rigid, which nothing can ever supply.

THE THREE RESCUE ROUTES, stated once: a value's carrier (value-direction), a pinned
concrete element (resolver search), and the caller's declared `requires` (the ordinary
forward). A rule-body site is refused only when ALL THREE are unavailable and the
callee's body reads the slot.

WHAT LANDED — full workspace **7265 passed / 0 failed**:
 - `type_value_forward_unsuppliable` and BOTH its call sites DELETED; the rule is keyed
   on a spec's shape in both halves, and `TypeValue` is an instance of it;
 - `wi_n31xx …a_sort_level_user_typeclass_is_refused_too` + its receiver control, and
   `…a_nullary_spec_with_a_pinned_element_still_loads` — the counterexample control;
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

### ACCEPTANCE

 - route 4 is implemented with a BINDING-AWARE cover, and blocker 2 is either fixed or
   stated as still open with its own row;
 - both body walks are gone, and with them `SlotToRead`, `native_backing_reads_slots` and
   the `if !reads { continue; }` gate;
 - `mid` above is REFUSED against BOTH bodies — DRIVEN, in one test, with the two bodies
   side by side, which is the row that says a callee's body no longer decides its callers;
 - `wi_xsvcs …a_slot_the_callee_never_reads_still_loads_and_answers` is repaired by
   DELETING its dead clause rather than by weakening the rule, and says so at its site;
 - the rows that only change WORDING are named as such, each saying what it asserted
   before;
 - kernel-language.md §8.7 states the rule as the four routes;
 - full workspace green via rustland/scripts/test.sh. Scaland is NOT in scope — it has no
   typer, so none of this is mirrored there (checked).

### THE ORIGINAL CLAIM (VINDICATED — kept for the record)

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

> The CLAIM above holds. What this ticket got wrong was its own blocker analysis: it
> said the 84 refusals mean the clause "cannot be deleted", and read that as the rule
> being too strong. The clause indeed cannot be deleted — it is owed — and the 84 are
> DISCHARGED by route 4, not exempt from the rule. The named prerequisite ("inference
> that pins a receiver's sort parameters from the receiver's type") is not it either:
> for `map`/`filter` those params come from the RETURN type. The real prerequisite is
> route 4 plus the carrier-binding defect, both stated above.
