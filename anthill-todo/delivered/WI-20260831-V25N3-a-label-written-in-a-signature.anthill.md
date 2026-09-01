## Attributes

- id: WI-20260831-V25N3-a-label-written-in-a-signature
- created: 2026-08-31T16:49:50Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-01T04:25:33Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A LABEL WRITTEN IN A SIGNATURE'S ROW TYPE-ARGUMENT IS JUDGED BY NOTHING — route C of WI-20260831-RSRP5's census.

RSRP5 established that an effect label is judged where the ROW is written, and closed two of the three routes there: a carrier's `provides Spec[E = {…}]` binding (`check_provision_row_bindings`) and a sort's bound alias `effects E = K`. The third — a row written as a TYPE ARGUMENT in a signature, `operation ask(s: Spec[E = {…}], …)` — has no gate at all.

MEASURED, both spellings loading CLEAN:

    operation ask(s: Spec[E = {Beep}], p: String) -> Out
      effects {s.E, Error} = Spec.go(s, p)              -- Beep is no registered Effect kind

    operation ask(s: Spec[E = {Modify[Thing]}], p: String) -> Out
      effects {s.E, Error} = Spec.go(s, p)              -- a TYPE-targeted Modify (§5.6)

The identical labels are REFUSED in an operation's own row and in a `provides` binding.

PRE-EXISTING, NOT OPENED BY WI-20260831-PYNS2, and that is measured rather than assumed: the same hole is drivable on the guardians `Llm` — `operation ask(m: Llm[E = {Error, LlmOutput}], p: Prompt) effects {m.E, Error} = Llm.complete(m, p)` loads clean today, and did before PYNS2, because `Llm` has two carriers and the route was already reachable there. PYNS2 widened WHICH specs the shape works on (one with no carrier yet); it did not create the gap.

WHY IT MATTERS. §5.5 now claims a row element is judged ONCE, AT ITS ORIGIN, so that a projection can be exempt. That claim is false for this origin, and every operation projecting `s.E` inherits an unjudged label — a misspelled kind reads as a new effect exactly as RSRP5 describes.

THE POPULATION IS THE WORK, and it is why this is not inline in PYNS2. `check_provision_row_bindings` walks `all_provisions`; this one has to census every TYPE POSITION where a spec application can bind a row parameter, not just a parameter's type — at minimum: an operation's parameter types and return type (`all_operation_params_and_effects` reaches both), an entity FIELD's type, a sort's own type-param binding, and a `requires Spec[E = {…}]` clause. Enumerate the producers before writing the gate; a list drawn from this ticket's two examples will be short (WI-20260830-APXSS).

The judging half is already built and shared: `effect_element_labels` + `classify_modify_target` + `registered_effect_kinds`, exactly as `check_provision_row_bindings` composes them, with the same per-slot dedup key and a message naming the written slot.

ACCEPTANCE: both fixtures above REFUSED, each naming the slot as written; a benign `E = {Error}` control that must still load; a control at a TYPE parameter binding (`Spec[C = Int64]`) that must NOT be read as an effect row (RSRP5's `a_type_parameter_binding_is_not_read_as_an_effect_row`, at the new site); and the census of type positions recorded, with a driven fixture per position covered and a named reason per position not.

## Changes

### 2026-09-01T04:25:39Z — feedback — user

DELIVERY RECORD. Rust 6244 passed / 0 failed (36 result lines); scaland 524 / 0, untouched — and that is measured, not inherited: `core/src/main/scala/anthill/` has no effect-label gate at all (no registration check, no `Modify`-target check, no registered-kind notion), and its only `EffectsRuntime` mentions are the parser/loader desugaring `effects E = ?`. Nothing to mirror.

THE CENSUS WAS THE WORK, AND IT WAS MEASURED, NOT ENUMERATED. I probed 20 candidate type positions with a bad label, then walked every live fact head, the const-type table and every op/const body of a corpus writing a row at each one, asking where the binding LANDED. Nineteen positions are drivable and every one of them LOADED CLEAN; the twentieth — an operation type-parameter DEFAULT — is refused before a row can be judged (nothing reads such a default), which is its named reason and is pinned by its own test so the exemption expires loudly.

THE FIX IS ONE PASS OVER THREE SOURCES, not a gate per position. `check_provision_row_bindings` became `check_written_row_bindings`; its judging half is RSRP5's, unchanged.

  1  ParameterizedSite (WI-835)   parameter/return types, entity fields, `sort S = …`,
                                  `const`, body `let`/lambda annotations, and any of
                                  those nested in a tuple, arrow, or another
                                  instantiation
  2  the three SPEC-CLAUSE facts  `provides`, a sort's `requires`, a provision condition
  3  OperationInfo requires/ensures   an op-scoped `requires Spec[E = {…}]`

THE BOUNDARY IS NOT A JUDGEMENT CALL. Source 1 is WI-835's registry, recorded at the type LOWERINGS — that ticket solved this same scope problem and its own doc records that ENUMERATING positions is what produced the mismatch it closed, so reusing it is the point. Source 2 is exactly `sort_inst_to_value`'s output: it is the one `TypeExpr::Parameterized` lowering that records no site (it assembles a `SortView`), and those three facts are what it emits. Source 3 is not a type lowering at all — an op-scoped `requires` list is OVERLOADED (spec requirements beside value preconditions), so the loader converts each item with the GOAL converter. Measured: with sources 1+2 alone, source 3's two spellings were the ONLY census positions still loading clean.

FOLDING THE PROVISION PASS IN CLOSED A HOLE IN ROUTE A ITSELF, which the census found and RSRP5 could not have: `provides Box[T = Spec[E = {Beep}]]` binds `Box`'s TYPE parameter, so the provision walk — filtered to the provided spec's own row parameters — never looked inside. It arrives as a SITE, and backing out source 2 leaves that test green, which is what dates it.

TWO THINGS THE CENSUS FORCED THAT THE TICKET DID NOT NAME.

  * `ParameterizedSite.bindings` recorded GROUND bindings only. One `denoted` element poisons a whole row to `Value::Node`, so `Spec[E = {Beep, Modify[clock]}]` dropped its entire `E` binding and the unregistered `Beep` beside the LAWFUL place went unjudged — measured loading clean, while the identical row in a `provides` clause was refused. ONE FIELD, TWO QUESTIONS: WI-835's "a denoted binding carries no `requires Spec[param]` obligation" is true of the Eq-key question and false of "what row did the author write". The field records what was WRITTEN now and each consumer filters by its own rule; `check_use_site_requires_eq` keeps its ground-only reading explicitly and is byte-identical.
  * An OPERATION's bracket parameter carries no `SortAlias`, so through the goal converter it arrives as an ordinary `SortRef` rather than a variable. Without §5.5's row-variable exemption asked of the LABEL, the prelude's own `map[…, EffS, …] requires Iterable[C = Sc, Element = S, E = EffS]` is refused and EVERY program that loads the prelude fails. Its own eight-line fixture is in the test file, so the reason is readable without reading a prelude combinator.

WHAT FAILS WHEN IT IS BACKED OUT — seven back-outs, one at a time, in the test file's header. Two earn their place by what they leave GREEN: backing out source 2 leaves the nested-in-provides test passing (so that row really is source 1's), and backing out source 1 leaves ALL SIX RSRP5 tests passing (so this ticket added an origin rather than changing the rule).

COST, measured rather than argued (release, guardians, min of 3): 0.13 ms with the spec-clause source alone — the shape RSRP5 shipped — and 0.42 ms with all three, against 0.15 ms for each sibling gate and 4.5 ms for `scan_definitions` on the same load.

/code-review RAISED FIVE FINDINGS. All five were MEASURED before acting, and one of them dissolved into a limit rather than a fix.

  1 (medium) VALID AND MINE. The source-1 doc claimed op-scoped `requires`/`ensures` lower through `type_expr_to_value` — false, and contradicted by my own source-3 back-out in the same file. Left standing, a maintainer deletes source 3 as redundant and every `requires Spec[E = {Beep}]` goes unjudged again with the suite green but for two census rows. Corrected.
  2 (low) VALID, AND IT CAUGHT A FIXTURE OF MINE ON ITS FIRST RUN. The census asserted presence while its own doc claimed a per-row COUNT. Tightened to exactly-once — which immediately failed row 02, whose fixture wrote the row at the parameter AND the return: two written positions, two correct refusals, and a useless census row. Rewritten as a body-less spec op so the return is the only occurrence.
  3 (low) VALID, MEASURED 1 -> 2. A sort writing the same bad label in `provides` AND `requires` reported ONCE, naming only the `provides`; same collapse for one operation's `requires` beside its `ensures`. The dedup key was the owner SYMBOL and the message carries the CLAUSE — so the key was coarser than the message. It is the rendered origin now, and `two_clause_kinds_on_one_owner_are_each_reported` pins both halves. RSRP5's own two-slot test stays green under that back-out: two axes, two tests.
  4 (low) A REAL GAP WHOSE PROPOSED REPAIR DOES NOT FIRE, and I built it before saying so. A fact-sourced refusal names no file. The suggested `functor_span` answers `None` for a sort and an operation symbol — it is keyed off a converted `Term::Fn` FUNCTOR, i.e. a name APPLIED in a body, not a declaration — and `rule_head_span`, which I tried next, is empty for a loader-EMITTED metadata fact. `term_span` on the `SortView` is not a third option: it is hash-consed and aliases across sites, so it would point at another file's identical clause. Recorded as a measured limit at the variant and in the test header rather than shipped as a branch that fires nowhere.
  5 (low) VALID, MEASURED, AND WORSE THAN STATED. Sources 2 and 3 walk the whole KB while source 1 is drained per load, so a `load_incremental` of a CLEAN file into a KB already holding an offending clause FAILED THAT BATCH over a file it was never given. Each clause fact is claimed once per KB now (`claim_row_binding_clause`), the same per-row cross-phase shape `resolved_requires_facts` has, and a re-presented file is still judged because it banks a fact with a new id (WI-1049). Pre-existing for source 2 since RSRP5; source 3 would have extended it to every operation.

SPEC. §5.5's judged-at-its-origin paragraph now LISTS every position that writes a row, and the "does NOT yet reach this third way" paragraph is deleted rather than softened. A new paragraph states the two positions outside the list and why each is outside: a hole and a row VARIABLE name no kind (the same exemption the projection has), and a bracket-parameter default is refused before a row is read.

