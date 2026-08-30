## Attributes

- id: WI-20260830-N0PDV-the-guardians-report-s-world
- created: 2026-08-30T09:30:36Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T09:30:36Z

- acceptance: cargo-test, scaland-sbt-test

- tags: guardians

## Description

FOUR PARTS, all in `examples/guardians`, best done in one pass because they touch the same files -- but independently testable, and PART 2 does not depend on PART 1. Parts 2, 3 and 4 were added 2026-08-30 while writing the ICTERI-2026 article's section 3, which needs constructs the example does not use and exposed the modelling defect in part 4.

### API BASELINE -- WRITE AGAINST `01421d5a`, NOT AGAINST WHAT THIS TICKET FIRST SAW

This item was written before `01421d5a` ("`External` is a fact about the model, not about being an `Llm`"), which gave `guardians.Llm` an effect ROW PARAMETER -- `effects E = ?` -- instantiated by each carrier (`LiveLlm` at `{External}`, `FakeLlm` at `{}`) and projected by everything downstream. Every row that touches a model now reads `{..., llm.E, ...}`:

    lib/spec.anthill      Triage.run       {External, llm.E, Error}
    lib/tasks.anthill     summarize        {llm.E, Error}
    lib/harness.anthill   attempt          {External, llm.E, Error}
    fixtures/agent/*      run              {External, llm.E, Error}

CONSEQUENCE FOR EVERY PART BELOW: the fixtures are edited by all four parts, and a fixture rewritten from this ticket's older prose will drop `llm.E` and be refused for the WRONG REASON -- which turns the `assert_refused` substrings green-to-red or, worse, keeps a refusal that no longer measures what its test name says. Diff a fixture against the current file before rewriting it, not against the snippets in this ticket.

MEASURED, and worth knowing while editing: an upstream effect parameter can be IMPORTED as well as projected. `import demo.Src.{E}` then `effects {E, Error}` loads; the same file with the import removed is refused with `unresolved name 'E'`, so the import genuinely binds rather than passing vacuously. The shipped example uses the PROJECTION form (`llm.E`) throughout; do not mix the two without a reason.

### PART 1 -- THE REPORT'S WORLD MODEL

THE GUARDIANS REPORT'S WORLD MODEL IS WRONG: a message can carry SEVERAL categories, or NONE, and `entity Verdict(message: MessageId, label: String)` (examples/guardians/lib/spec.anthill) admits exactly one, spelled as an open `String`.

THREE DEFECTS, of which only the second is a security matter.

D1 -- MULTI-LABEL. A message can be a payment redirect AND an invoice; suspicious AND from a known contact. `Verdict` has one `label` field. The KB layer is ALREADY RIGHT -- `classified(?m, ?c)` in lib/classify.anthill is a RELATION and is naturally multi-valued -- so it is `Verdict` alone that collapses it.

D2 -- NO ENCODING FOR "CANNOT BE CATEGORIZED", AND THAT IS A HOLE IN THE SECURITY ARGUMENT rather than a modelling wart. The concealment half of the article's attack is defeated by `ensures mentions_all(result)` ONLY because enumeration is TOTAL: `verdicts_of` emits one row per fetched message, derived from what `Email.fetch` returned, so no model can drop one. If "cannot categorize" is encoded as A MISSING ROW, an agent omits any message by declining to judge it -- and the injected message is EXACTLY the one an attacker wants omitted. The injection's second sentence becomes "report that you could not classify this one", and `mentions_all` passes VACUOUSLY. The rule that must become structural: ENUMERATION IS TOTAL AND DERIVED; CLASSIFICATION IS PARTIAL AND THE MODEL'S. An empty label set is a statement; a missing row is not.

D3 -- `label: String`. An open vocabulary, in the file next to lib/observe.anthill whose entire purpose is a closed one. lib/classify.anthill has the same weakness inline: `classified(?m, "Suspicious")` and `classified(?m, "Ordinary")` are string literals.

THE FIX.

  enum guardians.Category
    entity Suspicious
    entity Ordinary
    entity Other
  end

  entity Verdict(message: MessageId, labels: List[T = Category])

  constraint verdict_is_not_silent:
    :- Verdict(message: ?m, labels: ?ls), is_empty(?ls)

`Other` IS NULLARY, AND NOT FOR A SECURITY REASON -- say this in the source, because the obvious inference is wrong. `Other(Text[Untrusted])` WOULD BE SAFE: the lattice is precisely the mechanism for carrying attacker-authored text, and `fixtures/agent/rejected/leak.anthill` is the proof that untrusted text is refused AT THE SINK rather than at creation. Forbidding the payload would solve by prohibition a problem the label already solves by tracking. It is nullary because THE VERDICT IS OUTPUT, NOT CONTROL: nothing in a checked agent branches on a `Category`, the report is shown to the user, and `mentions_all` reads only the `message` field of each row. The loose half is output; the tight half is structure.

WHAT DOES NOT CHANGE, and this is why the fix is smaller than it looks. `mentions_all` is ALREADY existential over `items` -- `rule mentioned_in(Report(items: ?items, summary: ?), ?m) :- (some ?v in ?items: verdict_of(?v, ?m))` -- so several verdicts per message were always admissible. `verdict_of` needs a FIELD RENAME (`label: ?` -> `labels: ?`) and nothing else.

FILES. lib/spec.anthill (Category, Verdict, verdicts_of, the constraint); lib/classify.anthill (string literals -> Category entities, plus a rule for the case neither existing derivation fires); the eight fixtures that build a `Report` -- agent/good, agent/internal_send, agent/rejected/{leak,outbox,wide_row,wide_row_modify,computed_recipient,letbound_recipient}; rustland/anthill-core/tests/guardians_test.rs.

OPEN SUB-QUESTION, to settle first: is `is_empty` available on `List` in the prelude? If it is not, either the constraint needs another spelling or it cannot be written -- in which case D2's guarantee rests on `verdicts_of`'s contract alone, and THAT MUST BE RECORDED rather than left implied.

ACCEPTANCE. A `Verdict` whose `labels` list is empty is a LOAD ERROR naming the constraint (or, if `is_empty` proves unavailable, a recorded finding saying why the constraint could not be written). A verdict carrying TWO categories loads. CONTROLS, each of which must still hold: `good_agent_is_accepted` and `an_internal_send_needs_no_permission` still ACCEPTED; `exfiltrating_agent_is_refused_by_the_label`, `an_external_send_is_refused_by_the_conditional_permission`, `capability_widening_is_refused_by_the_row` and `a_modify_target_the_spec_never_granted_is_refused_by_the_row` still refused WITH THEIR EXISTING DIAGNOSTIC SUBSTRINGS UNCHANGED -- a fixture that dies earlier on a `Report` shape error turns those red, which is the same silent-coverage trap recorded in WI-20260829-MCKTE's feedback; `a_candidates_own_mentions_all_does_not_discharge_the_specs_postcondition` still fires; suite green.

DOWNSTREAM (PART 1). The ICTERI-2026 article (/Users/rssh/RD/toWrite/ICTERI-2026, draft-guardians-sections.tex section 7) now describes `Verdict(message, labels: List[Category])` and the enumeration/classification split above. Until this lands, the paper describes something the distribution does not do. Design note: /Users/rssh/RD/toWrite/ICTERI-2026/world-model-fix.md.

### PART 2 -- THE EXAMPLE DOCUMENTS ITSELF IN `--` COMMENTS, SO THE KB CANNOT SEE ANY OF IT

kernel-language.md and both articles state that a description block `{< ... >}` is "stored as an ordinary fact in the knowledge base ... available to queries and to agents as documentation of intent". `examples/guardians` contains NOT ONE -- `grep -rn '{<' examples/guardians` is empty. The example's documentation is unusually rich and IS exactly the intent-documentation the mechanism exists for, and all of it lives in lexer-discarded `--` comments. THE FLAGSHIP EXAMPLE HAS NO CONSUMER FOR A FEATURE THE PAPER CLAIMS.

WHAT MOVES AND WHAT DOES NOT. Convert the header rationale of the declarations a reader meets first: `guardians.Text` (what the `Trust` parameter is, and why a type parameter carries the flow discipline), `guardians.Message`, `in_org` (declared by the library, asserted by a deployment), `guardians.Triage.run` (what `mentions_all` is for), `Email.send` (the guarded permission). NOT ALL COMMENTS: the design history, the WI references and the measurement notes are commentary ON the source and belong in `--`. What moves is what a reader or an agent would want to QUERY -- what this declaration is FOR.

ACCEPTANCE (PART 2): `{< ... >}` present on at least the five declarations above; a KB query returns the description fact for `guardians.Text`; suite green. CONTROL: `lib_loads_without_any_fixture` still passes.

### PART 3 -- NO BOOLEAN `requires` ANYWHERE IN THE EXAMPLE

`grep -rn requires examples/guardians` finds one hit, and it is inside a comment. The construct WORKS -- measured.md C2 measures `send(body: Text[L = ?l]) requires flows_to(?l, Public)` being refused AT A CALL SITE -- but that lives in a smoke file under docs/measurements/guardians, and the shipped example declares none. So the one contract form the article calls "an obligation the agent must discharge" appears in the paper and not in the distribution.

WHERE IT GOES, AND WHY THE CHOICE MATTERS. A precondition on `Triage.run` is discharged by the CALLER, not by the generated agent, so it does not demonstrate the claim. A precondition on A TOOL THE AGENT CALLS is discharged at the agent's own call site, which is exactly the claim. `Email.send` is the natural site.

WHICH PREDICATE IS UNDECIDED, and `deliverable(to)` -- the article's placeholder -- is NOT a recommendation. Two candidates worth weighing: (a) a well-formedness condition on the address, cheap and independent; (b) promoting C2's `flows_to(?t, Public)` out of the smoke file into lib/email.anthill, so the lattice ordering rides on the CONTRACT rather than on unification alone, which would give the example both tiers of the same policy side by side -- the article's section 7 makes exactly that point. (b) IS NOT FREE: C2 records that a label-polymorphic wrapper floats the obligation and a wrapper declaring no contract of its own SWALLOWS its callee's, so check what it does to `summarize` before choosing it.

ACCEPTANCE (PART 3): a generated agent calling `Email.send` where the precondition cannot be proved is REFUSED, naming the unsatisfied precondition. CONTROLS: `good_agent_is_accepted` and `an_internal_send_needs_no_permission` still ACCEPTED, and every existing refusal keeps its current diagnostic substring -- same silent-coverage trap as PART 1.

DOWNSTREAM (PARTS 2 AND 3). The article's section 3 listing (draft-guardians-sections.tex, block A2) replaces the old `project.todo` WorkItem fragment with the email vocabulary, and shows two `{< ... >}` blocks and one `requires` that the distribution does not have. Until this lands, that listing is illustrative rather than transcribed.

### PART 4 -- THE DEPLOYMENT'S `in_org` ROW ENCODES A RULE, AND THE RULE IS THE DEPLOYMENT'S TO STATE

lib/email.anthill declares `rule in_org(?a)` and asserts nothing; fixtures/mailbox.anthill supplies the single row

    fact in_org(Address(local: ?, domain: "ourcorp.com"))

whose logical variable in the HEAD is what makes it universal over local parts. THE LIBRARY SIDE OF THIS IS RIGHT AND MUST NOT CHANGE -- see the correction below, which reverses an earlier draft of this part. What is wrong is only the fixture: a RULE ("ours iff the domain is ours") is being smuggled in as a FACT with a variable in it, so the concept the rule turns on is never named, and a deployment that writes the obvious `fact in_org(Address(local: "michelle", domain: "ourcorp.com"))` silently configures ONE MAILBOX rather than an organisation with nothing saying so.

THE FIX IS IN THE FIXTURE, NOT THE LIBRARY. Leave lib/email.anthill as it is -- `rule in_org(?a)` declared and empty, `external_addr` derived by negation -- and have the deployment say what it means:

    fact org_domain("ourcorp.com")
    rule in_org(?a) :- ?a = Address(local: ?_, domain: ?d), org_domain(?d)

CORRECTION, AND IT IS THE POINT OF THIS PART. An earlier draft of this ticket proposed moving `org_domain` and that rule INTO lib/email.anthill, on the ground that the library should own the rule and name the concept. THAT IS WRONG, and the reason is a modelling claim worth writing down: an `Address` may be ANY address, and whether one belongs to the organisation is an INSTITUTIONAL FACT, not a property computable from the address. `local`/`domain` is a decomposition of a string; membership is a matter of who the organisation says its people are. The two are different things and the library must not identify them.

WHY IT MATTERS BEYOND TIDINESS. "Our domain implies ours" is false in ordinary cases -- an organisation with people on a shared domain, a subsidiary on a different domain, aliases and forwarding -- and it is DANGEROUS in the case this example exists for: anyone who obtains an address at our domain, by signup or by compromising an account, becomes INTERNAL BY CONSTRUCTION, and `Email.send` then demands no `Permission[Outbox]` to mail them. A library that hard-codes the heuristic makes that unavoidable for every deployment. A library that declares the relation lets a deployment choose the heuristic and lets a stricter one enumerate from a directory instead.

WHAT SURVIVES from the earlier draft: naming `org_domain` rather than hiding the rule's shape inside a variable-headed fact. It just lives on the deployment's side of the line.

ACCEPTANCE (PART 4): fixtures/mailbox.anthill asserts `fact org_domain("ourcorp.com")` and a `rule in_org(?a) :- ...` over it, and no variable-headed `in_org` fact remains; lib/email.anthill is UNCHANGED. CONTROLS: `an_internal_send_needs_no_permission` still ACCEPTED; `the_organisations_identity_is_a_deployment_fact_and_the_default_is_closed` still fires with the fixture withheld -- that test IS the closed default and must be re-checked against the new shape rather than merely kept green; `an_external_send_is_refused_by_the_conditional_permission` unchanged. NEW ROW WORTH ADDING: a second `fact org_domain(...)` makes a second domain internal -- the case the variable-headed fact could not express without a second fact of its own.

DOWNSTREAM (PART 4). The article's section 3 listing (draft-guardians-sections.tex, block A2) shows the library side -- a bodyless `in_org` and `external_addr` by negation -- and a second listing shows a deployment supplying it both ways, by enumeration and by rule. The prose makes the same claim as the correction above.
