## Attributes

- id: WI-20260922-0DK3H-remove-runtime-dispatch-it
- created: 2026-09-22T07:56:43Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-22T11:29:57Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260922-QHDGC-require-spec-t-t-is-refused

- tags: typing

## Description

Remove runtime dispatch — it trades a LOAD error for a RUNTIME error

DECIDED BY THE USER, 2026-09-22, during WI-20260921-3G1YT: "we can't have runtime
dispatch because it is a runtime error instead of a loading error."

WHAT IT IS. `eval::spec_call_runtime_carrier` chooses WHICH implementation runs from
the ARGUMENT VALUE's carrier at reduction time, locating the receiver through
`self_receiver_param_index` (the self-representing shape, `Stream.head(s: Stream)`) or
`spec_carrier_param_candidates` (the carrier-param shape, `FiniteCollection.collect(c: C)`).

WHAT IT COSTS THE TYPER, which is why this is a typing ticket and not an eval one. Load
time cannot decide a call's legality, so the typer must either EXCUSE calls or APPEAL to
what eval will recover. WI-20260921-3G1YT deleted the excuses (two body walks, 428
lines) and, after the retraction in (1) below, deleted its own appeal too — route 4's
provision leg now decides by STATIC RESOLUTION. What is left standing is the RULE-BODY
pair:
 - `spec_has_value_directed_route` — "a value can name a provider";
 - `dep_has_searchable_pin` — "the resolver has something to match".
Both are runtime answers to a load-time question, and both are this ticket's subject.

AND THE APPEAL IS MEASURABLY UNSOUND, which is the argument for removing the pair rather
than tidying it. Asked at an OPERATION body, value-direction silenced SEVEN refusals
across `wi855`, `wi1102`, `wi999` and `wi_ckd4j` — ties among them. "A value CAN name a
provider" is true when there are TWO providers and when a conditional provision's
condition fails; a resolution separates `Resolved` / `Ambiguous` / `NoMatch` and a
value-directed route cannot.

MEASURED, THREE THINGS, on this tree.

 1. RETRACTED — THE STATIC SEARCH IS NOT INCOMPLETE. This ticket first claimed that
    `Iterable[C = List[T = Int64]]` answers `NoMatch` at load although
    `List provides Stream provides Iterable`, and named completing transitive provision
    resolution as the prerequisite. THAT MEASUREMENT WAS AN ARTIFACT OF THE PROBE. A
    `requires` clause is NORMALIZED by the loader to name every parameter, so a goal
    built from the CARRIER ALONE has no key for a candidate's `Element`/`E` bindings to
    match against. Re-measured with the dep's full key set and only the carrier swapped,
    the same carrier RESOLVES. There is no transitive gap and no prerequisite here.

    WI-20260921-3G1YT then replaced its own value-direction appeal with exactly that
    static resolution, so the shape this ticket was going to have to build is already
    built. What remains below is smaller than it looked.

 2. THE RULE-BODY CHANNEL IS ALREADY SUFFICIENT — NO LANGUAGE EXTENSION NEEDED. This
    refutes "a rule body has no frame to declare a dictionary in", which was asserted
    during 3G1YT and which proposal 060 already contradicted (`require[X]`, WI-1040).
    DRIVEN:

        rule described[A](?x: A, ?n) :-
          Desc[A], item(?x), require[Desc[T = A]], Desc.describe(?x, ?n)

    answers at TWO different carriers in ONE query (leaf -> 1, twig -> 2): one rule, one
    type parameter, two instantiations, two dictionaries, declared statically.

 3. ONE SPELLING OF THAT CHANNEL IS BROKEN, and it is WI-20260922-QHDGC's subject:
    `require[Spec[T = ?t]]` — the OPEN element — is refused at load, although a logical
    variable in type position is accepted in a bounding guard and as a head parameter
    type. That bug should be fixed FIRST: it is the natural spelling for a rule-body
    dictionary, and its absence makes the static channel look narrower than it is.

WHAT TO DELETE WHEN THE PREREQUISITE IS MET: the three appeals above, and with them the
last reason a caller's legality depends on anything but the two signatures and the
caller's scope.

OPEN, NOT MEASURED — the one remaining candidate for a shape only value-direction
reaches: WI-1057's instance-fact op-valued binding (`provides Desc[T = Leaf,
describe = leafDescribe]`), which has NO static pin, "so an operation body reaches it by
value and a rule body answers nothing". Measure it before scoping the removal; if it is
real it is either a second prerequisite or a stated exception, and either way it must be
decided rather than discovered.

ACCEPTANCE
 - transitive provision resolution answers `Iterable[C = List[T = Int64]]` at load,
   DRIVEN, with the stdlib combinator rows still green;
 - `spec_has_value_directed_route` and `dep_has_searchable_pin` are DELETED, and the rows
   that depended on each are named with what replaced them;
 - WI-1057's shape is measured and its verdict recorded here;
 - a program whose evidence is missing is refused AT LOAD, driven by a row that fails
   (dies at eval) when the change is backed out.

## Changes

### 2026-09-22T11:29:51Z — feedback — user

DELIVERED. The pair is gone, but it was THREE CLAIMS WEARING TWO NAMES, and the split is
this ticket's main finding rather than a detail of it.

  spec_has_value_directed_route  RECEIVER ARM  deleted, no replacement — it IS the runtime
                                               dispatch ("a value can name a provider")
  spec_has_value_directed_route  EMPTY-OPS ARM kept, as `spec_is_a_marker` — a LOAD-time
                                               structural fact, not an appeal to eval
  dep_has_searchable_pin                       replaced by
                                               `dep_completes_to_a_unique_provider`

THE MARKER ARM IS NOT RUNTIME DISPATCH, and deleting the function whole would have taken it
along. Its own doc made the argument: a spec declaring no operations "has NOTHING TO
RECOVER … an unfilled slot for one costs its callers nothing". That is decidable from the
declaration; nothing waits for a value. MEASURED as 7 rows — `wi625` x5 and `wi1098` x2,
all on `Eq` at `List.contains` — and the function's own note records 42 more
(`ErrorTag[T = <tuple>]`, `Eq[T = Float]`) from an earlier probe. Two claims under one
name and one `||` is why three tickets read the rescue as a single thing.

THE REPLACEMENT IS A PROOF WHERE THE OLD ONE WAS A HOPE. `dep_has_searchable_pin` asked
whether any element was GROUND — "so the resolver has a key to match on at fire time". It
admitted a program on the resolver HAVING a key, never on its FINDING anything.
`dep_completes_to_a_unique_provider` asks the same question of the provider FACTS, using
`unique_provider_completion` — which is `resolve_bridge_requirements`' own step, so the
load-time and fire-time readers cannot drift: facts only, a provider disagreeing on a
pinned element excluded, one leaving an element abstract declined, `None` on a second
surviving completion.

A BRANCH I ADDED AND THEN REMOVED, recorded because the reasoning was plausible and wrong.
`unique_provider_completion` answers `None` the moment nothing is open, so I added
`resolve_bridge_requirements`' `if all_pinned { goal }` beside it, reasoning that a fully
pinned dep would otherwise be refused although its goal resolves. Backing it out moved ZERO
rows (4886 pass either way): the case cannot reach the arm, because Strategy 3 inside
`build_dep_projection` has already answered it. A branch that cannot be driven is not in
the diff; the site says so.

#### THE STDLIB STOPPED LOADING, AND THE CAUSE WAS AN ASYMMETRY THE DELETION EXPOSED

The naive deletion failed 809 tests, all one root cause: three stdlib rule-body calls to
`PartialOrd.lt/gte/gt` could not prove `PartialEq[T = Int64]` / `[T = Timestamp]` — those
provision facts live in the per-language bindings (`anthill-stl/anthill/boundedint.anthill`),
not `stdlib/`.

THE FIX IS NOT A BINDING-FILE MOVE. `PartialOrd.gt/gte/lt/lte` are RESOLVER BUILTINS whose
default body — the thing carrying the `requires` — is never entered, so no `provides` row
would change the outcome. The op half already exempted them through
`OpSlotParkSite::for_call`'s `!kb.is_builtin`; THE SORT HALF NEVER ASKED. That asymmetry
was invisible because `dep_has_searchable_pin` happened to rescue the builtin shapes too
(`Int64`, `Timestamp` are ground). Deleting the rescue separated them. Site A now takes the
same exemption, and WI-855's "both spellings, one verdict" is restored rather than bent.

`wi1102`'s header carried the prediction that refusing here "takes the stdlib's own
`needs_rebuild` with it". RETRACTED AT ITS SITE, not edited away — it is the sentence that
kept the rescue alive across three tickets, and it was wrong for a reason worth keeping.

#### THE DECLARED BRACKET IS A DISCHARGE ROUTE, AND IT SUPPLIED A DEFERRED FOLLOW-UP'S DRIVER

`require[Spec[…]]` in a rule body is now route 4's slot source, fed through the ONE channel
`held_spec_views` already owns rather than a second notion of "declared". That is what makes
the TRANSITIVE leg free: `scope_contract_covers_dep` walks `direct_requires_chain`, so a
declared `require[FiniteCollection[C = List[T = String]]]` discharges the `Iterable[…]` that
`FiniteCollection` itself requires — DRIVEN by `wi_x9pb4 …the_bound_dictionary_names_the_
carrier_that_provides_the_spec`, whose dep arrives with every element OPEN, so nothing but
the bracket can reach it.

THIS IS THE FOLLOW-UP `check_one_spec_op_requirement`'s doc defers by name: its exact-symbol
match is "SOUND but INCOMPLETE … a carrier-aware transitive suppression … a clean follow-up
gated on an actual driver". 0DK3H is that driver, and the cover walk supplies the carriers
the symbol match could not — so no new mechanism was written for it.

ONE STALE CLAIM CORRECTED ON THE WAY: `wi_x9pb4`'s header says "`require[X]`'s bracket does
not survive to the goal". `lower_require` passes it "WHOLE, not stripped", which is why the
bindings were recoverable at all.

#### WI-1057's SHAPE — MEASURED, VERDICT: UNAFFECTED

The ticket's open question. `wi1043 …a_fact_route_supplier_answers_from_a_rule_body` passes
untouched: the argument pins the carrier concretely and the instance `fact Desc[T = Leaf,
describe = …]` IS a provider fact the static route finds. WI-1057's four pieces were in
EVAL, not in the typer's discharge, so removing value-direction does not reach them.

#### ACCEPTANCE ITEM 1's PREMISE WAS ALREADY RETRACTED BY THE TICKET ITSELF

"transitive provision resolution answers `Iterable[C = List[T = Int64]]` at load" was written
before the ticket's own item (1) retracted it ("THE STATIC SEARCH IS NOT INCOMPLETE … an
artifact of the probe"). Nothing was built for it. What stands in its place is the x9pb4 row
above, which drives the same carrier through the declared bracket.

#### EIGHT INVERSIONS, EACH NAMING ITS REASON, AND THREE DRIVEN REPAIRS

Refused at load where they used to load and report by NOT ANSWERING:
`wi1102 …control_a_rule_body_goal_is_not_refused`, `wi_n31xx` x2 (the sort- and op-half
receiver rows — kept as a PAIR, since WI-855 requires one verdict),
`wi_nx4fd …an_unground_receiver_still_suspends`,
`…an_under_determined_slot_with_no_completion_answers_nothing`, and the TIE arms of
`…rival_completions…` and `wi842 …a_rule_body_delays_on_the_tie`.

THE wi842 UNTIED ARM INVERTED TOO, AND THAT WAS NOT PREDICTED. `Leaf` looks like a sole
provider, but `DESC_INSTANCES` also carries `WrapDesc provides Desc[T = Wrap[A = E]]` with
`E` OPEN, and an open-ended rival is proof the arguments do not decide — both `T := Leaf`
and `T := Wrap[A = …]` answer. So both arms refuse for one reason, and the row says so.

TWO FIXTURES COULD NO LONGER HOLD BOTH SPELLINGS: `wi_x9pb4`'s and `wi_nx4fd`'s woven/plain
pairs each had an undeclared `plain` control beside the declared `woven` rule. Plain is now a
load error, so it moved to its own row and the woven half asserts BY VALUE (`[0, 2]`, `[2]`)
instead of against a neighbour — which the pair needed anyway, since two spellings that both
answer nothing satisfy an equality.

DRIVEN REPAIRS, so the refusals send authors somewhere that works:
`wi_x9pb4 …the_woven_spelling_answers_both_boxes` and `wi_nx4fd …the_woven_spelling_is_the_
repair` (the bracket, where it is LOAD-BEARING), and `wi1102 …a_rule_body_goal_that_pins_its_
carrier_loads_and_answers` (the pin). The bracket is deliberately NOT written beside the pin:
that row would pass with the bracket deleted.

THE REFUSAL MESSAGE was rewritten — it described both deleted predicates ("no value can name
a provider … pins no element the resolver could search on") — and now names the three repairs
the code actually honours.

CONTROLS NAMED, per CLAUDE.md: `wi_n31xx …a_nullary_spec_with_a_pinned_element_still_loads`
and `…a_sort_level_call_that_pins_the_carrier_still_loads` pass on BOTH trees; the wi842 and
`rival_completions` one-provider arms pass either way and are what say the refusals are about
missing evidence rather than about the shape.

/code-review (high), 2 findings, both fixed: a doc comment silently reattached to the wrong
collector, and `spec_is_a_marker` left carrying the deleted predicate's doc — which claimed
the opposite population and linked to two functions it no longer calls.

SPEC UPDATED (kernel-language.md): §5.4's four routes rewritten (declared bracket + provider
facts replace value-direction + searchable pin, with the two non-appeal exemptions stated),
plus the two dependent passages on where a tie is raised.

SCALAND: nothing to port — no `typing` module and no `find_dictionary` channel; `provides`
appears in its Loader only as a declaration form.

cargo-test: 36 binaries, 7287 passed, 0 failed. scaland-sbt-test: 578 + 35 + 1, 0 failed, exit 0.

