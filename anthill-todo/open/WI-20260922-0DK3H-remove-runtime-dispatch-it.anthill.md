## Attributes

- id: WI-20260922-0DK3H-remove-runtime-dispatch-it
- created: 2026-09-22T07:56:43Z

- status: Open
- status_agent: user
- status_at: 2026-09-22T07:56:43Z

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

