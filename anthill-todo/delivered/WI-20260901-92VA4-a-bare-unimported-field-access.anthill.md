## Attributes

- id: WI-20260901-92VA4-a-bare-unimported-field-access
- created: 2026-09-01T15:47:16Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-01T17:42:32Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BARE UNIMPORTED `field_access(q, x)` IS THE DESUGARING, AND kernel-language.md SAYS THREE
TIMES THAT IT MUST NOT BE. Decide which side moves. Split out of WI-20260824-6RXGD, whose
delivery measured this and deliberately left it standing (user, 2026-09-01).

MEASURED, WITH A CONTROL, in an operation body:
  operation get(q: P) -> Int64 = field_access(q, x)   -- loads clean; DRIVEN, answers 7
  operation get(q: P) -> Int64 = foo_access(q, x)     -- CONTROL: load error
  rule got(?q) :- p(?q), field_access(?q, x)         -- load error, and a GOOD one:
      "rule-body goal `field_access` names nothing: ... this goal can NEVER match ...
       Fix the spelling, or import the namespace that declares `field_access`."
  query pattern `field_access(?o, ?f)`                -- bare intern, no rescue
`dot_apply(q, x)` behaves identically to the first row — loads clean, DRIVEN, answers 7.
One spelling, three positions, and the OPERATION BODY is the only one that rescues it;
the rule body and the query pattern both treat it as the ordinary unimported name the spec
describes. (`entity p(x: Int64)`, receiver `p(x: 7)`.)

THE SPEC SAYS THE OPPOSITE, in the §8.6 "Synthesized forms do not use that rung" block:
  - "A user's same-spelled name cannot capture a desugaring."
  - "No name is reserved. There is no list of spellings the resolver treats specially."
  - "`field_access(?o, ?f)` written by hand is a call to whatever `field_access` denotes at
     that scope, which is nothing unless the file imports it. What it is NOT is the
     desugaring: provenance, not spelling, decides that."

MECHANISM, CONFIRMED. `parse::desugar_target::is` admits THREE spellings — the minted
address, the plain qualified name, and the SHORT name — deliberately, and its doc argues
for the third ("a hand-written `field_access(…)` is the same SHAPE"). The rescue happens at
ONE site: `kb/load.rs`'s accessor arm, `if dt::is(&name, dt::FIELD_ACCESS) && named_args
.is_empty()`, which routes an unresolved short name into the WI-280 / WI-714 / WI-749
re-route ladder. Narrowing that conjunct to `name == dt::FIELD_ACCESS` makes arm and control
agree — DRIVEN, one word. `dot_apply` has two sibling sites in the same file (the
`dt::is(&name, dt::DOT_APPLY)` arm and the parse-view `local_name` read).
NOT a change to `is` itself: its short arm is load-bearing on the KB VIEW, where
`local_name_of` yields the short name. This is a per-caller narrowing on the PARSE view.

CORPUS: ZERO hand-written short-spelling `field_access(` / `dot_apply(` calls in any
`.anthill` source in the tree (the `typing_pass_spec.anthill` and `reflect.anthill` hits are
reflect ENTITY constructors with named args, and prose). Neither direction migrates anything.

WHY IT WAS NOT SETTLED IN 6RXGD. 6RXGD's own review had found the narrow gate REMOVING the
three re-routes for a hand-written call with no working replacement, and the replacement the
spec prescribes — import the declared operation and call it — did not load. 6RXGD delivered
that replacement (`wi6rxgd_field_access_call_test`: `field_access[Name = "x"](q, "x")` now
type-checks and answers the field). So the objection that blocked narrowing is answered, and
the choice is now clean:
  (a) NARROW the parse-view gates and let a bare unimported `field_access` be the ordinary
      unresolved name the spec describes — the rule body's behaviour, extended to the
      operation body. Costs the hand-written SHORT spelling, which nothing writes.
  (b) AMEND the three §8.6 bullets to say the reflect (non-control) short spellings ARE
      recognized structurally where they resolve to nothing, and say why the rule body
      differs.
Whichever is chosen, the operation body and the rule body must stop disagreeing.

NOT PART OF THIS, and already pinned so it does not rot: a `FieldOf[…]` a user writes in
their OWN return-type annotation is not a `CtorReduceSite` and stays unreduced even with
both operands concrete — `wi6rxgd_field_access_call_test::
an_annotation_written_by_hand_still_does_not_reduce` records it.

ACCEPTANCE: drive the chosen reading in ALL THREE positions (operation body, rule body,
query pattern) with the `foo_access` control beside it; say at the site which rows fail when
the change is backed out; kernel-language.md and the site comment agree afterwards.
cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-09-01T17:42:32Z — feedback — user

DELIVERED 2026-09-01 (claude) — NARROWED BY PROVENANCE (user's decision, both questions).
The code moved, not the §8.6 bullets.

THE TICKET'S OWN TEXT WAS WRONG ABOUT `dot_apply`, and that is the first thing to record
because it changed the scope. It said `dot_apply` "behaves identically" and named its two
`load.rs` arms as needing the same narrowing. They do not: §5.3 GIVES THE AUTHOR that
spelling — "a sort-scoped law written against the method-call form, `rule dr:
dot_apply(?receiver, member, ?x) = … [simp]`" — so those arms take a SHAPE guard on purpose,
and their own comments record the measurement (WI-20260822-AKKWF: adding a mint gate fell 8
tests — `wi279_dot_dispatch`, `wi538_local_proof`, four `wi902_dot_rule_macro`, `wi903` —
every one reporting "expected operation declared on the receiver's sort" for the method the
dot rule existed to supply). §6.7 gives `field_access` no written form at all. I filed the
two names as one defect because they MEASURED the same; they differ in what the spec
sanctions, which is a question a measurement cannot answer. Found by reading the arm's own
comment before editing it.

SO THE CHANGE IS `field_access` ALONE, at one site: `kb/load.rs`'s accessor arm now gates on
`self.parsed.terms.is_minted(parse_id) && name == dt::FIELD_ACCESS`, the idiom
`parse::desugar_target` prescribes ("every reader whose arm is already gated on `is_minted`
may compare to the constant directly"). The `..` address is unspellable, so the constant
alone would answer the same; both are written because the gate is the claim and the constant
is the identity. The two chain WALKERS (`field_access_root_is_value`,
`field_access_dotted_name`) keep `dt::is`: they are reached only from this gate, so the
entry decides.

WHAT CHANGED, DRIVEN:
  field_access(q, q)                          was: rescued, dot-dispatch "no such member"
                                              now: "unknown functor", naming field_access
  field_access(q, x)                          was: LOADS CLEAN, answered 7
                                              now: refused, same as `foo_access(q, x)`
  anthill.reflect.field_access(q, x)          was: LOADS CLEAN, rescued
                                              now: an ordinary call to the declared operation
  q.x                                         unchanged, answers 7
  dot_apply(q, x)                             unchanged, answers 7   <- the asymmetry, driven

THE QUALIFIED ROW IS WHY THIS IS PROVENANCE AND NOT A SPELLING TEST. Dropping only `is`'s
SHORT arm would have left `anthill.reflect.field_access(q, x)` rescued, and §6.7 says a
written call is "a call to whatever `field_access` denotes at that scope" — which for the
qualified spelling is the declared operation.

THE DIAGNOSTIC HALF (user's second answer). The operation body now says what the rule body
says about a name nothing declares. `UnknownApplyFunctor`'s rendering keeps the phrase
"unknown functor" VERBATIM AND IN PLACE — ~15 assertions match on it, and
`wi557::genuinely_unknown_bare_functor_stays_terse` uses it to separate this from WI-565's
`BareMemberCall` member hint — and adds the census and the repair around it, from two new
shared functions (`load::no_declaration_census` / `load::undefined_name_repair`) that
`undefined_rule_body_goal_message` now reads too. Third copy avoided rather than written.

NOT CHANGING THE SHARED MESSAGE'S PHRASE was a measurement, not caution: 55 textual hits, ~15
of them real `contains("unknown functor")` assertions across 32 files.

SPEC: kernel-language.md §8.6 gains one paragraph recording the asymmetry the ticket got
wrong — `dot_apply` has a written surface form (§5.3), `field_access` has none, and neither
is a reserved spelling: the loader reads PROVENANCE for the accessor and a SHAPE for the dot
rule. The three bullets are unchanged and now true of the implementation.

TESTS: `wi92va4_written_accessor_test`, seven rows, THREE SEPARATE CONTROLS because the
claims are independent and one back-out would credit another:
  * restore `dt::is(&name, dt::FIELD_ACCESS)` at the gate -> three rows fail
    (`a_hand_written_bare_accessor_is_refused`,
     `a_qualified_hand_written_call_is_an_ordinary_call`,
     `the_refusal_names_the_functor_and_the_repair`);
  * restore `actual_type: "unknown functor"` -> exactly ONE fails
    (`the_refusal_names_the_functor_and_the_repair`);
  * append the census unconditionally (drop the `symbol_declares_nothing` test) -> exactly
    ONE fails (`a_declared_name_applied_wrongly_keeps_the_terse_message`). The message must
    be added AND withheld, which is two claims and therefore two controls.
Both measured, not asserted. `the_dot_form_still_lowers` and
`a_written_dot_apply_is_deliberately_untouched` and
`a_declared_dot_apply_is_unreachable_at_the_dot_rule_shape` pass under ALL THREE by design — they bound the
change, and a red one would mean the gate ate the desugaring or the sibling spelling.

/code-review (high) FOUND FOUR THINGS, and the two MEDIUMs were both mine to answer:
 1. THE SPEC PARAGRAPH I ADDED STATED A SCOPE-SENSITIVITY THAT DOES NOT EXIST. It said the
    `dot_apply` form applies "where nothing in scope declares the name" and that "a program
    that declares its own `dot_apply` gets its own". FALSE, and I had the counter-evidence
    already: the 999 measurement I generalized from was `dot_apply(1, 2)`, whose name slot is
    a LITERAL and therefore not the dot-rule shape. Re-driven — with `operation
    dot_apply(a: P, b: P)` declared, `dot_apply(q, q)` reports "no such member (dot
    dispatch)": the declaration is UNREACHABLE at the identifier shape. The arm is a pure
    shape guard and consults no scope. The spec now records that as a WART with its escape
    hatch, and `a_declared_dot_apply_is_unreachable_at_the_dot_rule_shape` drives both halves
    so the sentence cannot rot.
 2. THE CENSUS I BORROWED WAS FALSE AT THIS POSITION. `UndefinedRuleBodyGoal`'s wording is
    licensed by its head test; `UnknownApplyFunctor` fires on a WIDER condition ("neither a
    known operation, a constructor, nor a var-bound arrow type"), so `S(1)` on a declared
    sort and `n(1)` on a parameter reached it and were told "no rule, fact, operation,
    entity, const or builtin is declared under that name" about a name declared three lines
    up. Driven both. NARROWED to `KnowledgeBase::symbol_declares_nothing`, extracted from
    `undefined_functor` so the two cannot disagree about what "declared" means; the terse
    message returns for every other case. Its own control row and back-out are recorded.
    (The dotted-callee case KEEPS the census — nothing is declared under that name, and the
    rule-body message it is matching says the same for a dotted goal.)
 3. THE BACK-OUT REASON IN MY TEST HEADER WAS NOT THE MEASURED ONE. I wrote that restoring
    the gate makes two rows fail "because the program loads clean again"; run, they fail with
    a dot-dispatch "no such member", because the fixtures use `(q, q)` and `q` is not a field
    of `P`. "Loads clean" is true of `field_access(q, x)` — the motivating spelling, which
    those fixtures deliberately do not use. Corrected at the site.
 4. `undefined_contract_goal_message` still carried its own copy of the repair sentence while
    my helper doc claimed all three messages read it. It reads `undefined_name_repair` now;
    its census stays its own, deliberately, and the doc says which message shares which half.

NOT CLOSED, AND FILED RATHER THAN PARKED: the typer reports ONE error per operation body,
innermost first, so `field_access(q, x)` — a bare identifier in the field slot, which is the
likeliest way to write this by hand — is reported against `x` and never names the functor.
General and pre-existing: `foo_access(q, x)` behaves identically, and two independent
undeclared functors in one body report only the inner one (both measured). The rows above
therefore drive the functor refusal through `(q, q)`. Filed as
WI-20260901-P3CZV, with the three fixtures and an explicit "not diagnosed" — and with the
census warning that a fix which reports MORE errors is a corpus-wide change.

