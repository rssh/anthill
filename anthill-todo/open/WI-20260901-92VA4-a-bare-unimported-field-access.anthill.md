## Attributes

- id: WI-20260901-92VA4-a-bare-unimported-field-access
- created: 2026-09-01T15:47:16Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T15:47:16Z

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

