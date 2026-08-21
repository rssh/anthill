## Attributes

- id: WI-20260821-P85Z7-a-paren-less-nullary-rule-head
- created: 2026-08-21T07:53:13Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T07:53:13Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A PAREN-LESS NULLARY RULE HEAD INTRODUCES NOTHING, ANYWHERE. It must either introduce or
be refused; today it does neither, silently.

MEASURED (rustland, WI-980's tree). `rule shared_pl :- b(2)` at top level beside
`namespace nsx { rule shared_pl :- b(1) }` LOADS CLEAN, `query "shared_pl"` answers
`true` -- the namespace's clause landed on the same global bare intern as the top-level
one -- and NEITHER `shared_pl` NOR `nsx.shared_pl` resolves to a symbol. Two scopes
share one uncitable predicate. The parenthesised twin `rule shared_pl() :- b(2)` is
REFUSED by WI-980's `<global>` rule. Two spellings of one nullary predicate, opposite
verdicts.

THIS IS WI-894's DEFECT CLASS, STILL LIVE. §"A rule-introduced functor is scoped where it
is written" exists precisely to stop a rule head reaching `remap_name_str`'s bare
`intern(name)` fallback -- ONE GLOBAL NAME two scopes' same-spelled heads then share,
with the loser's laws ignored inside its own scope on a program that loads clean. The
nullary spelling never entered that fix.

MECHANISM, CONFIRMED NOT ASSUMED: `rule_introduced_functor_name` (kb/load.rs) ends with
`let Term::Fn { functor, .. } = parse_terms.get(subject) else { return None; };`. A bare
identifier is not an application, so the head yields no name, no `RuleHeadSite` is
collected, and WI-980's sub-pass 3 never sees it -- never scopes it, never refuses it.

CORPUS: FOUR live sites, one of them a shipped EXAMPLE and one inside a namespace (so it
is the harmful shape, not only the top-level one):
  rustland/anthill-cli/tests/fixtures/wi754/props.anthill:11  rule holds :- base(1)
  rustland/anthill-cli/tests/fixtures/wi754/props.anthill:12  rule never :- base(999)
  rustland/anthill-cli/tests/fixtures/wi754/multi-query.anthill:8  fact holds
  examples/webots-modelling/lf1/safety_gps.anthill:82  rule gps_drift_axiom :- ...
Four CLI test modules load the wi754 fixtures and depend on `holds` ANSWERING, so a bare
refusal is not available without migrating them -- decide before implementing.
`examples/webots-modelling/lf1/safety_gps.anthill:82` is the shape INSIDE a namespace,
which is the harmful one: it is scoped nowhere today.

THE DECISION THIS NEEDS, and why it is not a one-line patch: `rule_introduced_functor_name`
is ONE function read by BOTH head shapes, and the two want opposite answers.
 * PREDICATE head: `rule holds :- base(1)` is a proposition and wi754 treats it as one.
   It should introduce a nullary predicate, scoped where written.
 * EQUATION LHS: CLAUDE.md and kernel-language.md §5.3 state the opposite deliberately --
   "a `[simp]` head is an APPLICATION, so a nullary head needs its parentheses (`tau()`,
   not `tau`)" -- because a bare identifier matches no redex. `rule tau <=> ...` never
   fires, and that must stay true.
So the fix splits a case the function currently fuses, and every reader of it
(`RuleIntroduction`, the WI-1129 capture, the WI-898 kind choice) has to be checked
against the split. Census the readers per RESOLVER, not per method (WI-1090/888).

ALSO TO SETTLE: whether the minted symbol is reached at LOAD -- confirm the clause is
indexed under the scoped symbol and not still bare-interned; and whether `fact holds`
(the `multi-query.anthill` spelling) follows the rule head or is a separate question.

ACCEPTANCE: drive it. Two scopes each writing a bare nullary head of one name must give
TWO predicates, each answering its own clause and neither answering the other's -- the
control is that today the goal answers `true` from the wrong scope's clause. Assert the
qualified names resolve. Keep an equation row proving `rule tau <=> ...` still fires
NOTHING while `rule tau() <=> ...` does. Say at the site which rows fail on a back-out.
cargo-test green via rustland/scripts/test.sh.

