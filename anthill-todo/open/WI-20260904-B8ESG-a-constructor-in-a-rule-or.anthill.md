## Attributes

- id: WI-20260904-B8ESG-a-constructor-in-a-rule-or
- created: 2026-09-04T04:07:47Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T04:07:47Z

- acceptance: cargo-test

## Description

A CONSTRUCTOR IN A RULE- OR FACT-HEAD ARGUMENT NAMES NOTHING, SILENTLY. WI-1034 refuses a rule-body GOAL whose functor names nothing and WI-1058 refuses a rule-body TERM, but a head ARGUMENT has neither check -- so a head pattern built on an unresolvable functor loads clean and simply stops matching. DRIVEN, in the stdlib, during WI-909: reflect/typing.anthill writes 'rule list_contains(?x, cons(head: ?x, tail: ?))' importing only the List SORT (which does not bring members into scope, kernel-language.md 8.6). With cons off the implicit tier that head reached nothing, and 'list_contains(2, [1,2])' answered NO SOLUTIONS where it had answered true -- while the file loaded with an identical '2955 facts, 203 rules'. Backing the one import out reproduces it exactly. The same shape hid two more sites in anthill-todo, where stored item documents carry 'some(value: ...)' in FACT-head arguments: they loaded clean and failed at match time with 'match_failed(occurrence: Node, scrutinee: Term)'. WHY IT IS WORTH A CHECK RATHER THAN CARE: the loud channel covered 2 of 8 affected files in that migration; every other site had to be found by reading, and three successive audits each looked complete and were not. A name-resolution change cannot be verified by 'the corpus loads clean' while this position is unchecked. ACCEPTANCE: a bare functor in a rule- or fact-head argument that names nothing is reported at load, in WI-1034/WI-1058's own vocabulary and with its line:col; a test drives the typing.anthill shape and FAILS without the check. THE EXEMPTION CENSUS IS THE WORK, not the check: WI-1058 already skips a discharge's binder tuple, a binding pattern, and the interior of a type, and a head argument has its own legitimate non-denoting cases -- a head INTRODUCES its own functor (WI-896), so the check must judge arguments only, and constructor patterns in a head are matched against the scrutinee's declared type rather than the name ladder (measured on anthill-cli's args.anthill during WI-909's review), which may make some of them legitimately import-free. Census those before choosing where the check fires. RUSTLAND ONLY, deliberately: the gap was measured in rustland's loader (WI-1034's and WI-1058's checks are both rustland's) and the driven evidence above is rustland's. Whether scaland's loader has the same hole is UNASSESSED -- not 'no', unassessed -- so scaland-sbt-test is off the acceptance rather than claimed and left unmet. If someone checks scaland and finds the same gap, that is a twin item, filed on its own measurement.
## Changes

### 2026-09-12T16:39:22Z — feedback — user

RELEVANT CHANGE, from WI-20260911-073GH (commit 7b6470d8): this position is now UNIFORMLY silent, where it used to be accidentally loud for a subset — so the ticket is unchanged in substance but its evidence base moved, and anyone picking it up should know which way.

WHAT WAS ACCIDENTALLY COVERED. An entity registers its field schema under its BARE interned short name as well as its resolved symbol, and that bare symbol is the loader's resolves-to-nothing rung (WI-476). So a head argument whose functor named nothing but COLLIDED with some entity's short name anywhere in the corpus picked up that stranger's schema and hit the arity/label checks:

  A: namespace p.bits { sort Bit { entity t; entity zz }
                        sort Boxed { entity ff(a: Int64) } }
  B: namespace p.u    { fact holdsF(ff(1))   fact holdsZ(zz(1)) }   -- B imports nothing

  holdsZ -> LOUD: 'constructor zz given 1 positional argument(s) but has 0 unfilled field(s)'
  holdsF -> SILENT AND WRONG: stored as ff(a: 1), the positional->named desugar run under
            the field names of an entity B cannot see and did not name

Both are this ticket's defect wearing different clothes, and the loud one was loud about the WRONG THING — it named an over-arity CONSTRUCTOR application for a name that denotes nothing at that site. 073GH gates the three written-name walks on is_resolved (KnowledgeBase::written_entity_field_names), so holdsF is now stored as written and holdsZ loads clean like any other undeclared name. Driven by wi_073gh_applied_parameter_is_not_a_constructor_test::a_stranger_entity_does_not_rename_a_written_terms_arguments and ::a_zero_field_stranger_is_an_ordinary_undeclared_term, each against a control functor matching no entity anywhere.

WHY THIS MATTERS TO THE WORK HERE, in both directions:
  - AGAINST: the corpus lost a diagnostic. Anything a migration audit was catching via
    'constructor X given N positional argument(s)' in a head argument now loads clean.
    That strengthens this ticket's own argument -- 'the corpus loads clean' was already
    not a verification of a name-resolution change at this position, and is now less of
    one.
  - FOR: the surviving noise is gone, so the census this ticket calls THE WORK is now
    over a clean population. Before, some head arguments were refused for a reason that
    had nothing to do with whether they denote; those would have had to be subtracted.

NOT A DUPLICATE and nothing here is claimed as done: 073GH deliberately did not decide
whether an undeclared functor in a head argument should be refused -- it only stopped one
being silently RENAMED. This ticket still owns the refusal and its exemption census.

