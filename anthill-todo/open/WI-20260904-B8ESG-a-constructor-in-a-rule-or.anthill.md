## Attributes

- id: WI-20260904-B8ESG-a-constructor-in-a-rule-or
- created: 2026-09-04T04:07:47Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T04:07:47Z

- acceptance: cargo-test

## Description

A CONSTRUCTOR IN A RULE- OR FACT-HEAD ARGUMENT NAMES NOTHING, SILENTLY. WI-1034 refuses a rule-body GOAL whose functor names nothing and WI-1058 refuses a rule-body TERM, but a head ARGUMENT has neither check -- so a head pattern built on an unresolvable functor loads clean and simply stops matching. DRIVEN, in the stdlib, during WI-909: reflect/typing.anthill writes 'rule list_contains(?x, cons(head: ?x, tail: ?))' importing only the List SORT (which does not bring members into scope, kernel-language.md 8.6). With cons off the implicit tier that head reached nothing, and 'list_contains(2, [1,2])' answered NO SOLUTIONS where it had answered true -- while the file loaded with an identical '2955 facts, 203 rules'. Backing the one import out reproduces it exactly. The same shape hid two more sites in anthill-todo, where stored item documents carry 'some(value: ...)' in FACT-head arguments: they loaded clean and failed at match time with 'match_failed(occurrence: Node, scrutinee: Term)'. WHY IT IS WORTH A CHECK RATHER THAN CARE: the loud channel covered 2 of 8 affected files in that migration; every other site had to be found by reading, and three successive audits each looked complete and were not. A name-resolution change cannot be verified by 'the corpus loads clean' while this position is unchecked. ACCEPTANCE: a bare functor in a rule- or fact-head argument that names nothing is reported at load, in WI-1034/WI-1058's own vocabulary and with its line:col; a test drives the typing.anthill shape and FAILS without the check. THE EXEMPTION CENSUS IS THE WORK, not the check: WI-1058 already skips a discharge's binder tuple, a binding pattern, and the interior of a type, and a head argument has its own legitimate non-denoting cases -- a head INTRODUCES its own functor (WI-896), so the check must judge arguments only, and constructor patterns in a head are matched against the scrutinee's declared type rather than the name ladder (measured on anthill-cli's args.anthill during WI-909's review), which may make some of them legitimately import-free. Census those before choosing where the check fires. RUSTLAND ONLY, deliberately: the gap was measured in rustland's loader (WI-1034's and WI-1058's checks are both rustland's) and the driven evidence above is rustland's. Whether scaland's loader has the same hole is UNASSESSED -- not 'no', unassessed -- so scaland-sbt-test is off the acceptance rather than claimed and left unmet. If someone checks scaland and finds the same gap, that is a twin item, filed on its own measurement.
