## Attributes

- id: WI-20260821-6WVJB-a-predicate-s-clauses-must-all
- created: 2026-08-21T15:37:20Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T15:37:20Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260821-ZW940-arity-should-distinguish

## Description

A PREDICATE'S CLAUSES MUST ALL HAVE ONE ARITY. Rules accept mixed arity today and
operations refuse it; the two halves of the language should agree, and they should agree
on the OPERATION's answer.

DECIDED (user, 2026-08-21): disallow arity overloading in rules.

MEASURED, today's inconsistency:
  operation f(x) beside operation f(x, y) in one scope  -> REFUSED (WI-1049)
  rule p(1) beside rule p(1, 2) in one scope            -> LOADS, 2 clauses
and the rule half does not merely load, it DISPATCHES. Driven over
`{ rule p(1)  rule p(1, 2)  rule p(7) }`:
    p(1) -> 1   p(7) -> 1   p(1,2) -> 1   p(9) -> 0   p(1,9) -> 0

WHY THE OPERATION'S ANSWER AND NOT THE RULE'S -- the deciding fact is the VALUE POSITION.
A bare name is a value: `apply1(twice, 3)` LOADS with `twice` alone denoting the function,
and 052 OQ2 wants bare `Queen.find` citable as a `Relation[T]`. Arity is visible at a CALL
site and invisible at a value site, so overloading by arity would make the bare name
ambiguous with nothing to pick by. That is what the duplicate-operation refusal means by
"a scope maps a name to one symbol".

AND IT MAKES 052 COHERENT. A `Relation[T]`'s schema IS its row type -- the full named tuple
of its columns (052 OQ5, WI-20260818-YQB1Y). A mixed-arity predicate has NO single schema,
so it cannot be a relation value at all. That is a live incoherence, not a hypothetical:
the language offers relations-as-values and simultaneously admits predicates that cannot
have one.

CORPUS COST: ONE SITE. Of 41 multi-clause predicates over stdlib + anthill-stl +
examples/github-todo, exactly one has mixed arity -- `Constraint`, arities [1, 2], the
kernel's own bookkeeping for §6.2 constraints (a headless rule / denial), not user code.
No user-written predicate anywhere in the corpus mixes arity.

WHAT THIS TICKET MUST DECIDE:
 1. THE `Constraint` SITE. Constraints desugar to rules (§6.1/§6.2) and the kernel stores
    them under one `Constraint` name at two arities. Either the two shapes get two names,
    or `Constraint` is exempted as kernel-internal and the rule is stated over
    user-written predicates. Say which; do not let the census's one site decide by
    accident.
 2. WHERE IT IS ENFORCED. The natural site is where a head's clause is indexed -- the same
    place WI-939 item 4 refuses a clause in a bodied operation's arity+1 slot. The refusal
    must name BOTH clauses and their arities, like the duplicate-operation one.
 3. WI-938's DERIVED VIEW is not a violation. `operation f(x) -> y` has a relational view
    at arity 2; that is one name at two arities BY CONSTRUCTION and must stay legal. The
    rule is about hand-written clauses of one predicate, not about a derived view.
 4. 056's VARIADIC CAPTURE and named arguments. `rule fix(?r, ...?args)` and a head with
    named slots need "arity" defined before it can be checked -- positional count, or
    positional + named, or the capture counted as one.

WATCH FOR: this does NOT lift the operation-side complaint that opened WI-20260821-ZW940.
Operations still cannot overload, and the advice there is still "Rename one"; making that
legal needs type-directed resolution in value position or an explicit citation form, both
of which this ticket deliberately does not do.

ACCEPTANCE: `rule p(1)` beside `rule p(1, 2)` in one scope is a located load error naming
both clauses and both arities. CONTROLS that must stay green: two clauses of the SAME
arity are one predicate and both answer (`rule p(1)` + `rule p(7)`); a bodied operation's
derived relational view at arity+1 still works (WI-938); and same-named predicates in
DIFFERENT scopes are unaffected. Say at the site which rows fail on a back-out. cargo-test
green via rustland/scripts/test.sh.

