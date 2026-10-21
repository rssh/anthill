## Attributes

- id: WI-20260821-6WVJB-a-predicate-s-clauses-must-all
- created: 2026-08-21T15:37:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-21T05:15:58Z

- acceptance: cargo-test, scaland-sbt-test

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

## Changes

### 2026-10-20T19:31:03Z — feedback — claude

UNBLOCKED 2026-10-20: WI-20260821-ZW940 is closed as decided (arity does not distinguish operations; identity is (scope, name)), so this ticket's rule is the language's answer for both halves and no longer waits on anything.

ORDER AGAINST PROPOSAL 069 (WI-20261003-QV5W5): do this ticket first. 069 §"Omission at a call" enforces one arity only for a declaration carrying a default, and states that scope as the case of this ticket that defaults force. With this ticket delivered, 069 needs no arity rule of its own -- its gate ("carries at least one default") is this check with a condition added, and it should be dropped rather than implemented. QV5W5 now depends on this ticket.

ON DECISION ITEM 1 (Constraint), an observation, not a decision: the three stored shapes are Constraint(head(...)), Constraint(head(...), guard(...)) and Constraint(guard(<LogicalQuery>)) (kb/load.rs, store_denial_constraint_fact and store_logical_query_constraint_fact). The two-argument denial differs from the one-argument one only by an optional guard column, so the mixed arity is an optional column, the shape 069 gives a default to.

STALE TEXT TO UPDATE ON DELIVERY: docs/kernel-language.md §8.6 ("A declaration carries no arity claim. Clauses of one predicate may still differ in arity, exactly as today"); proposal 061 header ("one-arity-per-predicate remains WI-20260821-6WVJB"); proposal 069 lines ~312-316 and the Non-goals bullet ("does not decide one arity per predicate in general").

### 2026-10-20T19:32:01Z — feedback — claude

CORRECTION to the previous entry: the stale sentence ("A declaration carries no arity claim ...") is in docs/kernel-language.md §5.3 Rule, near line 2545, not §8.6.

ON DECISION ITEMS 3 AND 4, a suggested reading for the user to confirm, not a decision: arity is the declared column list -- positional and named columns counted together, a ...args capture counted as one column -- so a head with named slots and one with the same slots written positionally have one arity. WI-938's arity + 1 view stays legal under it: it is a reading of a GOAL against a bodied operation, not a second clause set of a predicate, and WI-939 item 4 already refuses a hand-written clause in that slot.

### 2026-10-20T19:52:29Z — feedback — claude

DECIDED (user, 2026-10-20), the four items:

 1. CONSTRAINT: outside the rule. The rule covers the names a program writes clauses under -- predicates and operations. `Constraint` is a kernel meta-sort (KERNEL_META_SORTS, symbol kind Sort) whose rows the loader writes for every `constraint` item, in three shapes: Constraint(head(..), guard(..)) for a guarded denial, Constraint(head(..)) for a bare one, Constraint(guard(<query>)) for a quantified one. No program in stdlib, examples or the CLIs queries them.
 2. ENFORCED as a load check over the clauses of each predicate and operation, a declaration counted as one of them.
 3. WI-938's arity + 1 view stays legal: it is a reading of a goal, no stored clause.
 4. ARITY IS THE ARGUMENT COUNT, positional and named counted together. `fact q(a: 1)` beside `fact q(a: 1, b: 2)` is refused; `fact r(1, 2)` beside `fact r(a: 3, b: 4)` stays legal. A `...args` capture never reaches a predicate: it is refused in a logical rule head (measured).

ADDED TO THIS TICKET (user, same day): a predicate's NAMED-ARGUMENT ORDER is normalized in heads and goals. Measured on the tree: with `fact r(a: 3, b: 4)`, `rule s(?x, ?y) :- r(b: ?y, a: ?x)` answers nothing while the goal written `r(a: ?x, b: ?y)` answers (3, 4); `fact r(b: 4, a: 3)` is the mirror. Entities and records already get one key order (canonicalize_record_named_args); a predicate's head and goal keep their source order.

FURTHER SHAPES THE CHECK COVERS, each loading clean today: clauses under one operation at two arities (`fact S.f(1, 2, 3)` beside `fact S.f(5)` for `operation f(x: Int64) -> Int64`); an imported predicate gaining a clause of another arity from the importing namespace (`namespace a { rule p(?x)  fact p(1) }  namespace b { import a.p  fact p(1, 2) }` -- `a.p` answers at both arities); a declaration beside a clause of another arity.

CENSUS (2026-10-20, every live clause, source and derived, stdlib + every example + the anthill-todo bundle): no predicate and no operation has clauses at two arities. The only mixed name is `Constraint` (guardians: arities 1 and 2), which item 1 leaves outside.

NOTE: the August probes in the description use `rule p(1)`, which has been a DECLARATION since 061 and stores no clause; the rows use `fact`.

### 2026-10-21T05:15:57Z — feedback — claude

DELIVERED 2026-10-21. One name, one arity: the clauses of a predicate and the clauses written under an operation all have one arity (positional and named counted together), a 061 declaration states it, and another arity is LoadError::ClausesOfDifferentArity naming each arity and where it is written (load::check_one_arity_per_name, beside WI-939's check), across loads too; a fact written at run time of another arity is refused by check_fact_mutation_target (KnowledgeBase::established_arity). The kernel's Constraint rows are outside it. Named arguments of a predicate's heads and goals match in any key order (discrim walks keys through KnowledgeBase::sort_named_keys_for_matching; a fact head is stored in key order, so the two spellings are one row); a named tuple keeps its order. Spec §5.3 rewritten (approved by the user 2026-10-21); proposals 061 and 069 updated. Rows: tests/include/wi_6wvjb_one_arity_per_name_test.rs (22) and kb::load::wi_6wvjb_one_arity_load_tests (1), each part backed out alone fails its rows. Seven existing rows rewritten (wi1058, wi896, wi899, kf2sd, cdhsq, 1kf32): their programs gave one name two arities. Full workspace 10,235 passed, 0 failed; families unmoved; scaland testFull 710 passed (unchanged, scaland mirrors neither the refusal family nor named-key canonicalization).

OPEN, for the user: a LONE clause under an operation at an arity unrelated to its parameter count still loads (fact S.f(1, 2, 3) beside operation f(x: Int64) -> Int64); only a second arity is refused. Whether an operation's declaration fixes its clauses' arity (own arity for Bool, arity + 1 otherwise) is not decided. And the SMT generator's per-arity handling (span/2 beside span/3) is now unreachable and was left in place.

