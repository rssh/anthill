## Attributes

- id: WI-20261121-MVQP8-an-unlabeled-constraint-is
- created: 2026-11-21T13:07:02Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-21T20:06:35Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN UNLABELED CONSTRAINT IS REPORTED WITHOUT A NAME OR A LOCATION: two violated unlabeled constraints print two identical lines, `integrity constraint is violated by the loaded facts`, and nothing tells them apart.

FOUND while choosing how a test harness reports which invariant a state breaks (WI-20261121-G8E02, explaining a failed goal). `anthill check` names a violated constraint only by a label written in the source. A label is also the only thing a description can attach to, so an unlabeled constraint cannot carry the prose a specification writes about it (WI-20261115-S6CWK row 3).

MEASURED on a4fb58dc9 (debug CLI of 2026-11-21), with `fact p(1)`, `fact q(1)`, `big(?x) :- ?x > 5`, `small(?x) :- ?x < 0`:
  1 `constraint forall ?x: p(?x) -: big(?x)` beside `constraint forall ?x: q(?x) -: small(?x)`: both violated, reported as two identical lines `error: integrity constraint is violated by the loaded facts`.
  2 `constraint labeled_one: forall ?x: p(?x) -: small(?x)`: `integrity constraint 'labeled_one' is violated by the loaded facts`. No location either.
  3 `{< every p is big >}` before an unlabeled constraint: refused, "description block on unlabeled constraint has no stable target" (S6CWK row 3, unchanged since 53a0d453b).

THE CAUSE. `LoadError::ConstraintViolated { label: Option<String> }` (kb/load.rs:2820) carries the written label and nothing else: no span, no head. The location is at hand: the registered guard stores its constraint's site (`Guard.site`, kb/mod.rs:140 on a4fb58dc9), and the post-load check that raises the violation (`KnowledgeBase::check_guards_except`) reads it only to leave out a constraint whose text the load refused. [CORRECTED 2026-11-21: this pointed at the neighbour `AggregationConstraintUnsupported`, which the loader raises at the constraint itself. The violation is raised after the load, from the guard.]

PROPOSED: the loader gives every unlabeled constraint a label generated from its text, and every violation report carries the constraint's location.
- A DENIAL `Inv :- Guard` is labeled by its head, `Inv`. §6.2's "The invariant (head) states what must be true" is written of this form. An aggregation is labeled by its comparison.
- A QUANTIFIED constraint has no head in that sense. [CORRECTED 2026-11-21: this said that for `forall ?x: A -: C` the head is the innermost consequent `C`, citing §6.2. §6.2's sentence is about the denial form. The grammar names `C` the quantifier's `body` (`quantified_constraint`, `field('body', …)`). The guard engine counts the bindings that satisfy the condition and `C` together (`eval_count_guard`), so only under `forall` is `C` what must hold. Under `no` it is what must not hold, and under `some`, `one` and `lone` it is part of what is counted. A report "integrity constraint big(?x) is violated" for `no ?x: p(?x) -: big(?x)` reads as the opposite of the constraint.] DECIDE WITH THE USER how a quantified constraint is labeled:
  (a) its quantifier, binder and consequent, with the condition elided: `forall ?x: … -: big(?x)`, `no ?x: … -: big(?x)`. The full text is used where two collide. The `…` is needed: `forall ?x -: big(?x)` is the bare-binder spelling of a different constraint (grammar: "condition is the body itself"). A constraint written with a bare binder is labeled by its whole text. Recommended.
  (b) the whole constraint as written, `forall ?x: p(?x) -: big(?x)`, with a hash where it is long.
- ONE LABEL SPACE PER SCOPE for constraints, rules and facts (decided with the user 2026-11-21), as for written labels: `rule x:` and `constraint x:` in one scope are one symbol today. A constraint's generated label therefore collides with a rule's or a fact's that prints the same.
- Row 1's labels follow from the choice above. Under (a) they are `forall ?x: … -: big(?x)` and `forall ?x: … -: small(?x)`. [CORRECTED 2026-11-21: this said `big(?x)` and `small(?x)`. Under the extension below, row 1's rules `big(?x) :- ?x > 5` and `small(?x) :- ?x < 0` take exactly those labels in the same scope.]
- When two unlabeled constraints in one scope share a label, each adds its guard (under (a), for a quantified one, its condition). The guard is printed when it is short (a limit to decide; about 40 characters). Otherwise the label adds a short hash of a CANONICAL form of the constraint: its tokens as written, one space apart, with comments and descriptions left out and each named variable renamed by its first occurrence. So renaming a variable or reformatting does not change the label. [CORRECTED 2026-11-21: this said a hash of the guard's STORED form. The stored form of a quantified guard carries the binder's name as a string (`var: "x"`, `Loader::build_logical_query`), and its pattern variables are global var ids minted per load (`convert_term` → `fresh_var`). A hash of it changes when the binder is renamed, and from one load to the next.] Two identical constraints are refused at load as duplicates. Two different guards whose short hashes clash are refused.
- A label is never positional (`#1`, `#2`): reordering two declarations must not move a label from one constraint to the other.
- The generated label is the constraint's symbol in its scope, as a written one is, so it is the target of a description: row 3 loads. The rest of S6CWK (clauses, facts, goals in a body) stays there.
- The report reads `integrity constraint big(?x) is violated by the loaded facts (file:line)`, and adds the description when the constraint has one. A written label is reported as today, with the location added.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven):
- row 1 reports two lines that differ, each naming its constraint by the label chosen above and giving its location [CORRECTED 2026-11-21: this named the lines `big(?x)` and `small(?x)`; see above];
- row 2 is reported with its location;
- row 3 loads, stores a DescriptionInfo naming the generated label, and its violation report shows the description;
- two unlabeled constraints with one head: with a short guard, each label shows its guard; with a long guard, each shows a hash, and renaming a variable in the guard leaves the hash unchanged;
- two identical unlabeled constraints are refused at load;
- written labels are unchanged apart from the location;
- back-out: without the generated label, row 1 prints two identical lines and row 3 is refused again.

## Changes

### 2026-11-21T13:22:44Z — feedback — claude

EXTENDED with the user 2026-11-21: EVERY UNLABELED CLAUSE GETS A GENERATED LABEL, not only a constraint. A rule's clause and a fact get one by the same rule as a constraint. A description before any of them then has a target. This closes WI-20261115-S6CWK rows 1-3 (a rule, a fact, a constraint) and answers its open design question: the target is the generated label, not the stored clause or its source occurrence.

- A rule's or a fact's label is its head as written: `product_has_positive_price(ShopState(products: ?ps))`.
- Where two clauses in one scope have the same head, the label adds the body. The three `can_add_to_cart(?s, ?customerId, ?productId, ?delta)` scenarios are such clauses. The body is printed when short, and otherwise replaced by a short hash of the clause's canonical form, as for a constraint's guard [CORRECTED 2026-11-21: this said "of its stored form"; see the constraint's guard above]. Two identical clauses get one label, since the label is a function of the text, and so share their descriptions. [CORRECTED 2026-11-21: this said "two identical clauses are one clause, as the store holds them". That is true of ground facts only (`assert_fact`'s dedup). Identical bodied rules are separate stored clauses. MEASURED on dae4e74e4: `rule r(?x) :- n(?x)` written twice, beside `rule s(?x) :- n(?x)` and `rule s(?y) :- n(?y)`, adds 4 rules to the load (351 → 355). `fact n(1)` written twice is stored once: 5855 facts, as with one.] The shop specification that holds the `can_add_to_cart` clauses is not in the repository, so the acceptance row writes three such clauses of its own.
- A written label is unchanged.
- The predicate-level case in S6CWK's feedback of 2026-11-21 reads as option (a) there: a predicate's description is its clauses' descriptions together.

ACCEPTANCE, added:
- S6CWK rows 1-3 load, and each stores a DescriptionInfo naming the generated label;
- the three `can_add_to_cart` clauses get three different labels, each with its own description;
- renaming a variable in a body leaves its hash unchanged;
- back-out: without the generated label, those rows are refused again.

### 2026-11-21T18:26:51Z — feedback — claude

REVIEWED 2026-11-21 for untrue statements, with the user. Corrected in place, each marked [CORRECTED 2026-11-21]: (1) the head of a quantified constraint is not its consequent: §6.2's sentence is about the denial form, the grammar calls the consequent the quantifier's body, and under no, some, one and lone it is not what must hold; how such a constraint is labeled is now to decide, options (a) and (b) in the description. (2) Row 1's labels are not big(?x) and small(?x): under the extension, the rules big(?x) :- ?x > 5 and small(?x) :- ?x < 0 take those labels in the same scope (one label space per scope, decided with the user 2026-11-21). (3) A hash of the guard's stored form does not survive renaming a variable or another load: the stored guard holds the binder name as a string and per-load var ids; the hash is of a canonical form instead. (4) Identical bodied rules are two stored clauses, not one; only ground facts are deduplicated. Also reworded the cause: the location is in the registered guard already (Guard.site). Re-measured rows 1-3 on dae4e74e4 with the debug CLI: as stated.

### 2026-11-21T18:33:19Z — feedback — claude

DECIDED with the user 2026-11-21: option (a). An unlabeled quantified constraint is labeled by its quantifier, binder and consequent, each condition elided: forall ?x: … -: big(?x), no ?x: … -: big(?x). A bare binder has no condition, so forall ?x -: big(?x) is labeled by its whole text. Where two labels collide, each takes its whole text, or the elided form and a hash when the conditions are longer than the limit. Row 1's labels are forall ?x: … -: big(?x) and forall ?x: … -: small(?x).

### 2026-11-21T19:13:01Z — feedback — claude

DECIDED with the user 2026-11-21, replacing the head-first label with a collision fallback: EVERY GENERATED LABEL IS ITS HEAD AND A HASH OF ITS CONTENT, head-HASH: pos(?x)-K3M9Q2XA, forall ?x: … -: big(?x)-K3M9Q2XA (the quantified head as decided before, each condition elided). The hash is of the clause's canonical form: its tokens as written, comments and descriptions left out, each variable renamed by its first occurrence, with the kind (a rule or fact, or a constraint). WHY: a head-only label depends on the scope, and changes when another clause of the same head is added, possibly in another file; whatever names the label from outside (a query by target, a harness recording which invariant a state breaks) then breaks. head-HASH depends on the clause alone, so adding a neighbour never moves it, and renaming a variable or reformatting leaves it. What changes the clause's meaning changes its label. Consequences: no collision rule and no 40-character limit; a fact and rule p(1) :- true are one clause and share a label; a constraint and a rule written alike are two labels; two constraints written alike are refused as before; two different clauses with one label (a hash clash) are refused. The rows that expected big(?x) (row 1) now expect forall ?x: … -: big(?x)-HASH.

### 2026-11-21T19:29:45Z — feedback — claude

DECIDED with the user 2026-11-21, final, replacing the earlier entries' label rules: ONE KIND OF LABEL. A rule that stores a clause, a fact, or a constraint written without a label gets the label it would have if one were written: its head's name, '-', and a hash of its content, pos-K3M9Q2XA. Identifiers may hold '-', so it is an ordinary name, and nothing after the converter tells it from a written label (user: 'the complicated design was having different labels, generated and written'; 'long labels are not ergonomic'). The name is the predicate the head states (an equation's subject; a quantified constraint's innermost consequent's); a head that states none, an operator for instance, is named by its kind (rule, constraint). The hash is of the canonical form (the kind, then the tokens with comments and descriptions left out, each variable renamed by its first occurrence), so another clause never moves a label, renaming or reformatting leaves it, and fact p(1) and rule p(1) :- true share one. SAME RULES AS A WRITTEN LABEL, consequences included: describe and using reach it by name; an unlabeled multi-head rule loads; every fact's label is a symbol; a labeled rule in a sort body is its MemberInfo row; a constraint's @[...] block is admitted. Two constraints written alike share one label, as two written constraints of one label do, and are no longer refused. Reports: integrity constraint 'big-MXPH78PX' is violated by the loaded facts at row1.anthill:7:3 — every p is big.

### 2026-11-21T19:59:43Z — feedback — claude

IMPLEMENTED, with the user 2026-11-21, beside the final label design above: (1) a fact's label is its clause's citation label, as a rule's is; a fact that dedups onto a clause already labeled keeps that label. (2) the Rust generator's property stub for a labeled rule is emitted #[ignore] (user decision): every rule that stores a clause is labeled now, and the stubs were todo!() tests that failed. (3) a message that names a clause by its label says where it is written (user): prove's laws-left-out warning reads 'anthill.prelude.WeakOrd.gt-PMMH12JG at anthill/prelude/ordered.anthill:156:5'; for that, an embedded stdlib entry is parsed with its entry name as its path. (4) /code-review found a described fact in a host provides block refused (its label undefined at the block's target sort) and a query pattern defining its label: both fixed, with rows. Not done: a hash clash between two clauses of one name in one scope is merged, not refused; duplicate unlabeled constraints are no longer refused (they share one label, as two written ones do).

### 2026-11-21T20:06:31Z — feedback — claude

DELIVERED in 12eada27b.

