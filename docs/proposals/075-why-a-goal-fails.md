# Proposal 075: The proof of a goal — `SLDProof` and `SLDProof.of`

## Status: Approved by the user (2026-11-21), third version. Written with the user under WI-20261121-G8E02. The first version (a separate walker, a `Failure` record, `query --explain` with JSON) and the second (`refutation`, the proof of `!goal` alone) were replaced by this one: History 13–21. Nothing here is implemented; §7 lists what is open.

## Tracked by: WI-20261121-G8E02.

## Relates to: `docs/kernel-language.md` §8.3 (rule evaluation: a relation yields proofs; negation; the depth and fuel limits), §4.1 (labels); WI-20261121-MVQP8 (every clause has a label); `stdlib/anthill/reflect/reflect.anthill`. Not to be confused with §5.10's `proof … by` declarations: those are proof obligations, discharged by `anthill prove`.

## The problem

When a goal has no answer, nothing says why. Over

```anthill
rule pos(?x)  :- ?x > 0
rule big(?x)  :- ?x > 5
rule even(?x) :- ?x % 2 = 0
rule good(?x) :- pos(?x), big(?x), even(?x)
```

`good(1)` has no solutions, and nothing says that `big(1)` fails, or why. A program cannot ask either: a test of the shop model (WI-20261115-32WQJ) that finds an invariant not holding for a state has no way to say which part of the state breaks it. Nor can anything say how a goal that holds was proved. The spec counts proofs (§8.3: a relation's answers are counted by their proofs) but never hands one out.

## 1. The idea

The search proves goals. It can give the proof back as a term.

- `good(6)` holds. Its proof is the clause that worked, with a proof of each of its body goals:

  ```
  good(6), by clause good-…, with ?x = 6:
    pos(6)   by clause pos-…:   6 > 0
    big(6)   by clause big-…:   6 > 5
    even(6)  by clause even-…:  6 % 2 = 0
  ```

- `good(1)` does not hold, so `!good(1)` holds, and `!good(1)` has a proof too: for every clause of `good` whose head matches, on every branch, a body goal that fails, and why it fails.

  ```
  !good(1), because in clause good-…, with ?x = 1:
    big(1) fails, because in clause big-…:  1 > 5 is false
  ```

The two are mirror images:

| | proof of `good(6)` | proof of `!good(1)` |
|---|---|---|
| clauses | one: the clause that worked | every clause whose head matches, on every branch |
| body goals | a proof of every body goal | one body goal that fails, and why |
| leaves | a fact, a builtin that holds, an assumption of a discharge (§3.1) | no clause matches, a builtin that fails |
| how many | one per way the goal holds | one: the one the search finds |

They nest. When `!q(1)` fails, the reason is the proof of `q(1)`. When `!r(2)` holds inside a proof, its proof is the refutation of `r(2)`. So one relation and one type cover both.

The search already goes through all of this to answer; today it keeps only the answer. This proposal lets it keep the proof.

## 2. The relation and the type

Declared in `anthill.reflect`, the relation in the type's own scope, so a rule calls it `SLDProof.of(goal, ?p)` (History 21):

```anthill
enum SLDProof
  -- ?goal is a goal g, or a negation !g.
  -- For g: one answer per proof of g, binding g's variables as a query does.
  -- For !g: at most one answer, the proof of !g the search finds.
  rule of(?goal, ?proof)

  -- the goal holds
  entity by_clause(goal: Term, clause: Option[T = Symbol], body: List[T = SLDProof])
  entity by_builtin(goal: Term)                   -- a builtin that holds: 6 > 5, ?r <=> 3
  entity by_assumption(goal: Term)                -- an assumption of an enclosing discharge
  entity residual(goal: Term)                     -- left unchecked: the answer is conditional on it (§7, question 1)
  -- the goal has no proof (the proof of !goal)
  entity refuted(goal: Term, steps: List[T = Step])
  entity builtin_false(goal: Term)                -- a builtin that fails: 1 > 5
  -- a discharge, (forall(?x…), A -: C): fresh constants for the binders,
  -- A assumed, and `proof` proves C where the discharge holds, refutes it where it fails
  entity by_discharge(goal: Term, fresh: List[T = Term], assumed: List[T = Term], proof: SLDProof)
end

-- In `clause`, the body goal `failing` fails; `because` proves !failing.
entity Step(clause: Option[T = Symbol], failing: Term, because: SLDProof)
```

- **`by_clause`**: the goal holds by `clause`, and `body` holds a proof of each of its body goals, in order. A fact is a clause with an empty body.
- **`refuted`**: every clause whose head matches the goal, on every branch, has a `Step`. When no clause's head matches, `steps` is `[]`.
- **`Step.because`** proves that `failing` fails. For `failing = big(1)` that is `big(1)`'s refutation. For `failing = !q(1)` it is the proof of `q(1)`.
- **`by_discharge`** is the proof of a discharge `(forall(?x…), A -: C)` (§3.1): the resolver takes a fresh constant for each binder, assumes `A`, and proves `C`. `fresh` lists the constants, `assumed` the assumptions with the constants filled in, and `proof` is `C`'s proof, or its refutation where the discharge fails.
- **`by_assumption`**: a goal inside a discharge answered by one of its assumptions rather than by a clause. In a proof by induction, this is where the induction hypothesis is used.
- **A goal a builtin turns into another goal** is not a node of its own: `?P(x)`, a predicate passed as an argument and applied, is proved as the call it makes, `prop_holds(i_nil)`.
- **`goal` and `failing`** are written with their values filled in, so they show the bindings.
- **`clause`** is the clause's label. A written clause has its written label or the one generated from its text (`good-K3M9Q2XA`, WI-20261121-MVQP8); a clause the loader derives has the derivation's name (`IntList.induction`, §6, *Labels for derived clauses*). It is `none` where the structure is not a clause (the instances of a `forall` or `some`, the two sides of `|`) and for a fact a program asserted while running (§7, question 2).

## 3. Examples

Over the rules of the problem:

```
SLDProof.of(good(6), ?p)
  ?p = by_clause(good(6), some(good-…), [
         by_clause(pos(6),  some(pos-…),  [by_builtin(6 > 0)]),
         by_clause(big(6),  some(big-…),  [by_builtin(6 > 5)]),
         by_clause(even(6), some(even-…), [by_builtin(6 % 2 = 0)])])

SLDProof.of(!good(1), ?p)
  ?p = refuted(good(1), [Step(some(good-…), big(1),
         refuted(big(1), [Step(some(big-…), 1 > 5, builtin_false(1 > 5))]))])

SLDProof.of(good(1), ?p)      no answer: good(1) does not hold
SLDProof.of(!good(6), ?p)     no answer: good(6) holds
```

| goal | its proof |
|---|---|
| `edge(1, ?y)` over facts `edge(1, 2)`, `edge(1, 3)` | two answers, `?y = 2` and `?y = 3`, each `by_clause` with its fact's label and an empty body |
| `!all_big([7, 3, 9])`, `rule all_big(?xs) :- (forall ?y in ?xs: ?y > 5)` | the `forall` is refuted at the element `3`: `Step(none, 3 > 5, builtin_false(3 > 5))` |
| `!reach_big(1)`, `rule reach_big(?x) :- edge(?x, ?y), big(?y)` | two steps in one clause, one per answer of `edge(1, ?y)`: `big(2)` fails and `big(3)` fails |
| `!cheap(p1)`, `rule cheap(?p) :- under_10(?p)` and `rule cheap(?p) :- on_sale(?p), under_20(?p)`, `p1` costs 25, not on sale | a step for each clause: `under_10(p1)`, and `on_sale(p1)` |
| `!edge(5, 1)` | `refuted(edge(5, 1), [])`: no clause matches |
| `!notq(1)`, `rule q(?x) :- ?x > 0`, `rule notq(?x) :- !q(?x)` | a step whose failing goal is `!q(1)`, because `by_clause(q(1), some(q-…), [by_builtin(1 > 0)])` |
| `!guarded(1)`, `rule loop(?x) :- loop(?x)`, `rule guarded(?x) :- loop(?x), ?x > 5` | no proof: `loop(1)` is cut at the depth limit, `!guarded(1)` is undecided, and the answer is conditional (§5) |

### 3.1 A proof by induction

A sort with constructors has a derived induction principle (§5.2, `<Sort>.induction`), one clause with a case per constructor. For

```anthill
enum IntList
  entity i_nil
  entity i_cons(head: Int64, tail: IntList)
end
```

it is

```anthill
IntList.induction(?P) :-
  ?P(i_nil),
  (forall(?h, ?t), ?P(?t) -: ?P(i_cons(?h, ?t)))
```

The stdlib's `Int64.induction(?P, ?lo, ?hi)` has the same shape, written by hand. With `fact prop_holds(i_nil)` and `rule prop_holds(i_cons(head: ?_h, tail: ?t)) :- prop_holds(?t)`, the resolver proves `IntList.induction(prop_holds)` today (`forall_impl_resolve_test`, `structural_induction_proves_property_via_auto_generated_rule`). Its proof:

```
SLDProof.of(IntList.induction(prop_holds), ?p)
  ?p = by_clause(IntList.induction(prop_holds), some(IntList.induction), [
         -- base case: the fact
         by_clause(prop_holds(i_nil), some(prop_holds-…), []),
         -- step case: fresh h and t, the hypothesis prop_holds(t) assumed
         by_discharge((forall(?h, ?t), prop_holds(?t) -: prop_holds(i_cons(?h, ?t))),
           fresh: [h, t], assumed: [prop_holds(t)],
           proof: by_clause(prop_holds(i_cons(h, t)), some(prop_holds-…), [
                    by_assumption(prop_holds(t))]))])
```

A failing induction says which case fails, and for the step case that the next case cannot be proved even with the hypothesis assumed, and why. Over a `q` that holds for `i_nil` and is not preserved by `i_cons`:

```
SLDProof.of(!IntList.induction(q), ?p)
  ?p = refuted(IntList.induction(q), [Step(none, (forall(?h, ?t), q(?t) -: q(i_cons(?h, ?t))),
         by_discharge(…, fresh: [h, t], assumed: [q(t)],
           proof: refuted(q(i_cons(h, t)), [ … ])))])
```

The loader derives the induction clause, so it has no text to generate a label from; its label is the principle's own name, `IntList.induction`, which names exactly one clause (§6, *Labels for derived clauses*). Today it has none: the loader sets a label for written facts and rules and for the `<op>__defeq` rule only (`kb/load.rs`, `kb/body_specialize.rs`).

Only proofs the SLD resolver makes are covered. An induction discharged by `anthill prove`, for example by the Z3 induction tactic (WI-101), is not an SLD proof, and `SLDProof.of` does not see it.

## 4. Using it

A test that finds an invariant not holding asks why:

```anthill
SLDProof.of(!product_has_positive_price(state()), ?p)
```

The proof leads to the `forall` over the products and its failing element: the product whose price is not above 0. A field left out of an entity pattern matches anything (§8.3, *Partial entity patterns*), so a rule that needs only part of a proof writes only that part.

On the command line it is an ordinary query: `anthill query 'SLDProof.of(!good(1), ?p)'` prints the proof.

Which invariants a state breaks is not the relation's question. A test that needs every invariant checked asks about each (History 15).

## 5. How it is decided

- **For `g`**: as the query `g` is. Each answer of `g` is one or more proofs, and each proof is an answer of `SLDProof.of`. Two proofs of the same bindings are two answers (§8.3: a relation yields proofs).
- **For `!g`**: as `!g` is. While `g` has an unbound variable, the relation waits; left so, its answer is conditional. If `g` has an answer, `!g` has no proof and there is no answer. If the search for `g` is undecided (a limit cut it, or it ends with conditional answers only), so is the relation: a conditional answer, never a proof. There is at most one answer: the proof the search finds. No other failing goal is looked for.
- **Limits**: the search runs on the fuel the calling search has left and is charged back, as a negation's search is.

## 6. Implementation

Rust, in `anthill-core`. Scaland loads the new declarations (it reads the same `stdlib/` files) and does not implement the relation.

1. **Proof mode in the search.** A search can run in proof mode. Each goal it puts in a frame then carries the proof node it belongs to: the clause it was opened for, or the `forall`, `some` or `|` it came from. The resolver reorders and flattens goals; the tag goes with each goal, so the proof follows the rule as written.
   - **A proof of `g`**: each frame carries the proof so far, as a structure shared with the frame it was copied from, so backtracking drops a branch's part of it with the branch. An answer's proof is the root node when its last goal is discharged.
   - **A proof of `!g`**: when a goal fails (a builtin that fails, no clause matches, every candidate of its choice point exhausted), the failure is added to its node; when the search ends with no answer, the nodes are the refutation.
   - **A discharge** (`step_forall_impl`) opens a node of its own, holding its fresh constants and its assumptions. A goal answered by an assumption (`Candidate::Assumption`) is a `by_assumption` leaf. Inside the discharge each fresh constant is a rigid variable, and a rigid variable must not escape its discharge (`gap_skolem_does_not_leak_into_caller_solution`), so the proof holds each one as data that names it, never as the variable.
   - **Off by default**: an ordinary query and an ordinary `!g` carry no tags and no proof, and their cost is measured unchanged.
2. **The relation** is a body-less `rule of(?goal, ?proof)` in the scope of `SLDProof`, in `reflect.anthill`. As built (2026-11-22):
   - **Its first argument is a GOAL position**, as `not`'s is (`KnowledgeBase::goal_slot_readings`): a rule body's `SLDProof.of(good(6), ?p)` reads `good(6)` as a goal and checks its name, and does not compute it as a value. A typed column (`?goal: Term`) was tried first and is refused on a body-less declaration, which stores no clause to enforce it in.
   - **The tag is bound once the names are defined** (`KnowledgeBase::resolve_builtins`, `SORT_SCOPED_BUILTIN_RELATIONS`): a sort's scope does not exist at bootstrap, where the other builtin relations are minted. An `enum` body holds the declaration.
   - **`step_init` sends it to `step_sld_proof_of`**, as it sends `not` to `step_naf`. It runs the goal's search in proof mode with the depth and fuel `step_naf` gives its search, charged back. For `!g` it waits on a non-ground `g`, has no answer where `g` has one, and is undecided where the search is. Each answer of `g` is handed back as two unifications — `g` with its instance in the answer, `?p` with the proof — followed by the answer's unchecked goals, one choice-point continuation per proof.
   - **A proof is a stored term**, built from the record (`kb/sld_proof.rs`); each goal in it has the final substitution applied, each fresh constant a `FreshConstant`, and each call quoted, as a `Term` field holds one. A goal with no term form is an error, never a stand-in.
   - **The record**: a node per goal, an attempt per asking, an instance per answer source taken; an attempt that is rotated, or whose goal a builtin replaces by the goal it turns into, is POSTPONED and never counted a failure; an attempt EXITS when the instance it took has no goal left in the frame, which `ProofRecorder::proved` propagates upward.
3. **The specification**: a paragraph in `docs/kernel-language.md` §8.3, after "Negation", once the user approves its text, and §4.1's sentence on labels extended to derived clauses.
4. **Tests** drive each row of the acceptance, in `anthill-core/tests/include/`, registered in `wi_tests.rs`, and the command line through an ordinary query in `anthill-cli/tests/include/`.

### Labels for derived clauses

Decided with the user (History 20). WI-20261121-MVQP8 gives a label to every clause written in source: the converter makes it from the clause's text. A clause the loader DERIVES has no text and gets none, so a proof could not say which clause it used. Each derived clause gets a label too, the derivation's name:

- the induction principle: `<Sort>.induction`, its own name, one clause per sort;
- a sort's domain, one clause per constructor: the domain's name with the constructor (`IntList.domain-i_cons`);
- the `<op>__defeq` rule, labeled already;
- every other kind of derived clause, named the same way: the derivation, and what tells its clauses apart where it makes several of one predicate.

So that no derived clause is missed, the loader's way of storing a clause takes a label, not an optional one: a site that has none does not compile, and the compiler finds every kind. A fact a program asserts while it runs is not the loader's and stays outside this rule (§7, question 2). The cost, one symbol per derived clause, is measured on the stdlib's load: its symbols and its time, before and after.

**As built (2026-11-22).** Every entry point that stores a clause takes a `ClauseLabel`: `Written` (the source's label or the converter's), `Derived` (named by the derivation), `Content` (labeled by what it stores) or `Runtime` (no label). One function, `label_clause`, sets the label. A clause that already has a label keeps its first one, and a `Derived` label that already labels another live clause is a panic.

| Clause | Label |
|---|---|
| induction principle | `<Sort>.induction`, the predicate's own symbol, stored once per sort |
| a domain's value face; a primitive's domain clause | `<Sort>.domain`; its relation (`Int64.domain`) |
| a domain's case | `<Sort>.domain-<ctor>` |
| a constraint's reflection row; its goals clause | the constraint's label; `<label>-goals` |
| `<op>__defeq` (made at proof time) | `<op>__defeq`, in the operation's declaring scope |
| an operation's equation | as the equation written as a rule would be: `double-<HASH>` |
| a reflect row, a provision, a flow fact | `Content`: `<about>.<predicate>-<HASH>`, under the declaration it is about (`IntList.SortInfo-…`) |

The hash is MVQP8's digest of the clause's kind, its domain and its head. It reads qualified names and numbers variables by first occurrence, so a row has the same name in every load.

Two decisions came from measurement:

- **A minted label is listed in no name table.** It is not a scope local and not in the qualified-name table. As a scope local, a label became a member of the declaration it was about, and `wi_rmzqz` refused a type alias "declared both as a type alias and with members of its own". In the qualified-name table, which `sort_has_constructors` reads whole, the standard library's typer went from 193 to 287 ms. So a proof prints a minted label, but no written name resolves to it. Only the induction principle's and a domain's labels can be cited by text, because they are the predicates' own names.
- **`KB.layer_symbols` leaves minted labels out**, as `KB.layer_clauses` leaves out derived clauses. Without that, the guardians gate refused well-formed candidates, because a later load derives flow facts about the library's `List.foldLeft` and `foldRight` that the library's own load did not.

The cost, on the stdlib's load:

| | Before | After |
|---|---|---|
| clauses labeled | 243 of 6,306 | all 6,306 |
| symbols | 5,870 | 11,876 |
| load time, optimized (median of 15) | 351–352 ms | 363–367 ms (about +4%) |
| copy of the shared base | 6.7 ms | 7.4–7.5 ms |

A constraint's row records the constraint's site as its item's span, not as a head span. A head span would put the row under the typer's construction check, which refuses a quantified constraint's row: its `LogicalQuery` holds a variable's name as a string where the schema says `Symbol`. That mismatch was already there and is not fixed here. Two rows that are the same up to their variables get two labels with the same name.

## 7. Open questions

1. **An answer that holds only if a left-over goal holds.** When the search meets a goal it cannot check yet, because the goal still has an unbound variable, it does not fail: it answers, and hands the goal back unchecked. That is a conditional answer, and the goal it hands back is its residual. Over `rule big(?x) :- ?x > 5`, `anthill query 'big(?x)'` prints `?x = ?_` with `residual: gt(?_, 5)`: `big(?x)` holds for any `?x`, provided `?x > 5`. A proof of that answer, `SLDProof.of(big(?x), ?p)`, is "by the clause `big-…`, using `?x > 5`", and `?x > 5` was never proved. Proposed: a leaf `residual(goal: Term)` for each goal handed back unchecked, here `residual(?x > 5)`, and `SLDProof.of`'s answer conditional on the same goals, as the query's answer is.
2. **A fact asserted while a program runs** (through `KB`, or a store such as anthill-todo's) has no label, and its proof names it `none`, as a `forall` element. A label for each would cost a symbol per fact at run time. Proposed: leave it `none`; the proof's `goal` is the fact itself. (A derived clause's label, this question's first form, is decided: §6, *Labels for derived clauses*.)
3. **A goal that raises** (a zero divisor): the search reports the error, and its answers are incomplete. Proposed: as for negation, undecided, a conditional answer, and the error reported.
4. **Goals the loader added to a body** (a typed head column's domain check, a requirement's dictionary lookup): proposed, proved or refuted like any other goal, written as the loader wrote them.
5. **Size.** A proof is as large as the derivation: a rule that walks a list of a thousand elements has a proof a thousand deep. The depth limit bounds it, as it bounds the search. Is a bound on the proof's own size wanted as well?

## Acceptance

Each row driven, as in WI-20261121-G8E02:

- `SLDProof.of(good(6), ?p)`: one answer, the `by_clause` of §3, down to `by_builtin(6 > 0)`, `by_builtin(6 > 5)` and `by_builtin(6 % 2 = 0)`;
- `SLDProof.of(!good(1), ?p)`: one answer, through `big(1)` and `builtin_false(1 > 5)`;
- `SLDProof.of(good(1), ?p)` and `SLDProof.of(!good(6), ?p)`: no answer;
- `SLDProof.of(edge(1, ?y), ?p)`: two answers, `?y = 2` and `?y = 3`, each by its fact's label;
- `!all_big([7, 3, 9])`: a step `3 > 5` under the `forall`;
- `!reach_big(1)`: two steps, `big(2)` and `big(3)`;
- `!cheap(p1)`: a step for each clause, each clause by its label;
- `!edge(5, 1)`: `refuted(edge(5, 1), [])`;
- `!notq(1)`: a step `!q(1)` because the proof of `q(1)`;
- `!guarded(1)`: a conditional answer, no proof;
- `SLDProof.of(big(?x), ?p)`: a conditional answer, its residual `?x > 5`, and its proof `by_clause(big(?x), some(big-…), [residual(?x > 5)])`;
- `SLDProof.of(IntList.induction(prop_holds), ?p)`: the proof of §3.1, by the clause `IntList.induction`, its base case by the fact and its step case a `by_discharge` with `prop_holds(t)` assumed and used as `by_assumption`; no fresh constant appears as a variable in the answer;
- after the stdlib's load and after a program's, every clause the loader stored has a label; a derived clause's is its derivation's name (§6, *Labels for derived clauses*); the stdlib's symbols and load time, before and after, are recorded;
- `SLDProof.of(!IntList.induction(q), ?p)`, over a `q` that holds for `i_nil` and is not preserved by `i_cons`: the step case refuted inside a `by_discharge`;
- `anthill query 'SLDProof.of(!good(1), ?p)'` prints the proof;
- an ordinary query and an ordinary `!g`, with proof mode off, take the same number of steps and give the same answers as before the change;
- back-out: without proof mode, the rows above do not load or have no answer.

## History

All 2026-11-21, with the user, in this order.

1. The ticket was reviewed against the code; its measurements hold.
2. The shop model's tests are written in anthill, so a printout alone does not serve them.
3. The in-language form is part of WI-20261121-G8E02.
4. A test checks the failing goal's name, not the exact label.
5. "We need reflect interface": it is declared in `anthill.reflect`.
6. Stopping at the first failure was to be an option.
7. It is a relation a rule calls directly.
8. No log of an earlier search: a search stops at the first failing goal and never asks the rest.
9. The answer was to carry a reason and the last clause checked.
10. A design document comes first, with the API explained.
11. A limit was to be a decided answer with a reason.
12. The first version's §1 gave a wrong reason, a description of how a query runs; corrected.
13. The user asked for a radical simplification: the proposal had become a complex structure.
14. The user's reframing: the answer is the proof of `!good(1)`, and the proof holds all the information. The second version followed it. It replaced the walker, the `Failure` record and its reasons (9 and 11 withdrawn: an undecided goal is undecided, as for negation), the first/all option (6 withdrawn), and `query --explain` with its JSON (an ordinary query prints the proof). It revised 8: the search itself keeps what it did, in a proof mode; the goals after the first failure are still never asked, and the diagnostic needs none of them.
15. Checking a list of invariants, each one, is not reflect's concern: the relation returns the diagnostic of why one goal does not hold, and that is all. So the proof of `!g` has at most one answer, the proof the search finds; several proofs of `!g` as several answers, the shop's harness over the relation, and checking names at load are withdrawn. If every invariant needs checking, the test harness asks about each of them.
16. The user asked why only refutation, how it differs from a positive proof, and why no operator returns the proof of a query. Nothing returns one today, positive or negative, and the two kinds nest, so one relation, `proof_of`, gives both: the proofs of `g` and the proof of `!g` (confirmed by the user). The second version's `refutation` and `NegProof` are replaced; its `holds(goal)` leaf is gone, since a failing `!q(1)` is explained by the proof of `q(1)`.
17. The user named the type: `SLDProof` or `KBProof`.
18. The user asked how a proof by induction looks. An induction principle is an ordinary clause whose body applies a predicate argument and holds a discharge, `(forall(?x…), A -: C)`. Added, with the user's agreement: `by_discharge` (the fresh constants, the assumptions, and the consequent's proof or refutation) and `by_assumption` (a goal answered by an assumption, the induction hypothesis), the example of §3.1, and three points: fresh constants are held as data, a derived clause's label (§7, question 3), and proofs made by `anthill prove` are not SLD proofs.
19. The type is `SLDProof` (user).
20. Every clause the loader stores gets a label, a derived one included (user, on "but we added labels in MVQP8": that work labels the clauses written in source, and the loader's derived clauses have none). §6, *Labels for derived clauses*; §7, question 3 is now about facts asserted at run time.
21. The relation is `anthill.reflect.SLDProof.of`, declared in the type's own scope and called `SLDProof.of(goal, ?p)` (user: first `sld_proof_of`, then "better inside the type's scope"; `proof_of` was the working name). The names question is closed, and §7's questions are renumbered: the fact asserted at run time is question 2.
22. The user approved this version, with §7's proposals as written. Next: the text in `docs/kernel-language.md` §8.3 and §4.1, for the user's approval, then the implementation.
