## Attributes

- id: WI-20261013-PR8SP-a-nullary-constructor-is-no
- created: 2026-10-13T06:01:50Z

- status: Open
- status_agent: user
- status_at: 2026-10-13T06:01:50Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A NULLARY CONSTRUCTOR IS NO CONSTANT OF ITS SORT IN THE SMT MAPPING — A PROBLEM FOR DISCHARGE: a claim about a named constructor proves when it is false, a lemma about a predicate over such a sort cannot be used of a named one, and a rule that bounds a variable by the sort cannot be discharged at all. Found while counting for WI-20261012-KF2SD; measured 2026-10-13 on main at bcad34e8 with WI-20261012-CDHSQ's change on it, `anthill prove --no-cache`, z3 4.16.0.

WHAT IS THERE: `docs/smtlib-forward-mapping.md` §2 maps a sort with entity constructors to `declare-datatypes` (`sort Color` → `(declare-datatypes ((Color 0)) …)`), and `anthill-smt-gen` does not: its sorts are `Real`, `Bool` and a scope's abstract parameter (`SmtSort`, `sort.rs`). So `Leader` of `sort Drone` (`entity Leader`, `entity Follower`) has no term, and what is done with it hangs on where it stands:
  (1) a ground argument of a call matched to a FACT — compared by name (`occs_match`). The one reading that works.
  (2) a fact's slot the call has a VARIABLE at — passed over (the fact reader: "Nullary symbol like `Leader`. Skip"), and so is such an argument of an inlined call (`bind_head_arg`: "not arithmetic; ignore"): the variable is bound to nothing.
  (3) the right side of an equation, `?who = Follower` — nothing of it reaches the document, and a call that names `?who` is matched as if the variable were free (the fact reader: a variable slot matches any fact's).
  (4) an argument of a call STATED as a relation (a cited lemma's premise, the consumer's call of it) — refused (`state_predicate_call`, CDHSQ); a head variable bounded by the sort — refused (`sort.rs`).

MEASURED, each with `sort Drone` as above:
  fact speed_of(Leader, 5.0)      fact speed_of(Follower, 50.0)
  rule named_other: lte(?v, 10.0) :- ?who = Follower, speed_of(?who, ?v)      proof named_other by z3 end
`✓ named_other: proved (z3: unsat)`, its whole document `(assert (not (<= 5.0 10.0)))` — the Follower's speed is 50. The equation leaves nothing in the document, and the call, its argument a variable, is matched to the first fact. The same with the equation written after the call. (`?who = Leader` proves too, and is true.) THIS IS NOT KF2SD's ALONE: read as the disjunction of the two facts, the disjunct is chosen by `?who`, which has no term to choose it by.
  rule speed_of(?who, ?v) :- gte(?v, 0.0)
  rule lemma: lte(?v, 9.0) :- speed_of(?who, ?v)                proof lemma by trust(…) end
  rule var_call:  lte(?v, 10.0) :- speed_of(?d, ?v)             proof var_call using lemma by z3 end       ✓ proved — the relation is `(Real Real) Bool`, the drone a `Real`
  rule ctor_call: lte(?v, 10.0) :- speed_of(Leader, ?v)         proof ctor_call using lemma by z3 end      error: … argument 1 is the bare name `Leader`, which is not written as an argument
So a lemma of EVERY drone cannot be used of one. And a lemma of one, `lte(?v, 9.0) :- speed_of(Leader, ?v)`, cannot be cited by anything: "cite … could not be lowered under its translation policy", the same refusal.
  rule bounded(?who: Drone, ?v) :- gte(?v, 0.0)
  rule typed(?who: Drone, ?v) :- bounded(?who, ?v), lt(?v, 0.0)   proof typed by z3 end
`error: … the bound of `?var_1` has no SMT sort: a bound is lowered when it is `Int64`, `Float`, `Bool` or an abstract parameter of an enclosing sort`.

WHY IT IS A PROBLEM FOR DISCHARGE: examples/webots-modelling/lf1 is a model over `Drone` — `real_pose_at(?k, Leader, ?l)`, `real_velocity_at(?k, ?drone, …)`, `distance_at_step`, which is of the two — and a call that names a drone can be READ THROUGH to a fact or a body and cannot be STATED. Reading through is what KF2SD is about: counted there, the one predicate of several clauses in lf1 and the suites is `real_pose_at/3` (two base facts and the bodied step), read six times in lf1's four top-level safety proofs, each time as its base fact. Whatever is decided for such a call — refused, the clauses' disjunction, or the uninterpreted relation — a relation over a drone and a choice of clause by a drone both need the constant. `velocity_envelope`'s premise is `real_velocity_at/5` over `?drone`: lifted (it is cited `by trust` today, so it is not), its consumer could not state a call at `Leader`.

WHAT IS PROPOSED, to decide: a sort ALL of whose constructors are nullary (an enumeration: `Drone`, `Color`) is a sort of the document, its constructors constants of it, pairwise distinct and exhaustive; a variable bounded by it, or at a position a fact or a bound gives that sort, is of it; `?who = Follower` is an equation on it; a fact's constructor slot met by a variable is that equation.
  WHICH ENCODING — measured on z3 4.16.0: `(declare-datatypes ((Drone 0)) (((Leader) (Follower))))` is refused under `QF_LRA`, `QF_NRA`, `QF_UFNRA` and `LRA` ("logic does not support algebraic datatypes" — and the run goes on to answer `sat`), and accepted under `ALL`. `(declare-sort Drone 0)` with a constant for each constructor, `(assert (distinct Leader Follower))` and `(or (= who Leader) (= who Follower))` for each variable of the sort is accepted under `QF_UFLRA`, `QF_UFNRA` and `UFLRA`, which are the logics a document with a declaration already has (`sort.rs`, the `UF` it adds). So: the declared sort keeps every proof's `logic:`; the datatype is what the mapping document says and moves each such proof to `ALL`.
  NOT HERE: a constructor WITH fields (`Pose(position: …)`, `some(?x)`) — an entity is read by its fields' constants and a constructor-shaped head by the call's shape (WI-687); a datatype for those is a ticket of its own.

THE CONTROL: `named_other` is a COUNTEREXAMPLE and its twin at `Leader` proves, and both prove when backed out; `ctor_call` proves using the lemma of every drone, and does NOT prove using a lemma of `Follower` alone; `typed` is read and proves. A proof that names no such sort has the document it had, to the byte. lf1's verdicts are as they are, or each that is not is listed with why.

DONE WHEN: the control rows hold and fail when backed out; `docs/smtlib-forward-mapping.md` says which of its §2 the emitter does (today it reads as if a datatype were emitted) and line 316's refusal of a bare name is narrowed to what is still refused; the documents that moved are listed; the gate is green.

## Changes

### 2026-10-13T08:33:24Z — feedback — user

AFTER WI-20261012-KF2SD (measured 2026-10-13 on its tree; docs/measurements/test-infrastructure/several-clauses-2026-10-13.txt §3, §6 (9)). `named_other` above no longer proves: `speed_of(?who, ?v)` is answered by two facts and is REFUSED — and so is `named`, the true one, for the equation `?who = Follower` still binds the variable to nothing a fact is selected by. WHAT MOVED TOWARD THIS: a FACT's constructor slot binds the call's variable, held as a construction is and with no SMT term — `fact lead(Follower)`, `lte(?v, 10.0) :- lead(?who), speed_of(?who, ?v)` reads the Follower's fact and is a COUNTEREXAMPLE, where the variable was left bound to nothing, the first fact read and the claim proved. That is SELECTION, and not the constant: readings (3) and (4) are as measured — the equation, the stated relation (`ctor_call`, the lemma of one drone), and the bound.

### 2026-10-14T09:09:09Z — feedback — user

AFTER WI-20261013-1KF32 (2026-10-14; docs/measurements/test-infrastructure/disjunction-2026-10-14.txt). A call several facts can answer is read in a WORLD for each, the document their disjunction, so `speed_of(?who, ?v)` over the two facts is two worlds whatever `?who` is: `named_other` (`?who = Follower`) is a COUNTEREXAMPLE — the verdict it should have, for a reason it should not: the Leader's world is read too — and `named` (`?who = Leader`, TRUE: 5 <= 10) is a COUNTEREXAMPLE as well, by the Follower's world, which the equation does not rule out. Measured on main at 107a1a02. A FACT's constructor slot does select (`lead(?who), speed_of(?who, ?v)` is one world, the drone's): it binds `?who` in its world, held as a construction is. What is still this ticket's is the equation with a nullary constructor, and the constant itself — the stated relation and the bound, as measured.

