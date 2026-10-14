# SMT-LIB Forward Mapping

This document defines how anthill kernel constructs map to SMT-LIB 2.6 — the **forward direction**: from resolved KB knowledge to SMT-LIB theory. The generated output is suitable for feeding to SMT solvers (Z3, CVC5, etc.) for verification of properties, constraint checking, and counterexample generation.

## 1. Overview

Unlike the Rust forward mapping (which walks `ParsedFile` for bootstrap reasons), the SMT-LIB codegen walks the **resolved `KnowledgeBase`** — querying `SortInfo`, `EntityInfo`, `OperationInfo` facts and user-defined rules. This means all symbol resolution, scope chain processing, and type parameter binding have already been performed by the loader.

**Mapping summary:**

- **Sorts with entity constructors** → algebraic datatypes (`declare-datatypes`)
- **Abstract sorts** → uninterpreted sorts (`declare-sort`)
- **Operations** → function declarations (`declare-fun`) or recursive definitions (`define-fun-rec`)
- **Rules (laws)** → universally quantified assertions
- **Constraints (denials)** → satisfiability checks
- **Contracts (requires/ensures)** → verification conditions

**Use cases:**

1. **Property verification** — check that laws are consistent and derived properties hold
2. **Counterexample generation** — find inputs that violate constraints or contracts
3. **Spec consistency** — verify that a set of axioms is satisfiable
4. **Obligation discharge** — prove operation contracts, elevating trust to `verified`

## 2. Mapping Rules

### Summary Table

| Anthill construct | SMT-LIB construct |
|---|---|
| Primitive `Int64` | `Int` |
| Primitive `Bool` | `Bool` |
| Primitive `String` | `String` |
| Primitive `Float` | `Real` (or `(_ FloatingPoint 11 53)` with FP theory) |
| Primitive `BigInt` | `Int` (SMT-LIB Int is arbitrary-precision) |
| Sort with entities (ADT) | `declare-datatypes` |
| Parametric sort with entities | `declare-datatypes` with `par` |
| Abstract sort (`sort T = ?`) | sort parameter in `par`, or `declare-sort` at top level |
| Type alias (`sort Money = Int64`) | inline substitution (no separate declaration) |
| Standalone `entity E(fields)` | single-constructor datatype |
| `operation` (with defining rules) | `define-fun-rec` |
| `operation` (unimplemented) | `declare-fun` (uninterpreted) |
| `rule head :- body` (derivation) | `(assert (forall (...) (=> body head)))` |
| `rule lhs = rhs` (equation) | `(assert (forall (...) (= lhs rhs)))` |
| `fact term` (ground) | `(assert term)` |
| `constraint inv :- guard` | `(assert (forall (...) (=> guard inv)))` |
| `requires precond` (on operation) | precondition in verification condition |
| `ensures postcond` (on operation) | postcondition in verification condition |
| `requires Spec[T]` (spec satisfaction) | axiom group (section 5) |
| `namespace` | comment block (SMT-LIB has no modules) |
| `List[T = X]` | `(List X)` (parametric datatype application) |
| `Option[T = X]` | `(Option X)` (parametric datatype application) |

### 2.1 Primitive Types

```smt2
; Int64    → Int (arbitrary-precision)
; BigInt → Int (same — SMT-LIB Int is already arbitrary-precision)
; Bool   → Bool
; String → String
; Float  → Real (default) or (_ FloatingPoint 11 53) (configurable)
```

### 2.2 Sort with Entities → Algebraic Datatype

Queried from KB via `SortInfo` facts (sort kind = `Defined`) and their `EntityInfo` children.

```
sort Color {                          (declare-datatypes ((Color 0))
  entity red               →           (((red) (green) (blue))))
  entity green
  entity blue
}
```

Fields become named selectors:

```
sort Duration {                       (declare-datatypes ((Duration 0))
  entity Duration(                →     (((mk-Duration
    amount: Int64,                            (Duration-amount Int)
    unit: String)                           (Duration-unit String)))))
}
```

**Constructor naming:** Entity names become constructor names directly. When a sort has a single entity with the same name (standalone entity sugar), the constructor is prefixed with `mk-` to avoid collision with the sort.

**Tester predicates:** SMT-LIB generates `is-ConstructorName` for each constructor automatically.

### 2.3 Parametric Sort → Parametric Datatype

Identified via `SortInfo.parameters` (non-empty list of type parameter names):

```
sort List {                           (declare-datatypes ((List 1))
  sort T = ?             →             ((par (T)
  entity nil                              ((nil)
  entity cons(                             (cons (head T) (tail (List T)))))))
    head: T,
    tail: List)
}
```

The arity equals `|SortInfo.parameters|`.

### 2.4 Mutually Recursive Sorts

The codegen computes SCCs (strongly connected components) from sort reference graphs. Mutually recursive sorts are grouped into a single `declare-datatypes`:

```smt2
(declare-datatypes ((Tree 1) (Forest 1))
  ((par (T)
    ((leaf (leaf-val T))
     (node (node-val T) (children (Forest T)))))
   (par (T)
    ((empty-forest)
     (forest-cons (forest-head (Tree T)) (forest-tail (Forest T)))))))
```

### 2.5 Abstract Sort → Uninterpreted Sort

Sorts with `SortKind::Abstract` and no defining alias:

```
sort AccountId = ?                    (declare-sort AccountId 0)
```

### 2.6 Type Alias → Inline Substitution

Type aliases (SortInfo with `SortAlias` fact) produce no SMT-LIB output. The target sort is substituted inline.

## 3. Operations

### 3.1 Uninterpreted Operations → `declare-fun`

Operations (from `OperationInfo` facts) without defining rules:

```
operation balance(a: Account) -> Money

→ (declare-fun balance (Account) Int)
```

### 3.2 Defined Operations → `define-fun-rec`

Operations with constructor-complete equational rules become recursive definitions:

```
operation length(l: List) -> Int64
rule length(nil) <=> 0
rule length(cons(?x, ?xs)) <=> add(1, length(?xs))

→ (define-fun-rec length ((l (List T))) Int
    (match l
      ((nil 0)
       ((cons x xs) (+ 1 (length xs))))))
```

**Strategy selection:** If rules form a complete, non-overlapping constructor-case definition → `define-fun-rec` with `match`. Otherwise → `declare-fun` + `assert` per rule.

### 3.3 Arithmetic and Comparison Builtins

Prelude operations on primitives map to SMT-LIB built-ins (plus `ite`, which is a
rule-level functor rather than an operation — WI-887).

**The mapping is by SYMBOL IDENTITY, not by name** (WI-897). The table below is keyed
by qualified name, resolved against the KB once (`SMT_BUILTINS` / `SmtBuiltinTable` in
`anthill-smt-gen/src/lib.rs`), and every later question is a `Symbol` compare. A
user's own operation that happens to be spelled `add` — even one whose qualified name
is `Numeric.add`, which a top-level `sort Numeric` mints exactly — is a different
symbol and is **not** lowered; smt-gen refuses it by name rather than guessing it meant
the prelude's. Before WI-897 each row was a string compare carrying a
fully-qualified / sort-qualified / bare triple, and the loose arms silently
reinterpreted such an operation (the hazard WI-680 recorded).

| Anthill operation | SMT-LIB |
|---|---|
| `anthill.prelude.Additive.add(a, b)` | `(+ a b)` |
| `anthill.prelude.Additive.sub(a, b)` | `(- a b)` |
| `anthill.prelude.Multiplicative.mul(a, b)` | `(* a b)` |
| `anthill.prelude.Int64.div(a, b)` | `(div a b)` |
| `anthill.prelude.Float.div(a, b)` | `(/ a b)` |
| `anthill.prelude.Float.neg(a)` / `anthill.prelude.Int64.neg(a)` | `(- a)` |
| `anthill.prelude.Float.abs(a)` / `anthill.prelude.Int64.abs(a)` | `(anthill_abs a)` |
| `anthill.prelude.Float.cos(a)` / `.sin(a)` | `(anthill_cos a)` / `(anthill_sin a)` |
| `anthill.prelude.PartialEq.eq(a, b)` | `(= a b)` |
| `anthill.prelude.PartialOrd.gt(a, b)` | `(> a b)` |
| `anthill.prelude.PartialOrd.lt(a, b)` | `(< a b)` |
| `anthill.prelude.PartialOrd.gte(a, b)` | `(>= a b)` |
| `anthill.prelude.PartialOrd.lte(a, b)` | `(<= a b)` |
| `anthill.prelude.Bool.not(a)` | `(not a)` |
| `anthill.prelude.Bool.and(a, b)` | `(and a b)` |
| `anthill.prelude.Bool.or(a, b)` | `(or a b)` |
| `anthill.prelude.Bool.ite(c, t, e)` | `(ite c t e)` |

`abs`, `cos` and `sin` have no SMT-LIB Real form and ride as uninterpreted functions —
`anthill_abs` gets a synthesised `(define-fun …)` prelude, `anthill_cos`/`anthill_sin`
get the Pythagorean identity per argument and nothing more (WI-681).

The comparisons live on `PartialOrd` and equality on `PartialEq` (WI-644 /
proposal 004, WI-1109): `Ord` declares neither, so `import anthill.prelude.Ord.{gte}`
resolves *through* the tower to `anthill.prelude.PartialOrd.gte` and lands on the row
above.

These apply when arguments are primitive types. For user-defined sorts, operations remain as uninterpreted functions with their axioms.

## 4. Rules and Laws

### 4.1 Equational Rules → Universal Assertions

```
rule add_comm: add(?a, ?b) <=> add(?b, ?a)

→ (assert (forall ((a T) (b T))
    (! (= (add a b) (add b a))
       :named add_comm)))
```

The `!` annotation with `:named` preserves the rule label for unsat cores and proof traces.

### 4.2 Conditional Rules → Universal Implications

```
rule ancestor(?X, ?Z) :- parent(?X, ?Y), ancestor(?Y, ?Z)

→ (assert (forall ((X Person) (Y Person) (Z Person))
    (! (=> (and (parent X Y) (ancestor Y Z))
           (ancestor X Z))
       :named ancestor_trans)))
```

### 4.3 Ground Facts → Assertions

```
fact parent("alice", "bob")

→ (assert (! (parent "alice" "bob") :named fact_parent_alice_bob))
```

### 4.4 Pattern-Matching Rules (non-`define-fun-rec` form)

When rules are partial or overlapping, expressed via constructor testers and selectors:

```smt2
(assert (forall ((l (List T)))
  (=> (is-nil l) (= (length l) 0))))
(assert (forall ((l (List T)))
  (=> (is-cons l)
      (= (length l) (+ 1 (length (tail l)))))))
```

### 4.5 Rules with Explicit `-:` (then) Conclusion

Anthill rules with the optional `-:` (then) clause encode positive theorems of the form `∀ vars. body ⇒ conclusion`. This clause is **Z3-specific** — SLD and the derivation-trace prover ignore it. Two SMT-LIB encodings depending on whether the rule is being *discharged* or *cited*:

**Discharge** (the rule is the proof target, `proof X by z3(...)`):

```
rule lower_bound_holds(?w)
  :- gte(?x, 5.0), eq(?w, ?x)
  -: gte(?x, 3.0)
```

```smt2
(assert (>= var_x 5.0))                         ; premises
(assert (not (>= var_x 3.0)))                   ; negated conclusion
(check-sat)                                     ; unsat ⇒ theorem holds
```

The conclusion is *negated* and added as the final assertion. Multiple conclusion clauses become `(assert (not (and …)))`. The verdict `unsat` certifies the theorem; `sat` returns a counterexample.

**A rule call in the body being discharged** (WI-20261012-KF2SD, WI-20261013-1KF32). A call of a rule's predicate is a premise like any other, and is *read*: bound to the slots of a fact, or opened as the body of the clause it calls with the call's arguments for the head's — and with its own variables, those its head was not passed, named past every name of the document (`var_<n>`, continued from the proof's clause, on across the worlds of one document; WI-20261012-BR7P3): by its index such a variable was the proof's variable of that index, and the document related two variables as one. A construction passed to the clause's head is closed over the caller's frame before it is read there, for the same reason, and a variable bound to a construction written as a term — an operand, a relation's argument — is refused: it has no SMT term. It is read by **the clauses that can answer it** — those of the call's arity whose head no argument of the call rules out. A number against another number and a constructor against another constructor rule a clause out. The call's own variable counts as what the body has bound it to, a number (`?k = 1`) or a construction (`?o = some(2.0)`, or a fact's slot it met earlier, a nullary constructor such as `Leader` among them); a free variable, a variable *inside* a construction, a computed term and a name that is no constructor rule nothing out. So

```
fact initial_pose(Leader, Pose(…))
fact initial_pose(Follower, Pose(…))
rule base_case(?w) :- initial_pose(Leader, ?l), …          -- one fact answers: read
```

is read by the Leader's fact, and `gain(none, ?r)` by the clause `rule gain(none, ?r) :- …` and not by `rule gain(some(?x), ?r) :- …` beside it. A clause of another arity is no candidate: `span/2` beside `span/3` is two predicates.

**Several clauses that can answer: a world for each** (WI-20261013-1KF32). A predicate of several clauses holds when *any* of them does, so the call means their disjunction. Read as the first one — which is what was done until WI-20261012-KF2SD, the first fact whose slots agreed and else the first clause with a body — the premise was stronger than the rule states, and a false claim proved; KF2SD refused it. Now the body is read once for each choice of the clause that answers each such call — a **world** — and the document asserts the disjunction of the worlds:

```
rule commanded_speed(?range, ?v) :- lt(?range, 5.0), ?v = 0.0
rule commanded_speed(?range, ?v) :- gte(?range, 5.0), ?v = 2.0
rule never_moves: lte(?v, 0.0) :- commanded_speed(?range, ?v)

(declare-const var_0 Real)
(assert (or
  ; 1: `….commanded_speed/2` (0 fact(s), 2 with a body) is answered by its clause 1 of 2
  (and (< var_0 5.0) (not (<= 0.0 0.0)))
  ; 2: `….commanded_speed/2` (0 fact(s), 2 with a body) is answered by its clause 2 of 2
  (and (>= var_0 5.0) (not (<= 2.0 0.0)))
))                                                         -- sat, range = 5: a COUNTEREXAMPLE
```

`(or D1 … Dn)` is unsatisfiable exactly when every `Di` is, so this is the document **split by the choice of clause**, kept one document: the proof's record, its cache key and its witness are of one, as they were. Each world reads the WHOLE body and the conclusion, by the reading a single clause always had: a variable a clause binds is substituted in its world (`?v` is `0.0` in the first, `2.0` in the second), an entity is an occurrence there, and a later call is selected by what the world bound — `speed_max(?who, ?v), margin(?who, ?m)` over a row per drone is two worlds, each drone's margin with its own speed, and not the four of every pairing. A variable no world binds is one constant of the document, declared once: the worlds are disjuncts, and `∃x. A ∨ B` is `(∃x. A) ∨ (∃x. B)`. Calls of several clauses that do not select each other are the **product** of their worlds, in the order of the choices, the first clause's world first; a body of **more than 64 worlds** is refused, naming each choice and how many it had. A function-like head's result (`rule f(?r) :- …`), which one world defines (`define-fun`), is one constant that each world equates. **What a world gives a variable** — a fact's slot, an entity's field, a head's number — is substituted where nothing has named the variable yet, as it always was; where a goal read before named it (`lte(?d, 10.0), start(?d)`) it stays a constant of the document and `(= var_d 5.0)` is asserted, and where the body defined it as a term (`?k = ?j + 1.0, start(?k)`) the term is equated with the value. (Substituted, the first was an undeclared constant — z3's "unknown constant", for one fact too — and the second dropped the definition.) So is every other place a variable is given a value (WI-20261014-FHEEK): an equation, a one-argument rule's result, an entity's field read by its constant, and what an inlined rule hands back to its caller, which is asked in the caller's frame. A variable defined twice is the equation of the two, and an alias (`?x = ?y`) given a value gives it to the variable it stands for. A variable the call writes twice meets ONE value: `twice(?k, ?k, ?r)` is answered by no clause whose head has two numbers there, and `pair(?x, ?x)` by no fact `pair(1.0, 2.0)`. Each world states, beside what it read, the calls a cited lemma's relation is of (below), so a lemma of a predicate of several clauses discharges every world. **A body that meets no such call is the document it was, to the byte.**

**A recursive clause is not unfolded.** A clause with a body read while a clause of its own predicate — the same name at the same arity: `span/2` calling `span/3` is no recursion — is being read is refused, naming the call and where it stands: a step beside its base case (`fact at(0, 1.0)`, `rule at(?k_next, ?x_next) :- at(?k, ?x), …`) would be a world for each depth, and a predicate of ONE such clause has no base case to stop at — `rule loop(?x) :- loop(?x), …` under a proof overflowed the stack and aborted the binary. Prove such a claim by induction, or give the case the proof is about a predicate of its own, as `examples/webots-modelling/lf1` does with `initial_pose` under `real_pose_at`. *Every* clause under the predicate counts, a lemma too: a rule stated with a label and the predicate for its head (`rule safe_weaken: safe(?x, ?n) :- safe(?x, ?m), …`) is a clause of it, as the resolver has it — and one that calls its own predicate makes every reading of the predicate recursive. A call that is **not read** is neither split nor refused, whatever its clauses — the conclusion of a structured proof skips its rule calls, and a lift states them (below). An **obligation** (`emit_obligation`, the bound of one term) is not split: there a call several clauses can answer is refused.

**What is answered and cannot be read is refused too**, each with its own words: a call no clause can answer (where those clauses are the predicate the body never holds — but a clause may be an operation's body specialized to another call's arguments, WI-687, and then it simply does not apply); a fact's slot met by a term over variables (`row(?x + 1.0, ?v)` against `fact row(5.0, 1.0)` is an equation that is not written); a fact's slot that is a string, a boolean or a name that is no constructor, met by a variable, which a variable is not bound to; a fact that names one variable in two slots; a number in the head of a clause with a body, met by a computed term or by a variable the body defined as one (`?k = ?j + 1.0, mode(?k, ?r)`); a construction in such a head met by a variable the body has bound to nothing (`rule gain(some(?x), ?r) :- …` called `gain(?o, ?r)`, WI-687). A variable in a *fact's* slot (`fact dflt(?who, 5.0)`) is every value there, and binds nothing. A number in a head met by a FREE variable binds it, as a fact's slot does: `mode(?k, ?r)` over `rule mode(0, ?r) :- …` and `rule mode(1, ?r) :- …` is a world for each, `?k` the number of its clause. Where no clause can answer a call in some world, the proof is refused, and the world is not dropped as `false`: "no clause" may be WI-687's specialization made for another call.

**The same rule in two more places** (the review of that change). *An entity premise* `Limit(cap: ?c)` reads the fields of the entity's fact, as constants of the document (`(define-fun cap () Real 5.0)`). An entity of several facts was read as its first, whichever fact the premise's own slots named (`Mode(kind: 2.0, cap: ?c)` took the cap of the row of kind 1), and KF2SD refused it; it is the table of a call in an entity's spelling, and is now a world for each fact the premise's slots ADMIT — a slot known to be a number rules out a fact whose field is another, so `Mode(kind: 2.0, cap: ?c)` is the fact of kind 2 alone — its variable slots bound to that fact's fields in the world (no field constant: one name would have every fact's value). EVERY fact of the entity is a row, one whose field is a variable too (`fact Lim(cap: ?any)`): there the slot's variable is free — such a row was no row, and alone it was the constant at `0.0`, so a claim it refutes proved. A variable in two slots (`M(kind: ?x, cap: ?x)`) admits a row whose two fields agree; a slot that is neither a variable nor a number (`kind: ?j + 1.0`) is refused; a premise no fact admits is refused. A cited lemma's lift is not split by an entity's facts, and refuses an entity of several, and a field of its one fact that is no number. And *the rule being proved* must be one clause: a name that resolves to several — a rule written with several heads is a clause for each, and so is a predicate written as several rules — is refused. It was proved of its first clause alone, while its lift is of every head, so `rule both: gte(?x, 0.0), gte(?x, 5.0) :- gte(?x, 1.0)` proved and was then cited for its second head. (The conjunction of the heads — `(assert (not (and H1 ... Hn)))` — is what proposal 032 §"Z3 backend" specifies; each clause numbers its variables by its own head first, so one clause's head is not written in another's frame, and that reading is not built.)

**Citation** (the rule is referenced from another proof's `using` clause, `proof Y using X by z3(...)`):

```
proof other_proof
  using lower_bound_holds
  by z3(logic: "LRA")
end
```

```smt2
; Cited-lemma assumptions (from `using` clause).
(assert (forall ((var_x Real)) (=> (>= var_x 5.0) (>= var_x 3.0))))
; ... rest of `other_proof` discharge follows
```

The lift function (`anthill_smt_gen::lift_rule_to_implication_clause`) emits `(forall (vars) (=> (and body) (and conclusion)))` directly — no inversion, no last-clause heuristic. The forall-quantification covers every free SMT variable produced from the rule's de Bruijn frame.

**Citability gate.** Only rules with an explicit `-:` clause are citable. Classical violation-shape rules (no `-:`) describe an *emptiness* claim ("body unsat") rather than an implication, and the lift refuses them with a clear error. Authors who want to cite a violation-shape claim must rewrite it in positive form.

**A premise that is a rule's predicate** (WI-20261012-CDHSQ; proposal 030 γ.1). A lift does not chase a rule call into its body, and it does not pass the call over either: the predicate is an **uninterpreted relation**, named by its qualified name and its arity, over the sorts of the call's arguments, declared once in the citing proof's document. The citing proof states *its own* call of that predicate with the same relation — the call a structured proof's conclusion skips, and the call an ordinary proof reads the body of, beside what it reads — and that is what discharges the premise:

```
rule related(?a, ?b) :- gte(?a, ?b)
rule lemma: gte(?a, ?b + 1.0) :- related(?a, ?b)       -- cited
rule holds: gte(?x, ?y + 1.0) :- related(?x, ?y)
proof holds using lemma by z3 end
```

```smt2
(set-logic UFLRA)
(declare-fun ns.related/2 (Real Real) Bool)
(declare-const var_0 Real)
(declare-const var_1 Real)
; Cited-lemma assumptions (from `using` clause).
(assert (forall ((var_0 Real) (var_1 Real))
  (=> (ns.related/2 var_1 var_0) (>= var_1 (+ var_0 1.0)))))
(assert (>= var_1 var_0))                       ; the body of `related`, read
(assert (ns.related/2 var_1 var_0))             ; the call, stated
(assert (not (>= var_1 (+ var_0 1.0))))
(check-sat)                                     ; unsat
```

A premise that is a fact's predicate (`start(?d)` beside `fact start(5.0)`), a one-argument rule's, a predicate of no arguments named bare (`ready`, the relation `ns.ready/0`), or a relational call of a bodied operation (`double(?x, ?r)`) is the same, the proof's call written with the value its own reading gave the argument (`(ns.start/1 5.0)`). A proof that cites no lemma with such a premise states no call and declares nothing: its document is the one it was. Passed over, as the premise was until this, the lift was `(=> true …)` — the lemma's conclusion handed over unconditionally — and `gte(?c, 5.0) :- gte(0.0, ?c)` proved by citing it.

Refused, and not left out. In the lift and in the proof alike: a call written with named arguments; an argument that is a bare name (a constructor, `Leader`; a constant of a carrier, which nothing here gives a sort) or a string; an argument that is no variable and that nothing gives a sort, under a scope that has an abstract parameter; a premise and a call at two signatures (an argument of another sort). In the lift: a premise that is a connective over goals (`a | b`, `a & b` — `or` and `and` are rules of the kernel, and were passed over by the same branch), and an entity premise's slot that is no variable (`Mode(kind: 2.0, cap: ?c)` — the slot was passed over, and with it which fact the lemma is of). A *head* that is a rule's predicate is no conclusion in this reading — its variables are the rule's parameters — so such a rule is "not citable", as it was.

## 5. Spec Satisfaction and Requires

### 5.1 Requires as Axiom Import

`SortRequiresInfo` facts link a sort to its required specs. The required spec's laws are emitted as axioms:

```
sort Ord {
  sort T = ?
  requires Eq[T]    ; imports Eq laws for T
}

→ (assert (forall ((a T) (b T))
    (= (neq a b) (not (eq a b)))))
```

**As `anthill prove` emits it** (WI-20261012-ZZ7PH; `anthill-smt-gen/src/sort.rs`, and proposal 030 §*What a requirement's record lowers to* for the decisions). A `by z3` proof is handed the laws of every `requires` of its enclosing scopes, and of what each required spec requires or provides in turn. The scope's abstract parameter is a sort of its own, a spec's operation at it an uninterpreted function named by the operation and the carrier, and a variable has that sort by its bound:

```
sort Scope
  sort T = ?
  requires Eq[T = T]

  rule irreflexive(?a: T) :- neq(?a, ?a)
  proof irreflexive by z3 end
end
```

```smt2
(set-logic UFLRA)

(declare-sort ns.Scope.T 0)
(declare-fun anthill.prelude.PartialEq.eq@ns.Scope.T (ns.Scope.T ns.Scope.T) Bool)
(declare-fun anthill.prelude.PartialEq.neq@ns.Scope.T (ns.Scope.T ns.Scope.T) Bool)

(declare-const var_1 ns.Scope.T)

; Laws of the specs the enclosing scopes require.
(assert (forall ((var_0 ns.Scope.T))
  (= (anthill.prelude.PartialEq.eq@ns.Scope.T var_0 var_0) true)))
(assert (forall ((var_0 ns.Scope.T) (var_1 ns.Scope.T))
  (= (anthill.prelude.PartialEq.neq@ns.Scope.T var_1 var_0)
     (not (anthill.prelude.PartialEq.eq@ns.Scope.T var_1 var_0)))))

(assert (anthill.prelude.PartialEq.neq@ns.Scope.T var_1 var_1))
(check-sat)                                  ; unsat
```

What decides each line:

| | |
|---|---|
| a variable's sort | its bound (`?a: T`, written on a head variable only; a step of a structured proof has its parent's), the signature of an operation it is an operand of, or the declared type of the entity field that binds it; where a rule read for the document is under a scope that has an abstract parameter one that none gives a sort is refused, elsewhere it is a `Real` |
| a spec's operation at a declared sort | an uninterpreted function `<operation>@<carrier>`, `eq` and the comparisons included; its default body is not a hypothesis |
| an operation at `Int64` / `Float` / `Bool` operands | its theory row (§3.3), or the "unhandled" error — never an uninterpreted function |
| an equation `lhs <=> rhs` | `(= lhs rhs)`; a guard is the premise |
| `constraint c: conclusion :- guard` | `(=> guard conclusion)` |
| a requirement at a concrete carrier (`Eq[T = Int64]`) | no law: a law is asserted only where every variable it quantifies is of a declared sort — `Int64` and `Float` are modelled by the reals, where a law is a theorem already or not known to hold. Left out and said |
| a law's premise that is a rule's predicate; a law that reads an entity's facts | the law is left out and said |
| a cited lemma's premise that is a rule's predicate | the uninterpreted relation of the predicate's name (§4.5, *A premise that is a rule's predicate*) — a lemma is proved and is handed to one proof, which states its own call; a law is of every provider, and is left out |
| the logic | the one written, with `UF` when a function or a relation is declared and without `QF_` when a hypothesis is quantified |

### 5.2 Fact-Based Spec Satisfaction

When a fact declares that a concrete type satisfies a spec, laws are instantiated:

```
fact Eq[T = Color]
rule eq(red, red) <=> true

→ (assert (= (eq-Color red red) true))
```

## 6. Constraints and Contracts

### 6.1 Constraints → Satisfiability Assertions

```
constraint non_negative: gte(balance(?a), zero) :- balance(?a, ?b)

→ (assert (forall ((a Account) (b Money))
    (! (=> (balance a b) (>= b 0))
       :named non_negative)))
```

To find violations, negate and check:

```smt2
(push)
(assert (exists ((a Account) (b Money))
  (and (balance a b) (< b 0))))
(check-sat)   ; sat → violation possible, unsat → invariant holds
(pop)
```

### 6.2 Operation Contracts → Verification Conditions

`OperationInfo.requires` and `OperationInfo.ensures` generate Hoare-triple VCs:

```
operation deposit(a: Account, m: Money) -> Account
  requires gt(m, zero)
  ensures eq(balance(result), add(balance(a), m))

→ (assert (forall ((a Account) (m Int) (result Account))
    (! (=> (and (> m 0)
                (= result (deposit a m)))
           (= (balance result) (+ (balance a) m)))
       :named deposit_contract)))
```

## 7. Codegen Architecture

### 7.1 Input: KnowledgeBase

The SMT-LIB codegen queries the resolved `KnowledgeBase`, not `ParsedFile`. All names are fully qualified, all scope resolution is done, all type parameters are bound.

**Key KB queries used:**

| Data needed | KB query |
|---|---|
| All sorts | `by_functor(SortInfo)` → extract `name`, `parameters`, `constructors` |
| Entity constructors | `by_functor(EntityInfo)` → extract `name`, `fields` |
| Operations | `by_functor(OperationInfo)` → extract `name`, `params`, `return_type`, `requires`, `ensures` |
| Sort kind | `sort_kind(term)` → `Abstract` / `Defined` / `Constructor` |
| Entity-parent | `sort_children(sort_term)` → constructor terms |
| User rules | `by_sort(Rule)` → head, body, domain |
| Spec requirements | `by_functor(SortRequiresInfo)` → `sort_ref`, `spec` (SortView with bindings) |
| Type aliases | `by_functor(SortAlias)` → source, target |

### 7.2 Pipeline

```
KnowledgeBase
  → collect SortInfo/EntityInfo/OperationInfo facts
  → build dependency graph (sort references in fields, operations, rules)
  → topological sort + SCC grouping for mutual recursion
  → emit preamble (set-logic, set-option)
  → emit datatypes (declare-datatypes, declare-sort)
  → emit functions (declare-fun, define-fun-rec)
  → emit axioms (assert for rules, facts, constraints)
  → emit queries (optional: check-sat, get-model, get-unsat-core)
```

### 7.3 Configuration

```rust
pub struct SmtLibConfig {
    /// SMT-LIB logic (e.g., "ALL", "QF_DTLIA", "AUFDTLIA").
    pub logic: String,
    /// Map Float to Real (default) or (_ FloatingPoint 11 53).
    pub float_as_real: bool,
    /// Append (check-sat) at the end.
    pub emit_check_sat: bool,
    /// Use :named annotations for unsat core extraction.
    pub named_assertions: bool,
    /// Monomorphize parametric sorts for solvers without par support.
    pub monomorphize: bool,
    /// Domain filter: only emit sorts/rules from these namespaces (empty = all).
    pub domains: Vec<String>,
}
```

### 7.4 Output Modes

1. **Theory mode** (default) — declarations and axioms only; user appends queries
2. **Consistency check** — append `(check-sat)` to verify axiom set is satisfiable
3. **Property verification** — negate a named rule and check for counterexamples
4. **Contract verification** — generate VCs for operation contracts

### 7.5 Term Translation

Walking KB terms (`kb.get_term(id)`) to SMT-LIB s-expressions:

| `Term` variant | SMT-LIB output |
|---|---|
| `Const(Int(n))` | `n` |
| `Const(Bool(b))` | `true` / `false` |
| `Const(String(s))` | `"s"` |
| `Const(Float(f))` | rational literal or `(/ p q)` |
| `Const(BigInt(n))` | `n` |
| `Var(v)` | bound variable name (from quantifier scope) |
| `Fn { functor, pos_args, named_args }` | `(functor arg1 ... argN)` — positional first, then named by field order |
| `Ref(sym)` | symbol name (sort or constant reference) |
| `Bottom` | `false` (in rule head position) |

Builtin functors (`add`, `eq`, `gt`, ...) are intercepted and mapped to SMT-LIB built-ins (section 3.3).

### 7.6 Names in a Document

A document names variables, constants and functions, and the solver takes a name for one thing. Two things given one name are one: a constant that proves what the source does not say (`A(cap: ?a), B(cap: ?b)` read as one `cap`, WI-20261014-VVRHJ), two variables related as one (an inlined rule's own variable read as the proof's of the same index, WI-20261012-BR7P3), or one name declared twice (two structured steps' new variables, WI-20261014-S1VNF). So every name follows one policy (decided with the user, 2026-10-14):

1. **Made in one place per document, from what it denotes.** The worlds of a disjunction (§4.5) and the lifts spliced into the document are of the document. No name is made from a short name, and none from an index read in another frame.
2. **Three kinds, spelled apart.**
   - **A variable** is `var_<n>`, from one count for the document. The variables of the proof's clause are `var_0` … `var_<k-1>`, by their index in its frame, so a document of one clause is the one it always was. Every other variable continues the count: an inlined rule's own (done, BR7P3), and a structured step's new variable in its lift (S1VNF). A quantifier's variables (a lemma's lift) are bound by it, and are spelled as the document's.
   - **What the knowledge base declares** — an operation, a relation, a sort, an entity's field read as a constant — is its qualified name, written by `smt_symbol` (simple where the standard admits it, quoted otherwise): `ns.related/2`, `anthill.prelude.PartialOrd.lt@ns.Scope.T`, and a field the entity's qualified name with the field, `test.ent.A.cap` (VVRHJ; a field is its short name `cap` until then). A qualified name always holds a `.`. `sanitize_smt_id`, which folds distinct names into one (`a.b` and `a_b` are both `a_b`), goes with it.
   - **What the emitter defines for itself** (`anthill_abs`, `anthill_cos`, `anthill_sin`) holds no `.` and does not begin `var_`.
3. **A name is its identity.** Whether a variable is already written in the document (`Emitter::bind_variable`) is asked of the document's text, token by token. That is exact because of 1 and 2, and only because of them: a token names one thing.
4. **A change to these rules moves only the documents that held a collision.** Every other document, with its cache key and its witness's hash, is the one it was, to the byte; the change lists those that moved.

scaland's emitter follows the same rules for what it reads.

## 8. Example: Complete Translation

### KB State (after loading)

```
SortInfo(name: Color, constructors: [red, green, blue], parameters: [], ...)
EntityInfo(name: red, fields: [])
EntityInfo(name: green, fields: [])
EntityInfo(name: blue, fields: [])
OperationInfo(name: eq, params: [(a: Color), (b: Color)], return_type: Bool, ...)
Rule: eq(red, red) = true
Rule: eq(green, green) = true
Rule: eq(blue, blue) = true
Rule: eq(?_, ?_) = false
Rule: neq(?a, ?b) = not(eq(?a, ?b))
```

### Generated SMT-LIB

```smt2
(set-logic ALL)
(set-option :produce-models true)
(set-option :produce-unsat-cores true)

; ─── Datatypes ─────────────────────────────────────
(declare-datatypes ((Color 0))
  (((red) (green) (blue))))

; ─── Functions ─────────────────────────────────────
(declare-fun eq-Color (Color Color) Bool)
(declare-fun neq-Color (Color Color) Bool)

; ─── Axioms ────────────────────────────────────────
(assert (! (= (eq-Color red red) true)     :named eq_red_red))
(assert (! (= (eq-Color green green) true) :named eq_green_green))
(assert (! (= (eq-Color blue blue) true)   :named eq_blue_blue))

(assert (! (forall ((a Color) (b Color))
  (=> (not (or (and (is-red a) (is-red b))
               (and (is-green a) (is-green b))
               (and (is-blue a) (is-blue b))))
      (= (eq-Color a b) false)))
  :named eq_default))

(assert (! (forall ((a Color) (b Color))
  (= (neq-Color a b) (not (eq-Color a b))))
  :named neq_derived))

; ─── Check ─────────────────────────────────────────
(check-sat)  ; expected: sat (axioms are consistent)
```

## 9. Integration with Trust Levels

When the solver returns `unsat` for a negated property, the fact's trust can be elevated to `verified`:

```
; Before: fact Eq[T = Color] @[trust: proposed]
; After:  fact Eq[T = Color] @[trust: verified, solver: "z3"]
```

This produces a `ProofResult.Proved` fact:

```
fact ProofResult.Proved(witness: "z3-unsat-proof", solver: "z3 4.13", duration: 50ms)
```

## 10. Scope and Limitations

### What maps well

- ADTs (sorts with entity constructors) — direct correspondence
- Equational laws — natural as universally quantified equalities
- Ground facts — trivial
- Arithmetic on primitives — built-in SMT-LIB theories
- Simple contracts (pre/post over primitives and ADTs)
- Constructor-based pattern matching

### What requires design decisions

| Anthill feature | Challenge | Approach |
|---|---|---|
| Effects (`Modify`, `Error`) | No SMT-LIB equivalent | Ignore for pure verification; model via state-passing for stateful VCs |
| Recursive rules | SMT solvers may diverge | `define-fun-rec` with termination hints; bounded unrolling fallback |
| Higher-order (arrow types) | SMT-LIB is first-order | Defunctionalize or use CVC5 HO logic |
| `Quoted` terms | Opaque host code | Skip (emit comment) |
| Description blocks | Not logical content | Skip |
| Metadata | Provenance, not logic | Skip (but use rule labels as `:named` annotations) |

### Solver compatibility

| Feature | Z3 | CVC5 |
|---|---|---|
| Algebraic datatypes | Yes | Yes |
| Parametric datatypes | Yes | Yes |
| `define-fun-rec` | Yes | Yes |
| Quantifiers | Yes | Yes |
| Unsat cores (`:named`) | Yes | Yes |
| Parametric `define-fun` | No | Yes |
| Higher-order | Limited | `--uf-ho` |

Default target: common subset. Solver-specific features enabled via config.

## 11. Future Directions

- **Incremental verification** — emit only changed axioms when KB is updated
- **Effect modeling** — state-passing encoding for `Modify` effects
- **Isabelle/Lean export** — higher-order proof assistant output for properties beyond first-order
- **Bounded model checking** — unroll recursive definitions to finite depth
- **Counterexample-guided refinement** — `get-model` results → concrete test cases → `tested(N)` trust
