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
| Primitive `Int` | `Int` |
| Primitive `Bool` | `Bool` |
| Primitive `String` | `String` |
| Primitive `Float` | `Real` (or `(_ FloatingPoint 11 53)` with FP theory) |
| Primitive `BigInt` | `Int` (SMT-LIB Int is arbitrary-precision) |
| Sort with entities (ADT) | `declare-datatypes` |
| Parametric sort with entities | `declare-datatypes` with `par` |
| Abstract sort (`sort T = ?`) | sort parameter in `par`, or `declare-sort` at top level |
| Type alias (`sort Money = Int`) | inline substitution (no separate declaration) |
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
; Int    → Int (arbitrary-precision)
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
    amount: Int,                            (Duration-amount Int)
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
operation length(l: List) -> Int
rule length(nil) = 0
rule length(cons(?x, ?xs)) = add(1, length(?xs))

→ (define-fun-rec length ((l (List T))) Int
    (match l
      ((nil 0)
       ((cons x xs) (+ 1 (length xs))))))
```

**Strategy selection:** If rules form a complete, non-overlapping constructor-case definition → `define-fun-rec` with `match`. Otherwise → `declare-fun` + `assert` per rule.

### 3.3 Arithmetic and Comparison Builtins

Prelude operations on primitives map to SMT-LIB built-ins:

| Anthill | SMT-LIB |
|---|---|
| `add(a, b)` | `(+ a b)` |
| `sub(a, b)` | `(- a b)` |
| `mul(a, b)` | `(* a b)` |
| `div(a, b)` | `(div a b)` / `(/ a b)` |
| `mod(a, b)` | `(mod a b)` |
| `neg(a)` | `(- a)` |
| `eq(a, b)` | `(= a b)` |
| `neq(a, b)` | `(not (= a b))` |
| `gt(a, b)` | `(> a b)` |
| `lt(a, b)` | `(< a b)` |
| `gte(a, b)` | `(>= a b)` |
| `lte(a, b)` | `(<= a b)` |
| `not(a)` | `(not a)` |
| `and(a, b)` | `(and a b)` |
| `or(a, b)` | `(or a b)` |
| `ite(c, t, e)` | `(ite c t e)` |

These apply when arguments are primitive types. For user-defined sorts, operations remain as uninterpreted functions with their axioms.

## 4. Rules and Laws

### 4.1 Equational Rules → Universal Assertions

```
rule add_comm: add(?a, ?b) = add(?b, ?a)

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

## 5. Spec Satisfaction and Requires

### 5.1 Requires as Axiom Import

`SortRequiresInfo` facts link a sort to its required specs. The required spec's laws are emitted as axioms:

```
sort Ordered {
  sort T = ?
  requires Eq[T]    ; imports Eq laws for T
}

→ (assert (forall ((a T) (b T))
    (= (neq a b) (not (eq a b)))))
```

### 5.2 Fact-Based Spec Satisfaction

When a fact declares that a concrete type satisfies a spec, laws are instantiated:

```
fact Eq[T = Color]
rule eq(red, red) = true

→ (assert (= (eq-Color red red) true))
```

## 6. Constraints and Contracts

### 6.1 Constraints → Satisfiability Assertions

```
constraint non_negative: gte(balance(?a), zero-val) :- balance(?a, ?b)

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
  requires gt(m, zero-val)
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
; Before: fact Eq[T = Color] [trust: proposed]
; After:  fact Eq[T = Color] [trust: verified, solver: "z3"]
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
