# Proposal 025: Proof Constructs

## Motivation

The kernel generates proof obligations from operation contracts (`requires`/`ensures`) and from `constraint` declarations. Currently, discharging these obligations is untyped — any agent can assert a `ProofResult` fact without the kernel verifying the proof structure. When definitions change, there is no mechanism to detect which proofs are invalidated.

We need:
1. A syntax construct that connects a proof to its rule
2. Kernel-verifiable and externally-delegated proof representations
3. Automatic dependency tracking with staleness propagation

## Design

### `proof` as a companion to `rule`

A `proof` is not a standalone proposition — it attaches to an existing `rule`. The rule states what is claimed; the proof provides evidence.

```anthill
sort Ordered
  requires Eq[T]

  rule lt(?a, ?b) :- eq(sign(compare(?a, ?b)), neg-one)

  proof lt
    by derivation
  end
end
```

A rule without a proof has `trust: proposed`. A rule with a verified proof gets elevated to the appropriate trust level (`proved`, `verified`, `tested`).

### Proof strategies

The `by` clause specifies how the proof is produced:

| Strategy | Meaning | Trust level |
|----------|---------|-------------|
| `by derivation` | Kernel searches for proof via SLD resolution | `proved` |
| `by <tool>` | External tool produces certificate | `verified` |
| `by test(runs: N)` | Test runner provides evidence | `tested(N)` |
| *(omitted)* | Obligation — waiting for agent to discharge | `proposed` |

### Automatic vs guided proofs

A proof can be **automatic** (kernel finds it) or **guided** (author provides steps).

**Automatic** — no body, kernel does full search:

```anthill
proof list_length_nil
  by derivation
end
```

**Guided** — body provides proof steps that narrow the search:

```anthill
proof append_assoc
  by derivation
  :- induction(?xs),
     case nil :- reflexivity,
     case cons(head: ?x, tail: ?rest) :- 
       apply(append_assoc, ?rest), reflexivity
end
```

The body is a sequence of **tactics** — directives that guide the kernel's search. Without a body, the kernel explores all resolution paths. With a body, it follows the given strategy and verifies each step.

**Tactics** reuse the rule body syntax (goals separated by `,`) with additional proof-specific forms:

| Tactic | Meaning |
|--------|---------|
| `induction(?var)` | Structural induction on a variable |
| `case <pattern> :- <goals>` | Prove a specific case |
| `apply(<rule>, <args>)` | Apply a named rule |
| `reflexivity` | Goal is `eq(?x, ?x)` |
| `symmetry` | Swap sides of an equality |
| `unfold(<operation>)` | Replace operation call with its body |
| `rewrite(<rule>)` | Rewrite using an equality rule |
| `by_assumption` | Goal matches an assumption in scope |

Tactics are themselves terms in the KB — extensible by defining new tactic rules.

**External** — delegated to a tool. The body specifies the query in the tool's language and any parameters:

```anthill
proof add_comm
  by z3
  query "(assert (forall ((a Int) (b Int)) (= (+ a b) (+ b a))))"
  mapping {
    add -> +,
    eq -> =,
    Int -> Int
  }
end
```

The `query` clause is the proposition in the tool's input language. The `mapping` clause connects anthill symbols to tool symbols — this is the bridge between anthill's KB and the external world.

For tools with standard translations, the mapping can be inferred:

```anthill
proof sort_correct
  by z3(timeout: 5000, logic: "LIA")
end
```

Here the kernel auto-translates the rule's proposition to SMT-LIB using the standard Int/Bool/arithmetic mapping.

**Test evidence**:

```anthill
proof sort_preserves_length
  by test(runs: 1000)
end
```

**Open obligation** — no proof yet, waiting for discharge:

```anthill
proof double_ensures
end
```

### Dependency inference

Dependencies are **computed**, not declared. The kernel infers them from:

1. **Proof body**: which rules were used during verification (for `by derivation`)
2. **Requires chain**: rules available from required sorts are implicit dependencies
3. **External certificates**: the tool reports which axioms it used

The dependency set is stored as metadata on the proof fact and is queryable:

```anthill
-- Query: what does this proof depend on?
?- proof_depends_on(lt, ?dep)
-- Returns: compare, Eq.eq, sign, ...
```

### Staleness propagation

When a definition changes (sort, operation, rule body):

1. Find all proofs whose dependency set includes the changed definition
2. Mark those proofs as `trust: stale`
3. Transitively: if proof A depends on proof B and B becomes stale, A becomes stale

This reuses the existing `trust` metadata — no new mechanism needed.

### Interaction with `requires`

`requires Eq[T]` has two roles:

- **Type level**: the sort is a subtype of Eq (subtyping, obligation checking)
- **Proof level**: Eq's rules are available as assumptions within proofs of this sort

The requires chain (`requires_chain` in Rust) already computes transitive dependencies. The same traversal determines what rules are available for proof construction and what changes would invalidate proofs.

### Auto-generated induction rules

Every sort/enum with constructors automatically gets an induction principle — a rule generated by the kernel from the type definition. This rule lives in the sort's scope alongside entities, operations, and user-written rules.

**Finite enum (case analysis):**
```anthill
enum Color
  entity red
  entity blue
  entity green
end

-- Auto-generated:
rule Color.cases(?P) :- ?P(red), ?P(blue), ?P(green)
```

**Recursive enum (structural induction):**
```anthill
enum List
  sort T = ?
  entity nil
  entity cons(head: T, tail: List[T])
end

-- Auto-generated:
rule List.induction(?P)
  :- ?P(nil),
     (forall(?h, ?rest), ?P(cons(head: ?h, tail: ?rest)) :- ?P(?rest))
```

**Multi-recursive enum (multiple induction hypotheses):**
```anthill
enum Tree
  sort T = ?
  entity leaf(value: T)
  entity branch(left: Tree[T], right: Tree[T])
end

-- Auto-generated:
rule Tree.induction(?P)
  :- (forall(?v), ?P(leaf(value: ?v))),
     (forall(?l, ?r), ?P(branch(left: ?l, right: ?r)) :- ?P(?l), ?P(?r))
```

**Bounded numeric (Int):**
```anthill
-- Int has bounded well-founded induction:
rule Int.induction(?P, ?lo, ?hi)
  :- ?P(?lo),
     (forall(?n), gte(?n, ?lo), lt(?n, ?hi), ?P(add(?n, 1)) :- ?P(?n))
```

**Unbounded numeric (BigInt):**
```anthill
-- BigInt has strong induction:
rule BigInt.induction(?P)
  :- ?P(0),
     (forall(?n), ?P(?n) :- gt(?n, 0), ?P(sub(?n, 1)))
```

The generation rules:
1. For each entity constructor, generate one case
2. Fields of the entity's own sort type (recursive positions) contribute induction hypotheses
3. Non-recursive fields are universally quantified
4. Entities with no recursive fields are base cases

Sorts with three kinds of members:
- **entities** — data constructors (closed for enums, open for sorts)
- **operations** — behavioral specifications
- **rules** — laws, derived facts, and auto-generated induction principles

The induction rule is available to any proof in the sort's scope, and to any sort that `requires` this sort (via the requires chain).

**Note on higher-order features:** The induction rules use predicate variables (`?P`) and nested implication (`:-` within `forall` goals). This extends anthill beyond first-order Horn clauses into the **hereditary Harrop formula** fragment (the same fragment λProlog uses). The variable `?P` ranges over predicates — anthill already has this implicitly (variables in type positions range over types, which are terms). Making predicate variables explicit in rules is a natural extension.

**Resolvability:** Higher-order unification is generally undecidable, but the **pattern fragment** (Miller, 1991) — where predicate variables are applied to distinct first-order terms — is decidable. The induction rules above are in this fragment. The kernel checks the restriction at load time:

- Predicate variables (variables in functor position) may only appear in **body** position, not rule heads
- Arguments to predicate variables must be first-order (no nested predicate variables)
- `?P(nil)`, `?P(cons(?h, ?rest))` — OK (applied to first-order terms)
- `?P(?Q)` — rejected (predicate applied to predicate)

**Resolution for nested goals:**
- `forall(?x, G)` → create fresh variable for `?x`, prove `G`
- `conclusion :- premise` (nested `:-`) → add `premise` as temporary assumption, prove `conclusion`

The `:-` operator serves double duty: at top level it separates rule head from body; inside `forall` goals it expresses implication. Same semantics — "the left holds if the right holds."

### Proof for operation contracts

Operation contracts generate implicit rules. A `proof` can target them:

```anthill
sort Stack
  operation push(s: Stack, x: T) -> Stack
    ensures eq(top(result), x)

  operation pop(s: Stack) -> Stack
    requires not(empty(s))

  -- Proof targets the ensures contract of push
  proof push.ensures
    by derivation
  end
end
```

The naming convention `<operation>.<clause>` identifies which contract clause is being proved.

## Internal proof theory

### What we can prove

Anthill's kernel has three reasoning mechanisms:

1. **SLD resolution** — backward chaining over Horn clauses. Can prove any goal that follows from the rules in the KB.
2. **Equational reasoning** — operations with expression bodies define equalities (`operation double(x: Int) -> Int = add(x, x)` means `double(x) = add(x, x)`). Rewriting by these equalities.
3. **Structural induction** — for enums with recursive entities (List, Tree), prove a property holds for all values by proving it for each entity constructor, assuming it holds for recursive sub-terms.

These cover the common proof patterns for algebraic specifications:
- Laws like `eq(add(a, b), add(b, a))` — equational reasoning
- Properties like `eq(length(append(xs, ys)), add(length(xs), length(ys)))` — induction + rewriting
- Derived rules like `lt(?a, ?b) :- ...` — SLD resolution

What we **cannot** prove internally:
- Properties requiring arithmetic decision procedures (delegated to Z3/SMT)
- Properties about infinite structures (requires coinduction — future work)
- Properties requiring higher-order reasoning

### Proof context

A proof operates in a **context** — the set of available assumptions. The context consists of:

1. **Axioms**: rules in the current sort's scope
2. **Inherited rules**: rules from required sorts (via `requires` chain)
3. **Definitions**: operation bodies as equalities
4. **Induction hypotheses**: when proving by induction, the property applied to structurally smaller terms

The context is computed by the kernel, not declared by the author. It is determined by the sort scope and the proof method.

### Proof tree

A proof is a **tree** where:
- The root is the **goal** — the proposition to prove
- Each internal node is a **proof step** — applying a rule, rewriting, or case split
- Leaves are **closed** — the goal matches an axiom, a definition, or an induction hypothesis

```
ProofTree = 
  | Axiom(rule: Symbol, subst: Substitution)         -- goal matches a rule directly
  | Resolution(rule: Symbol, subst: Substitution,     -- apply rule, prove subgoals
               subproofs: List[ProofTree])
  | Rewrite(equation: Symbol, direction: Direction,    -- rewrite goal using equation
            subproof: ProofTree)
  | Induction(variable: Symbol, enum: Symbol,          -- structural induction
              cases: List[InductionCase])
  | Assumption(index: Int)                             -- reference to assumption in scope

InductionCase =
  | Case(entity: Symbol,                               -- constructor pattern
         ih: List[Symbol],                             -- induction hypothesis names
         subproof: ProofTree)

Direction = LeftToRight | RightToLeft
```

### Proof steps in detail

**Axiom**: the goal unifies with a rule head that has no body (a fact). Proof is complete.
```
Goal: eq(length(nil), 0)
Step: Axiom(rule: length_nil, subst: {})
-- because: rule length(nil) = 0
```

**Resolution**: the goal unifies with a rule head. Prove each body goal.
```
Goal: lt(1, 2)
Step: Resolution(rule: lt_def, subst: {?a → 1, ?b → 2},
        subproofs: [proof of eq(sign(compare(1, 2)), neg-one)])
-- because: rule lt(?a, ?b) :- eq(sign(compare(?a, ?b)), neg-one)
```

**Rewrite**: replace a subterm using an equation (operation definition or proved equality).
```
Goal: eq(double(3), 6)
Step: Rewrite(equation: double_def, direction: LeftToRight,
        subproof: proof of eq(add(3, 3), 6))
-- because: operation double(x) = add(x, x), so double(3) → add(3, 3)
```

**Induction**: for a goal `forall xs: List[T], P(xs)`, split into cases by constructor.
```
Goal: eq(length(append(?xs, ?ys)), add(length(?xs), length(?ys)))
Step: Induction(variable: ?xs, enum: List,
        cases: [
          Case(entity: nil, ih: [],
            subproof: proof of eq(length(append(nil, ?ys)), add(length(nil), length(?ys)))),
          Case(entity: cons, ih: [ih_rest],
            subproof: proof of eq(length(append(cons(?h, ?rest), ?ys)),
                                  add(length(cons(?h, ?rest)), length(?ys)))
            -- where ih_rest: eq(length(append(?rest, ?ys)), add(length(?rest), length(?ys))))
        ])
```

**Assumption**: reference an assumption by index in the current proof scope. Used for induction hypotheses and local assumptions introduced by case analysis.

### Verification

The kernel **verifies** a proof tree by checking each node:

1. **Axiom**: verify the rule exists, head unifies with goal under the given substitution
2. **Resolution**: verify rule exists, head unifies, each subproof proves the corresponding body goal
3. **Rewrite**: verify the equation holds (operation definition or proved rule), the rewritten goal is correct, subproof proves the rewritten goal
4. **Induction**: verify the variable has an enum type, cases cover all entities (exhaustiveness), each case's subproof is valid with the induction hypothesis added to context
5. **Assumption**: verify the index refers to a valid assumption in the current scope

Verification is **linear** in proof tree size — each node is checked independently against its children.

### Guided proof syntax

The author can provide a proof tree explicitly using a body:

```anthill
proof append_assoc
  by derivation
  :- induction(?xs, List,
       case nil :- rewrite(append_nil, reflexivity),
       case cons(?h, ?rest) :-
         rewrite(append_cons,
           rewrite(append_assoc.ih,
             reflexivity)))
end
```

The body mirrors the proof tree structure using term syntax:
- `induction(?var, enum, case ..., case ...)` — structural induction
- `case <pattern> :- <proof>` — case in induction
- `rewrite(<equation>, <subproof>)` — equational rewriting
- `apply(<rule>, <subproof1>, ...)` — resolution step
- `reflexivity` — prove `eq(?x, ?x)`
- `assumption` or `<rule>.ih` — reference an assumption

Without a body, the kernel searches for a proof tree automatically.

### Automatic proof search

When no body is given (`by derivation` with no `:-`), the kernel searches for a proof tree:

1. Try direct resolution (depth-bounded SLD search)
2. Try rewriting with available equations
3. If the goal is universally quantified over an enum, try induction

The search is bounded by depth and time limits (configurable). If search fails, the proof remains an open obligation (`trust: proposed`).

### Proof representation in the KB

A verified proof tree is stored as a term:

```anthill
enum ProofTree
  entity axiom_step(rule: Symbol, subst: Term)
  entity resolution_step(rule: Symbol, subst: Term, subproofs: List[ProofTree])
  entity rewrite_step(equation: Symbol, direction: Symbol, subproof: ProofTree)
  entity induction_step(variable: Symbol, enum_sort: Symbol, cases: List[InductionCase])
  entity assumption_step(index: Int)
end

enum InductionCase
  entity proof_case(entity: Symbol, ih_names: List[Symbol], subproof: ProofTree)
end
```

This is a regular anthill enum — proof trees are terms in the KB, hash-consed and queryable.

### External: tool certificate

For `by <tool>`, the proof is an opaque certificate:

```
ExternalProof(
  tool: String,
  certificate: Term,     -- tool-specific proof artifact
  axioms_used: List[Symbol]  -- reported by the tool
)
```

The kernel cannot verify the certificate independently — it trusts the tool at `verified` level. The `axioms_used` field enables dependency tracking.

### Test evidence

For `by test(runs: N)`, the proof is test metadata:

```
TestEvidence(
  runner: String,
  runs: Int,
  failures: Int,
  seed: Option[Int]
)
```

Trust level is `tested(N)`.

## KB representation

A verified proof is stored as a fact:

```anthill
-- Emitted by the kernel after proof verification
fact ProofRecord(
  rule: Symbol,
  strategy: ProofStrategy,
  result: ProofResult,
  dependencies: List[Symbol],
  timestamp: String
) [trust: proved]
```

This integrates with the existing `ProofResult` enum (`Proved`, `Disproved`, `Timeout`, `Unknown`) and the `Trust` sort.

## Grammar

```
proof_declaration ::= 'proof' name
                      ['by' proof_strategy]
                      [proof_body]
                      'end'

proof_strategy ::= 'derivation'
                 | name ['(' field_list ')']    -- tool name with params
                 | 'test' '(' field_list ')'

proof_body ::= ':-' proof_term                 -- guided derivation (proof tree as term)
             | 'query' string_literal          -- external tool query
               ['mapping' '{' mapping_list '}']

proof_term ::= term                            -- proof steps expressed as terms
                                               -- (induction, rewrite, apply, etc.)

mapping_list ::= mapping_entry (',' mapping_entry)*
mapping_entry ::= name '->' name              -- anthill symbol -> tool symbol
```

`proof` is valid inside sort/enum bodies and at namespace level.

## Interaction with enum

Enums can have rules and proofs:

```anthill
enum List
  sort T = ?
  entity cons(head: T, tail: List[T])
  entity nil

  rule length(nil) = 0
  rule length(cons(head: ?, tail: ?t)) = add(1, length(?t))

  proof length
    by derivation
  end
end
```

## Summary

- `proof` attaches to a `rule`, providing evidence
- Three strategies: `derivation` (kernel), tool name (external), `test` (testing)
- Dependencies are inferred, not declared
- Staleness propagates through dependency graph
- Internal proofs (SLD traces) are kernel-verifiable
- External proofs are trusted at `verified` level
- Integrates with existing `Trust`, `ProofResult`, metadata system
