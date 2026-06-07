# Proposal 023: KB Guards — Constraint Checking on Assert

## Summary

Add a guard mechanism to the KB: constraints checked on every `assert`.
Constraints use quantified formulas with Alloy-inspired syntax (`forall`,
`some`, `one`, `lone`, `no`) and aggregation expressions (`count`, `sum`).
The guarded implication operator `-:` (reverse of `:-`) reads left-to-right.

## Motivation

The typing pass asserts `TypeOf(occ, type)` facts into the KB. Without guards,
nothing prevents contradictory facts (same occurrence, different types).
More generally, any domain may need integrity constraints on its facts.

## Constraint syntax

### Guarded implication: `-:`

Anthill uses `:-` for "if" (right-to-left implication):
```anthill
rule Q :- P              -- Q if P
```

The reverse operator `-:` means "then" (left-to-right):
```anthill
constraint: P -: Q       -- P then Q  (if P then Q)
```

Both express `P → Q`, just in different directions. `-:` reads naturally
in constraints where condition comes first.

### Quantifiers (Alloy-inspired)

All quantifiers share the same form:

```
quantifier ?var: condition -: body
```

Where `condition` selects the domain, `body` is what's asserted,
and the quantifier says how many elements must satisfy the body.

| Quantifier | Meaning | Equivalent |
|---|---|---|
| `forall ?x: P -: Q` | all x in P satisfy Q | `no ?x: P -: not(Q)` |
| `some ?x: P -: Q` | at least one x in P satisfies Q | `count >= 1` |
| `one ?x: P -: Q` | exactly one x in P satisfies Q | `count = 1` |
| `lone ?x: P -: Q` | at most one x in P satisfies Q | `count <= 1` |
| `no ?x: P -: Q` | no x in P satisfies Q | denial |

Examples:
```anthill
-- Every typed occurrence has a ground type
constraint grounded:
  forall ?o: TypeOf(occ: ?o, type: ?t) -: is_ground(?t)

-- Each occurrence has at most one type (uniqueness)
constraint unique_type:
  lone ?t: TypeOf(occ: ?o, type: ?t) -: true

-- No open work item is overdue
constraint no_overdue:
  no ?x: WorkItem(id: ?x, status: Open) -: overdue(?x)

-- Every claimed item has feedback
constraint feedback_required:
  forall ?w: WorkItem(id: ?w, status: Claimed) -: some ?f: Feedback(workitem: ?w) -: true
```

### Aggregation expressions

Aggregation reduces a query to a value, usable in comparison constraints:

```anthill
count(?var: condition -: body)
sum(?var: condition -: body)
min(?var: condition -: body)
max(?var: condition -: body)
```

Quantifiers are sugar over `count`:
```
some ?x: P -: Q    ≡  count(?x: P -: Q) >= 1
one  ?x: P -: Q    ≡  count(?x: P -: Q) = 1
lone ?x: P -: Q    ≡  count(?x: P -: Q) <= 1
no   ?x: P -: Q    ≡  count(?x: P -: Q) = 0
```

Examples:
```anthill
constraint max_open:
  count(?x: WorkItem(id: ?x, status: Open) -: true) <= 50

constraint budget:
  sum(?c: WorkItem(cost: ?c) -: true) <= 1000
```

## API

Two operations on KB:

```anthill
operation assert(kb: KB, term: Term, sort: Type) -> Option[T = FactId]
  effects Modifies[kb]

operation add_guard(kb: KB, guard: LogicalQuery) -> ConstraintId
  effects Modifies[kb]
```

- `add_guard` registers a guard that must always hold.
- `assert` checks all guards relevant to the asserted sort.
  Returns `none` if any guard is violated.

### LogicalQuery extensions

Add quantifier and aggregation nodes to `LogicalQuery`:

```anthill
sort LogicalQuery {
  -- existing
  entity empty_query
  entity pattern_query(term: Term)
  entity sort_query(sort_name: String)
  entity conjunction(left: LogicalQuery, right: LogicalQuery)
  entity disjunction(left: LogicalQuery, right: LogicalQuery)
  entity negation(query: LogicalQuery)
  entity guarded(query: LogicalQuery, condition: Term)
  entity projected(query: LogicalQuery, vars: List[T = String])
  entity limited(query: LogicalQuery, count: Int64)

  -- new: quantifiers (condition -: body form)
  entity forall_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
  entity some_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
  entity one_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
  entity lone_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
  entity no_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)

  -- new: aggregation
  entity count_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
  entity sum_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
  entity min_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
  entity max_q(var: Symbol, condition: LogicalQuery, body: LogicalQuery)
}
```

## Checking on assert — general semantics

When `assert(kb, fact, sort)` is called:

1. **Insert** the fact into the KB (tentatively).
2. **Check** all guards registered for `sort` against the KB
   (which now includes the new fact).
3. If any guard fails → **retract** the fact, return `none`.
4. If all guards pass → keep the fact, return `some(fact_id)`.

This is a mini-transaction: insert, validate, commit or rollback.

## Fast-path optimization

Not all guards require the full insert-check-retract cycle.
The KB analyzes guards and recognizes patterns that can be checked
**before** inserting (no rollback needed):

| Guard pattern | Recognized as | Pre-check |
|---|---|---|
| `one ?v: S(k: ?x, v: ?v) -: true` | Functional dep (k → v) | Query discrim tree for same key |
| `lone ?v: S(k: ?x, v: ?v) -: true` | Optional unique | Query discrim tree for same key |
| `no ?x: P -: Q` with single atom P | Simple denial | Query discrim tree for P |

These pre-checkable guards are an **optimization** — the general
semantics (insert, check, retract) is always correct. The fast path
avoids the insert/retract overhead for common constraint shapes.

Guards that cannot be pre-checked (e.g., aggregate constraints like
`count < 10` or `sum < 1000`) use the general path: insert first,
evaluate, retract on failure.

All checks use the existing `SubstTree` (discrimination tree). No new
index structures needed.

## Rust implementation sketch

```rust
/// A registered guard on the KB.
struct Guard {
    id: ConstraintId,
    query: LogicalQuery,      // the original guard
    kind: GuardKind,          // recognized optimization
}

enum GuardKind {
    /// Functional dependency: key field → value field in a sort.
    /// Pre-check via discrimination tree query.
    FunctionalDep {
        sort: Symbol,
        key_field: Symbol,
    },
    /// Cardinality bound: count of matching facts <= N.
    /// Pre-check: count existing matches, reject if already at limit.
    CardinalityBound {
        sort: Symbol,
        max_count: usize,
    },
    /// General guard: insert, evaluate, retract on failure.
    General(LogicalQuery),
}
```

In `KnowledgeBase`:
```rust
struct KnowledgeBase {
    // ... existing fields ...
    guards: Vec<Guard>,
    guards_by_sort: HashMap<Symbol, Vec<usize>>,  // sort → guard indices
}

impl KnowledgeBase {
    fn add_guard(&mut self, query: LogicalQuery) -> ConstraintId {
        let kind = self.analyze_guard(&query);
        let id = ConstraintId(self.guards.len());
        for sort in self.extract_sorts(&query) {
            self.guards_by_sort.entry(sort).or_default().push(id.0);
        }
        self.guards.push(Guard { id, query, kind });
        id
    }

    fn assert_checked(&mut self, term: TermId, sort: Symbol) -> Option<FactId> {
        let guard_indices: Vec<usize> = self.guards_by_sort
            .get(&sort).cloned().unwrap_or_default();

        // Fast path: pre-checkable guards (before insert)
        for &idx in &guard_indices {
            match &self.guards[idx].kind {
                GuardKind::FunctionalDep { key_field, .. } => {
                    // Extract key value from new term
                    // Query discrim tree for existing fact with same key
                    // If found with different value → return None
                }
                GuardKind::CardinalityBound { max_count, .. } => {
                    // Count existing facts of this sort
                    // If count >= max_count → return None
                }
                GuardKind::General(_) => {} // handled below
            }
        }

        // General path: insert, check, retract on failure
        let fact_id = self.assert_fact(term, sort, None);

        for &idx in &guard_indices {
            if let GuardKind::General(query) = &self.guards[idx].kind {
                if !self.evaluate_guard(query) {
                    self.retract_fact(fact_id);
                    return None;
                }
            }
        }

        Some(fact_id)
    }
}
```

## Constraint syntax integration

The `constraint` keyword in anthill source already exists in the grammar.
Extend it with quantifier and aggregation syntax:

```
constraint_declaration ::=
  'constraint' [label ':']
  constraint_body
  [meta_block]

constraint_body ::=
  quantified_constraint
  | aggregation_constraint
  | term_constraint

quantified_constraint ::=
  quantifier variable ':' rule_body '-:' constraint_body

quantifier ::= 'forall' | 'some' | 'one' | 'lone' | 'no'

aggregation_constraint ::=
  aggregate '(' variable ':' rule_body '-:' rule_body ')' comparison_op term

aggregate ::= 'count' | 'sum' | 'min' | 'max'

term_constraint ::=
  rule_body ['-:' rule_body]        -- simple guard
  | rule_body ':-' rule_body        -- existing syntax (invariant :- guard)
```

The loader converts constraint declarations to `LogicalQuery` terms
and calls `add_guard` during `load_all`.

Runtime code can also call `add_guard` dynamically (e.g., `init_typing`
in the typing pass registers uniqueness before type checking begins).

## Interaction with existing systems

- **Discrimination tree**: used as-is for guard checking. No structural changes.
- **`assert_fact`**: existing internal method. The new `assert` wraps it
  with guard checks. Existing code calling `assert_fact` directly bypasses
  guards (useful for loading, where constraints are checked in batch after).
- **`constraint` syntax**: already in the grammar, extended with quantifiers.
- **`LogicalQuery`**: extended with quantifier and aggregation nodes.

## Comparison with other systems

Inspired by Alloy's quantifier design:

| Alloy | Anthill | Meaning |
|---|---|---|
| `all x: S \| P` | `forall ?x: S(?x) -: P(?x)` | universal |
| `some x: S \| P` | `some ?x: S(?x) -: P(?x)` | existential |
| `one x: S \| P` | `one ?x: S(?x) -: P(?x)` | unique existence |
| `lone x: S \| P` | `lone ?x: S(?x) -: P(?x)` | at most one |
| `no x: S \| P` | `no ?x: S(?x) -: P(?x)` | none |

Key differences from Alloy:
- Anthill operates on a KB (fact store), not a relational model
- Guards are checked incrementally on `assert`, not by bounded model checking
- The discrimination tree provides efficient indexed checking
- Aggregation (`count`, `sum`) extends beyond Alloy's quantifiers

## Open questions

- Should guard violations return an error message (which guard failed, why)?
  Current design returns `none`. Could return `Result[FactId, GuardViolation]`.
- Should guards be removable? (For temporary constraints in a pass.)
- Batch checking: for deferred general constraints, when to run them?
  After `load_all`? On explicit `check_constraints(kb)` call?
- Should field multiplicity annotations (`one`, `lone`) on entity declarations
  automatically register guards? E.g., `entity TypeOf(occ: ExprOccurrence one, type: Type)`
  would auto-register a `one` guard on `occ`.
