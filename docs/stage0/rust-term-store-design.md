# Term Store Design

## 1. Problem Statement

The term store is the central data structure of the anthill kernel. Terms appear everywhere — rule heads and bodies, operation contracts, entity fields, metadata, workitem criteria. The store must support two phases:

- **Parsing**: build terms from source text (bottom-up, no deletion)
- **Deduction**: create, match, substitute, and discard terms during reasoning

Deduction is the **primary use case**. The store must be designed for it, not retrofitted.

### 1.1 What Deduction Does with Terms

From kernel-language.md §8.2–8.4, the reasoning engine needs:

**Forward chaining (bottom-up):** New fact asserted → check all rules whose body might match → if body satisfied, derive head as new fact. This creates new terms (the derived head, with variables substituted).

**Backward chaining (top-down):** Query `?- goal` → find rules whose head unifies with goal → recursively prove body terms. This creates temporary substitutions that may be discarded if a branch fails.

**Constraint checking:** New fact → for each denial `⊥ :- B1, B2, ...`, check if body is satisfiable with existing facts + new fact. Creates temporary bindings.

**Unification:** `Var(?x)` unifies with any same-typed term. `Fn(f, [a1...an])` unifies with `Fn(f, [b1...bn])` if all args unify pairwise. Creates substitution mappings `?x → term`.

### 1.2 Operations on Terms

The store must efficiently support:

1. **Allocate** a new term (during parsing and during deduction)
2. **Read** a term by handle
3. **Subterm traversal** — given a term, enumerate its immediate subterms
4. **Substitution** — given a mapping `{?x → t1, ?y → t2}`, produce a new term with variables replaced
5. **Matching** — given a pattern term and a ground term, find if the pattern matches (one-way unification)
6. **Unification** — given two terms, find a most-general substitution that makes them equal
7. **Query** — given a sort or pattern, retrieve all matching facts from the KB (see §7)
8. **Discard** — reclaim memory for terms from failed search branches

## 2. Subterm Relation

A term `t` is a **subterm** of `s` if:
- `t = s` (reflexive), or
- `s = Fn(f, [..., t_i, ...])` and `t` is a subterm of some `t_i`

### 2.1 Why We Need It

- **Pattern matching in rules:** `rule length(cons(?x, ?xs)) = succ(length(?xs))` — the engine must match `cons(?x, ?xs)` against a concrete list term, descending into subterms.
- **Occurs check:** During unification of `?x` with term `t`, we must verify `?x` does not occur in `t` (prevents circular terms).
- **Substitution:** Replacing `?x` everywhere it appears as a subterm.
- **Indexing for forward chaining:** When a new fact `f(a, b)` is asserted, we need to efficiently find rules whose body mentions `f(_, _)`. This requires indexing terms by their top-level functor.

### 2.2 Representation

Child subterms are stored directly inside the `Term` enum (args of `Fn`). Every traversal algorithm (unification, substitution, occurs check, pattern matching) recurses into subterms naturally — the call stack maintains the parent chain. No separate parent index is needed.

For forward chaining, the relevant index is by **top-level functor** (§7), not by parent. When a fact `f(a, b)` is asserted, we look up rules mentioning `f` — that's a functor index, not a parent index.

## 3. Mutation Model: Immutable Facts with Supersession

The fundamental question: when a workitem's status changes from Open to Claimed, do we mutate the existing term or create a new one?

**Answer: create a new fact.** This is mandated by the spec — `meta.supersedes` links the new version to the old one (kernel-language.md §7), and "each revision produces a new WorkItem fact" (stage0-metasystem-design.md §5.1). The knowledge base is an **append-only log of facts** with retraction markers.

```
Time 1:  assert  WorkItem("WI-001", status: Open)           [meta: iteration 1]
Time 2:  retract WorkItem("WI-001", status: Open)
         assert  WorkItem("WI-001", status: Claimed(...))   [meta: iteration 2, supersedes: WI-001@1]
```

The old fact remains in the store (other terms or history may reference it) but is no longer active in the fact base.

### 3.1 Consequences for Term Store Design

**Terms are immutable.** Once allocated, a term's structure never changes. This enables:

- **Hash-consing.** Structurally identical terms share the same `TermId`. Allocation checks if an equal term already exists; if so, returns the existing id. This gives O(1) structural equality (just compare `TermId`s) and saves memory when the same subterms appear in many facts.

- **Safe sharing.** Multiple facts can reference the same subterm. When `WorkItem("WI-001", status: Open)` and `WorkItem("WI-001", status: Claimed(...))` share the `"WI-001"` string term, that's one allocation, not two.

- **Terms can be duplicated** — the same term structure may appear in different contexts (different rules, different facts). Hash-consing means duplication is free: the second occurrence just gets the same `TermId`.

**Scoped arenas don't work.** Old facts are retracted in arbitrary order, not stack order. A workitem asserted at time 1 may be superseded at time 100, while a workitem asserted at time 50 is still active. Stack-based deallocation (WAM-style truncation) cannot handle this.

### 3.2 Memory Reclamation

Since terms are immutable and retracted in arbitrary order, we need **reference-based reclamation**:

**Option A: Reference counting.** Each `TermId` has a refcount. When a fact is retracted, decrement refcounts on its terms. When a refcount reaches zero, free the slot (add to a free list for reuse). Subterms' refcounts are also decremented (cascading).

**Option B: Mark-and-sweep.** Periodically (or when the store grows past a threshold), walk all active facts and mark reachable terms. Sweep unmarked terms into a free list. Simpler than refcounting but pauses.

**Option C: Generational / Nursery.** Most terms are long-lived (parsed from source). Short-lived terms come from deduction (speculative, then either committed or discarded). Use a nursery for deduction terms; promote to the main store on commit; drop the nursery on failure. This also solves the speculative allocation problem from standardize-apart (see §3.4).

### 3.2.1 Cycle Safety

Reference counting fails silently on cycles. Can cycles form in the term store?

**The term graph is always a DAG** — two invariants guarantee this:

1. **Bottom-up construction.** Allocating `Fn(f, [t1, t2])` requires `t1` and `t2` to already exist. A `TermId` cannot reference a term not yet allocated. So the reference graph points strictly backward (to older terms).

2. **Occurs check in unification.** Binding `?x → t` requires that `?x` does not appear in `t` (after chasing all variable bindings). This prevents direct cycles (`?x = f(?x)`) and indirect ones (`?x = f(?y), ?y = g(?x)` — chasing gives `?y = g(f(?y))`, occurs check detects `?y` in the result).

**If the occurs check has a bug or is skipped, cycles form and refcounting leaks.** Mitigation options:

- **Never skip occurs check.** Performance cost is O(term_size) per variable binding. For our term sizes (small), this is negligible. Don't optimize it away.
- **Debug-mode cycle detector.** In debug builds, periodically verify the term graph is acyclic (DFS with color marking). Panic on cycle detection.
- **Fallback GC.** If we ever need to skip occurs check (we shouldn't), switch to mark-and-sweep. Keep the mark-and-sweep code written but disabled, as a safety net.

### 3.2.2 Rational Trees and the Y-Combinator

Can the term language express self-referential structures like `Y(Y)` (the Y-combinator applied to itself)?

**The kernel language is first-order** — no lambdas, no higher-order terms. `Fn(name, args)` is a named constructor/function symbol, not a closure. The Y-combinator cannot be directly expressed as a term.

However, the lambda calculus can be **encoded** as a sort with rules:

```
sort Lambda { entity var(n: String), entity app(f: Lambda, x: Lambda), entity lam(p: String, b: Lambda) }
rule eval(app(lam(?x, ?body), ?arg)) = subst(?body, ?x, ?arg)
```

Evaluating `eval(app(Y, Y))` produces an infinite chain of reductions. Each step creates new finite terms. The term store never holds a cycle — the **computation** diverges, not the **representation**.

**Key distinction:**

| | Cyclic terms | Non-terminating derivation |
|---|---|---|
| Example | `?x = f(?x)` (term points to itself) | `ancestor(?x,?z) :- parent(?x,?y), ancestor(?y,?z)` |
| Term store | Contains a cycle | All terms finite, DAG |
| Occurs check | Prevents this | Doesn't prevent this |
| Memory | Refcounting leaks | Refcounting fine |
| Detection | DAG verifier | Loop detection / depth limit |

**Design decision: no rational trees.** We require all terms to be finite (no cycles). The occurs check enforces this. Computations that would produce infinite structures instead diverge — caught by loop detection and depth limits in the deduction engine (kernel-language.md §8.2: "stratification and loop detection").

Some systems (SWI-Prolog) support rational trees by disabling the occurs check. We don't need this — the kernel's purpose is algebraic specification and verification, not general-purpose computation. Infinite structures have no normal form and cannot participate in proofs.

**Consequence:** Reference counting is sufficient for our term store. The DAG invariant holds by construction.

**Recommendation:** Reference counting with mandatory occurs check. Add debug-mode DAG verification. This is sufficient and avoids GC pauses.

### 3.3 Hash-Consed Term Store

```rust
struct TermStore {
    terms: Vec<Option<Term>>,         // Some = live, None = free slot
    hash_index: HashMap<Term, TermId>, // structural dedup
    refcounts: Vec<u32>,              // parallel to terms
    free_list: Vec<TermId>,           // reusable slots
}

impl TermStore {
    /// Allocate a term, deduplicating via hash-consing.
    /// If an identical term exists, increments its refcount and returns it.
    fn alloc(&mut self, term: Term) -> TermId {
        if let Some(&existing) = self.hash_index.get(&term) {
            self.refcounts[existing.index()] += 1;
            return existing;
        }
        let id = self.alloc_slot(term.clone());
        self.hash_index.insert(term, id);
        id
    }

    /// Decrement refcount. If zero, free the slot and cascade to subterms.
    fn release(&mut self, id: TermId) {
        let rc = &mut self.refcounts[id.index()];
        *rc -= 1;
        if *rc == 0 {
            let term = self.terms[id.index()].take().unwrap();
            self.hash_index.remove(&term);
            self.free_list.push(id);
            // Cascade: release each subterm
            for sub in term.subterms() {
                self.release(sub);
            }
        }
    }
}
```

### 3.4 Substitution (for Deduction — Layer 1+)

Deduction (unification, backward chaining) uses substitutions as a separate layer. Substitutions bind variables (by `VarId`) to existing `TermId`s — the substitution *itself* doesn't create new terms.

However, **standardize-apart does allocate terms.** Before unifying a rule against a query, each rule application renames its variables to fresh `VarId`s. This creates new `Term::Var(fresh_vid)` entries in the store. If unification then fails (e.g., `f1(?a, 5)` vs `f1(?b, 1)` — variables bind fine but `5 ≠ 1`), these speculative terms need cleanup.

**Consequence:** "just drop the Substitution" is not sufficient. Speculative term allocations from failed branches must also be released. Approaches:

1. **Track and release** — the search branch keeps a list of TermIds it allocated; on failure, release them all.
2. **Nursery arena** — speculative terms go into a short-lived arena (§3.2 Option C). On success, promote to the main store; on failure, drop the arena. This matches the "most terms are long-lived, search terms are short-lived" pattern.
3. **Separate lightweight store** — don't hash-cons speculative terms at all; only hash-cons when committing.

The nursery approach is preferred. Design deferred to Layer 1.

```rust
struct Substitution {
    bindings: HashMap<VarId, TermId>,
    parent: Option<Box<Substitution>>,
}

impl Substitution {
    fn resolve(&self, var: VarId) -> Option<TermId> { ... }

    /// Materialize: apply substitution to a term, allocating new terms in the store.
    /// Hash-consing ensures no duplicates. Refcounts are incremented for new references.
    fn materialize(&self, kb: &mut KnowledgeBase, term_id: TermId) -> TermId { ... }
}
```

### 3.5 Summary

| Aspect | Design choice |
|--------|--------------|
| Mutation | Immutable terms, new facts supersede old |
| Deduplication | Hash-consing (structural sharing via `HashMap<Term, TermId>`) |
| Term duplication | Free — same `TermId` returned |
| Memory reclamation | Reference counting with cascading release |
| Deduction temporaries | Substitution layer (no term allocation until commit) |
| Scoped arenas | Not used — retraction order is arbitrary |

## 4. Term Representation

```
Term
  ├── Const(Literal)                          -- ground value: 42, "hello", true
  ├── Var(VarId)                              -- logic variable: ?x
  ├── Fn { functor: Symbol, args: Vec<FnArg> }  -- compound: account(?id, ?bal)
  ├── Ref(Symbol)                             -- reference: Ref(banking.Money)
  ├── Unspecified { text, hints }             -- partial: <"not yet formal">
  ├── Bottom                                  -- ⊥
  └── Ident(Symbol)                           -- bare identifier (pre-resolution)

VarId { id: u32, name: Symbol }               -- Eq/Hash on id only; name for display
TermId(u32)                                    -- handle into hash-consed TermStore

FnArg
  ├── Positional(TermId)
  └── Named(Symbol, TermId)
```

**Variable identity.** Logic variables are identified by `VarId`, a unique
index.  The human-readable name (e.g. `"x"` from `?x`) is carried inside
`VarId` for debug/display only — `Eq` and `Hash` compare only the `id`
field, so hash-consing treats variables as equal iff they have the same
index.  Within a single rule, all occurrences of `?x` share one `VarId`.
Across rules, `?x` gets a fresh `VarId` each time (the standard
"standardize apart" step).  The parser's converter maintains a per-rule
variable scope (`HashMap<Symbol, VarId>`) and resets it at each rule,
constraint, and operation boundary.

**Functor identity.** `functor` is a single interned `Symbol` carrying the
fully-qualified name (e.g. `"banking.deposit"`).  Two domains that each
define `+` produce distinct symbols, so domain-scoped identity is resolved
before terms enter the store.

**Infix desugaring.** Infix terms (`a + b`, `x = y`) are syntactic sugar
for `Fn` applications (`add(a, b)`, `eq(x, y)`).  They are desugared
eagerly in the parser's CST→IR converter — the `Term` enum has no `Infix`
variant.  This keeps one fewer case in every traversal (subterms, unification,
substitution, hash-consing) with no loss of source information: spans for
error messages are tracked by the parse IR nodes that reference the term, not
by the term itself.

**Bare identifiers.** The `Ident(Symbol)` variant represents names that have
not yet been resolved to `Fn`, `Ref`, or `Var`.  At parse/load time, some
identifiers cannot be resolved because the definition they reference may not
have been loaded yet (e.g. cyclic imports between domains).  A post-load
**resolve pass** over the KB will convert remaining `Ident` terms once all
files are loaded and all sorts/entities are registered.

### 4.1 Subterm Access

```rust
impl Term {
    /// Iterate over immediate subterm ids.
    fn subterms(&self) -> impl Iterator<Item = TermId> {
        match self {
            Fn { args, .. } => args.iter().map(|a| a.term_id()),
            Unspecified { hints, .. } => hints.iter().copied(),
            _ => empty(),
        }
    }
}

impl TermStore {
    /// Walk all subterms of a term (depth-first).
    fn walk(&self, root: TermId) -> impl Iterator<Item = TermId> { ... }

    /// Check if `needle` appears anywhere in the term tree rooted at `haystack`.
    fn contains_subterm(&self, haystack: TermId, needle: TermId) -> bool { ... }

    /// Apply a substitution, returning a new TermId in this store.
    /// Only allocates new terms where substitution actually changes something.
    fn substitute(&mut self, term: TermId, subst: &Substitution) -> TermId { ... }
}
```

## 5. Sort Lattice and Subtype Relation

The kernel has a type system (sorts). Unification must respect it — `?x : Nat` cannot unify with `Account(...)`. This requires a **sort lattice** with a subtype (subsort) relation.

### 5.1 Sources of Subtyping

**Constructor ≤ Sort.** A sort with entity constructors enumerates its constructors. Each constructor's type is a subtype of the sort:

```
sort Nat { entity zero, entity succ(pred: Nat) }

  zero  : Nat    -- zero ≤ Nat
  succ  : Nat    -- succ ≤ Nat
```

This is exactly Maude's subsort relation: constructor sorts are subsorts of the declared sort. Pattern matching on `?x : Nat` can produce `zero` or `succ(...)`.

**Parametric instantiation.** `List{T=Int}` is a ground instantiation of the parametric sort `List`. The relation between `List` (with abstract `T`) and `List{T=Int}` is **instantiation**, not subtyping. But the constructor subsort relation applies to the instantiated version too:

```
nil  ≤ List{T=Int}
cons ≤ List{T=Int}    -- where head : Int, tail : List{T=Int}
```

**Abstract sorts.** `sort Scalar` has no constructors and no subtypes — it's opaque until bound via `where { Scalar = float }`. An abstract sort is a **type variable** in the sort lattice.

### 5.2 Types Are Terms (Reflection Principle)

In a reflective system, the language describes itself. A standard domain `anthill.reflect.syntax` will define:

```
domain anthill.reflect.syntax
  sort Type {
    entity SimpleType(name: Name)
    entity ParameterizedType(name: Name, bindings: List{T = SortBinding})
  }
  sort SortBinding {
    entity SortBinding(param: Name, bound: Type)
  }
end
```

This means types ARE terms — terms of sort `anthill.reflect.syntax.Type`. The type `List{T = List{T = Int}}` is:

```
ParameterizedType("List", [
  SortBinding("T", ParameterizedType("List", [
    SortBinding("T", SimpleType("Int"))
  ]))
])
```

This is a regular `Fn` term in the term store, hash-consed like any other term.

**Consequence: `SortId` is just `TermId`.** A sort in the lattice is identified by the `TermId` of its type-term in the store. Hash-consing gives us identity: `List{T=Int}` in two places → same `TermId` → same sort. No separate sort representation needed.

**In the Rust parser IR**, `TypeExpr` remains a convenient enum for building the parse tree. But when loading into the KB, each `TypeExpr` is converted to a term:

```rust
fn type_expr_to_term(store: &mut TermStore, ty: &TypeExpr) -> TermId {
    match ty {
        TypeExpr::Simple(name) =>
            store.alloc(Term::Fn { name: "SimpleType", args: vec![name_to_term(name)] }),
        TypeExpr::Parameterized { name, bindings } => {
            let binding_terms = bindings.iter()
                .map(|b| binding_to_term(store, b))
                .collect();
            store.alloc(Term::Fn {
                name: "ParameterizedType",
                args: vec![name_to_term(name), list_term(binding_terms)]
            })
        }
    }
}
```

**Rules can reason about types**, because types are queryable facts:

```
rule has_numeric(?domain, ?sort) :-
  imports(?domain, anthill.prelude.Numeric, ?bindings),
  binding(?bindings, "T", ?sort)
```

### 5.3 Sort Relations Are Facts

There is no separate `SortLattice` structure. Sort relationships are **facts in the KB**, and the subsort index is a **materialized index** maintained by the same `assert()` path as all other indexes.

When a sort with constructors is loaded:

```
sort Nat { entity zero, entity succ(pred: Nat) }
```

The loader asserts facts:

```
fact Subsort("zero", "Nat")
fact Subsort("succ", "Nat")
fact SortInfo("Nat", Defined)
fact SortInfo("zero", Constructor)
fact SortInfo("succ", Constructor)
```

The KB maintains materialized indexes over these facts internally:

```
// Inside KnowledgeBase (not a separate struct):
subsort_children: HashMap<TermId, Vec<TermId>>   // parent → children
subsort_parents: HashMap<TermId, Vec<TermId>>    // child → parents
sort_info: HashMap<TermId, SortKind>             // Abstract | Defined | Constructor
```

These indexes are updated when sort facts are asserted, just like `by_sort` and `by_functor`. `kb.is_subtype(sub, sup)` reads the index. `kb.register_sort()` and `kb.register_subsort()` are convenience methods that assert the appropriate facts and update the indexes atomically.

Built during domain loading (after parsing):
1. Parse all sort declarations
2. Convert each sort's `TypeExpr` to a type-term in the store (hash-consed)
3. For each sort with entity constructors, assert `Subsort` facts for constructors
5. For each `import ... where`, instantiate parametric sorts — producing new type-terms like `ParameterizedType("List", [SortBinding("T", SimpleType("Int"))])`

### 5.4 Subtype Checking

There is no separate `SortLattice` struct — these are methods on `KnowledgeBase`:

```rust
impl KnowledgeBase {
    /// Is `sub` a subtype of `sup`?
    /// Both are TermIds of type-terms. Checks the transitive closure of the subsort relation.
    fn is_subtype(&self, sub: TermId, sup: TermId) -> bool { ... }

    /// What are the immediate child sorts?
    /// For a sort with constructors, this returns its constructors.
    fn sort_children(&self, sort: TermId) -> &[TermId] { ... }

    /// What kind of sort is this? (Abstract, Defined, Constructor)
    fn sort_kind(&self, sort: TermId) -> Option<SortKind> { ... }

    /// What is the least common supersort of `a` and `b`?
    /// Returns None if they are unrelated. (Layer 1)
    fn join(&self, a: TermId, b: TermId) -> Option<TermId> { ... }
}
```

### 5.5 Impact on Unification

Typed unification differs from standard first-order unification:

1. **Variable binding checks sort compatibility.** When binding `?x : S` to term `t : T`, we require `T ≤ S` (the term's sort must be a subtype of the variable's declared sort). Otherwise, unification fails with a type error — not a structural mismatch.

2. **Constructor matching respects the sort hierarchy.** Matching `?x : Nat` against `succ(zero)` succeeds because `succ ≤ Nat`. Matching `?x : Nat` against `Account(...)` fails because `Account` is not in the `Nat` subsort chain.

3. **Fn terms carry sort information.** `gt(balance(?a), zero-val)` — the engine needs to know that `gt` expects `Ordered` arguments, `balance` returns `Money`, and `Money` has `Numeric` (which extends `Ordered`). This is resolved via operation signatures in the domain.

4. **Sort inference for bare identifiers.** A bare `zero-val` in a rule body is an `Ident` at parse time. During sort resolution, it's looked up as an operation (`zero-val() -> T`) and the concrete sort is determined from the domain's imports.

### 5.6 Sort-Aware Substitution (Layer 1)

When materializing a substitution (committing a successful derivation):

```rust
impl Substitution {
    fn materialize(
        &self,
        kb: &mut KnowledgeBase,
        term_id: TermId,
    ) -> Result<TermId, TypeError> {
        // Walk the term, replacing Var(vid) with bindings[vid].
        // At each replacement, verify sort compatibility via kb.is_subtype().
        // Hash-consing ensures no duplicate terms created.
        ...
    }
}
```

### 5.7 Relation to Maude

This is directly the **order-sorted algebra** approach from Maude/OBJ:
- Sorts form a partial order (the subsort relation)
- Terms have a **least sort** — the most specific sort that contains them
- Unification is **order-sorted unification** — respects the sort hierarchy
- Constructors introduce subsort relationships

The key reference is Meseguer's order-sorted algebra papers and the Maude book (Chapter 3: Membership Equational Logic).

## 6. Unification

Order-sorted unification with occurs check. Respects the sort lattice — variable bindings are only allowed when sorts are compatible.

```rust
/// Attempt to unify two terms, extending the substitution.
/// Returns Err if unification fails (structural mismatch or sort incompatibility).
fn unify(
    kb: &KnowledgeBase,
    subst: &mut Substitution,
    t1: TermId,
    t2: TermId,
) -> Result<(), UnifyError> {
    let t1 = subst.chase(t1);  // follow variable bindings
    let t2 = subst.chase(t2);

    match (kb.get_term(t1), kb.get_term(t2)) {
        (Var(vid), _) => {
            if t1 == t2 { return Ok(()) }
            // occurs check: vid must not appear in t2
            if kb.contains_var(t2, *vid, subst) {
                return Err(UnifyError::OccursCheck)
            }
            // sort check: sort_of(t2) must be ≤ declared sort of variable
            let var_sort = kb.sort_of_var(*vid);
            let term_sort = kb.sort_of_term(t2);
            if !kb.is_subtype(term_sort, var_sort) {
                return Err(UnifyError::SortMismatch { expected: var_sort, actual: term_sort })
            }
            subst.bind(*vid, t2);
            Ok(())
        }
        (_, Var(_)) => unify(kb, subst, t2, t1),
        (Const(a), Const(b)) if a == b => Ok(()),
        (Fn { functor: f1, args: a1 }, Fn { functor: f2, args: a2 })
            if f1 == f2 && a1.len() == a2.len() =>
        {
            for (arg1, arg2) in a1.iter().zip(a2.iter()) {
                unify(kb, subst, arg1.term_id(), arg2.term_id())?;
            }
            Ok(())
        }
        _ => Err(UnifyError::Mismatch),
    }
}
```

Key properties:
- `unify` does **not** allocate new terms — it only extends the `Substitution`.
- Sort checking is integrated into variable binding — not a separate pass.
- New terms are only created when materializing a successful derivation.

## 7. The Knowledge Base as a Self-Indexed Structure

The previous sections described separate structures: TermStore, SortLattice, FactBase, RuleIndex. In practice, these collapse into **one unified structure** — the Knowledge Base — that maintains its own indexes, like a database or an e-graph.

### 7.1 Why Unify

- Assert a fact → must update term store (allocate), sort lattice (check type), fact indexes (by sort, functor), and trigger forward chaining (rule index). These aren't independent operations — they're one atomic `assert`.
- Equational rules (`add(?a, ?b) = add(?b, ?a)`) establish equivalence classes. An e-graph merges equivalent terms, and congruence closure propagates: if `a = b` then `f(a) = f(b)`. This affects indexing (query by functor must respect equivalences) and unification (terms in the same e-class unify).
- The subsort relation, fact indexing, and equational reasoning are all **views over the same data**. Maintaining them as separate structures means coordinating updates across all of them. A unified structure maintains consistency internally.

### 7.2 The KB Structure

One struct, all indexes internal. Sort relations are facts; the subsort index is maintained alongside other indexes.

```
KnowledgeBase
  ├── terms (hash-consed store)
  │     ├── nodes: Vec<Option<Term>>
  │     ├── hash_index: HashMap<Term, TermId>
  │     ├── refcounts: Vec<u32>
  │     └── free_list: Vec<TermId>
  │
  ├── interner: Interner
  │
  ├── facts: Vec<FactEntry>
  │
  ├── indexes (all maintained atomically by assert/retract)
  │     ├── by_sort: HashMap<TermId, Vec<FactId>>
  │     ├── by_functor: HashMap<Symbol, Vec<FactId>>
  │     ├── by_domain: HashMap<TermId, Vec<FactId>>
  │     ├── subsort_children: HashMap<TermId, Vec<TermId>>  -- parent → child sorts
  │     ├── subsort_parents: HashMap<TermId, Vec<TermId>>   -- child → parent sorts
  │     ├── sort_info: HashMap<TermId, SortKind>
  │     ├── discrim: SubstTree<FactId>                      -- substitution tree (§7.6)
  │     ├── by_body_functor: HashMap<Symbol, Vec<RuleId>>   -- for forward chaining (Layer 2)
  │     └── by_head_functor: HashMap<Symbol, Vec<RuleId>>   -- for backward chaining (Layer 2)
  │
  └── eclasses (Layer 2 — e-graph for equational reasoning)
        ├── union_find: Vec<TermId>
        └── class_members: HashMap<TermId, Vec<TermId>>

FactEntry
  ├── term: TermId
  ├── sort: TermId            -- sort is a TermId (types are terms)
  ├── domain: TermId
  ├── meta: Option<TermId>
  └── retracted: bool
```

### 7.3 Operations

All operations go through the KB, which maintains internal consistency:

```rust
impl KnowledgeBase {
    /// Allocate a term (hash-consed, refcounted).
    fn alloc(&mut self, term: Term) -> TermId { ... }

    /// Allocate a fresh logic variable id, carrying the display name.
    fn fresh_var(&mut self, name: Symbol) -> VarId { ... }

    /// Assert a fact. Updates all indexes, triggers forward chaining (Layer 2).
    fn assert_fact(&mut self, term: TermId, sort: TermId, domain: TermId, meta: Option<TermId>) -> FactId {
        let fact_id = ...;
        // Update indexes
        self.by_sort.entry(sort).or_default().push(fact_id);
        if let Term::Fn { functor, .. } = self.terms.get(term) {
            self.by_functor.entry(functor).or_default().push(fact_id);
        }
        fact_id
    }

    /// Retract a fact. Updates indexes, decrements refcounts.
    fn retract(&mut self, fact_id: FactId) { ... }

    /// Query: all facts of a given sort (including subsorts).
    fn by_sort(&self, sort: TermId) -> Vec<FactId> { ... }

    /// Query: all facts with a given top-level functor.
    fn by_functor(&self, sym: Symbol) -> Vec<FactId> { ... }

    /// Assert an equation (from an equational rule). Layer 2.
    /// Merges e-classes, propagates congruence, updates indexes.
    fn assert_equal(&mut self, t1: TermId, t2: TermId) {
        self.eclasses.union(t1, t2);
        self.rebuild_congruence();  // propagate: if a=b then f(a)=f(b)
    }

    /// Query: find facts matching a pattern.
    /// Uses the substitution tree (§7.6) for multi-level candidate narrowing,
    /// then verifies with match_term for deep nested matching.
    fn query(&self, pattern: TermId) -> Vec<(FactId, Substitution)> {
        let candidates = self.discrim.query(&self.terms, pattern);
        // Filter retracted, verify with full match_term
        ...
    }

    /// Unify two terms, respecting e-classes and sort lattice. Layer 1+.
    fn unify(&self, subst: &mut Substitution, t1: TermId, t2: TermId) -> Result<(), UnifyError> {
        // Chase e-class representatives before comparing
        let t1 = self.eclasses.find(subst.chase(t1));
        let t2 = self.eclasses.find(subst.chase(t2));
        ...
    }
}
```

### 7.4 E-Graph Integration

Equational rules like `add(?a, ?b) = add(?b, ?a)` don't just store an equation — they **merge equivalence classes** of terms:

1. Rule fires: `add(3, 5)` and `add(5, 3)` are asserted equal
2. E-graph merges their e-classes: `{add(3,5), add(5,3)}` are now equivalent
3. Congruence closure: any context containing `add(3,5)` is now equivalent to the same context with `add(5,3)`
4. Indexes are updated: querying for `add(3,5)` also finds `add(5,3)`
5. Unification: `?x` matching `add(3,5)` also matches `add(5,3)`

This is exactly what **egg** (e-graphs good) does for equality saturation. The KB's e-graph is a lighter version — we don't need full equality saturation, just congruence closure for asserted equalities.

### 7.5 Retraction

Retraction marks a fact as retracted and removes it from indexes. Refcounts on the fact's terms are decremented. The e-graph is NOT affected by retraction — equalities, once derived, persist (they are logical consequences, not assertions that can be withdrawn). If we need to retract an equation (e.g., a rule is removed), that requires rebuilding the affected e-classes, which is more expensive.

### 7.6 Substitution Tree (Discrimination Index)

The **substitution tree** is the primary structural index for term matching, replacing linear scan after `by_functor`. It is a discrimination tree that collects variable bindings during traversal — at each leaf, the stored data (FactId, rule RHS, etc.) is immediately usable with the accumulated substitution.

**Two edge types at each node:**

- **Concrete edges** — `HashMap<DiscrimKey, Node>`: dispatch on specific value (functor, literal, ident, etc.)
- **Variable edges** — `Vec<(VarId, Node)>`: match anything, bind VarId to the query value at this position

Ground facts create only concrete edges. Rule patterns with variables create variable edges at `Var` positions.

**Key extraction.** Terms are flattened into a sequence of `DiscrimKey` values. For `Fn { functor, args }`:

```
[Functor(sym), Arity(n), <arg_keys>...]
```

Arguments: positional first, named sorted by `Symbol::index()` for canonical ordering (the term itself is not modified). Each arg emits a structural marker (`Positional` or `NamedKey(sym)`) followed by a one-level value key (`Lit(...)`, `Ident(...)`, `FnRef { functor, arity }`, etc.).

Example — `Account(id: "A001", name: "Savings")`:
```
[Functor(Account), Arity(2), NamedKey(id), Lit("A001"), NamedKey(name), Lit("Savings")]
```

**Traversal semantics.** When walking the tree with a query term:

- Query concrete, tree concrete: follow if keys match (no binding)
- Query concrete, tree variable: bind tree's VarId to query value, follow
- Query variable, tree concrete: follow all concrete edges (bind query VarId)
- Query variable, tree variable: follow, bind both

At each leaf reached: `(LeafData, Substitution)` with all bindings collected along the path.

**Persistent substitution.** At branch points, the substitution is forked via `clone()`. The `PersistSubst` trait provides:

```rust
trait PersistSubst: Clone {
    fn new() -> Self;
    fn with_binding(self, var: VarId, term: TermId) -> Self;
    fn resolve(&self, var: VarId) -> Option<TermId>;
    fn into_substitution(self) -> Substitution;
}
```

`with_binding` consumes self (after clone at branch points). Two implementations:

- **SmallSubst** — `SmallVec<[(VarId, TermId); 8]>`. Clone = memcpy. `with_binding` pushes and returns self. Best for ≤ 8 bindings (Layer 0 fact patterns).
- **SharedSubst** — Arc cons-list. Clone = Arc refcount bump, O(1). `with_binding` prepends a new `Arc<SubstCell>` from the moved head. Structural sharing between branches — for deeper patterns with many branch points.

**Generic leaf type.** `SubstTree<L>` is generic over the leaf data:
- Fact indexing: `L = FactId`
- Rule indexing (future): `L = RuleEntry { rule_id, rhs: TermId }`

**Current integration.** Layer 0 uses the tree as a candidate-narrowing step: `discrim.query()` produces candidate `(FactId, _)` pairs, then `match_term()` verifies for deep nested matching beyond one arg level. When deeper indexing is added, `match_term` becomes unnecessary.

**Reference:** Shevchenko & Doroshenko, "TermWare-3" (2019) — discrimination trees for multi-level term dispatch.

### 7.7 Reference: E-Graphs

- **egg** (Rust library): https://egraphs-good.github.io/ — e-graphs with equality saturation
- **eqlog**: Datalog extended with equality — close to our equational rules
- Congruence closure: standard algorithm from Nelson-Oppen (1980)
- The connection: our KB is essentially a **Datalog + equality** engine (eqlog), with order-sorted types (Maude) and hash-consed terms

## 8. Open Questions

1. **Variable identity and scoping.** ~~Resolved.~~ Variables are identified by `VarId { id: u32, name: Symbol }`, where `Eq`/`Hash` compare only the `id`. The human-readable name is carried for display. Within a single rule, all occurrences of `?x` share one `VarId`. Across rules, the converter resets its variable scope, so `?x` gets a fresh `VarId`. At deduction time (Layer 1+), each rule application will use `kb.fresh_var()` to standardize apart.

2. **Sort of a variable.** The spec says `Var(type, name)` — variables have a declared type. But in the surface syntax, `?x` has no type annotation. The type is **inferred** from the context: if `?x` appears as argument to `balance(a: Account)`, then `?x : Account`. This requires a sort inference pass after parsing and before deduction. Sort information can be associated with `VarId` via a side table or by wrapping in a typed term.

3. **Negation.** The spec mentions `not(...)` in rules (§10.3 audit example: `not(AuditEntry(...))`). This is negation-as-failure (NAF), not classical negation. It interacts with the sort lattice: `not(P)` succeeds when `P` cannot be derived. NAF requires stratification to be well-defined. The term store doesn't need special support — `not` is a regular `Fn` term. The deduction engine interprets it specially.

4. **Infix desugaring.** ~~Resolved.~~ Infix terms (`a + b`, `x = y`) are desugared to `Fn` applications (`add(a, b)`, `eq(x, y)`) eagerly in the parser's CST→IR converter. The `Term` enum has no `Infix` variant. Source spans for error messages are tracked by the parse IR nodes, not by the term.

5. **Hash-consing and `Eq`/`Hash` for `Term`.** ~~Resolved.~~ `Float` uses `OrderedFloat<f64>` from the `ordered-float` crate, which provides `Eq`/`Hash`. `VarId` uses manual `Eq`/`Hash` that compares only the `id` field (name is display-only). `Term` derives `Eq`/`Hash`, which correctly delegates to these implementations.

6. **Ident resolution.** `Term::Ident(Symbol)` represents bare identifiers that haven't been resolved to `Fn`, `Ref`, or `Var`. A post-load resolve pass is needed after all files are loaded (to handle cyclic imports). Not yet implemented.

7. **Std-lib syntax sugar.** Domain-specific syntax sugar (e.g., list literals, map syntax) should NOT be added to the core tree-sitter grammar. It should be provided via an extension mechanism. The core grammar handles only the kernel language.

## 9. Implementation Layers

The `KnowledgeBase` is built incrementally. Each layer adds capability without changing the interface:

### Layer 0: Parse + Store + Index + Pattern Matching (Stage 0)

```
KnowledgeBase
  ├── terms: hash-consed Vec<Term> with refcounting
  ├── facts: Vec<FactEntry> with by_sort, by_functor, and by_domain indexes
  ├── discrim: SubstTree<FactId> — substitution tree for structural matching (§7.6)
  ├── sorts: subsort/supersort relations from parsed domain declarations
  ├── next_var: u32 (counter for fresh VarId allocation)
  └── rules: stored but not evaluated
```

- Parser allocates terms into KB via `kb.alloc()`
- Domain loading registers sorts, asserts parsed facts via `kb.assert()`
- `kb.by_sort()` and `kb.by_functor()` for index-based queries
- `kb.query(pattern)` uses the substitution tree (§7.6) for multi-level
  candidate narrowing, then verifies with `match_term` for deep nested
  matching — e.g., `WorkItem(?id, status: Open)` finds all open workitems.
  No speculative term allocation: patterns are caller-owned, matching only
  creates bindings in the `Substitution`.
- `kb.match_term(pattern, target)` — one-way unification of a single term
- `kb.fresh_var(name)` allocates unique variable identities
- Substitution struct (binds `VarId → TermId`), used by pattern matching
- `load()` takes a `SourceResolver` trait for resolving import paths to source text
  - CLI provides real FS implementation; tests use `NullResolver`
  - Import cycle detection via `HashSet<String>` of loaded paths
- Infix desugaring happens eagerly in the CST→IR converter
- Variable scoping: converter resets `var_scope` at each rule/constraint/operation boundary
- `Ident` terms pass through unresolved — resolve pass is future work
- No forward chaining, no e-classes yet

### Layer 1: Full Unification + Rule Evaluation (Stage 0.5)

Add to Layer 0:
- Sort inference (fill in variable sorts from operation signatures)
- `kb.unify()` — full two-way unification with sort checking and occurs check
- Standardize-apart: `kb.fresh_var()` for each rule application (needs nursery
  for speculative allocations, see §3.4)
- `Ident` resolution pass (after all files loaded)

### Layer 2: Forward Chaining + Equations (Stage 1)

Add to Layer 1:
- `assert()` triggers forward chaining via rule index
- `assert_equal()` merges e-classes, congruence closure propagates
- Backward chaining with standardize-apart and substitution scoping
- Constraint checking (denial rules)
- Negation-as-failure with stratification
