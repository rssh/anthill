# 072: Constructor contracts — `requires` and `ensures` on an entity declaration

## Status: Draft (2026-10-17). The user asked on 2026-10-17, while proposal 037 was being revised, that this be a proposal of its own rather than part of 037. Nothing here is implemented.

## Tracked by: WI-20261017-WPBXQ (the implementation, acceptance rows 1–4) and WI-20261017-J4WGC (row 5, proposal 037's pool, after 050.1 stage 1). Designed under WI-20261017-T34HP (user, 2026-10-17; `docs/design/037-implementation.md` D6).

## Relates to: [037](037-anthill-state-model.md) §3.3 (a keyed sort's constructor declares its connection to the sort's pool), [050.1](050.1-memory-alias-and-maybe-connected.md) (memory relations: §2's construction rule, §8's fresh default), [041](041-operation-result-naming.md) (the `result` binder), [058](058-modular-instances.md) §8 (the two kinds of `requires` item), `docs/kernel-language.md` §5.2 (entities and sort-level `requires`), §5.4 (a constructor in an operation body is a call), §8.5 (proof obligations).

## The problem

An entity declaration can say nothing about the values it builds: it has no precondition on its fields and no postcondition.

In an operation body a constructor is a call like any other (kernel-language §5.4), but unlike an operation it brings no contract:

- **Invariants.** `positive(n: Int64)` cannot say that `n` is greater than zero.
- **Memory.** 050.1 gives every construction one fixed reading: the value lies in the regions of its fields and adds none of its own. Proposal 037 needs a keyed sort to say the opposite, that each of its values names something outside the process and is connected to the sort's pool.

## 1. Syntax

```
Entity       ::= DescriptionBlock* [Visibility] 'entity' Name ['(' FieldList ')'] EntityClause*
EntityClause ::= 'requires' Goal (',' Goal)*
               | 'ensures' RuleBody
```

```anthill
sort Positive
  entity positive(n: Int64)
    requires gt(n, 0)
end

entity FileStore(root: String, convention: FileConvention)
  ensures memory_maybe_connected(result, file_storage)  -- proposal 037 §3.2
```

- **Fields are named bindings in both clauses,** as an operation's parameters are in its clauses. `ensures` may also name `result`, the built value. It is declared per entity (`positive.result`), as proposal 041 declares an operation's.
- **An entity's `requires` holds value preconditions only.** A spec requirement (`requires Eq[T = K]`) belongs to the sort (§5.2). On an entity it is a load error that names that repair, since a constructor carries no requirement dictionary (§5.4).
- **An entity without fields may carry `ensures` only.** It has nothing to constrain.

## 2. `requires` is owed wherever the entity builds a value

- **At a construction call in an operation body**, the precondition is proved from what the caller knows, which is proposal 050's logical environment Γ, exactly as an operation's value precondition is proved (WI-539). An unproved precondition is a load error.
- **In a clause**, a constructor is a term the clause matches, not a call (§5.4). Its precondition is judged as a rule-body call's is (WI-557, WI-602):
  - a ground refutation is a load error, so `fact holds(positive(n: 0))` is refused;
  - an undetermined precondition floats.
- **A term built by unification during resolution is not checked.** That is the one path left open (§5).

**What was required is kept.** A construction stores its arguments in its fields, so what its `requires` proved of the arguments still holds of the fields afterwards. After a construction call, Γ holds each `requires` item with each field name replaced by the same field of the result: building `positive(n: x)` under `requires gt(n, 0)` adds `gt(result.n, 0)` for the value bound as `result`. So an entity's `requires` is also an implicit `ensures`, assumed wherever §3 assumes the explicit one:

```anthill
operation half_of(b: Int64) -> Int64 requires gt(b, 0) = …

operation use(p: Positive) -> Int64 =
  match p case positive(n: m) -> half_of(m)        -- gt(m, 0) comes from positive's requires
```

## 3. `ensures` is a property of every value the entity builds

A constructor has no body, so its explicit `ensures` is not proved. It is an axiom about the values the entity builds, trusted as a host operation's clauses are (050.1). The implicit `ensures` of §2 differs: it was proved at each construction call. The typer assumes both in three places:

- **At a construction call,** as it assumes an operation's `ensures` at a call (050's call rule).
- **At a pattern that matches the entity,** for the value it matches.
- **For any value of a sort all of whose entities declare it:** a parameter, a call result, a field read.

The third place is what makes proposal 037's pools sound. Consider a `FileStore` returned by an operation that declares no memory clause, as in `let s = pick(kb)`. Without the third place, 050.1's default would make `s` fresh, and a write through `s` would be dropped from the row.

Where an entity's memory `ensures` and 050.1's fresh default disagree about a call's result, the entity's clause wins, because it speaks of the result through the result's sort. That refines 050.1 §8, which reads "a result no clause speaks of is connected with nothing".

## 4. What does not change

- **An entity with no clauses** means what it means today.
- **Matching and unification.** A clause constrains what may be built. It never filters what matches.
- **Dispatch, layout and equality.** A constructor still carries no requirement dictionary, and an entity's derived `Eq` is unaffected.

## 5. Open questions

- **A term built by unification during resolution** is not checked against its entity's `requires`; an example is a rule head with variables, bound when the rule fires. Checking it would put a proof at every unification that builds a term. Leaving it open means an `ensures` that rests on a `requires`, the implicit one of §2 included, may be assumed of a value nothing checked. A memory `ensures` like 037's rests on nothing, so it is unaffected.
- **Whether an `ensures` that follows from its entity's `requires` is proved** rather than trusted.
- **How a constructor's `requires` enters §8.5's proof obligations.**

## 6. Implementation

- **Grammar:** `EntityClause` after the field list, in both `tree-sitter-anthill` and the Scala parser.
- **Loader:** the clauses are stored with the entity, as an operation's are, and `result` is declared per entity.
- **Typer:**
  - the precondition at construction calls, through the call-site contract machinery (WI-539);
  - the implicit `ensures` added to Γ after a construction call, where a callee's `ensures` is added today (`assume_call_ensures`, `kb/typing/effects.rs`);
  - the ground-term check in clauses;
  - the `ensures` at calls, patterns and values of the sort.
- **Memory:** the memory half takes effect with 050.1 stage 1 (WI-20261015-809JN), which reads memory clauses at calls.
- **Spec:** §5.2's entity grammar, and §5.4's paragraph on constructors as calls.

## Acceptance

Each row drives the capability rather than only loading:

1. A construction call whose precondition is unproved is refused, and the same call with the precondition proved loads and builds the value.
2. A fact holding a ground term that refutes its entity's precondition is refused, and one that satisfies it loads.
3. A spec requirement written on an entity is refused, naming the sort-level form.
4. What was required is kept: §2's `use` loads, and the same program with `positive`'s `requires` removed is refused at `half_of(m)`.
5. With 050.1 stage 1, a write through a `FileStore` that an operation without a memory clause returns stays in the row.
