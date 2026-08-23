# Proposal 055 implementation: resolved type values in expression positions

**Language owner:** [`../proposals/055-types-in-value-position.md`](../proposals/055-types-in-value-position.md).
This document owns the parse/convert/load/type mechanics. The proposal owns
what programs mean.

## 1. Invariant

A nominal type is classified once, after name resolution and before ordinary
typing, and that classification survives as an explicit resolved expression:

```rust
enum ResolvedExpr {
    // existing value forms
    ValueRef(ValueId),
    Call(ResolvedCall),
    Constructor(ResolvedConstructor),

    // A bare sort/type-parameter reference or a sort-headed `application`.
    TypeValue(TypeExpr),
}
```

The exact Rust owner and names may differ; the invariant may not. No later
consumer may rediscover type-ness from an expected `Type`, from syntax alone,
or from the carrier (`TermId` versus `Value::Node`). Expected types validate a
classified expression; they do not classify it.

This separates two questions:

1. **Denotation:** does `Cell[Int64]` denote a `Type` value here?
2. **Validation:** does the enclosing expression accept a `Type` value?

Raw rule data may have no declared column type and therefore no validation
answer. It must still preserve the same `TypeValue` denotation rather than
falling back to an unresolved or differently-shaped term.

## 2. Parse boundary

No grammar change is required for the implicit nominal forms:

- a bare nominal type is already `name` / `absolute_name`;
- an applied nominal type is already `application`;
- the parse IR already preserves `[…]` versus `(…)`.

The parser does not decide whether `Cell[Int64]` is a type. Conversion keeps a
neutral name/application until the definitions and lexical bindings needed by
resolution exist. Resolution then classifies by the head symbol:

| resolved head | resolved expression |
|---|---|
| sort or standalone-entity sort | `TypeValue(TypeExpr)` |
| in-scope type parameter | `TypeValue(TypeExpr)` |
| local, field or value parameter | ordinary value reference |
| operation/relation used with `(...)` | call/goal |
| sort used with `(...)` | constructor call, subject to the existing surface gate |
| operation used as `op[T](...)` | typed call; `op[T]` is the callee, not a value |
| nothing | loud `UnresolvedName` |

The outer head of a call, rule/fact clause, or constructor is never itself a
value-expression occurrence. Classification recursively begins at its
arguments.

## 3. Value-expression occurrence audit

The maintainable rule is grammatical rather than a hand-maintained hint list:

> Every child whose grammar/IR role is `ValueExpression` recursively admits
> `ResolvedExpr::TypeValue`. A child whose role is head, callee, pattern,
> binder, label, member name, metadata key or `TypeExpr` does not.

The current grammar's value-bearing sites are:

| family | occurrences | result |
|---|---|---|
| application | positional and named call/constructor arguments | admit |
| operation expression | body/result (there is no separate `return` node) | admit |
| sequencing | `let_chain.value`, `let_chain.body`; rule-body `let_binding.value` | admit |
| conditionals | `if.condition`, `then`, `else` | admit; ordinary typing rejects `Type` as a Boolean condition |
| matching | scrutinee, branch guard, branch body | admit; patterns do not |
| functions | lambda body | admit; lambda pattern/binder does not |
| literals | collection, set and tuple element values, including named tuple values | admit |
| expression composition | parenthesized expression; infix/prefix operands | admit |
| projection | dot/distributive receiver | admit, subject to §4 |
| quantification | bounded-quantifier collection and goals in its body | admit; quantifier binder does not |
| logic | rule-body goals, goal arguments, nested data terms | admit; outer rule/fact heads do not |
| facts | constructor/entity field values | admit; top-level instance claim stays declaration-shaped |
| proofs | `conclude` goal and continuation body | admit |
| metadata | metadata values | admit; metadata keys do not |

Controls must pin both sides at each family: a nominal type occurrence that was
previously rejected becomes a `Type` value, while the corresponding head,
label, binder or pattern remains unchanged or loudly refused.

## 4. Dot receiver split

A type-shaped receiver currently participates in two different mechanisms:

```anthill
Map[K = String].empty()  -- sort companion/static lookup
Cell[Int64].name         -- potentially a member of the Type value
```

Do not settle this by whichever lookup happens first. Preserve the distinction
in the resolved receiver or projection node, for example:

```rust
enum ResolvedReceiver {
    Value(ResolvedExpr),
    TypeValue(TypeExpr),
    SortCompanion(TypeExpr),
}
```

Existing companion syntax and lookup remain authoritative. If a surface can
name both a companion member and a `Type` member and no existing rule orders
them, refuse the ambiguity naming both routes.

## 5. Structural type expressions

The full `_type` grammar is wider than nominal `name` / `application`. Tuple and
arrow type surfaces overlap existing value syntax:

```anthill
(left: Int64, right: String)  -- also a tuple value
(Int64) -> String             -- overlaps expression/operator syntax
```

They are therefore not implicitly classified in value expressions. Reification
uses the existing generic bridge, whose bracket is statically a type position:

```anthill
type_value[(left: Int64, right: String)]()
type_value[(Int64) -> String]()
```

`type_value[T]()` remains useful for a generic body's own type parameter too.
It lowers directly to `ResolvedExpr::TypeValue`; it does not evaluate a value
or dereference a `Type` value back into the typer.

## 6. Relationship to proposals 060 and 062

Brackets keep one meaning: they bind declaration-level type/requirement inputs.
They do not become predicate value arguments.

```anthill
requires Ord[X]                          -- sort requirement; `Ord[X]` is TypeExpr
require[Ord[X]]                          -- proposal 060 dictionary acquisition
is_entity_of(Trust, TrustLevel)          -- two ordinary goal arguments
is_entity_of[Trust, TrustLevel]          -- invalid unless that head declares such type parameters
```

`is_entity_of` is currently an untyped two-column rule shadowed by a builtin.
In proposal 062's guard, `Trust` resolves to the enclosing sort parameter and
`TrustLevel` to a sort, so both ordinary argument expressions become explicit
`TypeValue` nodes. At discharge their structural type terms are substituted
into the ordinary SLD goal. No source-level wrapper and no special
`is_entity_of` typing rule is required.

Proposal 060 supplies the matching precedent: a typed clause declaration is
classified statically and compiles to an ordinary generated goal. Runtime SLD
sees terms and carried types, not a typing operation.

## 7. Existing lowering paths

The WI-709/WI-710 inventory remains the coverage checklist:

| path | role | required change |
|---|---|---|
| `type_expr_to_child` | genuine type annotations | no value crossing; retain type-argument validation |
| typer expression lowering | operation expressions | consume resolved `TypeValue`, delete expectation-gated classification |
| `convert_term` | fact/constraint terms | preserve `TypeValue`; validate declared fields where a signature exists |
| `build_body_atom_occurrence` | rule-body occurrences | preserve `TypeValue`; validate typed/declared columns where available |

The last two paths must distinguish denotation from validation. A declared
`Type` field accepts the value. A declared `Term` field accepts the structural
carrier as the raw-term substrate. Any other declared sort is a loud mismatch.
An undeclared relational column preserves the type term and participates in
relation-column inference; it is not silently discarded.

The existing gates remain:

- **depth:** a top-level sort-headed clause may be an instance claim; a nested
  sort-headed bracket application is a type value;
- **surface:** `Sort[…]` is type/instance application, while `Sort(…)` is
  construction;
- **call:** `op[T](…)` is a typed call, not reification of `op[T]`.

## 8. Diagnostics

Required diagnostics are local to classification or ordinary validation:

- unresolved head: `UnresolvedName` at the name;
- undeclared/duplicate/over-applied type binding: existing type-argument error
  at the bracket application;
- wrong destination: `expected String, got Type (Cell[Int64])`, not an
  unresolved nested name;
- forgotten constructor parentheses in a `Type`-accepting position: the error
  or trace must name the denoted sort so the implicit reading is visible;
- structural type written without `type_value`: point to
  `type_value[<type>]()`;
- ambiguous companion versus `Type` member: name both lookup routes.

Do not retain a fallback that retries a failed value resolution as a type (or
the reverse). Resolve the symbol once and classify loudly.

## 9. Test matrix and controls

Each admitted family in §3 needs:

1. a driving test that evaluates/resolves the expression and asserts the
   resulting `Type` value, not merely that the file loads;
2. a negative destination test (`String`/`Bool` where appropriate);
3. a control proving the adjacent non-value role is not reclassified;
4. bare and applied nominal variants;
5. a logical-variable argument where the type remains non-ground;
6. raw rule/fact and typed operation-expression carriers where both paths
   must denote the same structure.

The minimum cross-proposal controls are:

- `requires Ord[X]` still creates a requirement edge;
- `require[Ord[X]]` still creates/fetches a dictionary;
- `is_entity_of(Trust, TrustLevel)` substitutes and resolves as an ordinary
  two-argument goal;
- `is_entity_of[Trust, TrustLevel]` is refused for an unparameterized rule;
- a typed head from proposal 060 still generates `domain` and does not change
  the stored discrimination-tree head.

Use `rustland/scripts/test.sh` for Rust test runs. Before commit, run the
repository's code-review skill; if unavailable, report that it was not run.

## 10. Delivery order

1. Introduce the resolved `TypeValue` distinction without widening acceptance;
   translate currently accepted expectation-hinted sites into it.
2. Make every operation-expression occurrence in §3 consume it; add both-side
   controls.
3. Carry the distinction through raw fact/rule lowering and add declared-column
   validation.
4. Decide and implement the dot receiver split.
5. Add structural `type_value[…]()` cases and diagnostics.
6. Remove `type_slot_arg_hint` as a classifier; expected `Type` remains an
   ordinary validation/inference input only.
7. Update the kernel specification and proposal 062's producer wording.

Each step should be independently loud when an unhandled carrier or occurrence
is reached; no compatibility fallback should silently preserve the old
expectation-directed result.
