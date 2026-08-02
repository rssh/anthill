# sql-store

The **shape** of a queryable SQL persistence backend: what a store sort, its
dialects, and its query bindings look like when written against the abstract
store algebra.

**This example does not run.** There is no host behind it — see below. It is here
so that a backend author has something to copy, and so that the shape is checked
by the compiler instead of living in a design document.

## Why it is an example and not a standard library

The abstract algebra it is written against **is** standard library —
`stdlib/anthill/persistence/store.anthill`, where `Store` / `NonMonotonicStore` /
`QueryableStore` / `BulkStore` declare the operations every backend supplies. That
file stays: it is the language-agnostic spec, and the two filesystem backends
realize it.

This file supplies no realization. Nothing implements a SQL backend in any host —
`rustland/anthill-core/src/persistence/` carries only the two file-store backends —
so `retract` / `update` / `retrieve` against a `SqlStore` value reach no registered
mirror. A shape no host realizes is an example, not a standard library: the rule is
stated in `docs/proposals/038-builtin-sorts.md`, "What the stdlib carries" (WI-934).

## What it therefore does NOT declare

No `fact NonMonotonicStore[SqlStore]`, no `fact QueryableStore[SqlStore]`. A
satisfaction fact may only stand in a closure where the spec's operations are
**backed** (proposal 038), and a fact standing here would certify operations that
die at the call — the unsoundness `check_provider_operations` exists to refuse
(WI-363 / WI-818 / WI-931).

That absence is enforced, not merely observed. Adding the provision back is
refused at load, because a host mapping on a *spec* operation backs the operation
and never a *carrier* (`op_backed`, WI-876 defect A). The refusal is pinned by
`wi931_free_standing_provider_backing_test::reinstating_the_sql_store_provision_is_refused`,
which loads this very file to state its claim about this very carrier.

## Writing the backend

A host that grows a SQL backend copies these declarations into its own closure —
the way `rustland/anthill-stl/anthill/persistence.anthill` does for the two file
backends — and there, beside the `operation_map` that names the host functions,
declares:

```anthill
provides SqlStore language rust
  artifact "…/sql_store.rs"
end

fact NonMonotonicStore[SqlStore]
fact QueryableStore[SqlStore]
```

The `provides` block is what marks the carrier host-realized; the satisfaction
facts are then believed because the operations behind them exist.

## Files

| File | What it is |
|------|------------|
| [`sql.anthill`](sql.anthill) | The shape: `SqlStore`, the `SqlDialect` enum, `QueryBinding`, `ColumnDef` |
| [`demo.anthill`](demo.anthill) | A worked instance — an `audit_db` store and an `audit_binding`, read back by rules |

The binding's SQL rides as `Quoted("sql", …)` terms (kernel spec §4.2): formal in
SQL, opaque to the kernel, meaningful to whatever executes them. That is what makes
the binding writable with no SQL backend in sight, and it is the use case `Quoted`
exists for.

The namespace is `anthill.examples.persistence.sql`, which keeps the `persistence.sql`
tail so the relation to `anthill.persistence` stays legible. It therefore does NOT
transliterate the directory name, unlike `examples/webots-modelling/lf1/` →
`anthill.examples.lf1`.

## Running it

There is none. Unlike `examples/classic-mini/*`, this example declares no
`anthill.cli.Main`, because there is nothing to execute. `sql_store_example_test.rs`
loads both files against the stdlib and **drives** the demo rules through the
resolver, so the shape cannot rot into something that no longer loads or no longer
reads back.

**The two files load in either order** (WI-936), and `sql_store_example_test` drives
both to check it. Until that fix the order was significant and its loss was silent:
`QueryBinding.columns`'s declared `List[T = ColumnDef]` is what desugars the demo's
list literal into a `cons` spine, and with `demo.anthill` converted first the file
still loaded clean while `account_column_type` answered nothing. A declared type is
now in force for the whole load whichever file it is written in (kernel spec §4.6,
"Collection literals").

## Reading further

- `docs/proposals/007-persistence-layer.md` §7 — the dialect/marshalling design
  this sketch came from, and (§ header) why its `queryable` read path predates
  proposal 057's extent model.
- `docs/rust-forward-mapping.md` §2.13, §6.1 — `SqlStore` as the worked example
  of entity → struct and satisfaction fact → `impl Trait for`.
