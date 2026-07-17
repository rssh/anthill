# Ancestor

The transitive closure of a parent relation — **the** classic recursive logic
program, and the smallest one that cannot be written without recursion at all.

## The problem

Five `parent` facts describe a family:

```
orville
└── abe
    └── homer
        ├── bart
        ├── lisa
        └── maggie
```

Who descends from whom? The facts only relate a child to their *immediate*
parent. Nothing in them mentions bart and orville in the same breath — that pair
has to be derived, three links deep.

## The encoding

Two clauses, and the second one is the entire algorithm:

```anthill
rule ancestor(?child, ?elder)
  :- parent(of: ?child, is: ?elder)

rule ancestor(?child, ?elder)
  :- parent(of: ?child, is: ?parent), ancestor(?parent, ?elder)
```

An ancestor is a parent, **or** a parent's ancestor. That is the whole definition
— it is what "ancestor" *means*, transcribed. There is no traversal, no visited
set, no queue, no depth parameter: `ancestor` calls itself and SLD resolution
follows the chain as far as the facts go.

Compare this to the same closure in a procedural language, where the recursion is
real work you have to write — and get right — and where the *query direction* is
baked into the code. Here one rule answers all of them, because a rule is a
relation and not a function:

```anthill
ancestor                     -- every ancestor pair (both columns free)
ancestor("bart")             -- bart's ancestors (first column bound)
ancestor("bart", "orville")  -- is orville an ancestor of bart? (both bound)
```

Cited by name, `ancestor` is a `Relation` over its two free head parameters
(proposal 052). **Applying it binds a column and narrows the schema** (§8.3):
`ancestor("bart")` is a `Relation[String]` of elders; with both columns bound it
is a membership question, `Relation[Unit]`.

## Running it

```bash
cd rustland && cargo build -p anthill-cli
./rustland/target/debug/anthill run examples/classic-mini/ancestor/
```

Prints `12`, `3`, `1`.

## Why 12

Each person's ancestors are everyone above them in the chain:

| Child | Ancestors | Count |
|-------|-----------|-------|
| bart | homer, abe, orville | 3 |
| lisa | homer, abe, orville | 3 |
| maggie | homer, abe, orville | 3 |
| homer | abe, orville | 2 |
| abe | orville | 1 |

Twelve pairs, from five facts. The base clause alone yields exactly the five
`parent` edges — so the other **seven** rows are the recursion's doing, and a
build that silently dropped the recursive clause would print `5`.

Then `3` is bart's ancestors, and `1` is the single derivation of
`ancestor("bart", "orville")`.

## What this example is really testing

That a **recursive rule can be cited by name as a relation value** — which, until
WI-714's schema-synthesis fix, it could not be. This example was written, found
to be blocked, and deliberately withheld from the collection rather than shipped
with a workaround.

The failure was in typing, not in the search: recursive rules always *resolved*
fine as subgoals; it was only the relation face that could not type them. A clause
types a head parameter where a body goal constrains it — an operation parameter,
an entity field. A **rule** subgoal constrains nothing. So in the recursive clause
here, `?elder`'s only occurrence is inside `ancestor(?parent, ?elder)` — the
rule's own self-reference — and it came out untyped. The cross-clause lub then saw
`String` from the base clause and *nothing* from the recursive one, read that
absence as a rival type, and rejected the column as disjoint:

```
error: type mismatch in ancestor.rule (rule): expected a common column type
across relation clauses, got disjoint types for column `elder`
```

The fix is that an unconstrained column contributes nothing to the lub: the column
takes its type from the clause that knows. That is the fixpoint answer, and it
needs no assume-then-check iteration precisely *because* a self-reference
contributes nothing to begin with. A genuine conflict — two clauses both typing a
column concretely, at `String` and `Int64` — is still a loud load error.

The bisection that found it is worth keeping: a single-clause rule cited by name
worked, a multi-clause non-recursive rule worked, and only the recursive one
failed. It was the recursion, not the clause count and not the lub in general.
