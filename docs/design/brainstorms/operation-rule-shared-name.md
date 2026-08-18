# Operation and relational rules sharing one symbol

**Status:** Brainstorm (2026-08-15)
**Origin:** Proposal 052 / WI-939 discussion
**Related:** [Proposal 052](../../proposals/052-rules-as-stream-valued-operations.md),
[abstract interpretation and rules](../abstract-interpreter-and-rules.md) (WI-580),
[proposal 059](../../proposals/059-secondary-entries.md)

This document explores a possible language design. It does **not** specify accepted syntax or current
kernel behavior. Proposal 052 retains only the open question until the choices at the end of this note
are made concrete and implementable.

## Candidate under exploration — operation and relational rules share one symbol

There is a coherent stronger answer to that residue: when one symbol denotes both an operation and
predicate clauses, let the **ordinary expression spelling always denote the operation**. Evaluation and
code generation therefore call / emit the operation; the mere existence of clauses never changes an
expression call into a relation value. Reaching the clause set is explicit; the initial placeholder was
a helper such as `relation(name)`, now narrowed to the `relation(Symbol)` candidate below. This is position-directed
in the same sense as §6.6's `not`: the ordinary value position is operational, while the explicit
relation position is relational.

The governing principle is: **the operation defines the relation; written same-name rules prove
properties of that operation**. The operation body is the single executable definition. Its Bool view or
arity+1 graph is derived mechanically as the implicit bridge below. A user-written rule does not add a
second definition or extend the set of permitted results; it contributes a theorem / narrowing lemma
whose conclusion must agree with the operation-defined relation.

The relational face would contain the written clauses plus an **operation bridge**. For a Bool-returning
operation at its declared arity the bridge has the semantic shape

```anthill
-- schematic only; this is NOT a source-level recursive clause
rule valid(?x) :- ground(?x), operation_call(valid, ?x) = true
```

For a non-Bool operation its graph remains the existing arity+1 shape:

```anthill
rule f(?x, ?result) :- ground(?x), unify(operation_call(f, ?x), ?result)
```

For several operation parameters the guard covers the **input tuple** —
`ground((?x1, ..., ?xn))` — and deliberately excludes the result column, which the bridge is meant to
bind. `ground` has its existing rule-body meaning: succeed when every input is deeply ground; otherwise
DELAY/rotate, never fail. The guard is therefore retryable after another goal binds an input.

`operation_call` above is a phase-qualified internal node: it bypasses relational lookup and enters
operation dispatch directly. Writing the bridge as `valid(?x) :- valid(?x)` would instead be ordinary
SLD recursion and is therefore not an implementation of this design. The same separation is needed in
generated code, where the operational call must not accidentally compile as a call back into the
relation wrapper.

The bridge is three-valued. A ground, runnable operation produces success/failure (Bool) or binds the
result (the graph view). If the operation cannot yet reduce because an input needed for dispatch or its
body is unground, it **DELAYS and leaves the bridge goal residual**; a later goal may ground the input and
the bridge can be retried. `DELAY` does *not* mean “some written clause may apply”, and it is not an extra
solution. Written clauses are independently searched and may produce answers even while the bridge is
delayed.

Operationally the resolver may search written clauses alongside the bridge, but semantically this is not
a union of two definitions. An unchecked clause could duplicate an operational answer or, worse, assert
an answer for which the operation returns false / a different result. The shared-name form therefore
chooses the **laws/refinements** contract:
**coherence is required; its obligation is generated automatically, while its discharge may require
evidence**. The author does not restate a separate coherence theorem: for every same-name rule the
checker derives the obligation from the rule and operation. For a bodied operation, WI-580's abstract
interpretation supplies the operational / proof view. It is not an optional lint. A program may record
the generated obligation while its proof is pending, but `check` / compilation may not accept the
combined face until it is discharged through the ordinary proof machinery.

**Coherence means that the written rules are valid properties of the operation**, not that those rules
define the operation completely. Three names keep the argument non-circular:

```text
W_f = answers derived from user-written clauses only
O_f = the operational graph: eval(f(a)) terminates with r
G_f = the public relation exposed by relation(f) = W_f union O_f
```

The generated bridge adds `O_f` to `G_f`; it is **not a clause of `W_f`**. In particular, the bridge is
excluded from the clause index / proof context used to establish coherence. If it were admitted there,
`W_f(a, r) :- eval(f(a)) = r` could prove itself and the check would measure nothing.

The generated bridge makes the *public* relation extensionally equal to the operation's graph. For a
pure operation `f : A -> R`, that resulting consumer contract is

```text
forall ground a, r:  G_f(a, r)  <=>  eval(f(a)) terminates with r
```

For a Bool-returning operation `p : A -> Bool`, the result column collapses and the obligation is

```text
forall ground a:  G_p(a)  <=>  eval(p(a)) terminates with true
```

Here `eval` is deliberately a **semantic judgment**, not a commitment to one representation. A proof
implementation may treat it as a **meta-language judgment**, invoking Anthill's evaluator / compiler
semantics directly, or may reify that semantics as an Anthill relation and prove against a
**self-interpretation in the KB**. The coherence contract is the same in either realization; 052 does
not require the kernel's operational semantics to be encoded in the KB before the shared-name design can
be specified. A self-interpreted `eval` becomes necessary only if proofs must inspect evaluation itself
(steps, divergence, effects, or errors), rather than merely establish its result.

Errors, effects and divergence require a separate observational-equivalence policy; this candidate is
therefore initially restricted to pure operations for which the bridge has the terminating / delayed
reading above. `DELAY` over an unground call is not a counterexample: the equivalence is claimed at
ground observations, while written rules may narrow symbolically on the way to such an observation.

The generated operation bridge proves `O_f ⊆ G_f` by construction. The only possible contradictory
claims are introduced by `W_f`, so the checker generates, for each written clause `head :- body`, the
obligation `body -> operational_meaning(head)`. The right-hand side is obtained by WI-580's on-demand
specialization when the operation has a body, or from the registered semantic theory when it is a
builtin / host operation; it is not a second, hand-maintained rule definition. Collected over the clauses
this is `W_f ⊆ O_f`, stated against the written clauses alone:

```text
forall ground a, r:  W_f(a, r) -> eval(f(a)) terminates with r
forall ground a:     W_p(a)    -> eval(p(a)) terminates with true
```

This is precisely the “no contradiction” property. For a deterministic operation, if a written rule
answers `W_f(a, r_bad)` while evaluation returns `r_good`, the obligation requires
`r_bad = r_good` and fails otherwise. For Bool, a written proof of `W_p(a)` is contradictory when
evaluation returns `false`, so its obligation fails. There is no need for a separate consistency axiom:
agreement with the operational graph rules out every contradictory written answer. If operations later
become nondeterministic, `O_f` must itself be a set of permitted results and the same subset statement
still applies.

The arrow here is intentionally **one-way**. It does not say that the written rules cover every result
of the operation. A rule such as `large(?x) :- huge(?x)` proves only the property
`huge(x) -> eval(large(x)) = true`; it need not enumerate every `x` for which `large(x)` evaluates true.
The too-strong obligation would be `O_f ⊆ W_f` (completeness), or `W_f = O_f`; neither is required of
the written rules. For a total deterministic operation the same consistency condition can equivalently
be written negatively:

```text
not exists ground a, r: W_f(a, r) and eval(f(a)) terminates with r_other and r != r_other
not exists ground a:    W_p(a)    and eval(p(a)) terminates with false
```

The positive subset form is preferred because it is the theorem each clause naturally proves with SLD
and induction; the negative form makes the “no contradiction” reading explicit.

The first formulas use `G_f` / `G_p` because they state the **public semantic contract** consumers get
after the bridge is added, not a completeness requirement on the written rules.
The second formulas use `W_f` / `W_p` because they state the **minimal proof obligation** the checker
generates from each written rule. Algebraically, once `G_f = W_f ∪ O_f`, the generated bridge gives
`O_f ⊆ G_f` and the proof gives `W_f ⊆ O_f`; therefore `G_f = O_f`. Using `G_f` in the proof
obligation would allow the generated bridge into the proof and obscure which inclusion is actually being
checked.

This is an automatically generated normal theorem obligation, **not necessarily an automatically proved
one**. Its evidence has three sources:

- **bodied operation:** WI-580 makes the body available to proof as derived defining equations / one-step
  abstract interpretation. SLD handles direct cases; recursive rules use the existing induction proof
  construct, with the recursive call's coherence statement as the induction hypothesis;
- **builtin / host operation:** there is no Anthill body for WI-580 to inspect. The obligation must be
  discharged against a registered semantic theory or certified backend model (for example the SMT
  integer theory for `Int` operations), or against already discharged theorems that specify the builtin.
  Merely executing a finite collection of examples is testing, not a proof;
- **complex case:** when automatic SLD / induction / theory reasoning is inconclusive, the author supplies
  an induction strategy, auxiliary lemmas, or another proof witness through the existing proof construct.

The generated obligation is still the single statement of what coherence means; user evidence proves
that statement rather than restating it. If no accepted evidence source can discharge it, the combined
operation/rule face is refused. Because the bridge supplies the converse inclusion, discharge of all
generated clause obligations establishes the full extensional equivalence above.

That proof settles **which values** the relation denotes, but not how often the stream yields one. 052
currently preserves resolver proof multiplicity, so a ground answer derivable both from a written clause
and from the bridge can still appear twice. The shared-name form must either specify set semantics /
deduplication for this union, or suppress the bridge where a written proof produced the same ground row;
coherence alone cannot make two proof paths into one stream element.

For comparison, the alternatives this proof-backed choice rejects are:

- **override:** clauses are tried first and the bridge is only a fallback. This avoids duplicates but
  makes search order observable and lets the relational meaning differ from ordinary evaluation;
- **open union:** clauses genuinely extend the relation beyond the operation. This is internally
  consistent, but then the two faces intentionally do not denote the same mathematical function and
  should not be presented as one definition.

Until the required proof gate and a multiplicity decision exist, the proposal retains today's louder
invariant: a bodied operation and defining clauses in its graph slot are refused, and only the derived
Bool / arity+1 relational view is available.

This candidate is also separate from WI-939's short-name collision. WI-939 concerned a namespace
predicate and a *different*, sort-member operation sharing a short name; proposal 059 R4 clause 3 now
refuses that capture at declaration. Here the rule head resolves to the **same operation symbol**, so it
is a question about two faces of one symbol, not arity-based selection between two declarations. The
existing legal case of a **body-less** operation defined by clauses already has that identity; the
candidate would relax the current refusal for a **bodied** operation plus clauses and therefore would
replace, not merely clarify, the “one operation, one definition” rule in kernel §8.6 and
`check_operation_body_and_clauses`.

## Current candidate — `relation(f)` macro over a name occurrence

Do not add a keyword or a third declaration/entity. There are exactly two semantic entities sharing one
source name:

```text
operation f
relation f = written rules of f + the implicit operation-backed rule
```

The surface remains an ordinary-looking call:

```anthill
f(a)                 -- invoke / compile operation f
relation(f)           -- obtain the rule-defined Relation named f
relation(S.f)         -- the qualified form
```

But `relation` does **not** receive a runtime `reflect.Symbol` or `Function` value. It is a compile-time
macro using the delivered 043.1 occurrence machinery. The macro receives the argument as a
`NodeOccurrence`, reads its `Expr`, and accepts exactly a bare name occurrence (unqualified or
qualified). It then resolves that occurrence through the ordinary name ladder and builds the occurrence
that denotes the existing relation. A call `relation(f(a))`, a lambda, a local function value, and every
other expression shape are rejected at the argument's span.

In 043.1's current two-stage macro mechanism, an occurrence macro runs as the RHS head of a fired
`[simp]` lowering, as `where -> guarded_of` already does. The implementable shape is therefore
schematically:

```anthill
operation relation(target) -> Relation                   -- surface redex; target intentionally untyped
rule relation(?name) <=> relation_of(?name) [simp]       -- compile-time lowering
operation relation_of(name: NodeOccurrence) -> NodeOccurrence
```

The surface result is deliberately the bare sort `Relation`: its `T` / `E` parameters are open only for
the transient redex. `relation_of` inspects the name occurrence, resolves it, computes its rule schema,
and returns a synthesized Relation occurrence; the existing 043.1 expansion path immediately re-types
that occurrence to the concrete `Relation[T, E]`. The surface result therefore never survives as an
erased runtime relation. The `target` slot is deliberately untyped: ordinary argument typing must not
pretend that the name is a runtime `Symbol` or require all operation names to conform to one `Function`
shape. The macro is the one reader of its syntax and rejects every non-name occurrence. This is the same
two-stage compile-time route as `Relation.guarded_of`, not a new macro facility.

`relation(f)` does not manufacture an additional operational-graph relation. It returns the one relation
defined by `f`'s rules; the operation-backed bridge is a member of that relation. The `O_f`, `W_f` and
`G_f` notation above names semantic subsets used in the coherence argument, not three KB entities.

This avoids the unresolved question of converting a source name to a runtime `Symbol`. It also avoids
using a `Function` parameter: although a bare operation can eta-lift to an arrow-typed `OpRef` in a
function-typed slot (WI-275/WI-1083), that route would wrongly appear to accept lambdas and other function
values, loses the rule-head schema at the signature, and is unnecessarily restrictive for builtins. The
macro needs the written name occurrence and its resolved referent, not an evaluated callable.

For a rule such as

```anthill
rule parent(?child: Person, ?parent: Person)
```

`relation_of` synthesizes an occurrence typed
`Relation[(child: Person, parent: Person)]`, reusing 052's existing rule-citation schema synthesis. The
macro's returned occurrence is re-typed by the existing 043.1 expansion path, so consumers see the
concrete schema rather than an erased `Relation`.

This candidate adds **no callable-Relation convention**. In particular,
`relation(parent)(child: alice)` is not proposed. Bind columns through the existing relation algebra:

```anthill
relation(parent).fix(child: alice)
relation(parent).where(lambda row -> condition(row))
relation(parent).takeN(10)
```

**A name with no written rules is a compile-time error.** `relation(f)` selects the relation defined by
written predicate clauses; it does not create a relation from an operation-only symbol. After resolving
the name, `relation_of` requires at least one predicate clause indexed under that symbol. If none exists,
the macro rejects at the argument occurrence with a diagnostic such as `` `f` has an operation but no
written relation rules ``. An unknown name keeps the ordinary unresolved-name diagnostic, and an
equation-only name is not a predicate relation. This is a macro **rejection**, never a declined expansion
that leaves a bare `Relation` redex to reach runtime.

## Current candidate — name meaning by position

Rule/goal position already supplies the relational call syntax; it needs no `relation_call` helper. For
an operation and relation sharing `f`, the meanings are:

| position | spelling | meaning |
|---|---|---|
| expression call | `f(x)` | invoke / emit operation `f` |
| bare expression | `f` | operation as a function value (eta/`OpRef`) |
| first-class relation expression | `relation(f)` | the rule-defined `Relation` value |
| rule head | `rule f(?x) :- ...` | contribute a written clause to relation `f` |
| rule-body goal | `... :- f(?x)` | call relation `f` (written clauses plus bridge) |
| internal bridge | `ground(?x), operation_call(f, ?x)` | once inputs are ground, enter operation dispatch directly; never relational lookup |

Semantically the relation contains an implicit clause:

```anthill
-- schematic internal rule, not source syntax
rule f(?x, ?result) :- ground(?x), unify(operation_call(f, ?x), ?result)
```

with the Bool same-arity variant using the same input-ground guard and testing the operation result
against `true`. Therefore a rule-body `f(?x)` searches the relation. It may answer through a written
narrowing/property clause, or through the implicit operation clause once every operation input is ground.
Until then `ground` DELAYs and rotates the bridge so another goal may bind the inputs. This explicit gate
also prevents `unify` from binding the result to an unreduced operation-call term. The phase-qualified
`operation_call` is load-bearing: spelling its body as `f(?x)` would call the relation again and recurse.

This is intentionally position-directed, following existing Anthill practice: a rule body is logical
syntax, while an operation body / ordinary expression is value syntax. `relation(f)` is needed only to
carry the logical relation into value syntax as a first-class `Relation`/`LogicalStream`; it is not needed
for one relation to call another inside SLD.

For qualification, `relation(S.f)`'s macro argument must be recognized as a qualified-name occurrence,
whereas an ordinary value receiver `x.f()` remains operation/dot dispatch. Both resolve through the normal
name ladder appropriate to their position; neither chooses by arity or by load order.

## Decisions required before promotion into proposal 052

A concrete proposal must settle all of the following, with grammar, typing and evaluation rules rather
than schematic helper names:

1. **Surface syntax — candidate selected:** `relation(f)` / `relation(S.f)`, lowered through a `[simp]`
   rule to an occurrence macro that accepts only a bare/qualified name `NodeOccurrence`. The surface is
   `operation relation(target) -> Relation`: an untyped syntax-bearing slot and a transient bare
   `Relation`, replaced and concretely re-typed by the macro. **A resolved name with no written predicate
   clauses is rejected at compile time at the name occurrence**; operation-only and equation-only symbols
   are not relation values. No keyword, runtime `Symbol`/`String` conversion, direct applied form, or
   callable-`Relation` feature is proposed.
2. **Name and position resolution — candidate selected:** expression calls and bare function values name
   the operation; rule heads contribute relation clauses; rule-body goals call the relation; only the
   internal bridge uses phase-qualified `operation_call`; `relation(f)` reflects the relation into value
   syntax. Confirm the qualified-name occurrence used by `relation(S.f)` and pin the same table in
   codegen tests. No position chooses by arity or load order.
3. **Bridge representation — partly decided:** guard the tuple of operation inputs with rule-body
   `ground`, then use phase-qualified `operation_call` and unify its reduced value with the unguarded
   result column. `ground` DELAYs/rotates until retryable and prevents binding an unreduced call term.
   Define the typed internal `operation_call` form and how requirements/provider dictionaries cross it.
4. **Delay and errors:** the exact result for unground dispatch, underdetermined bodies, missing backing,
   errors, effects and divergence. The initial restriction to pure operations must be either adopted or
   replaced with observational semantics.
5. **Rule role:** which same-name clauses are lemmas/properties and which graph-shaped clauses remain
   forbidden as competing definitions; how this classification works for Bool operations where the
   lemma and derived view have the same arity.
6. **Coherence gate:** the generated theorem statement, the proof context that excludes the bridge,
   accepted evidence for bodied operations (WI-580), builtins/host operations, and complex induction,
   and which commands refuse a pending or failed obligation.
7. **Multiplicity and order:** whether written lemma paths are executable answers at all; if so, whether
   the public relation is set-valued/deduplicated or proof-multiplicity-preserving, and how bridge versus
   lemma search order is observed.
8. **Compatibility:** the exact change to kernel §8.6 and `check_operation_body_and_clauses`, plus driven
   controls for bodyless relational definitions, builtin lemmas, the WI-580 derived view, and the
   proposal-059 short-name-capture refusal.

Only after these decisions are closed should a condensed normative section return to proposal 052.
