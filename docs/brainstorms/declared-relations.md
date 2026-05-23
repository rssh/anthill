# Declared relations, closed rulesets, and constrained variables

## Status: Brainstorming draft (2026-05-23)

Captured from a design session. **Not yet a proposal.** It records the thinking,
the decisions, and the open questions, so they can be distilled into proposals
later. The full vision here is a **long path**; the actionable near-term start is
in *Incremental foundation* below, and that is what we intend to do now.

## Relates to

- **044** (unified name resolution) — extend to rule-predicate heads.
- **032** (symmetric rule arrows) — rule labels.
- **043** (`[simp]`) — simp params, macros over expressions, `min_sort`.
- **014** (union types) — the `T | LogVar[T]` route.
- **015** (`?` universal type variables) — implicit type params.
- **017** (field access / dot projection) — `l.T` is its type-level analog.
- **042** (explicit type params on operations); **010** (query system); **026.1**
  (value-integrated KB queries) — the value↔resolution bridge.
- **WI-246** — rule body atoms as `NodeOccurrence` (delivered; see *Grounding*).
- **011 / 022** + `docs/proposals/typing_pass_spec.anthill` — the typing relation
  (`synth`/`check`/`wf_type`), the first customer.
- `LogicalStream` (`stdlib/anthill/prelude/logical_stream.anthill`) — the logic
  monad (`splitFirst`/`empty`/`pure`/`mplus`), the relation-result carrier.
- `min_sort` / `singleton` precision spectrum (`typing.rs:5474`; `Type` enum in
  `stdlib/anthill/prelude/sort.anthill`).

## Incremental foundation — what to do *now*

The vision (declared closed relations + typed many-sorted signatures + `LogVar`
across value/type/projection + ceremony-less `LogicalStream`-returning calls) is
a long path. To formalize the **typing relation today**, use less-advanced
methods on existing machinery:

- Express `synth` / `check` / `wf_type` (and reuse `type_compatible` /
  `is_entity_of` / `refines`) as **plain rules** — untyped params, no relation
  declarations, no closure enforcement.
- **Co-locate** them in `anthill.reflect.typing` (the namespace that already owns
  `type_compatible`). This sidesteps the cross-namespace import gap *entirely* —
  no declared-relations feature needed (see *Diagnosis*).
- Run as **compile-time SLD resolution** (the typer *is* resolution); use the
  existing query system (010 / 026.1) for any value-side extraction.
- Keep **PART II** (the operational `type_check` in the spec) as the *reference
  algorithm*; the plain co-located rules are the *declarative spec* it must agree
  with.
- **Defer**: typed signatures, closure *enforcement*, `LogVar`, ceremony-less
  calls, generics, path-dependence. Closedness stays a *conceptual* property of
  the typing relation for now, not a checked one.

Net: a working declarative typing relation today, on machinery that already
exists, while the `LogVar` / declared-relations vision matures separately and the
typing relation later upgrades onto it.

---

## Origin: the typing spec needs cross-namespace predicate reference

We are turning typing into a declarative, bidirectional **relation** (`synth` ⇒ /
`check` ⇐ / `wf_type`) that Rust and Scala *comply with* and that translates to
Isabelle/Lean/Coq — PART I of `typing_pass_spec.anthill`. That relation must
reference `type_compatible`, in `anthill.reflect.typing`; from a sibling
namespace, `import anthill.reflect.typing.{type_compatible}` **fails to load**.
Pulling that thread produced everything below.

## Diagnosis: predicates are import-private, though resolvable elsewhere

- Rules **have names**: `Rule.label: Option<Name>` (`ir.rs:304`) plus the head
  functor. `rule_id_by_qn` (`mod.rs:1706`) resolves label-first, then `by_functor`.
- But `process_imports` (`load.rs:930`) only consults `by_qualified_name` + scope
  — never `rules_by_label` / `by_functor`. `is_entity_of` imports only because it
  is a registered *builtin*; `type_compatible` is a pure rule head, invisible to
  `import`.
- `export` does not help — 044 made names visible-by-default, so it is a no-op
  (`load.rs:505`).
- **The asymmetry**: at *resolution* time predicates are global-by-functor; at
  *load* time they are namespace-scoped and rule heads are never surfaced to
  `import`. The name resolves everywhere except the import path — a plumbing gap,
  not a missing identity.

## Decisions

1. **FQN access reuses the operation mechanism** — register predicate heads into
   the operation symbol structure; the existing import + qualified-reference
   resolution then applies unchanged. Not a parallel label path.
2. **Two handles**: **label → one arm** (proof citation/substitution,
   `rules_by_label`; already 032); **FQ head → the ruleset** (`by_functor`).
   Reflective surface: ruleset-by-head = a `RuleInfo`, the predicate peer of
   `OperationInfo` (not exposed today).
3. **Relations are closed.** Declaring a relation freezes its clause set; closure
   point = **namespace-complete**. Appending an arm from another namespace is an
   error. Undeclared predicates/facts stay **open** and accreting.
4. **Closed logic over open data.** A closed relation stays *behavior-extensible*
   via the open fact-predicates it queries: `type_compatible`'s clauses are
   frozen, but two read `EntityInfo`/`SortRequiresInfo` *facts*. Users extend
   subtyping by adding **entities** (open facts), never **clauses**. This is
   exactly `Σ ⊢ e : τ` — a closed inductive over an open Σ — and what makes it
   Lean-emittable.
5. **A relation is a distinct kind — NOT "operation without a return."** No-return
   operations already exist and are **procedures** (`set(target,v) -> Unit effects
   Modify[T]`). Discriminator = definition + semantics, not the return: *function*
   (expr-body, computed, returns a value); *procedure* (expr-body, computed,
   effects, no meaningful return); *relation* (rule-defined, resolved, pure,
   nondeterministic). "Same name *access* as operations" was the real claim.

## Deeper substrate: typed signatures → constrained variables

A typed relation has a **many-sorted signature** —
`relation synth(ctx: Context, e: ExprOccurrence, t: Type, eff: List[Type])` —
which maps directly to a Lean index list (`inductive Synth : Context → Expr → Ty →
Prop`). Reaching it surfaced five interlocking requirements; four bottom out in
one primitive.

1. **No type declarations on rule params today** (rule heads bare). Syntactic
   prerequisite.
2. **A `[simp]` param `(x: Tp)` must admit three fillers** — a **Tp-value**, an
   **expression typed Tp**, or an **unfilled var** — because simp rules are macros
   over expressions. So `Tp` is a constraint *"slot sort ≤ Tp"*, satisfiable three
   ways: the `min_sort`/`singleton` spectrum (value … typed occurrence … unbound).
3. **Typed logical variables ⇒ constrained variables ⇒ CLP.** A var must hold its
   sort, but vars can themselves *be* types, so you need a **constrained variable**
   = var + limitations. A constrained var is at once a **generator** (enumerate
   inhabitants) and a **checker** (test). Lean: a **reified constraint term**
   (constraint-as-data; composes; constraint store first-class) over a `Var`
   variant. Not from scratch — generalizes the resolver's existing delay/rotation
   ("delay until the constraint is decidable").
4. **The dual folds in.** Operation-in-goal (`f(x,r)`) and relation-in-expression
   (`if type_compatible(a,b)` → provability/Bool) reconcile under *functions ⊂
   relations + position-driven coercion*; and `f(x,r)` is just `r` *constrained to
   f's graph at x* — the functional-predicate convention **is** a constrained var.
5. **No-return ≠ relation** — see Decision 5.

### Grounding in the current implementation

- **WI-246 delivered** (earlier belief it was open was stale): rule **body** atoms
  are `NodeOccurrence`s — `body_nodes` (`mod.rs:638`, via `rule_body_nodes()`),
  "the typer/`simp` view." `NodeOccurrence` carries `inferred_type` — the sort slot.
- But **present, not driven**: `materialize_from_handle` is a read-only walk; the
  typer does not run over rule occurrences (`inferred_type` stays `None`), and the
  rule **head is still a bare `head: TermId`** (`mod.rs:109`) — no head slot.
- So typed signatures are gated on (a) a head slot, (b) driving the typer over rule
  occurrences + checking against the signature, plus (c) constrained variables —
  *not* a from-scratch typed rule term. The **fact** case (empty body) is what
  forces head-side typing (nothing flows up from a body).

## `LogVar` as a universal open-slot primitive

`LogVar[T]` (a *typed* logical variable; none exists yet) turns out to be the same
primitive at three levels:

- **value level** — `LogVar[T]`: an open value slot (relation arguments).
- **type level** — a **type parameter is `LogVar[Sort]`.** This *is* the
  "`f(x,y):R` ≡ `f[T1,T2](x:T1,y:T2):R`" idea: omitting a param's type mints a
  fresh **type-level LogVar**; implicit generics = fresh `LogVar[Sort]`. (Realizes
  the earlier "logical variables can *be* types"; cf. 015's `?`.)
- **projection** — `head(l: List): l.T` reads the **type-level LogVar bound in
  `l`'s type** (`l : List[T = ?E]` ⇒ `l.T = ?E`). Path-dependent return types =
  projecting a LogVar binding out of a value's type — the type-level analog of 017.
  Value-dependent but path-dependent (a type member), not full Π → decidable.

**Ceremony-less call** — passing either `T` or `LogVar[T]` at a slot. Options:
or-types `T | LogVar[T]` (014); implicit conversion `T → LogVar[T]`; a typeclass
both satisfy (anthill `requires`). **Cleanest: subtyping `T <: LogVar[T]`** — a
value *is* a fully-bound logical variable, so it passes by plain subsumption; you
write `LogVar[T]` only to leave a slot open. (Same precision spectrum: ground
value … open `LogVar[T]`.)

So the foundational layer is *bigger* than "constrained vars for rule signatures":
**a typed logical variable manifest as value-slots (relations), type-slots
(generics), and projections (path-dependence), with a value as the ground case.**
Relations, generics, and dependent-ish returns fall out of one primitive — strong
evidence the primitive is real, and also why it is a long path.

## Runtime regimes & the value bridge

Split by **where the logical variables live**:

- **Resolution context** (logical vars exist): **solve** — unbound slots are
  outputs; you get bindings, possibly many. The generator / constrained-var world.
  *The typer lives here* — `synth`/`check` run at compile/load time, so producing
  a type via an unbound `?T` is a compile-time activity; the result is materialized
  into the ground `type_of` fact (the cache).
- **Value runtime** (no logical vars in any sort — every value is ground): a
  relation can only **check** (ground args → succeed/fail) — *unless* it is invoked
  as a streaming call (next bullet).

**A relation returns `LogicalStream[naming-pairs]`** — calling it *is* the query,
so the explicit `kb.query(...)` ceremony disappears. Each solution is a named tuple
over the output positions (handles multi-output: `synth ⇒ (t: Type, eff: …)`).
This is the real **functions ⊂ relations** unification: an operation is the special
case — one output, a stream guaranteed `pure` (singleton), collapsed to a bare
value. One calling syntax spans both. Consume via `splitFirst`; `LogVar[T]` is the
*ground value* that marks an open slot at the call (the actual logical variable is
allocated *inside* the relation's resolution and is gone by the time a stream
element surfaces — so the value runtime never holds a free logical var).

**Engine-backed realization.** Producing the stream *is* resolution, so a relation
realized in a host language requires the **embedded anthill engine** — the existing
`codegen bundle` / `rust+anthill` interpreter profile ("embeds the spec and
dispatches via the interpreter at runtime"). The line:
- pure operation → native host function, no engine;
- relation → dispatches into the embedded resolver; `LogicalStream` realizes to a
  host lazy stream;
- pure-codegen targets (C++/Rust forward maps, no resolver) get pure ops, and
  *maybe* ground decision-checks of a closed relation, but not the solve/stream.

The **typer is unaffected** — it runs in the toolchain's engine at compile time,
so the engine is always present; "is the engine embedded?" only bites for *user*
relations called at host runtime.

## What "no solution" means

The closed/open decision pays off a *third* time (after Lean-emittability and
encapsulation): **the meaning of failure.**

- **closed** relation → no solution = **definitely false** (sound negation; the
  ruleset is complete).
- **open** relation → no solution = **not derivable yet** (NAF / non-monotonic).

For the typer this *is* the "sometimes we have no type" question from the start:
`synth(ctx, e, ?T, ?E)` with no solution = `e` is **ill-typed**, and it is
*closedness* that makes that a definite type error rather than "not derived yet."
Sharp contrast: the **closed `synth`** — empty = type error; the **open `type_of`
cache** — empty = "not memoized," *not* an error. Same "no solution," opposite
meaning. That is *why* `type_of` must stay an open fact-predicate.

**Cardinality** maps onto `LogicalStream`: `empty` = no solution, `pure` = one
(the principal type), longer = nondeterministic. A relation used as a typer carries
a hidden obligation — **functional in its output mode** (0-or-1, never many; "many"
= ambiguous / non-principal typing). Error *reporting* lives in the `0` case
("no solution; here is the subgoal that failed"). Check-mode is the easy case;
synth-mode is where determinism is owed.

## Provisional proposal structure

- **Now (no new feature)** — the typing relation as plain, co-located rules in
  `anthill.reflect.typing` (see *Incremental foundation*).
- **Foundational (later)** — **constrained / typed logical variables** (`LogVar`):
  value-slots, type-slots (generics), projections; reified constraint term;
  extends delay; subsumes the three-filler simp slot, `T <: LogVar[T]`, function
  calls.
- **On top (later) — 045: Declared, closed relations** — typed signatures (because
  head vars are constrained vars), FQN access via the operation mechanism (extends
  044), closed rulesets (namespace-complete), `RuleInfo` reflection,
  `LogicalStream`-returning calls, engine-backed realization.

## Open questions

- Reified constraint term: shape; interaction with the discrimination tree and
  unification.
- How much CLP initially — generators, or sort-membership checking first?
- `T <: LogVar[T]` subsumption coherence; how much of generics / path-dependence to
  pull in vs. defer.
- Closure enforcement mechanics at namespace-complete; cross-file accumulation.
- Where relation-in-expression Bool-coercion lives (NAF / provability).
- Bootstrapping: the typing relation's signature uses meta-sorts (`Context`,
  `Type`) defined before it runs — stratifies, but spell out.
- Overlap with **023** (KB guards) and **033** (resolver primitives / disjunction):
  constraint checking touches both — reuse vs. new machinery?

## Build order

1. **[now]** typing relation as plain co-located rules in `anthill.reflect.typing`;
   keep PART II as the reference algorithm.
2. Typed rule params (grammar + IR: `(x: Tp)` on heads).
3. Constrained logical variables (`LogVar`; reified constraint term + delay).
4. Head occurrence slot + drive the typer over rule occurrences; check against
   signatures.
5. Predicate-head FQN registration (extend 044).
6. Closure enforcement (namespace-complete).
7. Declared closed relations (045); `LogicalStream`-returning calls; re-express the
   typing relations with signatures. Generics / path-dependence as the same
   primitive extended.
