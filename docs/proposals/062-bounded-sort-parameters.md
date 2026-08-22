# 062: A sort carries a GOAL over its type parameters

**Canonical reference:** [`kernel-language.md` §5.4](../kernel-language.md) (sort type parameters), §8.2 (entity subtyping). **Mechanism:** [`../design/constrained-term-substrate.md`](../design/constrained-term-substrate.md).

## Status: Draft (2026-08-22), from WI-20260822-T70A2. Claims marked MEASURED were reproduced against the Rust loader at `b67def46` with a both-sides control.

## Relates to: WI-502 (the constraint substrate — this is its first `Type`-kind producer), WI-569 / WI-570 / WI-571 / WI-572 (Steps 0–3, delivered), WI-835 / WI-644 (the written-site walk, the eager half), WI-067 (never NAF-decide an under-determined guard), WI-539 / WI-840 (the op-clause `requires` overload this reuses), WI-1110 (the cost of conflating two meanings in one clause), examples/guardians (the consumer).

## The rule

A sort may declare a **goal** over its type parameters. The goal is discharged the way
every other type constraint is: **when the variables it mentions bind**.

```anthill
enum guardians.Text
  sort Trust = ?
  requires is_entity_of(Trust, TrustLevel)
  entity text(raw: String)
end
```

`Text[Public]` loads · `Text[Int64]` is a load error · `Text[?t]` carries the constraint
on `?t`, and refuses at whatever later binds `?t` to a non-level.

**A goal is not per-parameter.** Which parameters it constrains is read off the goal —
whichever it mentions — so one clause may constrain several jointly, and a goal mentioning
none is a constant claim decided once:

```anthill
sort Transfer
  sort From = ?
  sort To   = ?
  requires flows_to(From, To)     -- one goal, two parameters
end
```

This is not a check bolted onto written type applications. A bound is a constraint, and a
constraint set is what typing already is here — which is why the written-site walk (below)
is only the eager special case of a ground argument, not the mechanism.

## Mechanism

A parameter's goal is a constraint on the parameter's variable, discharged when that
variable binds. The substrate is
[`../design/constrained-term-substrate.md`](../design/constrained-term-substrate.md) and
introduces no new constraint kind; the build order, prerequisites and measurements are in
[`../design/062-implementation.md`](../design/062-implementation.md). This proposal owns the
surface and its rules.

## Surface

`requires`, with a **parenthesised** goal — **decided 2026-08-22, not open.** Two
productions exist; only the first changes.

- `requires_declaration` (sort / namespace item) — `requires [binder:] <type>`. Type only, which is why a goal here is a syntax error today.
- `requires_clause` (operation, WI-448) — already `commaSep1(choice(requires_binder, _goal))`.

The overload is therefore not new. WI-840, at that production: an op-scoped `requires` list
is "OVERLOADED — one comma list carries both spec requirements (`requires Eq[T]`) and VALUE
preconditions (`requires neq(b, 0)`, WI-539)". Brackets-vs-parens is likewise already the
loader's meaning discriminator (`load.rs:17163`, WI-618).

**A goal is not a requirement.** The two flavors share a keyword and nothing else: a
bracketed `requires Spec[…]` is an edge in the subtype graph — it makes the sort *refine*
the spec, and so `type_compatible` with it — while a goal claims nothing about the sort at
all. Reading a goal as a requirement would have the typer derive
`Text <: is_entity_of(Trust, TrustLevel)`. Keeping them apart is structural rather than
remembered; how, and what it would otherwise cost, is
[`../design/062-implementation.md`](../design/062-implementation.md) §4.

## Semantics

**A substitution is well-formed only if every constraint it carries is satisfied.** That is
the whole rule. A goal declared on a sort enters the substitution as a constraint when the
sort is instantiated, and from then on it is part of what makes a substitution correct —
not a check run beside one. Proof is **static**: a program that cannot present a well-formed
substitution does not load.

The rest is *when* the goal may be resolved, and what its outcomes mean.

### Readiness — a goal is resolved only once its parameters are CONCRETE

Let `P(G)` be the sort parameters occurring in `G`. **`G` is not resolved at all until every
member of `P(G)` is bound to a CONCRETE type.** Before that the constraint simply suspends; it
is not run and its outcome is not consulted.

*Concrete*, deliberately, and not *ground* — the two come apart on a skolem, and resting the
rule on groundness would make it depend on an implementation accident. See "A skolem is
ground" below.

This is not caution, it is required for correctness, and the reason is measurable. Against
`fact flows_to(Public, Public)` and `fact flows_to(Untrusted, Untrusted)`, the goal
`flows_to(Untrusted, ?to)` — `From` bound, `To` not yet — **answers `?to = Untrusted`**. SLD
treats a free variable existentially, so resolving early does not suspend: it *succeeds*, and
in succeeding it pins `To` to a lattice point the author never wrote. A complete empty search
is the mirror hazard, since ordinary SLD reads it as refutation while an incomplete instance
should be waiting.

Two consequences, both load-bearing:

- **Guard resolution may never bind a sort parameter.** If it could, the guard would be choosing the program's types rather than checking them.
- **Non-parameter variables in `G` are the goal's own locals**, existentially quantified as usual, and may bind freely. Only `P(G)` is protected.

Readiness is therefore decided **structurally**, by what the parameters are bound to, and never
by what resolution happens to answer. That is also what keeps this inside the substrate's stated decidable
fragment — "subsort lattice + instance facts **over ground sorts**"
([`constrained-term-substrate.md`](../design/constrained-term-substrate.md)) — rather than
requiring that invariant to be revised.

A goal with **no** parameters has `P(G)` empty, so it is ready immediately and is decided once,
at load.

**A skolem is ground, and is still not ready.** §5.4 quantifies a variable written in a
parameter type, and WI-1FKR2 makes an operation's body *skolemize* it. Is such a body's goal
ready? Three sources disagree, which is exactly why the criterion must not be groundness:
classical logic says a skolemized formula IS ground, since skolemization replaces variables
with fresh constants; the kernel spec agrees, calling a skolem "the opaque **constant** a
consumer may assume nothing about"; while the implementation's `is_ground` answers no, because
it reports `HasVar` for every `Term::Var` and a skolem is *represented* as a rigid variable.

Only the third reading would have made a groundness gate behave, and it is the one most likely
to be corrected. Were it corrected, a groundness gate would call the body's goal ready, resolve
`is_entity_of(sk, TrustLevel)`, get no solutions, and refuse **every** label-polymorphic
operation body — `bodies_of`, `verdicts_of`, and every signature like them.

So the criterion is CONCRETENESS. A skolem is ground but not concrete: it stands for an
arbitrary type, so no verdict about it is a verdict about the program. Inside that body the
constraint is not-ready and rides as residual, and it can never become ready there — which is
correct rather than a shortfall, since the body must hold for **every** instantiation and the
obligation belongs to the caller that supplies the type.

This also bounds *Outcomes* below: "complete search, no solutions" is refutation only over
CONCRETE parameters. Over a skolem the same empty search means "not provable for an arbitrary
type", which is the caller's obligation and not a refusal.

### Outcomes, once ready

1. **Succeeds** — the binding stands.
2. **Complete search, no solutions** — refuted (readiness guarantees the parameters are concrete, which is what makes an empty search mean refutation here). The binding is rejected: a load error naming the sort, the goal, and the bindings that refuted it. Where the goal is `is_entity_of(P, E)`, the message also lists `E`'s entities, the "what was admissible" the author can act on.
3. **Truncated search, or unlowerable goal** — a load error (WI-628, WI-513). Never read as refutation, and never a vacuous hold.

### Not ready, and never becoming ready

A constraint whose parameters never all bind stays **residual**: it is surfaced with the
answer, which then means "under this constraint". It is never decided by absence (WI-067),
and never quietly dropped or read as discharged. A goal over several parameters is not-ready
until the last of them binds; that is the ordinary case, not an edge one.

### The eager case

A **written ground** argument makes the parameters ground at the point they are written, so
`S[P = X]` is ready there and the refusal lands at that span. That is an earlier discovery of
the same ill-formedness, not a second rule — and it is what makes the common case
(`Text[Int64]` in a signature) a diagnostic the author can read.

## Not in scope

1. **No run-time content** — labels erase; nothing reaches generated code.
2. **No lattice ORDER.** Ordering is already expressible (`fact Covariant(sort, param)` plus a `provides`-chain); this constrains *which* values are admissible, not how they compare.
3. **Rust only** — `scaland` has no typer.
4. **No typed-value carrier.** Runtime monomorphization stays WI-502's, untouched here.
5. **Does not close C7, and is not on guardians' critical path.** MEASURED — the guardians suite passes today with `sort Trust = ?` unbounded, 15/15 including `exfiltrating_agent_is_refused_by_the_label`: the security property rests on a sink demanding a LITERAL label, which an unconstrained parameter does not weaken. Nor would it have closed C7 (a sort mismatch against a variable-containing type passing silently) — C7's laundering ends by binding the label to `Public`, an entity of `TrustLevel`, so the constraint would be SATISFIED and the flow would still go through. C7 was a hole in the FLOW and was fixed separately (`59ac37b7`, RKMD4); this constrains the VOCABULARY. What guardians gains is that `Text[Publik]` becomes an error rather than a fresh type, and that the lattice is a checked claim rather than a convention.

The two gaps an eager-only design would have had — an argument instantiated later through
unification, and a compound argument containing a parameter — are closed by construction:
both are binds, and a bind wakes the constraint.

## Blast radius

Opt-in: a sort with no goal clause attaches no constraint, so `List`, `Option` and every
prelude sort are unaffected. MEASURED, no file writes a goal at a sort item (it does not
parse), and the op-clause production is untouched. The intended sites are guardians' `Text`,
`Message` and `Prompt`, whose `= ?` declarations already carry a comment citing this ticket.

## Decomposition

Build order and prerequisites: [`../design/062-implementation.md`](../design/062-implementation.md) §3.
The language work is the surface (`requires` with a goal at a sort item), its producer, and
the guardians / spec updates. It also includes making the constraint substrate able to
discharge a `Type` guard, which nothing does today — that is scope rather than a
dependency, but it must land before the producer, or the producer enforces nothing.

## Open questions

None outstanding for the language surface. One neighbouring defect is noted under
*Decisions* below and may deserve its own ticket.

## History — spellings refuted

Each is the first thing a reader proposes; each was measured, not argued.

**Marker spec** — `requires IsLevel[T = Trust]`, the ticket's own candidate. Does not bind
today, and a positive reading *would* discriminate: `fact Marked[T = Int64]` is refused
where `[T = Public]` loads. Rejected because the admissible set becomes a hand-maintained
second source of truth — it restates `EntityOf`, and cannot be derived from it. MEASURED,
`rule IsLevel[T = ?x] :- is_entity_of(?x, Level)` supplies no instance, since spec
resolution never reads the SLD path. Add `entity Confidential` and the two descriptions
drift.

**Subtype bound** — `sort Trust <: TrustLevel`. The wrong relation: `types_compatible` is a
union of identity / `is_entity_of` / `refines` / `provides`, and three of those arms raise
exactly the questions this ticket needn't answer. Naming the parameter after the bound
instead fails twice — 13 sorts in the tree have two or more parameters (`Pair[A, B]`,
`Function[A, B]`, …), which would collide on one name under WI-764; and a parameter named
`TrustLevel` shadows the enum inside the body it bounds, since `type_expr_to_child` tests
`is_type_param` first.

**Sort-body `constraint`** — wrong polarity (a denial: a succeeding body is a violation)
and inert. §8.4: plain denials are "stored as reflected structure but **not** registered as
a guard" (WI-882). MEASURED, the body resolves nothing — replacing both names with garbage
loads identically, same 2675 facts. The control is the point: "it loads clean" was never
evidence. That the WI-1034 / WI-1058 "names nothing" refusals do not reach constraint
bodies is a separate defect.

## Decisions recorded (do not re-litigate)

- **The keyword is `requires`** (2026-08-22). Not a new keyword, and not `where`. The overload it asks for already exists one level down: WI-840 states that an op-scoped `requires` list "is OVERLOADED — one comma list carries both spec requirements (`requires Eq[T]`) and VALUE preconditions (`requires neq(b, 0)`, WI-539)". A reader therefore already meets a `requires` whose meaning turns on whether its argument is a type or a goal, and brackets-vs-parens is already the loader's discriminator for that question elsewhere (WI-618). The cost — that a reader must learn the two forms differ — is accepted, and the spec §5.4 text must state it outright rather than leaving it to be inferred.
- **The goal is an ordinary goal — no decidable-subset restriction** (2026-08-22). An earlier draft asked whether to admit only a single atom or a conjunction of them. It buys nothing: logical resolution is well-defined, and the one hazard a restriction would have addressed — a goal that loops — is already handled by bounding rather than forbidding. `max_depth` cuts the search, binds are occurs-checked, and WI-628's truncation flag exists precisely so that "the EAGER `resolve` consumers (the constraint / quantifier guards, which read `is_empty()` / a count as a verdict)" cannot decide from an incomplete search. This discharge is such a consumer, and §Semantics rule 5 already refuses a truncated verdict. A restriction would therefore have duplicated a rule the proposal states while removing expressiveness for nothing. What remains is COST, not legality: the goal is discharged at every bind of the parameter, so an expensive goal is paid repeatedly — the author's choice, and measurable.

  This does not conflict with §Semantics' readiness gate. That gate restricts *when* a goal runs, never its SHAPE — any goal is legal, and none is resolved before its parameters are ground.
- **The goal is a reflect relation** (2026-08-22), not a Rust-side index. It joins the sort-relation family in `anthill.reflect`, one fact per clause — the `SortRequiresInfo` shape, and a separate entity for the reason `ProvidesConditionInfo` already records (a parameter may carry several goals, and a field would have to hold a list):

  ```anthill
  -- SortGoalInfo: ONE goal declared on a sort. Emitted per `requires <goal>`
  -- clause. Deliberately NOT SortRequiresInfo — a goal is not a requirement,
  -- and that relation feeds `refines` / `type_compatible` (see §Surface).
  entity SortGoalInfo(
    sort_ref : Term,   -- the sort the clause is written on
    goal     : Term    -- the goal, as written
  )
  ```

  **No `param` field.** Which parameters a goal constrains is derivable from the goal — the variables occurring in it — and a field would have forced every goal to be about exactly one, making `requires flows_to(From, To)` inexpressible. Two fields also keeps it the shape of its neighbour `SortRequiresInfo(sort_ref, spec)`.

  Visible rather than internal because the layer that most needs it is anthill's own. Guardians' premise is that a model *generates* the agent and the kernel checks it — "the checker tells the generator what to fix" — and a generator that can query this relation asks what `Trust` admits **before** generating, instead of emitting `Text[Publik]` and being refused after. The same rows also feed the diagnostic's "what was admissible" list, which would otherwise be recomputed Rust-side.
- **A `requires` goal is PROVED while loading** (2026-08-22), not merely recorded. An obligation has three fates that look alike in the source — proved at load, carried to run time, or recorded and never checked — and this one takes the first: a substitution carrying a refuted constraint is ill-formed, and a program that cannot present a well-formed substitution does not load. This matches what `requires` already does over VALUES (WI-539: `needy(5)` discharges `neq(b, 0)` by substitution, `if neq(b, 0) then needy(b)` by the branch context, and an unestablished call is refused).

  It does **not** match C2 of `examples/guardians/docs/design/measured.md`, where an operation's `requires flows_to(?l, Public)` over a TYPE-level variable loads clean and gates nothing — "proof obligations tied to an `Implementation` fact, not a static call-site check". That is read here as a defect of the same class this proposal exists to remove — an obligation that reads as a guarantee and is not one — rather than as a precedent to follow. Filing it is a separate ticket.
