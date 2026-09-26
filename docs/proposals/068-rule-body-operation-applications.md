# 068: An operation application in a rule body is a computation — typed as in an operation body, evaluated by value

## Status: Draft (2026-09-26). Decided in discussion while reviewing WI-20260827-XBHX3; the term "functional fragment", the flex/rigid/concrete reading of the dictionary, and the SUSPENDED/UNREDUCED split (§2) are the user's. Decided in review: a value is what evaluation produces (§1); `===` reduces its operands (§5); an application that can never reduce is UNREDUCED, not suspended, and is never retried (§2); `<=>` still binds, and a bound application keeps its mark (§1); an operation call in a fact head is a pattern (§5); a comparison takes the state of its operands — SUSPENDED gives SUSPENDED, UNREDUCED gives UNREDUCED, and UNREDUCED wins (§2.2); the rule depends on no library sort's interpretation (§2.3). Nothing is implemented. The implementation design will be `docs/design/068-implementation.md`, written after this is reviewed.

## Relates to: kernel-language §5.3 ("A rule body evaluates both a goal and a value slot"), §8.3 (`=` "reduces both operands"; `<=>`), §5.4 (bare names); [049](049-equality-and-unification.md) (`<=>`), [051](051-structural-vs-semantic-equality.md) (semantic `=`), [058](058-modular-instances.md) (dictionaries), [060](060-clause-level-requirements-and-typed-heads.md) (clause-level requirements); `docs/design/abstract-interpreter-and-rules.md` §3.3 (the WI-580 unfold).

## Tracked by: WI-20260926-ACG10 (first step: review this proposal). It would absorb WI-20260827-XBHX3 and WI-20260924-35E14 (both depend on it) and give WI-20260923-KCNA0, WI-20260908-FJG8B and WI-20260909-M8QWJ their loud side (§2). No library sort is a dependency (§2.3).

## The problem

The language already says what an operation application in a rule body is. §8.3: `=` "reduces
both operands". §5.3: "A rule body evaluates both a goal and a value slot". An operation and an
entity constructor are distinct declarations, so — unlike Prolog, where `1+2` is legitimately a
term — `C.tag(red())` is a computation and `box(v: 1)` is data.

The implementation does not hold to it once the call is NESTED. MEASURED on `main` at `fa32695e`,
with `C.tag` a bodied `match` operation (`tag(red()) = 1`) and `String.contains` host-mapped.
`(total, definite)`:

| goal | answer | truth |
|---|---|---|
| `String.contains("abc", "b") = true` | (1, 1) | 1 |
| `bb(v: String.contains("abc", "b")) = bb(v: true)` | **(0, 0)** | 1 |
| `box(v: C.tag(red())) = box(v: 1)` | **(0, 0)** | 1 |
| `?v <=> box(v: C.tag(red()))` | (1, 1), and `?v`'s field `v` is **the call `tag(red())`** | `?v = box(v: 1)` |
| `?v <=> box(v: C.tag(red())), ?v = box(v: 1)` | **(0, 0)** | 1 |
| `box(v: ?n) <=> box(v: C.tag(red())), ?n = 1` | (1, 1) | 1 |

The first two rows differ only in depth; the last two differ only in how the same equations are
spelled. The refutations are DEFINITE, so `not(...)` over any of them proves a falsehood.

The same happens where the operation has NO implementation at all, as an abstract spec legitimately
may. `Set.empty` / `insert` / `union` / `intersection` / `difference` have no body, no host mapping
and no provider; with sets written as `insert`/`empty` chains:

| goal | answer | truth |
|---|---|---|
| `insert(insert(empty(),1),2) = insert(insert(empty(),2),1)` | (1, 1) | 1 |
| `intersection({1,2}, {2}) = {2}` | **(0, 0)** | 1 |
| `not(intersection({1,2}, {2}) = {2})` | **(1, 1)** — NAF proves a falsehood | 0 |
| `union({1}, {2}) = {1, 2}` | **(0, 0)** | 1 |

The missing implementation is not the defect. The refutation comes from comparing the unevaluated
`intersection(…)` term as data; under §2 that application is UNREDUCED, the comparison is UNREDUCED,
and the answer is undecided rather than false.

The WI-580 unfold (`unfold_eq_operand`) shows the same thing from its side, with the gate that
declines it whenever the other operand carries a bodied call (WI-20260827-XBHX3):

| goal | gate on | gate off |
|---|---|---|
| `C.bpick(?c) = box(v: C.tag(red()))` | (1, 0) | (1, 1) `?c = red` — the true answer |
| `C.pick(?c) = C.mk(red())` (custom `Eq`, WI-20260827-P1TPE) | (1, 0) | **(0, 0)** — a wrong refutation |
| `append(?a, [3]) = append(?b, [4])` | (1, 0), 0.3 ms | (32, 0), 14 ms — the recursion no longer terminates against OTHER |

A third symptom is a call that is not evaluated read as a FAILURE (WI-20260924-35E14). With `Colour`
providing `Score` (`score`: red 1, green 2, blue 3):

| goal | answer | truth |
|---|---|---|
| `rule early(?x) :- domain_member(?x, Colour), Score.score(?x, 3)` | `blue` | `blue` |
| `rule late(x: Colour) :- Score.score(x, 3)` | **no solutions** | `blue` |
| `rule unbound(?r) :- Score.score(?v, ?r)` | **no solutions** | a conditional answer |

`Score.score(x, 3)` is the functional-relation view `f(args, ?r)`. With `x` unbound the bridge declines,
and the WI-938 hook "falls through to ordinary candidate selection instead, which is the pre-WI-938
behaviour (no answer)"; no clause is written for `score/2`, so the goal fails — no residual, no
warning. The typed head's generator is appended after the body (060 §2.2), so in `late` the call runs
before `x` is bound and never runs again. Under §2 the call is SUSPENDED with blocker `x`: it rotates,
is asked again once `x` is bound, and answers `blue`; in `unbound` it stays suspended and ends as a
conditional answer carrying the call. The bridge declines for three reasons — an unbound argument, no
supplier, a supplier tie — and today all three collapse into that one fall-through; under §2 the first
is SUSPENDED and the other two UNREDUCED.

**The cause is that a rule body is an untyped term.** An operation body is checked by the
bidirectional typer (`check_operation_bodies`): every call gets an inferred type and a `CallClass`
stamp, and eval runs it strictly, arguments first. A rule body gets `type_rule_bodies`: variable
types are collected, a few goal-position shapes are handed to the typer, and a DATA slot is only
name-checked (`data_functor_error`, WI-1058). So nothing records "this node is a call"; the resolver
re-decides it from the VALUE at run time, separately in each consumer, and each consumer reduces
to a different depth:

| consumer | how deep it reduces |
|---|---|
| `eq` / `cmp` / `arith` (`reduce_operand`) | the top of each operand |
| `<=>` (`unify_values`) | every level it recurses into — but a BIND stores the interior unreduced (`unify_bind`) |
| the WI-580 unfold | nothing: it reads OTHER unreduced, hence the gate |

## 1. The rule

**An operation application written in a rule body denotes its VALUE, at any depth — including
under an entity constructor, a tuple, or a collection literal — exactly as it does in an operation
body.** It is evaluated strictly, arguments first, by the evaluator that runs operation bodies,
with the same dispatch, dictionaries and effect rules.

**A value is what evaluation produces** — no other notion is needed. An entity application and a
literal evaluate to themselves; an operation application is replaced by its result. An application
that has not been evaluated is not a value: it is SUSPENDED or UNREDUCED (§2), and it is never
compared as data.

**`<=>` still binds** (decided in review) — it is how a value gets bound, and `let ?v = e` is its
sugar. It evaluates its operand where it can and binds the value; where it cannot, it binds the
variable to the application ITSELF, which keeps its SUSPENDED / UNREDUCED mark. A consumer that later
needs the value evaluates it then, or waits on its blockers; none compares it as data. An ANSWER whose
binding still holds a suspended application is conditional, not definite. The harm that "never bind"
would have guarded against is the one the WI-938 hook met — `?r` bound to the call and reported as a
definite answer — and that is a harm of treating the application as DATA, which the mark prevents; it
is not a harm of binding.

**Inside a quote nothing is evaluated.** A quoted expression is a term — any value — and is not a
fragment. `as_term(e)` is not a quote: it reflects the VALUE of `e`, which §1 evaluates first; the
quote bracket that holds an application unevaluated is WI-189's `↑e` / `quote(e)`.

The unit is a **functional fragment**: a maximal subtree of a rule body rooted at an operation
application or a binder form (`lambda` / `let` / `match`). The walk that finds fragments descends
through goal connectives, predicate atoms, entity constructors and tuples, and never types those.
In `C.bpick(?c) = box(v: C.tag(red()))` the fragments are `C.bpick(?c)` and `C.tag(red())`;
`box(…)` is data.

With the rule, every row in the first table answers its truth column, and the answer to
`?v <=> box(v: C.tag(red()))` binds `box(v: 1)`.

## 2. When an application does not reduce: SUSPENDED or UNREDUCED

An application that was not evaluated is in one of two states. They are close — neither is a value,
neither is compared — but they are not the same, and treating them as one costs both diagnosis and
time (§2.2).

- **SUSPENDED** — it cannot be evaluated YET. An argument it needs is an unbound variable, or its
  dictionary is a flex `?d` that a later goal may bind. It carries its **blockers**: those variables.
  Evaluating it again makes sense only after one of them is bound.
- **UNREDUCED** — it can never be evaluated. No implementation is reachable for it: no body, no host
  mapping, no provider supplies it. It has no blockers, so nothing it could wait for exists, and it
  is never re-evaluated.

### 2.1 The dictionary decides which

| dictionary | meaning | the application |
|---|---|---|
| **flex** — an unbound `?d` | a goal in this derivation may still bind it (a later `find_dictionary`, a clause condition) | **SUSPENDED**, with `?d` among its blockers |
| **rigid** — no instance is chosen and none will be | no implementation is reachable | **UNREDUCED** |
| **concrete** — bound to a provider | the implementation is known | is **called**; a provider that lacks the member is a **loud error** |

A rule's dictionary slot that nothing binds is not made rigid by generalizing the rule over it: a
rule's variables are opened fresh at every use, so such a slot is flex. And a CONCRETE carrier with
no provider — KCNA0's `Desc.tag()` at `Blue`, which provides nothing — is a load error, not an
abstract instance.

### 2.2 What each state does

**SUSPENDED** rotates behind its siblings, as a delayed goal does today. On its turn, if none of its
blockers has been bound since it suspended, it is skipped WITHOUT being evaluated again; it
residualizes, as today, when only waiting goals remain.

Today there is no such check. `delay_goal` (`resolve.rs`) moves a delayed goal to the back and counts
consecutive delays; every time a sibling makes progress the count resets and the goal is evaluated
again from scratch — a reduction that can include a bridge run, and `run_in_bridge_interp` builds a
fresh interpreter and registers the builtins on every call. The blockers are what make the retry
cheap: the evaluator suspends BECAUSE it needed a particular variable, and names it.

**UNREDUCED** is never retried.

- **At load, it is an ERROR at a CALL SITE whose implementation the typer can decide is
  unreachable** — the site, not the declaration: declaring a spec operation that providers are meant
  to implement is legal, and a HEAD or an equation's side is a pattern, not a call. Three cases,
  each decided without a run-time value:
  1. the operation has no implementation of ANY kind — no body, no host mapping, no `@[simp]`
     defining equation, no relational rules — and is not a spec operation, so no provider could
     supply it (FJG8B / M8QWJ). Decided by the operation alone;
  2. a spec operation called at a carrier the typer resolves to a CONCRETE sort, which provides no
     instance supplying the member (KCNA0's `Desc.tag()` at `Blue`);
  3. a spec operation called at the spec ITSELF, which nothing provides.
- **At run time otherwise** — where the carrier depends on something the typer does not fix: a
  type variable of the rule (opened fresh at each use, so the dictionary is flex and the call is
  SUSPENDED first), a variable whose type nothing determines (the WI-282 exemption), a projection
  grounded only by the call's arguments (KCNA0's q1), an untyped carrier (§6). Once the dictionary
  turns concrete and no provider supplies the member, the call is UNREDUCED: it is evaluated ONCE
  and PARKED on the frame with its cause. It stays behind its siblings — a sibling may still FAIL
  and refute the clause, and a refutation must win over an undecided answer — but it is never asked
  again, and it joins the residual as a NAMED cause (KCNA0's acceptance) or a fault.

The resolver already separates the two ANSWERS — `BuiltinResult::Delay` is "a PROMISE: re-ask me",
`BuiltinResult::Unknown` is "an ANSWER: … nothing will ever instantiate it" — but schedules them
alike: an `Unknown` "costs the same rotations a `Delay` does". What the rotation needs is the goal's
PLACE behind its siblings, not its re-evaluation, so parking serves `Unknown` too.

**A comparison takes the state of its operands** (decided in review). `=` / `neq`, `===`, `cmp`,
`arith`, and `<=>` where it must compare rather than bind: an operand that is SUSPENDED makes the
comparison SUSPENDED, carrying the operand's blockers; an operand that is UNREDUCED makes it
UNREDUCED. Where both occur, UNREDUCED wins — no binding can make the comparison decidable. No
consumer compares either kind as data, and none dispatches to a carrier's `eq` over one: dispatch
reads the operand's value, and there is none yet.

**Marks.** A state that does not depend on the derivation may be marked on the NODE: "no
implementation is reachable at this call" is a property of the call site when its carrier is
static, so the typer can mark the fragment (and refuse it at load). What depends on the derivation —
the blockers, which are variables of this derivation — is recorded on the frame's goal entry, never
on the occurrence: occurrences are `Rc`-shared across derivations and branches, so a σ-dependent
mark on one would leak into another.

### 2.3 Library code is not part of the rule

The rule is stated without reference to any library sort, and no library sort's interpretation is
an input to it (decided in review). An abstract spec whose operations have no implementation is
legitimate: its applications are UNREDUCED, and a comparison over one is UNREDUCED, never false.

One consequence is stated so it is not discovered: `Set`'s equality works today by comparing
unevaluated `insert` / `empty` terms — its `eq` / `contains` / `subset` rules match them in their
heads — so those comparisons (the five `wi616_semantic_eq_test` rows WI-1057 measured) become
UNREDUCED. Giving `Set` an implementation is a library choice, not a condition of the rule. Step 1
(§8) lists every such piece of library code.

## 3. Rule-body operation applications are typed as in an operation body

Each functional fragment is typed by the operation-body typer (`type_check_node_at`), in an
environment carrying the rule's variable types (as `type_rule_bodies` already installs for a dot).
This answers the three reasons WI-1058 recorded for not typing a data slot, because those reasons
were about typing DATA nodes, and a fragment is not one:

1. **Lost expectation.** A fragment's root call synthesizes its type from its signature, and its
   arguments get their expectations from the parameters — as in an operation body. The slot's own
   declared type (WI-20260904-50B2K's `declared` list) is the fragment's expectation where there
   is one.
2. **Lost scope.** Binder forms are fragments themselves, so nothing is typed outside its binder.
3. **Rewriting.** The rewrite came from `@[simp]` firing inside the typer. Fragments are typed with
   simp OFF (the op-body entry, `type_check_node_gated_in_gamma`, already takes `simp_enabled`), so
   the only rewrites are dispatch rewrites (dot → `Apply`, a spec-op pin), which the rule walk
   already stores. `@[simp]` keeps firing at resolve time under `ResolveConfig { simplify }`.

**Consequence: new load errors.** A rule whose fragment is ill-typed — `?x = box(v: String.length(3))`
— loads today and is refused. Dispatch (pins, supplier ties, refusals) is decided at load for every
rule-body call, not only for spec-op calls (WI-1026 / WI-1043). A variable whose type nothing
determines (the WI-282 exemption) leaves its fragment partially typed; such a call keeps a
value-directed dispatch at run time.

Typing assigns types and dispatch classification. It does not decide call-versus-data and reduces
nothing: whether an application reduces is §2's question — answered at load where the typer can see
it (UNREDUCED as an error), and at run time otherwise.

## 4. Evaluate, suspend, narrow — or unreduced

At run time a fragment has four outcomes:

- **evaluate** — what it needs is known: it runs through the operation-body evaluator (the SLD→eval
  bridge) and is replaced by its value;
- **suspend** — it needs an unbound variable or a flex dictionary: SUSPENDED with its blockers (§2.2);
- **narrow** — its evaluation stops on a `match` whose scrutinee is an unbound variable: the resolver
  may case-split one alternative per arm (design §3.3, "abstract-interpretation-on-suspend"), which
  is how `append(?a, [3]) = [1, 3]` solves `?a = [1]`;
- **unreduced** — no implementation is reachable: parked, never retried (§2.2).

The rule is that every consumer (`=`, `<=>`, `===`, `cmp`, `arith`, the relational views, the unfold)
sees the same outcome for the same fragment. Narrowing keeps its existing soundness gates (disjoint
arms; the P1TPE residual check).

## 5. What does not change

- Rule and fact HEADS are patterns: `rule contains(insert(?, ?y), ?x)` matches the term. That holds
  for an operation call in a fact head too — `fact p(C.tag(red()))` is a pattern, not evaluated
  (decided in review).
- `=` never binds; `<=>` is structural and never dispatches — its operands are now values.
- `===` compares the VALUES of its operands, as it already does at the top of an operand: "never
  dispatches" is about the comparison, not the operands — `eq_operands` reduces both sides, and
  `struct_eq(dbl(2), 4)` succeeds (the `BuiltinTag::Eq` doc, measured under WI-20260910-FDPJ8).
  §1 extends that to every depth, so `box(v: C.tag(red())) === box(v: 1)` holds, where today it
  answers 0. Decided in review (2026-09-26): the operands are reduced.
- The goal-position READINGS of §5.3: a `Bool` operation as a condition, `f(args, ?r)`. What changes is
  their behaviour on a call that is not evaluated, which follows §2 — SUSPENDED rotates and is asked
  again, UNREDUCED is parked — instead of falling through to an empty answer (WI-20260924-35E14).
- Effects: an effectful operation is still declined by the bridge's empty effect registry (§5.3),
  and whether `Error` alone may run (WI-20260827-NFXPZ) stays open.

## 6. Carriers that are not typed

A query given to `anthill query`, a pattern built by `query_pattern_term`, and a goal built at run
time (an `or` branch bound through a head match, a σ-rebuilt `Entity`) carry no typing. They must
answer as the typed path does — one rule answering differently by how it reached the resolver is
the class WI-20260910-FDPJ8 and WI-20260906-7YPGM repaired. So the value-directed decision stays,
as the fallback for these carriers, and is held to the same outcomes.

## 7. Open questions

1. **Cost.** The bridge builds a fresh interpreter per call today; evaluating per fragment makes
   fewer calls. To be measured, not assumed.

## 8. Implementation — a sketch; `docs/design/068-implementation.md` owns it

1. **Measure first, change nothing:** type every fragment stamp-only with simp off; count the reports
   across the corpus; check the stamps land on the stored occurrences; and list the library code that
   relies on comparing an unevaluated application as data (§2.3), each to be tracked on its own.
2. **One walker, one evaluator:** a tree walker owning only the logical actions (walk data, apply σ,
   evaluate / suspend / narrow / park per fragment), delegating every computation to the interpreter.
   The interpreter learns to CARRY a logic variable in bridge mode and to raise `Suspended` only where
   a value is needed, NAMING the variable — so the ground gate moves from "all arguments ground before
   the call" to "the value is needed", and a suspension carries its blockers. The frame's goal entry
   records the blockers, and an UNREDUCED goal is parked rather than rotated for re-evaluation.
3. **Retire the per-consumer reductions:** `reduce_op_value`'s call-by-name fold and
   `body_specialize`'s reducer become the walker's; XBHX3's gate goes with the unfold reading OTHER as
   fragments.
4. **The unfold threads dictionaries** as clause conditions (as WI-20260925-P7VP4 does for rule-body
   calls) instead of declining every operation with `requires`.

Rust only: scaland has no typer. The spec edits (§8.3's evaluation paragraph, §5.3's "what the gate
still declines", §8.1's rule-body typing sentence) land with step 2, not before.
