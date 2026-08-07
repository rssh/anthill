# The requirement channel — a dictionary is a term, a requirement is a goal

## Status

Design — origin 2026-08-07. **Owns** the SLD side of the requirement channel.
**Supersedes** [`requirement-dictionaries.md`](./requirement-dictionaries.md) §3.3's
Γ-slot substrate and the "a rule has no caller" premise it rests on (§1). §3.2's
*semantics* — the guard **is** the dictionary-resolution — is retained unchanged.
**Staging invariant settled** (2026-08-07 review): run time performs no typing
operations — §2.1, and §4 is reworded on it.
**Surface owned by proposal 060** (`docs/proposals/060-clause-level-requirements-and-typed-heads.md`):
the generated-body-goal rule, the three spellings, position restriction, the anchor
rule — including its second anchor, WI-742's typed relational head (`?x: T` →
`domain(?x, T)`), which grounds a `require[Spec[T]]` with no witness call.

**One representation delivered** (WI-1045): §9 is no longer a rule to apply but a
state of the code — there is one dictionary carrier, one constructor, and no
conversion at a crossing.
**Consumers:** WI-1037; **WI-070** (`Branch` effect) and **WI-069** (`Suspension`
snapshot/resume) — jointly 027.2's eval↔SLD switch.

---

## 1. The correction

`requirement-dictionaries.md:676` and `kb/typing.rs:40023` both assert *"a rule has
no caller."* False. A rule has three: a parent rule body's goal (a resolver `Frame`
push), a top-level query (the only caller-less one), and an **eval frame** via
`prove_rule_predicate_value` (`eval/eval.rs:2266`) — which holds `frame.requirements`
and drops them at the crossing (`resolve.rs:4788`).

What is missing is a **channel**, not a caller. Two facts got compressed into one
falsehood: the resolver `Frame` has no requirement field, *and* a goal's carrier may
be unbound at open time. The second justifies a **delayable** resolution; it does not
justify the absence of a channel.

---

## 2. The model

> **A dictionary is a term. `find_dictionary` is an ordinary relation. The binding is σ.**

A dictionary is an impl symbol and its sub-dictionaries. There is no closure in it,
no host handle, no second store: **a dictionary is exactly a first-order term**
`Dictionary(sub₀ … subₙ₋₁, impl: S)`, and since WI-1045 that is not a *view* of it
but what it IS — an ordinary `Value::Entity` carried identically by σ, by
`eval::Frame::requirements` and by `Closure::requirements`
(`eval/dictionary.rs`).

Three consequences, and they are the whole design:

- **Matchable is not a property to add.** It unifies, fingerprints and indexes in the
  discrimination tree today, because a symbol tree is all it ever is. A dictionary
  that *couldn't* be matched is not constructible.
- **No new carrier.** σ binds `VarId → Value` (`kb/subst.rs:60`) and
  `Value::Requirement` is a `Value` (`eval/value.rs:127`). Binding a logical variable
  to a dictionary is representable today.
- **No runtime environment, no frame field, no arena move.** The clause's requirement
  scope is eliminated by a typing-time rule transformation; what survives to run time
  is goals and arguments. See §5.

### 2.1 Staging invariant — run time performs no typing operations

**After the typing pass, run time performs no typing operations** — no inference, no
type unification, no instance selection. Selection happens in the typing pass (the
delta-resolving over rule bodies); what survives to run time is reading a value's
**carried type** (`value_type_term`, WI-578 — a stored term, read whole, never
collapsed to its head symbol) and selecting from the tables built at load. The complete runtime kernel is six
operations over **already-resolved** dictionaries:

| op | what it does |
|---|---|
| **fetch** | read the carrier's carried type, select from the load-built `provides`/sort-ops tables (the head constructor picks the entry; the type arguments flow to the sub-fetches) |
| **bind** | put the fetched dictionary in σ (`?d`) |
| **copy** | the §6 crossings — install a σ-value into `frame.requirements`, or hand an eval frame's dictionaries to a proved goal |
| **project** | `sub(d, i)` on a resolved dictionary |
| **compose** | conditional provisions: assemble a parent from its prebuilt impl + sub-dictionaries fetched by the components' carried types |
| **check** | structurally unify a supplied dictionary against the locally fetched one (§4) |

None of these is a typing operation. Three consequences:

- **`X` is a typing-time object only.** Run time never sees the spec term `Eq[T]`;
  it executes a compiled dispatch record (§5). "X ground" was never the operative
  condition — **whether the carried type is readable** is (§4).
- **A runtime tie is unreachable, not refused.** Overlap between provider heads is
  decided at typing/load (the 058 coherence machinery); if run time ever finds two
  table entries for one carried type, that is a loud defect, not a semantics.
- **No runtime sub-search over `provides`** — a table fetch cannot truncate, so the
  WI-628 truncation discipline does not apply here.

One existing deviation to reconcile: `resolve_bridge_requirements`
(`typing.rs:14667`) runs `unify_types` at dispatch time. The declared side is
static, so the same projection-path compilation applies there; until it is
applied, the bridge is the one grandfathered exception — say so at the site
(§10).

---

## 3. Surface — an interpreted term

**No grammar change.** `require[X]` already parses in a rule body (see the note
below), and so does `requires(X)`. What is added is an **interpretation**:

> `require[X]` **brings the dictionary for `X` into the clause's environment**, where
> body calls that need a dictionary can be passed it.

```anthill
p(?x, ?y) :- requires(Eq[T]), eq(?x, ?y)          -- today. Checks only
p(?x, ?y) :- require[Eq[T]], eq(?x, ?y)           -- new. In scope for the clause;
                                                  --      eq dispatches through it
p(?x, ?y) :- ?d = require[Eq[T]], f(?x, ?d)       -- named, when the author wants
                                                  --      to pass it by hand
```

The bare goal is the ordinary form and the named one is the same thing with a handle
on it — 058 §3.4's anonymous-vs-named distinction, read in a clause. "In the
environment" is a **scope** statement, not a storage one; §5 says what it is made of.

Three spellings, three distinct things, no overload: `requires <T>` **declares** a
slot (sort/op level, `grammar.js:584`, untouched); `require[X]` **denotes** a
dictionary in term position; `anthill.kernel.find_dictionary` (`kb/load.rs:2345`) is
the **kernel relation** both lower to — the one WI-300's `requires(X)` already
desugars into, gaining an output argument.

Two surface rules the interpretation adds. **Position is restricted**: `require[X]`
is legal as a bare body goal or as the RHS of a top-level `=` (the two forms
above); nested deeper in a term (`f(require[Eq[T]], ?y)`) it is refused loudly —
no general lifting. And **the name's home is the CONVERTER**, not the kernel
vocabulary: both legal spellings are rewritten away at convert, so a kernel-vocab
entry would be reached only by an *illegal* one — where it would turn a loud error
into a name that resolves to nothing and then fails silently. `require` is matched
by name and shape exactly as `requires`, `unify` and `eq` are.

**It rides machinery that exists.** The resolver already *reduces operands* before an
`=`/`cmp` decides: `reduce_dot_value` and `reduce_op_value` (`resolve.rs:6043`,
`:6101`) evaluate a term-valued operand and **delay** when it cannot be reduced
(`is_unreduced_op_call`, the WI-483 leave-uninterpreted rule). An interpreted
`require[…]` operand is one more arm there — and it is the *same function* WI-1037 is
about, so the two land in one place rather than two.

**The bracket is where instances are already named.** 058 §3.3's selection surface is
`f[Spec = W](…)`, and WI-840's named slot makes `SortedSet[T = String, O = ByLength]`
a type. Naming a spec instance in brackets is what brackets already mean; `require[X]`
is that channel read for its value rather than for its selection.

> **The bracket form is INTERPRETED, not disallowed.** An earlier draft of this
> document rejected `require[X]` on the claim that `Name[…]` is the parameterized-type
> channel and could never arrive as a goal atom. **That was wrong.** WI-311's
> `application` is the *unified* type/term application — it absorbed the old
> `instantiation_term`, the converter classifies type-vs-term **by position**
> (`convert.rs:2312` builds functor + pos_args + named_args), and the grammar path
> `application ∈ _non_name_atom_term ∈ _atom_term ∈ _term ∈ _goal ∈ rule_body` is
> open. `require[X]` parses in a rule body today. What it needs is a **meaning**.

`requires` as a **declaration** keyword (`grammar.js:584`) is untouched at sort and
operation level; nothing here changes 058 §3.4's named slots.

**058 §3.10 compliance — and why the bracket does not breach it.** §3.10 permits a
first-class dictionary *value* to fill an **anonymous** slot but never a named one:
*"a named slot is a type parameter, and a value cannot determine a type."* The
bracket in `require[X]` sits on the **input** side — it names the spec instance being
asked for, which is exactly what 058 §3.3's `f[Spec = W](…)` already does. The
**output** `?d` is an ordinary logical variable in term position, not a type
parameter: a rule has no type identity for it to be part of, and it is not
addressable in any type. So no dictionary value ever fills a named slot, and 058
§3.4's named slots on sorts and operations are untouched. **Do not read the bracket as
making `?d` a type parameter** — that is the one misreading this spelling invites.

---

## 4. Semantics — determined, never chosen

`find_dictionary` is a **function, never a generator** (058 §3.10). Selection is
**decided at typing time**: the pass narrows candidates by **one-way match** — only
provider variables may bind; a match that would instantiate a query variable is not
a match (the WI-824 σ-gate, generalized). Groundness of X was never the operative
condition — the provider need only be **the same for every instantiation of what is
still unknown**. `Eq[Pair[Int64, ?B]]` commits to the Pair provider (forced, not
chosen) and recurses into its conditions; that is exactly how §9's partial
dictionaries arise.

At run time the goal executes its compiled record (§2.1, §5):

| state at the read | outcome |
|---|---|
| `?d` unbound, carried types readable, unique entry | **fetch, compose, bind** |
| `?d` unbound, carried types readable, no entry | **fail** — no instantiation can resolve (sound: a well-typed use would carry the instance) |
| `?d` unbound, a carried type unreadable (witness value unbound) | **delay** — re-fires when the witness value binds |
| two entries for one carried type | **defect** — loud; overlap was typing/load's to refuse (§2.1) |
| `?d` **bound** | **check** against the locally fetched entry (below; the caller-supplied case, §6) |

The delay row replaces `FindDictOutcome::Suspend` (`typing.rs:37635`) with the
general mechanism, and its wake condition is now trivial: the compiled record
**mentions the witness value variables**, so binding them re-fires the goal through
ordinary delay/rotation. The bound row is the new capability — today's guard has no
such mode because there was no way to have one.

**Check — WI-860's rule: two derivations of one relation must agree.** When the
local entry is **unique**, a supplied `?d` must **unify** with it — disagreement is a
loud error, never a precedence win for either side. A supplied dictionary may
*legitimately* differ only where the local derivation cannot decide
(`Unresolvable`/`Ambiguous`, WI-855 — e.g. a WI-843 named-instance selection
`f[Spec = W]` made statically upstream): there, supplied decides. §6's "supplying
beats re-deriving only where re-derivation cannot decide" is this rule derived,
not stipulated. (WI-1040's acceptance (c) is corrected accordingly: a differing
supplied dictionary *passes* only on an undecidable row; on a unique row it must
fail loudly.)

---

## 5. The environment is eliminated during typing

Formalize §3's "environment" as a **rule transformation at typing time**, after which
it does not exist at run time at all. For each rule body:

1. each `require[X]` goal → `find_dictionary(X, ?d)` with a **fresh** `?d` (the
   author's own variable when written `?d = require[X]`);
2. each body call covered by `X` → the same call carrying `?d` in its requirements
   channel;
3. attribution — which call is covered by which `require` — is **WI-613's σ-class
   matcher** (`find_requires_slot` / `find_requires_location`), reused wholesale.

**What step 1 emits is a COMPILED DISPATCH RECORD, not a type term.** Per §2.1, run
time never sees `Eq[T]`. The emitted goal extends the delivered guard encoding
(`find_dictionary(spec_base, op, witness_args…)`,
`record_find_dictionary_grounding`, `typing.rs:40046`) with the output slot `?d`.
Because the goal mentions the witness **value** variables, delay wakes on their
binding with no new machinery. The encoding, settled (2026-08-07):

- **`out` is a presence-optional NAMED arg** — the delivered resolver arm reads
  only positionals (`builtin_find_dictionary`, `resolve.rs:5088`), so a no-`out`
  goal takes the existing path untouched and acceptance (f) holds *structurally*.
  `out` is present iff the dictionary is actually threaded (a covered call, or
  author-named); absent = check-only = skip composition.
- **One form, one owner** (the WI-900 rule): the sweep always emits the extended
  form; the guard encoding is not a second shape — `requires(X)` *is* the no-`out`
  case. No persistence migration exists: the rewritten form is an in-memory
  contract between sweep and resolver arm (rule bodies re-elaborate from source
  every load); the idempotence gate stays arity-based (1 pos arg = unrewritten).
- **The record stores almost nothing.** The candidate entries are the KB's
  `provides`/sort-ops tables — precompiled at load, shared, selected by carried
  type; the per-goal narrowing of §4 is a coherence *check*, not payload.
  Carrier/projection indices derive at fire time from `(spec, op)` via
  `OperationInfo`/`simp_guard_holds_core` — reads, not typing operations. **No new
  node kind.**
- **The full spec rides in a TYPE-POSITION channel, never general scope
  resolution.** `rewrite_requires_goal` (`convert.rs:2799`) strips type-args
  precisely because a bare `T` as a term argument would hit scope resolution with
  no binding in a free rule; un-stripping must route the decoration where a bare
  name is legitimately a type Var (WI-849). Which concrete channel is §10 item 1.

**The anchor rule.** The record is compiled from an **anchor** that grounds the
spec's params: a covered body call (the witness — the guard tier's existing
requirement) or a typed pattern binding (`?x: T` — WI-582 on equational heads;
WI-742 extends it to relational heads, where the annotation compiles to a
`domain(?x, T)` goal whose carried-type read is exactly the projection source —
proposal 060 §3). `?d = require[Eq[T]]` with neither — no body call covered by
`Eq`, no typed binding of `T` — has nothing to compile a projection path from and
is **refused at typing** (the guard tier's "cannot be grounded" hard error,
extended to the named form), never left to delay forever.

**The call site drives it; `require[X]` is only the explicit form.** A body call to an
operation whose sort declares `requires` does not need the author to have written
anything: the transformation reads the callee's dictionary chain
(`provider_dict_entries` / `synth_req_names` — the same producers
`resolve_bridge_requirements` reads, so there is one list, not two) and synthesizes one
`find_dictionary` goal per slot:

```
… op(a, b) …    ⇒   … find_dictionary(X, ?dx), find_dictionary(Y, ?dy),
                        apply_within(fn = op, args = (a, b),
                                     requirements = [?dx, ?dy]) …
```

**Placement: immediately before the call each goal serves.** `?dx` / `?dy` are bound
*from the body*, so they must be bound before the call reads them — and as late as
possible, because resolving them needs the carrier type, which comes from the call's
own arguments and may itself only be bound by earlier body goals. Immediately-before
satisfies both: no delay in the common case, and the transformation stays local — no
whole-body reordering. (Placement is not a *correctness* condition — a goal reading an
unbound dictionary variable delays until it is bound, which is what keeps a
hand-written `require[X]` sound wherever the author puts it. It is what makes the
generated case not pay for that safety net.)

`apply_within` is the existing carrier — `req_insertion` already emits exactly this for
op bodies, so no new node kind. An author-written `require[X]` simply **pre-binds** one
of those variables, which the generated goal then meets in its *bound* mode (§4: check
by unification). Default is automatic; writing it is how you name or share one.

**Emit a goal only where the typer did not already pin.** Where the §3.2 ladder
resolved the witness at compile stage, the dict is already built and installed
(`ConcreteApplyWithin.dispatch_dict`, WI-415) — synthesizing a run-time goal there
would be a straight pessimization of a solved case. The generated goal is the
**fallback for what the typer could not pin**, which in a rule body is the common case
because the carrier is often unbound until run time.

**This does not breach 058 §3.10** (*"instances are never CHOSEN at run time"*), though
it looks adjacent. §3.10 forbids *choosing*; under §2.1 the run-time act is fetch and
compose over table entries the typing pass selected — no typing operation, a tie
refused before run time (§4). And WI-300's guard already reads the runtime binding,
so a rule body reading carried types at fire time is the established precedent, not
a departure: 058 §3.3 puts rule bodies out of scope for selection precisely because
the typer often cannot pin there.

**Both halves already exist, one phase away from this.** `record_find_dictionary_grounding`
(`typing.rs:40046`) already rewrites rule bodies at typing time — walks
`kb.live_rule_ids()`, rebuilds the goal list, `set_rule_body_nodes` — it just rewrites
into a *checking* goal. And `req_insertion::run` (`kb/req_insertion.rs:46`) already
performs step 2's weave, but walks **`kb.op_bodies` only, never rule bodies**. This is
that weave extended to rules — `requirement-dictionaries.md` §3.3's "the op-body weave
transfers to rules in full", with the Γ slot replaced by an ordinary variable.

So the resolver gets **no new concept**: after elaboration a rule body is goals and
arguments, and `ResolverFrame` is untouched. An earlier draft of this document gave it
a `requirements: [(Symbol, VarId)]` slot map inherited on push like `assumed_facts`;
**dropped** — that was eval's shape imported where it does not apply. Eval needs a
frame slot because its variables are frame locals; a clause's are clause-scoped
already, and after step 1 the dictionary is just another logic variable in σ.

Rule→rule *inheritance* is the one thing genuinely absent: a callee rule does not see
its caller's dictionaries. Neither named consumer needs it (§7); build it when
something drives it.

Also absent, and for the record: **Γ** — `ResolveConfig.gamma` (`resolve.rs:367`) is a
fact overlay, global to one resolve call, seeded only by `prove_from_gamma`: not
per-activation and not backtrackable. And **no arena move**: the resolver need not own
allocation, because the only place it must produce a dictionary is a crossing, where
an interpreter is already in hand.

**This dissolves `requirement-dictionaries.md` §3.4's `[Open]` whole-rule-vs-positional
question.** A body goal reading the variable before `find_dictionary` binds it sees an unbound
var and delays. Ordering is a performance question, not a correctness one.

---

## 6. The crossings

- **SLD→eval** (`bridge_op_to_eval` → `call_op_bridged`) — *this is the "pass it to
  operations that require dictionaries" step.* When the clause has a `require[X]`
  covering the callee's requirement, read its σ-value and install it into the callee's
  `eval::Frame::requirements`, which is where a body's `var_ref(__req_*)` reads it;
  else
  `resolve_bridge_requirements` (`typing.rs:14667`) re-derives at the concrete
  argument types, as it does today. Supplying beats re-deriving only where
  re-derivation cannot decide (`Unresolvable`/`Ambiguous`, WI-855).
- **eval→SLD** (`prove_rule_predicate`): the caller's `frame.requirements` are
  dictionaries; hand them to the goal so a `require(X, ?d)` in the proved rule
  **checks** rather than re-resolves.

**Identity (WI-1045).** A dictionary has **one** — its content. It is an ordinary
value, so it stays valid in σ after `run_in_bridge_interp` drops the interpreter
that built it, and two dictionaries compare by `(impl, ordered subs)` wherever
they were built. The warning this paragraph used to carry — *two scratch
interpreters are two arenas, so compare structurally, never by `raw()`* — has no
subject any more.

---

## 7. Consumers

**WI-1037** — *mostly independent of this document.* Its defect is that
`reduce_op_value` folds the SPEC op's default body: `classified_apply_target` answers
`None` for `ConcreteApplyWithin` (`kb/node_occurrence.rs:608`), so the fix is to
redirect to `ConcreteApplyWithin.fn_target_sym`, decline the structural fold for that
class, and reach the bridge — which then resolves the impl's own `requires` chain
itself. Only when the *enclosing rule* declares a requirement to forward does WI-1037
need §6's supply path.

**WI-070 `Branch` / WI-069 `Suspension`** (027.2's eval↔SLD switch) — a dictionary is
a term bound in σ, and each branch has its own σ,
so multi-shot resume gets per-branch dictionaries **for free**. Being immutable, a
dictionary needs none of 047 §8's `register_undo` machinery that mutable state under
`Branch` does.

---

## 8. Non-goals

- The dictionary does **not** become a head argument — that changes rule arity and
  indexing and breaks a rule cited by name as a relation (052).
- **Nor a head goal.** `rule_heads` is `commaSep1($._goal)` — the same `_goal` as the
  body — so `require[X]` parses and converts on the left too (the converter refuses
  only data literals and `let`/`cut`). But a multi-head rule *concludes* each head:
  each becomes its own rule and the rule must carry a label for a unique citation
  handle (`load.rs:15613`, `:15623`). A `require[X]` there would **assert** the
  requirement, not demand it. Requirements stay on the right of `:-`.
- **No selection** at a rule-body requirement (058 §3.3 puts rule bodies out of scope).
- No new value carrier; no change to named slots (058 §3.4) or to §3.2's semantics.

## 9. One representation — the dictionary is an ordinary structural value

> **A dictionary has ONE runtime representation: an ordinary first-order value in
> the carriers every other value uses. There is no second store, no second identity,
> and no conversion at a crossing.**

A dictionary is **immutable** (the arena has no setter), **acyclic** (the
operation-call-model no-cycles policy), and — after the typing pass — **ground**
(§2.1: the fetch delays rather than composing a hole). An immutable ground acyclic
`(impl symbol, ordered children)` tree is a first-order value and nothing more; §2
said so already ("no closure in it, no host handle, no value"). So it belongs in the
carriers that already hold first-order values, and everything the channel needs —
unify to bind `?d`, unify to check a supplied one, read child `k`, read the impl —
is what those carriers already do.

The eval-side `RequirementArena` was a **second store for a shape the ordinary
carriers already hold**. What it bought was deallocation; what it cost was real and
had to be documented as a hazard: a second identity notion (`(arena, raw)`, so two
scratch interpreters gave one dictionary two identities and every comparison had to
be routed through the WI-1019 view), plus a conversion at every crossing. **WI-1045
retired it**, removing both and removing the boundary at which the two forms could
disagree.

**Not two representations kept in step — one.** `Frame::requirements`,
`Closure.requirements`, σ, and the reflect `Dictionary` face all name the same
value. `project(k)` is reading child `k`; `functor()` is reading the `impl` field.

**STORAGE IS A SEPARATE DECISION and this rule deliberately does not make it.**
"One representation" is about *shape and identity* — one functor, one key set, one
comparison — not about which carrier or store holds it. Whether a dictionary is
interned, arena-held or built fresh is chosen on its own merits, and can be changed
without touching anything above.

**One spelling, too — DELIVERED (WI-1045).** The IR construction node was
`anthill.reflect.Expr.construct_requirement(impl_functor = …, requirements = <cons
list>)` while the value presents `Dictionary(sub₀ … subₙ₋₁, impl: S)` — a different
functor, different key names, and a list where the value has positional children,
for one thing. They are now **one constructor**: the node's functor IS
`anthill.realization.runtime.Dictionary`, its sub-dictionaries are positional and
its provider is the named `impl`, so the node and the value it evaluates to present
the same head. The `Expr.construct_requirement` entity is gone from
`stdlib/anthill/reflect/reflect.anthill`; `dictionary_view_syms` owns both names for
every side.

**What this rule is NOT resting on.** An earlier version of this section argued for
the term from *partial* dictionaries: a conditional provision `provides Eq[Pair[A,
B]] :- Eq[A], Eq[B]` (058 §3.8, WI-869) makes `Eq[Pair[Int64, ?B]]` reachable with
`?B` unbound, which a `SmallVec<[RequirementHandle]>` has no inhabitant for. **That
premise is stale and must not be repeated.** §2.1 relocated narrowing to the typing
pass, and §4 says so in this document: typing-time narrowing is by one-way match,
which makes those partial dictionaries *forced, not chosen*. After typing there is
no partial dictionary — an unreadable carried type delays. The term is right for
the reasons above, none of which involve holes.

A conditional provision remains a Horn clause over `provides`, so candidate
narrowing is ordinary SLD over the same relation, run in the **typing pass**; run
time composes the resulting rows and does not search. Hence "at most one solution"
is a typing-time claim: no answer stream to dedup, and two entries for one carried
type is a defect (§4), not a tie.

### 9.1 WI-869's unfilled slot

WI-869 made strictness **per-provision**: a slot is demanded at a dispatch when it
is sort-level or a condition of the provision dispatched, *"otherwise left unfilled,
and reading an unfilled slot is refused at the read."*

Under §2.1 that read has **one** state at run time, not two: an unfilled slot is a
slot the dispatched provision **never promised**, a structural **hole** — a distinct
leaf, refused loudly at the read. The "not yet known" leaf an earlier draft proposed
alongside it (an unbound variable, read as a delay) is **unreachable after typing**,
for the same reason §9's partial dictionary is: composition never starts on an
unreadable carried type, so no slot is ever left pending. Both would have been
needed only if run time composed under uncertainty, which §2.1 forbids.

Delivered state (WI-1040, unchanged by WI-1045): neither leaf is constructible on
the fetch path, and WI-869's four producers are untouched. The hole leaf becomes
real when a dictionary can reach σ from somewhere other than a fetch — i.e. with
§10 item 3.

## 10. Open

Items 2 and 5 are **settled and delivered** (item 2's eval half by WI-1045);
1, 3 and 4 are untouched.

1. **[OPEN] The type-position channel for the un-stripped spec** (§5 — the rest of
   the encoding is settled there): which concrete channel carries the `[T…]`
   decoration past scope resolution (the application's type-args channel,
   WI-272/383, vs a type-kind occurrence child), so WI-613 attribution sees full
   specs. The constraint is fixed — a bare name there is a type Var (WI-849),
   never a scope-resolved ref; only the carrier is to pick. `require[X]` strips its
   type-args at convert exactly as `requires(X)` does, for the same stated reason,
   so the duplicate-spec-base hard error still stands.
2. **[SETTLED — one representation, no conversion] The dictionary carrier.** The
   item offered two settlements ("both carriers key alike" or "one converts at
   entry"). **Neither: there is one representation.** §9 is the rule — one functor,
   one key set, one comparison, named identically by σ, `Frame::requirements`,
   `Closure.requirements` and the reflect `Dictionary` face — and the eval-side
   `RequirementArena` is retired rather than converted into.

   *Delivered by WI-1040:* the σ half — `?d` binds to a value shaped exactly as
   WI-1019's view announced. *Delivered by WI-1045:* the eval half.
   `Frame::requirements`, `Closure::requirements` and `Value::OpRef`'s `dict` all
   hold `eval::dictionary::Dictionary` — a validated wrapper around the very
   `Value`, so `as_value` is the identity and the SLD→eval edge converts nothing.
   `RequirementArena`/`RequirementHandle` and the `Value::Requirement` variant are
   deleted, the two tree→dictionary producers are one
   (`typing::dictionary_of_tree`), and the IR construction node was respelled to
   the dictionary's own constructor. Driven by
   `wi1045_one_dictionary_representation_test`.
3. **[OPEN] The eval→SLD handoff mechanism** (§6): `prove_rule_predicate` is a
   closed ground test with no dictionary parameter; specify the channel (a
   signature extension vs a `ResolveConfig` overlay à la `assumed_facts`) and the
   caller-name → spec attribution at the boundary.
4. **[OPEN] The bridge deviation** (§2.1): compile `resolve_bridge_requirements`'s
   dispatch-time `unify_types` into projection paths, or grandfather it
   explicitly at the site.
5. **[SETTLED — the witness IS the covered call] Attribution.** The item asked
   whether WI-613's σ-class matcher (`find_requires_slot` /
   `find_requires_location`) could be reused wholesale. It is not needed at this
   tier and was not used: the goal's own witness scan already names an
   *occurrence*, and where that witness is an operation **of the spec itself** the
   witness and the covered call are the same node — attribution by identity, with
   nothing to match. The scan gained a fourth pass for a **defaulted** spec op
   (`lookup_spec_op_dispatch` answers only for a body-less one, so a spec op with a
   default body was previously no witness at all); it is ordered LAST, where the
   only prior outcome was the "cannot be grounded" hard error, so no rule that
   loads today can change which witness it picks.

   **The boundary, stated because it is a real gap and not an oversight:** the
   *transitive* witness (an op that declares `requires X`) and the *inherited* one
   (an op of a spec X requires, e.g. `eq` for `Eq`) still ground the requirement
   but are **not woven**. The first needs §6's crossing — threading a dictionary
   into a callee's frame, not choosing its member — and the second needs a
   projection into a sub-slot. Both bind `?d`, so the named spelling passes them by
   hand today. Item 1's un-stripping remains the precondition for attributing two
   `require`s on one spec base.

## 11. Delivered by WI-1040, and what it fixed in this document

- **Surface.** `require[X]` as a bare body goal and as the RHS of a top-level `=`;
  every other position refused loudly at convert, with its own sentence.
- **`require`'s name-resolution home is the CONVERTER, not the kernel vocabulary.**
  §3 said the name "joins the kernel vocabulary beside `find_dictionary`"; that was
  written before the position restriction was settled and it is now the wrong
  answer. Both legal spellings are rewritten away at convert, so a kernel-vocab
  entry would only ever be reached by an *illegal* one — where it would turn
  today's loud error into a name that resolves to nothing and then fails silently.
  The converter owns the name, exactly as it owns `requires`, `unify` and `eq`.
- **The weave.** A covered call is rewritten to `Expr::ApplyWithin { functor, args,
  requirements: [?d] }` — the existing carrier, now with its first *occurrence*-side
  producer. It stays `ViewHead::Opaque` in `TermView` deliberately: its faithful
  term twin is the WRAPPED reflect shape `apply_within(fn = …, args = …,
  requirements = …)`, whose head functor is `apply_within` and not the callee, so a
  transparent head would be a cross-carrier miss of the WI-425/WI-815 kind. The two
  readers that must understand a woven call read `as_expr()` directly: the WI-938
  functional-relation goal hook and `reduce_op_value`. `is_unreduced_op_call` counts
  a surviving `ApplyWithin` as un-reduced — measured, without that the hook bound a
  result variable to the call node itself.

- **The woven population is NARROWER than "every covered call", and the price of the
  `Opaque` head is paid here.** An `Opaque` goal is invisible to builtin dispatch, to
  the discrim query, and to the WI-938 hook unless that hook recognizes the callee —
  so only a rule-less **bodied** operation is woven. A **body-less** spec op (the
  typeclass norm, `PartialEq.eq`) and a **builtin-backed** one keep exactly their
  `requires(X)` behaviour; MEASURED, weaving them took a clause from one solution to
  none. Widening this needs a goal-position reader for a woven call, or the head's
  twin problem solved — not a quiet transparent head. **Every** call in the admitted
  population is woven, not just the witness: weaving one left the others folding the
  spec's default, which is a silent wrong answer in a clause that asked for the
  dictionary.
- **The fetch never composes under uncertainty**, which is what collapses §9.1 to a
  single leaf and retires §9's partial-dictionary argument: an unreadable carried
  type DELAYS *before* composition starts, so what σ holds is always ground.
  WI-869's four producers are untouched.
- **σ carries the term; eval still carries a handle.** The remaining conversion at
  `eval_requirement_chain_node` was §9's target and **WI-1045 removed it**: eval now
  carries the same value, and `eval_requirement_chain_node` reads a frame slot
  rather than converting one.
