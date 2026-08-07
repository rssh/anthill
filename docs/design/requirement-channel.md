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

A requirement arena slot is `{ functor: Option<Symbol>, requirements:
Option<SmallVec<[RequirementHandle]>> }` (`eval/requirement_arena.rs:28`) — an impl
symbol and its sub-dictionaries. There is no closure in it, no host handle, no value:
**a dictionary is exactly a first-order term** `Dictionary(sub₀ … subₙ₋₁, impl: S)`,
and WI-1019's `TermView` already presents it as precisely that, totally and losslessly
(`kb/term_view.rs:2228`, `:2322`, `:2364`, `:2386`).

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

Two surface rules the interpretation adds: **`require` needs a name-resolution
home** — no symbol `require` exists today; it joins the kernel vocabulary beside
`find_dictionary` (`load.rs:2345`). And **position is restricted**: `require[X]`
is legal as a bare body goal or as the RHS of a top-level `=` (the two forms
above); nested deeper in a term (`f(require[Eq[T]], ?y)`) it is refused loudly —
no general lifting.

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

**Handle identity.** `RequirementHandle { raw, arena: RequirementArenaRef }` where the
ref is an `Rc` (`eval/requirement_arena.rs:90`, `:167`), so a dictionary built in a
scratch interpreter stays valid in σ after `run_in_bridge_interp` drops it. **Pin at
the site:** two scratch interpreters are two arenas — compare **structurally** (the
WI-1019 view), never by `raw()`.

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

## 9. Conditional provisions decide the representation

A provision may be conditional — `provides Eq[Pair[A, B]] :- Eq[A], Eq[B]` (058 §3.8,
delivered WI-869). This is not a complication for a relational `requires`; it is the
reason the shape fits. A conditional provision **is a Horn clause over `provides`**
(058 §3.8), so candidate narrowing is ordinary SLD over the same relation — run in
the **typing pass** (§2.1), where a provider's own chain composes by resolution
rather than by bespoke code; run time only composes the resulting rows.

But it settles a question that was open while `requires` only *checked*:

- **The σ-bound dictionary must be a TERM, not an arena handle.** A conditional
  provision makes a **partially resolved** dictionary reachable: resolving
  `Eq[Pair[Int64, ?B]]` pins the outer impl while `?B` is unbound, so one sub-dictionary
  is not yet known. A term represents that natively — `Dictionary(impl: PairEq, d_A,
  ?d_B)`, refined later by binding `?d_B`. A handle **cannot**: an arena slot is
  `{ functor: Option<Symbol>, requirements: Option<SmallVec<[RequirementHandle]>> }`
  (`eval/requirement_arena.rs:28`) — a sub must be an already-built handle, and there is
  no variable inhabitant. The handle stays eval's form, where everything is ground by
  construction; the boundary converts.
- **"At most one solution" is a TYPING-TIME claim.** A dictionary may be reachable
  by several derivations, but candidate narrowing and overlap refusal happen in the
  typing pass (§2.1) — run time fetches and composes, it does not search, so there
  is no answer stream to dedup and no runtime tie to adjudicate (two entries for
  one carried type is a defect, §4).

### 9.1 The one genuine interaction to settle

WI-869 made strictness **per-provision**: a slot is demanded at a dispatch when it is
sort-level or a condition of the provision dispatched, *"otherwise left unfilled, and
reading an unfilled slot is refused at the read."* The staging invariant (§2.1) makes
the two unfilled states **representably distinct**, which is the proposed settlement:

- **not yet known** — composition stopped at an unreadable carried type: an
  **unbound variable**. Reading it **delays**; a later binding fills it.
- **never promised** — the dispatched provision does not demand the slot: a
  structural **hole**, a distinct leaf that is not a variable. Reading it **refuses
  loudly**; no later binding can fill what was never promised.

Illegal reads become distinguishable by shape at the site instead of by policy.
Owned by **WI-1040**: confirm the two-leaf representation before writing the read,
and say at the site which of the four WI-869 producers each leaf is keyed to.

## 10. Open

1. **The type-position channel for the un-stripped spec** (§5 — the rest of the
   encoding is settled there): which concrete channel carries the `[T…]`
   decoration past scope resolution (the application's type-args channel,
   WI-272/383, vs a type-kind occurrence child), so WI-613 attribution sees full
   specs. The constraint is fixed — a bare name there is a type Var (WI-849),
   never a scope-resolved ref; only the carrier is to pick.
2. **One σ-carrier for a dictionary value**, stated once: §6 lets eval-supplied
   HANDLES ride in σ; §9 requires partial compositions to be structural TERMS.
   Either both key and unify alike through the WI-1019 view (then name the term
   constructor — its functor must equal the view head's `Dictionary` symbol), or
   one carrier converts at entry. Includes term→handle materialization at the
   SLD→eval crossing (refuse on non-ground), and a driving test that unifies a
   handle against a partial term, binding a sub-slot.
3. **The eval→SLD handoff mechanism** (§6): `prove_rule_predicate` is a closed
   ground test with no dictionary parameter; specify the channel (a signature
   extension vs a `ResolveConfig` overlay à la `assumed_facts`) and the
   caller-name → spec attribution at the boundary.
4. **The bridge deviation** (§2.1): compile `resolve_bridge_requirements`'s
   dispatch-time `unify_types` into projection paths, or grandfather it
   explicitly at the site.
5. **Attribution** reuses WI-613's σ-class matcher (`find_requires_slot` /
   `find_requires_location`) wholesale, per `requirement-dictionaries.md` §3.4. To
   confirm, not redesign — item 1's un-stripping is its precondition.
