# The requirement channel for rules — implicit parameters, implicit arguments

**STATUS: DESIGN. §7 STEP 3 IS BUILT (WI-20260909-NAR1X, 2026-09-12); STEPS 1, 2 AND 4
ARE NOT.** Settles [`requirement-channel.md`](./requirement-channel.md)
§10 item 3 — "specify the channel … and the caller-name → spec attribution at the boundary" —
and the carrier question [`060-typedomains-implementation.md`](./060-typedomains-implementation.md)
answers two ways (§4.3 step 3 vs §5). Companion to `requirement-channel.md`, which owns the
dictionary mechanics, and to [`operation-call-model.md`](./operation-call-model.md), whose rule
for operations this extends to rules unchanged.

**WHAT STEP 3 TOOK, AND WHERE THIS NOTE WAS WRONG ABOUT THE TREE — §5.2 carries both,
corrected in place rather than erased.** The short version: at the rule→op edge the
implicit argument already existed. WI-1040 puts the clause's dictionary BESIDE the call
as `Expr::ApplyWithin { requirements: [?d] }` — a term beside the goal, De Bruijn-closed
with the body and opened with it, which is exactly what §4 says an implicit argument is —
so nothing had to be invented to carry one. What was missing was two readers: the weave
refused to put that channel on a CARRIER-LESS callee, and the bridge dropped it on the
way into eval. Both are §5.2. The per-predicate SEQUENCE of §2 was not needed at this
edge and remains unbuilt: a rule→op edge's callee sequence is the operation's own
`requires` chain, which is recorded already, and its caller sequence is the clause's own
`require[X]` reads, which the converter has lowered since WI-300.

**The design in one sentence: a predicate has IMPLICIT PARAMETERS — its requirement sequence,
part of its head interface — and a goal, being a call of a predicate, carries IMPLICIT
ARGUMENTS for them, written by the typer beside the goal term and bound to the clause's
parameters at the push, positionally, the way explicit arguments are bound by head unification.
Every goal becomes a head when it is interpreted, implicit arguments included.** Everything else
here is that sentence applied at each edge.

**How this note got here, recorded rather than erased.** A first draft treated the channel as an
ambient environment inherited by every activation; the operation channel is not that (§1). A
second put a per-activation channel on `ResolverFrame`; a resolver frame is a resolvent, not an
activation (§1). A third filled it at run time by matching specs against the caller's; a typed
rule has one `SortDomain` slot per column and a generative call has no values, so nothing at run
time can say which same-base slot is which (§4). A fourth had the typer record a per-clause plan
and the push execute it by lookup; with the sequence on the HEAD the lookup is a position, and
the plan is just the goal's arguments. What survived every draft: replace, never inherit; a slot
holds its spec beside its dictionary (§3); the three crossings (§5).

**Terms.** A predicate's IMPLICIT PARAMETERS are its requirement sequence `[R₁ … Rₙ]`, one
`RequiresEntry` each, part of the head interface and the same for every clause — as an
operation's `requires` chain is part of its signature and `dict_layout` its positional shape. A
clause has one IMPLICIT-PARAMETER VARIABLE `?rₖ` per entry, a clause variable like any other. A
body `?d = require[Rₖ]` is the READ of one: `?d` is `?rₖ`, as `var_ref(__req_k)` reads slot k of
an operation's `Frame::requirements`. A goal's IMPLICIT ARGUMENTS are one term per implicit
parameter of the predicate it calls. FILLING is binding `?rₖ` to the goal's k-th implicit
argument; DERIVING is the read building the dictionary itself from a value's carried type, which
is what `find_dictionary` does today and what it keeps doing when `?rₖ` arrives unbound.

## 0. The five questions, answered

| question | answer | § |
|---|---|---|
| WHAT HAPPENS at a rule call | the callee's implicit parameters are bound to the goal's implicit arguments — REPLACE, never inherit. Identical to `enter_operation`, at every TYPED edge: a citation in an operation body, a body goal in a rule, an operation call in a rule body (**the last one is BUILT** — §5.2.1) | 1 |
| what this DEPENDS ON | a predicate's implicit-parameter sequence — derived from its clauses' `require[X]` reads, or written on the head — and the typer's edge check that writes each body goal's implicit arguments. Neither exists: `RuleEntry` stores no sequence, and a body goal carries no arguments beyond the written ones | 2 |
| what CARRIES it | the GOAL. Its implicit arguments ride beside its term, De Bruijn-closed with the body and opened with it, and move with it under rotation and continuation. Not a `ResolverFrame` field: a frame holds the callee's body AND the caller's remaining goals. Not `ResolveConfig`: activations differ. Not the term itself: the arity census `060-implementation.md` §7.3 paid | 1 |
| what a slot HOLDS | a `RequiresEntry` beside the variable holding its dictionary. A dictionary value cannot say which spec it witnesses, so the dictionary alone cannot be attributed | 3 |
| how a slot is FILLED | at the push, positionally: `?rⱼ := tⱼ` for each implicit parameter, right after head unification. The typer wrote `tⱼ` at the edge — the caller's `?rₖ`, a dictionary tree over the caller's `?r`s, or a fresh variable — by `resolve` under the edge's σ. Run time matches nothing. A DYNAMIC edge — semantic-eq dispatch, `apply_domain` — writes no arguments, so every parameter arrives unbound and derives | 4, 5 |

## 1. The model — replace, do not inherit

**THE OPERATION MODEL IS REPLACEMENT, and it is stated at the site.** `enter_operation`
(`eval/eval.rs:3228`) installs the callee's channel with the comment at `:3263`: *"callee's
`frame.requirements` come from `apply_within`'s expanded requirements channel. Plain `apply` calls
install an empty channel — a generic body's `var_ref(__req_*)` read then surfaces a clear 'unbound
in requirement position' error rather than being silently wrong."* The channel installed is built
by `expand_dispatching_dict` (`:2064`) out of the CALLEE's layout — `__req_self` plus the slice
`slots_for(owner)` names (`typing.rs:63069`). `Frame::child_context` (`eval/frame.rs:292`) clones
the parent's channel, and it is used for a child EXPRESSION inside one operation, never for a
call.

So an operation activation's evidence is not what its caller happened to be holding. It is what
the CALLEE DECLARED, filled from what the caller holds. **A rule activation is the same thing and
takes the same rule** — and once the requirement sequence is on the head, the rule is just
argument passing: a call supplies one argument per parameter, the callee binds them.

**THE PRODUCER IS THE DECLARATION, NOT THE CALLER'S VALUES.** An earlier draft asked "which of
the caller's dictionary VALUES does a rule push rebase from?", found that answering needs the spec
a `Dictionary` does not carry (§3), and concluded no producer was possible — hence an ambient
environment. The operation model never asks that question. It reads the callee's declared
sequence, which is static, and RESOLVES each entry against the caller's at the call site.
**AND THAT IS EXACTLY `resolve` + `available_requires` + `FromScope`.** The callee's sequence is
the DEMAND; the caller's is the SUPPLY; `FromScope(k)` is the answer "this parameter's argument
is the caller's `?rₖ`". `060-typedomains` §3 named the same thing from the other end —
`apply_domain` is "the SLD-side twin of `dispatch_apply_with_requirements`". One mechanism, two
engines.

**THERE IS NO OTHER MECHANISM, and the entry is not a special case.** A third draft kept the
entering operation's evidence as a resolution-global set and let inner activations "read the type
off the value" they were handed. That reading is local CONSTRUCTION, available only when the value
carries its type, and it is not a channel:

```anthill
rule a(?x: A, ?l: List[A]) :- ?d = require[Eq[A]], b(?l)
rule b(?l: List[B])        :- ?d = require[Eq[B]], …
```

called as `a(3, nil())`: `a` pins `A` from `?x` and holds `Eq[Int64]`; `b` receives `nil()`,
whose carried type has no element, and can build nothing. Yet `a` knows the answer. The
requirement mechanism exists because the typer compiles an operation ONCE, with its type
arguments RIGID — names, not types — so it can never produce the dictionary, and a value does not
carry its instance either; what the typer cannot know must be threaded at run time. That is as
true one rule edge down as it is at the operation boundary. So every edge — the entry, rule→rule,
rule→op — is the same argument passing.

**AND THE MAPPING IS THE TYPER'S, not the run time's.** With `a`'s one `Eq`, a run-time match by
spec picks it by accident. Take the ordinary typed clause instead:

```anthill
rule r(?a1: A, ?a2: A, ?b1: B, ?b2: B) :- Eq[A], Eq[B], something
```

cited from `g[X, Y](p: X, q: X, u: List[Y], v: List[Y]) requires Eq[X], Eq[Y]` as
`r(p, q, u, v)` with `u`, `v` empty: the caller holds `Eq[Int64]` and `Eq[List[Int64]]`, `B` is
never pinned from `nil()`, and an unbound `B` is covered by BOTH. Under 060-typedomains every
typed column adds a `SortDomain[T]` parameter besides (§4.4 there), so several of one base is what
a typed clause looks like — and a GENERATIVE call has no values at all. The typer, at the edge,
unifies `r`'s head types with the goal's argument types — `A := X`, `B := List[Y]` — and writes
`r`'s arguments: `g`'s first `?r`, and `ListEq` over `g`'s second. Names, not types: the typer
never sees `Int64`, and does not need to. The run time binds by POSITION and never matches.

**CARRIER: THE GOAL, not a `ResolverFrame` field.** A value written per activation cannot ride
`ResolveConfig`, whose own justification is the opposite property (`resolve.rs:619`): *"Global to
one resolve call (every frame sees the same Γ), so it rides the config, not the per-frame
`assumed_facts` stack."* But it cannot ride the frame either. A `ResolverFrame` is a RESOLVENT —
its own doc (`resolve.rs:838`): *"a step of SLD resolution — a resolvent (`goals`), the
substitution proving it, and the assumptions in scope"* — and the rule-body push builds ONE goal
list out of the callee's body AND the caller's remaining goals (`resolve.rs:4550`,
`new_goals.extend(remaining)`). A field on that frame is read by both halves. `assumed_facts`
gets its scope not from the per-push clone but from a `__pop_assumption(N)` MARKER GOAL appended
after the consequents (`resolve.rs:2762`, popped at `:1517`) — and the delay fallback (`:4190`)
moves a delayed goal to the END of the list, past any marker, while `find_dictionary` is
precisely the goal that delays (`:7910`).

A goal is a predicate call, and a call has arguments. So each entry of `goals` is the goal's term
PLUS its implicit arguments, and the pair moves together — under the delay fallback (`:4226`), a
bounded-quantifier continuation (`:4256`, `:3015`), `forall_impl` consequents (`:2779`), a fact
match (`:4384`), the rule-body push (`:4551`), and the initial goals (`:4966`): every goal-list
construction copies goals whole, and none of the seven makes a decision. A goal with no implicit
parameters carries an empty sequence, one shared empty `Rc`, so the common case costs a pointer
copy. **The dictionary VALUE is an ordinary σ binding** — the carrier WI-1040 already drives
across a rule boundary (`a_clause_dictionary_crosses_a_rule_boundary_and_is_checked`), restored on
backtrack with the rest of σ, and read by `require[X]` in the check mode that exists (§2).

**TWO THINGS TO SAY PLAINLY.**

- **The sequence belongs to the PREDICATE.** An intermediate draft put it on the clause, because
  a run-time fill knew its clause. With arguments written by the typer at the edge, the edge must
  know the sequence before any clause is chosen — `build_relation_value` already depends on "all
  clauses of a multi-clause relation share one head interface" for COLUMNS, and the requirement
  sequence is that kind of thing. §2 says how the clauses' reads become one sequence.
- **Cost lands on the resolver's hot path.** Every goal carries a sequence, and every rule
  activation whose predicate has one binds it. The dominant case has none and shares the empty
  one, so this is probably an `Rc` clone per goal moved plus an emptiness test per push — a claim
  to MEASURE, not to assume, and the one number this design owes before it is built.

## 2. The prerequisite — the reads exist; the sequence and the arguments do not

**`RuleEntry` (`kb/mod.rs:333`) carries `head`, `body_nodes`, `arity`, `globals`, `type_bounds`,
`head_vars` — and no implicit-parameter sequence; a body goal occurrence carries its written
arguments and no implicit ones.** `type_bounds` is WI-582's typed-head bound list (5G28A extended
what it holds), which says what a COLUMN is, not what EVIDENCE the clause takes from its caller.

**A body `require[X]` is the READ of an implicit parameter — and an earlier draft called it the
parameter itself.** WI-300's converter desugars `require[X]` to `find_dictionary(X, out: ?d)`,
minting `?d` when the author wrote none (`convert.rs:3390`); the typing sweep rewrites the spec
into `find_dictionary(spec, op_functor, args…, out: ?d)`. That goal has two readings, decided by
whether `?d` is bound when it runs:

| `?d` at goal time | the goal | who this is |
|---|---|---|
| UNBOUND | DERIVES a dictionary from the arguments' carried types at the current binding | the local fetch — the rule obtaining evidence FOR ITSELF, the twin of an operation body resolving an instance from an argument's type |
| BOUND | CHECKS the supplied dictionary against the local derivation — `read_dictionary_into` does bind and check as ONE `unify_values` (WI-1040 acceptance (c)) — and where the local derivation is Undecided, the supplied one stands | the read of an implicit parameter the caller filled — the twin of `var_ref(__req_k)` |

Today nobody binds `?d` across the op→rule edge, and across rule→rule only an author who threads
`?d` through the WRITTEN head by hand does (WI-1040's crossing test). The guard form
`requires(X)` has no `out` and is a CHECK, never a read. `060-typedomains` §4.4's `:- Eq[A]` must
be a READ: its clause's `eq(?y, ?z)` is a rule-body operation call, and crossing 3 (§5.2) fills
that call from the clause's own parameter, which a check does not have. And under that document's
transform every typed column adds a `SortDomain[T]` read, generated rather than written — so a
typed predicate's sequence is mostly entries of ONE base, and the written `require`s are the
minority.

**THE SEQUENCE: derived from the reads, or written on the head.** Nothing here depends on which
surface; what is fixed is the rule that makes one sequence out of several clauses. Each clause's
reads are expressed over the head's COLUMN TYPES by position (clause 1 may write `?x: A` and
clause 2 `?x: T`; both mean "column 1's type"), and the predicate's sequence is the UNION, in first
occurrence order, with a load check that two clauses do not read one spec at two different column
types under one name. A clause simply reads the entries it uses, and its `?d` for entry k IS
`?rₖ`. A read that cannot be expressed over the head's columns is the unanchored case, already
refused (channel §10 item 1). A written head-level form, if one is added, must state the same
sequence; two clauses disagreeing with it is a load error naming both.

**What is missing is the SEQUENCE on the predicate and the EDGE CHECK that writes arguments.**
`RuleEntry` (or the predicate's record) must carry `[RequiresEntry …]` with, per clause, the De
Bruijn index of each `?rₖ`; and the typer must, at every typed edge (§4), unify the callee's head
bounds with the goal's argument types AS THE CALLER KNOWS THEM, resolve each entry of the
callee's sequence under that σ against the CALLER's sequence ∪ provisions, WRITE the answer as
the goal's implicit arguments, and REFUSE at load — naming caller, callee and entry — where an
entry at a type the caller declared has no answer. That is the operation call-site check applied
to a rule edge.

## 3. A dictionary cannot name its spec, so a slot holds a PAIR

`Dictionary` is `Dictionary(sub₀ … subₙ₋₁, impl: S)` (`eval/dictionary.rs:58`), and WI-867's doc
at `:67` states the consequence: *"it knows a provider and no spec, so it cannot tell a dictionary
that carries evidence from one that is short of it."* `Frame::requirements`
(`eval/frame.rs:262`) works around this by keying on a synthesized `__req_*` NAME — minted from
the OWNER's chain, so it says nothing to anyone else.

A sequence entry therefore carries the `RequiresEntry` (`typing.rs:61747`: `required_sort`,
`spec: Value`, `supply`) beside the variable holding the dictionary, which is what `resolve`
reads as `available_requires` at the edge. **At an eval→SLD boundary those entries are
recoverable from the frame**, through the same two lists that minted the names:
`synth_req_names_of` walks `provider_dict_entries(parent_sort)` (`typing.rs:62746`) and
`synth_op_req_names_of` walks `op_requires_chain_rc(op)` (`:62640`). Pairing the frame's
dictionaries with those chains reuses the producer's own enumeration, so the pairing cannot drift
from the naming.

**ONE SLOT IS NOT RECOVERABLE and must be recorded rather than recomputed.** `__req_self` is
pushed ahead of the chain (`eval/eval.rs:2104`) and its spec is computed one line earlier —
`dispatch_spec_of_op(&kb, dispatched_from).or_provider(provider)` (`:2090`) — from
`dispatched_from`, which the frame does not keep (`Frame::op` is the TARGET). One added `Frame`
field, not a change to `requirements`' element type; the alternative is a second derivation of a
value WI-866 gave one owner (`DispatchSpec::or_provider`).

## 4. The fill — arguments written at the edge, bound at the push

**THE TYPER WRITES THE ARGUMENTS; THE PUSH BINDS THEM — the operation model with nothing added.**
At a typed call site of an operation, `resolve` runs at TYPING with the caller's chain as scope
and σ over the call's type variables (`ResolutionScope.sigma`, `typing.rs:30579`, WI-821), and
emits per callee slot a `FromScope(k)` read or a construction — `requirement_at_current(k)` IR.
A rule edge gets the same, and its output is a TERM per callee parameter:

```
implicit argument tⱼ  =  ?rₖ                          -- FromScope(k): the caller's k-th parameter
                      |  Dictionary(…, impl: S) over ?r's  -- Build: provisions compose it, leaves may be the caller's
                      |  ?fresh                        -- Local: the typer has nothing; the value decides
```

written beside the body goal's occurrence, De Bruijn-closed over the caller clause's variables
exactly as the goal's written arguments are, and opened with the body by `with_fresh_vars`. **A
term is a ROUTE, not a value.** The typer compiles `g[X, Y]` once with `X`, `Y` RIGID and never
sees `Int64`; it writes "`g`'s first `?r`", and `g`'s frame holds whatever is in it when
`g[Int64, Int64]` is entered — exactly `requirement_at_current(k)`. That rigidity is the
motivation for the channel: what the typer cannot know is threaded at run time, as an argument.

**When the typer writes each form, and where the earlier drafts' run-time arms went:**

- `?rₖ` — exactly one caller entry covers under σ. TWO covering is a LOAD refusal naming both and
  the entry: the `≥ 2` arm of earlier drafts, now where it is loud and early. Never first-wins —
  and `resolve`'s scope loop IS first-match today (`typing.rs:30875`, the
  `for (i, ar) in scope_entries` loop returns at the first cover), so the refusal is a change to
  that loop, which serves every `resolve` consumer, made there with a row per consumer.
- a dictionary tree — no caller entry covers and provisions construct it; `resolve` is the
  recursive composer, so a `?rₖ` leaf deep inside the tree is what `SortDomain[List[T = X]]`
  needs, and why no new composition machinery appears anywhere in this note. The tree holds
  variables until the caller's parameters are bound; that is ordinary for a term.
- `?fresh` — the entry's type is a FRESH variable at this edge: an untyped caller,
  `rule a(?x) :- b(?x)`, where the typer knows nothing about `?x` and the run time may — a value
  that carries its type derives, as WI-300 does today. NOT for a type the caller DECLARED and does
  not supply: `rule a(?x: A) :- b(?x)` with `b` reading `Eq[B]` and `a` holding no `Eq[A]` is
  REFUSED at load — the caller declares it or constructs it, exactly as an operation must. The
  line is WI-270's: refuse what typing could not determine, not what was not written.

**AT THE PUSH** (`resolve.rs:4551`), after `with_fresh_vars` has opened the clause and head
unification has bound the written arguments: bind `?rⱼ := tⱼ` for each implicit parameter, in
order — one unification per entry, no lookup, no matching, no type needed. Then append the body
goals, each carrying its own opened implicit arguments. Nothing need be bound for this to work: a
`?rₖ` argument aliases two variables, a tree holds variables, a `?fresh` binds nothing. The
timing hazard an intermediate draft found — the generated `domain` goal pins a bound's type
variable only when it RUNS (`pin_bound_from_value`, `typing.rs:66467`, from `resolve.rs:6179` and
`:6336`), after the push — is moot, because nothing at the push reads a type.

**AT THE `find_dictionary(X, …, out: ?d)` READ, nothing new.** `?d` (that is, `?rₖ`) bound → CHECK
against the local derivation where one exists (WI-860: `read_dictionary_into` does bind and check
as one `unify_values`; a supplied dictionary disagreeing with a UNIQUE local derivation fails
loudly naming both). `?d` unbound → DERIVE, as today. `fetch_dictionary`'s scope stays hardcoded
empty (`typing.rs:65888`):

```rust
let scope = ResolutionScope { available_requires: &[], sigma: None, selected: &[] };
```

and its doc — *"a rule clause has no caller frame whose slots could satisfy this by forwarding"* —
stays true of the READ: the forwarding is an argument, bound before the body ran.

**Edit 2 — the terminal arm answers `None`** (`typing.rs:66253`, in `dictionary_of_tree`):

```rust
ResolvedRequiresNode::FromScope { .. } => return None,
```

When the typer turns a resolved tree into an argument term, this arm emits the caller's `?rₖ`
(a De Bruijn reference) instead. The node's own doc (`typing.rs:30625`) already says what it
means: *"the caller's `frame.requirements[slot]` already holds the right requirement value."*
**This design makes that sentence true at run time.**

**Edit 3 is already the typer's.** The wildcard-tolerance `ResolutionScope`'s doc warns of —
*"without a gate an abstract caller entry (`Desc[AT]`) covers a CONCRETE goal (`Desc[Pebble]`)"* —
is gated by `requires_entry_covers_goal` (`typing.rs:40333`) taking `sigma`, and the edge check
passes the edge's σ exactly as a call-site dict build does (WI-821). Nothing runs at run time to
need it.

### 4.1 The matching rule — at the edge, total, and it needs no new key

Spec-base equality is not a matching rule: either side may hold two entries of one base. **The
identity is the spec VALUE compared under the edge's σ.** For each callee entry, let `C` be the
caller entries whose spec covers it:

| `|C|` | the typer writes |
|---|---|
| 1 | `?rₖ` |
| 0 | a tree, if provisions construct it; else `?fresh`, if the entry's type is fresh at this edge; else REFUSED at load naming caller, callee and entry |
| ≥ 2 | REFUSED at load naming both entries. Never first-wins: "the caller supplied it" is not a tie-break, for the reason WI-860 gives |

Three properties, each of which was an open question in an earlier draft:

- **A caller entry nothing asks for is IGNORED, not diagnosed.** The caller's sequence is written
  for the caller's needs; a callee that does not demand it is not in error.
- **A UNIQUE local derivation still wins a disagreement loudly** (WI-860), at the read, in CHECK
  mode — a supplied argument does not silence the value's own evidence.
- **S8CBV's projection root SHARPENS `covers`; it does not replace this rule.** σ-cover already
  separates two same-base entries whose types differ. Nothing is deferred: the function is total
  today and S6 narrows the refusing arm.

### 4.2 Several parameters — the ordinary case

Under 060-typedomains every typed column is a `SortDomain[T]` parameter, so `r(?a1: A, ?a2: A,
?b1: B, ?b2: B) :- Eq[A], Eq[B], something` has FOUR — `SortDomain[A]`, `SortDomain[B]`, `Eq[A]`,
`Eq[B]` — two bases, two of each. Nothing about the passing is per-clause:

- **Each parameter has its own argument and its own variable.** They are independent ROOTS
  (060-typedomains §4.4), tied only by the type variables they share: at the edge, `A := X`
  decides `SortDomain[A]`'s and `Eq[A]`'s arguments together, and at run time the tie between
  `?a1` and `?a2` is `pin_bound_from_value`'s ("a rule's two columns are a TIE rather than two
  independent checks").
- **Siblings are not scope for each other, and need not be.** Resolving `Eq[List[A]]` may descend
  to an `Eq[A]` leaf; that leaf is the caller's `?rₖ` or constructed, never the sibling `Eq[A]`
  parameter. Coherence says the two are the same dictionary, and the sibling's own CHECK at its
  read holds it to the local derivation — a sibling read would add a second reader of one fact.
- **Two entries of ONE base are told apart by the edge's σ**, `SortDomain[A]` and `SortDomain[B]`
  at `X` and `List[Y]`, and by POSITION at run time. That is why the mapping cannot be made at
  run time by spec: with `B` unbound both cover. The load-time duplicate refusal stands only for
  two EQUAL requires or one that no anchor grounds (`requirement-channel.md` §10 item 1).
- **A caller entry may serve several callee entries**, and a caller entry nothing asks for is
  ignored.
- **Cost is linear in the sequence length**: one `resolve` per entry per edge at TYPING; one
  unification per entry at the push.

**WHAT EXISTS, MEASURED 2026-09-12.** No shipped `.anthill` program (stdlib, examples,
anthill-todo) has a rule-body `require[…]` at all. The only multi-`require` clauses are
`wi_96ztm_two_dictionaries_test.rs`'s — two of ONE base at two carriers (`Desc[T = Leaf]` /
`Desc[T = Other]`, `PartialEq[T = Thing]` / `PartialEq[T = Gadget]`), every one grounded locally
from a typed head binding and handed on through the WRITTEN head. They drive derive and check,
not the passing; the first predicate needing several PASSED entries is the typed head above, once
060-typedomains generates its `SortDomain` reads. And 96ZTM's
`a_call_two_dictionaries_both_claim_is_refused` STAYS a refusal here: a nullary call in a rule body
is a crossing-3 edge (§5.2), and two clause entries covering its one requirement is §4.1's `≥ 2`
arm at typing.

## 5. The boundaries — three crossings, two kinds of edge

An edge is TYPED when the typer sees it and can write arguments — a citation in an operation
body, a body goal in a rule, an operation call in a rule body. It is DYNAMIC when the callee is
chosen at run time from a value — semantic-eq dispatch, `apply_domain` — and there the values
are ground or the dictionary is itself a written argument, so every implicit parameter arrives
unbound and derives.

| # | crossing | site | kind | where the arguments come from |
|---|---|---|---|---|
| 1 | op A → rule R, GROUND closed test | `prove_rule_predicate` (`resolve.rs:7443`), reached through `prove_rule_predicate_value` (`eval/eval.rs:3194`) from `eval/mod.rs:1083` and `eval/eval.rs:2665`, both gated by `eq_bridge_target`, and from `eval/builtins.rs:1553`, which restates the gate inline — two args, a body-less op, ground operands, a `sem_eq_dispatch_target` match | DYNAMIC | NOWHERE, and none is missing. The callee is `<carrier>.eq`, chosen by the value; both operands are ground and carry their types; every anchored read of R derives LOCALLY. A read that could not is one no anchor grounds, refused at load (channel §10 item 1). **NAR1X's row is crossing 3's**: R holds its `Monoid[A]` by local derivation and calls the carrier-less `unit()` — see §5.2 |
| 2 | op A → rule R, GENERATIVE citation | `build_relation_value` (`eval/eval.rs:638`) builds the value; `execute_logical_query` (`execute.rs:1086`) starts the search LATER | TYPED | the citation's arguments, VALUES from A's frame, CAPTURED IN THE VALUE — §5.1 |
| 3 | rule R → op B | `reduce_op_value` → `bridge_op_to_eval` (`resolve.rs`) | TYPED | the call's implicit argument — WI-1040's `Expr::ApplyWithin { requirements: [?d] }`, σ-walked and handed explicitly into a FRESH interpreter. **BUILT** — §5.2, §5.2.1 |

`prove_rule_predicate` also runs as a CLOSED SUB-PROOF from inside a resolution
(`resolve.rs:7388`, the semantic-eq dispatch). That is crossing 1 again — dynamic, ground, local —
stated so it is not found as a hole.

### 5.1 Crossing 2 — the arguments are CAPTURED IN THE VALUE

**A first-class relation outlives the frame that built it.** `build_relation_value` constructs
`Value::Relation { query: Rc<Value>, columns: Rc<[(Symbol, VarId)]> }` (`eval/value.rs:312`) — a
packaged query carrying no environment — and the resolver is not started until
`execute_logical_query`. In between, the relation can be returned, composed, captured in a closure,
or consumed after its creating frame has popped. Reading the frame at construction to seed a config
that does not yet exist is not a mechanism.

**THE PRECEDENT SHIPS: a closure has this problem and solves it by capture.** `Closure` carries
`requirements: SmallVec<[(Symbol, Dictionary); 1]>` (`eval/closure.rs:45`), and its doc at `:40`
states the rule: *"restored on call to preserve the lexical scope where the lambda was created, not
where it's invoked."* A `Relation` takes the same treatment:

- **WHERE IT LIVES:** a third field on `Value::Relation`: the cited predicate's implicit
  arguments as VALUES, evaluated at `build_relation_value` from the typer's terms for the
  citation — a `?rₖ` read from `Frame::requirements` (paired with its entry per §3), a tree
  built over such reads, each entry's spec walked through `Frame::type_args` FIRST so a rigid
  `Eq[T = X]` is the real `Eq[T = Int64]` (060-implementation §7.3's E1). `Rc`, so `clone`
  stays O(1) — the variant's existing payloads are `Rc` for that reason.
- **WHO READS IT:** `execute_logical_query` attaches them to the initial goal as its implicit
  arguments — never from a live frame. This is the one entry that carries op evidence INTO a
  resolution, and the generative `member(?x)` with `?x` free is what it exists for.
- **WHAT COMPOSITION DOES:** capture is at the LEAF — `build_relation_value` builds one cited-rule
  relation and combinators build over those. Because arguments travel with the goal (§1), a
  combinator over relations whose captured arguments differ needs no rule: each leaf's goal
  carries its own when the query is lowered; nothing merges and nothing picks. An earlier draft
  refused this case; the refusal was an artefact of a per-frame carrier.

### 5.2 Crossing 3 — a fresh interpreter, and what the arguments change

`run_in_bridge_interp` (`resolve.rs:10056`) does `std::mem::take(self)` on the KB and builds
`Interpreter::with_config(kb, bridge_mode: true)`. **The knowledge base is shared — moved across
and back — and the ACTIVATION STACK is not.** B begins with an empty frame stack, so no
inheritance rule of any kind reaches it. Today B's channel is derived from scratch by
`resolve_bridge_requirements(kb, op, args)` (`typing.rs:25835`), which pins the op's chain **from
the ARGUMENTS' types and nothing else**; `reduce_op_value` says so at `resolve.rs:9823` —
bridging the callee here "resolves its `requires` at the concrete argument types instead, **which
is the one entry that can**."

**THAT IS THE RIGHT QUESTION AT A DYNAMIC CALL AND THE WRONG ONE AT A TYPED CALL.** NAR1X marks
the case with `op_has_spec_carrier_param == false` (`typing.rs`) — `Zeroable.zero()`,
`Monoid.unit()`, a nullary or all-content spec op: no argument to pin from. A rule holding the
right dictionary still cannot CALL `unit()` with it. But an operation call in a rule body is a
CALL, and it carries its implicit argument like any other's: `unit()`'s `Monoid[T]` is the
clause's own `?d`, and the bridge builds B's `Frame::requirements` from it — positionally
against B's `dict_layout` — and pins from argument types only where a call carries none
(value-directed dispatch, the host entry). **NAR1X's acceptance row needs only this and local
derivation**: R's `Monoid[A]` is derived at crossing 1 from the ground operand, and `unit()`
reads it as its argument.

### 5.2.1 What was actually in the tree — MEASURED 2026-09-12, and this paragraph was wrong twice

**Wrong claim 1: "`resolve_bridge_requirements` answers `Unresolvable` and `call_op_bridged`
SUSPENDS."** It does not, for the shape the sentence names. `Zeroable.zero()` reaches
`call_op_bridged` on the SPEC op, and a spec sort declares no `requires` of its own, so the
resolution answers `NoneNeeded` and eval is asked to run an operation with **no implementation
at all**. The failure is one step EARLIER than the channel: nothing had SELECTED an impl. The
`Unresolvable` the paragraph names is real but is the SECOND failure — it is what the selected
impl hits when its own provision is conditional (`Wrap provides Zeroable[T = Wrap] :-
Zeroable[E]`), where the chain needs the element and a nullary call pins nothing.

**Wrong claim 2: that the typer must write anything new.** It need not, at this edge.
WI-1040's weave already rewrites a covered call to `Expr::ApplyWithin { requirements: [?d] }`,
and `reduce_op_value`'s arm for it already reads the dictionary and resolves the impl member
(`resolve_op_target_checked`). That IS the implicit argument and its reader; the weave simply
declined to reach a carrier-less callee, on a WI-1040 measurement ("weaving a body-less spec op
takes `require[PartialEq[T]], eq(?x, ?y)` from ONE solution to ZERO") that had since expired for
half its population — WI-1057 built the goal-shape reader a woven body-less callee needs
(`body_less_relation_arity`, read through `dispatched_relation_arity`'s woven-head arm), and the
row that measurement was taken on is BUILTIN-backed, which that reader refuses on its own.

**SO STEP 3 IS TWO EDITS, and they are two axes with two back-outs:**

| # | edit | site | what it fixes |
|---|---|---|---|
| 1 | the weave ADMITS a carrier-less body-less spec op | `collect_covered_calls` | nothing selected the impl — the goal answered `[]` |
| 2 | the woven call's dictionary CROSSES into the bridged frame, expanded by `expand_dispatching_dict` rather than re-resolved from argument types | `WovenDispatch` (`resolve.rs`) → `bridge_op_to_eval` → `call_op_bridged` | the selected impl's OWN chain had nothing to pin — the goal answered one INDEFINITE residual |

**AND THE READ IS PROJECTION, NOT PER-ENTRY RESOLUTION.** §4 describes the typer writing one
term per callee parameter. What ships at this edge hands over **one root** and lets
`expand_dispatching_dict` project `slots_for(owner)` out of it — 060-typedomains §4.1's
PROJECTION read, which that document argues is the one a rule can afford ("a head's arity is
fixed while a requires chain's length is not"). The two agree where it matters: a `?rₖ`
argument and a projection of the caller's root name the same dictionary. They differ where §4.1
of THIS note does — several INDEPENDENT roots per clause — and that is step 1's business, not
step 3's, because a rule→op edge has exactly one root: the `require` the weave covered the call
from.

**WHAT STEP 3 STILL DOES NOT DO.** The `Frame` spec field of §3 was not needed and was not
added: `expand_dispatching_dict` recomputes `__req_self`'s spec from `dispatched_from`, which
the woven call carries (the SPELLED spec op), so nothing had to be recovered from a frame. §3's
argument stands for the direction that reads slots BACK out of an eval frame — crossing 2's
capture — and is untouched.

**THE BOUNDARY CHECK NEEDED A CARRIER FOLD, and it is worth recording because the class
recurs.** A σ-bound dictionary reaches a rule body on the goal walk's occurrence carrier
(`Value::Node(Expr::Spliced(entity))`, WI-20260906-7YPGM), while `Dictionary::from_value` is
eval's one structural boundary check and is written against the `Value::Entity` shape eval
builds. Handing it the wrapper answers `None` and the call silently stops dispatching. The fold
is `as_bind_value`, the shared owner of "what does this carrier bind" — not a second unwrapper.

**THE PER-SLOT CORRESPONDENCE EXISTS ON THE RESOLVING PATH.**
`BridgeRequirements::Resolved(Symbol, Vec<(Symbol, ResolvedRequiresNode)>)` (`typing.rs:25760`)
is one tree PER SLOT keyed by the `synth_req_names` name, built by a zip over the chain
(`:25928`) — so an argument has a slot to land in. The loop's three failure arms — a SORT-half
`return Unresolvable`, NX4FD's recorded `Absent`, an OP-half `continue` — stay as they are for the
argument-less path; a call with arguments never reaches them, because the typer refused at load
what it could not write.

**THE HAND-OFF IS EXPLICIT, NOT AMBIENT.** A thread-local (the shape `BRIDGE_REENTRY_DEPTH` has at
`resolve.rs:10060`) would make B's dictionaries depend on who happened to be on the stack. The
arguments are threaded `reduce_op_value` → `bridge_op_to_eval` → `run_in_bridge_interp`'s closure
→ `call_op_bridged`. `bridge_op_to_eval` has three call sites, all inside `reduce_op_value`
(`resolve.rs:9827, 9841, 9872`); `run_in_bridge_interp` has three (`:10008`, `:10118`,
`simp_rewrite.rs:1715`), of which the last two are the eq bridge and simp firing, which have no
requirement caller and pass nothing.

## 6. What may still ride as a WRITTEN argument

`060-implementation.md` §7.3 measured the head-argument route for the TYPE channel and rejected it
for EXISTING heads: seven stdlib clauses under four predicates (`Set.eq`, `Set.subset`,
`Set.contains`, `Lattice.less`), **not one carrying a head bound**, 13 tests red, and the group
naming the reach drives `Set.eq` through the spec-op dispatch bridge, *"which builds its goal at
the WRITTEN arity"*. **That verdict stands and this design does not disturb it:** the implicit
arguments ride BESIDE the term, so no head's arity changes, the discrimination tree keys on the
written term alone, and a goal builder that knows nothing of them builds a goal with none — which
is a dynamic edge, and derives. Putting them INSIDE the term would be the same semantics at the
cost of that census; nothing here needs it.

**A DERIVED head is a different population, and `060-typedomains` may still use it.** Writing the
provider's `member(?x, ?d)` with the dictionary as a WRITTEN argument (§4.1, §5 there) costs no
existing site and needs no edge check: `apply_domain` is a DYNAMIC edge whose supply IS its
written argument, and the provider clause's `SortDomain` read is a fixed projection of it — that
document's §4.3 step 3, which an earlier draft of this note struck and should not have. The two
forms are alternatives and the choice belongs to that document, which still owes the census its
§6 records as missing — every arity reader, the discrimination key, the printer round trip.

## 7. Build order, with the control each step owes

1. **The sequence and the edge check (§2, §4).** Per predicate, `[RequiresEntry …]` from the
   clauses' reads (union over head column types, first-occurrence order, the disagreement check),
   with each clause's `?rₖ` indices; at every typed edge, the unification, the `resolve` under the
   edge's σ against the caller's sequence ∪ provisions, the implicit arguments written beside the
   body goal, and the refusals (`≥ 2`; a declared type with no answer). Acceptance: a predicate
   with a `require[X]` read LOADS with a readable sequence; a body goal's implicit arguments are
   readable; `a(?x: A) :- b(?x)` with `a` holding no `Eq[A]` is REFUSED naming `a`, `b` and the
   entry; two caller entries covering one callee entry are REFUSED naming both; two clauses
   reading one spec at different column types are REFUSED naming both. CONTROLS: a predicate with
   no read behaves exactly as today; an UNTYPED caller `a(?x) :- b(?x)` loads with `?fresh` —
   both passing either way by design, said at the site.
2. **The push binds the arguments — driven on the rule→rule edge.** Goals carry their implicit
   arguments through the seven goal-list constructions (§1); `with_fresh_vars` opens them with
   the body; the push binds `?rⱼ := tⱼ`. Acceptance: §1's `a(3, nil())` answers through `a`'s
   parameter, asserted by value with two suppliers; and §1's `r(?a1: A, ?a2: A, ?b1: B, ?b2: B)`
   cited from a caller holding `Eq[Int64]` AND `Eq[List[Int64]]` with the `B` columns empty
   answers with the right pair — the row a run-time match fails, because an unbound `B` is
   covered by both. CONTROLS: with the bind at the push removed, both rows DELAY (the local
   derivation is under-determined); with the push binding the callee's `?r`s to the CALLER's
   `?r`s by position instead of to the goal's arguments ("inherit"), a callee whose entry is at a
   different type answers the CALLER's supplier; a callee goal that delays and is re-asked after
   rotating behind the caller's remaining goals still reads the CALLEE's parameter — the row a
   per-frame carrier fails.
3. **Crossing 3 — the bridge reads the arguments. BUILT, WI-20260909-NAR1X, 2026-09-12**
   (`rustland/anthill-core/tests/include/nar1x_carrier_less_spec_op_test.rs`). Not as written
   above — see §5.2.1 for what the tree actually held. Delivered as TWO edits: the weave admits
   a carrier-less body-less spec op, and the woven call's dictionary crosses into the bridged
   frame. The `Frame` spec field of §3 was NOT needed. Acceptance, driven: a rule whose
   requirement is at a carrier-less spec op, entered as a ground test from a polymorphic
   operation, answers BY VALUE with two suppliers giving `3` and `5`. CONTROLS, measured per
   axis: with the weave admission backed out that row answers `0` where the truth is `1` — a
   WRONG answer, not a missing one, because a rule-defined `eq` whose clause cannot run is
   `Refuted`; with the dictionary hand-off backed out a conditional provider's row answers one
   INDEFINITE solution where the value is `103`; a rule whose op call HAS a carrier argument
   answers identically either way (BY DESIGN, and it is what says this serves only the
   carrier-less call); a supplied dictionary disagreeing with a UNIQUE local derivation fails
   loudly naming both (WI-860), which WI-1040's
   `a_clause_dictionary_crosses_a_rule_boundary_and_is_checked` already owns and this did not
   move.
4. **Crossing 2 — the capture.** The `Value::Relation` field, the evaluation at
   `build_relation_value` through `Frame::type_args`, the seed at `execute_logical_query` (§5.1).
   Acceptance: a citation consumed **after the creating frame has popped** — the row a
   frame-reading implementation fails; and the generative row, `member(?x)` with `?x` free cited
   at `g[Colour]`, which is 060-typedomains' own.
5. **Not in this note**: `apply_domain`, the typed-head sweep that generates the `SortDomain`
   reads, and the derivation of `provides SortDomain[…]` (`060-typedomains` §6 lists four
   placements and picks none).

## 8. What this does NOT settle

- **The hot-path cost** (§1's second point). A sequence per goal and one unification per entry
  per activation, expected to reduce to an `Rc` clone and an `is_empty()` for the overwhelming
  majority. Unmeasured, and it is the number this design owes first.
- **Whether the sequence is also WRITTEN on the head**, beside being derived from the reads. §2
  fixes the derivation and the disagreement check; a written form is surface, and adds a second
  statement of one sequence that must agree with the first.
- **The blast radius of the declared-type refusal once `SortDomain` reads are generated.** Every
  typed rule calling a typed rule must then hold or construct `SortDomain` for the callee's column
  types; a concrete caller constructs, an abstract one must declare. Measured nowhere yet, and the
  number that says whether `?fresh` needs to be wider than "fresh at this edge".
- **Whether a clause's body goals inherit the TYPE channel** — `060-implementation.md` §7.3's own
  open question. Not needed for the requirement passing, which is positional; open for a body
  goal that carries no bound of its own and must enumerate.
