# Proposal 058 — Modular instances: selecting a non-canonical provider at a use site

**Status:** Draft (2026-07-25). Design phase of WI-648. **Recommendation: explicit selection first, implicit scoped selection deferred** — and, consequently, an **amendment to `kernel-language.md` §Instance coherence**, whose per-`import` promise is not merely unimplemented but *cannot express either driver* (§3).

**Tracks:** WI-648 (design + implement). WI-817 depends on it for its provider-selection dimension.
**Driving clients:** `SortedSet` / sorted `Map` ordered by a *chosen* comparator (the ticket's standing example); `Int64` carrying **both** the additive and the multiplicative monoid (the deciding argument, §1).
**Depends on:** [042-explicit-type-parameters-on-operations](042-explicit-type-parameters-on-operations.md) (the call-site `[bindings]` channel this reuses — already parsed and lowered, §2.2), [020-bracket-type-parameters](020-bracket-type-parameters.md) (the `[bindings]` syntax), WI-431 (instance facts — the op-binding declare form), WI-448 (op-scoped `requires`), WI-450 (witness sorts — the named declare form).
**Related:** [library/004-partial-vs-total-equality-and-ordering](library/004-partial-vs-total-equality-and-ordering.md) (its "Out of scope — modular typeclasses" clause defers exactly this; §6 here spells out the interaction), WI-577 (first-class `Dictionary[S]` values — §7.1 explains why they do not supply a *named* slot), WI-300 (rule-body requirement goals), [`design/operation-call-model.md`](../design/operation-call-model.md) (the `requirements` channel and `resolve`), [`design/requirement-dictionaries.md`](../design/requirement-dictionaries.md) (what the dictionary *is*), [`design/spec-instance-dispatch.md`](../design/spec-instance-dispatch.md) (§Coherence — options A/B/C; this proposal is neither, see §8).
**Affects:** `docs/kernel-language.md` §Instance coherence (amended) + §5.4 (named requirement slots); `rustland/anthill-core/src/kb/typing.rs` (`seed_op_type_args`, the two load-time coherence checks, the dispatch classifier); `rustland/anthill-core/src/kb/load.rs` (`build_call_type_args`); grammar (the `requires name: Spec[…]` binder, §4.7 — the *select* surface itself needs **no** grammar change); `stdlib/anthill/prelude/` (`SortedSet`, later). Runtime: **none new** (§5.3). Rust + scaland.

---

## 1. Problem

**`Int64` cannot carry both the additive and the multiplicative monoid.** An algebraic-specification language must be able to state both structures — `5` is an element of `(Int64, +, 0)` and of `(Int64, ×, 1)` — but in Anthill, declaring two providers of one spec for one carrier does not load. And even if it did, a call `Monoid.combine(a, b)` has no way to say which of the two it means: the call must run one body, and nothing in the program picks it.

Measured (probe run 2026-07-25, `try_load_kb_with`, both diagnostics verbatim):

```anthill
sort Monoid  sort T = ?  operation combine(a: T, b: T) -> T  operation unit() -> T  end
sort AddM   fact Monoid[T = Int64]   operation combine(a: Int64, b: Int64) -> Int64 = add(a, b)  …
sort MulM   fact Monoid[T = Int64]   operation combine(a: Int64, b: Int64) -> Int64 = mul(a, b)  …
sort Use    operation go(a: Int64, b: Int64) -> Int64 = Monoid.combine(a, b)                     end
```

```
20:49: type mismatch in Monoid.combine.dispatch: expected unique impl for per-call bindings,
       got multiple impls match (coherence rule)
ambiguous witness: 2 distinct witness sorts provide 'Monoid' for carrier 'anthill.prelude.Int64'
       (keep exactly one)
```

Two independent refusals fire: the **per-call-site** one (`typing.rs:10731`) and the **load-time global** one (`typing.rs:15999`; the instance-fact flavor is `typing.rs:15937`). Both diagnostics name the missing capability by name — *"there is no way to select between them (scoped/named instance selection is not yet supported)"* (`load.rs:726`, `:731`).

The second one does not depend on the call at all. Delete `sort Use` from the program above — leaving `AddM` and `MulM` and nothing that calls `Monoid.combine` — and the load still fails with the same *"keep exactly one"*. What Anthill rejects is the pair of declarations; the question of which monoid a call wants is never reached.

The stdlib works around this by **bundling**: `algebra.Ring` (`stdlib/anthill/prelude/algebra.anthill:28`) declares `add`/`sub`/`mul`/`zero`/`one` in one spec, so the two monoids never appear as two instances. That is the Num-style dodge — it works for a fixed pair known in advance and does not generalize (a fold over `max`, over `∧`, over string concatenation).

**The same refusal, in its committed form,** is `two_describers_for_one_carrier_rejected_globally` (`rustland/anthill-core/tests/include/wi817_polyrec_requirement_test.rs:662`) — a *selection-discriminating* fixture: `LoudDesc.describe = 5`, `QuietDesc.describe = 7`, a lambda created in the loud scope and invoked from the quiet one. Scoped-correct is **75**, both-loud **55**, both-quiet **77**. It is the acceptance program.

### 1.1 What is already permitted, and why it decides the shape

The witness-coherence check **already exempts** providers whose carrier is *concrete* (`typing.rs:15977`):

> a **concrete** provider (with constructors) is a backend whose VALUES carry their own sort, so value-directed dispatch distinguishes them by the value … NOT an ambiguity.

So Anthill already ships a two-instances-per-spec rule, and its criterion is exactly §1's — **it asks whether the CALL has one answer**, not whether the fact base does: with a concrete provider the value answers, so two providers are no ambiguity. This proposal changes nothing about that criterion. It supplies a way for the call to be answered in the other case, where the value is silent — and moves the refusal to the call that picks no variant (§4.1 tier 3).

---

## 2. What exists today (measured inventory)

### 2.1 Declare — two forms, one of them already named

| form | example | identity | named? |
|---|---|---|---|
| **witness sort** (WI-450) | `sort QuietDesc  fact Desc[T = Pebble]  operation describe(…) = 7  end` | the provider **sort symbol** | **yes** — `QuietDesc` |
| **instance fact** (WI-431) | `fact Monoid[T = Int64, combine = add]` | the bindings it asserts | **no** |

`SortProvidesInfo(sort_ref: Term, spec: Term)` (`stdlib/anthill/reflect/reflect.anthill:687`) carries **two fields and no declaring scope**. This is load-bearing for §8: a scope-distance rule needs provenance that is not recorded; explicit selection needs only `sort_ref`, which is.

### 2.2 Select — the surface already parses, and today means nothing

Call-site brackets (`f[T = X](args)`) parse into a `type_args` named-arg channel (`parse/convert.rs:1724`), lower via `build_call_type_args` (`load.rs:9249`) to `(Option<Symbol>, Value)` pairs, and are consumed by `seed_op_type_args` (`typing.rs:12912`). Measured, four probes:

| program | today |
|---|---|
| `idy[Bogus = Int64](n)` — callee **has** type params | **loud**: `unknown type-param 'Bogus'` |
| `plain[Bogus = Int64](n)` — callee has **no** type params | **loads clean — silently dropped** |
| `go[Desc = QuietDesc](pebble())` — a spec-name binding | **loads clean — silently dropped** |
| `idy[Id.T = Int64](n)` — a **qualified** spelling of a *real* type param | **loud**: `unknown type-param 'Id.T'` — the key is a bare label and the channel has **no resolution rung** (§4.2) |

The silent drop is `typing.rs:12925`: `if type_args.is_empty() || op.type_params.is_empty() { return Ok(()) }`. It is a "loud error over silent skip" violation in its own right, and it is a **hazard for this proposal specifically**: the surface below is *already accepted and already inert*, so a program written against it would load silently wrong before the typer leg lands. Closing it is a prerequisite (§9 phase 0), not a nicety.

### 2.3 Thread — complete, and needs nothing new

A resolved instance already rides as a **dictionary**: `Value::Requirement(handle)`, a `(functor, [sub-requirements])` tree in a refcounted arena (`design/requirement-dictionaries.md` §1). It is built by `construct_requirement(impl, [...])`, read by `var_ref(__req_*)`, and supplied per call — `callee.frame.requirements = caller.apply_within.requirements` (`design/operation-call-model.md` §"Dispatch site"). The runtime **is already parameter-inserted dictionary passing**; the design doc names Scala's `using` explicitly. `resolve(goal, scope)` already returns `ResolvedTree = leaf | conditional | from_scope`, and the cross-sort constructing case already emits a `dispatch_dict` at classification (WI-829, `typing.rs:8610`).

Selecting an instance therefore adds nothing to the threading. The whole change is **where the `impl` in `ResolvedTree::leaf { impl }` comes from**: the call site, instead of a search.

---

## 3. The three-way divergence, and the ruling

Three texts describe three different rules; none matches the code.

| source | rule |
|---|---|
| `kernel-language.md:2109`, `:2111` | **per-scope**: "different scopes may resolve the same `Spec[carrier]` to different providers, the per-`import` choice" |
| WI-648's framing | **global default + named opt-in** |
| the implementation | **global**, unconditional, refused at load (§1) |

**Ruling: the spec's per-`import` text is not merely unimplemented — it cannot express either driver, so it is the text that must change.**

- The deciding argument needs **both monoids in one body**: `fold[Monoid = AddM](xs)` beside `fold[Monoid = MulM](ys)`. Per-`import` selection admits at most one provider per scope, so no scope can write both.
- `SortedSet.new(cmp)` chooses per **construction site**, not per scope; two differently-ordered sets routinely coexist in one function.
- Per-`import` selection is also *implicit*: adding an import silently changes what existing code computes, and §2111 concedes the consequence — "a diamond whose arms captured providers from different scopes may observe different `A[X]` behavior". That is the Haskell orphan-instance hazard, adopted as the default rather than opted into.

The amendment is in §10. It **narrows a promise the code never kept**, so no loading program changes meaning.

---

## 4. Design

### 4.1 The coherence ladder

Selection at a spec-op call site resolves in order:

1. **Explicit selection** at the use site — highest precedence, `[Spec = Witness]` (§4.2). Explicit beats implicit, always.
2. **The unique provider** for `(spec, carrier)` — today's rule, unchanged. Programs that load today load identically.
3. **Two or more providers and no explicit selection** — a **loud error at that use site**, naming the candidates.

The change from today is entirely tier 3: the refusal moves **from load time to the unselected use site**. Two instances may now *coexist*; what is refused is an *unselected* dispatch against them. Nothing becomes silently dispatched — an ambiguous site that says nothing is still an error, with a better message (it can name the witnesses and the syntax that picks one).

### 4.2 Select — surface

Reuse the call-site bracket channel, keyed by the **requirement slot** rather than by a type parameter:

```anthill
operation fold[T](xs: List[T]) -> T requires Monoid[T]     -- 042 type param + op-scoped requires (WI-448)

fold[Monoid = AddM]([2, 3, 4])            -- 0 + 2 + 3 + 4 =  9
fold[Monoid = MulM]([2, 3, 4])            -- 1 × 2 × 3 × 4 = 24
fold[T = Int64, Monoid = AddM]([2, 3, 4]) -- both channels in one bracket list
```

The key names a requirement the callee declares; the value names a **witness sort**. **No grammar change** — this is the production 042 already added and `parse/convert.rs` already lowers (§2.2).

**Two slots of one spec** need a name per slot. A named slot is written as a **type parameter carrying a bound** (§4.7) — the witness is the *supplier*, so the clause is `provides`:

```anthill
operation biFold[T, plus { provides Monoid[T] }, times { provides Monoid[T] }](xs: List[T]) -> T

biFold[plus = AddM, times = MulM](xs)
```

Resolution of a bracket key, in order: (1) a declared **type parameter** name — today's meaning, unchanged and first, so no existing program shifts, and it now *subsumes* the named-slot case, because a named slot **is** a type parameter; (2) a requirement's **spec short name**, when unambiguous among the callee's remaining (anonymous) requirement slots. Anything else is a **loud error** — including on a callee with no type parameters, which is the §2.2 silent drop closed.

**A key is a bare LABEL, so rule (2) is a name LOOKUP — not a short-name comparison of two identities.** The distinction is WI-672's, and it is load-bearing here because "matches on short name" is what that work *deleted*:

- Rule (1) matches by **symbol identity** — `n == name_sym` (`typing.rs:12931`) — because both sides are the bare spelling: a written key lowers to a bare interned `Symbol`, *"the param label (`A`) … **NOT a caller-scope value**"* (`build_call_type_args`, `load.rs:9249`), and `op.type_params` holds `kb.intern("T")` (WI-708, `typing.rs:12892`, whose doc says the bare symbol *"stays the call-site / seeding key"*).
- Rule (2) **cannot** match by identity: its candidate set is *derived* from the slots' **canonical spec symbols**, which are qualified. Crossing bare-label → qualified-symbol is exactly `same_label`'s sanctioned family 2 — *"a type-param binding key matched WITHIN an already-established same-spec context … the same-spec gate makes short names unique"* (`typing.rs:11328`). **The "unambiguous among the callee's remaining slots" clause IS that gate**, not a courtesy: without a gate this is the unsound identity comparison whose owners are `same_sort_canonical` / `same_qname`, *neither of which matches on last segment*.

**A qualified key is refused, not resolved.** Rule (1) already refuses one — §2.2's fourth row, measured: a *qualified spelling of a real type param* is `unknown type-param`, while the bare key loads. Rule (2) adds no rung either, so `fold[algebra.Monoid = AddM]` is a loud error, and `same_label`'s own `debug_assert` (`typing.rs:11336`) fires on the partially-qualified pair (`algebra.Monoid` vs `anthill.prelude.algebra.Monoid`) if one tries to match it. Three reasons, in order of force:

1. **A resolved key would be a second name law in one bracket list.** Rule (1)'s key is unresolvable *in principle* — `T` is a binder of the *callee*, visible in no scope — so a ladder mixing the two would rank a label against a reference, and resolve-then-fall-back-to-label is a fallback (`CLAUDE.md`: "avoid fallbacks, better know about errors early").
2. **It would make selection depend on the caller's imports.** Measured: a cross-namespace call into a `requires`-carrying callee (`sort Lib  sort LT = ?  requires Desc[T = LT]  …`) from a namespace that **never imports `Desc`** loads clean; structurally, the supply path takes no scope at all — `build_concrete_dispatch_dict(kb, subst, callee_spec_sort, caller_sort, caller_requires, rigids)` (`typing.rs:11700`) reads provider facts and resolved symbols only. (Load-strength: the clean load is measured, the threaded dictionary was not driven to a value.) So a callee whose `requires` names `a.Monoid[T]`, called from a scope that imported `b.Monoid`, would be refused at a *one-slot* call with nothing ambiguous about it. A short name is the only spelling either side can write without consulting the other's imports. The **value** half is caller-resolved and must be — it denotes a witness the caller picks, which is what §10's "an import governs *visibility*" governs.
3. **It buys no expressiveness** — every selection a short name cannot express is written with the §4.7 binder instead ("When the short name does not discriminate", below).

**A direct spec-op call is the same case.** `Desc.describe(w)` has no `requires` slot of its own — the thing being selected is the *dispatching dictionary*, `requirements[0]` (`design/operation-call-model.md` §"Dispatch site"). Rule (2) therefore also admits the **dispatched spec's own short name**:

```anthill
Desc.describe[Desc = LoudDesc](w)      -- pick the provider backing this very call
```

One key, one meaning, whether the spec arrives as a callee's requirement or as the call's own dispatch target.

**When the short name does not discriminate, the binder does.** Two anonymous slots of the *same* spec (`requires Monoid[T], Monoid[U]`), or of two specs sharing a last segment (`a.Monoid` and `b.Monoid`), leave rule (2) with no unique answer — that *is* the loud error, and the fix is to **name** the slot (§4.7), which makes it a type parameter and so puts it under rule (1). Rule (1) is therefore the **complete** mechanism and rule (2) a gated shorthand: no expressible selection depends on the short name, which is why refusing a qualified key costs nothing.

**Shadowing guard.** An operation that declares a type parameter whose name collides with one of its own requirement **spec short names** is refused **at the declaration**, not at the call. One name, one channel. Binder-vs-parameter collision is no longer a separate case: a named slot *is* a parameter, so the ordinary duplicate-parameter rule already covers it — one more thing the bound form removes rather than adds.

### 4.3 Declare

Witness sorts need nothing — they are already named (§2.1). Instance facts (`fact Monoid[T = Int64, combine = add]`) have no name; two of them for one `(spec, carrier)` therefore stay refused at load exactly as today. Naming them is a possible later increment (`fact AddM: Monoid[…]`); it is **out of scope** here, and the diagnostic should say so rather than imply a selection that cannot be written.

### 4.4 Validation at the selection site

Given `f[Spec = W](…)`, the typer checks:

1. `W` provides `Spec` at the call's bindings — i.e. a `SortProvidesInfo(sort_ref = W, spec = Spec[…])` whose spec view unifies with the goal. A witness that does not provide the goal is a loud error naming both.
2. The slot exists on the callee (§4.2 resolution order).
3. The selection is **not** applied to a call whose dispatch is already value-directed on a concrete carrier (§1.1) — there, the value decides and an explicit witness would silently contradict it. Refuse, do not prefer.

### 4.5 Resolve — one hook

`resolve(goal, scope)` (`design/operation-call-model.md` §Algorithm) gains a **step 0**: if the call site explicitly bound this goal's spec, return `ResolvedTree::leaf { impl: W, type_args }` after check (1). Steps 1–4 are untouched — a conditional witness still recursively resolves its own `:-` subgoals, and its sub-resolutions may themselves be explicitly selected at the same site.

### 4.6 Thread — nothing

`ResolvedTree::leaf { impl: W }` is emitted as `construct_requirement(W, [...])` in the callee's `requirements[0]` (or the named slot), by the machinery that already emits it for a searched result (§2.3). A body that forwards its own requirement (`var_ref(__req_monoid)`) forwards the selected one automatically — so `fold[Monoid = AddM](xs)` reaches `Monoid.combine` inside `fold`'s body with no per-call plumbing.

### 4.7 A **named** requirement slot is a parameter; an **anonymous** one is a constraint

This is the rule that resolves the `SortedSet` type-identity question, and it is worth stating on its own because it is what makes `SortedSet` work without new type machinery.

**Measured — type identity keys on declared type parameters, and on nothing else:**

| probe | result |
|---|---|
| `Option[T = Int64]` returned where `Option[T = String]` declared | loud: `expected Option[T = String], got Option[T = Int64]` |
| `Box[E = Pebble, Desc = QuietDesc]` — bind a `requires` slot in type position | loud: **`Box` has no type parameter named 'Desc' — it declares type parameter(s) E** |
| `sort Box  sort E = ?  sort O = ?  end`, `Box[E = Pebble, O = QuietDesc]` vs `…O = LoudDesc` | loud: `expected Box[E = Pebble, O = LoudDesc], got Box[E = Pebble, O = QuietDesc]` |
| the same two bindings **agreeing** | loads clean |

So a **witness sort binds an ordinary type parameter today**, and two different witnesses in one parameter are already two distinct types, refused by the existing checker with **no new mechanism at all**. What a `requires` slot lacks is not expressiveness — it is a *name*.

Hence the rule:

- **`requires Eq[T]`** (anonymous) — a *constraint*. Solve it, do not record it. `List[T = Int64]` is one type no matter which `Eq` witness satisfies it, which is correct: the `Eq` instance is incidental to what a list *is*.
- **`requires O: Ordered[T]`** (named) — a *parameter*. It is addressable by name in brackets, in **type** position as well as at a call, so `SortedSet[T = String, O = ByLength]` and `SortedSet[T = String, O = Alphabetical]` are different types. That is correct too: the ordering is not incidental to what a sorted set *is*.

**The author chooses by naming it**, and the choice is visible in the declaration. The same rule holds at both levels — an operation's named binder (§4.2) is addressable in that operation's bracket list; a sort's named binder is addressable in that sort's type application. One rule, two scopes.

Two consequences to keep honest:

- **The binder is new grammar, and namelessness is currently deliberate.** `requires d: Desc[E]` does not parse (measured: `syntax error near ': Desc'`). The two existing productions carry no name slot — `requires_declaration: 'requires' <type>` (sort/namespace-level, a bare **type**) and `requires_clause: 'requires' <rule_body>` (op-scoped, WI-448). `design/operation-call-model.md` states the current property outright: sub-requirements are *"positional and nameless (impl-side `requires` clauses have no source-level names)"*. The *select* surface needs no grammar change (§4.2); the *declare* binder does. Three wrinkles, all found by reading the productions rather than assumed:
  1. **The op-scoped clause is overloaded.** One `rule_body` list holds both spec requirements (`operation member(x: T, l: List) -> Bool requires Eq[T]`, `stdlib/anthill/prelude/list.anthill:58`) and value **preconditions** (`requires neq(b, 0), gt(b, 0)`, WI-539). A binder attaches only to the *type* flavor and must coexist with predicates in the same comma list. The sort-level form takes a type only, so it is clean there.
  2. **`d: Desc[E]` sits next to named-argument syntax** inside a `rule_body` (`f(x: 1)`). A bare `name: Type` is not valid at rule-body top level today, so the extension is available — but `requires_clause` already needs `prec.dynamic(1)` to win a GLR tie against `requires_declaration`, so this wants a corpus test, not an assumption.
  3. **The binder names the top-level slot only.** Sub-nodes inside a `ResolvedSortNode` stay positional (`requirement_at_sort(node, k)`), exactly as today. Phase 1 adds a name where a name was missing; it does not re-key the projection path.

  Related spec refinement for phase 5: `kernel-language.md:909` describes operation-level `requires` as *preconditions on individual operations*, which is right and needs only to be **split in two** — a **value** precondition (`requires neq(b, 0)`, WI-539), and a **type** precondition (`requires Ord[T]`, WI-448). The implementation already draws that line: the call-site contract check filters to the value goals via `is_value_precondition_clause`, leaving the type ones to dispatch.
- **Adding a binder to an existing sort adds a parameter.** Bindings are by name, so omitting it stays legal and it infers — resolving to the unique provider by §4.1 tier 2. If it cannot be inferred and has no unique provider, that is `UnconstrainedTypeParam` — loud, and right.

### 4.8 Reading `requires` as a goal — why the binder is not a new kind of thing

The named binder is best explained as **sugar over machinery Anthill already has**, in the language's own idiom. The demand/supply relation is already a rule in the reflect layer:

```anthill
-- stdlib/anthill/reflect/typing.anthill
rule provides(?A, ?S_inst) :- SortProvidesInfo(sort_ref: ?A, spec: ?S_inst)
```

whose own comment names the framing: *"The demand/supply twin of `refines`: `requires X` and `fact X[Y]` are the two ends of one relation."* Read that way, a `requires` clause **is a goal**, and its witness is the goal's answer:

| surface | reading |
|---|---|
| `requires Ord[T]` | the goal `provides(?W, Ord[T])` must be solvable; **`?W` is discarded** |
| `requires O: Ord[T]` | `sort O = ?`, plus the goal `provides(O, Ord[T])`; **the answer is bound to a name** |

That is the whole content of §4.7: the anonymous form cannot appear in a type because *nothing named its witness*; the named form can because it is an ordinary bound variable. Nothing new is introduced — a name is given to an answer that was always being computed.

The rest of the proposal falls out of the same reading:

| concept | as a goal |
|---|---|
| the requirement dictionary | the **witness** of `provides(?W, Spec[…])`. `design/operation-call-model.md` says it verbatim: `construct_requirement` builds *"the SLD resolution chain materialized"* |
| instance resolution | SLD search for `?W` |
| **global coherence** | a demand that the goal's answer set be a **singleton** |
| **ambiguity** (§1) | a **call** that picks neither of two answers. The two-answer goal itself is ordinary |
| **explicit selection** `f[Ord = ByLength](…)` | **pinning the variable before asking**: the goal becomes `provides(ByLength, Ord[…])`. Both answers still exist — the call has named the variant it wants, rather than the goal having become single-answered |

So §4.1's ladder is not a new coherence policy bolted on: it says *pin the variable; or leave the search to answer with a single witness; or, when it answers with several and the call pinned none, be told so at that call*. And §4.4's validation is just checking that the pinned value satisfies the goal it was pinned into.

**One distinction the reading must keep.** An op-scoped `requires` carries **two kinds of precondition** — and both are goals, so what separates them is not the goal but what is kept:

> a **value** precondition (`requires neq(b, 0)`, WI-539) keeps the goal's *success*; a **type** precondition (`requires Ord[T]`) keeps its *answer*, the witness.

The binder names that answer. This is an explanation, **not a working desugaring today**: writing `requires provides(O, Ord[T])` in a body parses (the clause takes a `rule_body`) but is treated as a precondition — proved and discarded — so no dictionary is threaded. Stated so no reader mistakes the synonym for an available spelling.

---

## 5. Worked examples

### 5.1 Two monoids on one carrier (§1's program)

The two witnesses coexist (§4.1 tier 3 no longer refuses them at load); every site that says which resolves by tier 1. The unselected `Use.go` becomes an error naming `AddM`/`MulM` and the syntax that picks one — the diagnostic moves from the *declarations* to the *one call that is actually ambiguous*. Adding `[Monoid = AddM]` to it makes the program load and compute `add`.

### 5.2 The committed fixture

`two_describers_for_one_carrier_rejected_globally` flips, with one selection written per site:

```anthill
LoudOps.run:     QuietOps.invoke(lambda w -> Desc.describe[Desc = LoudDesc](w), z)
QuietOps.invoke: add(fn(z), mul(10, Desc.describe[Desc = QuietDesc](z)))
```

The lambda's selection is resolved where the lambda is **created** and rides its captured `frame.requirements` (`reduce_lambda` snapshots them — `design/requirement-dictionaries.md` §1), so the quiet caller invoking it still gets 5: **5 + 10·7 = 75**. **55 or 77 is a failure, not a variant** — either betrays a both-one-way selection, which is the whole point of the fixture. The test's own doc already records 75 as the WI-648 acceptance value.

### 5.3 `SortedSet` — the driver, threaded end to end

**Declare.** The ordering is *not* incidental to a sorted set, so its slot is **named** (§4.7) and thereby becomes a type parameter:

```anthill
sort SortedSet
  sort T = ?
  requires O: Ord[T]                                            -- NAMED ⇒ a parameter of the type

  operation empty()                                    -> SortedSet[T = T, O = O]
  operation insert(s: SortedSet[T = T, O = O], x: T)   -> SortedSet[T = T, O = O]
  operation union(a: SortedSet[T = T, O = O],
                  b: SortedSet[T = T, O = O])          -> SortedSet[T = T, O = O]
  operation toList(s: SortedSet[T = T, O = O])         -> List[T = T]
end

sort ByLength      fact Ord[T = String]  operation compare(a: String, b: String) -> Int64 = … end
sort Alphabetical  fact Ord[T = String]  operation compare(a: String, b: String) -> Int64 = … end
```

Two providers of `Ord[String]` now **coexist** — §4.1 tier 3 no longer refuses them at load; only an *unselected* dispatch is an error.

**Select**, at the construction site — the ordinary §4.2 bracket path, no new surface:

```anthill
let a = SortedSet.empty[T = String, O = ByLength]()
let b = SortedSet.empty[T = String, O = Alphabetical]()
```

**Thread** — nothing new (§4.6). `insert`'s body calls `Ord.compare(x, y)`; that resolves through slot `O`, which the caller filled with `construct_requirement(ByLength, [])`. `a` and `b` carry different dictionaries at run time because they were constructed with different ones.

**And the merge hazard is caught statically, today, by the existing checker:**

```anthill
SortedSet.union(a, b)
-- expected SortedSet[T = String, O = ByLength], got SortedSet[T = String, O = Alphabetical]
```

That is measured type behaviour (§4.7's third probe), not a proposed check. `union` needs no special rule; it is ordinary parameter agreement.

**Omitting the binding keeps existing code working.** `SortedSet.empty[T = Int64]()` leaves `O` to inference, which resolves it to the unique `Ord[Int64]` provider by tier 2 — the same program you write today, meaning the same thing.

There is no remaining gap here: a comparator cannot be chosen at run time at all, and the abstract case is ordinary polymorphism — §7.1.

---

## 6. What this does not change: `Eq` / `Ord`, and `Map[K = Float]`

§5.3 chooses a comparator for a container, so a reader will ask whether the same bracket can choose an `Eq` for `Map[K = Float]`. It cannot, and the two mechanisms are orthogonal:

- The `PartialEq` / `Eq` / `PartialOrd` / `Ord` hierarchy is untouched. Explicit selection picks *among providers of a spec*; it does not change which spec a carrier provides, nor whether `Eq`'s reflexivity law is checked. `Float` provides `NonEq`, not `Eq` (`float.anthill:71`), and no bracket key alters that.
- **`TotalFloat` remains the answer for `Map[K = Float]`.** A container's key requirement is embedded in the **sort** — `requires Eq[T = K]` (`map.anthill:7`), `requires Eq[T]` (`set.anthill:10`) — a slot that is **anonymous**, so by §4.7 it is a constraint and stays out of `Map`'s type identity, which is why no key can address it. Naming it would be a different (and wrong) design: two `Map[K = Int64]`s must not differ by which `Eq` satisfied them. The newtype changes the *type*; selection changes the *witness*.
- **That embedded requirement is not enforced today**, so `Map[K = Float]` loads clean (measured 2026-07-28). It is WI-644's one outstanding acceptance item — *"`Map[K=Float]` is a load error, `Map[K=TotalFloat]` loads"* — deferred 2026-07-08 and currently **unowned**: WI-644 is `Delivered`, and WI-658's pointer to "sibling WI-649" is stale (WI-649 is the reify cyclic-σ ticket). This proposal neither causes nor closes that gap; it is recorded here so §6 is not read as describing a check that runs.

---

## 7. Consequences, and what is genuinely left open

### 7.1 There is **no** runtime-chosen order — settled, not deferred

An earlier draft of this section deferred "a comparator chosen at run time" to an existential. That was wrong, and the reason is worth stating, because it is what makes §4.7 safe rather than merely convenient.

**An order cannot be conjured at run time.** Every witness is a *sort*, declared in the program text. At run time a dictionary can only be copied from one that was already chosen during typing — there is no operation that builds a new witness. So "runtime choice" only ever means *which statically-pinned branch executed*, and that is expressible with ordinary universal polymorphism, which already works:

```anthill
operation report[T, O](s: SortedSet[T = T, O = O]) -> String   -- O abstract: usable, unnameable

if cfg then report(SortedSet.empty[T = String, O = ByLength]())
       else report(SortedSet.empty[T = String, O = Alphabetical]())
```

`report` calls `Ord.compare` through slot `O` and can never *name* which order it received. That is precisely the abstract case — and the branch lives at the **call**, where each side is statically pinned, not in the type. Nothing is unwritable.

**Why a first-class `Dictionary[S]` value cannot erase it either.** WI-577's own design already puts the witness on the static side: the runtime slot carries only `(functor, sub-handles)`, and *"the witnessed spec is not recoverable from the value … the spec lives in the **type** (`S`), which the typer already has"* (`design/requirement-dictionaries.md` §2.5); the value face is deliberately **accessor-only** (§2.3). A dict *value* may therefore fill an **anonymous** requires slot — a constraint records nothing in the type, so nothing is erased. It cannot fill a **named** one, and not by prohibition: a named slot **is a type parameter** (§4.7), and a value does not determine a type. The two channels do not mix, by construction rather than by rule.

**The one residual existential** — a heterogeneous collection holding sets of *differing* orders, `List[SortedSet[T = String, O = ?]]` — is not a `SortedSet` question and not this proposal's to answer. It is the general existential the design already names elsewhere: *"bare `Dictionary` (S unknown) **is** the existential form"* (§2.5). If Anthill wants it, it wants it uniformly (WI-402, `design/path-dependent-types.md`); this proposal neither needs nor forecloses it.

### 7.2 Codegen

The C++ backend rejects `lambda_within` today for want of a static record of which dictionaries a closure needs (WI-817's note). Explicit selection makes that record *more* static, not less — the selected witness is a load-time constant — so this is expected to help. Not verified; verify before claiming it.

---

## 8. Rejected alternatives

- **Scoped implicit selection first** (`spec-instance-dispatch.md` rule B — scope distance + import-edge constant *K*). Rejected as the *first* increment, not on principle: it needs declaring-scope provenance that `SortProvidesInfo` does not record (§2.1), it needs *K* and a tie policy settled (the design doc's own reason for staying at rule C), it is implicit — so an import silently changes results — and it still cannot express the deciding argument (§3).
- **Last-wins** (`spec-instance-dispatch.md` option A). Order-dependent across module loads; silently picks. Contradicts the repository's "loud error over silent skip" principle.
- **Keep the global rule, wrap instead** (the newtype-per-order status quo). Already available, and library/004 uses it deliberately for `TotalFloat`. It does not scale to the algebra case: a newtype per monoid means `Int64`'s arithmetic must be re-exported per wrapper.
- **A new keyword** (`using` / `given` block). More surface for the same effect; the bracket channel already parses, already lowers, and already carries type arguments through the identical frame slot (§2.2, §2.3).

---

## 9. Build order

| phase | content | acceptance |
|---|---|---|
| **0 — prerequisite** | close the §2.2 silent drop: an unmatched bracket key is a loud error even when the callee declares no type params | `plain[Bogus = Int64](n)` fails to load; the existing `NoSuchTypeParam` message is reused |
| **1 — declare** | grammar + loader for the named binder `requires name: Spec[…]`, on an **operation** and on a **sort** (§4.7); the §4.2 shadowing guard | a two-slot op loads; a named sort-level slot is addressable in type position (`Box[E = …, O = …]`); a colliding type-param name is refused **at the declaration** |
| **2 — select** | bracket key → requirement slot (§4.2 order, incl. the direct spec-op case); witness validation (§4.4); `resolve` step 0 (§4.5) | `fold[Monoid = AddM]` / `[Monoid = MulM]` compute `9` / `24` on `[2,3,4]`; a **qualified** key (`[algebra.Monoid = AddM]`) and a short name ambiguous across two anonymous slots are each a **loud error** naming the slots |
| **3 — coherence** | move the two-provider refusal from load to the unselected use site (§4.1 tier 3) | the §1 program loads; `two_describers_…` flips to **75** (55/77 fail); every current single-provider program is unchanged — **full suite green** is the control |
| **4 — `SortedSet`** | the stdlib driver on phases 1–3 (§5.3) | two orderings coexist; `union` of a `ByLength` set and an `Alphabetical` one is a **type** error; omitting `O` still resolves to the unique provider |
| **5 — spec** | amend `kernel-language.md` §Instance coherence (§10); document §5.4 named slots + the §4.7 named-vs-anonymous rule | spec and implementation agree, which is what §3 says they do not today |
| **deferred** | named instance facts (§4.3); implicit scoped selection (§8); the general existential (§7.1 — *not* a `SortedSet` blocker) | — |

Phases 0–3 are one WI-648 implementation arc; each is independently green. Phase 4 is the driver landing and is what makes phases 1–3 worth having. scaland mirrors phases 1–2 (it has no operation loading — the divergence is pre-existing).

**Note on phase 1's cost.** The binder is the only grammar in the proposal, and it is what buys §4.7 — so it is not optional plumbing: without a *name*, a witness cannot enter a type, and `SortedSet`'s merge hazard has no static answer.

---

## 10. Spec amendment (`kernel-language.md` §Instance coherence)

Replace the per-`import` promise with the ladder actually implemented. Proposed text:

> **Instance coherence.** A spec has at most one *default* provider for a given carrier. A second provider is permitted — but every dispatch against that carrier must then say **which**, by binding the requirement slot at the call: `fold[Monoid = AddM](xs)`. An unselected dispatch with two candidates is an error naming both. A sort's *embedded* requirements — the providers filling its `requires` slots — are resolved in **that sort's** scope and captured when its instance is constructed, so `Spec[carrier]` behaves consistently within any one instance. Selection is therefore **explicit and per-call**, not per-scope: two routes to `A[X]` agree unless a call site deliberately says otherwise. (Implicit scope-directed selection — a nearer provider silently winning — is deliberately **not** the rule; see proposal 058 §3.)

The sentence at `:2109` ("A consumer chooses which instantiation to use via `import`") is likewise replaced: an import governs *visibility*, and among visible providers the call selects.
