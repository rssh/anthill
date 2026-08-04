# 059: Companion Members — a sort's scope, entered twice

## Status: Draft (2026-08-04). Written from WI-975, which asked what a second declaration of one name means and found two mechanisms sharing one spelling. **A type is defined once; a `namespace` at its address is a second ENTRY to that type's scope, not a separate module attached to it.** Every claim below is measured against the Rust loader, with both-sides controls, not derived from the spec.

## Relates to: 058 (modular instances — the coherence model R4 is derived from: coexistence gated on nameability §3.1, `one_default` and no-displacement §3.6, and the "canonical companion" discipline it already names), 001 (sort/domain unification — its "Name Uniqueness" rule refused reopening by name; its deferred `companion` sugar is R2's shape), §6.3 (entity sugar; "operations move a free-standing entity to the long form"), §6.7 / WI-279 (dot dispatch resolves a member **declared on the receiver's sort** — there is no free-function fallback), WI-925/926/928/946 (one written name, one symbol, a category SET), WI-857 (requirement-dictionary layout), WI-818/876/931 + 038 (what backs a provision, and where a satisfaction fact belongs).

## The problem

Dot dispatch requires **membership**: `x.f()` resolves `f` on the receiver's least declared sort, and a free `operation f(r: Rec)` beside the type is not a candidate — measured, the prefix call `f(r)` evaluates while `r.f()` is refused `no such member (dot dispatch)`. So a free-standing `entity X(…)` gains a dot-callable operation only by acquiring a **member**.

Two spellings claim to do that; both load, neither is specified.

| written | today |
|---|---|
| `entity X(…)` then `sort X { operation … }` | loads, but the second body resolves **nothing** from outside itself — not its namespace's imports, not `X` |
| `entity X(…)` beside `namespace X { operation … }` | **works, completely** |

The first is broken mechanically: pass 1 gates the enclosing-scope parent link on the declaration being new, and a free-standing `entity` created no scope for the later `sort` body to inherit. The second works because a `namespace` declaration always creates that link and then merges onto the type's symbol.

## What a companion actually is — one scope, two entries

The visibility is **symmetric in every direction measured**. It is not an attachment with privileged one-way access; the sort body and each `namespace X` block are entries to the same scope of the same symbol.

| direction | measured |
|---|---|
| companion reads the sort's **type parameter** (`operation unwrap(b: Box) -> T`) | dispatches |
| companion calls the sort's own member, bare | `14` |
| companion names the sort's **variants**, bare, in a `match` | `2` |
| a **second** companion calls the first companion's member | `14` |
| the **sort body** calls a companion member, bare | `10` |
| the **sort body** dot-calls a companion member on its own receiver | `10` |
| companion's `requires S[T = X]` — control: delete it | both spellings fail **identically**, same message |
| companion member **backs** a provision declared one level out — control: no backing anywhere | provision holds; the control is refused, naming both |
| companion holds `fact S[T = X]` or a host `provides … language … end` block | loads (the obligation check for that placement is WI-978) |
| companion on a **stdlib** sort: `namespace anthill.prelude.Int64 { operation twice(x: Int64) = x + x }` | `7.twice()` ⇒ `14` |
| companion at a *different* address (`ns.ext.Rec`, not `ns.data.Rec`) | not attached — attachment is by qualified **address**, never by import |
| a companion **const**, against an operation declared beside it: symbol in scope / bare inside / `import X.{…}` then bare / `receiver.…` | yes·yes·`5`·**refused** — against the operation's yes·yes·`6`·`6` |

So the three questions this proposal was asked have one answer: **yes, in both directions.** `requires`/`provides` written in a companion are the *sort's*; the sort's members (type parameters included) are in scope in a companion; and the sort body sees companion members. What is missing is not wiring — it is **bounds**.

Unbounded today, each silent:

| shape | today |
|---|---|
| two companions declaring the same member name | **silent, last wins** |
| a companion redeclaring a member the sort's own body declares | **silent, companion wins** |
| `entity` inside a companion | loads and constructs, but is **not** a variant — surfaces later as `expected C, got Blue` |
| a second `sort C { … }` body beside `sort C { entity Red }` | **silently reopens** — both variants construct, the second body's members dispatch |

## Definitions

- **Second entry.** A `namespace X` declaration at the qualified address of a sort `X`. Attachment is by address, never by import.
- **Member of `X`.** A name declared in `X`'s scope. Reachable bare from within that scope, and from outside through `import X.{…}`.
- **Dispatch surface of `X`.** The members reachable as `receiver.name(…)`. Its elements are exactly the **operations**: a const is a member and is not on the surface (measured above), and this holds in the sort's own body as much as in a second entry.
- **Definition.** The `sort X … end` or `entity X(…)` that declares the type. Distinct from an entry, which adds to its scope.

## The rules

**R1 — A type is defined once.** Two *type* declarations at one address are a load error naming both spans: `sort X` + `sort X`, `enum X` + `enum X`, and `entity X` + `sort X` (§6.3 makes that pair two spellings of one declaration, so it is the same error). Reopening a closed ADT is the harm — today a second body silently adds variants.

**R2 — A second entry declares members of `X`.** What it declares enters `X`'s scope, is scoped by `X`'s type parameters, and may back `X`'s provisions — one symbol, as everywhere else (WI-926). Legal before, beside, or after the definition; the *before* order is a load-order accident today, not a language distinction (WI-979). This is the only route to a member of a type whose declaration one does not own, and it is 001's deferred `companion` spelled by address rather than keyword.

**R3 — A second entry may add members and provisions, never identity.** The lists below are **exhaustive over an entry's direct content** — every production the grammar admits there is classified, and anything unlisted is refused pending classification rather than silently allowed. A **nested namespace** written inside an entry is not a second entry to `X`: it is an ordinary namespace at its own address (`X.Inner`), and these restrictions do not recurse into it. A **description block** is inert and always allowed.

**Allowed — stated explicitly, because it is the point of the mechanism:**

- **operations** — the dispatch surface; an `operation` block is sugar for them and follows them;
- **consts** — members, not on the dispatch surface;
- **`fact Spec[X]` provisions, and host `provides Spec language L … end` blocks.** A provision *is a fact*, and a second entry is the sort's own scope, so there is nothing to refuse: the same declaration one level out is uncontroversial, and moving it next to the member that backs it is what §6.3/038 already asks for — **a satisfaction fact belongs in the closure where its backing exists**. A companion that may not carry the provision for the members it supplies could never make a foreign carrier satisfy a spec, which is most of why one writes a companion at all. The backing obligation must hold for a provision placed there exactly as it does one level out (WI-978 — today it does not run at all).
**Refused, each naming the sort:**

- an `entity` — a constructor is identity, and R1 says identity is written once;
- a `sort T = ?` or a type-parameter list — same reason;
- a sort-level **`requires`** — the requirement slots a type's frames carry are its structure, so the same rule reaches it. **If you want a `requires`, define a sort.**
- a **rule** — of any kind: a Horn clause, a `[simp]`/`[unfold]` equation, a sort-scoped `dot_apply` law; a `rule` block is sugar for rules and follows them;
- a **fact that is not a provision**, and a **constraint** — not as separate policies but by the same clause, because *facts are rules*: a fact is a bodyless rule and a constraint a headless one, so both are reached by the rule ban. A provision is the stated exception above, and the exception must be spelled that way round — allow `provides`/`fact Spec[X]`, refuse every other fact — since "it is a fact" is exactly what makes the rest refusable.

**Imports are shared, not entry-local**, and that is measured, not assumed: an import written in a second entry resolves a bare name in the sort's **body** (`7`, against a control with the import deleted that fails `unknown functor`), and an import written in the body resolves one in the entry (`9`). This follows from R2 — one scope — and it is deliberate rather than tolerated: making imports entry-local would split the one scope R2's six measured directions of symmetry establish, so an entry would stop being an entry. The cost is that an import is a **capture route** exactly as a declaration is, which is why R4's capture clause below is written over *names that resolve*, not over members.

The rule case is worth its own paragraph, because it is the one thing here that is not merely a scoping question. **R4 cannot police a rule**, and that is the point: two rules with one head are not a name collision, they are one predicate with two clauses, so "declared once" has no purchase. Every rule *fills* — and filling is exactly what breaks things, because the search over rules is **not monotone**. Measured:

```
rule p(1)
rule q(0) :- not p(2)          -- q(0) holds: 1 answer
namespace Rec  rule p(2)  end  -- a second entry adds one clause
                               -- q(0) now holds: 0 answers
```

A statement that was true is false, and every proof discharged from it (§Local interpretation / in-body proofs / the proof-verify pass) was verified against a knowledge base that no longer exists. An `[simp]` equation is worse in kind, not better: it is applied by the **typer**, rewriting LHS→RHS in operation bodies before dispatch, so a second entry's equation changes how *other files* type-check — action at a distance at load time rather than at run time.

**The ban is uniform, and its justification must not rest on ownership** — the language has no ownership predicate and no compilation unit, so "the writer is not the type's author" is not a distinction anything could enforce, and R2 deliberately admits a canonical companion sitting beside its own definition. The structural argument holds for *every* second entry without it:

1. a rule's binding is decided by resolution, and R6 concedes that binding is not even order-stable yet — so an entry cannot know which predicate it is joining;
2. R4 cannot police the result, because two clauses of one predicate are not a name collision;
3. the effect is non-monotone, so it reaches statements already proved;
4. and **the remedy is always available to whoever may legitimately add the rule**: a rule about `X` belongs in `X`'s definition, which is exactly the text the party entitled to add it can edit. The ban therefore costs that party a move they can already make, and costs everyone else precisely what it should — no ownership test required at load time.

One honest limit remains: this does **not** close the underlying hazard. A rule extending a predicate declared elsewhere is non-monotone wherever it is written — an ordinary nested namespace does the same, and so does the sort's own body. R3 closes the route this proposal opens; the general case belongs with R6 and the module question.

**R6 — A rule head's binding does not depend on declaration order.** The policy is not in question and is not changed here: §"A rule head functor is resolved, not declared" (WI-896) says the functor runs the ordinary ladder and the rule contributes a clause to whatever it lands on, *introducing* the name — scoped where written — only where the ladder finds nothing. What is undefined today is **when "the ladder finds nothing" is evaluated.** Measured, it is evaluated against a half-built name table, so textual order decides:

| written | binding |
|---|---|
| `rule p(1)` at namespace level, **then** `sort Rec { rule p(2) }` | both clauses join `p`; no `Rec.p` exists |
| `sort Rec { rule p(2) }`, **then** `rule p(1)` | two predicates — `Rec.p` and `p` — one clause each |

and identically for a second entry in place of the sort body, which is why this is not a companion question. It is stated here because R3's refusal of rules would otherwise rest on behaviour that is itself undefined.

**The binding is computed against the finished program**, never against the prefix of it that happens to be scanned: scopes outermost-first, all of a scope's heads together, so that the two rows above give the same answer — the first one, since in the finished program `p` does resolve from inside `Rec`. This is the invariant every *other* name already has (pass 1 defines every name across every file before any pass 2 runs — the WI-321 cross-file recursion invariant); a rule head escapes it only because its introduction happens during that same pass. A scope that wants its own name where an enclosing one resolves **declares** it — the remedy §WI-896 already prescribes ("to introduce a name that already resolves, declare it"). Tracked as WI-980.

The asymmetry between the last one and the provisions above is the point, and it is not about dictionary layout. `dict_layout` bundles the spec's chain then the provider's **over the whole knowledge base** (WI-857), so a second entry re-lays-out precisely what editing the definition re-lays-out — there is no companion-specific cost to price there.

The line is **who the declaration binds**. A provision is a *fact about* the type — additive, and true or false on its own terms. A `requires` is a constraint *on the type's callers*: every use of its operations must now supply that dictionary. A second entry is written by someone who is not the type's author and often not even its user, so allowing it there lets a third party add an obligation to everyone who already uses the type. That is the downstream-added-superclass move, and no module system permits it.

What refusing it costs, measured — a smaller thing than it looks:

| | |
|---|---|
| sort-level `requires` in a second entry, member calls the spec op **bare** | loads |
| the same member with the clause deleted | refused — `show` is a member of sort Show, not in scope as a bare name here |
| the same member calling it **qualified** (`Show.show(r)`), clause deleted | **loads** |
| op-level `requires` in a second entry — bare call | refused, identically to no clause at all |
| op-level `requires` — qualified call, and the control with no clause | both load |

So the only load-time effect attributable to the clause is **bare-name access to the spec's operations inside that entry**; the qualified spelling needs no clause. (Load-time only — whether a second entry's `requires` also changes runtime dictionary layout was not established, the generic-caller fixture having failed for unrelated reasons.)

And the remedy is available and mechanical for a type one owns: `sort Rec { requires Show[T = Rec]; entity Rec(n: Int64) }` plus a companion member using it **loads** (measured). That is §6.3's existing move — *operations move a free-standing entity to the long form* — reaching requirements too, which is R5.

For a **foreign** type there is no remedy, deliberately. Adding a requirement to a type one does not own re-lays-out its dispatch for every one of its users, and that is the single thing in this proposal a module boundary would certainly forbid — see below.

**R4 — FILL, never DISPLACE.** Three clauses. The first two are 058's rules applied to members rather than new ones; the third is what those two do not reach.

- **Two suppliers of one member name are refused at load**, naming both sites — by 058 §3.1's *coexistence gated on nameability*. Two providers of a spec may coexist because an ambiguous call has a repair the author can write (`[Spec = W]`); two members of one sort under one name have **no such currency** — `r.peek()` cannot say which — so this is the case 058 already calls "coexistence one cannot select out of is a trap, not a feature".
- **A second entry may not redeclare a member the definition declares** — 058 §3.6's *no-displacement*, in its own words: **fill silence, never overwrite speech**, so that no one line flips what every linked library's bracket-less dispatch already means.
- **No declaration may CAPTURE a name that already resolves in the sort's scope.** The two clauses above are keyed on *members*, and that is not enough: a name can already mean something without being a member. Measured — a sort body calls a bare `f(…)` that resolves through `import lib.f` and answers `1`; add `namespace Rec { operation f(…) }` and the *same unedited body* answers `2`. Nothing named `f` was a member, so the clauses above admit it, and existing code silently changed meaning — the precise opposite of *fill silence, never overwrite speech*. So the clause is written over **names that resolve**, not over members, which is also what makes it cover the import route above and consts (measured: a companion `const K` captures an imported `K`, `2` against a control's `1`).

The capture clause is stated over the **scope**, not over second entries, and deliberately so: measured, the *same* flip happens when the capturing member is written in the sort's own body, so an entry-local rule would be a patch on the wrong object — and it would split the one scope R2's symmetry rests on. §6.3 already records this hazard for the long form as a caution (WI-935, "an `import ns.{f}` elsewhere may bind to the member rather than to the namespace-level `f` — silently, since both are legal"); R4 turns that caution into a refusal, for both spellings at once. It is therefore a **change to behaviour the spec currently permits**, and its migration must be measured before it lands — how many places in stdlib, `anthill-stl`, examples and fixtures declare a member whose short name already resolves in its scope — tracked as WI-981.

The first two clauses are silent last-wins today, which is what makes a second entry indistinguishable from monkey-patching. Note the sort's *own* member already outranks other supply routes at dispatch (WI-842 refuses a tie between a member, an instance fact's binding, and a witness sort's member, naming each by its route); R4 closes the one route that never reaches that check, because it overwrites rather than competes.

**Provisions declared in a second entry are arbitrated by 058, not here.** A companion's `provides Spec[X]` is an ordinary provision: `one_default` refuses a second default for a `(spec, carrier)`, and the nameability gate decides whether rivals may coexist at all — *"`one_default` arbitrates all rows regardless of origin"*. 058 already contemplates this mechanism by name, prescribing "mark inline when you own the carrier **or ship its canonical companion**". Two consequences worth stating, both inherited rather than invented: a carrier that provides for itself has an inferred default, so a companion declaring a rival **violates `one_default`** — the orphan case is already refused where it would displace; and since 058 §4 proposes retiring the `fact X[…]` spelling of a provision in favour of `provides X[…]`, a second entry should be written in the latter.

**R5 — §6.3's remedy, restated.** To give a free-standing entity operations: rewrite it into the long form when you own the declaration, or write a companion when you do not. Both are one symbol.

## Where this leads: compilation modules

The things one wants to price about a second entry — the `requires` R3 refuses, the orphan provision it allows, and why its members are visible without an import — are **one question**, and it is not about companions.

A **dictionary layout is defined over the whole knowledge base.** So is provider search, so is the member set a receiver dispatches against. Every load sees every file, nothing is compiled separately, and therefore no declaration anywhere can invalidate a *previously compiled* call site — there are none. Under that model a second entry is exactly as consequential as an edit to the definition: **there is no boundary for anything here to cross.** That is why R3's refusal of `requires` rests on *who a declaration binds*, and R4's on 058's nameability, rather than on any layout cost — there is none to charge.

Each of the three becomes a real question the moment there is one:

- a `requires` added by a downstream unit changes an upstream type's dictionary layout — which is why R3 refuses it outright rather than pricing it;
- a provision for a foreign carrier is an **orphan instance**. Within one KB, 058 already decides it (`one_default`, nameability). What no whole-program rule can reach is two units that each declare one and are **never loaded together** — neither `one_default` nor R4 ever sees the pair;
- global attachment means a unit's member set depends on which other units happen to be loaded.

These are the classic separate-compilation constraints (Haskell's orphan rule, Rust's coherence), and Anthill meets them through this one mechanism. **This proposal deliberately does not invent a module system to answer them.** It records that R3's line and R4's KB-wide arbitration are *whole-program* answers, correct exactly as long as the program is whole — and that a compilation-module design is what would revisit them, together, as one decision rather than three.

R4 survives either way, because it is 058's rule and not a new one: a module system would tighten *where* the arbitration happens, not what it decides.

## Open question

**Spelling.** Keep `namespace X`, or introduce the `companion` block 001 deferred? `namespace X` needs no grammar and already works; a keyword makes the intent legible, gives R3 a natural home, and distinguishes "I am entering this type's scope again" from "I am declaring an unrelated namespace that happens to share a name".
