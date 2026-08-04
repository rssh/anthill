# 059: Secondary Entries — one scope, a main entry and secondary ones

## Status: Draft (2026-08-04). Written from WI-975, which asked what a second declaration of one name means and found two mechanisms sharing one spelling. **A type is defined once; a `namespace` at its address is a SECONDARY ENTRY to that type's scope, not a separate module attached to it.** Every claim below is measured against the Rust loader, with both-sides controls, not derived from the spec.

## Relates to: 058 (modular instances — the coherence model R4 is derived from: coexistence gated on nameability §3.1, `one_default` and no-displacement §3.6, and the "canonical companion" discipline it already names — 058's term, not one this proposal adopts), 001 (sort/domain unification — its "Name Uniqueness" rule refused reopening by name; its deferred `companion` sugar is R2's shape, spelled without the keyword), §6.3 (entity sugar; "operations move a free-standing entity to the long form"), §6.7 / WI-279 (dot dispatch resolves a member **declared on the receiver's sort** — there is no free-function fallback), WI-925/926/928/946 (one written name, one symbol, a category SET), WI-857 (requirement-dictionary layout), WI-818/876/931 + 038 (what backs a provision, and where a satisfaction fact belongs).

## The problem

Dot dispatch requires **membership**: `x.f()` resolves `f` on the receiver's least declared sort, and a free `operation f(r: Rec)` beside the type is not a candidate — measured, the prefix call `f(r)` evaluates while `r.f()` is refused `no such member (dot dispatch)`. So a free-standing `entity X(…)` gains a dot-callable operation only by acquiring a **member**.

Two spellings claim to do that; both load, neither is specified.

| written | today |
|---|---|
| `entity X(…)` then `sort X { operation … }` | loads, but the second body resolves **nothing** from outside itself — not its namespace's imports, not `X` |
| `entity X(…)` beside `namespace X { operation … }` | **works, completely** |

The first is broken mechanically: pass 1 gates the enclosing-scope parent link on the declaration being new, and a free-standing `entity` created no scope for the later `sort` body to inherit. The second works because a `namespace` declaration always creates that link and then merges onto the type's symbol.

## What a secondary entry actually is — the same scope, entered again

The visibility is **symmetric in every direction measured**. It is not an attachment with privileged one-way access; the main entry and each secondary one declare into the same scope of the same symbol.

| direction | measured |
|---|---|
| a secondary entry reads the sort's **type parameter** (`operation unwrap(b: Box) -> T`) | dispatches |
| a secondary entry calls the sort's own member, bare | `14` |
| a secondary entry names the sort's **variants**, bare, in a `match` | `2` |
| one secondary entry calls another secondary entry's member | `14` |
| the **main entry** calls a secondary entry's member, bare | `10` |
| the **main entry** dot-calls a secondary entry's member on its own receiver | `10` |
| a secondary entry's `requires S[T = X]` — control: delete it | both spellings fail **identically**, same message |
| a secondary entry's member **backs** a provision declared one level out — control: no backing anywhere | provision holds; the control is refused, naming both |
| a secondary entry holds `fact S[T = X]` or a host `provides … language … end` block | loads (the obligation check for that placement is WI-978) |
| a secondary entry on a **stdlib** sort: `namespace anthill.prelude.Int64 { operation twice(x: Int64) = x + x }` | `7.twice()` ⇒ `14` |
| a secondary entry at a *different* address (`ns.ext.Rec`, not `ns.data.Rec`) | not attached — attachment is by qualified **address**, never by import |
| a secondary entry's **const**, against an operation declared beside it: symbol in scope / bare inside / `import X.{…}` then bare / `receiver.…` | yes·yes·`5`·**refused** — against the operation's yes·yes·`6`·`6` |

So the three questions this proposal was asked have one answer: **yes, in both directions.** `requires`/`provides` written in a secondary entry are the *sort's*; the sort's members (type parameters included) are in scope in a secondary entry; and the main entry sees a secondary entry's members. What is missing is not wiring — it is **bounds**.

Unbounded today, each silent:

| shape | today |
|---|---|
| two secondary entries declaring the same member name | **silent, last wins** |
| a secondary entry redeclaring a member the main entry declares | **silent, the secondary entry wins** |
| `entity` inside a secondary entry | loads and constructs, but is **not** a variant — surfaces later as `expected C, got Blue` |
| a second `sort C { … }` body beside `sort C { entity Red }` | **silently reopens** — both variants construct, the second body's members dispatch |

## Definitions

A sort's scope has one or more **entries** — texts that declare into it. An address without a sort has no entries in this sense at all; it is an ordinary namespace, and this proposal says nothing about it.

- **Main entry.** The `sort X … end` or `entity X(…)` that *defines* the type: its constructors, type parameters and requirements. **At most one** exists (R1) — an address may have none, and then there is no type there.
- **Secondary entry.** A `namespace X` at an address that **has a main entry**. It *adds to* `X`'s scope and defines nothing about the type. Any number may exist. Attachment is by address, never by import.
- **Ordinary namespace.** A `namespace X` at an address with **no** main entry — the overwhelmingly common case, and every namespace in the language until a sort shares its address. It declares a module, not members of a type, and **nothing in R3 or R4 reaches it**: a rule, an entity, a nested sort are all as legal there as they have ever been. Only the presence of a main entry turns the same text into a secondary entry.
- **Member of `X`.** A name declared in `X`'s scope, by any entry. Reachable bare from within that scope, and from outside through `import X.{…}`.
- **Dispatch surface of `X`.** The members reachable as `receiver.name(…)`. Its elements are exactly the **operations**: a const is a member and is not on the surface (measured above), in the main entry as much as in a secondary one.

**The two are told apart by the address, not by the text.** `namespace X` is written identically either way; what decides is whether a sort exists at `X` — measured, a plain namespace's symbol is `Namespace` alone, and one beside a main entry carries `Sort` too, so the question an implementation asks is `has_kind(X, Sort)`, the same `has_kind`-not-`kind_of` reading WI-956 settled for the gates.

One consequence is uncomfortable and belongs on the record: **a namespace becomes a secondary entry because someone else declared a sort at its address.** Written alone, `namespace Utils { rule p(1) }` is an ordinary namespace and its rule is legal; let another file declare `sort Utils` there and the same text is a secondary entry whose rule R3 refuses. Nothing local to the namespace changed. This is the whole-program property again, in the classification itself rather than in dispatch — see "Where this leads".

**"Main" and "secondary" name roles, not order.** A secondary entry may be written first, in the same file or another, and read first by the loader; which text the loader happens to reach first decides nothing. Today that is not quite true — a secondary entry read before the main one breaks the sort (WI-979) — which is a defect against this definition, not a distinction it recognises.

## The rules

**R1 — A type is defined once.** Two *type* declarations at one address are a load error naming both spans: `sort X` + `sort X`, `enum X` + `enum X`, and `entity X` + `sort X` (§6.3 makes that pair two spellings of one declaration, so it is the same error). Reopening a closed ADT is the harm — today a second body silently adds variants.

**R2 — A secondary entry declares members of `X`.** What it declares enters `X`'s scope, is scoped by `X`'s type parameters, and may back `X`'s provisions — one symbol, as everywhere else (WI-926). Legal before, beside, or after the main entry. This is the only route to a member of a type whose declaration one does not own, and it needs no keyword of its own — see the closing note.

**R3 — A secondary entry may add members and provisions, never identity.** The lists below are **exhaustive over an entry's direct content** — every production the grammar admits there is classified, and anything unlisted is refused pending classification rather than silently allowed. A **nested namespace** written inside an entry is not a secondary entry to `X`: it is an ordinary namespace at its own address (`X.Inner`), and these restrictions do not recurse into it. A **description block** is inert and always allowed.

**Allowed — stated explicitly, because it is the point of the mechanism:**

- **operations** — the dispatch surface; an `operation` block is sugar for them and follows them;
- **consts** — members, not on the dispatch surface;
- **a nested `sort` / `enum` with a body** — it declares a *new type at its own address* (`X.Inner`), so it is that type's **main entry**, not a declaration about `X`. Same reading as the nested namespace above, and the restrictions do not recurse into it. (`sort T = ?` stays refused: that one *is* a type parameter of `X`, which is `X`'s identity.);
- **a `proof` whose target is declared in the same entry** — see below;
- **`fact Spec[X]` provisions, and host `provides Spec language L … end` blocks.** A provision *is a fact*, and a secondary entry is the sort's own scope, so there is nothing to refuse: the same declaration one level out is uncontroversial, and moving it next to the member that backs it is what §6.3/038 already asks for — **a satisfaction fact belongs in the closure where its backing exists**. A secondary entry that may not carry the provision for the members it supplies could never make a foreign carrier satisfy a spec, which is most of why one writes a secondary entry at all. The backing obligation must hold for a provision placed there exactly as it does one level out (WI-978 — today it does not run at all).
**Refused, each naming the sort:**

- an `entity` — a constructor is identity, and R1 says identity is written once;
- a `sort T = ?` or a type-parameter list — same reason;
- a sort-level **`requires`** — the requirement slots a type's frames carry are its structure, so the same rule reaches it. **If you want a `requires`, define a sort.**
- a **rule** whose head does not *introduce*, or whose predicate has clauses in another entry — the two conditions below. A `rule` block is sugar for rules and follows them; a dot rule and an operator rule never introduce, so both are always refused. **Enforced today as: every rule, no case analysis** — see "what an implementation does today";
- a **`proof` whose target is declared in another entry** — a proof is not a pure consumer of the knowledge base: verification calls `set_proof_result`, writing `VerdictWrite::Discharged { witness, solver }` or `FailedUnknown { reason }` **back onto the target rule**. So a proof mutates the state of a declaration it may not own, and the same condition the rule clause uses applies — the entry that declares the target may prove things about it, and nobody else. (What *reads* a discharged verdict, and therefore how much behaviour this changes, is not established here.);
- a **fact that is not a provision**, and a **constraint** — not as separate policies but by the same clause, because *facts are rules*: a fact is a bodyless rule and a constraint a headless one, so both are reached by the rule ban. A provision is the stated exception above, and the exception must be spelled that way round — allow `provides`/`fact Spec[X]`, refuse every other fact — since "it is a fact" is exactly what makes the rest refusable.

**Imports are shared, not entry-local**, and that is measured, not assumed: an import written in a secondary entry resolves a bare name in the sort's **body** (`7`, against a control with the import deleted that fails `unknown functor`), and an import written in the body resolves one in the entry (`9`). This follows from R2 — one scope — and it is deliberate rather than tolerated: making imports entry-local would split the one scope R2's six measured directions of symmetry establish, so an entry would stop being an entry. The cost is that an import is a **capture route** exactly as a declaration is, which is why R4's capture clause below is written over *names that resolve*, not over members.

The rule case is worth its own paragraph, because it is the one thing here that is not merely a scoping question. **R4 cannot police a rule**: two rules with one head are not a name collision, they are one predicate with two clauses, so "declared once" has no purchase. And a rule that *joins* an existing predicate breaks things even though it only adds, because the search over rules is **not monotone**. Measured:

```
rule p(1)
rule q(0) :- not p(2)          -- q(0) holds: 1 answer
namespace Rec  rule p(2)  end  -- a secondary entry adds one clause
                               -- q(0) now holds: 0 answers
```

A statement that was true is false, and every proof discharged from it (§Local interpretation / in-body proofs / the proof-verify pass) was verified against a knowledge base that no longer exists. An `[simp]` equation is worse in kind, not better: it is applied by the **typer**, rewriting LHS→RHS in operation bodies before dispatch, so a secondary entry's equation changes how *other files* type-check — action at a distance at load time rather than at run time.

**The ban is uniform, and its justification must not rest on ownership** — the language has no ownership predicate and no compilation unit, so "the writer is not the type's author" is not a distinction anything could enforce, and R2 deliberately admits a a secondary entry sitting beside its own main entry. The structural argument holds for *every* secondary entry without it:

1. a rule's binding is decided by resolution, and R6 concedes that binding is not even order-stable yet — so an entry cannot know which predicate it is joining;
2. R4 cannot police the result, because two clauses of one predicate are not a name collision;
3. the effect is non-monotone, so it reaches statements already proved;
4. and **the remedy is always available to whoever may legitimately add the rule**: a rule about `X` belongs in `X`'s main entry, which is exactly the text the party entitled to add it can edit. The ban therefore costs that party a move they can already make, and costs everyone else precisely what it should — no ownership test required at load time.

**The rule a secondary entry MAY declare, and the two conditions that make it sound.** The blanket ban above is the *enforced* rule, not the intended one. A rule is a definition, and a definition of something new displaces nothing — so a secondary entry may declare a rule exactly when both hold:

1. **its head introduces** — the head resolves to nothing in the finished program, so no existing goal can be about it; and
2. **one entry owns the predicate** — every clause of that head is written in that same entry.

Each condition answers a measured failure of the naive "fresh head is harmless" reading.

*Without (2), two entries silently compose one predicate.* Two secondary entries that each introduce `freshp` do not collide — both clauses join it, `freshp(1)` and `freshp(2)` both answering. Neither captured a pre-existing name, so R4 is silent, and the predicate ends up assembled by two parties that never agreed on it. Condition (2) is what R4 cannot express, because a predicate legitimately has many clauses; it is a rule about where they may be *written*.

*Without (1), the head is not really new.* A main entry carrying `rule q(0) :- not freshp(1)` answers `q(0)` once; add `namespace Rec { rule freshp(1) }` and it answers zero times, though the head was as fresh as heads get — the symbol lands at `X.freshp`, exactly where the main entry would have put it. The reference existed before the definition did. That is reachable in **rule bodies and constraints only**: measured, both load while naming a predicate that resolves to nothing, and an operation body naming one is already refused (`unknown functor`). So it is precisely WI-895's gap, and (1) is only *checkable* once it closes — a name that resolves to nothing must stop being referenceable before "resolves to nothing" can mean "no one refers to it".

Two shapes are excluded by (1) rather than by a clause of their own, which is the sign the condition is the right one: a **dot rule** and an **operator rule** carry the desugar's functor (`dot_apply`, `add`), and a desugared conclusion introduces nothing (§"A rule-introduced functor is scoped where it is written") — so neither is ever fresh, and the `[simp]`-fires-in-the-typer hazard cannot arise through them.

**What an implementation does today: refuse every rule in a secondary entry, with no case analysis on the head.** Not as a placeholder — the narrow rule is not yet enforceable. Condition (1) is undecidable while text order decides whether a head introduces (R6/WI-980), and it is unsound while a body may reference what resolves to nothing (WI-895, Open). The narrow rule lands when both are closed, and needs no further design: conditions (1) and (2) are decidable at scan time, (2) by grouping a predicate's clauses by the entry they are written in.

One honest limit remains: this does **not** close the underlying hazard. A rule extending a predicate declared elsewhere is non-monotone wherever it is written — an ordinary nested namespace does the same, and so does the sort's own body. R3 closes the route this proposal opens; the general case belongs with R6 and the module question.

**R6 — A rule head's binding does not depend on declaration order.** The policy is not in question and is not changed here: §"A rule head functor is resolved, not declared" (WI-896) says the functor runs the ordinary ladder and the rule contributes a clause to whatever it lands on, *introducing* the name — scoped where written — only where the ladder finds nothing. What is undefined today is **when "the ladder finds nothing" is evaluated.** Measured, it is evaluated against a half-built name table, so textual order decides:

| written | binding |
|---|---|
| `rule p(1)` at namespace level, **then** `sort Rec { rule p(2) }` | both clauses join `p`; no `Rec.p` exists |
| `sort Rec { rule p(2) }`, **then** `rule p(1)` | two predicates — `Rec.p` and `p` — one clause each |

and identically for a secondary entry in place of the sort body, which is why this is not a question about secondary entries. It is stated here because R3's refusal of rules would otherwise rest on behaviour that is itself undefined.

**The binding is computed against the finished program**, never against the prefix of it that happens to be scanned: scopes outermost-first, all of a scope's heads together, so that the two rows above give the same answer — the first one, since in the finished program `p` does resolve from inside `Rec`. This is the invariant every *other* name already has (pass 1 defines every name across every file before any pass 2 runs — the WI-321 cross-file recursion invariant); a rule head escapes it only because its introduction happens during that same pass. A scope that wants its own name where an enclosing one resolves **declares** it — the remedy §WI-896 already prescribes ("to introduce a name that already resolves, declare it"). Tracked as WI-980.

The asymmetry between the last one and the provisions above is the point, and it is not about dictionary layout. `dict_layout` bundles the spec's chain then the provider's **over the whole knowledge base** (WI-857), so a secondary entry re-lays-out precisely what editing the definition re-lays-out — there is no cost specific to a secondary entry to price there.

The line is **who the declaration binds**. A provision is a *fact about* the type — additive, and true or false on its own terms. A `requires` is a constraint *on the type's callers*: every use of its operations must now supply that dictionary. A secondary entry is written by someone who is not the type's author and often not even its user, so allowing it there lets a third party add an obligation to everyone who already uses the type. That is the downstream-added-superclass move, and no module system permits it.

What refusing it costs, measured — a smaller thing than it looks:

| | |
|---|---|
| sort-level `requires` in a secondary entry, member calls the spec op **bare** | loads |
| the same member with the clause deleted | refused — `show` is a member of sort Show, not in scope as a bare name here |
| the same member calling it **qualified** (`Show.show(r)`), clause deleted | **loads** |
| op-level `requires` in a secondary entry — bare call | refused, identically to no clause at all |
| op-level `requires` — qualified call, and the control with no clause | both load |

So the only load-time effect attributable to the clause is **bare-name access to the spec's operations inside that entry**; the qualified spelling needs no clause. (Load-time only — whether a secondary entry's `requires` also changes runtime dictionary layout was not established, the generic-caller fixture having failed for unrelated reasons.)

And the remedy is available and mechanical for a type one owns: `sort Rec { requires Show[T = Rec]; entity Rec(n: Int64) }` plus a secondary entry's member using it **loads** (measured). That is §6.3's existing move — *operations move a free-standing entity to the long form* — reaching requirements too, which is R5.

For a **foreign** type there is no remedy, deliberately. Adding a requirement to a type one does not own re-lays-out its dispatch for every one of its users, and that is the single thing in this proposal a module boundary would certainly forbid — see below.

**R4 — FILL, never DISPLACE.** Three clauses. The first two are 058's rules applied to members rather than new ones; the third is what those two do not reach.

- **Two suppliers of one member name are refused at load**, naming both sites — by 058 §3.1's *coexistence gated on nameability*. Two providers of a spec may coexist because an ambiguous call has a repair the author can write (`[Spec = W]`); two members of one sort under one name have **no such currency** — `r.peek()` cannot say which — so this is the case 058 already calls "coexistence one cannot select out of is a trap, not a feature".
- **A secondary entry may not redeclare a member the main entry declares** — 058 §3.6's *no-displacement*, in its own words: **fill silence, never overwrite speech**, so that no one line flips what every linked library's bracket-less dispatch already means.
- **A member operation may not capture an operation it does not override.** The two clauses above are keyed on *members colliding*, and that is not enough: a name can already mean something without being a member. Measured — a main entry calls a bare `f(…)` that resolves through `import lib.f` and answers `1`; add a secondary entry declaring `f` and the *same unedited body* answers `2`. Nothing named `f` was a member, so the clauses above admit it, and existing code silently changed meaning.

  The qualifier "it does not override" is not a hedge; it is what the corpus forced. Counting every declaration whose short name already resolves in its declaring scope gives **61 sites** across stdlib, `anthill-stl`, examples and `anthill-todo` — so the unqualified clause is unimplementable. The breakdown says why, and each exclusion is principled rather than a carve-out for convenience:

  | class | count | why it is not a capture |
  |---|---|---|
  | a **parameter** shadowing an operation (`Float.pow.exp`, `KB.assert.kb`) | many of 38 | a binder is not a declaration |
  | a **type name** shadowing a type (`IndexedSeq.Effect`, `TypeExtractor.Error`) | rest of 38 | dot dispatch never routes through it |
  | a member **overriding a spec operation** (`List.length` over `IndexedSeq.length`) | 19 + 4 | this is how a sort implements what it provides — reached through the `requires` link, or through an import of the spec's member |
  | **no override relationship** | **0** | the hazard, and the corpus no longer contains one |

  So the clause bites **nothing in the corpus** and lands with no migration. It had two sites, `reflect.KB.nonvar` and `reflect.KB.ground` over the namespace-level operations of those names, and the verdict was neither of the two the count anticipated (rename, or exempt): the captured names were the ones worth keeping, so the *members* went. Their receiver was never read, and one question had two answers — see WI-982. Whether the instrument should still be a refusal or a **warning** stays a live question at zero sites: WI-346 already warns for the neighbouring requires-shadow case, and this is its sibling. Census and site list: WI-981, less the two WI-982 removed.

  Like the two clauses above it, this one is stated over the **scope**, not over secondary entries: measured, the same flip happens when the capturing operation is written in the main entry, so an entry-local rule would patch the wrong object and would split the one scope R2 rests on. §6.3 records the hazard for the long form as a caution already (WI-935); this makes it a check, for both spellings at once.

**Is R4 implementable?** Each clause is decidable, and each has a measured blast radius — but they need two different mechanisms, and clause 3 needs a predicate the route alone does not give.

| clause | sites in the corpus | what it needs |
|---|---|---|
| 1 — two suppliers of one member name | **0** | a pass-1 declaration ledger |
| 2 — a secondary entry redeclaring a main-entry member | **0** (a sub-case of 1) | the same ledger |
| 3 — capturing an operation it does not override | **0** (was 2, removed by WI-982) | the override relation, after pass 2 |

Clauses 1 and 2 cannot be checked by walking symbols: `define` **merges** two same-named declarations in one scope into one symbol, so by the time symbols exist the duplication is gone. They need each *declaration* recorded as pass 1 makes it, keyed on (scope, local name) — the same ledger R1 needs for duplicate type declarations, so it is one piece of machinery for both. Measured that way over 427 operation/const declarations in stdlib, `anthill-stl`, examples and `anthill-todo`: **no name is declared twice in one scope**, so both clauses land with no migration. (The zero is honest but easy: the corpus contains no secondary entries at all, so clause 2 has nothing to bite on yet. Clause 1 also covers two same-named operations in one *main* entry, and that is genuinely zero.)

Clause 3 must key on the **override relation** — is the captured operation a member of a spec the declaring sort requires or provides — and **not** on the route by which the name was reached. The measurement is why: 4 of the legitimate overrides arrive through an `import` of the spec's member rather than through the `requires` link, so a route-based rule refuses exactly the wrong four. That relation is known only after pass 2, so the check runs there, not in pass 1 beside the ledger.

The first two clauses are silent last-wins today, which is what makes a secondary entry indistinguishable from monkey-patching. Note the sort's *own* member already outranks other supply routes at dispatch (WI-842 refuses a tie between a member, an instance fact's binding, and a witness sort's member, naming each by its route); R4 closes the one route that never reaches that check, because it overwrites rather than competes.

**Provisions declared in a secondary entry are arbitrated by 058, not here.** A secondary entry's `provides Spec[X]` is an ordinary provision: `one_default` refuses a second default for a `(spec, carrier)`, and the nameability gate decides whether rivals may coexist at all — *"`one_default` arbitrates all rows regardless of origin"*. 058 already contemplates this mechanism by name, prescribing "mark inline when you own the carrier **or ship its canonical companion**". Two consequences worth stating, both inherited rather than invented: a carrier that provides for itself has an inferred default, so a secondary entry declaring a rival **violates `one_default`** — the orphan case is already refused where it would displace; and since 058 §4 proposes retiring the `fact X[…]` spelling of a provision in favour of `provides X[…]`, a secondary entry should be written in the latter.

**R5 — §6.3's remedy, restated.** To give a free-standing entity operations: rewrite it into the long form when you own the declaration, or write a secondary entry when you do not. Both are one symbol.

## Where this leads: compilation modules

The things one wants to price about a secondary entry — the `requires` R3 refuses, the orphan provision it allows, and why its members are visible without an import — are **one question**, and it is not about secondary entries.

A **dictionary layout is defined over the whole knowledge base.** So is provider search, so is the member set a receiver dispatches against. Every load sees every file, nothing is compiled separately, and therefore no declaration anywhere can invalidate a *previously compiled* call site — there are none. Under that model a secondary entry is exactly as consequential as an edit to the definition: **there is no boundary for anything here to cross.** That is why R3's refusal of `requires` rests on *who a declaration binds*, and R4's on 058's nameability, rather than on any layout cost — there is none to charge.

Each of the three becomes a real question the moment there is one:

- a `requires` added by a downstream unit changes an upstream type's dictionary layout — which is why R3 refuses it outright rather than pricing it;
- a provision for a foreign carrier is an **orphan instance**. Within one KB, 058 already decides it (`one_default`, nameability). What no whole-program rule can reach is two units that each declare one and are **never loaded together** — neither `one_default` nor R4 ever sees the pair;
- global attachment means a unit's member set depends on which other units happen to be loaded — and, per the Definitions, so does whether a unit's `namespace X` is an ordinary namespace or a secondary entry at all.

**The likely shape of the answer: open and closed packages.** A package that is *closed* admits no secondary entry to its addresses from outside itself; an *open* one does. That single axis answers all four at once — a downstream `requires` and an orphan provision are simply unwritable against a closed package, its member set is fixed at its boundary, and the classification flip above cannot be caused from another package, since no one else can enter its addresses. Within a package the non-locality remains, where it is local enough to see. Two things would have to be decided with it and are not decided here: whether closed is the **default**, and whether openness is declared by the package that owns the address (a permission) or claimed by the one extending it (a request). This proposal takes no position beyond noting that it is one mechanism rather than four.

These are the classic separate-compilation constraints (Haskell's orphan rule, Rust's coherence), and Anthill meets them through this one mechanism. **This proposal deliberately does not invent a module system to answer them.** It records that R3's line and R4's KB-wide arbitration are *whole-program* answers, correct exactly as long as the program is whole — and that a compilation-module design is what would revisit them, together, as one decision rather than three.

R4 survives either way, because it is 058's rule and not a new one: a module system would tighten *where* the arbitration happens, not what it decides.

## Spelling — settled, not open

`namespace X` is the spelling. No keyword is introduced, and no noun beside
*secondary entry* is: 001 deferred a `companion` block and 058 speaks of a
"canonical companion", but a second word for one thing only raises the question
of what a companion-less secondary entry would be. The mechanism needs no
grammar, works today, and is named by what it is.
