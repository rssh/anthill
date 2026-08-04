# 059: Secondary Entries — one scope, a main entry and secondary ones

## Status: Draft (2026-08-04). Written from WI-975, which asked what a second declaration of one name means and found two mechanisms sharing one spelling. **A type is defined once; a `namespace` at its address is a SECONDARY ENTRY to that type's scope, not a separate module attached to it.** Every claim below is measured against the Rust loader, with both-sides controls, not derived from the spec.

## Relates to: 058 (modular instances — the coherence model R4 is derived from: coexistence gated on nameability §3.1, `one_default` and no-displacement §3.6, and the "canonical companion" discipline it already names — 058's term, not one this proposal adopts), 001 (sort/domain unification — its "Name Uniqueness" rule refused reopening by name; its deferred `companion` sugar is R2's shape, spelled without the keyword), §6.3 (entity sugar; "operations move a free-standing entity to the long form"), §6.7 / WI-279 (dot dispatch resolves a member **declared on the receiver's sort** — there is no free-function fallback), WI-925/926/928/946 (one written name, one symbol, a category SET), WI-857 (requirement-dictionary layout), WI-818/876/931 + 038 (what backs a `provides`/`fact Spec[X]`, and where a satisfaction fact belongs).

## The problem

Dot dispatch requires **membership**: `x.f()` resolves `f` on the receiver's least declared sort, and a free `operation f(r: Rec)` beside the type is not a candidate — measured, the prefix call `f(r)` evaluates while `r.f()` is refused `no such member (dot dispatch)`. So a free-standing `entity X(…)` gains a dot-callable operation only by acquiring a **member**.

Two spellings claim to do that; both load, neither is specified.

| written | today |
|---|---|
| `entity X(…)` then `sort X { operation … }` | **refused** — the second body resolves **nothing** from outside itself, not its namespace's imports and not `X`, so every name in it is an `unresolved name` error |
| `entity X(…)` beside `namespace X { operation … }` | **works, completely** |

The first is broken mechanically: pass 1 gates the enclosing-scope parent link on the declaration being new, and a free-standing `entity` created no scope for the later `sort` body to inherit. The second works because a `namespace` declaration always creates that link and then merges onto the type's symbol. Note the first fails LOUDLY, and WI-979 deliberately left it that way while fixing its siblings: R1 refuses two type declarations at one address outright, so supplying the missing link would build a capability R1 removes.

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
| a secondary entry's member **backs** a `fact Spec[X]` declared one level out — control: no backing anywhere | the claim holds; the control is refused, naming both |
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

A sort's scope has one or more **entries** — texts that declare into it. Syntactically an entry is a **`namespace`, `sort`, `enum` or `entity` declaration with definitions inside**; those four are what declare into a scope, and nothing else does. An address without a sort has no entries in this sense at all; it is an ordinary namespace, and this proposal says nothing about it.

- **Main entry.** The `sort X … end`, `enum X … end` or `entity X(…)` that *defines* the type: its constructors, type parameters and requirements. **At most one** exists (R1) — an address may have none, and then there is no type there.
- **Secondary entry.** A `namespace X` at an address that **has a main entry**. It *adds to* `X`'s scope and defines nothing about the type. Any number may exist. Attachment is by address, never by import.
- **One entry, individuated.** The **main entry** is the single `sort`/`entity` declaration, wherever it sits. A **secondary entry** is all `namespace X` text at that address **within one file**: two `namespace X … end` blocks in the same file are ONE secondary entry, and the same text in a second file is a second one. A file holding both the declaration and a `namespace X` block therefore holds two entries — main and secondary — which is what keeps R4's main-vs-secondary asymmetry meaningful.

  The **file** is the unit for two reasons. What the entry-keyed rules guard against is a predicate "assembled by two parties that never agreed on it", and two blocks in one file are one author making one edit — a file boundary is the smallest place where *two parties* is real. And it is the unit this proposal already uses: an import resolves only in the file it is written in. One notion of locality, not two.

  It is also the only one that is checkable. Every declaration carries a `SourceSpan` with its `SourceId`, and `file_idx` is threaded through both scan passes — but two `namespace X … end` blocks at one address compute the same qualified name, reuse the same symbol, and alloc the same hash-consed scope term, so no per-block identity exists to group by. "Entry = one block" would have to mint one first.

  **What "with definitions inside" leaves open: a type alias.** `sort X = T` puts its definition after the `=`, not inside, so it is not an entry by that reading. But measured, `sort Path = String` beside `namespace Path { operation len(p: Path) -> Int64 }` loads, `Path.len("x")` answers, and the loader's own diagnostic calls `len` "a member of sort Path" — the alias behaves as a main entry. Either an alias is one, with its definition written outside its body, or that attachment is a divergence. A bare `entity Foo` with no fields asks the same question. (`enum` needs no such call: it is named above, and measured — `enum Colour { entity red }` beside `namespace Colour { operation code }` dispatches `Colour.code(red)`.)

- **Ordinary namespace.** A `namespace X` at an address with **no** main entry — the overwhelmingly common case, and every namespace in the language until a sort shares its address. It declares a module, not members of a type, and **nothing in R3 or R4 reaches it**: a rule, an entity, a nested sort are all as legal there as they have ever been. Only the presence of a main entry turns the same text into a secondary entry.
- **Member of `X`.** A name declared in `X`'s scope, by any entry. Reachable bare from within that scope, and from outside through `import X.{…}`.
- **Dispatch surface of `X`.** The members reachable as `receiver.name(…)`. Its elements are exactly the **operations**: a const is a member and is not on the surface (measured above), in the main entry as much as in a secondary one.

**The two are told apart by the address, not by the text.** `namespace X` is written identically either way; what decides is whether a sort exists at `X` — measured, a plain namespace's symbol is `Namespace` alone, and one beside a main entry carries `Sort` too, so the question an implementation asks is `has_kind(X, Sort)`, the same `has_kind`-not-`kind_of` reading WI-956 settled for the gates.

One consequence is uncomfortable and belongs on the record: **a namespace becomes a secondary entry because someone else declared a sort at its address.** Written alone, `namespace Utils { rule p(1) }` is an ordinary namespace and its rule is legal; let another file declare `sort Utils` there and the same text is a secondary entry whose rule R3 refuses. Nothing local to the namespace changed. This is the whole-program property again, in the classification itself rather than in dispatch — see "Where this leads".

**"Main" and "secondary" name roles, not order.** A secondary entry may be written first, in the same file or another, and read first by the loader; which text the loader happens to reach first decides nothing. Measured in both orders, and it holds for the classification (`has_kind(X, Sort)`), for the eponymous collapse, and for the visibility of the sort's variants to its enclosing scope — WI-979, which is what made the loader read all three off *which declaration came first* rather than off the declarations.

## The rules

**R1 — A type is defined once.** Two *type* declarations sharing a **(scope, local name)** are a load error naming both spans: `sort X` + `sort X`, `enum X` + `enum X`, and — as **siblings** — `entity X` + `sort X` (§6.3 makes that pair two spellings of one declaration, so it is the same error). Reopening a closed ADT is the harm: today a second body silently adds variants.

**Keyed on the declaration AS WRITTEN, not on the address it ends at**, and §6.3's eponymous constructor is why. `sort Vec3 { entity Vec3(…) }` collapses the constructor onto the sort's own symbol (WI-926), so both declarations end at address `ns.Vec3` — address-keyed, that is indistinguishable from the sibling `entity X` + `sort X` this rule refuses, and a legal shape is rejected. Written-keyed they differ: the sort is `(ns, "Vec3")`, and the entity, declared inside the sort body, is `(ns.Vec3, "Vec3")`. The sibling form stays caught, both halves being `(ns, "Vec3")`. The address cannot tell them apart because the collapse has already erased the difference by the time addresses exist — and that collapse is something §6.3 does deliberately. Measured, the shape is real but small: 4 eponymous sites (`Vec3`, `TotalFloat`, `Duration`, `Timestamp`) among 140 `sort`/`enum` headers across stdlib, `anthill-stl`, examples and `anthill-todo`. This is the same key R4's ledger uses, which is what makes it one piece of machinery for both.

**R2 — A secondary entry declares members of `X`.** What it declares enters `X`'s scope, is scoped by `X`'s type parameters, and may back `X`'s `provides`/`fact Spec[X]` claims — one symbol, as everywhere else (WI-926). Legal before, beside, or after the main entry. This is the only route to a member of a type whose declaration one does not own, and it needs no keyword of its own — see the closing note.

**R3 — A secondary entry may add members and spec claims, never identity.** The lists below classify what an entry may contain, and anything unlisted is refused pending classification rather than silently allowed. Where a construct does *not* recurse, that is stated with its reason; recursion is otherwise the default, because a refusal a construct can be nested inside is not a refusal.

- A **nested namespace** does not recurse: it is not a secondary entry to `X` but an ordinary namespace at its own address (`X.Inner`), so `X`'s rules do not reach it. Same for a nested `sort`/`enum`, for the same reason.
- A **`provides Spec language L … end` block DOES recurse.** The grammar admits `rule`, `rule` blocks, `fact` and `proof` inside one, and the loader takes them through the ordinary `load_rule` path — so every hazard the rule ban exists for is reachable one level in. Measured, with this proposal's own non-monotonicity example: `rule q(0) :- not p(2)` answers once; adding `rule p(2)` as an entry's direct content drops it to zero, and adding the *same clause inside a `provides … language anthill … end` block in that entry* drops it to zero identically. A block is a **realization** — it says how an existing declaration is met in a host language — not a second place to define predicates, so it earns no different verdict. Refusing there costs nothing: measured over every `provides` block in stdlib, `anthill-stl`, `anthill-cpp-gen` and examples (15, all `rust` or `cpp`), the contents are only the realization clauses — `artifact`, `carrier`, `operation_map`, `const_map`, `namespace_map` — and `fact Spec[T = Carrier]` claims, which the lists below allow. **Zero rules, zero proofs, zero other facts.** The realization clauses are allowed wherever the block is; they cannot appear as an entry's direct content at all.
- A **description block** — the `{< … >}` a declaration carries — is inert and always allowed. A standalone `describe X {< … >}` is a *different* production and is not this; see below.

Three productions the grammar admits directly in an entry are **not yet classified**, and must be before "anything unlisted is refused" becomes code: a bodyless type alias (`sort Alias = Int64` — the allowed list is qualified "with a body", and the refused list reaches only `sort T = ?`); the standalone type-parameter binders `sort ?T` / `sort [T]`, where the braced spelling has a body and so is admitted by a list meant to ban it; and `describe`, which is not inert — it asserts `DescriptionInfo` facts, which the fact ban below reaches, and it names a *target*, so it writes about a declaration another entry may own, the objection raised against a foreign-target proof.

**Allowed — stated explicitly, because it is the point of the mechanism:**

- **operations** — the dispatch surface; an `operation` block is sugar for them and follows them;
- **consts** — members, not on the dispatch surface;
- **a nested `sort` / `enum` with a body** — it declares a *new type at its own address* (`X.Inner`), so it is that type's **main entry**, not a declaration about `X`. Same reading as the nested namespace above, and the restrictions do not recurse into it. (`sort T = ?` stays refused: that one *is* a type parameter of `X`, which is `X`'s identity.);
- **a `proof` whose target is declared in the same entry** — see below;
- **A SPEC CLAIM, written `provides` — `provides Spec[X]`, or a host `provides Spec language L … end` block.** A secondary entry is the sort's own scope, so there is nothing to refuse in the claim itself: the same declaration one level out is uncontroversial, and moving it next to the member that backs it is what §6.3/038 already asks for — **a satisfaction fact belongs in the closure where its backing exists**. A secondary entry that may not carry the spec claim for the members it supplies could never make a foreign carrier satisfy a spec, which is most of why one writes a secondary entry at all. The backing obligation must hold for a claim placed there exactly as it does one level out (WI-978 — today it does not run at all). The block is allowed; its INTERIOR is governed by these same two lists, per the recursion rule above — its realization clauses (`artifact`, `carrier`, `operation_map`, `const_map`, `namespace_map`) and the spec claims it carries are allowed, and a rule, any other fact, or a foreign-target proof written inside it is refused exactly as it would be one level out.

  **The other spelling of the same claim — `fact Spec[X]` — is refused HERE, though it means the same thing.** Not because the claim is unwelcome but because in a secondary entry it cannot be told from an ordinary parameterized data fact; see the fact ban below for the measurement and for when this lifts.
**Refused, each naming the sort:**

- an `entity` — a constructor is identity, and R1 says identity is written once;
- a `sort T = ?` or a type-parameter list — same reason;
- a sort-level **`requires`** — the requirement slots a type's frames carry are its structure, so the same rule reaches it. **If you want a `requires`, define a sort.**
- a **rule** whose head does not *introduce*, or whose predicate has clauses in another entry — the two conditions below. A `rule` block is sugar for rules and follows them; a dot rule and an operator rule never introduce, so both are always refused. **Enforced today as: every rule, no case analysis** — see "what an implementation does today";
- a **`proof` whose target is declared in another entry** — a proof is not a pure consumer of the knowledge base: verification calls `set_proof_result`, writing `VerdictWrite::Discharged { witness, solver }` or `FailedUnknown { reason }` **back onto the target rule**. So a proof mutates the state of a declaration it may not own, and the same condition the rule clause uses applies — the entry that declares the target may prove things about it, and nobody else. (What *reads* a discharged verdict, and therefore how much behaviour this changes, is not established here.);
- **EVERY fact, and any constraint.** They need no policy of their own: *facts are rules*, so a fact is a rule with no body and a constraint a rule with no head, and the rule ban above already reaches both.

  **Written as an exception to the ban, not as a list of bad facts.** The default is refuse — being a fact is exactly what makes it refusable — and the exception is the `provides` DECLARATION, which is not a fact at all. Spelled the other way round ("facts are fine, except…") the list would have to enumerate every harmful shape, and a new one would arrive allowed.

  **TODAY THE CARVE-OUT CANNOT BE MADE EXACTLY.** The loader already has the discriminator — `maybe_emit_fact_provides_info` — but it recognises a spec claim by SHAPE: the fact's functor is a sort with at least one type parameter. Measured, that cannot tell a spec from a parameterized DATA sort: `sort Box { sort T = ?; entity box(v: T) }` with `fact Box[T = Int64]` is recorded as "Int64 provides Box", against a real spec claim recorded correctly and an ordinary `fact Point(x: 1, y: 2)` correctly recorded as neither. So a shape-tested carve-out would admit a data fact over any parameterized sort — which is exactly the population the default-deny rule exists to refuse.

  **So the carve-out is spelled, not inferred: in a secondary entry the claim must be written `provides`, and a `fact` is refused there.** `provides X[…]` is a declaration the grammar recognises, so admitting it needs no discriminator at all; `fact` needs one that does not exist. This costs nothing measurable — the corpus contains no secondary entries, so nothing is migrated — and it is the direction 058 §4 already prescribes, which proposes retiring the `fact X[…]` spelling in favour of `provides X[…]`. A secondary entry is simply the first place where the ambiguous spelling is not merely redundant but unsafe.

  **It is staged, not final.** The restriction is narrower than the intended rule (a spec claim is allowed; only one of its two spellings is), and it lifts the moment either half of the root cause is fixed: **nothing declares a sort to BE a spec** — there is no `spec` keyword and no `SymbolKind::Spec`, so every reader infers it from shape — or 058 §4 retires the `fact` spelling and the question stops arising. Until then the refusal is the honest instrument, because the alternative is not "allow spec claims" but "allow every parameterized data fact and call it a spec claim".

**An import resolves only in the file it is written in, and it is spent before entries are merged.** An import maps a local name to a `Symbol`; once names are `Symbol`s it has no further job — measured, the scope import table has exactly one reader, `resolve_in_scope`'s step 1b, and the typer never consults it. R2's one scope is therefore no argument for sharing imports: **the scope is shared for the members an entry DECLARES**, and an import declares nothing. Members can be shared while imports stay lexical. So an import cannot reach across a merge, and R4 has nothing to say about one.

TODAY IT IS SHARED BY ADDRESS INSTEAD — the divergence, not the rule. Measured: `namespace demo { namespace Rec { import other.f } }` **in a separate file** changes what a bare `f` resolves to inside `sort Rec`'s body in another file, `1` to `2` in an unedited body. It does not leak *outward* (an import in a nested `namespace Inner` never reaches the enclosing namespace), so the reach is the address, not the text. **This is not about secondary entries**: the same flip happens between two ordinary `namespace demo` blocks with no sort at that address, so it is neither caused nor fixable here. WI-995.

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
2. **one entry owns the predicate** — every clause of that head is written in that same entry, keyed as the Definitions individuate one: the main entry, or one file's text at that address.

Each condition answers a measured failure of the naive "fresh head is harmless" reading.

*Without (2), two entries silently compose one predicate.* Two secondary entries **in different files** that each introduce `freshp` do not collide — both clauses join it, `freshp(1)` and `freshp(2)` both answering. Neither captured a pre-existing name, so R4 is silent, and the predicate ends up assembled by two parties that never agreed on it. Condition (2) is what R4 cannot express, because a predicate legitimately has many clauses; it is a rule about where they may be *written*.

Two blocks in ONE file are one entry, so they compose `freshp` freely — deliberately. That is one author writing two paragraphs, which is exactly the case condition (2) has no reason to refuse.

*Without (1), the head is not really new.* A main entry carrying `rule q(0) :- not freshp(1)` answers `q(0)` once; add `namespace Rec { rule freshp(1) }` and it answers zero times, though the head was as fresh as heads get — the symbol lands at `X.freshp`, exactly where the main entry would have put it. The reference existed before the definition did. That is reachable in **rule bodies and constraints only**: measured, both load while naming a predicate that resolves to nothing, and an operation body naming one is already refused (`unknown functor`). So it is precisely WI-895's gap, and (1) is only *checkable* once it closes — a name that resolves to nothing must stop being referenceable before "resolves to nothing" can mean "no one refers to it".

Two shapes are excluded by (1) rather than by a clause of their own, which is the sign the condition is the right one: a **dot rule** and an **operator rule** carry the desugar's functor (`dot_apply`, `add`), and a desugared conclusion introduces nothing (§"A rule-introduced functor is scoped where it is written") — so neither is ever fresh, and the `[simp]`-fires-in-the-typer hazard cannot arise through them.

**What an implementation does today: refuse every rule in a secondary entry, with no case analysis on the head.** Not as a placeholder — the narrow rule is not yet enforceable. Condition (1) is undecidable while text order decides whether a head introduces (R6/WI-980), and it is unsound while a body may reference what resolves to nothing (WI-895, Open). The narrow rule lands when both are closed, and needs no further design: conditions (1) and (2) are decidable at scan time, (2) by grouping a predicate's clauses on `(address, SourceId)` with the main entry as its own group — the key the Definitions give, and one the scan already carries.

One honest limit remains: this does **not** close the underlying hazard. A rule extending a predicate declared elsewhere is non-monotone wherever it is written — an ordinary nested namespace does the same, and so does the sort's own body. R3 closes the route this proposal opens; the general case belongs with R6 and the module question.

**R6 — A rule head's binding does not depend on declaration order.** The policy is not in question and is not changed here: §"A rule head functor is resolved, not declared" (WI-896) says the functor runs the ordinary ladder and the rule contributes a clause to whatever it lands on, *introducing* the name — scoped where written — only where the ladder finds nothing. What is undefined today is **when "the ladder finds nothing" is evaluated.** Measured, it is evaluated against a half-built name table, so textual order decides:

| written | binding |
|---|---|
| `rule p(1)` at namespace level, **then** `sort Rec { rule p(2) }` | both clauses join `p`; no `Rec.p` exists |
| `sort Rec { rule p(2) }`, **then** `rule p(1)` | two predicates — `Rec.p` and `p` — one clause each |

and identically for a secondary entry in place of the sort body, which is why this is not a question about secondary entries. It is stated here because R3's refusal of rules would otherwise rest on behaviour that is itself undefined.

**The binding is computed against the finished program**, never against the prefix of it that happens to be scanned: scopes outermost-first, all of a scope's heads together, so that the two rows above give the same answer — the first one, since in the finished program `p` does resolve from inside `Rec`. This is the invariant every *other* name already has (pass 1 defines every name across every file before any pass 2 runs — the WI-321 cross-file recursion invariant); a rule head escapes it only because its introduction happens during that same pass. A scope that wants its own name where an enclosing one resolves **declares** it — the remedy §WI-896 already prescribes ("to introduce a name that already resolves, declare it"). Tracked as WI-980.

**Why R3 refuses a `requires` where it allows a spec claim.** (Back to R3's two lists — R6 above is stated where it is because R3's rule ban would otherwise rest on undefined behaviour.) The asymmetry between the refused sort-level `requires` and the allowed spec claim is the point, and it is not about dictionary layout. `dict_layout` bundles the spec's chain then the provider's **over the whole knowledge base** (WI-857), so a secondary entry re-lays-out precisely what editing the definition re-lays-out — there is no cost specific to a secondary entry to price there.

The line is **who the declaration binds**. A spec claim is a *fact about* the type — additive, and true or false on its own terms. A `requires` is a constraint *on the type's callers*: every use of its operations must now supply that dictionary. A secondary entry is written by someone who is not the type's author and often not even its user, so allowing it there lets a third party add an obligation to everyone who already uses the type. That is the downstream-added-superclass move, and no module system permits it.

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
- **A secondary entry may not redeclare a member the main entry declares AND IMPLEMENTS** — 058 §3.6's *no-displacement*, in its own words: **fill silence, never overwrite speech**, so that no one line flips what every linked library's bracket-less dispatch already means. "Implements" is not "has a body"; see below, where measuring it is the whole difficulty.

  **A declaration with no IMPLEMENTATION is silence, and may be filled.** A signature that states the *interface* and nothing about the *implementation* leaves a question open, and a secondary entry answering it displaces nothing. Measured: `sort Rec { entity Rec(n: Int64); operation render(r: Rec) -> Int64 }` plus `namespace Rec { operation render(r: Rec) -> Int64 = r.n }` loads and dispatches today. The **signature is the main entry's** and the filling entry may not change it; that is what makes this a contract rather than a second declaration.

  **"No anthill body" is NOT the test, and using it would silently discard the fill.** An operation with no body may already be implemented by a host mapping or a resolver builtin, and the interpreter reaches those FIRST: `call_op_sym` and `call_op_bridged` both return a registered builtin before any body lookup, and an `operation_map` clause arrives there AS a registered builtin (`register_operation_mappings` → `register_builtin_sym`). Measured against `sort String`'s `isEmpty` — declared body-less in stdlib, mapped to `string_is_empty` in `anthill-stl` — a secondary entry supplying `operation isEmpty(s: String) -> Bool = false`, wrong for every input, **loads clean and never runs**: `"".isEmpty()` still answers `true` and `"x".isEmpty()` still `false`, identical to the control with no secondary entry at all. The author is told nothing.

  That shape is not a corner: it is how every host carrier is written. Counting `operation_map` entries in `anthill-stl` — each one a declaration whose implementation is the host artifact's — `Float` has 29, `String` 13, `Int64` 9, `BigInt` 7, `persistence` 6: **64 members** that read as silence under a body-only test. So **silence means no implementation from ANY source** — no anthill body, no `operation_map`/`const_map` entry for the target language, no registered builtin — and a fill over a declaration backed by any of them is refused, naming the backing. A `[simp]` equation is a fourth case and a different one: it does not back the operation (WI-818/885) but the typer rewrites LHS→RHS before dispatch, so a filled body is dead at every rewritten call site and live anywhere else. That split is why it must be named rather than folded in.

  The check is decidable but **not in pass 1 beside the ledger**: host mappings are read from `anthill.realization.OperationMapping` facts the loader emits, so like clause 3 it runs after them.

  This is the rule that carries **spec-author and implementer as different hands** — one writes the sort and its signatures, another (often an AI agent) supplies the bodies in anthill, and the interface it must meet is checkable rather than conventional. Without it the flow has only the spec-sort-plus-`provides` route, which forces the author to publish a separate spec sort even when the interface belongs to the type itself. Clause 1 still applies to *two* fillers: two suppliers of one member name are refused whether or not the main entry declared it.
- **A declaration may not capture a name it does not override.** The two clauses above are keyed on *members colliding*, and that is not enough: a name can already mean something without being a member. Measured — a main entry calls a bare `f(…)` that resolves through `import lib.f` and answers `1`; add a secondary entry declaring `f` and the *same unedited body* answers `2`. Nothing named `f` was a member, so the clauses above admit it, and existing code silently changed meaning.

  **Stated over every declaration category that can win name lookup — not over operations, and not over members.** Both narrowings are refuted by measurement: the other two categories a secondary entry may declare capture just as silently, and a const captures without ever joining the dispatch surface.

  | the capturing declaration | measured |
  |---|---|
  | a **const** — `namespace Rec { const LIMIT: Int64 = 2 }` against a body reading a bare `LIMIT` through `import lib.{LIMIT}` | `1` ⇒ **`2`**, loads clean |
  | a **nested sort** — `namespace Rec { sort Code { … } }` against a member whose signature returns an imported `Code` | `100` ⇒ **`200`**, loads clean; the body constructs the nested type and `.tag()` dispatches on it |

  A type capture is not excused by *"dot dispatch never routes through it"* — it routes straight through it, the captured type being what the receiver dispatches against. Nor is it caught by accident: give the two types different fields and it surfaces as `'Code' has no field 'v' (declares: w)`, a loud error for the wrong reason, but same-shape nothing complains. A rule may not rest on the types happening to disagree.

  A const is a member (it is in scope bare, and reachable through `import X.{…}`) but is **not** on the dispatch surface, so clause 1 does not reach the capture either — which is why this clause is stated over lookup rather than over membership.

  The qualifier "it does not override" is not a hedge; it is what the corpus forced. Counting every declaration whose short name already resolves in its declaring scope gives **61 sites** across stdlib, `anthill-stl`, examples and `anthill-todo` — so the unqualified clause is unimplementable. The breakdown says why, and each exclusion is principled rather than a carve-out for convenience:

  | class | count | why it is not a capture |
  |---|---|---|
  | a **parameter** shadowing an operation (`Float.pow.exp`, `KB.assert.kb`) | part of 38 | a binder is not a declaration |
  | a **type parameter** shadowing a type (`IndexedSeq.Effect` — `sort Effect = ?`) | part of 38 | also a binder; R3 refuses `sort T = ?` in a secondary entry outright, so it can never be the capturing declaration there |
  | an **entity variant** shadowing a type (`TypeExtractor.Error`, over `effects.anthill`'s `sort Error`) | rest of 38 | a constructor is identity — R3 refuses an `entity` in a secondary entry, same as above |
  | a member **overriding a spec operation** (`List.length` over `IndexedSeq.length`) | 23 | this is how a sort implements what it provides |
  | **no override relationship** | **0** | the hazard, and the corpus no longer contains one |

  The middle two rows are worth keeping apart, because read together as "a type name shadowing a type" they look like nested type declarations and neither is: `IndexedSeq.Effect` is a type parameter, `TypeExtractor.Error` an entity variant of `enum anthill.prelude.TypeExtractor`. R3 already refuses both spellings in a secondary entry, so widening the clause to types costs **no migration** — and the shape that does capture, a nested `sort` with a body inside a secondary entry, occurs **zero** times in the corpus.

  So on the *no-override* hazard the clause bites **nothing in the corpus**. Its whole migration is the two sites the narrowed exclusion below stops covering, which an existing warning already names. Census: WI-981, less the two WI-982 removed.

  **The repair is to delete the capturing member, not to rename it** — whenever the member's own answer does not read its receiver. A receiver nothing reads is dispatch ceremony, not an interface: it exists so the name dot-dispatches, and it is also the thing that captures. Renaming keeps two names for one question; deleting leaves the one the caller already had. Reach for a rename only when the member genuinely answers about its receiver and the collision is coincidence.

  This is the clause's one real hit, and it is the argument for keeping it. Both sites were `reflect.KB.nonvar` / `reflect.KB.ground`, and the capture was the *visible end* of a defect: the captured names were unreachable in value position, and the same question had two answers that disagreed by carrier. The shadow was the smaller half — see WI-982.

  **The instrument is a refusal**, like the two clauses above it. The only argument for a warning was blast radius, and the corpus holds none.

  **THE EXCLUSION IS `provides` ALONE.** A sort that merely *requires* a spec earns no permission to rebind that spec's operations — §8.7 is explicit that such an operation "is **not** overriding it: that operation is unrelated", and a name one has not overridden is a name one may not capture. The wider `requires`-or-`provides` reading is tempting because 19 of the legitimate cases reach the spec's member through the `requires` link, but that is the **route** the name resolved by, the very quantity the paragraph below says the check must not key on. Keyed on the **relation**, measured over the 183 sorts that declare operations:

  | the sort's relation to the spec whose op it shadows | sites |
  |---|---|
  | **provides** it (transitively, as `sort_provides` reads it) | **40** |
  | **requires** it only | **2** — `FiniteCollection.filter` / `.map` over `Iterable.filter` / `.map` |

  Counted per *triple*, not per declaration, so it does not sum to the 23 above: `List.collect` shadows both `FiniteCollection.collect` and `FiniteStream.collect` — one declaration in that census, two rows here.

  So the narrow exclusion costs **2 sites**, and the clause uses the spec's word with the spec's meaning rather than against it.

  **And the 2 are already flagged.** WI-346's `check_requires_shadows` computes this same set by the same predicate — direct `requires`, minus transitive `sort_provides` — and measured at full load it emits exactly two warnings, `FiniteCollection.map` and `FiniteCollection.filter` over `Iterable`. So the narrowing does not *discover* a migration; it **upgrades an existing warning to a refusal on the same two declarations**, and clause 3 subsumes WI-346 rather than sitting beside it. Whether those two are a genuine refinement or the coin flip `ordered.anthill` warns of — *"a carrier that provides BOTH specs two `sort_ops` entries for one short name, and which one wins is HashMap-iteration order"* — is the question the upgrade forces, and is the whole of its cost.

  A caution on measuring this: no test helper surfaces load warnings. `try_load_kb_with_files` discards `load_all`'s `Ok(_)`, and `load_stdlib_kb_with_source` returns the result of loading the *probe source* against an already-built stdlib. Both report zero warnings for a corpus that emits two.

  Like the two clauses above it, this one is stated over the **scope**, not over secondary entries: measured, the same flip happens when the capturing operation is written in the main entry, so an entry-local rule would patch the wrong object and would split the one scope R2 rests on. §6.3 records the hazard for the long form as a caution already (WI-935); this makes it a check, for both spellings at once.

**Is R4 implementable?** Each clause is decidable, and each has a measured blast radius — but they need two different mechanisms, and clause 3 needs a predicate the route alone does not give.

| clause | sites in the corpus | what it needs |
|---|---|---|
| 1 — two suppliers of one member name | **0** | a pass-1 declaration ledger |
| 2 — a secondary entry filling a member that is **already implemented** | **0** | the ledger, plus *has an implementation* per declaration — body, host mapping, or builtin |
| 3 — capturing a name it does not override | **2** (the `requires`-only pair; **0** on the no-override hazard, was 2 before WI-982) | the override relation, after pass 2 |

Clauses 1 and 2 cannot be checked by walking symbols: `define` **merges** two same-named declarations in one scope into one symbol, so by the time symbols exist the duplication is gone. They need each *declaration* recorded as pass 1 makes it, keyed on (scope, local name) — R1's key too, and for the same reason: it records the declaration as written, before §6.3's collapse. One piece of machinery for both. Measured that way over 427 operation/const declarations in stdlib, `anthill-stl`, examples and `anthill-todo`: **no name is declared twice in one scope**, so both clauses land with no migration. (The zero is honest but easy: the corpus contains no secondary entries at all, so clause 2 has nothing to bite on yet. Clause 1 also covers two same-named operations in one *main* entry, and that is genuinely zero.)

Clause 2's *has an implementation* is the one part the ledger alone cannot answer. A body is visible in pass 1; a host mapping is not — it is read off the `anthill.realization.OperationMapping` facts the loader emits from a `provides … language L … end` block, which may sit in another file entirely (`String`'s is in `anthill-stl`, its declaration in `stdlib`). So clause 2 splits: the ledger decides *redeclared*, and a post-pass-2 read decides *already implemented*.

Clause 3 must key on the **override relation** — does the declaring sort *provide* the spec whose operation it shadows — and **not** on the route by which the name was reached. The measurement is why: 4 of the legitimate overrides arrive through an `import` of the spec's member rather than through the `requires` link, so a route-based rule refuses exactly the wrong four. That relation is known only after pass 2, so the check runs there, not in pass 1 beside the ledger. `sort_provides` already computes it, transitively, and is what WI-346 uses.

It must also not assume the captured name has a **declaration**, nor that it is an operation. `register_builtin_tag` mints a symbol for a name nothing declares — `symbols.define(short, qualified, SymbolKind::Operation, scope)` — so a resolver builtin can be an operation by *kind* with no declaration behind it: measured, `anthill.kernel.find_dictionary` carries kinds `["Operation"]` and appears in no `.anthill` file. Nor is `Operation` even the reliable kind: the tag on `anthill.reflect.Expr.ho_apply` rides an **Entity** symbol, so a check keyed on `kind == Operation` misses it. The check reads the override relation, which such a name simply lacks; it must not reach for a declaration, or for a kind, to read.

The first two clauses are silent today: last-wins between two secondary entries, and the secondary entry winning over the main one — which is what makes a secondary entry indistinguishable from monkey-patching. Note that a sort's own member does **not** outrank the other supply routes at dispatch: WI-842 **refuses** a tie between a member, an instance fact's binding, and a witness sort's member, naming each by its route, and it deleted the ranking that used to prefer the member. That is the standard R4 restores — a second supplier competes and is refused, rather than overwriting where no check can see it.

**A spec claim declared in a secondary entry is arbitrated by 058, not here.** A secondary entry's `provides Spec[X]` is an ordinary one: `one_default` refuses a second default for a `(spec, carrier)`, and the nameability gate decides whether rivals may coexist at all — *"`one_default` arbitrates all rows regardless of origin"*. 058 already contemplates this mechanism by name, prescribing "mark inline when you own the carrier **or ship its canonical companion**". Two consequences worth stating, both inherited rather than invented: a carrier that provides for itself has an inferred default, so a secondary entry declaring a rival **violates `one_default`** — the orphan case is already refused where it would displace; and since 058 §4 proposes retiring the `fact X[…]` spelling in favour of `provides X[…]`, a secondary entry **must** be written in the latter — R3 refuses the `fact` spelling there, for the reason given with the fact ban.

**R5 — §6.3's remedy, restated.** To give a free-standing entity operations: rewrite it into the long form when you own the declaration, or write a secondary entry when you do not. Both are one symbol.

## Where this leads: compilation modules

The things one wants to price about a secondary entry — the `requires` R3 refuses, the orphan `provides` it allows, and why its members are visible without an import — are **one question**, and it is not about secondary entries.

A **dictionary layout is defined over the whole knowledge base.** So is provider search, so is the member set a receiver dispatches against. Every load sees every file, nothing is compiled separately, and therefore no declaration anywhere can invalidate a *previously compiled* call site — there are none. Under that model a secondary entry is exactly as consequential as an edit to the definition: **there is no boundary for anything here to cross.** That is why R3's refusal of `requires` rests on *who a declaration binds*, and R4's on 058's nameability, rather than on any layout cost — there is none to charge.

Each of the three becomes a real question the moment there is one:

- a `requires` added by a downstream unit changes an upstream type's dictionary layout — which is why R3 refuses it outright rather than pricing it;
- a `provides`/`fact Spec[X]` for a foreign carrier is an **orphan instance**. Within one KB, 058 already decides it (`one_default`, nameability). What no whole-program rule can reach is two units that each declare one and are **never loaded together** — neither `one_default` nor R4 ever sees the pair;
- global attachment means a unit's member set depends on which other units happen to be loaded — and, per the Definitions, so does whether a unit's `namespace X` is an ordinary namespace or a secondary entry at all.

**The likely shape of the answer: open and closed packages.** A package that is *closed* admits no secondary entry to its addresses from outside itself; an *open* one does. That single axis answers all four at once — a downstream `requires` and an orphan spec claim are simply unwritable against a closed package, its member set is fixed at its boundary, and the classification flip above cannot be caused from another package, since no one else can enter its addresses. Within a package the non-locality remains, where it is local enough to see. Two things would have to be decided with it and are not decided here: whether closed is the **default**, and whether openness is declared by the package that owns the address (a permission) or claimed by the one extending it (a request). This proposal takes no position beyond noting that it is one mechanism rather than four.

These are the classic separate-compilation constraints (Haskell's orphan rule, Rust's coherence), and Anthill meets them through this one mechanism. **This proposal deliberately does not invent a module system to answer them.** It records that R3's line and R4's KB-wide arbitration are *whole-program* answers, correct exactly as long as the program is whole — and that a compilation-module design is what would revisit them, together, as one decision rather than three.

R4 survives either way, because it is 058's rule and not a new one: a module system would tighten *where* the arbitration happens, not what it decides.

## Spelling — settled, not open

`namespace X` is the spelling. No keyword is introduced, and no noun beside
*secondary entry* is: 001 deferred a `companion` block and 058 speaks of a
"canonical companion", but a second word for one thing only raises the question
of what a companion-less secondary entry would be. The mechanism needs no
grammar, works today, and is named by what it is.
