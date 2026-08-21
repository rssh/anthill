# 059: Secondary Entries — one scope, a main entry and secondary ones

## Status: Draft (2026-08-08; operation policy revised after WI-1049). Written from WI-975, which asked what a second declaration of one name means and found two mechanisms sharing one spelling. **A type is defined once; a `namespace` at its address is a SECONDARY ENTRY to that type's scope, not a separate module attached to it.** Measurement claims below are taken from the Rust loader with both-sides controls; the rules and module discussion are prescriptive.

## Relates to: 058 (modular instances — R4 reuses §3.1's coexistence-gated-on-nameability principle; 058's "canonical companion" is a separate witness sort, not this mechanism), 001 (sort/domain unification — its "Name Uniqueness" rule refused reopening by name; its deferred `companion` is likewise a separate address, not R2), §6.3 (entity sugar; "operations move a free-standing entity to the long form"), §6.7 / WI-279 (dot dispatch resolves a member **declared on the receiver's sort** — there is no free-function fallback), WI-925/926/928/946 (one written name, one symbol, a category SET), WI-1049 (one operation declaration per name per scope), WI-857 (requirement-dictionary layout), WI-818/876/931 + 038 (what backs a `provides`/`fact Spec[X]`, and where a satisfaction fact belongs).

## The problem

Dot dispatch requires **membership**: `x.f()` resolves `f` on the receiver's least declared sort, and a free `operation f(r: Rec)` beside the type is not a candidate — measured, the prefix call `f(r)` evaluates while `r.f()` is refused `no such member (dot dispatch)`. So a free-standing `entity X(…)` gains a dot-callable operation only by acquiring a **member**.

The loader exposes two candidate spellings; one is already refused for incidental scope-wiring reasons, while the other works but was not specified.

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
| a **generic caller** reaches that member through `requires Spec[T = X]` — control: the same op in the sort body | `111` both ways (WI-1008). It answered only in the control until the entry's operations joined `SortInfo.operations`: that record was main-entry-only while `MemberInfo` and `OperationInfo` both listed them, so everything keyed on it — the requires dictionary above all — resolved to the spec's body-less declaration and died `OperationBodyMissing` on a program that loaded clean. The claim's placement is not the discriminator; the **op's** is |
| a secondary entry holds `fact S[T = X]` or a host `provides … language … end` block | loads, and the backing obligation now holds there as it does one level out (WI-978 — the check was never the problem; the *emitter* filed no provision when the main entry was a free-standing `entity`, since it read the symbol's FIRST category rather than asking `has_kind(X, Sort)`) |
| a secondary entry on a **stdlib** sort: `namespace anthill.prelude.Int64 { operation twice(x: Int64) = x + x }` | `7.twice()` ⇒ `14` |
| a secondary entry at a *different* address (`ns.ext.Rec`, not `ns.data.Rec`) | not attached — attachment is by qualified **address**, never by import |
| a secondary entry's **const**, against an operation declared beside it: symbol in scope / bare inside / `import X.{…}` then bare / `receiver.…` | yes·yes·`5`·**refused** — against the operation's yes·yes·`6`·`6` |

So the three questions this proposal was asked have one answer: **yes, in both directions.** `requires`/`provides` written in a secondary entry are the *sort's*; the sort's members (type parameters included) are in scope in a secondary entry; and the main entry sees a secondary entry's members. What is missing is not wiring — it is **bounds**.

The remaining bounds are mixed today:

| shape | today |
|---|---|
| two secondary entries declaring the same **operation** name | **refused at load** — WI-1049 records declarations, not the merged symbol |
| a secondary entry redeclaring an **operation** the main entry declares | **refused at load**, whether either declaration has a body |
| `entity` inside a secondary entry | loads and constructs, but is **not** a variant — surfaces later as `expected C, got Blue` |
| a second `sort C { … }` body beside `sort C { entity Red }` | **silently reopens** — both variants construct, the second body's members dispatch |

## Definitions

A sort's scope has one or more **entries** — texts that declare into it. Syntactically an entry is a **`namespace`, `sort`, `enum` or `entity` declaration with definitions inside**; those four are what declare into a scope, and nothing else does. An address without a sort has no entries in this sense at all; it is an ordinary namespace, and this proposal says nothing about it.

- **Main entry.** The `sort X … end`, `enum X … end` or `entity X(…)` that *defines* the type: its constructors, type parameters and requirements. **At most one** exists (R1) — an address may have none, and then there is no type there.
- **Secondary entry.** A `namespace X` at an address that **has a main entry**. It *adds to* `X`'s scope and defines nothing about the type. Any number may exist. Attachment is by address, never by import.
- **One entry, individuated.** The **main entry** is the single `sort`/`entity` declaration, wherever it sits. A **secondary entry** is all `namespace X` text at that address **within one file**: two `namespace X … end` blocks in the same file are ONE secondary entry, and the same text in a second file is a second one. A file holding both the declaration and a `namespace X` block therefore holds two entries — main and secondary — which keeps R3's entry-local rule/proof ownership conditions meaningful.

  The **file** is the unit for two reasons. What the entry-keyed rules guard against is a predicate "assembled by two parties that never agreed on it", and two blocks in one file are one author making one edit — a file boundary is the smallest place where *two parties* is real. And it is the unit this proposal already uses: an import resolves only in the file it is written in. One notion of locality, not two.

  It is also the only one that is checkable. Every declaration carries a `SourceSpan` with its `SourceId`, and `file_idx` is threaded through both scan passes — but two `namespace X … end` blocks at one address compute the same qualified name, reuse the same symbol, and alloc the same hash-consed scope term, so no per-block identity exists to group by. "Entry = one block" would have to mint one first.

  **What "with definitions inside" leaves open: a type alias.** `sort X = T` puts its definition after the `=`, not inside, so it is not an entry by that reading. But measured, `sort Path = String` beside `namespace Path { operation len(p: Path) -> Int64 }` loads, `Path.len("x")` answers, and the loader's own diagnostic calls `len` "a member of sort Path" — the alias behaves as a main entry. Either an alias is one, with its definition written outside its body, or that attachment is a divergence. A bare `entity Foo` with no fields asks the same question. (`enum` needs no such call: it is named above, and measured — `enum Colour { entity red }` beside `namespace Colour { operation code }` dispatches `Colour.code(red)`.)

- **Ordinary namespace.** A `namespace X` at an address with **no** main entry — the overwhelmingly common case, and every namespace in the language until a sort shares its address. It declares a module, not members of a type, and **nothing in R3 or R4 reaches it**: a rule, an entity, a nested sort are all as legal there as they have ever been. Only the presence of a main entry turns the same text into a secondary entry.
- **Member of `X`.** A name declared in `X`'s scope, by any entry. Reachable bare from within that scope, and from outside through `import X.{…}`.
- **Dispatch surface of `X`.** The members reachable as `receiver.name(…)`. Its elements are exactly the **operations**: a const is a member and is not on the surface (measured above), in the main entry as much as in a secondary one.

**The two are told apart by the address, not by the text.** `namespace X` is written identically either way; what decides is whether a sort exists at `X` — measured, a plain namespace's symbol is `Namespace` alone, and one beside a main entry carries `Sort` too, so the question an implementation asks is `has_kind(X, Sort)`, the same `has_kind`-not-`kind_of` reading WI-956 settled for the gates.

One consequence is uncomfortable and belongs on the record: **a namespace becomes a secondary entry because someone else declared a sort at its address.** Written alone, `namespace Utils { rule p(1) }` is an ordinary namespace and its rule is legal; let another file declare `sort Utils` there and the same text is a secondary entry whose rule R3 refuses. Nothing local to the namespace changed. This is the whole-program property again, in the classification itself rather than in dispatch — see "Where this leads".

**"Main" and "secondary" name roles, not order.** A secondary entry may be written first, in the same file or another, and read first by the loader; which text the loader happens to reach first decides nothing. Measured in both orders: WI-979 makes the classification (`has_kind(X, Sort)`) and eponymous collapse order-independent, and WI-994 does the same for visibility of the sort's variants to its enclosing scope.

## The rules

**R1 — A type is defined once.** Two *type* declarations sharing a **(scope, local name)** are a load error naming both spans: `sort X` + `sort X`, `enum X` + `enum X`, and — as **siblings** — `entity X` + `sort X` (§6.3 makes that pair two spellings of one declaration, so it is the same error). Reopening a closed ADT is the harm: today a second body silently adds variants.

**Keyed on the declaration AS WRITTEN, not on the address it ends at**, and §6.3's eponymous constructor is why. `sort Vec3 { entity Vec3(…) }` collapses the constructor onto the sort's own symbol (WI-926), so both declarations end at address `ns.Vec3` — address-keyed, that is indistinguishable from the sibling `entity X` + `sort X` this rule refuses, and a legal shape is rejected. Written-keyed they differ: the sort is `(ns, "Vec3")`, and the entity, declared inside the sort body, is `(ns.Vec3, "Vec3")`. The sibling form stays caught, both halves being `(ns, "Vec3")`. The address cannot tell them apart because the collapse has already erased the difference by the time addresses exist — and that collapse is something §6.3 does deliberately. Measured, the shape is real but small: 4 eponymous sites (`Vec3`, `TotalFloat`, `Duration`, `Timestamp`) among 140 `sort`/`enum` headers across stdlib, `anthill-stl`, examples and `anthill-todo`. WI-997 delivers this type-declaration ledger. Operation declarations now use WI-1049's separate per-load declaration log, because their check is keyed by the one operation symbol and must also distinguish a source declaration from bootstrap pre-registration.

**R2 — A secondary entry declares members of `X`.** What it declares enters `X`'s scope, is scoped by `X`'s type parameters, and may back `X`'s `provides`/`fact Spec[X]` claims — one symbol, as everywhere else (WI-926). Legal before, beside, or after the main entry. This is the only route to a member of a type whose declaration one does not own, and it needs no keyword of its own — see the closing note.

**R3 — A secondary entry may add members and spec claims, never identity.** The lists below classify what an entry may contain, and anything unlisted is refused pending classification rather than silently allowed. Where a construct does *not* recurse, that is stated with its reason; recursion is otherwise the default, because a refusal a construct can be nested inside is not a refusal.

- A **nested namespace** does not recurse: it is not a secondary entry to `X` but an ordinary namespace at its own address (`X.Inner`), so `X`'s rules do not reach it. Same for a nested `sort`/`enum`, for the same reason.
- A **`provides Spec language L … end` block DOES recurse.** The grammar admits `rule`, `rule` blocks, `fact` and `proof` inside one, and the loader takes them through the ordinary `load_rule` path — so every hazard the rule ban exists for is reachable one level in. Measured, with this proposal's own non-monotonicity example: `rule q(0) :- not p(2)` answers once; adding `rule p(2)` as an entry's direct content drops it to zero, and adding the *same clause inside a `provides … language anthill … end` block in that entry* drops it to zero identically. A block is a **realization** — it says how an existing declaration is met in a host language — not a second place to define predicates, so it earns no different verdict. Refusing there costs nothing: measured over every `provides` block in stdlib, `anthill-stl`, `anthill-cpp-gen` and examples (15, all `rust` or `cpp`), the contents are only the realization clauses — `artifact`, `carrier`, `operation_map`, `const_map`, `namespace_map` — and `fact Spec[T = Carrier]` claims, which the lists below allow. **Zero rules, zero proofs, zero other facts.** The realization clauses are allowed wherever the block is; they cannot appear as an entry's direct content at all.
- A **description block** — the `{< … >}` a declaration carries — is inert and always allowed. A standalone `describe X {< … >}` is a *different* production and is not this; see below.

Three productions the grammar admits directly in an entry were left unclassified when this was written; WI-1000 settled all three, and each verdict is stated with the list it belongs to below. In summary:

| production | verdict | why |
|---|---|---|
| a **bodyless type alias**, `sort Alias = Int64` | **allowed** | it declares a NEW TYPE at its own address (`X.Alias`), so it is that type's own main entry — the nested-`sort`-with-a-body reason exactly. "With a body" in the allowed list is there to exclude the `= ?` binder beside it, and an alias's definition is a concrete type, not a hole. Measured: `sort Code = Int64` in a secondary entry, used as a sibling operation's return type, loads and the operation answers |
| the **type-parameter binders** `sort T = ?`, `sort ?T`, `sort [T]`, `sort [F] { … }` | **refused** | a type parameter is `X`'s identity. All four are one declaration: the converter desugars the per-statement spellings to the enclosing-list IR (WI-454), the bare ones to `sort T = ?` and the braced one to an `is_type_param`-marked carrier — so the "braced spelling has a body" objection dissolves, the marker being what the check reads rather than the body. Measured, it is also recorded INCOHERENTLY: written in an entry it reaches `add_type_param` (the entry's scope IS the sort's scope) while `SortInfo(name: X).parameters` stays `nil`, against `[T]` for the identical declaration in the main entry — WI-1008's split again, in the one field R3 says must never be written from here |
| a standalone **`describe X {< … >}`** | **allowed iff its target is declared in the same entry** — the `proof` condition, verbatim | of the two objections to it, only the target one bites. The fact objection does not single it out: the inline `{< … >}` block this list calls "inert and always allowed" asserts the very same `DescriptionInfo` predicate, from a nested sort or an alias in the same entry. The target objection is the one this proposal already raises against a foreign-target proof, so `describe` takes that rule rather than a rule of its own. A SECOND reason stood here when WI-1000 decided this, and is recorded because the verdict outlived it: refusing `describe` outright would then have cost a capability rather than nothing — measured, an operation's own inline description block emitted **no** `DescriptionInfo` at all (the grammar parsed a `description` field on `operation_declaration`; `parse::ir::Operation` had nowhere to put it), so a standalone `describe` was the only way to document a member, including one the entry itself declares. **WI-1070 closed that drop** — an `operation`'s and a `const`'s own block now emits like a sort's, in both operation spellings (kernel-language.md §4.1, §5.9) — so the capability reason is spent. The verdict is unchanged, and surviving the loss of that reason is the test of it: it keys on the TARGET, not on the absence of an alternative. |

Corpus cost of all three: **zero**. There are no secondary entries, and no standalone `describe` anywhere in stdlib, `anthill-stl`, examples or `anthill-todo`.

**The target set the last row is checked against is "written in this entry", not "legal in this entry".** A refusal does not stop the declaration loading, so a `describe` beside a refused `entity` of that name really is about this entry's own declaration; reporting it as foreign would raise a second diagnostic for one root cause and name the wrong reason. The set is every named direct declaration of the entry — an unlabeled rule contributes nothing, correctly, having no citation handle for a `proof` or a `describe` to name it by either.

**Allowed — stated explicitly, because it is the point of the mechanism:**

- **operations with a runnable Anthill body** — the dispatch surface; an `operation` block is sugar for them and follows them. A body-less operation is refused in a secondary entry: that spelling reserves an implementation slot, while a secondary entry may only add a complete new member. A `[simp]` equation is not a body (WI-818/881), so it does not satisfy this condition;
- **consts with a defining value** — members, not on the dispatch surface. The body requirement above reaches them for its own reason, not by analogy: a value-less `const` reserves a host slot for a `const_map` entry, `const_map` being the const-level peer of `operation_map` (§10.2 / WI-889), and reserving a slot on a type one is extending is the main entry's to do. This list said only "consts", written before that peer was weighed (WI-1000);
- **a nested `sort` / `enum` with a body**, and equally **a bodyless type alias `sort Alias = T`** — each declares a *new type at its own address* (`X.Inner`, `X.Alias`), so it is that type's **main entry**, not a declaration about `X`. Same reading as the nested namespace above, and the restrictions do not recurse into it. (`sort T = ?` stays refused: that one *is* a type parameter of `X`, which is `X`'s identity.);
- **a `proof` whose target is declared in the same entry**, and — WI-1000, same condition — **a standalone `describe` whose target is declared in the same entry**; see below;
- **A SPEC CLAIM, written `provides` — `provides Spec[X]`, or a host `provides Spec language L … end` block.** A secondary entry is the sort's own scope, so there is nothing to refuse in the claim itself: the same declaration one level out is uncontroversial, and moving it next to the member that backs it is what §6.3/038 already asks for — **a satisfaction fact belongs in the closure where its backing exists**. A secondary entry that may not carry the spec claim for the members it supplies could never make a foreign carrier satisfy a spec, which is most of why one writes a secondary entry at all. The backing obligation must hold for a claim placed there exactly as it does one level out — delivered by WI-978, which found the claim was never *recorded* for a free-standing-`entity` main entry, so nothing downstream (the obligation, coherence, dispatch) could see it. The block is allowed; its INTERIOR is governed by these same two lists, per the recursion rule above — its realization clauses (`artifact`, `carrier`, `operation_map`, `const_map`, `namespace_map`) are allowed, and a rule, a fact, or a foreign-target proof written inside it is refused exactly as it would be one level out.

  **So a block written inside a secondary entry carries no `fact Spec[T = Carrier]` claims, and this is the one place the two lists cost something.** An earlier draft of this sentence read "the spec claims it carries are allowed", which the lists do not support: `ProvidesItem` admits no `provides` production, so `fact` is the only spelling available inside a block, and the fact ban reaches it for the same reason it reaches one written directly — the loader's discriminator recognises a claim by SHAPE and cannot tell a spec from a parameterized data sort. The consequence is a placement, not a loss: inside a secondary entry the lawfulness claims move OUT of the block and are written `provides Spec[T = Carrier]` as the entry's direct content, where this list allows them, and the realization clauses stay in the block. Corpus cost zero — no `provides` block sits inside a secondary entry, there being none. (WI-1000.)

  **The other spelling of the same claim — `fact Spec[X]` — is refused HERE, though for THIS sort it means the same thing.** Not because the claim is unwelcome but because in a secondary entry it cannot be told from an ordinary parameterized data fact; see the fact ban below for the measurement and for when this lifts.

  **THE TWO SPELLINGS DIFFER ONLY WHERE THE SCOPE NAMES NO TYPE, and the refusal is narrow because of it.** WI-1069 settled this; an earlier draft of this section read "they take the carrier from different places" and "only `fact` can name a foreign carrier", both of which are false. A provision records **two** things — the PROVIDER, whose member set is the dictionary, and the CARRIER, what it is provided *for* — and inside a sort's scope both spellings answer them identically:

  | written | provision recorded |
  |---|---|
  | `provides Show[T = Other]` in a secondary entry to `sort Rec` | provider `Rec`, carrier `Other` — a WITNESS |
  | `fact Show[T = Other]` in that **same** body (were the ban lifted) | provider `Rec`, carrier `Other` — the same PROVISION |
  | `fact Show[T = Other]` one level out | provider `Other`, carrier `Other` — no type at the address, so the provider comes from the bindings too |
  | `provides Show[T = Other]` at an address no type occupies | **refused** — no provider for the bindings to be about |

  `load_fact` takes `sort_ref` from the enclosing scope whenever that scope names a type, exactly as `load_provides_clause` does; the carrier is read off the spec's carrier parameter by `provision_carrier_binding` in both cases. So an entry can make **every** spec claim, foreign carriers included, and what R3 retires is a SPELLING and not a capability. `fact Spec[Carrier]` one level out stays the route for an orphan instance at an address no type occupies, which is the one thing `provides` cannot say. Nothing is unwritable anywhere.

  **The two record one PROVISION; they are not one STATEMENT, and the difference is what the ban costs.** A fact is a rule with an empty body, so `load_fact` also enters the head in the rule index: the goal `Show(T: ?q)` answers under the `fact` spelling and not under `provides` (measured, WI-1069). That surface — not the claim — is what a secondary entry gives up, and it is precisely the surface the ban exists to withhold, since it is what cannot be told from an ordinary parameterized data fact. Two asymmetries run the other way and are worth stating before 058 §4 retires anything: a `fact` on a non-parametric sort WITH CONSTRUCTORS asserts a data instance and emits no provision at all, and `provides Spec[…] :- goals` has no `fact` spelling. (058 §4's proposed retirement of `fact X[…]` should be read accordingly: it is about the sense that duplicates `provides`, not about `fact <term>`, and it retires a queryable head along with the spelling.)

  **Refusing a foreign carrier binding was measured and rejected (WI-1069).** In its plain form — "the spec's carrier parameter must name the enclosing sort" — it refuses the shipped standard library at five sites (`List`, `Relation`, `FiniteStream`, `MappedStream`, `FilteredStream`), each of which binds the carrier to its own type parameter. Exempting that fold, it fails 90 tests across 25 modules, concentrated in witness dispatch and the 058 §3.6 defaults. The shape is not a trap; it is the witness spelling.

  **THE GRAMMAR HAD TO ADMIT `provides` IN A NAMESPACE BODY.** `provides_clause` was a `_sort_content` production only, so R3's allowed spelling of a spec claim was **unwritable** in the one place this proposal calls the point of the mechanism, while the refusal above removed the spelling that *was* writable — together they would have retracted a capability WI-978 and WI-1008 delivered. `_namespace_content` now admits the clause (WI-1000). The grammar cannot tell a secondary entry from an ordinary namespace, that being a question about the address and not about the text, so **the loader classifies**: a `provides` clause names its PROVIDER by WHERE it stands (`load_provides_clause` takes the enclosing scope's owner as the providing sort), and written at an address no sort occupies it is refused naming the namespace, rather than filing a provision under the namespace itself. Reinterpreting it there — deriving the carrier from the bindings, the way a namespace-level `fact Spec[Carrier]` does — is 058 §4's proposal to retire the `fact` spelling, and is not settled here.

**Only the entry's OWN address is classified (WI-1000).** A DOTTED declaration name declares into the namespace its prefix names — `ensure_intermediate_namespaces` creates it — so `operation Inner.helper` written in a secondary entry to `Rec` declares `Rec.Inner.helper`, a member of the ordinary namespace `Rec.Inner`, and this proposal's own rule that "nothing in R3 or R4 reaches" an ordinary namespace applies. Measured: the symbol resolves at `…Rec.Inner.helper` and not at `…Rec.helper`, and the nested-`namespace` spelling of the same declaration was already admitted — so classifying the dotted one gave two spellings of ONE declaration opposite verdicts. **One exception, also measured:** a dotted `sort <prefix>.T = ?` still registers `T` as a type PARAMETER of the ENCLOSING sort (`add_type_param` is called with the scope the declaration is WRITTEN in, not the one its name lands in), so it reaches identity wherever its symbol goes and stays refused.

**A `proof` / `describe` target may be QUALIFIED against the entry's own address.** `describe Rec.g` inside `namespace Rec` is a qualified self-reference and means what `describe g` means. A prefix naming anything else is foreign — including a NESTED SORT's member (`Code.widen`), since a nested `sort … end` is the main entry of its own type and its members belong to that entry, not to this one.

**Refused, each naming the sort:**

- an `entity` — a constructor is identity, and R1 says identity is written once;
- a **type-parameter binder** in any of its four spellings — `sort T = ?`, the per-statement `sort ?T` / `sort [T]`, the braced `sort [F] { … }`, or an enclosing `[…]` parameter list — same reason. All four are one declaration in the IR (WI-454), so the check reads the `is_type_param` marker, not the presence of a body;
- a sort-level **`requires`** — the requirement slots a type's frames carry are its structure, so the same rule reaches it. **If you want a `requires`, define a sort.**
- a **rule** whose head does not *introduce*, or whose predicate has clauses in another entry — the two conditions below. A `rule` block is sugar for rules and follows them; a dot rule and an operator rule never introduce, so both are always refused. **Enforced today as: every rule, no case analysis** — see "what an implementation does today";
- a **`proof` whose target is declared in another entry** — a proof is not a pure consumer of the knowledge base: verification calls `set_proof_result`, writing `VerdictWrite::Discharged { witness, solver }` or `FailedUnknown { reason }` **back onto the target rule**. So a proof mutates the state of a declaration it may not own, and the same condition the rule clause uses applies — the entry that declares the target may prove things about it, and nobody else. (What *reads* a discharged verdict, and therefore how much behaviour this changes, is not established here.);
- a **standalone `describe` whose target is declared in another entry** — WI-1000, the same condition and the same reason: it writes about a declaration another entry owns. See the classification table above for why the target and not the `DescriptionInfo` fact is what the rule keys on;
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

**What an implementation does today: refuse every rule in a secondary entry, with no case analysis on the head.** Not as a placeholder — when this was written the narrow rule was not yet enforceable: condition (1) was undecidable while text order decided whether a head introduces (R6/WI-980), and it was unsound while a body could reference what resolves to nothing (WI-895). Both are now delivered, so the blanket refusal is ready to be narrowed and WI-1001 is that work. It needs no further design: conditions (1) and (2) are decidable at scan time, (2) by grouping a predicate's clauses on `(address, SourceId)` with the main entry as its own group — the key the Definitions give, and one the scan already carries.

One honest limit remains: this does **not** close the underlying hazard. A rule extending a predicate declared elsewhere is non-monotone wherever it is written — an ordinary nested namespace does the same, and so does the sort's own body. R3 closes the route this proposal opens; the general case belongs with R6 and the module question.

**R6 — A rule head's binding does not depend on declaration order.** The policy is not in question and is not changed here: §"A rule head functor is resolved, not declared" (WI-896) says the functor runs the ordinary ladder and the rule contributes a clause to whatever it lands on, *introducing* the name — scoped where written — only where the ladder finds nothing. What R6 supplies is **when "the ladder finds nothing" is evaluated** — the one thing WI-896 left open. Measured before WI-980 closed it, the ladder was asked against a half-built name table, so textual order decided:

| written | binding |
|---|---|
| `rule p(1)` at namespace level, **then** `sort Rec { rule p(2) }` | both clauses join `p`; no `Rec.p` exists |
| `sort Rec { rule p(2) }`, **then** `rule p(1)` | two predicates — `Rec.p` and `p` — one clause each |

and identically across two FILES at one address, on whichever the loader reached first — which is why this is not a question about secondary entries. (It held for a secondary entry in place of the sort body too, when that was measured; R3 has since refused rules there outright, so the shape is no longer reachable.) It is stated here because R3's refusal of rules would otherwise rest on behaviour that is itself undefined.

**The binding is computed against the finished program**, never against the prefix of it that happens to be scanned: a head introduces its name only where no scope it can *see* already introduces it, so that the two rows above give the same answer — the first one, since in the finished program `p` is introduced at `demo` and does resolve from inside `Rec`. (An earlier draft of this sentence prescribed a recipe — *scopes outermost-first, all of a scope's heads together* — and that recipe is wrong: outermost is a property of the ENCLOSING chain, while a head's reach also runs along `requires` and import edges that no ordering of scopes by nesting can respect. Measured, ordering by address depth left a `requires` pair order-dependent at equal depth and split a pair that plain text order had joined where the required sort sat deeper.) This is the invariant every *other* name already has (pass 1 defines every name across every file before any pass 2 runs — the WI-321 cross-file recursion invariant); a rule head escapes it only because its introduction happens during that same pass. A scope that wants its own name where an enclosing one resolves **declares** it — the remedy §WI-896 already prescribes ("to introduce a name that already resolves, declare it"). **Delivered by WI-980**, and not by an ordering: the guard asks whether some scope this one can *see* already **introduces** the name — a property of the finished text rather than of how much of the scan has run. It is asked by running the resolver itself over an overlay of the program's rule heads, so the reach is a reference's reach by construction; the scope's own contents are excluded, since two heads of one name in one scope are two clauses of one predicate. *Introduces*, not merely *writes*: an outer head that itself binds — through a file-local import, say — leaves nothing for a sibling file to reach, so ownership is resolved against the other scopes' verdicts rather than read off the text. It is computed as a **fixpoint over rounds**, not by recursion: the relation is not monotone — the more scopes own a name the more heads yield, so the fewer own it — and a recursion must therefore break cycles provisionally, which is only sound if nothing computed under the break is reused. Three rules, each applied only where its premise is certain: a scope that can see nothing *even when every other candidate is treated as an owner* introduces; a scope that sees a settled owner from every one of its files yields; and a remaining tie — mutual visibility — is broken inside one strongly-connected component, where a member **nested inside** another member yields and, failing that, every member introduces its own. `<global>` is the one scope that plays only one of the two roles: a namespace-less file's head **introduces** its name there, but no head written inside a namespace ever yields to it — a name every file shares must not absorb one written in a namespace, and a refusal instead would outlaw the language's own documented first form. Corpus census of sites whose binding this changes: zero. It does not reach a **paren-less nullary** head, which introduces nothing anywhere and predates this rule.

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

**R4 — ADD A FRESH OPERATION, NEVER FILL OR DISPLACE.** Three clauses. The first two govern operation declarations; the third reaches captures that are not declaration collisions.

- **An operation name is declared at most once per scope**, naming both sites on a second declaration — delivered by WI-1049. Anthill has no signature-keyed overloading: two declarations reach one symbol, so there is no second operation for dispatch to select. The rule crosses entry boundaries without a special case: two secondary entries may not declare the same operation, and a secondary entry may not redeclare an operation from the main entry.

  **A main-entry declaration reserves the name whether or not it has an implementation.** A body-less declaration is not silence available to another `operation` declaration; it is the one declaration of the interface and may be backed by a builtin or by an `operation_map` in another file or host-language package. The admission decision therefore never asks whether a body, mapping or builtin exists and never changes when a realization package is added or removed.

  Measured against `sort String`'s body-less, host-mapped `isEmpty`: before WI-1049, a secondary entry supplying `operation isEmpty(s: String) -> Bool = false` loaded clean and its body never ran, because the registered host implementation wins before body lookup. It is now refused as a duplicate declaration before host backing is relevant. This is not a corner case: the host carriers intentionally declare body-less operations whose implementations live in `operation_map` blocks.

- **An operation introduced by a secondary entry has a runnable Anthill body.** A secondary entry adds a complete new member; it does not reserve an abstract slot for a later builtin or host mapping. A host `provides … language L … end` block remains legal there, and an `operation_map` still attaches only to an operation some entry already declared — a mapping does not bring an operation into existence (§10.2). A mapping may coexist with a portable Anthill body under the realization rules; what it may not do here is substitute for the body the secondary-entry declaration itself is required to carry.

  This deliberately drops the earlier "spec-author and implementer as different hands" spelling in which the main entry declared a signature and a secondary entry repeated `operation` with its body. WI-1049 makes that pair illegal, and for the right representational reason: the second text is a second declaration under one symbol, not an implementation attachment. If Anthill needs a separately-written implementation of an existing declaration, it needs a distinct construct such as `implement`, arbitrated explicitly against Anthill bodies and per-language host mappings; it is not an exception to one-declaration-per-name and is outside this proposal.
- **A declaration may not capture a name it does not override.** The declaration-collision rule above is keyed on *members colliding*, and that is not enough: a name can already mean something without being a member. Measured — a main entry calls a bare `f(…)` that resolves through `import lib.f` and answers `1`; add a secondary entry declaring `f` and the *same unedited body* answers `2`. Nothing named `f` was a member, so the freshness and body rules admit it, and existing code silently changed meaning.

  **AND THE CAPTURED NAME NEED NOT HAVE BEEN DECLARED — which is what settles WI-939.** That ticket asked whether a namespace-level rule and a sort member may share one short name, offering (a) resolve by arity, (b) an ambiguity error, (c) forbid the coexistence at declaration. This clause answers **(c)**, and needs no wording of its own to do it: a predicate a **rule head** introduced (§"A rule head functor is resolved, not declared") already resolves inside every sort in that namespace, through the enclosing parent and with no `import` anywhere, so a member taking the name captures it. Measured, `sort Vec3 { operation vec_add(a, b) }` beside a namespace-level `rule vec_add(?a, ?b, ?c)` is refused in **either text order** — which mattered because a rule head's *binding* was order-dependent until WI-980, while this check — running after pass 2 over the finished KB — never inherited that. Both orders are still asserted: the rows are what shows the two questions are separate.

  Two asymmetries follow from where the clause is asked, and both are deliberate. It is asked only of declarations whose scope owner is a sort, so the **member is always the capturing side** and an ordinary namespace is never one — WI-939 worded (c) the other way round ("refuse a namespace-level name that a sort in the same namespace also declares"), and the pair is refused either way. And a rule head, being resolved rather than declared, has no entry in the declaration ledger the refusal reads for the captured half, so the message names **one of the predicate's clauses** rather than a declaration, and says which it is.

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
  | **no override relationship** | **0 by this census; 3 in fact** | the hazard — and the census did not reach two of its shapes. See "What the census missed" below |

  The middle two rows are worth keeping apart, because read together as "a type name shadowing a type" they look like nested type declarations and neither is: `IndexedSeq.Effect` is a type parameter, `TypeExtractor.Error` an entity variant of `enum anthill.prelude.TypeExtractor`. R3 already refuses both spellings in a secondary entry, so widening the clause to types costs **no migration** — and the shape that does capture, a nested `sort` with a body inside a secondary entry, occurs **zero** times in the corpus.

  Census: WI-981, less the two WI-982 removed.

  **WHAT THE CENSUS MISSED, and the two exclusions that answer it (WI-999).** The five classes above sum to 61, and the clause as first written refuses **three** corpus sites none of them names. Both missing shapes are captures of a name the declaring scope's own text never asked for, and each is excluded on its own ground rather than by a count.

  | the captured name | sites | why it is not a capture |
  |---|---|---|
  | a **sibling type's CONSTRUCTOR**, reached through §8.6's variant-exposure link — `prelude.SortedSet.merge` over `EffectExpression.merge`; `reflect.Substitution.apply` over `Expr.apply` | 2 | **Members and constructors are named per TYPE.** §8.6 leaks an enum's constructors to the *enclosing namespace* so they can be written unqualified **there**; that is not a statement that the bare name is in use at any address inside it. Two types in one namespace may name their members and constructors freely against one another — the alternative makes every constructor name in a namespace a reserved word for every sort in it, which is not a name space anyone can work in. Stated in kernel-language.md §8.6 and §8.7 as well |
  | an enclosing **NAMESPACE** — `reflect.KB.reflect` over `anthill.reflect` | 1 | A namespace denotes no value and no type: it can appear only as the head of a qualified path, so there is no answer for a body to silently get a different one of. What a capture does to a path belongs to the dotted ladder — measured below |

  **THE EXPOSURE EXCLUSION IS SPENT BY AN IMPORT, and it is a property of the PATH rather than of one edge.** §8.6's leak is excused because it is *automatic*; an `import` of the leaking type, or of the namespace it leaks into, is the author asking for those bare names, so a declaration taking one captures it and stays refused. Both spellings reach the same `add_import_parent`, so the discriminator is the edge's WRITER, not its shape — and it must be carried down the walk, not tested at one hop: `import wilib.*` makes the first edge an import and leaves `wilib → Colour` an ordinary exposure edge, so an edge-local test admits the import and then skips the very name it brought into view. Measured on that shape, an edge-local reading loads clean while an unedited `Red(x: 7)` rebinds to a new `Box.Red`.

  **AND IT IS ASKED PER FILE, not over their union.** An import resolves only in the file that wrote it, so a name can have meant something else *for one file* and nothing at all for another; the question is put once for each file that has text at the address. Asking under the union instead refuses programs no file could have misread — measured, an `import wins.f` in a file that never mentions `Rec` blocks a `Rec.f` written in another, with no body anywhere reading a bare `f` there and the only repair in someone else's text. The per-file reading still catches what the union was there for: 059's motivating case is a secondary entry written by a *third party*, where the harmed body is in the file that wrote the import and the capturing declaration's own file resolves the name to nothing.

  Neither missed shape is excused by "it would fail loudly", which this clause refuses everywhere else. The constructor shape is silent: measured, a sibling enum's `entity m(left, right)` and a sort member `m(left, right)` of the same return type load clean and the unedited body calls the member. The namespace shape is silent too, and that is why it is the *ladder's*:

  | written | measured, before WI-1075 | now |
  |---|---|---|
  | `namespace outer { namespace inner { operation g; sort Box { … inner.g(…) } } }` | resolves to `outer.inner.g` | unchanged |
  | + a member `Box.inner` | **loud** `unknown functor` | unchanged |
  | + a member `Box.inner`, and a **top-level** `namespace inner` also exists | **loads clean**, silently calling the TOP-LEVEL `inner.g` | **loud** — `..inner.g` is how the top-level one is asked for |

  The third row was the recovery rung WI-751 added for a shadowed head, re-rooting at the bare global twin. Reachable with no capturing declaration anywhere — a `let` binder, a sort or a labelled rule shadows a head just as well — so refusing the declaration would have closed one route into a defect that has others. **WI-1075 closed it at the ladder**, by separating that rung's two jobs: the absolute reading got its own spelling, `..a.b.c`, and a bare dotted path became purely relative (proposal 044 §"Absolute paths"; `kernel-language.md` §8.6). The rung had fired **zero** times across the corpus, so the change cost no migration — and the exclusion above no longer rests on nothing being *reachable* but on nothing being *writable*: with `..` spelled, capturing a namespace name can neither break a path silently nor re-point one.

  So on the *no-override* hazard the clause bites **nothing in the corpus** — which is what the census claimed, now holding for stated reasons rather than by an incomplete count. Its whole migration is the two sites the exclusion below stops covering, which WI-1048 measured as a deliberate refinement, so they are two sites clause 3 must NOT touch rather than two it must migrate (see below).

  **The repair is to delete the capturing member, not to rename it** — whenever the member's own answer does not read its receiver. A receiver nothing reads is dispatch ceremony, not an interface: it exists so the name dot-dispatches, and it is also the thing that captures. Renaming keeps two names for one question; deleting leaves the one the caller already had. Reach for a rename only when the member genuinely answers about its receiver and the collision is coincidence.

  This is the clause's one real hit, and it is the argument for keeping it. Both sites were `reflect.KB.nonvar` / `reflect.KB.ground`, and the capture was the *visible end* of a defect: the captured names were unreachable in value position, and the same question had two answers that disagreed by carrier. The shadow was the smaller half — see WI-982.

  **The instrument is a refusal**, like the two clauses above it. The only argument for a warning was blast radius, and the corpus holds none.

  **THE EXCLUSION IS `requires` OR `provides`, KEYED ON THE RELATION.** Measured over the 183 sorts that declare operations, counted per *triple* rather than per declaration (so it does not sum to the 23 above: `List.collect` shadows both `FiniteCollection.collect` and `FiniteStream.collect` — one declaration there, two rows here):

  | the sort's relation to the spec whose op it shadows | sites |
  |---|---|
  | **provides** it (transitively, as `sort_provides` reads it) | **40** |
  | **requires** it only | **2** — `FiniteCollection.filter` / `.map` over `Iterable.filter` / `.map` |

  `provides` is uncontroversial: that is how a sort implements what it provides. **The `requires` half was argued both ways and is settled by measurement (WI-999).**

  The case against it is §8.7: a sort that merely *requires* a spec earns no permission to rebind that spec's operations, since such an operation "is **not** overriding it: that operation is unrelated", and a name one has not overridden is a name one may not capture. Under that reading clause 3 admits a requires-shadow only where its signature is a deliberate **refinement** — the 2 sites above, which WI-1048 established are exactly that: they differ in RETURN TYPE (`FiniteCollection[…]` vs `Stream[…]`), which is the whole of proposal library/003 + WI-599's THIN design; on a `List` dispatch picks the finite one deterministically by §8.7's `requires`-refinement tie-break, not by `HashMap` order, and a call expecting the other is a type error naming both types. So the narrow reading needs a gate — `typing::requires_shadow_is_confusable` — or it refuses a design §8.7 prescribes.

  **That gate cannot carry a refusal, and this is what decides it.** It warns unless the two operations are *confidently distinguishable*, and every leg it cannot decide falls open to "confusable" — correct for a warning, since a lint may only get quieter where a difference is proven. Measured, it falls open whenever the requirement binds the spec to a **type parameter** rather than to a carrier:

  ```
  sort Polynom
    sort R = ?
    requires Ring[R]
    operation add(p1: Polynom[R], p2: Polynom[R]) -> Polynom[R]
  end
  ```

  σ maps `Ring.T ↦ R`, and a type parameter is a **wildcard** — `R` is not provably different from `Polynom[R]`, so no leg carries a proof and the pair reads as confusable. Under the narrow reading that is a **load error** on the ordinary way to give a sort an operator beside a requirement on its *element* type. The requirement is not about `Polynom` at all; the spec's `add` is `R`'s.

  **So the narrow exclusion is dropped, which is this clause's own second stated option.** A requires-shadow is excused, and WI-346's lint keeps exactly that population — advisory, which is what a predicate that falls open to "warn" can support. Clause 3 and the lint are then two questions rather than one: the lint asks whether the author believed `requires` overrides, and clause 3 asks whether a name silently changed meaning.

  A caution on measuring the lint: no test helper surfaces load warnings. `try_load_kb_with_files` discards `load_all`'s `Ok(_)`, and `load_stdlib_kb_with_source` returns the result of loading the *probe source* against an already-built stdlib. Both report zero warnings for a corpus that emits some.

  Unlike the secondary-entry body requirement, this clause is stated over the whole **sort scope**: measured, the same flip happens when the capturing operation is written in the main entry, so an entry-local rule would patch the wrong object and would split the one scope R2 rests on. §6.3 records the hazard for the long form as a caution already (WI-935); this makes it a check, for both spellings at once.

**Is R4 implementable?** The duplicate-operation half is already delivered. The remaining clauses are decidable, but the entry-content check and the capture check need different mechanisms.

| clause | sites in the corpus | what it needs |
|---|---|---|
| 1 — a second operation declaration under one name | **0; delivered (WI-1049)** | the per-load operation-declaration log, keyed by symbol |
| 2 — a body-less operation introduced by a secondary entry | **0; delivered (WI-1000)** | the R3 entry classifier plus the operation's written body presence |
| 3 — capturing a name it does not override | **0; delivered (WI-999)** | the pass-1 declaration ledger, then the `provides`/`requires` relation after pass 2 |

Clause 1 cannot be checked by walking symbols: `define` **merges** two same-named declarations in one scope into one symbol, so by the time symbols exist the duplication is gone. WI-1049 therefore records every written `Item::Operation` during one load phase and refuses a symbol with two declaration sites. The check already crosses main/secondary and file boundaries and is deliberately independent of bodies and host backing. Measured over the corpus, no operation name is declared twice in one scope.

Clause 2 asks only about the declaration as written in the secondary entry: does it have a runnable Anthill body? It deliberately does **not** inspect `OperationMapping` facts or builtin registries. Those are backing for the one declaration; they do not decide who owns its name. This removes the old post-pass-2 "is already implemented" branch entirely.

Clause 3 must key on the **relation** — does the declaring sort provide or require the sort that owns the captured name — and **not** on the route by which the name was reached. The measurement is why: 4 of the legitimate overrides arrive through an `import` of the spec's member rather than through the `requires` link, so a route-based rule refuses exactly the wrong four. That relation is known only after pass 2, so the check runs there, not in pass 1 beside the ledger. `sort_provides` and `requires_chain_flat` already compute it, transitively.

The **capturing** side needs the pass-1 ledger, and for a reason the exclusions do not share. `define` merges a declaration onto an existing symbol, so a finished scope's `locals` map says which name won but neither where it was written — and a refusal that cannot name the line is not actionable — nor which KEYWORD was written, which is what the category list turns on: `sort T = ?` (a binder, excluded) and `sort Alias = T` (a type, checked) both define a `SymbolKind::Sort` in one scope. Every named declaration is recorded, including the two categories that can never capture, because a type parameter and an entity variant can still BE captured and the diagnostic names their line from the same log.

The check must also not assume the captured name has a **declaration**, nor that it is an operation. `register_builtin_tag` mints a symbol for a name nothing declares — `symbols.define(short, qualified, SymbolKind::Operation, scope)` — so a resolver builtin can be an operation by *kind* with no declaration behind it: measured, `anthill.kernel.find_dictionary` carries kinds `["Operation"]` and appears in no `.anthill` file. Nor is `Operation` even the reliable kind: the tag on `anthill.reflect.Expr.ho_apply` rides an **Entity** symbol, so a check keyed on `kind == Operation` misses it. The check reads the override relation, which such a name simply lacks; it must not reach for a declaration, or for a kind, to read.

Operation redeclaration is loud today (WI-1049), and a fresh body-less operation in a secondary entry is loud since WI-1000. Refusing that shape prevents a secondary entry from reserving a host-facing slot on a sort it is extending. Note that a sort's own member does **not** outrank the other supply routes at dispatch: WI-842 **refuses** a tie between a member, an instance fact's binding, and a witness sort's member, naming each by its route, and it deleted the ranking that used to prefer the member. That is the same standard here — a second supplier is refused rather than settled by route order.

**A spec claim declared in a secondary entry needs 058's arbitration; R4 does not invent another one.** A secondary entry's `provides Spec[X]` contributes an ordinary provision row. Proposal 058 §3.6 proposes `one_default` and no-displacement for such rows, but that policy is not delivered merely by allowing the placement here, and 058's "canonical companion" is a separate witness sort rather than a secondary entry at the carrier's address. Until 058's proposed arbitration lands, this proposal establishes only that the claim is legal here and must satisfy the same backing obligation as one written outside the entry. Since 058 §4 proposes retiring the `fact X[…]` spelling in favour of `provides X[…]`, a secondary entry uses the latter — R3 refuses the `fact` spelling there for the reason given with the fact ban.

**R5 — §6.3's remedy, revised.** To give a free-standing entity operations, either rewrite it into the long form or add a fresh, body-having operation in a secondary entry at its address. The long form keeps an owned interface together; the secondary entry is also available when the type declaration cannot be edited. Both routes produce one symbol, and neither route may redeclare an operation the entity's scope already owns.

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
