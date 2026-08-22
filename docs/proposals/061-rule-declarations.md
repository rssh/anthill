# 061: Rule declarations — a predicate is declared, not discovered

**Canonical reference:** [`kernel-language.md` §8.6](../kernel-language.md), §"A rule head functor is resolved, not declared" and §"A rule-introduced functor is scoped where it is written".

## Status: DELIVERED (2026-08-21, WI-20260821-FQC85; drafted the same day). Written from WI-980, which made a rule head's binding order-independent and, in doing so, measured what it costs to decide a name *during* the pass that creates it. Measurement claims below are taken from the Rust loader with both-sides controls; the rule and its staging are prescriptive.

## Relates to: WI-980 (order-independent head binding — this proposal is its structural alternative), WI-896 (a head is resolved, not declared — amended here), 059 §Definitions (the FILE as the unit at which "two parties" becomes real), 052 (rules as stream-valued operations — a declared predicate is the name such a value is cited by), WI-898 (equational heads index under the connective — **out of scope**, see below), 060 (clause-level typed heads — the guard that makes a shared predicate safe), WI-995 (imports are file-local — the reason a predicate's clauses in two files can disagree).

## Delivered — what the implementation settled that this text did not

The rule and its staging shipped as written. Five things the draft above states were
**corrected or decided by measurement** during delivery, and the text is left standing
because a proposal keeps its own record:

1. **`:- true` did not work, and had to be made to.** The draft prescribes `fact`'s
   desugaring as `:- true` and calls both migration targets "live" on the evidence that
   they LOAD. Driven: `rule p(1) :- true` loaded clean and answered **nothing** — `true`
   is a `boolean_literal`, so the body carried a constant goal no clause and no builtin
   resolves, and WI-1034's "names nothing" refusal cannot reach it because a constant
   names no name. The loader now reads a `true` body goal as the **empty conjunction**,
   which is what makes `fact H` and `rule H :- true` the same clause.
2. **`fact` is NOT an available migration target for a named predicate.** A `fact` head
   introduces no scoped symbol — measured, `fprobe.ff` does not resolve while
   `fprobe.hh` (a rule head) does — so migrating a site to `fact` moves its clause to the
   bare global intern and deletes the name its own scope could cite. The draft's per-site
   reading ("the logic axioms read as assertions (`fact`)") would have broken
   `logic_sorts_test`, which drives those symbols. This is WI-20260821-RDGQC's gap, now
   recorded at kernel-language.md §6.1.
3. **The logic axioms are DECLARATIONS, not assertions.** `constructive.anthill` and
   `classical.anthill` say so themselves — "they exist as named symbols so a
   `proof … :- modus_ponens, …` hint block can reference them" — and as facts their
   variable heads asserted that every pair of propositions satisfies modus ponens. The
   11 sites keep their body-less spelling and now mean it.
4. **The corpus census was 23 sites, not 20.** `rustland/anthill-todo/anthill/rules.anthill`
   carries three more (`all_deps_satisfied_rest`, `description_view` ×2), and
   `docs/proposals/typing_pass_spec.anthill` — parsed and loaded by `typing_test` — eight
   more. Measured with a parser-driven census through the loader itself, not by regex.
   The **test** corpus is a separate population the draft did not count: 116 further
   sites across 31 Rust fixture files.
5. **A body-less rule that can declare NOTHING is refused** — a `⊥` denial, a multi-head
   rule, a qualified head, a paren-less nullary, a name ANOTHER CONSTRUCT already declares
   in that scope (measured: `operation has(x) -> Bool` beside `rule has(?x)` loaded clean
   with a `Goal` kind merged onto the operation's own symbol), and a head the defining
   pass never reaches (a `provides … language … end` block's interior) — as is a
   declaration carrying a label, a `[…]` tag, a `[t]` introducer or a typed column. The
   draft does not name any of these; each would otherwise have become a silent drop, and
   two (WI-20260821-W9SD3's qualified head, WI-20260821-P85Z7's paren-less nullary) are
   filed silences the refusal now covers in their body-less spelling. The last two were
   found by `/code-review` after the first version of each guard shipped — the
   never-reached one had asked the resolution LADDER, which any prelude name satisfies.

Open question 2 (arity) is **not** settled by this delivery: a declaration states its
head's arity and enforces nothing, and one-arity-per-predicate remains
WI-20260821-6WVJB, which depends on the operation-side decision in WI-20260821-ZW940.
Open questions 3–5 are recorded in kernel-language.md §8.6 as stated rules.

## The problem

**A predicate is the only name in the language with no declaration.** Four core constructs — `namespace`, `sort`, `rule`, `operation` — and of those only `rule` brings a name into existence *as a side effect of using it*. Every other name is defined in the loader's first pass, before anything resolves anything; a rule head's name is created during the pass that decides it.

That is the whole of WI-980. Measured: `rule p(1)` beside `sort Rec { rule p(2) }` loaded as **one** predicate with two clauses when the namespace-level rule was written first and as **two** predicates when it was written second. Operations show no such thing — the identical shape with `operation` in place of `rule` is refused identically in all four orders (one file / two files × both orders), because an operation makes no decision: its name goes to its own scope, always.

WI-980 closed the ordering by asking a question the pass cannot move — *does some scope this one can see already introduce the name* — resolved through the resolver itself. That works, and it is machinery: a recursion with a memo, a cycle detector, an enclosure tie-break, a depth bound, and a per-`(scope, name, file)` split forced by file-local imports. Every one of those exists to *infer* something an author could simply have said.

## The rule

> **A logical rule's head functor names a DECLARED predicate. A declaration is written once, in one file, in the scope that owns the name; a rule head is always a clause OF something and never brings a name into existence.**

**The declaration is a rule with no body** (decided 2026-08-21; §below):

```anthill
namespace demo
  rule p(?x, ?y)              -- the DECLARATION: no body, asserts nothing

  fact p(1, 2)                -- a clause of it
  sort Rec
    rule p(3, ?y) :- q(?y)    -- also a clause of it -- resolution, not introduction
  end
end
```

What it must DO was settled first — bring the name into existence in pass 1, in one scope, **asserting nothing** — and the rules below are written against that. The spelling follows in the next section.

Nothing about resolution changes: the head runs the ordinary ladder, exactly as §WI-896 says, and contributes a clause to whatever it lands on. What changes is that there is now something to land on, put there by pass 1 like every other name — so *when* the ladder is asked stops mattering, which is the invariant WI-321 gives every other name kind.

**A scope that wants its own predicate where an enclosing one resolves declares it.** That is §WI-896's own remedy, which today has no form: the only way to declare a predicate name is a body-less `operation`, and that drags in a signature and membership of the dispatch surface (059 §Definitions: "the dispatch surface of `X` is exactly the operations"). A rule declaration is the form the remedy always assumed.

## The declaration's syntax: a rule with no body

> **No body ⇒ DECLARES. A body ⇒ asserts.** A rule with no body declares its head's predicate and asserts nothing. `fact` is how a body-less assertion is written, and it desugars to an explicit `:- true`.

| written | reads as |
|---|---|
| `rule p(?x, ?y)` | **DECLARES** `p` — asserts nothing, has no clauses |
| `rule p(?x, ?y) :- G` | a **clause** of `p` |
| `fact p("a", "b")` | an **assertion** — desugars to `rule p("a", "b") :- true` |
| `rule lhs <=> rhs` | a **defining equation** — untouched (§5.3, WI-881) |

**It makes the language uniform, and removes `rule`'s exception.** `operation f(…) -> R` declares and `= body` defines; `const N: T` declares and `= expr` defines. `rule` was the sole construct where the body-less form *asserted*, and only because §6.1's desugaring — titled *"Fact (body-less rule)"* — spent that form on `fact`. Moving one `:- true` into the desugaring gives all four constructs one reading.

**It also settles the groundness question by removing it.** The old objection to any head form was that `head` means `head :- true` and that reading does not vary with groundness — the ground spelling asserts one tuple, the variable spelling the universal relation — and the language must not give one syntax two readings according to whether its arguments are ground. Under this rule the **arguments stop carrying the distinction and the body carries it**, so `rule p(?x, ?y)` and `rule p(1, 2)` are read the same way: both declare.

**The split point already exists and is already load-bearing.** `body: None` is *not* newly overloaded by this proposal — the language already reads a body-less rule head two ways, and `EQUATION_FUNCTORS` is where. It has exactly one member, `unify` (`<=>`), and its own doc defines an equation as the node "**as a body-less rule head**"; `=` and `===` are the test column and their body-less heads are already refused (WI-888, WI-1090). So the reader this proposal needs — *is this body-less head a minted equation connective, or anything else* — is the reader the loader already runs, paired with `SimpleTermStore::is_minted` because `unify` is also an ordinary identifier a user may call (WI-948: *a name, not a verdict*).

Measured over the corpus, that split is what carries the weight:

| body-less rule heads | count |
|---|---|
| minted equation (`<=>`) — **unchanged** | **97** |
| plain head — **re-read as a declaration** | **20** |

**Migration: 20 sites.** Parser-driven census over 148 corpus files (stdlib, `anthill-stl`, `examples`, CLI fixtures, `anthill-todo`; the 4 that do not parse are WI-852's deliberately-malformed fixtures). **17 in the stdlib and 3 in `examples/github-todo`** — *not* stdlib-only, as an earlier regex census of this proposal claimed at 25:

| file | sites |
|---|---|
| `logic/constructive.anthill` | 8 — `identity`, `modus_ponens`, `conjunction_intro`, `conjunction_elim_l/r`, `disjunction_intro_l/r`, `ex_falso` |
| `logic/classical.anthill` | 3 — `excluded_middle`, `contradiction`, `double_negation` |
| `reflect/typing.anthill` | 2 — `list_contains`, `type_compatible` |
| `prelude/lattice.anthill` | 2 — `less`, both inside one `rule { … }` block |
| `prelude/set.anthill` | 1 — `subset` |
| `realization/realization.anthill` | 1 — `effect_map_entry` |
| `examples/github-todo/rules.anthill` | 3 — `all_deps_verified_rest`, `description_view` ×2 |

Each becomes `fact …` or gains an explicit `:- true`, and **both targets are live**: measured, `fact p(?x, ?y)`, `fact p(?A, ?A)` and `fact p(?x, cons(head: ?x, tail: ?))` all load clean, so §6.1's *"ground assertion"* is descriptive prose rather than an enforced restriction — which matters here, because **18 of the 20 sites carry variables**. Which of the two a site wants is a per-site reading, not a mechanical rewrite: the logic axioms read as assertions (`fact`), while a pattern clause like `rule type_compatible(?A, ?A)` may prefer to keep the `rule` keyword and say `:- true`.

**The grammar does not move.** `fact` is already its own IR item (`"fact_declaration" => convert_fact(…).map(Item::Fact)`) and a body-less rule is already `Item::Rule { body: None }`, so the two are distinguishable before any desugaring. The change is what the **loader** reads `body: None` as — from *assert* to *declare* — with `Item::Fact` untouched.

**One consequence must be handled, and it is measured.** §6.1's desugaring is **read by other guards**: §8.3 refuses a `fact lhs === rhs` explicitly *"a fact being a body-less rule (§6.1)"*. That is not commentary — driven, `fact aa() === bb()` is refused with a message that names *"the **rule** `aa(…) === …`"*, so the fact reaches the guard **as a desugared body-less rule**. Desugar `fact` to `:- true` instead and `fact lhs === rhs` and `fact lhs = rhs` escape the WI-888 / WI-1090 refusals in silence. The repair is to key those two guards on the **head functor** rather than on body-lessness — which is the question they were always asking — and it must land **with** the desugaring change, not after it. This is WI-1090's own recorded lesson (*narrowing a list reaches readers that ask another question*) arriving from the opposite direction.

**What it does not reach.** No corpus rule head is a body-less **paren-less nullary** (`rule holds`): the four sites the spec names all carry bodies (`rule holds :- base(1)`, `rule gps_drift_axiom :- …`). So the separate paren-less scoping gap — that such a head introduces nothing anywhere and falls to one global intern — is untouched by this rule and still needs its own answer.

## Auto-declaration, and where it stops

Requiring a declaration for every predicate would be a migration for no gain in the common case: a predicate whose clauses are all in one file has one author, who can see all of them.

> **A predicate whose heads are all written in ONE file is auto-declared, in the scope §WI-896's ladder already picks. A predicate with heads in MORE THAN ONE file must be declared explicitly; without a declaration it is a load error naming the files.**

**AMENDED BY WI-20260822-845G7 — the unit is the SCOPE as well as the file.** This proposal's rule leans on "the scope §WI-896's ladder already picks", and picking it was the whole of WI-980's `Ownership` fixpoint. 845G7 deleted that fixpoint on the measurement below, so there is no longer a ladder to pick a scope with: an undeclared head declares at the scope it is **written in**, and a name introduced at two scopes that can reach each other is a load error. Auto-declaration therefore covers one scope in one file; both wider shapes are refused, and the declaration this proposal introduces is the remedy for both.

**The measurement, and it is what settles it.** Instrumenting the head-decision loop over the whole test suite — stdlib, `anthill-stl`, `examples`, `anthill-todo` and every fixture — gives **234,078** decisions, one per rule head that did not already denote:

| verdict | count |
|---|---:|
| introduce at this scope | **233,917** |
| join ANOTHER scope's head | **161** |
| yield to an ordinary declaration | **0** |

130 of the 161 are one fixture, and every one of the remaining 22 distinct triples is in a fixture written to exercise the fixpoint itself. **Zero** come from the shipped corpus. The 400 lines of non-monotone fixpoint — optimistic overlay, three settling rules, SCC tie-break, `(scope, name, file)` key, `<global>` two-roles exception, depth bound — computed a constant for every real program.

**What the amendment costs, and why it is stated over VISIBILITY rather than over files.** Removing the join reverses `demo { rule p(1) :- true; sort Rec { rule p(2) :- true } }` from one predicate to two. Corpus cost: **zero** — no shipped predicate joins across scopes. But leaving the split *silent* would trade one hazard for another, and 059 §Definitions' file argument does not transfer: it answers "assembled by two parties that never agreed on it", while one author writing that pair in one file is one party who would get a meaning they did not write. So the refusal is stated over what a scope can SEE, and a same-file pair is refused exactly as a cross-file one is. Two scopes that cannot reach each other keep their own, which is the common case and the control the rule rests on.

**The file is the unit, and 059 already argued why** (§Definitions): what the rule guards against is a predicate "assembled by two parties that never agreed on it", and two blocks in one file are one author making one edit — a file boundary is the smallest place where *two parties* is real. It is also the unit `import` already uses, since an import resolves only in the file it is written in.

**Census: the rule refuses nothing that exists.** Over stdlib + `anthill-stl` + `examples/github-todo`: **102** predicates carry rule heads, and **every one of them has its heads in exactly one file** — zero span more than one. The corpus cost of requiring a declaration for the multi-file case is therefore **zero**, and the 43 distinct rule-introduced names (14 in `anthill.reflect.typing`, 8 in `logic.Constructive`, 7 in `anthill.stage0.workflow`, 3 each in `reflect.feed`, `realization`, `logic.Classical`, …) are all auto-declared.

## One arity per predicate

**A predicate's clauses all have one arity** (decided 2026-08-21; WI-20260821-6WVJB). Today rules accept mixed arity and operations refuse it — measured, `rule p(1)` beside `rule p(1, 2)` loads and *dispatches* (`p(1)`→1, `p(1,2)`→1, `p(9)`→0), while `operation f(x)` beside `operation f(x, y)` is refused. The two halves should agree, and they agree on the operation's answer.

**The deciding fact is the VALUE position.** A bare name is a value: `apply1(twice, 3)` loads with `twice` alone denoting the function, and 052 OQ2 wants bare `Queen.find` citable as a `Relation[T]`. Arity is visible at a call site and invisible at a value site, so overloading by arity leaves the bare name with nothing to pick by — which is what the duplicate-operation refusal means by *"a scope maps a name to one symbol"*.

**It also makes 052 coherent.** A relation's schema **is** its row type, the full named tuple of its columns (052 OQ5). A mixed-arity predicate has no single schema and therefore cannot be a relation value at all — a live incoherence, since the language offers relations-as-values and admits predicates that cannot be one.

Corpus census: of 41 multi-clause predicates, **one** has mixed arity — the kernel's own `Constraint` — and no user-written predicate anywhere mixes it.

**For this proposal the consequence is that a declaration carries no arity question.** A predicate has one arity because its clauses do, so the declaration states it once by writing the head, and open question 1's `rule p/2` spelling is dead twice over: nothing else in the language uses `/arity`, and the number would identify nothing.

## What it removes

Each of these is machinery WI-980 needed only because a predicate's home is inferred. All are cross-FILE phenomena, so the auto-declaration boundary is exactly where they live:

| measured behaviour | why it exists | under this rule |
|---|---|---|
| a sibling file's head **moved another file's clause** — `zlib.q` 2→1, `zdemo.q` 0→2, with file A unedited | a mint in one file of a scope captures a head in a sibling file, because imports are file-local while symbols are per-scope | the two files' heads are one predicate, so a declaration is required and states the home once |
| a mutual-import cycle picked an owner by **file order** | no scope in a cycle is outermost | two files ⇒ declaration required |
| the same pair at one address, split across files, gave **two different programs** by file order | the decision ran per file | two files ⇒ declaration required |
| ownership had to be keyed per `(scope, name, FILE)` | two heads of one predicate can sit in files with different imports | cannot arise: one predicate, one file, or a declaration |

What remains is the single-file case, decided by §WI-896's ladder as it is today — the part of WI-980 that has been stable throughout.

## Equational rules are NOT this construct

An equational rule (`lhs <=> rhs`) is about **extending unification**, not about naming a predicate. Its clauses are indexed under the `eq`/`unify` **connective**, not under its subject (WI-898), so the subject owns no clauses and there is no predicate to declare: `rule eq(red, red) <=> true` leaves `eq` owning nothing, and a carrier that wants `eq` by cases writes **predicate** heads instead (§8.7). The two shapes already earn different symbol kinds — `Goal` for a predicate head, `EquationFunctor` for an equation's subject — precisely because of where the clauses land.

So this proposal governs **logical rules only**. An equational head neither needs a declaration nor is auto-declared by one, and `[simp]`'s enablement (§5.3, WI-881) is untouched.

**This section is also where the declaration's syntax lands its weight**, now that the declaration is a body-less rule. The two constructs share the shape `body: None` and are told apart by the head's functor — a minted `unify` node is an equation, anything else is a declaration — which is the reader the loader already runs (`EQUATION_FUNCTORS` has one member and its doc defines an equation as exactly "a body-less rule head"). The corpus makes the stakes concrete: **97** body-less heads are minted equations and must not move, against **20** plain heads that this proposal re-reads. The pairing with `SimpleTermStore::is_minted` is not optional — `unify` is also an ordinary identifier a user may call, and WI-948 records that this predicate is *a name, not a verdict*.

## Open questions

1. **Spelling — SETTLED (2026-08-21): a rule with no body.** The rule, the split point and the 20-site migration are in §"The declaration's syntax" above.

   The **nine candidate spellings**, what each was measured against, and the cross-language survey are in **[docs/brainstorms/rule-declaration-syntax.md](../brainstorms/rule-declaration-syntax.md)**. They are not repeated here — this proposal states the rule; the search that found it is a record. Three of its conclusions bear on the rule and stay below.

   **Why a head form was available at all.** Every head form looked spoken for, on the reasoning that `head` means `head :- true`, and that reading does not vary with groundness — the ground spelling asserts one tuple, the variable spelling the universal relation — so a head form would give one syntax two readings according to whether its arguments are ground. **That objection is conditional, and its condition is §6.1's desugaring rather than anything about heads.** `head :- true` is what a body-less head means *because `fact` was desugared onto that form*; move the `:- true` into the desugaring and the objection lapses for every head form at once. It is also why this spelling wins on the two things a spelling is judged by here: it costs no grammar and no keyword, and it *removes* an irregularity instead of adding a construct to work around one.

   **The account of what a declaration MEANS is not discarded with the variants.** The most principled candidate was a namespace-scoped **assumption** — the hereditary-Harrop antecedent `(forall(?x), p(?x) -: G)` with the namespace as the implication's scope — because an assumption asserts nothing *by construction*, which is exactly the property `head :- true` lacked. It was not chosen because it never supplied a surface text, which is what was being chosen. It remains the right reading of what a body-less rule **is**, written in syntax the language already has.

   **The one interaction worth spelling out, because 060 and this proposal look like they collide and do not.** 060 §2 reads `?x: T` on a relational head as a `domain(?x, T)` **goal**, prepended to the rule's body — the ascription is spent generating values. That reading is about a **clause**. A body-less head is not a clause and has no body for such a goal to go into, so the ascription is free to be what it looks like: the **column's type**. So this spelling gets *name plus typed columns* — the form Soufflé and SQL both land on, and the thing 052 says a relation's schema **is** — with no new keyword:

   ```anthill
   rule allowed(?from: Stage, ?to: Stage)               -- declaration: two columns, both Stage
   rule allowed(?f: Stage, ?t: Stage) :- edge(?f, ?t)   -- clause: 060's domain(…) goals apply
   ```

   **Not claimed as delivered**: 060's typed-head work is WI-742 and unimplemented, and which reading a body-less typed head takes must be written into 060 rather than assumed from here.

   **What it does not settle.** Whether a declared predicate is an **operation** — on the dispatch surface, with a return type — is untouched by the spelling: that is open question 4 and 052 OQ2. The earlier [declared-relations](../brainstorms/declared-relations.md) session answered it independently (Decision 5: a relation is a distinct kind, *not* an operation without a return), which is the direction §"What it removes" already assumes but does not argue.

2. **Arity is NOT part of a predicate's identity, and that is measured.** Operations refuse two declarations of one name (WI-1049), while predicates accept clauses of mixed arity and **dispatch** them correctly — driven over `{ rule p(1); rule p(1,2); rule p(7) }`: `p(1)`→1, `p(7)`→1, `p(1,2)`→1, `p(9)`→0, `p(1,9)`→0. So the language is inconsistent with itself here (WI-20260821-ZW940). But the deciding fact is that **a bare name is a VALUE**: `apply1(twice, 3)` loads, `twice` alone denoting the function, and 052 OQ2 wants bare `Queen.find` citable as a `Relation[T]`. Arity is visible in call position and invisible in value position, so signature-keyed overloading would make the bare name ambiguous — which is exactly what the duplicate-operation refusal means by "a scope maps a name to one symbol". Corpus census: of 41 multi-clause predicates, **1** has mixed arity, and it is the kernel's own `Constraint`.
3. **A single-file mutual cycle** — `namespace mA { import mB.*; rule p(1) } namespace mB { import mA.*; rule p(2) }` in one file — is auto-declared with no outermost scope to pick, so WI-980's cycle handling is still needed for it. It is visible to its own author, which is 059's argument for the file boundary, but it is the residue and should be stated rather than assumed away.

   **SETTLED BY WI-20260822-845G7: there is no residue, because there is no cycle handling.** Every scope introduces at its own address, cycle or not, and a name introduced at two mutually-reachable scopes is refused — in one file exactly as in several. The paragraph below records how the single-file case was decided before that, and why the file boundary it rested on did not survive.

   **The MULTI-FILE cycle is no longer residue — it is refused (WI-20260821-E85J5).** The file rule above is keyed on the PREDICATE, and WI-980's tie-break splits a cycle into two *single-file* predicates before the file rule counts anything, so the one assembly this proposal exists to refuse was the one it could not see. What the silence cost a use was then measured: a scope's own name beats an import (`resolve_in_scope` returns from `locals` before consulting any import or parent), so the predicate the tie-break minted at `mA` shadows the `import mB.*` that made the cycle — `mA.usesp(2)`=0 against a control, with no own `p`, of 1. The shadow itself is uniform with the rest of the language and is kept; what is refused is inventing it out of two files neither of which shows the cycle. Both remedies this proposal already prescribes work and are driven: one declaration in the owning scope makes the other scopes' heads its clauses (`mA.p` gains both, `usesp(2)`=1), one in **each** scope says they are separate predicates (the shadow, as written). The refusal's narrowness is bounded by two measured non-cases — a NESTED two-file cycle is the ordinary `heads in more than one file` error, since the enclosing member owns; a cycle inside ONE file keeps auto-declaring, which is what this open question is about and stays about.
4. **Does a declaration join the dispatch surface?** It must not (059: the surface is exactly the operations), but 052 OQ2 wants `Sort.rule` citable as a `Relation[T]` value — so a declared predicate is exactly the thing that arm would resolve, and the two proposals should agree on what a declaration makes citable.
5. **Migration for the multi-file rule.** Zero today, measured. But the rule is a *whole-program* property — a predicate becomes "multi-file" when someone adds a second file, so an edit in one place can require a declaration somewhere else. That is the same discomfort 059 records for secondary entries ("a namespace becomes a secondary entry because someone else declared a sort at its address"), and it should be recorded here too rather than discovered.
