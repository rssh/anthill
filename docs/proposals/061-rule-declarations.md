# 061: Rule declarations — a predicate is declared, not discovered

**Canonical reference:** [`kernel-language.md` §8.6](../kernel-language.md), §"A rule head functor is resolved, not declared" and §"A rule-introduced functor is scoped where it is written".

## Status: Draft (2026-08-21). Written from WI-980, which made a rule head's binding order-independent and, in doing so, measured what it costs to decide a name *during* the pass that creates it. Measurement claims below are taken from the Rust loader with both-sides controls; the rule and its staging are prescriptive.

## Relates to: WI-980 (order-independent head binding — this proposal is its structural alternative), WI-896 (a head is resolved, not declared — amended here), 059 §Definitions (the FILE as the unit at which "two parties" becomes real), 052 (rules as stream-valued operations — a declared predicate is the name such a value is cited by), WI-898 (equational heads index under the connective — **out of scope**, see below), 060 (clause-level typed heads — the guard that makes a shared predicate safe), WI-995 (imports are file-local — the reason a predicate's clauses in two files can disagree).

## The problem

**A predicate is the only name in the language with no declaration.** Four core constructs — `namespace`, `sort`, `rule`, `operation` — and of those only `rule` brings a name into existence *as a side effect of using it*. Every other name is defined in the loader's first pass, before anything resolves anything; a rule head's name is created during the pass that decides it.

That is the whole of WI-980. Measured: `rule p(1)` beside `sort Rec { rule p(2) }` loaded as **one** predicate with two clauses when the namespace-level rule was written first and as **two** predicates when it was written second. Operations show no such thing — the identical shape with `operation` in place of `rule` is refused identically in all four orders (one file / two files × both orders), because an operation makes no decision: its name goes to its own scope, always.

WI-980 closed the ordering by asking a question the pass cannot move — *does some scope this one can see already introduce the name* — resolved through the resolver itself. That works, and it is machinery: a recursion with a memo, a cycle detector, an enclosure tie-break, a depth bound, and a per-`(scope, name, file)` split forced by file-local imports. Every one of those exists to *infer* something an author could simply have said.

## The rule

> **A logical rule's head functor names a DECLARED predicate. A declaration is written once, in one file, in the scope that owns the name; a rule head is always a clause OF something and never brings a name into existence.**

The declaration is a head with no body and no clauses:

```anthill
namespace demo
  ⟨declaration of p — SPELLING NOT YET SETTLED, see open question 1⟩

  rule p(1, 2)                -- a clause of it
  sort Rec
    rule p(3, 4)              -- also a clause of it — resolution, not introduction
  end
end
```

The declaration's **spelling is deliberately left as a placeholder** through this proposal. What it must DO is settled — bring the name into existence in pass 1, in one scope, asserting nothing — and that is what the rules below are written against. Which text carries it is open question 1, and the proposal is readable without fixing it.

Nothing about resolution changes: the head runs the ordinary ladder, exactly as §WI-896 says, and contributes a clause to whatever it lands on. What changes is that there is now something to land on, put there by pass 1 like every other name — so *when* the ladder is asked stops mattering, which is the invariant WI-321 gives every other name kind.

**A scope that wants its own predicate where an enclosing one resolves declares it.** That is §WI-896's own remedy, which today has no form: the only way to declare a predicate name is a body-less `operation`, and that drags in a signature and membership of the dispatch surface (059 §Definitions: "the dispatch surface of `X` is exactly the operations"). A rule declaration is the form the remedy always assumed.

## Auto-declaration, and where it stops

Requiring a declaration for every predicate would be a migration for no gain in the common case: a predicate whose clauses are all in one file has one author, who can see all of them.

> **A predicate whose heads are all written in ONE file is auto-declared, in the scope §WI-896's ladder already picks. A predicate with heads in MORE THAN ONE file must be declared explicitly; without a declaration it is a load error naming the files.**

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

## Open questions

1. **Spelling — OPEN.** What the declaration must DO is settled: bring the name into existence in pass 1, in one scope, **asserting nothing**. Which text carries it is not.

   **The negative half IS settled: no body-less HEAD can serve.** `head` is `head :- true`, and that reading does not vary with groundness — the ground spelling asserts one tuple, the variable spelling the universal relation — and the language must not give one syntax two readings according to whether its arguments are ground. Each candidate head form is already spoken for:

   | head form | what it already means |
   |---|---|
   | `rule p("a", "b")` | a clause: that tuple holds |
   | `rule p(?x, ?y)` | the universal relation. Worse than useless: it **entails** every `p(a,b)`, so later clauses add nothing — measured, adding or removing plugin clauses beneath it changes no answer |
   | `rule p(?x: T, ?y: U)` | 060 §2's generator — a `domain(?x, T)` goal that ENUMERATES over T |
   | `rule p/2` | nothing else uses `/arity`, and arity is not part of a predicate's identity, so the number identifies nothing |
   | `rule ns.p(…)` | a clause of an existing predicate; by §WI-896 it can never introduce one |

   **What a declaration MEANS, and why every short form is an abbreviation of it.** Written out, the declaration is a **second-order existential**: *there exists a predicate p* —

   ```
   ∃p . declared(p)              -- the technically correct form; long, and second-order
   ```

   That is the reading every variant below abbreviates, and it explains the shape of the whole search. An existential **binds** its variable, which makes `p` a MENTION rather than a use.

   **The language already HAS a mention position — scoped to an implication.** Anthill is not first-order: it carries Miller's fragment, the unbounded **hereditary-Harrop** form `(forall(?x), Q(?x) -: P(?x))` used by the auto-generated induction principles, and higher-order predicate variables (`rule ind(?P) :- ?P(nil)`, desugaring to `ho_apply`). And §"A rule head functor is resolved, not declared" already says the antecedent of such a discharge **declares** its functor. Measured:

   ```
   rule ind(?x) :- (forall(?n), undeclared_here(?n) -: undeclared_here(?n))   →  LOADS
   rule ind(?x) :- undeclared_here(?x)                                        →  REFUSED,
       "rule-body goal `undeclared_here` names nothing"
   ```

   So the question this proposal asks is not *invent a mention position* — it is **give the language, at NAMESPACE scope, the declaration-by-assumption it already has at implication scope**. That is also how λProlog, the source of this fragment, answers it: a separate **signature** (`sig mymod. type append list A -> list A -> list A -> o.`) declares what a module's predicates are, distinct from the clauses that define them.

   Each candidate below is a way of getting that mention position into a namespace:

   - **V1 / V1a** borrow one from `operation`, which already has a declaration form.
   - **V2 / V3 / V5** mint one with a keyword.
   - **V4 / V6** try to reuse a rule form, and fail because a rule USES its functor rather than mentioning it.
   - **V7** tries argument position, and fails on exactly this point — measured, the argument is a `Ref` only when the predicate already exists and degrades to `Ident` when it does not, which is the difference between a use and a mention made visible.
   - **V8** — a namespace-scoped **assumption**: the hereditary-Harrop antecedent with the NAMESPACE as the implication's scope.

     ```
     (forall(?x), p(?x) -: G)          -- an assumption scoped to a goal — exists today
     ⟨declare p⟩ inside namespace demo -- the same assumption, scoped to the namespace
     ```

     This is the variant most native to the logic the language already implements, and it supplies the property every head form failed to: **an assumption asserts nothing.** It is not a claim added to the knowledge base; it is a hypothesis the scope is elaborated under and discharged by. That is exactly why `head :- true` cannot serve and this can — the difference is assertion versus assumption, not syntax.

     It also makes the multi-file rule fall out instead of being stipulated: a namespace spans files, so an assumption scoped to the namespace covers every file that writes into it — which is the scope §Auto-declaration needs. And it is λProlog's module semantics directly: `sig` declares, `module` supplies the clauses, and the signature is the assumption the module is elaborated under.

     Open within V8: what the surface text is (it still needs one), whether the assumption is discharged at the namespace boundary or persists into the KB, and how it interacts with 059's secondary entries, which let a second file write into one scope.

   **The variants fall into two DIRECTIONS, and the syntax question is downstream of which one is taken.**

   - **A — the declaration is an OPERATION of the same name, with a standard body** (V1a). The predicate *is* an operation; its body runs its own clauses. No new syntax. It makes 052's claim — a rule is a stream-valued operation — literally true rather than aspirational, and answers 052 OQ2 for free, since `Sort.p` is then a member. Its two consequences are not side effects but the design itself: the predicate joins the **dispatch surface**, and it has a **return type**, which is exactly 052's `Relation[T]` question.
   - **B — the declaration is its own kind** (V2–V5). A declared predicate is not an operation: no dispatch surface, no return type, nothing to run. Needs new syntax, and keeps rules and operations distinct — so 052's claim stays partly aspirational and `Sort.p` still needs OQ2's arm.

   **So the real fork is whether rules and operations converge or stay distinct.** Measured, they are distinct today: a rule head is not on the dispatch surface (`x.p(y)` → *"expected operation declared on the receiver's sort, got no such member (dot dispatch)"*, while the sibling operation is found), and a rule-introduced name earns `SymbolKind::Goal`, not `Operation`. **B is the status quo made explicit; A is a genuine unification.**

   **Variants to choose among.** Each does the job; they differ in what they cost and what else they buy.

   | | spelling | for | against |
   |---|---|---|---|
   | **V1** | `operation p(from: String, to: String) -> Bool` — body-less | **exists today**; documented (*"a body-less operation carrying clauses is one definition written relationally"*); measured working at namespace AND sort level, declaration-alone resolving with zero clauses | it has a GOAL face and **no value-call face** (below); joins the **dispatch surface** (059), so `receiver.p(x)` becomes callable; carries a **return type**, and `-> Bool` reads as a test where 052 reads a rule as `Relation[T]` |
   | **V1a** | V1 plus a **standard body** — the declaration's body is "consult my own clauses" | closes V1's missing face without a new keyword, and is 052's own claim (a rule IS a stream-valued operation) made operational | needs a canonical body to exist and to be specified — what it returns for a multi-solution relation is exactly 052's `Relation[T]` question |
   | **V2** | `relation p(from: String, to: String)` | reads natively; names what 052 already calls `Relation[T]`; carries column names AND types, which is the schema 052 says a relation *is*; no dispatch-surface question | a new keyword |
   | **V3** | `shared rule p(?x, ?y)` / `multifile rule p(?x, ?y)` | Prolog's `multifile` precedent; says *why* the declaration exists, so the diagnostic writes itself | a new keyword, and it covers only the multi-file case — §WI-896's *"to introduce a name that already resolves, declare it"* still has no form |
   | **V4** | `rule p(?x, ?y) [decl]` | **no grammar change** — 043's attribute channel already exists | attributes say how a rule *fires*, not whether it is one; and to a human the head still reads as the universal relation |
   | **V9** | **change `fact`'s desugaring to carry the body explicitly** — `fact p("a","b")` → `rule p("a","b") :- true` — which frees the body-less `rule` form to be the declaration | no new keyword, and it makes the language UNIFORM: `operation f(…) -> R` declares and `= body` defines; `const N: T` declares and `= expr` defines; `rule p(…)` would declare and `:- body` define. **No body ⇒ declares; a body ⇒ asserts**, across all four constructs, with `rule` no longer the exception. It also removes the groundness question entirely: the ARGUMENTS stop carrying the distinction and the BODY carries it, so `rule p(?x,?y)` and `rule p("a","b")` are read the same way. Migration measured at **25 sites**, all in the stdlib. **The grammar does not move**: `fact` is already its own IR item (`"fact_declaration" => convert_fact(…).map(Item::Fact)`) and a body-less rule is already `Item::Rule { body: None }`, so the two are distinguishable before any desugaring — the change is what the LOADER reads `body: None` as, from "assert" to "declare", with `Item::Fact` untouched | §6.1's desugaring changes, and with it the sentence calling a fact a "ground assertion"; the 25 sites — the logic axioms `rule modus_ponens(?p, ?q)` / `rule excluded_middle(?p)`, and pattern clauses like `rule type_compatible(?A, ?A)` — must each become `fact …` or gain an explicit `:- true`, and which of the two they want is a per-site reading, not a mechanical rewrite |
   | **V7** | `rule declared(allowed)` — a reflective fact the loader reads, Prolog's directive idea in anthill's own reflective-fact idiom (`SortInfo`, `OperationInfo`, `DescriptionInfo`) | no new syntax at all; reuses the fact machinery; precedent in both Prolog's `:- dynamic p/2` and this language's own `anthill.reflect` facts | **the argument cannot reference what does not exist yet**, measured: `declared(allowed)` resolves to `Ref(Symbol)` when `allowed` already has a clause and degrades to `Ident(Symbol)` when it does not — which is exactly the case a declaration is for. Making it work means the loader special-cases `declared` and reads the `Ident`, so the argument is a NAME rather than a reference: `declared(allowd)` then declares a phantom in silence, and `Ident` is the carrier `functor_sym` is already known to miss |
   | **V6** | `rule :- p(?x, ?y)` — a headless rule | **the spelling is free**: measured, both `rule :- p(?x,?y)` and a bare `:- p(?x,?y)` are syntax errors today, since anthill's denial form is keyword-tagged (`constraint c :- …`). No new keyword | `:- B` means DENIAL to every logic programmer, and §6.2 is literally titled *"Constraint (headless rule / denial)"* — so it would read as *"p never holds"*, an assertion of the opposite. Logically backwards: a declaration asserts nothing, `:- B` asserts ¬B. And a body is a conjunction, so `rule :- p(?x), q(?y)` does not say which predicate it declares |
   | **V5** | `defines p(?x, ?y)` at namespace level | parallel to `requires` / `provides`; reads as a statement about what this namespace defines | a new keyword; says nothing about columns or types |

   **V1 has a goal face and no value-call face, measured.** With `operation allowed(from, to) -> Bool` declared body-less and `rule allowed("a","b")` supplying a clause:

   ```
   as a GOAL   — allowed("a","b") in a rule body            →  answers (1 solution)
   as a CALL   — operation use() -> Bool = allowed("a","b") →  ERROR "operation has no body:
                 cw.allowed — nothing this runtime can run is registered for it"
   ```

   The stdlib is no different: `Set.empty` fails the same way, because its body-less operations are **spec** operations backed per-carrier through the requirement dictionary, not things called directly. So "defined relationally" today means *usable as a goal*, and the value-level call is simply absent.

   That is what V1a addresses — give the declaration a canonical body meaning "consult my own clauses", so the call face is defined in terms of the clauses that already answer the goal face. It is also where 052 and this proposal meet: 052 says a rule IS a stream-valued operation, and a standard body is that claim made runnable rather than asserted.

   **What other languages do**, since every one of them that lets clauses span files has an explicit declaration and none auto-declares across them:

   | language | form | bearing |
   |---|---|---|
   | Prolog | `:- multifile p/2.` `:- discontiguous p/2.` | `multifile` IS this proposal's rule, by name. Its spelling — a top-level directive — is unavailable here: §6.2 spends the headless form on denial |
   | Mercury | `:- pred p(int, int).` / `:- func f(int) = int.` | declarations MANDATORY; and `pred` vs `func` keeps predicates and functions **distinct kinds with distinct syntax** — external evidence for direction B over A |
   | Soufflé (Datalog) | `.decl edge(x:number, y:number)` | declaration with **typed columns** — V2 almost verbatim |
   | SQL | `CREATE TABLE t(a INT, b TEXT)` | the relation is declared with typed columns before any row exists |
   | Haskell / Rust | `class C a where m :: a -> Int`, instances elsewhere | the extension-point pattern: signature in one place, definitions across modules — C666A's spec/implementor shape |

   Two independent traditions (Soufflé, SQL) land on **name plus typed columns**, which is what 052 says a relation's schema *is*. And the one language that took predicate declarations most seriously, Mercury, kept predicates and functions apart rather than unifying them.

   **Two candidates stand out, for opposite reasons.** **V8** is the only one where the declaration asserts nothing *by construction* — an assumption is not an assertion — and it is native to the Miller fragment the language already implements. **V9** is the only one that needs no new syntax AND leaves the language more uniform than it found it: *no body ⇒ declares* would hold for `operation`, `const` and `rule` alike, and `rule` is currently the sole exception only because `fact`'s desugaring took its body-less form.

   **The decision is to pick one of these or to propose another.** V1 is the only one that ships today, and V2 is the only one that carries 052's schema; the two consequences under V1 — dispatch surface and return type — are what a choice has to weigh against V2's new keyword.

2. **Arity is NOT part of a predicate's identity, and that is measured.** Operations refuse two declarations of one name (WI-1049), while predicates accept clauses of mixed arity and **dispatch** them correctly — driven over `{ rule p(1); rule p(1,2); rule p(7) }`: `p(1)`→1, `p(7)`→1, `p(1,2)`→1, `p(9)`→0, `p(1,9)`→0. So the language is inconsistent with itself here (WI-20260821-ZW940). But the deciding fact is that **a bare name is a VALUE**: `apply1(twice, 3)` loads, `twice` alone denoting the function, and 052 OQ2 wants bare `Queen.find` citable as a `Relation[T]`. Arity is visible in call position and invisible in value position, so signature-keyed overloading would make the bare name ambiguous — which is exactly what the duplicate-operation refusal means by "a scope maps a name to one symbol". Corpus census: of 41 multi-clause predicates, **1** has mixed arity, and it is the kernel's own `Constraint`.
3. **A single-file mutual cycle** — `namespace mA { import mB.*; rule p(1) } namespace mB { import mA.*; rule p(2) }` in one file — is auto-declared with no outermost scope to pick, so WI-980's cycle handling is still needed for it. It is visible to its own author, which is 059's argument for the file boundary, but it is the residue and should be stated rather than assumed away.
4. **Does a declaration join the dispatch surface?** It must not (059: the surface is exactly the operations), but 052 OQ2 wants `Sort.rule` citable as a `Relation[T]` value — so a declared predicate is exactly the thing that arm would resolve, and the two proposals should agree on what a declaration makes citable.
5. **Migration for the multi-file rule.** Zero today, measured. But the rule is a *whole-program* property — a predicate becomes "multi-file" when someone adds a second file, so an edit in one place can require a declaration somewhere else. That is the same discomfort 059 records for secondary entries ("a namespace becomes a secondary entry because someone else declared a sort at its address"), and it should be recorded here too rather than discovered.
