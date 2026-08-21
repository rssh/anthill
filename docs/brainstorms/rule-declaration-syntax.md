# Rule declaration syntax — the nine variants and what each one cost

## Status: Brainstorming draft (2026-08-21)

Split out of **[proposal 061](../proposals/061-rule-declarations.md)** when its open
question 1 was settled, so the proposal states the rule and this records the search.
**Not a proposal.** Nothing here is normative; 061 §"The declaration's syntax" is.

The question: Anthill needs a way to *declare a predicate* — bring the name into
existence in pass 1, in one scope, **asserting nothing**. What it must DO was settled
early. Which text carries it was not, and nine candidates were measured before **V9**
(a rule with no body) was chosen.

## Relates to

- **[061](../proposals/061-rule-declarations.md)** — the proposal this was split from.
- **[declared-relations.md](declared-relations.md)** — the earlier session on the same
  substrate. Its **Decision 5** ("a relation is a distinct kind — NOT *operation without
  a return*") is independent support for direction **B** below, reached two months before
  this search and without reference to it.
- **052** (rules as stream-valued operations), **059** (secondary entries),
  **060** (clause-level typed heads), **WI-896**, **WI-980**.

## Why every HEAD form looked spoken for

The objection that shaped the whole search: `head` means `head :- true`, and that reading
does not vary with groundness — the ground spelling asserts one tuple, the variable
spelling the universal relation — so any head form would give one syntax two readings
according to whether its arguments are ground.

It held for a long time, and it is why V1–V8 all try to find a *different* position to
declare from. It turned out to be **conditional**: `head :- true` is what a body-less head
means *because `fact` was desugared onto that form* (§6.1). Move the `:- true` into the
desugaring and the objection disappears for every row at once — which is V9.

The table as it stood before that move:

| head form | what it meant before | under V9 |
|---|---|---|
| `rule p("a", "b")` | a clause: that tuple holds | **declares `p`**; the clause is `fact p("a", "b")` |
| `rule p(?x, ?y)` | the universal relation. Worse than useless: it **entails** every `p(a,b)`, so later clauses add nothing — measured, adding or removing plugin clauses beneath it changes no answer | **declares `p`** — and the useless reading stops being reachable at all, which is a gain rather than a cost |
| `rule p(?x: T, ?y: U)` | 060 §2's generator — a `domain(?x, T)` goal that ENUMERATES over T | **declares `p` with typed columns** — no collision, because 060 spends the ascription on a *clause* and this shape is not one ([061 open question 1](../proposals/061-rule-declarations.md) spells this out) |
| `rule p/2` | nothing else uses `/arity`, and arity is not part of a predicate's identity, so the number identifies nothing | dead twice over — [061 §One arity per predicate](../proposals/061-rule-declarations.md) |
| `rule ns.p(…)` | a clause of an existing predicate; by §WI-896 it can never introduce one | unchanged: a qualified head still never introduces |


## What a declaration MEANS

**Why every short form is an abbreviation of it.** Written out, the declaration is a **second-order existential**: *there exists a predicate p* —

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

## Two directions

**The variants fall into two DIRECTIONS, and the syntax question is downstream of which one is taken.**

- **A — the declaration is an OPERATION of the same name, with a standard body** (V1a). The predicate *is* an operation; its body runs its own clauses. No new syntax. It makes 052's claim — a rule is a stream-valued operation — literally true rather than aspirational, and answers 052 OQ2 for free, since `Sort.p` is then a member. Its two consequences are not side effects but the design itself: the predicate joins the **dispatch surface**, and it has a **return type**, which is exactly 052's `Relation[T]` question.
- **B — the declaration is its own kind** (V2–V5). A declared predicate is not an operation: no dispatch surface, no return type, nothing to run. Needs new syntax, and keeps rules and operations distinct — so 052's claim stays partly aspirational and `Sort.p` still needs OQ2's arm.

**So the real fork is whether rules and operations converge or stay distinct.** Measured, they are distinct today: a rule head is not on the dispatch surface (`x.p(y)` → *"expected operation declared on the receiver's sort, got no such member (dot dispatch)"*, while the sibling operation is found), and a rule-introduced name earns `SymbolKind::Goal`, not `Operation`. **B is the status quo made explicit; A is a genuine unification.**

## The nine variants

Each does the job; they differ in what they cost and what else they buy.

| | spelling | for | against |
|---|---|---|---|
| **V1** | `operation p(from: String, to: String) -> Bool` — body-less | **exists today**; documented (*"a body-less operation carrying clauses is one definition written relationally"*); measured working at namespace AND sort level, declaration-alone resolving with zero clauses | it has a GOAL face and **no value-call face** (below); joins the **dispatch surface** (059), so `receiver.p(x)` becomes callable; carries a **return type**, and `-> Bool` reads as a test where 052 reads a rule as `Relation[T]` |
| **V1a** | V1 plus a **standard body** — the declaration's body is "consult my own clauses" | closes V1's missing face without a new keyword, and is 052's own claim (a rule IS a stream-valued operation) made operational | needs a canonical body to exist and to be specified — what it returns for a multi-solution relation is exactly 052's `Relation[T]` question |
| **V2** | `relation p(from: String, to: String)` | reads natively; names what 052 already calls `Relation[T]`; carries column names AND types, which is the schema 052 says a relation *is*; no dispatch-surface question | a new keyword |
| **V3** | `shared rule p(?x, ?y)` / `multifile rule p(?x, ?y)` | Prolog's `multifile` precedent; says *why* the declaration exists, so the diagnostic writes itself | a new keyword, and it covers only the multi-file case — §WI-896's *"to introduce a name that already resolves, declare it"* still has no form |
| **V4** | `rule p(?x, ?y) [decl]` | **no grammar change** — 043's attribute channel already exists | attributes say how a rule *fires*, not whether it is one; and to a human the head still reads as the universal relation |
| **V9** | **change `fact`'s desugaring to carry the body explicitly** — `fact p("a","b")` → `rule p("a","b") :- true` — which frees the body-less `rule` form to be the declaration | no new keyword, and it makes the language UNIFORM: `operation f(…) -> R` declares and `= body` defines; `const N: T` declares and `= expr` defines; `rule p(…)` would declare and `:- body` define. **No body ⇒ declares; a body ⇒ asserts**, across all four constructs, with `rule` no longer the exception. It also removes the groundness question entirely: the ARGUMENTS stop carrying the distinction and the BODY carries it, so `rule p(?x,?y)` and `rule p("a","b")` are read the same way. Migration measured at **20 sites** — 17 stdlib, 3 `examples/github-todo` (a parser-driven census; an earlier regex pass said *25, all in the stdlib* and was wrong on both counts). **The grammar does not move**: `fact` is already its own IR item (`"fact_declaration" => convert_fact(…).map(Item::Fact)`) and a body-less rule is already `Item::Rule { body: None }`, so the two are distinguishable before any desugaring — the change is what the LOADER reads `body: None` as, from "assert" to "declare", with `Item::Fact` untouched | §6.1's desugaring changes, and with it the sentence calling a fact a "ground assertion"; the 20 sites — the logic axioms `rule modus_ponens(?p, ?q)` / `rule excluded_middle(?p)`, and pattern clauses like `rule type_compatible(?A, ?A)` — must each become `fact …` or gain an explicit `:- true`, and which of the two they want is a per-site reading, not a mechanical rewrite; and the `=`/`===` body-less refusals must be re-keyed on the head functor in the same change, since a `fact` reaches them today only through the desugaring (measured) |
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

## What other languages do

Every one of them that lets clauses span files has an explicit declaration and none auto-declares across them:

| language | form | bearing |
|---|---|---|
| Prolog | `:- multifile p/2.` `:- discontiguous p/2.` | `multifile` IS this proposal's rule, by name. Its spelling — a top-level directive — is unavailable here: §6.2 spends the headless form on denial |
| Mercury | `:- pred p(int, int).` / `:- func f(int) = int.` | declarations MANDATORY; and `pred` vs `func` keeps predicates and functions **distinct kinds with distinct syntax** — external evidence for direction B over A |
| Soufflé (Datalog) | `.decl edge(x:number, y:number)` | declaration with **typed columns** — V2 almost verbatim |
| SQL | `CREATE TABLE t(a INT, b TEXT)` | the relation is declared with typed columns before any row exists |
| Haskell / Rust | `class C a where m :: a -> Int`, instances elsewhere | the extension-point pattern: signature in one place, definitions across modules — C666A's spec/implementor shape |

Two independent traditions (Soufflé, SQL) land on **name plus typed columns**, which is what 052 says a relation's schema *is*. And the one language that took predicate declarations most seriously, Mercury, kept predicates and functions apart rather than unifying them.


## The outcome

**V9.** It costs no grammar and no keyword, and it *removes* an irregularity rather than
adding a construct to work around one. **V8** remains the better account of what a
declaration *means* — an assumption asserts nothing by construction, which is precisely
the property `head :- true` lacked — and that reading is not discarded: it is what V9's
body-less rule **is**, written in syntax the language already has. What V8 never supplied
was a surface text, which is what was being chosen.

Recorded in [061 §"The declaration's syntax"](../proposals/061-rule-declarations.md),
with the split point (`EQUATION_FUNCTORS`' single member), the 97-vs-20 corpus census,
and the one consequence that must land in the same change: the `=`/`===` body-less
refusals read a `fact` only through §6.1's desugaring, so they must be re-keyed on the
head functor when that desugaring moves.
