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
  rule p(?x, ?y)              -- DECLARATION: `demo.p` exists, arity 2, no clauses

  rule p(1, 2)                -- a clause of it
  sort Rec
    rule p(3, 4)              -- also a clause of it — resolution, not introduction
  end
end
```

Nothing about resolution changes: the head runs the ordinary ladder, exactly as §WI-896 says, and contributes a clause to whatever it lands on. What changes is that there is now something to land on, put there by pass 1 like every other name — so *when* the ladder is asked stops mattering, which is the invariant WI-321 gives every other name kind.

**A scope that wants its own predicate where an enclosing one resolves declares it.** That is §WI-896's own remedy, which today has no form: the only way to declare a predicate name is a body-less `operation`, and that drags in a signature and membership of the dispatch surface (059 §Definitions: "the dispatch surface of `X` is exactly the operations"). A rule declaration is the form the remedy always assumed.

## Auto-declaration, and where it stops

Requiring a declaration for every predicate would be a migration for no gain in the common case: a predicate whose clauses are all in one file has one author, who can see all of them.

> **A predicate whose heads are all written in ONE file is auto-declared, in the scope §WI-896's ladder already picks. A predicate with heads in MORE THAN ONE file must be declared explicitly; without a declaration it is a load error naming the files.**

**The file is the unit, and 059 already argued why** (§Definitions): what the rule guards against is a predicate "assembled by two parties that never agreed on it", and two blocks in one file are one author making one edit — a file boundary is the smallest place where *two parties* is real. It is also the unit `import` already uses, since an import resolves only in the file it is written in.

**Census: the rule refuses nothing that exists.** Over stdlib + `anthill-stl` + `examples/github-todo`: **102** predicates carry rule heads, and **every one of them has its heads in exactly one file** — zero span more than one. The corpus cost of requiring a declaration for the multi-file case is therefore **zero**, and the 43 distinct rule-introduced names (14 in `anthill.reflect.typing`, 8 in `logic.Constructive`, 7 in `anthill.stage0.workflow`, 3 each in `reflect.feed`, `realization`, `logic.Classical`, …) are all auto-declared.

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

1. **Spelling.** `rule p(?x, ?y)` with no body is the minimal form and needs no grammar change — it is already parsed, and only the interpretation is new. But a body-less head is today an ordinary **fact** (`rule parent("alice","bob")` is a ground assertion, §"Facts are rules"), so the two are ambiguous at the surface: a declaration must be distinguishable from a ground fact whose arguments happen to be variables. Options: require all-variable arguments and treat that as the declaration (measured risk: `rule p(?x, ?x)` is a legitimate fact-shaped clause); a keyword (`declare rule p(?x, ?y)`); or an arity-only form.
2. **Is the declaration also the arity?** A predicate's clauses may differ in arity today. If a declaration fixes arity, that is a new check and a new refusal; if it does not, the declaration carries only a name and a scope.
3. **A single-file mutual cycle** — `namespace mA { import mB.*; rule p(1) } namespace mB { import mA.*; rule p(2) }` in one file — is auto-declared with no outermost scope to pick, so WI-980's cycle handling is still needed for it. It is visible to its own author, which is 059's argument for the file boundary, but it is the residue and should be stated rather than assumed away.
4. **Does a declaration join the dispatch surface?** It must not (059: the surface is exactly the operations), but 052 OQ2 wants `Sort.rule` citable as a `Relation[T]` value — so a declared predicate is exactly the thing that arm would resolve, and the two proposals should agree on what a declaration makes citable.
5. **Migration for the multi-file rule.** Zero today, measured. But the rule is a *whole-program* property — a predicate becomes "multi-file" when someone adds a second file, so an edit in one place can require a declaration somewhere else. That is the same discomfort 059 records for secondary entries ("a namespace becomes a secondary entry because someone else declared a sort at its address"), and it should be recorded here too rather than discovered.
