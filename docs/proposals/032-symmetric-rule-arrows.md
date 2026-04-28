# Proposal 032: Symmetric Rule Arrows

**Status:** Draft
**Related:** [023-kb-guards](023-kb-guards.md), [025-proof-constructs](025-proof-constructs.md), [031-structured-proofs](031-structured-proofs.md)
**Affects:** `docs/kernel-language.md` §5.3, `tree-sitter-anthill/grammar.js` (rule production), `rustland/anthill-core/src/parse/` (rule IR + converter), `scaland/` (parallel parser), all call sites using `rule H :- B -: C` form

## Motivation

The current rule grammar gives `:-` and `-:` *different* roles at top level:

```
Rule ::= 'rule' [Name ':'] Head [':-' Body] ['-:' Conclusion]
```

A rule with both arrows is **two rules wearing one syntactic coat** — each backend pulls a *different* logical content out of the same source:

- **SLD** (kernel-language.md §5.3, line 717) treats the rule as `H :- B` and ignores `-: C`. The head `H` is the goal; `C` does not appear in resolution.
- **Z3** (lines 706–711) encodes the rule as `B ⇒ C` and ignores `H`. The conclusion `C` is what gets checked; `H` is unused.

A literal reading of the surface — "H if B, and B then C" — would be `B ⇒ H ∧ C`, i.e. `H, C :- B`, which is not Horn. The current grammar avoids that by letting each backend pick a different sub-clause; the cost is that the same syntax means two different things depending on who reads it.

This produces three concrete problems:

1. **Reader confusion.** `rule n :- y -: z` is parsed as anonymous rule with head `n`, body `y`, conclusion `z`. A reader scanning quickly mistakes `n` for a name (because the named form is `rule n: head :- body`, and the `n:` separator is quiet next to `:-` and `-:`). Two arrows within one line, plus an optional `name:` colon, create three colon-shaped tokens fighting for attention.

2. **Asymmetry with nested implications.** Proposal 025 already specifies `:-` and `-:` as **interchangeable surface forms of one implication operator** inside `forall` and as nested goal terms:

   > Both mean P → Q. The author picks whichever reads better in context.

   At top level the *same two tokens* mean different things: `:-` introduces a body, `-:` introduces a separate conclusion slot, and a rule may carry both. Readers cannot transfer their mental model from nested goals to top-level rules.

3. **Citability carve-out.** The current spec (kernel-language.md §5.3) states that rules without `-:` are not citable via `using` because their theorem statement is "the body has no satisfying instance" rather than `premises ⇒ conclusion`. This carve-out exists only because the dual-arrow form is the only way to mark a "real" conclusion. Removing the dual form removes the carve-out: every named rule has a determinate conclusion (its head) and is uniformly citable.

## Design

**One implication operator, two surface directions, applied uniformly at every level of the grammar.**

```
A :- B    ≡    B -: A         (logically: B ⇒ A)
```

Top-level rule:

```
Rule  ::= 'rule' [Name ':'] (Heads ':-' Body | Body '-:' Heads | Heads)
Heads ::= Term (',' Term)*    -- one or more heads (multi-head: conjunctive sugar)
        | '⊥'                 -- denial
Body  ::= Term (',' Term)*
```

Exactly one arrow per rule, or zero (the bare `Heads` form with a single head is a fact). The combined `Head :- Body -: Conclusion` form is removed.

Nested implication (already symmetric per proposal 025) is unchanged; this proposal extends the same symmetry to the top level.

### Equivalences

```anthill
-- Derivation rule (Horn), backward and forward forms:
rule ancestor(?X, ?Z) :- parent(?X, ?Y), ancestor(?Y, ?Z)
rule parent(?X, ?Y), ancestor(?Y, ?Z) -: ancestor(?X, ?Z)

-- Denial / integrity constraint, backward and forward:
rule ⊥ :- balance(?a, ?b), lt(?b, 0)
rule balance(?a, ?b), lt(?b, 0) -: ⊥

-- Fact (no arrow):
rule parent("alice", "bob")

-- Positive theorem — the *real* conclusion is the head, in either direction:
rule lower_bound: gte(?d, ?d_min)
  :- reachable_real(?l, ?f), position_distance(?d, ?l, ?f),
     DistanceBounds(d_min: ?d_min, d_max: ?_)

rule lower_bound:
  reachable_real(?l, ?f), position_distance(?d, ?l, ?f),
  DistanceBounds(d_min: ?d_min, d_max: ?_)
  -: gte(?d, ?d_min)
```

Both forms desugar to the same internal Horn clause. Direction is purely stylistic — backward (`:-`) reads naturally for derivation rules ("ancestor is true *if* parent and ancestor"); forward (`-:`) reads naturally for proof steps and forward-chaining specifications ("from these premises, *therefore* conclusion").

### Multi-head rules (conjunctive sugar)

A rule may carry **multiple head terms separated by `,`**. The semantics are conjunctive — every head term is a conclusion that follows from the body. The form is pure desugaring into N single-head Horn clauses sharing a body; no new solver machinery, no extension beyond the Horn fragment.

```anthill
-- multi-head, backward form:
rule completion:
  completed(?w),
  timestamp_recorded(?w, ?t)
    :- WorkItem(id: ?w, status: Done), finished_at(?w, ?t)

-- multi-head, forward form (mirror):
rule completion:
  WorkItem(id: ?w, status: Done), finished_at(?w, ?t)
    -: completed(?w),
       timestamp_recorded(?w, ?t)

-- desugars to (in either direction):
rule completion#1: completed(?w)
  :- WorkItem(id: ?w, status: Done), finished_at(?w, ?t)
rule completion#2: timestamp_recorded(?w, ?t)
  :- WorkItem(id: ?w, status: Done), finished_at(?w, ?t)
```

#### Comma semantics: `,` always means AND

Because the same `,` token appears on both sides of the arrow, its meaning must be unambiguous. **In Anthill, `,` always means logical conjunction**, on both sides of `:-` / `-:` and at every nesting level.

This is a **deliberate departure from classical clausal-form (CNF) convention**, where a clause `A1 ∨ A2 ∨ ¬B1 ∨ ¬B2` rewrites as `B1 ∧ B2 → A1 ∨ A2` and the same comma would be disjunction in head position, conjunction in body position. Classical readers should expect this departure to be jarring at first.

The departure is justified by language-wide consistency:
- Body comma is conjunction (existing behavior, unchanged).
- `requires` / `ensures` clauses use `,` for conjunction.
- `forall ?x: P, Q` uses `,` for conjunction.
- Nested goal terms in proposal 025 use `,` for conjunction.
- Tuple sorts and named-arg lists use `,` as a list separator, not as a logical operator at all.

Making head-`,` mean disjunction (the CNF reading) would be locally consistent with classical clausal form but globally inconsistent with the rest of the language. We pick global consistency.

#### Disjunction is reserved for a future proposal

`;` (semicolon) and `|` (pipe) are **reserved** in head position. The loader rejects any rule of the form `H1; H2 :- B` or `H1 | H2 :- B` with a clear message: "disjunctive heads are not supported in the current Horn fragment; if you need at-least-one-of semantics, file a proposal." This keeps the door open for a future ASP-style or disjunctive-Datalog extension without committing to one now.

#### Constraints on multi-head rules

- **No `⊥` in a multi-head list.** Denials have exactly one head, `⊥`. Mixing `⊥` with positive heads has no coherent reading and is rejected by the loader.
- **At least one head.** A bare arrow with empty head list (`:- B` / `B -:`) is a parse error. Use `rule ⊥ :- B` for denials.
- **Head functors all become scoped definitions.** Each `Hi` in a multi-head rule registers its functor as a named symbol in the enclosing scope, exactly as the single-head case does today (kernel-language.md §5.3, "Rule head functors are scoped definitions"). N heads ⇒ up to N new (or shared) functor definitions in the scope.
- **Citation under `using N`** cites the *group*: in SLD it provides each `Hi :- B` clause individually; in Z3 it injects `forall vars. body ⇒ (and H1...Hn)`, which is logically equivalent to N separate `body ⇒ Hi` lemmas.
- **Internal naming.** When the rule has a name `N` and N>1 heads, the desugared sub-rules are named `N#1`, `N#2`, …, `N#n` (positional). The user-visible citation handle is still `N`; the suffixed names are an implementation detail of the desugaring used for trust-report attribution.

### Nested implications (inside `forall` and goal terms)

Proposal 025 establishes nested `:-` / `-:` as goal-term forms inside the hereditary Harrop fragment, used in induction rules and proof-step contexts:

```anthill
-- existing 025 example, unchanged:
rule List.induction(?P)
  :- ?P(nil),
     (forall(?h, ?rest), ?P(?rest) -: ?P(cons(head: ?h, tail: ?rest)))

-- multi-premise body inside a nested implication:
rule Tree.induction(?P)
  :- (forall(?v), ?P(leaf(value: ?v))),
     (forall(?l, ?r), ?P(?l), ?P(?r) -: ?P(branch(left: ?l, right: ?r)))
```

Multi-head extends to nested implications by the same rule: the `,` after the arrow groups conclusions conjunctively. Logically `forall ?x. P(?x) ⇒ (Q(?x) ∧ R(?x))` ≡ `forall ?x. (P(?x) ⇒ Q(?x)) ∧ (P(?x) ⇒ R(?x))`, so the conjunctive desugaring is sound at any nesting level.

```anthill
-- nested multi-head conclusion (allowed):
(forall(?x), P(?x) -: Q(?x), R(?x))
-- = forall ?x. P(?x) ⇒ (Q(?x) ∧ R(?x))
-- = forall ?x. (P(?x) ⇒ Q(?x)) ∧ (P(?x) ⇒ R(?x))

-- nested multi-premise body with multi-head (also allowed):
(forall(?l, ?r), ?P(?l), ?P(?r) -: ?P(branch(?l, ?r)), well_formed(?l, ?r))
```

#### Precedence: `,` always binds tighter than `:-` / `-:`

To keep the parser unambiguous at every nesting level, the comma binds tighter than the arrows. Concretely:

```
P, Q :- R, S          ≡   (P, Q) :- (R, S)        -- multi-head, multi-premise
P -: Q, R             ≡   P -: (Q, R)             -- single-premise, multi-head
P, Q -: R             ≡   (P, Q) -: R             -- multi-premise, single-head
```

This matches Prolog's classical precedence (`,` at 1000, `:-` at 1200; lower priority binds tighter) and applies uniformly at top level and inside nested goal terms.

If an author wants to *break* a comma group across an arrow boundary — i.e. treat one comma as a goal-list separator rather than as head/body conjunction — they parenthesize the inner implication explicitly:

```anthill
-- two goals at the same level: a nested implication AND a separate conjunct
:- (P -: Q), R
-- = (P ⇒ Q) ∧ R
```

#### Comma in `forall` binder lists is a separate syntactic context

`forall(?x, ?y)` uses `,` as a *binder separator*, not as goal-list conjunction. The comma inside the `forall(...)` parens is parsed by the binder-list grammar, not the goal-list grammar. This is consistent with proposal 025's existing usage (`forall(?h, ?rest), ?P(?rest) -: ...`) and unchanged here.

The grammar distinguishes the two contexts by paren scoping: commas *inside* `forall(...)` are binder-list commas; commas *outside* (i.e. at the level of the goal list that follows the binder) are goal-list commas, and inside that goal list the `,`-vs-arrow precedence rule above applies.

### What goes away

- The `Conclusion` slot in the rule production. There is no separate conclusion term distinct from the head; every rule has exactly one conclusion (its head) and one body (possibly empty).
- The backend-dependent reading of the dual-arrow form. Today `H :- B -: C` means `H :- B` to SLD and `B ⇒ C` to Z3. After this proposal, every rule has one logical reading shared across all backends.
- The "label term" pattern in positive theorems. Authors currently place a synthetic term like `lower_bound_holds(?d)` in the head slot purely to expose quantified variables for citation; the real conclusion sits after `-:`. Under this proposal, the real conclusion *is* the head. The rule's **name** carries the citation handle — names are already the `using X` key.
- The citability carve-out. Every named rule is uniformly citable as `forall vars. body ⇒ head`, regardless of which direction the author chose.

### Naming the rule

The optional `name:` syntax is unchanged:

```anthill
rule lower_bound: gte(?d, ?d_min) :- ...
rule lower_bound: ... -: gte(?d, ?d_min)
```

The proposal does *not* change to brackets or sigils. With exactly one arrow per rule, the `name:` colon has no second separator on the line to compete with — the original confusion (`rule n :- y -: z` looking like a named rule) cannot arise because the dual-arrow form no longer exists.

### Z3 backend

The two encodings in kernel-language.md §5.3 collapse to one. For a rule with heads `H1, ..., Hn` and body `B1, ..., Bm`:

| Mode | SMT-LIB encoding |
| --- | --- |
| `proof X by z3(...)` | `(assert (and B1 ... Bm)); (assert (not (and H1 ... Hn))); (check-sat)` — `unsat` ⇒ theorem holds. Arrow direction (`:-` or `-:`) is irrelevant; the parser yields the same internal `(heads, body)` pair. |
| `proof Y using X by z3(...)` | `(assert (forall (<vars>) (=> (and B1 ... Bm) (and H1 ... Hn))))` injected into Y's preamble. |

The single-head case (n = 1) is the natural specialisation: `(and H1)` collapses to `H1`. The encoding is uniform across single- and multi-head rules.

Denial-shape rules (`Heads = ⊥`) keep their current semantics: head is `false`, so `(assert (not false))` is `(assert true)` — i.e., the check is just "body is unsat," exactly as today. The forward form `body -: ⊥` produces the same encoding.

### SLD / derivation backend

The SLD resolver consumes single-headed Horn clauses. Multi-head rules are **expanded at load time** into N separate single-head clauses sharing a body, indexed independently in the discrimination tree. Surface direction (`:-` vs `-:`) is erased before indexing. From the resolver's perspective nothing changes — it never sees a multi-head clause.

## Migration

The dual-arrow form `rule [N:] H :- B -: C` does **not** correspond to a single Horn clause — under the current spec, SLD reads it as `H :- B` and Z3 reads it as `B ⇒ C`. Migration is therefore not a mechanical rewrite to "one canonical Horn form"; it depends on what `H` and `C` are doing at each call site.

### Migration cases

**Case 1 — `H` is a synthetic label term, never queried elsewhere.**
The author invented a predicate name solely to expose the quantified variables and give `using` something to cite. No other rule defines, asserts, or queries that predicate. Migration: **drop `H`; promote `C` to head.** The rule's name carries the citation handle.

```anthill
-- before
rule lower_bound_holds(?d)
  :- reachable_real(?l, ?f), position_distance(?d, ?l, ?f),
     DistanceBounds(d_min: ?d_min, d_max: ?_)
  -: gte(?d, ?d_min)

-- after
rule lower_bound: gte(?d, ?d_min)
  :- reachable_real(?l, ?f), position_distance(?d, ?l, ?f),
     DistanceBounds(d_min: ?d_min, d_max: ?_)
```

**Case 2 — `H` is a real SLD-queryable predicate AND `C` is a separate Z3 obligation.**
Two distinct claims share one body. Migration: **split into two rules**, both Horn.

```anthill
rule [N_h:] H :- B          -- the SLD-derivable fact
rule [N_c:] C :- B          -- the Z3-checkable arithmetic obligation
```

The two rules can cite each other if needed. If `H` and `C` are linked (`H` is true exactly when `C` is true), add a bridging rule `rule H :- C` or `rule C :- H` to capture the equivalence.

**Case 3 — `H` and `C` are equivalent surface forms of the same claim.**
For example, `H = is_bounded(?d)` (logical-predicate style) and `C = gte(?d, ?d_min)` (arithmetic style). Migration: **pick the form Z3 actually consumes** (typically `C`); drop `H`. If existing SLD code queried the predicate form, add a one-line bridging rule:

```anthill
rule [N:] gte(?d, ?d_min) :- B
rule is_bounded(?d) :- gte(?d, ?d_min)         -- bridge, only if SLD callers query is_bounded
```

### Spec text

kernel-language.md §5.3 rewritten: drop the `Conclusion` production, drop the "Citability" paragraph, collapse the two Z3 encoding rows.

### Affected call sites

Top-level rules currently using the dual-arrow form (full audit before implementation; preliminary list):

- `docs/kernel-language.md` §5.3 example (`lower_bound_holds`)
- `docs/proposals/030-theorem-registry.md` (Z3-citable rule examples)
- `docs/proposals/031-structured-proofs.md` (inner-rule step shape)
- `examples/webots-modelling/lf1/` — `step_distance_lemma` and the decomposed sub-lemmas
- Any in-tree `.anthill` file in `stdlib/` or `anthill-todo/` that uses `-:` on a rule (TBD via grep audit)

Nested `-:` inside `forall` and as goal terms (proposal 025 / 023 usage) is **untouched** — those uses were already symmetric.

## Implementation notes

### Tree-sitter grammar

Current rule production accepts an optional `:-` body and an optional `-:` conclusion as independent suffixes. Replace with a choice:

```js
rule_decl: $ => seq(
  'rule',
  optional($.rule_name),
  choice(
    seq($.heads, ':-', $.rule_body),
    seq($.rule_body, '-:', $.heads),
    $.heads,                         // fact (single head, no body)
  ),
  optional($.meta_clause),
),

heads: $ => choice(
  '⊥',
  sep1($.term, ','),                 // one or more head terms, conjunctive
),
```

The two arrow alternatives need different head/body slot ordering, but both produce the same downstream IR shape `(heads: Vec<Term>, body: Vec<Term>)`. Note that `heads` and `rule_body` both use `,` as a separator — the grammar treats them symmetrically, and the loader applies the conjunctive semantics on both sides. The `;` token is *not* admitted in `heads` to keep the disjunctive-extension door reserved.

### Parser IR (rustland + scaland)

- `parse::ir::RuleDecl` is updated to `heads: SmallVec<[Term; 1]>` and `body: Vec<Term>` (smallvec inline-1 because the single-head case dominates).
- The converter normalises both surface directions into the same IR. Source span for the arrow token is preserved for diagnostics.
- Remove the `conclusion: Option<Vec<Term>>` field (currently used for the `-:` slot).
- A separate flag (or sentinel head term) marks denial-shape rules where `heads = [⊥]`.

### Loader

- Remove the conclusion-vs-head split logic in `kb::load`.
- **Multi-head desugaring**: when `heads.len() > 1`, the loader emits N single-head Horn clauses sharing the body. Each clause registers its head functor as a scoped definition. The user-visible name `N` is preserved as the citation-handle key; internal sub-rules carry positional suffixes `N#1`..`N#n` for trust-report attribution.
- Z3 backend: emit the unified `(forall vars. body ⇒ (and H1...Hn))` encoding. Single-head rules are the n=1 specialisation. Update the structured-proof step-checker (proposal 031) to consume `(heads, body)` instead of `(head, body, conclusion)`.
- SLD: indexes the desugared single-head clauses; resolver code is unchanged.

### Diagnostics

- Parse error: any rule containing both `:-` and `-:` (the grammar production no longer admits this; emit a clear migration message: "rules may use `:-` or `-:` but not both; the conclusion is the head term").
- Parse/load error: `;` or `|` in head position. Message: "disjunctive heads (`;` / `|`) are reserved for a future proposal; use multiple `,`-separated heads for conjunctive multi-head, or split into separate rules."
- Load error: `⊥` mixed with positive heads in a multi-head list. Message: "⊥ (denial) cannot be combined with other heads; denials have exactly one head."
- Load error: `rule X` (bare head) when `X` is `⊥`. Message: "denials require a body; write `rule ⊥ :- <body>`."

## Open questions

1. **Should `-:` remain available at top level, or restrict it to nested goals?** Keeping it preserves the proposal's "uniform symmetry" pitch and supports forward-style proof-step authoring (lf1, proposal 031). The cost is two surface forms for one operator. The proposal *recommends keeping both*; readability gain in proof-step contexts is worth the small surface-area cost.

2. **Interaction with proposal 031's structured proofs.** Inner `rule h_i:` steps in a proof body currently use the dual-arrow form. Under this proposal, they collapse the same way: the step's head is the conclusion, and the step body holds the premises. Multi-head steps are also admissible (a step concludes multiple sub-claims at once). Proposal 031's example syntax block needs updating.

3. **Multi-head naming under `using`.** When a rule with name `N` has multiple heads, `using N` cites the whole group. Open question: do we also want per-head citation (`using N#1`, `using N#2`) for cases where a downstream proof only needs one of the conclusions? Recommendation: not initially — keep the user-visible API at the group level; the `#i` suffixes are an internal attribution detail. Revisit if real call sites demand it.

4. **Multi-head citability across SLD vs Z3.** A multi-head rule fed to Z3 produces a single `forall body ⇒ (and H1...Hn)` lemma, while SLD treats it as N separate clauses. For most uses the difference is invisible (Z3 conjunction is logically equivalent to N separate implications). Edge case: if a downstream proof cites `N` and only needs `H2`, the Z3 encoding still injects the full conjunction — slightly more work for the solver but no soundness issue. Worth measuring on real workloads before optimizing.

5. **Nested multi-head adoption.** Allowing multi-head conclusions inside `forall` and goal terms is sound (logically equivalent to the conjunctive expansion) but expands the surface area of the hereditary Harrop fragment Anthill exposes. λProlog and similar systems typically restrict nested implications to single conclusions for readability; Anthill chooses to allow nested multi-head for symmetry with the top-level form. If real proofs find this unhelpful (e.g. nested multi-head conclusions are rare in practice and harm readability when they appear), we can restrict nested implications to single-head later — backward-compatible since current call sites are all single-head.
