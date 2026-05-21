# The `[simp]` rewriting engine — implementation design (rustland)

## Status: Implementation design — for review (2026-05-21)

## Relates to

- `docs/design/simp-rewrite-brainstorm.md` — **rationale**: why method dispatch (and folding, and AD) are `[simp]` rules; the tooling/delegation/DSL story; the worked examples. Read it for *why*.
- `docs/proposals/043-simp-rewrite.md` — the proposal (semantics) this doc implements: the `[simp]` rewriting engine, with dot dispatch as its first client. Read it for *what the feature is*.
- **This doc** — **how the engine is built** in rustland. The engine is the subject; dot dispatch, `min`-folding, and AD are *clients*. It corrects two substrate claims the brainstorm/proposal got wrong.
- Substrate: `docs/design/occurrence-as-value-type.md` (`NodeOccurrence`, `Value::Node`), `docs/design/operation-call-model.md` (typer-then-`req_insertion` split), `docs/design/interpreter-ir.md` (downstream consumer; equation-defined ops).
- WI-139 (delivered) — `[simp]`/`[unfold]`/`[hint]` attributes (`anthill-core/tests/include/equational_attr_test.rs`).
- Proposal 026.1 Q2 — `TermView` (unification over `TermId` *or* `Value`).

## What this document is / isn't

**Is:** the rustland plan for a general engine that fires `[simp]` equational rules over expression content. Dot dispatch is its first and simplest client; `min`-folding and AD are later clients on the same engine. Concrete: substrate anchors, the data-flow change, the build order.

**Isn't:** the language design of dot syntax (→ proposal 043) or the rationale (→ brainstorm). One thing this doc *does* surface that the others under-state: the engine's **reduction strategy, termination policy, and firing specificity are semantics**, not mere implementation detail (§6) — they may warrant their own proposal.

**The framing correction this doc exists to make:** proposal 043 presents "method dispatch via simp rewriting" and scopes "the engine" to exactly what the two dot rules need (type-level guards, structural termination). But the general `[simp]`-rule-firing engine is the **foundation**, and it is already *half-built* — at the term level, in the resolver. Centering the design on the engine (rather than on dot) makes that foundation explicit and makes phase-agreement (§4.4) structural instead of an afterthought.

---

## 1. The engine, in one paragraph

A `[simp]` rule is an equation `lhs = rhs` (head `eq(LHS, RHS)`, `is_equation`, `mod.rs:1778`) tagged so it is **directionally rewritable** (`meta_has_flag(.., "simp")`, `load.rs:2682`; WI-139 keeps it indexed in `by_functor`). The engine **fires such rules LHS→RHS to normal form**. There are two firing sites — the SLD resolver (over runtime `Term`s) and the typer (over expression-position `NodeOccurrence`s during type-checking) — and the brainstorm's whole correctness story (open Q4/Q20) is that *the same rule must fire identically in both*. So the engine is properly understood as **one rule-matching/strategy core, run in two phases** (resolver and typer), not as a dot-dispatch feature.

---

## 2. Substrate audit — what exists, what's missing

### 2.1 Exists (more than 043 credits)

| Capability | Anchor | Note |
|---|---|---|
| **Unified read-side view** over `TermId` *and* `Value` | `TermView` trait, `term_view.rs:55`; `impl … for TermIdView` (80), `for Value` (134) | The matcher is **not** term-only |
| Structural matching generic over the view | `match_view<V: TermView>` (`mod.rs:1379`); discrim `query_*<V: TermView>` (`discrim.rs:427/437/455`) | Works against a `Value` target today |
| **Resolver-phase rewriter (Term)** | `apply_eq_rules` (`resolve.rs:1266`): innermost, LHS→RHS, to-fixpoint, fuel-bounded (100, `simplify` 1258) | This *is* a general simp engine — at term level |
| `[simp]`/`[unfold]` gate `by_functor` | `meta_has_flag` (`load.rs:2682`); `unindex_functor` for untagged equations (~1250) | Rules reachable as data |
| Synthesized-occurrence substrate | `synthesized_expr` (`node_occurrence.rs:184`): `origin: Synthesized{from,by}`, span inherited, `classification: None` | RHS provenance channel |
| `PassId` (symbol-backed) | `occurrence.rs:19` | Pass tag — no enum edit |
| Field registry + `field_access` builtin | `entity_fields`/`entity_field_types` (`mod.rs:208/254`), `is_free_standing_entity` (2259); builtin `resolve.rs:1975`, reg `mod.rs:2308` | Backs the `dot_field` client guards |
| `Value::Node(Rc<NodeOccurrence>)` — reflect Expr as a value | `value.rs:107` | The occurrence-as-value bridge |

### 2.2 Missing (this is the foundation work)

1. **`Value::Node` is opaque to the matcher.** `impl TermView for Value` maps `Value::Node(_) → ViewHead::Opaque` (`term_view.rs:165`), lumped with closures/streams. So a rule LHS `dot_apply(?x, ?name, ?args)` **cannot match** an Expr occurrence — `head`/`pos_arg`/`named_arg` report opaque. The brainstorm's premise "pattern variables bind to reflect `Expr`/`Node` values; rules match `dot_apply(?x,…)` against them" is **assumed, not implemented**. Making `Value::Node` *structural* is the single enabling change.
   - Concrete wrinkle: `ViewItem` (`term_view.rs:46`) is `Copy` with `Term(TermId) | Value(&'a Value)`. An occurrence's children are `Rc<NodeOccurrence>`, not `&Value`, so exposing them needs a new child shape (e.g. `ViewItem::Node(&'a NodeOccurrence)`), which ripples through the discrim walker. Non-trivial but mechanical.
2. **No build side.** `TermView` is read-only (it's the *target* side of unification). Rewriting must *construct* an RHS. `apply_eq_rules` builds `TermId`s (`self.alloc(Term::Fn …)`, `resolve.rs:1292`) — cheap, hash-consed. There is no equivalent that constructs an **occurrence** RHS (`synthesized_expr`, span-preserving). And `Value::Node` can't be lowered to a `TermId` either (`execute.rs:229`, `UnsupportedVariant("Node")`), so "rewrite as term, re-materialize" would silently drop spans/provenance.
3. **The typer is annotate-only over an immutable tree.** `op_bodies` is written once at load (`load.rs:5451`); type-checking only mutates two `RefCell`s (`classification`, `resolved_type_args`) on existing nodes. Child slots are bare `Vec<Rc<…>>` (no `RefCell`) and `Expr` is `!Clone` (`node_occurrence.rs:309`). So the typer phase cannot "replace a node" in place — it must **produce a new subtree and write it back** (§5.1).
4. **`typeof` is not exposed to guards.** The dispatch guard needs `typeof(receiver)`; the resolver has no `typeof` builtin and no access to the typer's `TypeResult`s (§5.4). Plus `typeof`/`find_operation_on_sort` don't exist as callable surface.

---

## 3. Two corrections to the brainstorm/proposal

- **`typeof(?x)` does NOT read `classification`** (brainstorm line ~174). `classification` holds a `CallClass` (`typing.rs:2403`) — dispatch-rewrite info (`PinNow`/`ConcreteApplyWithin`/`DeferToRequirement`), set **only** on spec-op call sites; a bare receiver never gets one. The type lives in `TypeResult.ty` and is discarded after checking. The reflect `type_of(occ, type)` entity (`reflect.anthill:421`) is an *unasserted fact shape*, not a builtin. See §5.4 for where the receiver type actually comes from.
- **The matcher is not term-only, but it stops at `Value::Node`.** §2.2(1). The brainstorm treats Expr-occurrence matching as available; it is the specific corner that is opaque today.

---

## 4. Architecture: one rewriter, two phases

One rewrite relation — *find a subterm matching a `[simp]` rule's LHS, check the guard, replace with the RHS instance* — run in two phases that already exist and differ in **one** thing: the representation each phase holds.

```
                       one rewrite relation
        ┌──────────────────────┴───────────────────────┐
  resolver phase (exists)                        typer phase (new)
  apply_eq_rules: Term → Term                    rewrites NodeOccurrence op bodies
  runtime / proof                                compile-time
        └──── shared: by_functor rules · TermView matcher ·
              guard eval · reduction strategy + termination (§6) ────┘
  differ ONLY in result construction:  Term (alloc)   |  NodeOccurrence (synthesized_expr)
  spans:           term_spans side-table (mod.rs:237) |  inline + Synthesized origin
```

Why the representations differ: each phase rewrites **what it already holds** — the resolver its `Term` goals/facts, the typer the `NodeOccurrence` op bodies that req_insertion/eval/IR also consume. **Spans are not the differentiator** — terms carry them in `term_spans: HashMap<TermId, SourceSpan>` / `functor_spans` (`mod.rs:237/243`; `occurrence.rs:3`), occurrences inline (plus `Synthesized` provenance). Nor is hash-consing — that is the `TermStore`, not the rewriter. The only representation-specific step is **building the rewritten result**; everything else (rule lookup, matching, guards, strategy) is shared.

### 4.1 The matcher already spans both representations

`TermView` (`term_view.rs:55`) matches a rule-LHS pattern (a `TermId`) against a target that is **either** a `Term` **or** a `Value` (`impl … for Value`, line 134) — it is not term-specific. The one gap: `Value::Node` is `ViewHead::Opaque` today (`term_view.rs:165`). Make it structural — `head` → the inner `Expr`'s functor (`Expr::Apply{functor}` → `Functor{Some(functor)}`, `Expr::DotApply` → a `dot_apply` symbol, …); `pos_arg`/`named_arg` → child occurrences (via a new `ViewItem::Node`, §2.2(1)) — and `match_view(rule_lhs, &Value::Node(occ))` binds pattern vars to child occurrences with **no second matcher**.

### 4.2 The resolver phase (exists)

`apply_eq_rules` (`resolve.rs:1266`): rewrites `Term`s during SLD resolution. Stays as-is; it already sets the reference strategy (innermost) and termination (fuel 100) the typer phase must match.

### 4.3 The typer phase (new) — and the simplest thing it does

A bottom-up walk over op-body `NodeOccurrence` trees that reuses the matcher (§4.1) + rule lookup + strategy, builds `synthesized_expr` RHSs, and writes the result back via `set_op_body_node` (§5). Its simplest use needs **no dot, no `typeof`, no value folding** — a guard-free structural rewrite of the user's own functors:

```
rule add_zero: add(?x, 0) = ?x   [simp]      -- fires in the typer phase:
operation residual(v: Vec, k: Int) -> Vec    --   add(mul(v,k), mul(v,0))  →  mul(v,k)
  add(mul(v, k), mul(v, 0))                   -- (with mul_zero / add_zero, all guard-free)
```

Dot dispatch (§7.1) is a *more involved* client of the same walk — it adds a type-directed guard. Showing the guard-free case first is deliberate: the engine is the feature; `dot_apply` is one functor it happens to rewrite.

### 4.4 Phase agreement

A `[simp]` rule fires in both phases and must mean the same thing. Reusing the matcher + strategy + termination (rather than reimplementing the typer phase beside `apply_eq_rules`) makes that **structural**, not a test-and-pray obligation — the main reason to build the typer phase *on* the existing matcher. (For pure dispatch rules the resolver phase is vacuous — no `dot_apply` terms exist at runtime — so agreement bites only for value rules like `min`.)

---

## 5. The typer phase in detail

### 5.1 The annotate-only constraint → tree production

Per §2.2(3), getting `dot_apply` (and any rewritten redex) out of the stored body requires the pass to be **tree-producing**: synthesize replacements, rebuild ancestors (hand-written per-variant reconstruction — `Expr: !Clone`; `Rc::clone` the unchanged children; a new `map_children` helper dual to `drain_expr_children`, `node_occurrence.rs:100`), and write the new root back. This is the work 043 under-describes as "hook firing into the work loop." Note this is *not* how `req_insertion` works — that pass annotates `CallClass` and records a diagnostic-only `TermId→TermId` side table (`req_insertion.rs:14–20`, `dispatch_rewrites` `mod.rs:278`); it never rewrites the tree. Front-end B is the first genuine occurrence-tree rewriter.

### 5.2 Placement in the load pipeline

`load_all` (`load.rs:1366`) → `type_check_sorts` (`1485`) → `req_insertion::run` (`1492`). Front-end B runs **per op body, interleaved with / just before** the op-body type-check (`typing.rs:5902`), writing the rewritten (redex-free) tree back **before** `req_insertion`. Everything downstream — the final type-check, `req_insertion`, eval, IR — then sees a tree with no `dot_apply` and no un-fired `[simp]` redexes, and is unchanged.

### 5.3 The driver

Per op body, with the **same `TypingEnv`** the op-body driver builds (params bound, enclosing sort set; mirror `typing.rs:5884–5896`):

```
fn rewrite(kb, env, occ) -> Rc<NodeOccurrence>:
  1. Rewrite children bottom-up → possibly-new child Rcs (map_children).
  2. Rebuild this node if any child changed.
  3. Query by_functor for [simp] equations whose LHS functor matches this node
     (per WI-139 indexing) — this is the *general* step, not dot-specific.
  4. For each candidate (firing order per §6): match LHS against this node as a
     Value::Node target via match_view (§4.1); evaluate the guard (§5.4); on success
     reify the RHS into a fresh synthesized_expr(.., from=occ, by=SIMP_PASS).
  5. Recursively rewrite the synthesized RHS (chains, delegation re-emit, AD cascade),
     bounded by fuel (§6); return it. If nothing fires, return the rebuilt node.
```

For the dot client this terminates structurally (RHS has no `dot_apply`); for value/AD clients fuel bounds it.

### 5.4 Guard / `typeof` boundary

The dispatch guard `find_operation_on_sort(typeof(?x), ?name, ?op)` needs `typeof(receiver)`. The receiver subtree is already rewritten (bottom-up) and dot-free, so its type is `type_check_node(kb, env, &receiver, None).ty` (`typing.rs:904`; reentrancy holds — fresh stacks, no call-scoped KB state, §A). **Read it from the `TypeResult`, never from `classification`** (§3). Two ways to feed it to the guard:

- **(i) Engine-evaluated typed guards (recommended for Part 1).** The pass holds `recv_ty`; it evaluates the type-level predicates (`is_entity`, `has_field`, `find_operation_on_sort`) directly against the KB. The `[simp]` rules still live in the KB as data (LSP inverse queries, brainstorm §LSP), but *firing* uses the typed context the resolver lacks.
- **(ii) Assert `type_of` facts.** Typing asserts `reflect.type_of(occ, T)` (`reflect.anthill:421`) so an SLD `typeof` builtin can answer, and the whole guard runs in the resolver. More uniform, enables arbitrary user guards; turns the discarded `TypeResult.ty` into persisted state.

Recommend **(i)** until non-prelude `[simp]` guards with arbitrary `typeof` appear (DSL dispatch / Part 2).

---

## 6. Reduction strategy, termination, firing — the semantic decisions

These belong to the **shared core** (so both phases agree, §4.4), and they are semantics:

- **Reduction strategy: leftmost-innermost / bottom-up.** Forced by type-directed dispatch (outer rule needs `typeof` of the reduced inner term) and matches both the typer's walk and `apply_eq_rules`'s innermost order. Consequence: strict, no lazy discard (brainstorm Q20).
- **Termination.** Dot client: structural (no machinery). General/value/AD clients: fuel (port `apply_eq_rules`'s bound) + a `Synthesized.from` ancestor-loop check. Commutative/AC laws (`min_comm`) must stay **bare** (non-`[simp]`) or the phase loops (brainstorm Q3/Q18). Open: should the loader *reject* a `[simp]` tag on a detectably-non-terminating rule (LHS≡RHS permuted)?
- **Firing specificity** when several rules match one redex (`diff_scale` vs `diff_mul`): most-specific-LHS-first / textual / general-then-cleanup (brainstorm Q16). Must be one documented policy in the core.

Because these are observable semantics shared across compile-time and runtime, a sibling proposal (not just this impl doc) may be the right home for ratifying them. Flag for decision.

---

## 7. Clients

### 7.1 Client A — dot dispatch (proposal 043 §6)

The minimal client: type-level guards only, structural termination.

- **`Expr::DotApply { receiver, name, pos_args, named_args }`** node (`node_occurrence.rs`, sibling to `Apply`); wire into `drain_expr_children`/`for_each_child`; add reflect entity `dot_apply(receiver, name, args)`.
- **Converter** (`parse/convert.rs`): emit a `dot_apply` term for **value-receiver** dot forms — both `?x.field` (currently `BuildFrame::FieldAccess`, `convert.rs:1020`, keeps the receiver) and `?x.method(args)` (currently flattened via `collect_field_access_segments`, `convert.rs:342`, which has **no `variable` branch** → silently drops the receiver: the actual gap). Keep `Foo.bar` / `Map[K=…].empty()` flattening (sort/namespace receivers). Add the `dot_apply` functor → `Expr::DotApply` case in `materialize_from_handle` (`node_occurrence.rs`; called `load.rs:5450`).
- **`find_operation_on_sort(sort, name) -> Option<qualified_op>`**: tier-1 (in-body ops, no import) composable from `operations_of_sort` (`op_requirements.rs:177`, walks `SortInfo.operations`) + `find_operation_in_scope` (`load.rs:2814`); tier-2 (extension ops, import-scoped) is new — no first-param index exists.
- **Prelude rules** (KB data; firing engine-driven per §5.4(i)):
  - `dot_field: dot_apply(?x, ?name, []) = field_access(?x, ?name) :- is_entity(typeof(?x)), has_field(typeof(?x), ?name) [simp]` — reaches the existing `field_access` builtin unchanged.
  - `default_dot: dot_apply(?x, ?name, ?args) = ?op(?x, ?args) :- find_operation_on_sort(typeof(?x), ?name, ?op) [simp]`.
  - Guard-exclusive; field-first on collision (optional load-time lint).
- **Errors**: neither fires → "no field or method `name` on sort `S`" at `occ.span`, via the `Synthesized` chain.
- **Type params & `requires` ride existing machinery — no dot-specific path.** The rewrite emits a plain `apply(op, [receiver, …args])` with empty `type_args`; by the time anything downstream sees it, it is indistinguishable from a written call. Type parameters are inferred by the normal op-body type-check (WI-270 expected-type threading; WI-272 `resolved_type_args`) — `?xs.map(?f)` pins `map`'s `T` through the *receiver* (first arg: `xs: List[Int]` ⇒ `T=Int`), `?f` pins `U`. `requires` clauses are elaborated by `req_insertion::run`, which runs **after** the rewrite (§5.2) and reads `CallClass` off the now-classified synthesized apply — so `?a.min(?b)` (`Ord[T]`) and `?l.contains(?e)` (`Eq[T]`) dispatch through the existing PinNow / ConcreteApplyWithin / DeferToRequirement path (`typing.rs:2403`), and an unsatisfied `requires` is a genuine "sort `S` lacks `Ord`/`Eq`" error at the dot-call span. **Ordering requirement:** the rewrite must complete before the final op-body type-check + `req_insertion` — it does (§5.2). **Open decision (D6):** requirement-aware `find_operation_on_sort` (early/precise rejection, overload disambiguation) vs name+sort resolution with `requires` checked on the produced apply (lean: the latter).

### 7.2 Client B — value-conditional simp (`min`) [sketch]

Adds the `constant_fold(?const, ?source)` builtin (the only occurrence-aware value bridge: compile-time fold-or-STUCK, runtime identity), STUCK→residualize handling, and fuel termination. `min(3,5)` folds to `3`; `min(?age, ?thr)` residualizes to a runtime call evaluated by the *same* rules via the resolver phase. Reinforces §4.4: the two phases must share the constant/non-constant boundary.

### 7.3 Client C — automatic differentiation (`diff`) [sketch]

`diff` is a plain operation over `Expr`, defined by `[simp]` *rules* (the rules carry the tag, the op doesn't). Recursive rewriting to fixpoint; needs `[unfold]` at the typer phase to inline bodies before pattern-matching (brainstorm Q15) and a firing-specificity policy (§6). Pure structural rewriting — never STUCKs.

---

## 8. Interactions (unaffected by construction)

Because the typer phase writes the rewritten, redex-free tree back **before** them: `req_insertion::run` (`req_insertion.rs:41`) collects `CallClass` over `Expr::Apply` on the rewritten tree as today; eval / interpreter IR never see `dot_apply` and lower `apply(List.map, …)` like any call. The pre-existing "equation-defined op has no body to lower" concern (`min` residualized) is the IR doc's open question (`interpreter-ir.md:190`), not new here.

## 9. Test plan

1. `TermView for Value::Node`: a rule LHS matches against a `Value::Node` Expr occurrence (the §2.2(1) unit gap).
2. Converter: `?x.field` and `?x.method(args)` → `Expr::DotApply` with receiver intact; `Foo.bar` still flattens (byte-identical IR).
3. `find_operation_on_sort`: tier-1 `?l.map(?f)` resolves `List.map` with no import; tier-2 only when imported.
4. Driver: `xs.map(f).filter(p)` chains; `p.x` → `field_access`; no-match error at source span; rewritten body type-checks and runs identically to a hand-written `apply(...)`.
5. Phase agreement: a value rule (`min`) gives the same result via the resolver phase (runtime `Term`) and the typer phase (compile-time occurrence).

## 10. Decisions to confirm

- **D1 — engine vs one-off.** Build the typer phase by reusing the shared matcher (extend `TermView` to `Node` + add the occurrence build side), *not* as a dot-special-cased pass. (This doc's recommendation; the user's steer.)
- **D2 — guard evaluation** §5.4: (i) engine-evaluated for Part 1, defer (ii) `type_of` facts.
- **D3 — strategy/termination/specificity** §6: ratify in a sibling proposal or here?
- **D4 — `ViewItem::Node` representation** §2.2(1): new `ViewItem` variant vs alternative occurrence-matcher.
- **D5 — tier-2 import semantics/timing** (043 open-Q10a).
- **D6 — requirement-aware dispatch?** §7.1: should `find_operation_on_sort` consider `requires` satisfiability (early/precise errors, overload disambiguation), or resolve by name+sort and let the produced apply's `requires` check report downstream (lean)?

## 11. Build order

1. **Decide D1–D3** (this replaces 043's "confirm interposition point" spike).
2. **Shared core, read side:** `TermView for Value::Node` structural + `ViewItem::Node` (§4.1, §2.2(1)).
3. **Shared core, build side + strategy/termination** factored so the resolver phase's behavior is unchanged (§4.2, §6).
4. **Front-end B driver:** bottom-up, tree-producing, write-back, provenance (§5).
5. **Dot client substrate:** `Expr::DotApply` + converter + `materialize_from_handle` + `find_operation_on_sort` tier-1 (§7.1).
6. **Prelude `default_dot`/`dot_field`** + engine-evaluated guards (§5.4(i)); diagnostics + collision lint.
7. **Tests** (§9). Then tier-2, and clients B/C separately.

---

## Appendix A — reentrancy (holds)

`type_check_node` (`typing.rs:904`) allocates fresh local `work`/`results` per call (910–911), takes `occ` by reference, and is already re-entered recursively by the `check_*` helpers (`typing.rs:3863–3865, 3906`). The op-body driver builds a fresh `TypingEnv` per op (`5884–5896`); no call-scoped state lives on `kb` across the walk. So the typer phase may call `type_check_node` on any subtree to obtain `recv_ty`. Reentrancy was 043's stated first concern; it is real but *not* the binding constraint — that is the annotate-only/tree-production change (§2.2(3), §5.1).
