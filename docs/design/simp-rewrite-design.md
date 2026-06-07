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

**The framing correction this doc exists to make:** the general
`[simp]`-rule-firing engine is the **foundation** — dot is one client. And the
engine is **type-directed**, integrated with the typer: rules are defined over
expressions (so firing is compile-time), and matching/guards consult the
operand's sort (`min_sort`, `requires`). The earlier "type-independent engine,
run in two phases, with dot bolted on" framing was wrong (see
`simp-dot-finding.md`); centering on a *type-directed* engine over expressions
is what this doc now does.

---

## 1. The engine, in one paragraph

A `[simp]` rule is an equation `lhs = rhs` (head `eq(LHS, RHS)`) tagged
**directionally rewritable** (`meta_has_flag(.., "simp")`, `load.rs:2682`). Its
guard is its explicit `:- …` **plus the `requires` of its enclosing sort** (a
rule in a sort inherits that sort's `requires` implicitly) — so it is generally
*not* body-less, and `is_equation`'s empty-body gate must be relaxed to index
guarded rules. The engine **fires such rules LHS→RHS to normal form over
expressions**.

A rule is defined over **expressions**, so firing it is a **compile-time**
activity — not a clock, but the *mode* of holding an expression (a
`NodeOccurrence` / a term being matched, **not** an evaluated value), whose type
is therefore known. One rewriter runs wherever an expression is held, all at
compile time: the **typer** over op-body occurrences, and the **logical engine**
(the SLD/equational engine — `apply_eq_rules`) **when it resolves rules at
compile time** (also over expressions).

The logical engine is **general** — it *also* runs at **runtime**, where the
goals it resolves are **not** expressions (evaluated values, or something else
entirely); simp does **not** apply there. So the domain is "compile-time, over
expressions," not "SLD" as such — the only real boundary is **expression vs
value**. Because an expression carries its type, firing is **type-directed**:
matching is subsort-aware and guards consult `min_sort` + `requires` (§6).

(Terminology: **"logical engine"** = the SLD/equational resolution engine — to
avoid confusion with the pre-type **name/scope resolver**, which runs before
type-checking.)

---

## 2. Substrate audit — what exists, what's missing

### 2.1 Exists (more than 043 credits)

| Capability | Anchor | Note |
|---|---|---|
| **Unified read-side view** over `TermId` *and* `Value` | `TermView` trait, `term_view.rs:55`; `impl … for TermIdView` (80), `for Value` (134) | The matcher is **not** term-only |
| Structural matching generic over the view | `match_view<V: TermView>` (`mod.rs:1379`); discrim `query_*<V: TermView>` (`discrim.rs:427/437/455`) | Works against a `Value` target today |
| **Logical-engine rewriter (Term)** | `apply_eq_rules` (`resolve.rs:1266`): innermost, LHS→RHS, to-fixpoint, fuel-bounded (100, `simplify` 1258) | This *is* a general simp engine — at term level (the logical engine, used over expressions when resolving rules) |
| `[simp]`/`[unfold]` gate `by_functor` | `meta_has_flag` (`load.rs:2682`); `unindex_functor` for untagged equations (~1250) | Rules reachable as data |
| Synthesized-occurrence substrate | `synthesized_expr` (`node_occurrence.rs:184`): `origin: Synthesized{from,by}`, span inherited, `classification: None` | RHS provenance channel |
| `PassId` (symbol-backed) | `occurrence.rs:19` | Pass tag — no enum edit |
| Field registry + `field_access` builtin | `entity_fields`/`entity_field_types` (`mod.rs:208/254`), `is_free_standing_entity` (2259); builtin `resolve.rs:1975`, reg `mod.rs:2308` | Backs the `dot_field` client guards |
| `Value::Node(Rc<NodeOccurrence>)` — reflect Expr as a value | `value.rs:107` | The occurrence-as-value bridge |

### 2.2 What the 2026-05-21 audit listed as missing — and what's *actually* left

*Most of this landed since the audit.* (1) occurrence matching and (2) the
occurrence build side are **done** (WI-276/277); (3) is a standing constraint
the build side now satisfies. The genuinely-remaining foundation work is **(4)
typed occurrences** (so `min_sort` is a lookup), plus the firing logic on top:
guard-aware + subsort-aware firing (WI-283) and the `DotApply` matcher arm
(WI-279).

1. **`Value::Node` matching — mostly DONE (WI-276/277), `DotApply` arm remains.**
   *Update:* `occ_head`/`occ_pos_child` already make `Value::Node` **structural**
   for `Apply`/`Constructor`/`Const`/`Ref`/`Ident`/`Var`, with `ViewItem::Node`
   for child occurrences — so a rule LHS matches an Apply/Constructor occurrence
   today. The "single enabling change" framing of the 2026-05-21 audit is stale.
   What's left: `Expr::DotApply` (and control-flow forms) still hit
   `_ => ViewHead::Opaque`; giving `DotApply` an `occ_head` arm (head = the
   `dot_apply` functor, children = receiver/name/args) is **dot-client
   substrate** (WI-279), not engine-enabling work. (It was added and reverted
   with the WI-278 (c)/(e) increment; reinstate it under WI-279.)
2. **Occurrence build side — DONE (WI-277).** *Update:* `simp_rewrite.rs` already
   constructs an occurrence RHS — `substitute_to_occurrence` builds it as a
   `synthesized_expr` (span + `Synthesized` provenance preserved), and
   `reassemble`/`subst_visit` + the iterative `rewrite` walk rebuild ancestors
   and write the new tree back. The 2026-05-21 concern ("no occurrence RHS
   builder; rewrite-as-term-then-re-materialize would drop spans") is resolved —
   the build side is occurrence-native. What remains is **not** the build side
   but the *firing logic*: making firing **guard-aware + subsort-aware** and
   converging it with `apply_eq_rules` (WI-283), and the `DotApply` matcher arm
   (WI-279). (`apply_eq_rules` still builds `TermId`s for the logical-engine call
   site — fine; that's the per-representation result step, §4.)
3. **Occurrence trees are immutable; rewrites swap the root, never mutate in place.** `op_bodies` is populated at load (`load.rs:5540`) and thereafter only **whole-tree replaced** via `set_op_body_node` (e.g. `simp_rewrite::run`); a node is never mutated in place. Type-checking only writes the two per-node `RefCell`s (`classification`, `resolved_type_args`); child slots are bare `Vec<Rc<…>>` (no `RefCell`) and `Expr` is `!Clone` (`node_occurrence.rs:316`). So a rewrite must **produce a new subtree and write it back** — which the build side now does (§2.2(2), §5.1). *Note:* typed occurrences (§2.2(4)) add the kept type as a third per-node annotation (or a side table keyed by occurrence) — an impl-detail choice.
4. **Occurrence types are discarded; no `min_sort`.** Firing is type-directed (§6): a sort/spec rule matches only where the operand's sort conforms, and the dot guard needs the receiver's sort = `min_sort` (widen to the least declared sort). The typer *computes* each occurrence's type but **discards it** (`TypeResult.ty`; the occurrence keeps only `classification`/`resolved_type_args`). So the foundation needs **typed occurrences** — the typer *keeps* each occurrence's type (storage form is an implementation detail) — and a `min_sort` reader over them. `find_operation_on_sort` likewise doesn't exist yet.

---

## 3. Two corrections to the brainstorm/proposal

- **The receiver's sort is `min_sort`, not `classification`.** `classification`
  holds a `CallClass` (`typing.rs:2403`) — dispatch-rewrite info, set only on
  spec-op call sites; a bare receiver never gets one. The type lives in
  `TypeResult.ty` and is **discarded** after checking. So the fix is **typed
  occurrences**: the typer keeps each occurrence's type, and `min_sort` (widen
  to the least declared sort = `sort_head(TypeResult.ty)`) reads it. `min_sort`
  is the precise notion the proposal's vague `typeof` was reaching for, and it
  is an *expression-accepting* (compile-time) builtin/reader, never a runtime
  goal.
- **The matcher handles `Value::Node` occurrences (WI-276/277), except `DotApply`/control-flow.** §2.2(1). Expr-occurrence matching is available for Apply/Constructor/leaves today; only the `DotApply` arm remains, and it is dot-client substrate (WI-279).

---

## 4. Architecture: one rewriter over expressions

One rewrite relation — *find a subexpression matching a `[simp]` rule's LHS,
check the (type-directed) guard, replace with the RHS instance* — run at two
**call sites** that differ in **one** thing: the representation each holds. Not
"two phases": both rewrite **expressions** (the only boundary is
expression-vs-value, §1).

```
                  one rewriter over expressions
        ┌──────────────────────┴───────────────────────┐
  logical-engine call site (exists)              typer call site (new)
  apply_eq_rules over expressions                rewrites NodeOccurrence op bodies
  (rule resolution, at compile time)             (op-body expressions, in the typer)
        └──── shared: rules · TermView matcher (subsort-aware) ·
              guard eval (min_sort + requires) · strategy + termination (§6) ────┘
  differ ONLY in result construction:  Term (alloc)   |  NodeOccurrence (synthesized_expr)
  the real boundary:  expression (rewrite)  vs  value (eval — outside simp)
```

Why the representations differ: each call site rewrites **the expressions it
already holds** — the logical engine its `Term` goal-expressions, the typer the `NodeOccurrence`
op bodies that req_insertion/eval/IR also consume. **Spans are not the
differentiator** — terms carry them in `term_spans` / `functor_spans`
(`mod.rs:237/243`), occurrences inline (plus `Synthesized` provenance). Nor is
hash-consing — that is the `TermStore`, not the rewriter. The only
representation-specific step is **building the rewritten result**; everything
else (rule lookup, subsort-aware matching, guards, strategy) is shared.

### 4.1 The matcher already spans both representations

`TermView` (`term_view.rs:55`) matches a rule-LHS pattern (a `TermId`) against a target that is **either** a `Term` **or** a `Value` — it is not term-specific. `Value::Node` is already structural for `Apply`/`Constructor`/leaves (WI-276/277): `head` → the inner `Expr`'s functor, `pos_arg`/`named_arg` → child occurrences via `ViewItem::Node`, so `match_view(rule_lhs, &Value::Node(occ))` binds pattern vars to child occurrences with **no second matcher**. The remaining arm is **`Expr::DotApply`** (head = the `dot_apply` functor; children = receiver / name / args) — dot-client substrate, WI-279.

**Matcher ≠ typer.** `occ_head → Opaque` only means *no rule LHS structurally matches that node*; it says nothing about typability. The forms that stay `Opaque` — control-flow (`If`/`Match`/`Let`/`Lambda`/collection literals) and post-elaboration `*Within` — are still **typed** by the typer and the rewrite **walk still descends into their children** (a redex inside an `if`-branch is rewritten). They're opaque because a `[simp]` rule LHS is a *functor-application* pattern, so nothing would match an `if`/`match` node directly — a scoping choice, liftable later (e.g. `if true then ?a else ?b = ?a`) by making them structural too.

### 4.2 The logical-engine call site (exists)

`apply_eq_rules` (`resolve.rs:1266`): rewrites the `Term` expressions the logical engine holds when resolving rules at compile time. It already sets the reference strategy (innermost) and termination (fuel 100). It is **also guard-free today** (`is_equation`, empty body) — so it must gain the same guard-aware, subsort-aware firing as the typer call site (§6); they run the one rewriter. (The logical engine *also* runs at runtime over non-expression goals — out of simp's scope, §1.)

### 4.3 The typer call site (new) — and the simplest thing it does

A bottom-up walk over op-body `NodeOccurrence` trees that reuses the matcher (§4.1) + rule lookup + strategy, builds `synthesized_expr` RHSs, and writes the result back via `set_op_body_node` (§5). Even a "simple" identity is type-directed once its functor is a sort op:

```
rule add_zero: add(?x, 0) = ?x   [simp]      -- add is Numeric.add → carries
operation residual(v: Vec, k: Int64) -> Vec    -- `requires Numeric[T]` implicitly;
  add(mul(v, k), mul(v, 0))                   -- fires by sort conformance →  mul(v,k)
```

What such rules *do* have for free is **structural termination** (RHS no larger than LHS), independent of the type-directed guard. Dot dispatch (§7.1) is the same kind of client — a sort-scoped, `requires`-guarded rule. The engine is the feature; `dot_apply` is one functor it rewrites.

### 4.4 One rewriter — consistency is structural (no "phase agreement")

There are not two phases to reconcile: the **same** rewriter (matcher + strategy + termination + guard eval) runs at both call sites over expressions, so consistency is **structural**, not an obligation to police. The only boundary is expression-vs-value: simp rewrites expressions; an evaluated value is outside its domain. `min(3,5)` simplifies identically wherever it appears as an expression (op body or goal); the value `3` is out of scope.

---

## 5. The typer-side rewrite in detail

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
  3. Query the rule index for [simp] rules whose LHS functor matches this node
     (incl. guarded rules — the empty-body gate must be relaxed); the general
     step, not dot-specific.
  4. For each candidate (firing order per §6): match LHS via match_view (§4.1),
     subsort-aware (operand conforms to the rule's sort: min_sort(child) <: S);
     evaluate the guard — explicit `:- …` + the sort's `requires` — against
     min_sort + satisfaction (§6); on success reify the RHS into a fresh
     synthesized_expr(.., from=occ, by=SIMP_PASS).
  5. Recursively rewrite the synthesized RHS (chains, delegation re-emit, AD cascade),
     bounded by fuel (§6); return it. If nothing fires, return the rebuilt node.
```

For the dot client this terminates structurally (RHS has no `dot_apply`); for value/AD clients fuel bounds it.

### 5.4 The guard reads `min_sort` off the typed occurrence

Firing is type-directed: matching is subsort-aware and the guard consults the
operand's sort. That sort is **`min_sort`** — widen the (typed) occurrence to
its least declared sort (`= sort_head` of its type). It is **not a goal** and
not `typeof`-the-builtin; it reads the occurrence's **kept** type (§2.2(4),
§3 — typed occurrences). So:

- The receiver's subtree is rewritten bottom-up before this node, so it is typed
  and dot-free; `min_sort(receiver)` is a lookup over its type (no recompute, no
  side-table of `type_of` facts, no faked env). `is_entity`/`has_field`/
  `find_operation_on_sort` are likewise expression-accepting compile-time
  builtins evaluated against the KB.
- The `requires` half of the guard (explicit + the enclosing sort's) is a
  satisfaction check on `min_sort`; for the produced `apply`, ordinary
  `req_insertion` runs afterwards (the *downstream* role — §7.1, proposal §6.6).

Guards are **not only type-level.** An explicit `:- …` may be any resolvable
condition — type-level (`min_sort`/`is_entity`/`has_field`/`requires`) **or
value-level** (`compare(?x,?y) <= 0`, `constant_fold` — §7.2). The engine
evaluates the guard generally; `min_sort`/`requires` is the type-directed kind,
and value-level guards are the basis of the value-conditional clients (§7.2).

The earlier (i) "engine-evaluated guards over a reconstructed pre-typer env" and
(ii) "assert `type_of` facts so a `typeof` goal answers" were both wrong: (i)
faked the type context (and missed scope); (ii) mis-modeled `min_sort` as a
goal. With typed occurrences, neither is needed.

---

## 6. Reduction strategy, termination, firing — the semantic decisions

These belong to the **shared core** (so both call sites stay consistent, §4.4), and they are semantics:

- **Reduction strategy: leftmost-innermost / bottom-up.** Forced by type-directed dispatch (an outer rule needs `min_sort` of the reduced inner term) and matches both the typer's walk and `apply_eq_rules`'s innermost order. Consequence: strict, no lazy discard (brainstorm Q20).
- **Termination.** Structural where the RHS is no larger than the LHS (no fuel). Value/AD clients: fuel (port `apply_eq_rules`'s bound) + a `Synthesized.from` ancestor-loop check. Commutative/AC laws (`add_comm`) must stay **bare** (non-`[simp]`) or it loops. Open: should the loader *reject* a `[simp]` tag on a detectably-non-terminating rule (LHS≡RHS permuted)?
- **Firing specificity — three steps, two dimensions** (matches proposal §4.6). When several rules could rewrite one redex, selection is: **(1) structural narrowing** (discrim tree — functor/name/arg shape, concrete edges before variable edges); **(2) subsort-aware sort-directed matching** — a rule on sort `S` applies iff `min_sort(receiver) <: S` (conformance, transitive: a rule on `C` fires on `A <: B <: C` too), which the structural tree does **not** capture; **(3) the `requires`-guard**. Ordering combines both dimensions: most-specific **sort** first (`A` over `B` over `C`), structural specificity as tiebreak; a scope-less all-variable LHS (`default_dot`) is the top, tried last. Pure structural discrim is *insufficient* — it can't distinguish two rules differing only by receiver sort (`List.map` vs `Either.map`).
  - **Export consequence.** Most-specific-first is an engine *ordering*; exporting to a flat, unordered logical-rule set requires **synthesizing exclusion guards** so the less-specific rules don't also handle the more-specific case: rule on `B` gets `:- not (min_sort(recv) <: A)`, rule on `C` gets `:- not (min_sort(recv) <: B)`, per goal. That turns the ordered override into an equivalent unordered set.

Because these are observable semantics shared across compile-time and runtime, a sibling proposal (not just this impl doc) may be the right home for ratifying them. Flag for decision.

---

## 7. Clients

### 7.1 Client A — dot dispatch (proposal 043 §6)

Dot is one client of the **type-directed** engine: a dot rule is the same shape
as a spec/sort equational rule — **sort-scoped, `requires`-guarded**, fired in
the typer where `min_sort` is in hand. The guard uses `min_sort`, never a
`typeof` goal.

- **`Expr::DotApply { receiver, name, pos_args, named_args }`** node (`node_occurrence.rs`, sibling to `Apply`); wire into `drain_expr_children`/`for_each_child`; add reflect entity `dot_apply(receiver, name, args)`.
- **Converter** (`parse/convert.rs`): emit a `dot_apply` term for **value-receiver** dot forms — both `?x.field` (currently `BuildFrame::FieldAccess`, keeps the receiver) and `?x.method(args)` (currently flattened via `collect_field_access_segments`, `convert.rs:342`, which has **no `variable` branch** → drops the receiver: the gap). Keep `Foo.bar` / `Map[K=…].empty()` flattening. Add the `dot_apply` functor → `Expr::DotApply` case in `materialize_from_handle`. (Bare-*identifier* value receivers — `p.x`, `l.method()` on a param/local — are a deferred follow-up: scope-aware load-time re-route, WI-280.)
- **`find_operation_on_sort(sort, name) -> Option<qualified_op>`**, subsort-aware:
  - **Tier 1** — the sort's own ops (`map` in `enum List`), no import.
  - **Tier 1b** — ops of specs the sort *satisfies* (`Int64.min` → `Ordered.min` via `fact Ordered[Int64]`); the headline `requires`-typeclass case. The WI-240 `sort_ops` table covers user `fact Spec[ImplSort]` but **not** builtin satisfaction (`Int64 → Ordered`) — gap to close (WI-281).
  - **Tier 2** — import-scoped extension ops (no first-param index yet).
- **Dispatch rules** — guards use `min_sort` + the expression-accepting `is_entity`/`has_field`/`find_operation_on_sort` builtins (not a `typeof` goal):
  - `dot_field: dot_apply(?x, ?name, []) = field_access(?x, ?name) :- is_entity(min_sort(?x)), has_field(min_sort(?x), ?name) [simp]` — writable; reaches the existing `field_access` builtin.
  - **sort-specific rules** (the extensible case) are writable with a **concrete** RHS, declared on the sort: e.g. `either_map: dot_apply(?e, map, [?f]) = either_map(?e, ?f) [simp]` in `Either`. Conformance (§6 step 2) makes it apply; sort-specificity makes it outrank the default.
  - the **global default** ("resolve `name` to an op on `min_sort(?x)`") has a *dynamically-resolved* functor, so a literal `?op(?x,?args)` RHS is a **variable-functor** non-term. Express it either as **engine fallback logic**, or via an **`apply_op(?op, [?x|?args])` builtin** that makes even the default a writable rule (open: D6).
- **Errors**: neither fires → "no field or method `name` on sort `S`" at `occ.span`, via the `Synthesized` chain.
- **Type params & `requires` ride existing machinery — no dot-specific path.** The rewrite emits a plain `apply(op, [receiver, …args])` with empty `type_args`; by the time anything downstream sees it, it is indistinguishable from a written call. Type parameters are inferred by the normal op-body type-check (WI-270 expected-type threading; WI-272 `resolved_type_args`) — `?xs.map(?f)` pins `map`'s `T` through the *receiver* (first arg: `xs: List[Int64]` ⇒ `T=Int64`), `?f` pins `U`. `requires` clauses are elaborated by `req_insertion::run`, which runs **after** the rewrite (§5.2) and reads `CallClass` off the now-classified synthesized apply — so `?a.min(?b)` (`Ord[T]`) and `?l.contains(?e)` (`Eq[T]`) dispatch through the existing PinNow / ConcreteApplyWithin / DeferToRequirement path (`typing.rs:2403`), and an unsatisfied `requires` is a genuine "sort `S` lacks `Ord`/`Eq`" error at the dot-call span. **Ordering requirement:** the rewrite must complete before the final op-body type-check + `req_insertion` — it does (§5.2). **Open decision (D6):** requirement-aware `find_operation_on_sort` (early/precise rejection, overload disambiguation) vs name+sort resolution with `requires` checked on the produced apply (lean: the latter).

### 7.2 Client B — value-conditional simp (`min`) [sketch]

Adds the `constant_fold(?const, ?source)` builtin (the only occurrence-aware value bridge: compile-time fold-or-STUCK, identity otherwise), STUCK→residualize handling, and fuel termination. `min(3,5)` folds to `3` as an *expression*; `min(?age, ?thr)` residualizes and is rewritten by the *same* rules whenever it is later processed as an expression (the logical-engine call site). Reinforces §4.4: one rewriter, so the constant/non-constant boundary is shared by construction.

### 7.3 Client C — automatic differentiation (`diff`) [sketch]

`diff` is a plain operation over `Expr`, defined by `[simp]` *rules* (the rules carry the tag, the op doesn't). Recursive rewriting to fixpoint; needs `[unfold]` in the typer to inline bodies before pattern-matching (brainstorm Q15) and a firing-specificity policy (§6). Pure structural rewriting — never STUCKs.

---

## 8. Interactions (unaffected by construction)

Because the typer-side rewrite writes the redex-free tree back **before** them: `req_insertion::run` (`req_insertion.rs:41`) collects `CallClass` over `Expr::Apply` on the rewritten tree as today; eval / interpreter IR never see `dot_apply` and lower `apply(List.map, …)` like any call. The pre-existing "equation-defined op has no body to lower" concern (`min` residualized) is the IR doc's open question (`interpreter-ir.md:190`), not new here.

## 9. Test plan

1. `TermView` for `Expr::DotApply`: a dot rule LHS matches a `DotApply` occurrence (Apply/Constructor occurrence matching already lands via WI-276/277).
2. Converter: `?x.field` and `?x.method(args)` → `Expr::DotApply` with receiver intact; `Foo.bar` still flattens (byte-identical IR).
3. `find_operation_on_sort`: tier-1 `?l.map(?f)` resolves `List.map` with no import; tier-2 only when imported.
4. Driver: `xs.map(f).filter(p)` chains; `p.x` → `field_access`; no-match error at source span; rewritten body type-checks and runs identically to a hand-written `apply(...)`.
5. One rewriter: a value rule (`min`) gives the same result rewritten at either call site — the typer over an op-body occurrence, the resolver over a goal term (both expressions).
6. Type-directed: a sort/spec rule fires only where the operand conforms (`min_sort <: S`), incl. via the subsort chain; a more-specific-sort rule overrides a more-general one; exported flat, the exclusion guards reproduce the override.

## 10. Decisions to confirm

- **D1 — engine vs one-off (decided).** One **type-directed** engine over expressions, reusing the shared matcher (extend `TermView` to `Node` + add the occurrence build side), run at both call sites — *not* a dot-special-cased pass.
- **D2 — typed occurrences (decided).** The typer **keeps** each occurrence's type; `min_sort` reads it. *How* it's stored (node field / side table keyed by occurrence / `type_of` facts) is an implementation detail. This replaces the earlier (i) engine-evaluated-over-faked-env / (ii) `type_of`-goal options (both wrong, §5.4).
- **D3 — strategy/termination/specificity** §6: strategy = leftmost-innermost; **specificity is subsort-aware (§6): structural narrowing → sort-directed matching (`min_sort <: S`) → `requires`-guard; most-specific-sort wins**, structure as tiebreak. Export to flat rules synthesizes exclusion guards. Termination policy still open for value/AD clients. Ratify in a sibling proposal or here?
- **D4 — `ViewItem::Node` representation** §2.2(1): new `ViewItem` variant vs alternative occurrence-matcher.
- **D5 — tier-2 import semantics/timing** (043 open-Q10a). Plus **Tier-1b spec-satisfaction** (`Int64.min`→`Ordered.min`) — currently a `sort_ops`-table gap (WI-281).
- **D6 — requirement-aware dispatch + the global default.** Should `find_operation_on_sort` be requirement-aware at *selection* (early/precise errors), or name+sort with `requires` checked *downstream* on the produced apply (lean: downstream)? And is the global default **engine fallback logic** or an **`apply_op` builtin** (making the whole dispatch writable data)?
- **D7 — guarded-rule indexing.** Relax `is_equation`'s empty-body gate so guarded `[simp]` rules (incl. implicit enclosing-sort `requires`) are indexed and fired.

## 11. Build order

1. **Typed-occurrence substrate** — the typer keeps each occurrence's type; add a `min_sort` reader (D2). Prerequisite for everything type-directed.
2. **Shared core, read side:** the `Expr::DotApply` matcher arm (§4.1; Apply/Constructor/leaves already structural via WI-276/277) + **subsort-aware matching** (§6 step 2).
3. **Shared core, guard-aware firing + build side:** evaluate guards (explicit `:-` + enclosing-sort `requires`) via `min_sort` + satisfaction; relax `is_equation` indexing (D7); occurrence build side (`synthesized_expr`); converge `apply_eq_rules` and the typer call site onto it (§4.2, §6). **This is WI-283.**
4. **Typer-side driver:** bottom-up, tree-producing, write-back, provenance, run per op body just before the op-body type-check (§5.1/§5.2).
5. **Dot client substrate:** `Expr::DotApply` + converter (value receivers; bare-identifier is WI-280) + `materialize_from_handle` + `find_operation_on_sort` (Tier-1 / Tier-1b spec-satisfaction). **WI-279.**
6. **Dot rules** — `dot_field` + sort-specific rules; global default (engine logic or `apply_op`, D6); diagnostics + collision lint.
7. **Tests** (§9). Then tier-2, and clients B/C separately.

---

## Appendix A — reentrancy (holds)

`type_check_node` (`typing.rs:904`) allocates fresh local `work`/`results` per call (910–911), takes `occ` by reference, and is already re-entered recursively by the `check_*` helpers. The op-body driver builds a fresh `TypingEnv` per op; no call-scoped state lives on `kb` across the walk. So the rewrite may call `type_check_node` on any subtree if a (re)type is needed. (With typed occurrences (D2), `min_sort` is a *lookup* over the kept type, so on-demand recompute is largely unnecessary; reentrancy remains available as a fallback.) Reentrancy was 043's stated first concern; it is real but *not* the binding constraint — that is the annotate-only/tree-production change (§2.2(3), §5.1).
