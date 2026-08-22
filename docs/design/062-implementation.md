# 062 implementation notes — mechanisms, prerequisites, measurements

Companion to [proposal 062](../proposals/062-bounded-sort-parameters.md), which states the
surface and its rules. This document carries the mechanism, the build order, and the
measured boundaries. Measurements are against the Rust loader at `b67def46`, each with a
both-sides control.

## 1. Substrate — the constraint store (pre-existing)

The bound is a `Constraint::Type` on the parameter's variable. Nothing here is new; see
[`constrained-term-substrate.md`](./constrained-term-substrate.md) for the model.

- `Substitution.constraints: ImHashMap<VarId, Vec<Constraint>>` — per-branch, `VarId`-keyed, persistent so it rides `subst.clone()` at O(1) (WI-569 / Step 0). Branch lifetime equals a binding's: snapshot/restore discards a failed unification's tentative constraints (M7).
- Two kinds exist. `Lacks` (#1, WI-328) is live — an effect-row tail's forbidden label. `Type` (#2, WI-502) is ours: "a reified type-guard `Value` the variable's eventual binding must satisfy", with `subsort(min_sort(?x), Numeric)` and `min_sort(?x) = T` as its documented examples. `is_entity_of(?t, TrustLevel)` is that shape, so **no new kind is introduced**.
- `Constraint::Type` is **write-mostly**: "no producer wires it … and no consumer discharges it yet; Step 1 lands only the substrate." Proposal 062 is its first producer.
- Merge-on-alias is implemented: binding `?a := ?b` moves `?a`'s constraints onto `?b`, so a constraint follows a union chain unaided. `residual_constraints` surfaces undischarged ones on the answer (σ → (σ, C)).

## 2. The discharge path — part of the work, not a dependency

MEASURED, the store is real but only half-inhabited, and the live half does not use the
generic path:

- **`Constraint::Lacks` is live** — one production site outside tests (`typing.rs:43863`), for effect-row tails.
- **It does not go through `bind_waking`.** `Lacks` is checked by a hand-rolled path at `bind_row_tail` (`typing.rs:44157`), the single place a row tail binds. That is why every bind in `typing.rs` can be `subst.bind_value(…)` — 12 sites — while `Lacks` is still honoured.
- **`Constraint::Type` has NO producer.** Every `add_type_constraint` call lives in `subst.rs`'s unit tests, and its values are placeholders (`Value::Str("subsort(min_sort(x), Numeric)")`, `Value::Int(7)`). It has never been exercised against a real guard.
- **`bind_value` has no loud-on-bypass assertion**, though `bind_compressed` does: "route it through bind_waking so its constraints wake (loud-on-bypass, M7(a))".

So there are two implementable shapes, and the choice is real:

**(A) Follow the `Lacks` precedent — check at the parameter's binding sites.** A hand-rolled
check where a sort parameter binds, mirroring `bind_row_tail`. Narrow, proven in this
codebase, touches no hot path. Cost: a third per-kind check path, and the generic wakeup
stays unexercised.

**(B) Widen the typing boundary.** Route typer binds through `bind_waking` and fill its
reserved `Type` slot. This is what `constrained-term-substrate.md` prescribes ("the
constraint+wakeup is preferred: it prunes at the bind site … and it is the substrate already
built"), and it would retire the `Lacks` special case in time. Cost: a change to the typer's
inner loop, wanting its own measurement, plus `bind_value` gaining the assertion its sibling
has.

**This is scope, not a blocker.** Nothing external gates it: the check is code to be
written, and it can be written as part of this work. What it does impose is an ORDERING
within the work — a producer wired before a discharge path enforces nothing and says
nothing, since `bind_value` neither wakes nor complains. Shape (A) or (B) lands first, then
the producer. That is sequencing, not a dependency edge.

**Consequence for testing.** Neither shape is observable at the language level on its own, so
neither can be driven by an `.anthill` test; acceptance is unit-level on `Substitution` or on
the chosen binding site. The first test that drives the capability end-to-end belongs to the
producer (§3 step 4).

## 3. Build order

1. **A discharge path for `Type` guards** — shape (A) or (B) of §2. Resolve the guard with the binding substituted, reject on refutation, suspend as residual when under-determined, never NAF-decide (WI-067). Shares a home with `constrained-term-substrate.md`; whether it is extracted as its own WI is a reviewability call, not a dependency.
2. **Grammar + IR + convert** — the goal form on `requires_declaration`, fanned out at convert time into its own item, as `effects E = ?` already fans into `AbstractSort` + `RequiresDecl`. Corpus tests for both the bracket and paren forms.
3. **Load — the producer** — attach the goal as a `Constraint::Type` on the parameter's variable, and emit one `SortGoalInfo` fact per clause (proposal §Decisions). The fact is declared once at load and never revised, unlike `SortRequiresInfo` — which the loader retracts and re-asserts as bindings complete (WI-1112) — so it is `constant()` for `fact_monotonicity` and may be indexed build-once.

   **Attachment — ONE record, a watch set, and a lifecycle.** An earlier draft said "file the
   same goal under every variable it mentions". That is wrong as stated, and the store makes it
   wrong in a specific way: `Constraint::Type` entries are independent `Value`s with no shared
   identity, `Type` is deliberately never deduped, and `residual_constraints` returns EVERY
   entry with no boundness filter (`subst.rs:606`). So two filed copies of one goal give a
   discharged constraint AND a stale residual copy under an already-bound variable in the same
   answer, and merge-on-alias can duplicate it further.

   The record therefore needs an IDENTITY and a WATCH SET: one constraint, an id, the set of
   parameter variables it waits on, and wake registrations under each. Discharge or refutation
   removes it from **every** key it is registered under. The alternatives — a canonical owner
   with forwarding, or explicit cross-key removal on any copy resolving — are equivalent in
   effect; what is not acceptable is independent copies, which is what the store gives by
   default.

   Tests must cover both binding orders, aliasing (`?a := ?b` after one copy has woken),
   duplicate suppression, and — the one an implementation will miss — a SUCCESSFUL discharge
   leaving no residual behind.

   **Readiness, not per-bind evaluation.** A wake does not mean "resolve now". Proposal
   §Semantics gates on groundness of `P(G)`: resolve only when every parameter variable in the
   goal is ground, and never let resolution bind one. Measured reason —
   `flows_to(Untrusted, ?to)` against the two-fact lattice answers `?to = Untrusted` rather than
   suspending, so an early resolve pins a parameter the author never wrote. A wake is therefore
   a readiness CHECK first and a resolution only if ready.

   **The zero-variable case has no key and needs its own path.** A goal mentioning no
   parameters is ready immediately, but "file under every mentioned variable" registers it
   nowhere, so no wake ever fires. Such a goal is resolved once at LOAD, at the declaration,
   with the same four outcomes (proved / refuted / truncated / unlowerable). Without this arm a
   constant goal is silently inert — the exact failure this proposal exists to remove.

4. **Eager path** — a written ground argument reports at its own span, via the WI-835 site record.
5. **Guardians + spec** — the three declarations take the goal form; kernel-language §5.4 gains the clause.

Step 1 must precede step 3 for the reason in §2. All five are this work.

## 4. The `SortRequiresInfo` hazard

The goal form must **never** produce a `SortRequiresInfo` row. That relation feeds `refines`,
which feeds `type_compatible` (`typing.anthill:57`, `:185`), so a goal recorded as a requires
row would let the typer derive `Text <: is_entity_of(Trust, TrustLevel)` — a subtyping fact
about a goal — and hand it to dispatch. The chain has **151 reader sites across 9 Rust
files** (`req_insertion`, `op_requirements`, `typing`, `resolve`, `eval`, `load`, `mod`,
`intern`, `eval/mod`), each of which would otherwise have to discriminate spec entries from
goal entries. WI-1110 is the recorded cost of this class of conflation.

The loader-side fan-out is what keeps this structural rather than remembered: two items
leave convert, and no reader changes.

## 5. The eager path — replay, not a second enforcer

The proposal calls the written-ground case "an earlier discovery of the same ill-formedness,
not a second rule". That claim is only true if the eager path does NOT independently resolve
the clause. It must be a **diagnostic replay**: the constraint is what enforces, and the site
record supplies span and bindings so the refusal can be reported where the author wrote it. If
the site walk resolves the goal itself, there are two enforcers, the "one mechanism" claim is
false, and the two paths need equivalence tests against each other. Pick replay.

What the WI-835 record supplies, none of it re-derived:

- span of the base name, per site;
- bindings with positionals **already mapped** onto declared parameter names (`Map[Float, Int64]` ⇒ `K = Float`);
- raw *and* σ-substituted clause forms, which is how `Map[K = Float]`'s message names both the parameter `K` and the carrier `Float` — reading the parameter back out of σ misnames it whenever two params bind one carrier.

`check_use_site_requires_eq` is **not** modified; the new discharge is a sibling in the same
walk. Its `Eq` check keeps its negative reading and its own justification.

**Ownership, and the plumbing that does not exist yet.** The typer and the resolver share the
`Substitution` TYPE — `types_compatible(kb, &mut Substitution, …)` — so the carrier is not the
problem. Three things are, and the build order must answer them before step 3:

- **Where the constraint is created** for each sort instantiation, and which substitution owns it through type unification.
- **Which bind API returns a verdict.** `bind_waking` returns `()` (`subst.rs:530`), so today it cannot reject: it commits and then wakes, and its wake step is inert. A pre-commit guard with reject power needs a bind entry point that can answer refuted / suspended / ok.
- **How a refused guard prevents the binding** rather than unwinding one already made.

## 6. Measured boundaries

- `sort Trust = ?` admits everything — `operation nonsense(t: Text[Int64])` loads clean.
- `requires IsLevel[T = Trust]` does not bind: only `anthill.prelude.Eq` is consulted at use sites.
- A positive spec check *does* discriminate for a user marker — `fact Marked[T = Int64]` refused, `[T = Public]` loads — so the marker route fails on design, not mechanism (proposal §History).
- A rule cannot supply an instance: `rule IsLevel[T = ?x] :- is_entity_of(?x, Level)` yields none. Spec resolution reads provisions and instance facts, never the SLD path.
- `is_entity_of` discriminates and is derived from the enum: `(Public, Level)` and `(Untrusted, Level)` true, `(Int64, Level)` no solutions. It is a name-keyed builtin (`register_builtin_tags`) shadowing the declared rule at `typing.anthill:33`, reading the O(1) `entity_parent` index.
- `requires` at a sort item refuses a non-sort structurally: "a `requires` names a SPEC — only a sort (§5.2) has the operations a requiring sort dispatches against."
- A sort-body `constraint` over the parameter loads but resolves nothing — the same file with both names replaced by garbage loads identically, 2675 facts either way.
- **SLD binds a free parameter existentially rather than suspending.** With `fact flows_to(Public, Public)` and `fact flows_to(Untrusted, Untrusted)`, the goal `flows_to(Untrusted, ?to)` answers `?to = Untrusted` (1 solution), while `flows_to(Untrusted, Public)` answers none. So "resolve the guard and see" does NOT distinguish under-determined from refuted, and resolving early would pin a parameter. This is why readiness is decided by groundness, structurally, before any resolution — §3 step 3.
- `residual_constraints` (`subst.rs:606`) returns every entry in the store and its parent chain, with **no** filter on whether the variable is bound; `Type` entries are never deduped. Independent copies of one goal therefore survive as stale residuals after discharge.
- `bind_waking` (`subst.rs:530`) returns `()`, and commits before its (inert) wake step. There is no bind API today that can refuse.
