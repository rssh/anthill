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

   **Attachment — file under every variable the goal mentions.** The two forms
   `constrained-term-substrate.md` describes are *semantically equivalent*; they differ in
   keying and timing. The per-variable wakeup files a constraint under one `VarId` and fires
   at that variable's bind, BEFORE the commit, so it can veto the binding — it "prunes at the
   bind site rather than after a full head match". The body-guard form is an ordinary goal
   after the match, keyed by nothing, able to fail the clause but not a bind.

   The doc calls a multi-variable guard "a compound the per-variable wakeup can't express",
   and that is about the store being SINGLE-KEYED (`ImHashMap<VarId, Vec<Constraint>>`) — a
   goal over `From` and `To` has no one key. It is not a limit on what the mechanism can
   decide. Filing the same goal under EACH mentioned variable resolves it: every bind wakes
   it, it re-resolves under what is bound so far, and while under-determined it suspends —
   already outcome 3, not a new case. This is CLP-style re-suspension, and the three
   outcomes (holds / refuted / suspend) are exactly its shape.

   Cost is one re-resolve per mentioned-variable bind — two for `flows_to(From, To)` — against
   the body-guard's one. Bought with it: bind-site rejection, and a single-parameter goal
   needs no special case, since filing under "every variable it mentions" degenerates to the
   plain per-variable wakeup when there is one.

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

## 5. The eager path (WI-835 reuse)

A ground written argument binds the parameter at the lowering, so the wakeup fires during
load. `take_parameterized_type_sites()` supplies what the diagnostic needs and nothing has to
be re-derived:

- span of the base name, per site;
- bindings with positionals **already mapped** onto declared parameter names (`Map[Float, Int64]` ⇒ `K = Float`);
- raw *and* σ-substituted clause forms, which is how `Map[K = Float]`'s message names both the parameter `K` and the carrier `Float` — reading the parameter back out of σ misnames it whenever two params bind one carrier.

`check_use_site_requires_eq` is **not** modified; the new discharge is a sibling in the same
walk. Its `Eq` check keeps its negative reading and its own justification.

## 6. Measured boundaries

- `sort Trust = ?` admits everything — `operation nonsense(t: Text[Int64])` loads clean.
- `requires IsLevel[T = Trust]` does not bind: only `anthill.prelude.Eq` is consulted at use sites.
- A positive spec check *does* discriminate for a user marker — `fact Marked[T = Int64]` refused, `[T = Public]` loads — so the marker route fails on design, not mechanism (proposal §History).
- A rule cannot supply an instance: `rule IsLevel[T = ?x] :- is_entity_of(?x, Level)` yields none. Spec resolution reads provisions and instance facts, never the SLD path.
- `is_entity_of` discriminates and is derived from the enum: `(Public, Level)` and `(Untrusted, Level)` true, `(Int64, Level)` no solutions. It is a name-keyed builtin (`register_builtin_tags`) shadowing the declared rule at `typing.anthill:33`, reading the O(1) `entity_parent` index.
- `requires` at a sort item refuses a non-sort structurally: "a `requires` names a SPEC — only a sort (§5.2) has the operations a requiring sort dispatches against."
- A sort-body `constraint` over the parameter loads but resolves nothing — the same file with both names replaced by garbage loads identically, 2675 facts either way.
