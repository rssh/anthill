# 065: `TypeValue[B]` — a rigid type is a value only where a requirement says so

## Status: PROPOSED (2026-09-19). Decided in discussion after WI-20260918-R541X; supersedes the two open directions recorded on WI-20260919-891QP.

## Amends: [055](055-types-in-value-position.md) §2 (its type-PARAMETER bullet — a rigid denotes a `Type` value only under a requirement) and §8 (`type_value[T]()` is backed by that requirement, not by the frame channel). 055's other decisions stand unchanged; §5 below goes through them one by one.

## Relates to: WI-20260918-R541X (the defect class this closes for good), WI-20260919-891QP (a provider's own parameters through a slot — closed by §4), WI-20260919-H20YY (a defaulted member's override through a slot — depends on 891QP), WI-20260911-3MV2C (the error tag — the same discipline applied to one spec), CKD4J (`eq_derive` derives nothing for a parametric sort — the same gap §2 must close), `docs/design/requirement-channel.md` §2.1 (staging invariant), `docs/kernel-language.md` §8.7 (override refinement).

## The problem, in one paragraph

Today EVERY generic body may read its type parameters as values. `operation ty[T]() -> Type = Cell[V = T]` works because the call site writes `T`'s binding onto the frame's type-argument channel (WI-272/708), and R541X extended that channel to sort parameters reached through generic callers and requirement slots. That makes the channel an implicit `Typeable` held by every operation, and it has three costs. **Parametricity is false**: a signature `f[B](x: B) -> R` promises nothing about whether `f` inspects `B`. **The channel cannot reach everywhere**: a provider's own parameters on a member entered through a requirement slot (891QP) have no call site that could write them, because the dictionary carries no type bindings. **An erasing backend has nothing to read**: the channel is an interpreter artifact. R541X made the unreachable cases loud (`EvalError::UnboundTypeParam`); this proposal makes them unwritable.

## The rule

**Reading a rigid type `B` in VALUE position requires `TypeValue[T = B]` among the requirements in scope.** Otherwise it is a load error naming the parameter, the read, and the clause to add.

```anthill
sort anthill.reflect.TypeValue            -- beside `Type` itself (055 decision 2)
  sort T = ?
  operation type_value() -> Type          -- body-less; every instance is DERIVED (§2)
end

operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]   -- loads
operation bad[B](x: B) -> Type = Cell[V = B]
  -- load error: `B` is read as a value at <line:col>, and nothing in scope requires
  --   `TypeValue[T = B]`; add `requires TypeValue[T = B]` to `bad`.
```

**055 §8's spelling is this member.** `type_value[T = B]()` is `TypeValue.type_value` called with a callee bracket, which binds the enclosing sort's parameter (WI-20260911-RS2G4) — so 055's "canonical static→dynamic reifier" needs no declaration of its own, and a bare `B` in value position (055 §2) is sugar for the same call. (The loader's internal `Expr::TypeValue` — the resolved-IR form of 055 §2 — is a different thing with a colliding name; it is not surface.)

**Explicit, not inferred** (user decision, 2026-09-19). The clause is part of the signature, because the signature is what a caller — and a spec — reads. Inferring it from a body is deferred, not rejected: it is a convenience over this rule, not a different rule, and it cannot apply to a body-less spec operation at all.

What the rule does NOT touch:
- **Type positions.** `x: B`, `-> List[T = B]`, a `requires` bracket — types used as types are static and erasable, and nothing reads them at run time.
- **Concrete sorts.** `Cell[V = Int64]` in value position reads no rigid; its `TypeValue` is the derived instance, discharged statically at no cost to the author.
- **Rule bodies**, which unify types rather than read them (`docs/kernel-language.md`, "One principle, two engines").

## 1. Lowering: a value read IS a slot dispatch

A value-position read of rigid `B` lowers to `TypeValue[T = B].type_value()`, dispatched through the requirement slot like any other body-less spec operation (`DeferToRequirement`). A type EXPRESSION that mentions `B` — `Cell[V = B]` — is already evaluated by the argument pump, which evaluates each argument and builds the application through the canonical builder; only the leaf read changes. So **no new surface is needed** to "build a `Type` from computed `Type` values" — the gap 891QP's direction (ii) recorded dissolves, because the pump was always that builder.

The frame type-argument channel stops being consulted for value reads once every such read is backed by a slot. It stays, for now, for its one other consumer — `Error.reify`'s `T1` (027.4) — whose migration is 3MV2C's decision (open question 2).

## 2. `TypeValue` is DERIVED, never written

Every sort gets its `TypeValue` instance from the loader, and a user-written `provides TypeValue[…]` is refused.

**Why derived-only is not a style choice.** A forgeable `TypeValue` makes every type read a claim instead of a fact: `Boom provides TypeValue[T = Boom]` with a `type_value` answering `Int64` would route a boundary, a `facts_of`, or an error tag to the wrong sort, silently. GHC made `Typeable` derived-only for exactly this reason; 3MV2C reached the same line independently ("derived-only keeps the discharge a GUARANTEE; overridable makes it a CLAIM").

**A parametric sort's instance is CONDITIONAL**, carried in the instance's own context:

```anthill
-- derived for `sort Box { sort V = ?  … }`:
Box provides TypeValue[T = Box[V = V]] requires TypeValue[T = V]
--   type_value() = Box[V = V]      -- the `V` read is a slot dispatch into the context
```

This is `Typeable a => Typeable (Box a)`, and it is the same derivation shape CKD4J found missing for `Eq` (`provides Eq[Pair] :- Eq[A], Eq[B]`). **One conditional-derivation mechanism serves both**; it should not be built twice.

Structural types need an instance per FORMER, not per sort: named tuples, arrows, and whatever else `TypeExtractor` builds. Effect rows are not values and get none (open question 3).

## 3. An implementation may not require more than its spec — at the OPERATION level

An operation-level `requires` is an extra INPUT: a dictionary the caller supplies. A caller dispatching through a spec knows only the spec's signature, so it cannot supply what only the implementation asks for. The substitutability rule: **an implementation's operation-level requirements are a subset of the spec operation's** (after aligning the two operations' parameters, as §8.7 already aligns them).

For `TypeValue` this is the parametricity rule carried across dispatch: if `Spec.f[B]` does not declare `requires TypeValue[T = B]`, **no implementation of it can inspect `B`**. A spec that wants its implementations to be able to must say so in the spec — the analogue of a Scala trait method declaring `[B: ClassTag]`.

The requirements an implementation MAY add are those over its **own sort's** parameters, carried on the INSTANCE:

| clause | supplied by | may an implementation add it? |
|---|---|---|
| operation-level, over the operation's own parameters — `f[B](…) requires TypeValue[T = B]` | the caller, per call | **no**: ⊆ the spec operation's |
| instance context / provider sort, over the provider's own parameters — `Box provides TypeValue[…] requires TypeValue[T = V]` | the dictionary's builder, from the carrier's type arguments, at selection | **yes**: the spec's caller never sees it |

**A direct call does not relax it.** `Box.type_value()` at a pinned carrier could in principle supply an extra operation-level dictionary. It is still refused: one member must be a valid implementation of the spec from every route that reaches it, which is §8.7's reading (a member needing more than the spec is a distinct operation, not an override).

**What already exists, and what is NOT yet known.** §8.7 requires an override's `requires` to be "no stronger", and `check_override_refinement`'s precondition leg reads the implementation's `requires` list — the same list the loader injects `EffectsRuntime[…]` clauses into, so spec-requirement clauses and logical preconditions share it. An added `requires TypeValue[T = B]` is therefore PROBABLY already refused as a strengthened precondition. **Not driven.** The first implementation step drives it, and either records the existing refusal as this rule's enforcement or adds the leg.

## 4. What it closes

- **891QP** — `Box`'s member reading `V` is served by `Box`'s derived instance context `TypeValue[T = V]`, which the dictionary builder fills from `Box[V = Boom]`'s argument when the slot is selected. The witness idiom is the same: `CrateTT provides TypeValueB[T = Crate[W = E]]` needs `requires TypeValue[T = E]` on the provision, where `E` is determined by the head. Projection paths (891QP's direction (i)) are NOT needed for value reads; they remain the tool for the bridge's `unify_types` (requirement-channel.md §10 item 4), a separate question.
- **H20YY** — the override `type_value() -> Type = Option[T = V]` reads `V` through the same instance context, once H20YY routes the call through the slot.
- **R541X's residue** — every `UnboundTypeParam` becomes a load error at the read, and the run-time fault remains only as a backstop.
- **3MV2C** — `raise(error: T) … requires ErrorTag[T]` with the type term as default is this discipline applied to one spec; whether `ErrorTag` IS `TypeValue` or refines it is 3MV2C's to decide.

## 5. Against 055, decision by decision

- **§2, the denotation rule** — classification is unchanged, including 055's "independent of the expected sort": a type parameter in value position is still classified as a `Type` value. This proposal adds a WELL-FORMEDNESS condition to that one bullet (the requirement) and a LOWERING (the slot dispatch). The sort bullet is untouched.
- **§3, `Type` lives in `anthill.reflect`** — so does `TypeValue`.
- **§4, the no-dereference fence** — unaffected. Everything here is on the type→value side; `type_value()` produces a value, and nothing turns one back into a type.
- **§5, profiles** — this proposal makes the compile-only fence checkable from a SIGNATURE. An operation can read a rigid as a value only under `requires TypeValue[…]`, so the fence's "no reflect sort in a value-carrying position" can refuse on that clause without inspecting the body. In a full profile the dictionary is the thing an erasing backend reads, which 055 §8's "erased/monomorphized" left unstated.
- **§6, instance claims** — a derived `TypeValue` provision is one; derived-only (§2 above) is a rule about who writes it, not about what it denotes.
- **§8, `type_value[T]()`** — it was to "land after WI-708", reading the frame channel. It is now a member of the spec it names; the WI-708 dependency is replaced by §1's slot dispatch. Never built in the stdlib (measured: no stdlib operation returns `Type`), so there is nothing to migrate.

## 6. Migration

The stdlib has **no** operation returning `Type` (measured: 0). Ten test files contain one; among them the WI-708 rows (`ty[T]() -> Type = Cell[V = T]`), the RS2G4 rows (`Box[T = Letter].selfType()` — a sort parameter, so `Box` gains a sort-level `requires TypeValue[T = T]`), and R541X's own file. Those are the WRITTEN reads; the full census is step 1 below, and it is MEASURED rather than grepped — by the rule itself, run in the typer as a count instead of a refusal, over stdlib and every test fixture. (R541X's `refuse_unbound_type_param` marks the same two read shapes — a `TypeValue` head, `reduce_var`'s sort arm — but in the EVALUATOR, so it would count only the reads a test happens to execute.) `Type`-slot arguments (`facts_of(kb, T)`, `is_modifiable(T)`) are value reads too and are in that count.

## 7. Order of work

1. **Census + the §3 probe.** Count the value reads of rigids across stdlib and tests; drive whether an implementation adding `requires TypeValue[T = B]` is already refused.
2. **Conditional derivation** (with CKD4J): derived `TypeValue` for every sort and former, conditional for parametric sorts; refuse a user-written provision.
3. **The load rule + lowering (§1)**, with the migration of step 1's census in the same change, so the suite never passes through a state where the rule is on and a read is unmigrated.
4. **891QP** through instance contexts (§4); its two R541X rows flip to positive.
5. **H20YY**.

## Open questions

1. **Inference from a body** — deferred by decision, not rejected. When it is taken up: an inferred clause is still a signature change a caller sees, so it wants a rule for WHERE it becomes visible (a declaration's printed signature, `anthill check` output).
2. **`Error.reify`'s `T1`** is the second consumer of a rigid-as-value, reading the frame channel rather than the body. Consistency says it needs the clause too (`catchIt[P](…) requires TypeValue[T = P]`); 3MV2C owns the decision, and until it is made the channel stays.
3. **Formers without a value reading.** An arrow type's effect row is not a value; `TypeValue` of `(Int64) -> Int64 @ {E}` with `E` rigid needs either an effect-row analogue or a refusal. Proposed: refuse at the read, naming the row, until a program needs it.
4. **Transients.** A `Type` value built per dispatch is a transient, and interned terms live for the KB's lifetime (CLAUDE.md's representation note; 3MV2C's 2026-09-18 feedback on `ground_type_params`). The lowering must build its result on the transient carrier, not intern one per call.
