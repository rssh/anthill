# 065: `TypeValue[B]` — a rigid type is a value only where a requirement says so

## Status: PARTLY IMPLEMENTED (2026-09-20). Proposed 2026-09-19, decided in discussion after WI-20260918-R541X; supersedes the two open directions recorded on WI-20260919-891QP.

**BUILT:** §2's derivation (WI-20260919-HXGXF, sorts only — structural FORMERS deferred), §3's subset rule including the type-parameter alignment an implementation needs to restate a clause (WI-20260919-N31XX part 1), and "The rule" itself with §6's migration (N31XX part 2) — in both halves, the READ and the FORWARD. **NOT BUILT: §1, the lowering.** A value read is still served by the frame type-argument channel, not by a slot dispatch, so §1's "the channel stops being consulted" has not happened and steps 4 (891QP) and 5 (H20YY) are untouched. §7 records each step's state and what it measured.

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

**What already exists — MEASURED by WI-20260919-BQHGD (§6).** `check_override_refinement`'s precondition leg already refuses an ADDED operation-level clause. It also refuses a clause RESTATED from the spec when that clause names the operation's own type parameter, because it does not align the two operations' type parameters. Step 3 adds that alignment; without it no implementation could restate `TypeValue[T = B]`.

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

## 6. Migration — MEASURED (WI-20260919-BQHGD, 2026-09-19)

**The census.** The rule was run in the typer as a COUNT, not a refusal: a temporary pass at the top of `check_operation_bodies` walked every operation body and recorded each expression occurrence naming a type parameter. It covered the full workspace test run, so the stdlib, `anthill-stl`, the examples and every Rust test fixture, with 157 hits over **19 unique sites**:

| where | sites | parameter kinds |
|---|---|---|
| stdlib, `anthill-stl`, examples | **0** | — |
| `wi_rs2g4_receiver_bracket_binds_sort_params_test` | 8 | 5 sort (`Box.T` ×3, `Pair2.A`, `Pair2.B`), 3 operation (`both2.U`, `ty.U`, `tyb.U`) |
| `wi_r541x_body_read_of_type_param_test` | 6 | 4 sort, 2 operation |
| `wi708_body_type_arg_read_test` | 3 | operation |
| `wi_bad3v_dot_type_arg_bracket_test` | 1 | operation |
| `wi_h054k_type_position_subst_test` | 1 | operation — see below |

Every site is the loader's resolved `TypeValue` form (055 §2): none arrived as a raw `Ref`, so `reduce_var`'s WI-206 sort arm is not reached by a type-parameter read from checked source. Eighteen sites are a bare parameter inside a type expression (`Cell[V = T]`) or a whole body (`= T`).

**The nineteenth is not a value read, and the rule must not count it.** `operation dq[K]() -> Int64 = size(put(mkq(K), "a", 1))` passes `K` as an ARGUMENT to `rule mkq(?k) <=> Map[K = ?k, V = Int64].empty() @[simp]`. After simp inlining, `K` sits in a TYPE position. Judged before expansion, the rule would refuse a program whose only use of `K` is as a type. **Step 3 judges reads after `@[simp]` expansion.**

**The census does not cover:** bodies loaded with `run_typer: false` (never checked); rule bodies (excluded by the rule); the scaland port; and `Error.reify`'s `T1`, which reads the frame channel rather than a body (open question 2).

**The §3 probe.** `wi_bqhgd_override_requires_subset_probe_test`:
- **Refused today, as 065 wants:** an override that ADDS an operation-level clause the spec lacks ("strengthens the precondition").
- **Loads and runs today:** a spec-only clause (a subset); a clause restated over a GROUND type (`Eq[T = Int64]` on both sides); a clause on a parametric provider sort over its own parameter (065 §3's permitted half).
- **OVER-REFUSED today:** a clause RESTATED verbatim over the operation's own type parameter (`requires Eq[T = B]` on spec and override). The leg compares clauses structurally and does not align the two operations' type parameters (`Desc.f.B` vs `Leaf.f.B`). An implementation must restate `TypeValue[T = B]` to read `B`, so **step 3 must add that alignment**. The row pinning today's refusal is the one it flips.

The migration is therefore five test files and nothing else. The RS2G4 file is the largest, and its sort-parameter reads gain a sort-level `requires TypeValue[T = T]` on `Box` and `Pair2`.

## 7. Order of work

1. **Census + the §3 probe** (WI-20260919-BQHGD). Count the value reads of rigids across stdlib and tests; drive whether an implementation adding `requires TypeValue[T = B]` is already refused.
2. **Conditional derivation** (WI-20260919-HXGXF, on CKD4J's mechanism): derived `TypeValue` for every sort and former, conditional for parametric sorts; refuse a user-written provision. **BUILT for SORTS (2026-09-20); FORMERS deferred** — a named tuple or arrow has no sort to carry a provision, so it needs a structural reading rather than a provision row, the same open shape as the named-tuple key in `kernel-language.md` §8.3.

   **Three things §2 above did not anticipate, each measured.** (a) `type_value()` is **nullary**, so no argument and no receiver names the type and WI-350's abstract-receiver fallback has nothing to resolve from — the dispatching dictionary is the *only* carrier of the answer, so the call MUST reach the requirement slot. (b) A spec op with a **default body is dispatched statically** and never reaches that slot (measured: the body ran with an empty requirements frame), so `type_value` is body-less — and a body-less spec op with no carrier member is refused for want of backing, while the loader cannot synthesize a per-carrier body (`set_op_body_node` takes only parsed source or a `@[simp]` rewrite). The backing is therefore a **builtin on the spec op**, which `op_backed` accepts and which covers every carrier at once. (c) The **dictionary IS the type**: `Dictionary(sub₀ … subₙ₋₁, impl: S)` names the head in `impl` and carries one sub per condition, so the answer is a walk of the evidence that selected the call — GHC's `Typeable` representation, and the reason no per-carrier implementation is needed.

   Three exclusions are load-bearing, each found by a refusal: a **type parameter** is not a carrier (its name term is a variable, so its row unifies with every goal); a **spec** is not a carrier (`List provides Iterable`, so the spec's row competes by subsumption with `List`'s own); and a provision's conditions **do not start at dictionary sub 0** (the carrier's own sort-level `requires` come first — `Map requires Eq[T = K]`).

   **Open question 4 is half-answered.** The EVIDENCE is transient — `eval/dictionary.rs` states dictionaries are deliberately not interned — but the `Type` the builtin BUILDS from it still goes through `kb.alloc`, and the parametric family is unbounded. That remains to fix.
3. **The load rule + lowering (§1)** (WI-20260919-N31XX), with the migration of step 1's census in the same change, so the suite never passes through a state where the rule is on and a read is unmigrated. **THE RULE AND THE MIGRATION ARE BUILT (2026-09-20); THE LOWERING IS NOT.**

   **Where the rule sits, and why that is the rule and not a detail.** It runs in `check_operation_bodies`, on the tree the typer **wrote back** (`result.node`) rather than the one it was handed — because `@[simp]` fires *during* the typer's node walk, and §6's nineteenth census site is a `K` that inlining moves into a type position. Judged before expansion, the rule refuses a program whose only use of `K` is as a type; judged after, there is no value read at all. Measured: with the rule at the top of that function (where step 1's temporary census sat) `wi_h054k_type_position_subst_test` goes red, and with it on the written-back tree that file never appears among the refusals at all.

   **What the census predicted, confirmed by construction.** Switching the rule on took exactly the four census files red — `rs2g4`, `r541x`, `wi708`, `bad3v` — 28 rows, and `h054k` was not among them. The stdlib, `anthill-stl` and the examples stayed green, which is §6's "0 sites" re-measured as a refusal rather than as a count.

   **Two things the migration MEASURED that §3 had only stated.** (a) The table's two halves are enforced: with `requires TypeValue[T = V]` written on `Box.valueOfB` — an *operation*-level clause over the provider's own sort parameter — `Box` and `CrateTT` were both refused *"it strengthens the precondition"*, and moving the identical evidence to the **sort** loads and answers. So a member reading its enclosing sort's parameter carries the clause on the sort, and only a member reading its **own** type parameter carries it on the operation. (b) A sort-level clause must be **suppliable at every call site of its members**, which turned R541X's unbracketed `SHold.f()` from a located run-time fault into a load refusal — the paragraph's own "now unreachable from checked source", arriving as a consequence rather than as an edit.

   **THE RULE HAS TWO HALVES, and the second was found by asking for an example.** The READ half above refuses a body that inspects a rigid without saying so. It does not, on its own, refuse a caller that **forwards** one: `mid[U](y: U) = tyOf(y)` against `tyOf[B] requires TypeValue[T = B]` inspects nothing itself, yet hands its own rigid to an operation that does — holding no evidence and having declared none. With only the read half, a signature can still quietly depend on a type it promises nothing about, which is exactly what this proposal exists to stop.

   So the FORWARD half is refused too, **at the call**. `build_op_scoped_dicts` makes an unsuppliable operation slot a SILENT ABSENCE on purpose, for a reason its own comment measures — 29 stdlib bodies declare a chain and never read it, so a slot nothing fills costs them nothing. `TypeValue` can never be one of those: `type_value()` is **nullary**, so no argument and no receiver names the type and the dispatching dictionary is the *only* carrier of the answer (§7 step 2, fact (a)). A body holding this evidence necessarily reads it through the slot, so an unfilled one is either an eval-time `Internal` death no handler can catch, or a clause that was pure noise. Neither is an absence worth keeping silent.

   **The leg is deliberately NARROW, and a control says so.** The same forward shape over a plain user spec — `requires TT[T = B]`, nothing to do with 065 — still loads. Operation-level requirement propagation is *not* checked in general, and that wider gap is real, pre-existing and not this proposal's to close; the acceptance row asserts both halves so the two cannot be confused later.
4. **WI-20260919-891QP** through instance contexts (§4); its two R541X rows flip to positive.
5. **WI-20260919-H20YY**.

## Open questions

1. **Inference from a body** — deferred by decision, not rejected. When it is taken up: an inferred clause is still a signature change a caller sees, so it wants a rule for WHERE it becomes visible (a declaration's printed signature, `anthill check` output).
2. **`Error.reify`'s `T1`** is the second consumer of a rigid-as-value, reading the frame channel rather than the body. Consistency says it needs the clause too (`catchIt[P](…) requires TypeValue[T = P]`); 3MV2C owns the decision, and until it is made the channel stays.
3. **Formers without a value reading.** An arrow type's effect row is not a value; `TypeValue` of `(Int64) -> Int64 @ {E}` with `E` rigid needs either an effect-row analogue or a refusal. Proposed: refuse at the read, naming the row, until a program needs it.
4. **Transients.** A `Type` value built per dispatch is a transient, and interned terms live for the KB's lifetime (CLAUDE.md's representation note; 3MV2C's 2026-09-18 feedback on `ground_type_params`). The lowering must build its result on the transient carrier, not intern one per call.
