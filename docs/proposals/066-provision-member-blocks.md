# 066: Provision blocks — a conditional provision's members are written inside it

## Status: DELIVERED (2026-09-19, WI-20260919-1Z3E7) — the scoping rule, the syntax, the `Pair` migration. Decided in discussion on WI-20260918-CKD4J, including the keyword (`where`, §3). The per-provision LAYOUT (§2's "possible later") is the next step, agreed 2026-09-19.

## Amends: [058](058-modular-instances.md) §3.8 (conditional provisions — WHO may read a condition) and §4 (syntax). `docs/kernel-language.md` §8.7 ("Conditional provisions").

## Tracked by: WI-20260919-1Z3E7.

## Relates to: WI-20260918-CKD4J (derived conditional `Eq`/`PartialEq` rows, which this makes safe to add to a carrier with existing bodies), WI-869 (the per-provision dictionary chain and its strictness mask), WI-822 (operation-level `requires` slots), `stdlib/anthill/prelude/pair.anthill` (the only conditional provider in the corpus).

## The problem, in one paragraph

A `provides X[S] :- g1, …, gn` tail conditions ONE provision, but today every body the carrier owns is type-checked as if `g1 … gn` were sort-level `requires`. The frame layout is per sort (`provider_dict_chain`), and the typer installs that whole chain as each body's enclosing scope. Dispatch is already per provision (a sibling provision's slot is filled `Unavailable` and refused when read, WI-869), so conditional provisions are SOUND. But a body can USE a condition it does not own, and then the condition silently becomes that operation's requirement, charged to every caller and blamed on the carrier. MEASURED (CKD4J, 2026-09-19): in `sort Box3 { … provides PartialEq[Box3] :- PartialEq[T]; operation inner(b: Box3, c: Box3) -> Int64 = … eq(x, y) … }`, `inner` declares nothing and implements no `PartialEq` member, yet it loads. The call `Box3.inner(box3(v: fe(1.5)), …)` is then refused with "requirement `PartialEq[T = FE]` of `Box3` cannot be supplied for call to `Box3.inner`". The requirement exists in no definition.

## Why it cannot be fixed on the operation, nor by inference

The condition must be stated somewhere, and there are two candidate places. Both are wrong.

- **On the operation** (`operation eq(…) requires PartialEq[A] = …`): the member no longer conforms to the spec's signature. `PartialEq.eq` has no such requirement, and a member with an extra `requires` is not an implementation of it.
- **Nowhere, with membership inferred** (a body sees the conditions of every provision it implements by name or binding): the body reads evidence that its own definition never states. It type-checks against a contract that is visible only by reading every `provides` line of the sort and knowing which spec declares which member.

The condition belongs to the provision. So the operations that rely on it are written inside the provision's own definition, which is a new definition form and not an operation.

## 1. The rule

**A provision's `:- goals` are in scope exactly for the operations written inside that provision's block.** Every other body of the carrier sees only the sort-level `requires` and its own operation-level `requires`, as if the provision had no conditions.

```anthill
enum anthill.prelude.Pair
  sort A = ?
  sort B = ?
  entity pair(fst: A, snd: B)

  provides PartialEq[Pair] :- PartialEq[A], PartialEq[B] where
    operation eq(a: Pair, b: Pair) -> Bool =
      match a case pair(al, ar) -> match b case pair(bl, br) ->
        if PartialEq.eq(al, bl) then PartialEq.eq(ar, br) else false
  end

  provides Eq[Pair] :- Eq[A], Eq[B]          -- no members: the one-line clause stays
  …
end
```

- **A member conforms to its spec's signature unchanged.** The block supplies the conditions and the operation adds nothing.
- **A block member is still an operation of the carrier** (`Pair.eq`), found by the same name/binding rules as today. Only its typing scope changes.
- **The one-line clause stays**, and means a provision with no members of its own. Such a provision is backed by inherited defaults or builtins; the derived structural `Eq`/`PartialEq` of CKD4J is the main case. Its conditions reach no body.
- **Using a condition outside its block is a load error** of the usual kind ("nothing in scope provides `PartialEq[T]`…"). The repair is to move the operation into the block, or to give it its own `requires` if it is a helper that is not a spec member.

## 2. What does not change

- **Dispatch.** WI-869's per-provision strictness mask already fills a sibling provision's slots `Unavailable`. The block makes the static check agree with that, and adds no runtime mechanism.
- **Frame layout.** Still per sort: sort-level `requires`, then every provision's conditions, then an operation's own `requires`. What changes is which of those slots a body may resolve against, not where they are. (A per-block layout is possible later, and is not needed for this rule.)
- **The call-site side.** Measured (CKD4J): a non-member operation called at an element that cannot satisfy a condition is not charged for it, whether or not the operation reads its own `requires` slot.

## 3. Syntax

A bare `provides X :- g` followed by operations and `end` would be ambiguous inside a sort body: the `end` could close the block or the sort. So the block opens with **`where`** (user decision, 2026-09-19; the word is unused elsewhere in the grammar). The body takes the same two forms as a sort body (`_body_sort`):

```anthill
provides PartialEq[Pair] :- PartialEq[A], PartialEq[B] where
  operation eq(a: Pair, b: Pair) -> Bool = …
end

provides PartialEq[Pair] :- PartialEq[A], PartialEq[B] where {
  operation eq(a: Pair, b: Pair) -> Bool = …
}
```

- **The block admits operations only**, and each must be an operation the provided spec itself declares (§5 Q2, decided: a helper goes outside with its own `requires`). A provision's facts, rules and nested provisions are written as they are today; widening the item set is a separate decision.
- **In a sort or enum body only.** A namespace body and a `provides … language …` binding block have no carrier to own the operations; a block there is a parse error.
- **`where` without `:- goals` is legal**, and means a provision whose members are grouped with it but which has no conditions to scope. It reads the same as writing the operations outside, and exists so that adding a condition later does not move code.
- **Not the proposal-038 block.** `provides Spec language L … end` is a standalone binding block that opens the carrier's scope. The two share `provides … end`, but the new block has `where` where that one has `language`, so they never collide.

## 4. Migration

`pair.anthill` is the only conditional provider in the corpus. `eq` moves into the `PartialEq` block. `compare` is the member of `WeakOrd` and moves into that block. The `Eq`, `PartialOrd` and `Ord` provisions keep the one-line form.

## 5. Open questions — answered

1. **One operation serving two provisions.** ANSWERED (measured, 2026-09-19): `Ord` declares no operation — it is a conversion to `WeakOrd` — so `compare` is only ever dispatched as `WeakOrd.compare`, with `WeakOrd`'s slots filled, including through a body that `requires Ord[T]`. Written once, in the `WeakOrd` block. The case the question feared is real only for an operation that serves two specs DECLARING the same member; there the dispatch through the other spec leaves the block's slots unfilled and the read is refused at eval (WI-865's message), pinned in `wi869_per_provision_conditions_test::a_member_dispatched_through_another_spec_is_refused_at_eval`.
2. **Helpers.** DECIDED: the block holds the provided spec's own members only (a loud load error otherwise); a helper states its own operation-level `requires` (supported since CKD4J's sub-goal fix), which answers both a component compare and a whole-carrier compare whose condition is a sub-goal.

## 6. Implementation (WI-20260919-1Z3E7)

- **Grammar**: `provides_members` on `provides_clause`; the converter flattens a block into carrier operations marked with `Operation::provision`, refusing it outside a sort/enum body.
- **Loader**: one `anthill.reflect.ProvisionMemberInfo(operation, provided)` fact per member; the spec-membership check.
- **Typer**: `ProviderDictChain::hidden_from_body` marks the condition slots a body may not resolve against; the mask rides on the body's `DictChain` (`hides`/`hidden`) and in `ResolutionScope::hidden`, and every cover decision — the scope lookup, the defer triggers, the forwarding strategies, the refusal explainer — skips a hidden slot, while every layout reader sees the chain unchanged. A refused spec-op call whose evidence is a hidden condition gets its own diagnostic naming the block (`TypeError::ProvisionConditionOutOfScope`).
- **Migration**: `pair.anthill` (`eq` in the `PartialEq` block, `compare` in the `WeakOrd` block), and the conditional fixtures of `wi869`, `wi1093`, `nar1x`.
