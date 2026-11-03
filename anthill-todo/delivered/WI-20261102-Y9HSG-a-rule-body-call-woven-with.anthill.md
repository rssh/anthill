## Attributes

- id: WI-20261102-Y9HSG-a-rule-body-call-woven-with
- created: 2026-11-02T06:52:51Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-02T22:48:17Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

A RULE-BODY CALL WOVEN WITH ITS DICTIONARY DOES NOT RUN A DEFAULT BODY ITS PROVIDER INHERITS: the call flounders with the dictionary in hand. Found on WI-20260925-SHED7 step 3 (proposal 067; docs/brainstorms/fillable-collection-landscape.md §4.1, `fromList`).

MEASURED on 5476eece, a copy of `PersistentCollection` with a default `fromL` and no `requires`:

  sort Pc2
    sort C = ?
    sort Element = ?
    operation ins(c: C, elem: Element) -> C
    operation emp() -> C
    operation fromL(xs: List[T = Element]) -> C =
      match xs
        case nil() -> emp()
        case cons(x, rest) -> ins(fromL(rest), x)
  end
  sort Bag[T]   -- bnil, badd(e: T, rest: Bag[T = T]); provides Stream[T = T, E = {}] with its splitFirst;
                -- provides Pc2[C = Bag[T = T], Element = T] with ins and emp, and no fromL of its own
  sort Sat[C]
    requires Pc2[C = C, Element = Bit]
    rule model(vs: C) :- vs <=> Pc2.fromL([?p, ?q, ?r]), <tiny-sat's neg/or2 clauses>
  end

`Sat[C = Bag[T = Bit]].model.takeN(100).length()` loads and raises `relation_floundered(goals: [unify(bnil, apply_within(fn: fromL, args: [cons], requirements: [Dictionary(impl: Bag)]))])`: the woven call's dictionary is bound, to `Bag`'s, and the call is never reduced. `Bag` supplies no member; the default body is what the provision runs (kernel-language §8.7, "Defaulted operations … carry over automatically"), at the instance the dictionary names (§5.2, "A spec's default body is not such a dispatch"). An operation body's call of such a default answers (`Pc[C = Bx].fromL([1, 2, 3])` = `badd(e: 1, rest: badd(e: 2, rest: badd(e: 3, rest: bnil)))`, measured). Related: WI-20260926-DSEXA item 1 reads a concrete dictionary with no supplier for the member as UNREDUCED; an inherited default is a supplier.

CONTROL: the same `fromL` declared without a body and written by `Bag` answers 2 models.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): the program answers 2 models; `Sat[C = Bag[T = Bit]].model(badd(t, badd(t, badd(f, bnil))))` answers 1, `(t, t, t)` nothing; the body-less control unchanged.

