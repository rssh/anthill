## Attributes

- id: WI-20261102-ME8WR-a-spec-s-default-body-that
- created: 2026-11-02T22:55:36Z

- status: Open
- status_agent: claude
- status_at: 2026-11-02T22:55:36Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A SPEC'S DEFAULT BODY RUNS ITS RECEIVER-LESS SIBLING AT THE SPEC ITSELF WHEN THE BRACKETED CALL'S INSTANCE IS NOT RESOLVED, and the instance of a two-parameter spec is resolved only when every parameter is fixed at the call AND named by a body-less member's signature. The call then gets no instance dictionary (no `__req_self`), so `emp()` inside the default runs `Pc2.emp`'s missing body — in an operation body as in a rule. Found delivering WI-20261102-Y9HSG.

MEASURED on 02de8910, the same on ee37ed91 (before Y9HSG):

  sort Pc2
    sort C = ?
    sort Element = ?
    operation emp() -> C
    operation both() -> C = emp()
  end
  sort Bag
    entity bnil
    provides Pc2[C = Bag, Element = Int64]
    operation emp() -> Bag = bnil()
  end
  rule rBoth(?n) :- ?n <=> Pc2[C = Bag, Element = Int64].both()
  operation opBoth() -> Bag = Pc2[C = Bag, Element = Int64].both()

- `opBoth()`, run as a program, dies "operation has no body: Pc2.emp"; `rBoth(bnil())` raises relation_floundered(unify(bnil, both)).
- Add a body-less member naming `Element` (`operation one(e: Element) -> C`, supplied by `Bag`): both answer `bnil` — 1 (the rule only since Y9HSG).
- With that member, leave `Element` out of the bracket (`Pc2[C = Bag].both()`): both fail again, though `Bag`'s one provision of `Pc2` decides `Element`.
- Fix `Element` by an argument instead (`both(xs: List[T = Element]) -> C = emp()`, `Pc2[C = Bag].both([1])`): it fails with `emp` the only body-less member, and answers 1 once `one(e: Element)`, `size(c: C) -> Int64` or `ins(c: C, elem: Element) -> C` is declared and supplied — `size` names no `Element`, so the second condition is not simply "named by a member"; what each of them adds to the provision is the question.

The bracketed call is classified `ConcreteApplyWithin { …, resolved_tree: None, frame: Absent }` where it fails (traced on the `requires Unit[T = Element]` variant of `both`, the first shape found), and `{ resolved_tree: Some(Leaf { impl_sort: Bag }), frame: Dict(…) }` where it answers. A one-parameter spec (`Mk { sort C = ?; e() -> C; viaDefault() -> C = e() }`, wi_shed7_default_body_sibling_test) answers with no other member.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): the program above answers `bnil` in an operation body and in a rule; so does `Pc2[C = Bag].both()` (the provision completes `Element`) and the argument form with `emp` the only body-less member; a second provider builds its own value; a default with a `requires` of its own (`both() -> C requires Unit[T = Element]`, reading `Unit.unit[T = Element]()`) answers too — the resolver's classified route then owes it the op-scoped stamps after the dictionary and the derivation of those it cannot read (WI-20261102-Y9HSG left such a callee on the stamps alone: `DictionaryOwed::OwnSlots`, kb/resolve.rs; `spec_op_requirement_at_member_test`'s two rule-body rows). CONTROLS: the shapes that answer today are unchanged.
