## Attributes

- id: WI-20260923-ZBWMC-scan-sort-carrier-bindings
- created: 2026-09-23T20:45:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-24T09:41:19Z

- acceptance: cargo-test

- tags: typing

## Description

`scan_sort_carrier_bindings`' `provides` ARM IS DEAD: the WI-201 bare-spec sugar never narrows a carrier from a `provides` clause.

FOUND by WI-20260923-N3W68 (its #9 audit of the positional-binding fill) and REASONED FROM THE CODE, not yet driven by a program — so this ticket's first job is to reproduce it.

WHAT THE CODE SAYS. `Loader::scan_sort_carrier_bindings` (load.rs) pre-scans a sort's items for `fact Spec[…]` and `provides Spec[…]` and records `(spec, member) → carrier` for the WI-201 bare-spec sugar. Its `provides` arm lowers the clause with `sort_inst_to_value`, which returns a `SortView(base, …)`-headed term (WI-366). The arm's next gate — "only a SPEC lends carrier members": `matches!(kind_of(functor), Some(SymbolKind::Sort)) && !sort_has_constructors(functor)` — then reads the head `anthill.reflect.SortView`, which is an ENTITY, so every parameterized `provides` clause is skipped. A bare `provides Spec` carries no binding to record. So only the `fact` arm can ever record anything — and WI-20260917-S8JYF retired the `fact` spelling of a provision, which makes it worth asking whether the scan as a whole still has a producer.

WHAT TO DO. Reproduce first: a sort whose `provides Spec[Member = X]` should let the bare-spec sugar narrow a parameter to `X`, observed through a load verdict or a dispatch answer, against the same program in a spelling that does record. Then either
  * the narrowing is wanted: unwrap the view in the arm (`unwrap_spec_view` — base from `pos[0]`, the bindings named, positionals through `KnowledgeBase::positional_param_slots`) before the spec gate; or
  * it is not: delete the arm, and say at the scan why a `provides` clause does not lend carrier members.

ACCEPTANCE: a test that DRIVES the chosen behaviour (the narrowing observed, or its absence pinned where a program would notice), its back-out stated at the test; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-24T09:41:18Z — feedback — user

DELIVERED. REPRODUCED first: under `provides Store[State = WIS]`, `count(s: Store.State) -> Int64 = s.n` was refused (`?State.n … declare no 'n'`) while `fact Store[State = WIS]` (the spelling S8JYF retired) loaded — the provides arm gated on the SortView wrapper's head, so only the retired fact spelling narrowed. CHOSEN: the narrowing is wanted (WI-201 / 066 `where`-block members need it), and the fact arm is DELETED — a fact is not a provision. The scan now reads `provides` clauses only, decodes via `unwrap_spec_view_value`, and classifies each (spec, member) as one nameable carrier / several / unnameable. A /code-review at max (10 finders, 8 verifiers, sweep) found that making the arm live exposed the rest; USER DECISION (2026-09-24): ambiguity is LOUD and whole-sort. Fixed inline: (1) carriers must be spellable — no logic var anywhere, no operation, a type parameter only if in scope (was head-only: `State = Other.X` loaded and died at run time; `List[T = ?]` refused a program that loaded); (2) several bindings are an ambiguity, never a source-order pick (a third provision had re-admitted a dropped one); (3) new LoadError::AmbiguousSpecMember from a post-load `check_bare_spec_narrowings` over the provision relation, so a binding in another entry/file refuses the narrowing (059); (4) every scope installs its own carrier block: `namespace <Sort>` entries narrow from their own provisions, a plain nested namespace no longer inherits; (5) the `kind_of` spec gate removed (order-dependent, redundant); (6) the pre-scan's lowering is memoized for `load_provides_clause` (a described binding had emitted two DescriptionInfo facts); (7) duplicate named bindings in a spec clause refused (`duplicate_named_binding`); (8) `provides_block_identity` read the SortView head, filing `provides Stack[T = Int64] language rust` under anthill.reflect.SortView — fixed. Deleting the fact arm also made sort-body facts load like namespace ones (the pre-scan's memoized context-free conversion had skipped WI-716 none-fill and B8ESG) — pinned. Tests: wi_zbwmc_provision_narrowing_test (29 rows, 11 back-outs measured over the whole wi_tests binary and per arm, ledger in its module doc); wi201 rows migrated to provides, its conflict row now asserts the ambiguity; a parameterized binding-block row. Spec: kernel-language §5.4 now states the sugar, the narrowing and the ambiguity. Filed (user-approved) for pre-existing finds: WI-20260924-F3FYJ, WI-20260924-0S3YG, WI-20260924-F8PYZ. Full workspace green via rustland/scripts/test.sh (wi_tests 5 039 passed, 3 ignored).

