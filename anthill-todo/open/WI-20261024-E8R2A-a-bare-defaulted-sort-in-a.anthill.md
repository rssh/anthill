## Attributes

- id: WI-20261024-E8R2A-a-bare-defaulted-sort-in-a
- created: 2026-10-24T21:17:14Z

- status: Open
- status_agent: user
- status_at: 2026-10-24T21:17:14Z

- acceptance: cargo-test

- tags: typing

## Description

A BARE DEFAULTED SORT IN A CLAUSE'S BINDING VALUE TAKES NO DEFAULT. Found during WI-20261024-DK83Q (user: file, 2026-10-24).
MEASURED (2026-10-24, on 05ee1554 and 2f9c0750 alike), over `sort Cfg[T = Int64] { entity cfg(v: T) }` and `sort Store { sort State = ?  operation peek(s: State) -> Bool }`:

  sort FileStore
    provides Store[State = Cfg]
    operation peek(s: Store.State) -> Bool = true
    operation count(s: Store.State) -> Int64 = s.v
  end
  operation go() -> Int64 = FileStore.count(cfg(v: 7))

is refused, "count.return: expected Int64, got s.T": the sugar narrows `Store.State` to `Cfg` with `T` left open, where in a type position `Cfg` is `Cfg[T = Int64]` (proposal 069: a written type that leaves a parameter out takes its default, wherever the application stands). In a carrier provision too: `provides Rel[A = Self, B = Cfg]` with the member `mix(a: Self, b: Cfg)` is refused as a member that does not fit, its `b: Cfg[T = Int64]` against a spec `B` read as any `Cfg`. `Loader::sort_binding_to_value` fills no default — neither its `Simple` arm (`clause_binding_as_written`) nor its `Parameterized` one (`assemble_binding_value`) — where `type_expr_to_child_inner` does (`fill_parameter_defaults`).
ACCEPTANCE (cargo-test via rustland/scripts/test.sh): `go` runs, answering 7, and the `Rel` provision loads with its member; a binding written `Cfg[T = ?]` stays open (069's opt-out); `wi_dk83q_identical_substitution_test::a_defaulted_slot_left_out_is_no_family` still holds.

