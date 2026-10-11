## Attributes

- id: WI-20261011-7G99A-is-unit-only-in-one-place-the
- created: 2026-10-11T20:14:19Z

- status: Open
- status_agent: user
- status_at: 2026-10-11T20:14:19Z

- acceptance: cargo-test

- tags: typing

## Description

`()` IS `Unit` ONLY IN ONE PLACE — the value written in an operation body. Everywhere else it is a tuple of no components, a different type, and a `Unit` slot refuses it. User, 2026-10-11: `()` is `Unit` universally. Measured 2026-10-11 on b3f238c0; found while delivering WI-20261011-3HN0N.

THE PROGRAMS, each its own namespace importing `Int64`, `Unit`. (1) THE TYPE AND THE VALUE DISAGREE IN ONE OPERATION: `operation f() -> () = ()` is refused 'type mismatch in f.return (op-return): expected (), got Unit'. (2) `operation f() -> Unit = ()`, `operation g(u: ()) -> Int64 = 4`, `g(f())` is refused 'g.u (op-arg): expected (), got Unit'; with the two types swapped, 'expected Unit, got ()'. (3) A FACT: `sort U { entity u(v: Unit, n: Int64) }`, `fact U.u(v: (), n: 4)` is refused 'u.v (entity-field): expected Unit, got TupleLiteral'. (4) A GOAL: `rule value(?r) :- U.u(v: (), n: ?r)` is refused 'u.v (entity-field): expected Unit, got ()'. (5) WHAT AN EQUATION LEAVES IN A RULE BODY'S OWN TERM: `sort Box { entity mk(v: Int64); operation nothing(b: Box) -> Unit; rule nothing(?b) <=> () @[simp] }`, `operation takes(u: Unit, n: Int64) -> Int64 = n`, `rule value(?r) :- ?r <=> takes(Box.mk(4).nothing(), 4)` is refused 'value.body (rule): expected Unit, got ()', where the operation-body twin `takes(Box.mk(4).nothing(), 4)` runs to 4. WHAT LOADS: `operation mk() -> U = U.u(v: (), n: 4)`; `operation same() -> Bool = () = ()`; `f([(), ()])` at `List[T = Unit]`; a plain relation, `rule holds(()) :- true` with the goal `holds(())`.

MECHANISM, as far as read. Four readers answer 'what is the type of a tuple with no components', and one says `Unit`. `check_tuple_literal_constructor` (typing/constructor.rs), which types the constructor node an operation body writes, returns `Unit` for no components. The literal node of a rule's own term is typed by `TypeBuildFrame::TupleLit` (typing/build.rs), which builds `named_tuple_value` of no fields. The structural value-type reader (typing/value_type.rs, `tuple_type_denoted` in node_occurrence.rs), which the rule-body walk's declared-slot check reads an argument through, builds the same for either node — (5) is refused with the reading of WI-20261011-3HN0N made everywhere, measured. The fact head's field check names the literal's entity, `TupleLiteral`. And a type written `()` is the tuple type of no fields, which neither `unify_types` nor `types_compatible` relates to `Unit`. Not measured: eval builds `Value::Tuple` with no components for `()`, and `Value::Unit` is another carrier — whether the two compare equal, and which a host operation returning `Unit` gives.

WHAT. One type and one value: the tuple of no components IS `Unit`, as a written type, as a literal in every text (an operation body, a fact, a goal, a rule's own term, what an equation leaves there), and as the value eval builds. Decide first, with the user, where it is made one — where the tuple type of no fields is built, so every reader agrees by construction, against a reading at each of the four — and what kernel-language.md says (§4.5 tuple sorts; the spec is changed only after that discussion).

CONTROLS. A row per program above: (1)–(5) are refused today and load, (3) and (4) with the fact matching the goal and answering 4. What must not move: the operation-body rows of wi_3hn0n_tuple_on_rhs_test (an_empty_tuple_on_the_right_hand_side_is_unit, a_lambda_in_a_rule_body_returns_the_unit_an_equation_leaves) and a tuple of one or more components, whose type is its own. ONE ROW TURNS BY DESIGN: wi_3hn0n_tuple_on_rhs_test::a_rule_bodys_own_empty_tuple_is_typed_as_before pins (4)'s refusal as the control of 3HN0N's boundary — a rule body's own term is not read as an operation body's. With `()` typed `Unit` there, that row is rewritten to its positive, and the boundary keeps one control, wi285_unrec_test::collection_literal_frames_assemble_types; say at `visit_type`'s literal arm whether the boundary still has a behaviour to hold.

