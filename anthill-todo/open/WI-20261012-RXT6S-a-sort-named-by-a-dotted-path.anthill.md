## Attributes

- id: WI-20261012-RXT6S-a-sort-named-by-a-dotted-path
- created: 2026-10-12T06:15:41Z

- status: Open
- status_agent: claude
- status_at: 2026-10-12T06:15:41Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

A SORT NAMED BY A DOTTED PATH IS NOT A TYPE VALUE — over `sort Outer { sort Inner { operation deep() -> Int64 = 21 } }`, `namespace lib.t { sort Far { operation k() -> Int64 = 9 } }` and `operation nm(t: Type) -> Int64 = 1`, in an operation body `nm(Outer.Inner)`, `nm(lib.t.Far)`, `nm(..lib.t.Far)`, `let t = Outer.Inner`, `(Outer.Inner).deep()`, `(lib.t.Far).k()` and the result `operation ty() -> Type = Outer.Inner` are refused with "type mismatch in Inner.name: expected resolved name, got unresolved" — for the namespace path one such error a segment, `lib.name`, `t.name`, `Far.name`. In a rule body `?x <=> (Outer.Inner).deep()` and `?x <=> (lib.t.Far).k()` are refused the same way (`Outer.name`, `lib.name`). The companion calls `Outer.Inner.deep()` and `lib.t.Far.k()` answer 21 and 9; the imported bare name answers (`import lib.t.Far`, then `nm(Far) + (Far).k()` is 10); so does the dotted name as an entry of a bracket (`nm(Bx[V = Outer.Inner]) + (Bx[V = lib.t.Far]).one()` is 2) and under a bracket of its own (`(Outer.Inner[W = Int64]).deep()`, both bodies). Measured 2026-10-12 on 711c2289; found with WI-20261008-A3FY2.

WHY. A dotted name in a term position is a minted `field_access` chain. In the operation-body walk the chain has a ladder (`visit_load`: the `field_access` re-routes and `try_qualified_const_ref`) with a rung for a local root, a rule citation, a const and a relation prefix, and none for a chain whose whole name resolves to a sort: it is built as the application of `field_access`, and the typer reads each segment as a bare name. The classification proposal 055 §2 asks for (`Loader::bare_name_denotes_type`, in `push_leaf_occ`) is asked of a leaf only, where design 055 §2 counts `name` — a dotted one too — as the bare nominal type. A rule body follows the operation body: `Loader::written_type_receiver_occurrence` reads a bare name or a bracket.

WHAT. Read a dotted chain whose whole name resolves to a sort as that sort's type value: a rung of the ladder after the local pass, placed against the rule citation and the const by measurement, and the same reading of a rule body's dot receiver. Decide it beside WI-20261008-R653S, which asks what a paren-less `Sort.member` is in an operation body — `Outer.Inner` is that spelling with a sort for the member. A free-standing entity named by a path, and an eponymous sort, keep the reading their bare names have.

CONTROL. One fixture per row: an argument at a `Type` parameter, a `let`, a result, a parenthesized receiver in an operation body and in a rule body, each for a nested sort, a sort of another namespace and an absolute name, beside the imported bare name. Fences that pass either way: the companion calls; a dotted rule citation (`ns.rel` is the relation); a dotted const (`Float.infinity`); a field of a local value (`p.x`); a dotted name in a rule's data slot (`fact holds(ns.rel)` and the goal `holds(ns.rel)` stay one term). `wi_a3fy2_rule_body_type_receiver_test::a_dotted_sort_name_is_no_written_type_in_either_body` pins today's refusal and turns. Say which rows fail with the change backed out.

DONE WHEN: a sort named by a path is the type value its bare name is, in every position above and in both bodies; the gate is green.

