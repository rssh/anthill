## Attributes

- id: WI-20261013-WF14Z-068-c1b-a-rule-variable-is
- created: 2026-10-13T08:03:12Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:12Z

- acceptance: cargo-test

- depends_on: WI-20261013-GGXCX-068-c1a-design-the-clause

- tags: proposal-068, typing

## Description

068 C1b — A RULE VARIABLE IS TYPED ACROSS ITS CLAUSE: by the goals that take it, both sides of `<=>`, a constructor's result and the head's written bound, tied to the enclosing sort's parameters. Part 2 of WI-20260926-7D48J, implementing C1a's decisions 1 and 2. ROWS, each measured on the ticket that found it: WI-20260925-0RRQP's `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)` inside `sort Box[T] requires O: WeakOrd[T]` — `?x` is at `Box`'s `T` and the inferred condition routes to `O`; a head typed `?a: Int64` reaches the call's element (7D48J note 2026-10-08, row 3); a dot on a rule variable whose type the clause determines is evaluated — over `sort Cnt { entity cnt(n: Int64); operation bump(c: Cnt) -> Int64 = … }`, `?c <=> cnt(n: 4), ?x <=> ?c.bump()` answers 5 as `Cnt.bump(?c)` does, and so does `rule inner(?c: Cnt, ?x) :- ?x <=> ?c.bump()` called with `cnt(n: 4)`; `?c.bump() = 5`, `p(?c.bump())` and the goal `?c.isPos()` answer as their written-call twins (note 2026-10-11, A3FY2); a field of a typed head parameter is a receiver — over `entity P(t: Int64)`, `rule r0(?p: P, ?x) :- ?x <=> (?p.t).abs()` and the sigil-free `rule r0(p: P, ?x) :- ?x <=> (p.t).abs()` answer 3 for `P(-3)` (note 2026-10-12, RXT6S). ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven): each row answers as stated, each back-out named at its site. CONTROLS: an operation body's typing unchanged; classic-mini unchanged.

## Changes

### 2026-10-13T10:07:30Z — feedback — claude

FROM WI-20260925-0RRQP (2026-10-13, built on 33ffa2a4, not committed when this was written). TWO OF THIS TICKET'S ROWS ANSWER NOW, each a row of wi_0rrqp_clause_typed_through_constructor_test: 0RRQP's own — `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)` in `sort Box` is 4 / -4 through `orderOf`'s `O`; and the dot on a variable the clause types — `?c <=> cnt(n: 4), ?x <=> ?c.bump()` binds 5, and `?c.nosuch()` there is a load error, 'no such member (dot dispatch)'. What types the variable is a constructor's application unified with the declared type of the position it fills; an operation call's result is still not read (`?r <=> Util.sign(?a, ?b)` leaves `?r` untyped), and neither is a head's written bound (`rule h1(?a: Int64, ?x) :- ?x <=> ?a.abs()` was not re-measured). A ROW THIS TICKET DOES NOT HOLD YET: a dot on a variable whose type is a VARIABLE only a citation fixes. In `sort Box { sort T = ?; requires O: WeakOrd[T]; entity box(a: T, b: T) }`, `rule orderDot(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), ?c <=> ?x.compare(?y)` binds `?c` to the term `1.compare(5)` — uncited, and cited as `orderDot(p).head.c` from a member operation under `O = Descending` and under `O = Ascending` — where the written call `WeakOrd.compare(?x, ?y, ?c)` in the same place is 4 / -4. The clause types `?x` at `t`, no sort, so the dot is not dispatched at load and stays data; this ticket's wording covers a variable 'whose type the clause determines'. The same dot in the member operation (`match p case box(a, b) -> a.compare(b)`) is 4 / -4.

### 2026-10-21T15:29:36Z — feedback — claude

FROM WI-20260925-0RRQP (2026-10-21, not committed when this was written): a citation now opens each clause variable its arguments leave unfixed INSIDE a free column's type as an unknown (`close_unfixed_clause_vars`, user decision 2026-10-21), so `tag.head.x` over `rule tag(?x: Wrap[T = ?t]) :- holder(h: ?x)` is refused returned as a `Wrap[T = Colour]`. A column whose WHOLE type is a variable is left as it was — a stated limit there, `a_column_nothing_types_is_read_at_any_type`: `rule untyped(?x) :- tag(?x)` read back as an `Int64` loads and answers a `wrap`. MEASURED: closing such a column too refused 51 rows of the workspace in 13 modules (wi_0rrqp 16, wi_p7vp4 14, wi_5g28a_rule_dictionary 7, wi_prva2 3, …), nearly all one shape — a column a call at goal position fills, `WeakOrd.compare(?x, ?y, ?c)` cited `….head.c` returned as `Int64`, refused 'expected Int64, got ?c' — because the clause typing does not read an operation call's result (this ticket's 'the goals that take it'). Once this ticket types those columns, the whole-column case can be closed as the nested one is, and the 51 rows are its measurement.

### 2026-10-21T18:15:28Z — feedback — user

C1a DECIDED (WI-20261013-GGXCX, user 2026-10-21; docs/design/068-implementation.md §6.2 lists every row): THIS PART BUILDS DECISIONS 1, 2 AND 3's C1b CLASSES. (1) A clause is typed as a whole, one substitution in any order of its goals, from the head's bound (written or inferred), a constructor's fields and result, an entity goal's fields, an operation call's parameters and result (value slot and `f(args, ?r)`), a RULE GOAL'S COLUMNS — the callee's, written or inferred, opened fresh per goal, relations typed callee before caller, a self-call reading its own columns as one type — and a field read; the enclosing sort's parameters (a named requirement's slot included) are clause variables a citation fixes, rigid in the body. (2) Every entity construction in a rule or a fact is typed against its fields (body, head, fact); a relation column whose clauses have no join is a rigid 'some type', and a test (`domain(?v, T)`, `<=>` against a construction or literal, a head's bound) narrows it, while a demand (call argument, dot, field read) needs it typed. (3) The C1b load errors, each counted on 068-implementation §1.2's corpus and the suite BEFORE it refuses (the count recorded in §6.2): construction vs field; a variable whose positions disagree; head bound vs body; rule goal vs the callee's column; a demand on an un-narrowed 'some type'; a member missing on a typed receiver; the sort's parameter fixed by the body. FLIPS OWED in wi_0rrqp_clause_typed_through_constructor_test: a_body_that_fixes_a_sorts_parameter_is_read_as_before (refused), a_constructor_that_does_not_fit_its_position_pins_nothing (refused), a_slot_the_arguments_own_type_says_is_not_read (-4), a_column_nothing_types_is_read_at_any_type (refused; 0RRQP's 51 rows its measurement); SHED7's `Sat.model` with `vs <=> [...]` refused, its `fromList` repair loading.

