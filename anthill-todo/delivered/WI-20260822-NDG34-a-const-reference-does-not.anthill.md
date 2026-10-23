## Attributes

- id: WI-20260822-NDG34-a-const-reference-does-not
- created: 2026-08-22T06:16:53Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-23T11:54:25Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `const` REFERENCE IN GOAL POSITION (`:- flag`) LOADS AND NEVER MATCHES, and under
`not(…)` that silence becomes a WRONG ANSWER: with `const flag: Bool = true`,
`rule p(1) :- not(flag)` answers 1 DEFINITE.

WHAT IS NO LONGER THIS TICKET'S. WI-20261001-KDMQS folded a const in every clause DATA
slot, rule-body goal arguments included, so the value-slot rows this ticket was filed
with now answer what their literals answer: `:- Int64.gt(nn, 3)` and `:- flag = true`
answer 1 (`wi_kdmqs_const_data_slot_test::a_const_in_a_rule_body_value_slot_is_its_value`,
and the `pfold` row of `wi_j38je_boolean_goal_test::what_the_condition_reading_cannot_yet_reduce`).
That also settled the old decision 1 (fold at LOAD, from a load-time value table, and a
host const through its `language rust` `const_map`; spec §5.9). KDMQS deliberately left
GOAL position unfolded (`ConstFold::Goal` in kb/load.rs), and that is what remains here.

MEASURED after KDMQS (`const flag: Bool = true`, `const off: Bool = false`,
`const nn: Int64 = 5`):
  rule p(1) :- flag                -> 0   should be 1
  rule p(1) :- off                 -> 0   correct, by accident
  rule p(1) :- not(flag)           -> 1   WRONG: a free proof
  rule p(1) :- not(off)            -> 1   correct, by accident
  rule p(1) :- base(2) | flag      -> 0   should be 1
  rule p(1) :- flag = true         -> 1   the repair, working since KDMQS
  rule p(1) :- nn                  -> 0   a non-Bool const goal, silently
  rule p(1) :- flag() = true       -> load error "flag.apply: expected known operation
                                       or arrow-typed variable, got unknown functor"

WHAT THIS TICKET MUST DECIDE:
 1. THE GOAL READING J38JE WITHHELD. `:- flag = true` is now a working repair, so `:- flag`
    can be REFUSED under §5.3's closed reading, or given the SEARCH reading directly: a
    Bool const at a goal slot read as `true` / `false`, which §5.3 already reads as
    success / failure (folding it at `ConstFold::Goal` would be the whole change). Decide
    which, and update §5.3's "not yet enforced" paragraph.
 2. A NON-BOOL const in goal position (`:- nn`) is silent where a non-Bool literal goal is
    a located load error (J38JE item 4). It should join that refusal.
 3. THE ARITY SPELLING. `flag()` is a different error from `flag`. One spelling must be
    the reference and the other must say so.

ACCEPTANCE: drive every row of the table above and assert the DEFINITE answer count, in
both polarities and under `not(…)` and `|`. Update the `pconst` row of
`what_the_condition_reading_cannot_yet_reduce` rather than deleting it. Say at each site
which rows fail on a back-out. cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-09-09T04:11:53Z — feedback — user

TWO MEASUREMENTS FROM WI-879, one that WIDENS the table and one that INVALIDATES a row of it. (1) A HOST-SUPPLIED CONST BEHAVES IDENTICALLY, so it is this ticket's and not a neighbour's. `const_map` (WI-889, 2026-07-31 — it predates this ticket) gives `Float.infinity` / `nan` / `pi` a value source that is a host function rather than an anthill body, and the split is exactly the same one measured here. Side by side, one program, today: `operation hbody() -> Bool = PartialOrd.gt(infinity, 1.0)` reached from a rule answers `true`, and `rule host_const(?r) :- Float.gt(infinity, 1.0, ?r)` answers a RESIDUAL — beside `const nn: Int64 = 5` whose `operation obody() -> Bool = Int64.gt(nn, 3)` answers `true` and whose `rule user_const(?r) :- Int64.gt(nn, 3, ?r)` answers a residual, with both literal controls answering `true`. Same eval-vs-SLD split, same direction, no difference between a host-backed const and a bodied one. IT DOES CHANGE DECISION 1, THOUGH, and the ticket's two options are not equally available for it: option (a) FOLD AT LOAD has to obtain the value at load time, and a host const's value comes from the runtime's own function at first demand (`force_const`, eval-side), so folding it at load means INVOKING a host function during the load — which the purity gate the option leans on (proposal 039 / WI-084) does not cover, because there is no anthill body to gate. Option (b) FOLD AT RESOLVE has no such problem. Whichever is chosen, say what it does for a const whose value source is the host's, and say it for the `language cpp` case too, where this runtime cannot call it at all. (2) ROW 3 OF THE TABLE HAS AGED — re-measured in the ticket's OWN spelling (2-ary goals, `p(1)`-shaped heads) today: `rule r1(1) :- big()` = 1 (unchanged, "1 FOLDS"); `rule r3(1) :- Int64.gt(nn, 3)` = **ONE NON-DEFINITE ROW**, where this ticket recorded **0** ("DOES NOT"); `rule r4(1) :- Int64.gt(5, 3)` = 1 (unchanged, control); `rule r5(1) :- flag = true` = 0 (unchanged). WI-879 is why: `builtin_cmp` used to return `BuiltinResult::Failure` for any operand pair it could not compare, and now returns an UNDECIDED delay with `truncated: true` — an unfolded const reference rides as a `Value::Node` that is not a literal, so it lands in exactly that arm. THE DEFECT IS UNCHANGED (the const still does not fold, and the rule still does not answer what the literal answers); what changed is the SHAPE of not answering, from a silent refutation to a withheld verdict. This ticket's acceptance says "drive every row of the table above and assert the ANSWER COUNT", so measuring row 3 against 0 would now be measuring a stale baseline — assert one non-definite row, and note that the count goes to 1 DEFINITE when the fold lands. NOTE ALSO THAT THE TABLE NOW HOLDS TWO FAILURE SHAPES: rows 3/4 go through `builtin_cmp` (WI-879's arm, residual) while row 5's `flag = true` goes through `PartialEq.eq` / `BuiltinTag::SemEq`, which WI-879 did not touch and which still answers 0. The acceptance should say which row expects which, or a single "answers nothing" assertion will pass for two different reasons.

### 2026-10-01T10:28:39Z — feedback — user

SCOPE CUT 2026-10-01 after WI-20261001-KDMQS (7ca64491), with the user's agreement: the value-slot rows are fixed there (a const folds in every clause data slot), so the description now holds only the GOAL-position question, re-measured on the KDMQS tree. New finding while re-measuring: :- not(flag) with flag = true answers 1 DEFINITE, a free proof. The previous description (decisions 1-3 and the original table) is in this item's git history before this change.

### 2026-10-23T11:54:17Z — feedback — claude

DELIVERED 2026-10-23 (commit ccfcf21b). A `Bool` const at a goal is the literal it holds, so the goal is the search that literal is.

THE DECISIONS. (1) The search reading, by J38JE's user decision that a Bool-valued expression in goal position is a condition. Folded at load from KDMQS's value table (literal body, another const, a `language rust` const_map host value). Measured, before -> now: `:- flag` 0 -> 1, `:- not(flag)` 1 -> 0, `:- base(2) | flag` 0 -> 1; the `off` rows answer 0 and 1 as before; `:- flag = true` 1 either way. A `Bool` const the table gives no value — a computed body, or a host value only a `language cpp` binding supplies — is refused at the goal with the table's reason, as in a data slot. A query evaluates it instead, and `?- not(ns.flag)` answers 0 (it answered 1). (2) A non-Bool const at a goal (`:- nn`, also under `not` and `|`) is refused, naming the const and its type, beside `:- 42`'s refusal. (3) `flag` is the reference. `flag()` is refused at a goal, as in a value slot and an operation body, and the refusal names the reference; not said of a function-typed const (`inc(3)` keeps the plain message). (4) User decision 2026-10-23: a fact or rule clause whose head names a const is refused at any arity. Such a clause was filed under the const's symbol: `rule flag :- true` beside `const flag: Bool = false` made `:- flag` answer 1.

ALSO FIXED, found while measuring. An enforced constraint's goal reads a `Bool` const: `forall ?x: item(n: ?x) -: flag` was reported violated by facts that satisfy it. A dotted const refused for its value in a rule-body data slot is one error; it added two cascade errors.

ROWS: wi_ndg34_const_goal_test (13 tests), each back-out measured at the file's head; J38JE's `pconst` row and KDMQS's `flag_goal` row now assert 1. Spec §5.2's bullet, §5.3, §5.9; proposal 039's delivery note.

LEFT OPEN. A non-Bool const in a constraint goal is not refused, and neither is a literal (`-: 42` reports the constraint violated): J38JE's goal-reading refusal walks rule bodies only. A query has no refusal channel, so `?- not(ns.nn)` answers 1, as `?- not(42)` does.

