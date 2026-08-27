## Attributes

- id: WI-20260826-VPEWK-a-rule-body-operand-does-not
- created: 2026-08-26T16:56:10Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T06:02:09Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A rule-body OPERAND does not reduce a HOST-IMPLEMENTED operation, while the same call at a GOAL position does — one call, two positions, two answers, and nothing states the asymmetry.

THE GAP, DRIVEN. All rows measured through `anthill query` on a rule body, in one file, on the built tree.

  goal      :- Bool.and(true, true)                              1 solution
  goal      :- Bool.and(true, false)                             no solutions
  operand   :- Bool.and(true, true) = true                       NO SOLUTIONS   <- the gap
  operand   :- bodied() = true      (operation bodied() -> Bool = true)     1 solution
  operand   :- bodiedF() = true     (operation bodiedF() -> Bool = false)   no solutions
  operand   :- viaHost() = true     (a BODIED op whose body calls Bool.and) 1 solution

So the value-slot evaluator EXISTS and computes correctly — `reduce_operand` (WI-482/WI-483), the single pipeline shared by `eq` / `cmp` / `arith` / `unify`. What it declines is a BODY-LESS operation. `anthill.prelude.Bool.{and,or,not}` are declared body-less and backed by host functions (`eval/builtins.rs:91-93`), so they land in the declined class; `viaHost` is the same computation one level down and answers, which is what says the host function itself is reachable and only the OPERAND POSITION is not.

WHY THE TWO SIDES DISAGREE. The goal side asks `op_reducible_in_rule_body` = `op_body_node(f).is_some() || is_interpreter_mapped_op(f)`; the second supplier is WI-20260822-J38JE's, added for exactly this reason — before it "a host-implemented operation was callable from an OPERATION BODY and inert in a RULE BODY, for no reason anyone had stated". The operand side asks `reduce_op_value(.., dispatch_body_less: false)`, i.e. a BODY and nothing else. J38JE fixed one position and the other kept the old question.

WHAT THE FLAG IS PROTECTING, so a fix does not delete it. `reduce_dispatched_goal_call`'s doc states it: an operand is a term a RULE WROTE, and a body-less spec op there may be SYMBOLIC ALGEBRA rather than a computation. `anthill.prelude.Set`'s `insert` / `empty` are the named case — parametric parent, no body, a real signature, and the terms the membership rules resolve over. Dispatching them would reduce DATA, which is the same failure as the five wi616 regressions `is_unreduced_op_call` records, reached through the other door.

THE SEPARATOR IS EXACT, AND IT IS THE PREDICATE THE GOAL SIDE ALREADY USES. `is_interpreter_mapped_op` answers TRUE for `Bool.and` (registered at `eval/builtins.rs:92`) and FALSE for `Set.insert` (registered nowhere — zero `register_if_present` entries under `anthill.prelude.Set`). Driven, same file, both arms:

  :- Bool.and(true, true) = true                             no solutions   (host-mapped, wrongly declined)
  :- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1) 1 solution     (symbolic, correctly left as DATA)

That second row is the CONTROL a fix must keep green, and it is the whole reason the gate cannot simply become "dispatch body-less ops too".

DIRECTION (from the user). Add handling of host-implemented operations to the interpreter's operand path: admit an interpreter-mapped op at the operand, so the gate asks the consumer's real question instead of the `body-less` proxy. GROUNDNESS DECIDES THE REST — if the arguments are known and concrete, reduce; if unground or ABSTRACT (a rigid var, an unbound operand), the evaluator returns DELAY rather than an answer, which is the residual discipline the goal side already follows (WI-519 / `is_unreduced_op_call`) and never a silent decline.

NOT DRIVEN: everything under DIRECTION is a code read plus the user's design call. The eight rows above ARE driven.

CONTROL, when it is fixed: `:- Bool.and(true, true) = true` answers 1 and `:- Bool.and(true, false) = true` answers 0 (the pair, so the row measures the COMPUTATION and not merely that something reduced); `:- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1)` still answers 1; and an unground operand SUSPENDS as a residual rather than answering or vanishing. Do not state the fix's control as "the corpus is still green" — `reduce_operand` is shared by `eq` / `cmp` / `arith` / `unify`, so a corpus run is the blast-radius check, not the measurement.

BLAST RADIUS, why this is not inline in another ticket. `reduce_operand` serves every operand comparison in the language. Its own doc calls keeping `dispatch_body_less` off "a correctness rule, not a cost tweak" and names five wi616 regressions as what the other setting cost. A change here needs its own full-workspace run and its own reading of those five.

FOUND BY WI-20260825-P9Y67, which needed to know whether a rule-body value position could be driven at all. Two wrong diagnoses were recorded and corrected on the way, and both are in kernel-language.md §5.2 now: that a host-backed op is inert in a rule body (false — it reduces at a goal), and that a value slot is not evaluated (false — `reduce_operand` runs).

ACCEPTANCE: the six DRIVEN rows above, plus the `Set` control, plus an unground-operand delay row. Full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-27T04:51:47Z — feedback — claude

RESIDUE FOLDED IN FROM WI-20260822-ZJZS7, which this ticket supersedes for its one surviving row. ZJZS7 asked the same question four days earlier and got three of its four parts delivered by commit 36f16461 (J38JE), which names ZJZS7 in its message and at kb/resolve.rs:8060: item 1 for the GOAL position (op_reducible_in_rule_body = op_body_node().is_some() || is_interpreter_mapped_op(), resolve.rs:8089), item 2 (the effect-free clause kept and documented at bare_bodied_bool_relation, resolve.rs:8117), and item 3 -- which is MOOT rather than answered, because push_and gave & a real conjunction reading and WI-1046 refusal was DELETED, not narrowed by an operand-type predicate as ZJZS7 proposed. What survived is exactly this ticket headline gap.

TWO THINGS TO USE.

1. THE ROW IS ALREADY PINNED, UNDER THE OTHER TICKET ID. anthill-core/tests/include/wi_j38je_boolean_goal_test.rs:512 asserts answers(j38jeh.pand(1)) == 0 with the message "a HOST-BACKED op does not reduce in a rule body: WI-20260822-ZJZS7", where the fixture rule is `rule pand(1) :- Bool.and(true, true) = true`. That test module is GREEN on the current tree (11 passed, run 2026-08-27), so the row is live. The enclosing test is what_the_condition_reading_cannot_yet_reduce, whose header says it is "written to FAIL when any of them lands, which is the intent" -- so the fix FLIPS this assertion rather than adding a fresh one, and the flip is this ticket first control. Its sibling row pandop(1) (the same conjunction through a BODIED operation) already answers 1 and must stay 1.

2. THAT TEST COMMENT IS NOW STALE IN TWO WAYS, and must be corrected by whoever fixes this, because it is the most-read statement of the gap. At wi_j38je_boolean_goal_test.rs:470-476 it says (a) "A HOST-BACKED OPERATION does not reduce here either ... they are inert in SLD ... a rule body reduces a BODIED operation and a resolver BUILTIN, and nothing else" -- FALSE at the goal position since 36f16461, which is precisely the asymmetry this ticket is about; and (b) "That is why `a & b` in a goal is still refused rather than admitted" -- FALSE, the same commit deleted that refusal and its two refusal rows now assert ANSWERS. Both sentences date from before the commit that landed in the same ticket.

A RECORDED NEGATIVE THAT TOUCHES THIS TICKET DIRECTION, read it before starting. kb/resolve.rs:8173, in functional_relation_arity, states for ZJZS7: widening that gate to a host-mapped op changes NOTHING -- String.concat("a", "b", ?r) still answers nothing with it widened, AND still does "with reduce_op_value body-less arm opened up beside it. Whatever blocks the arity+1 view for a host op is further in and is not either of those two gates". That is the SAME ARM this ticket proposes to admit an interpreter-mapped op into. It is NOT a refutation -- that measurement was the ARITY+1 relational view (a host op called with an extra output slot), while this ticket row is ARITY+0 in an operand slot, a different route -- but it does mean flipping dispatch_body_less alone has already been tried and measured INERT for a neighbouring shape. So do not state this ticket fix as "opened the body-less arm"; measure the operand row itself, both polarities, and say which of the two routes the change actually travels.

### 2026-08-27T05:09:05Z — feedback — claude

THE FILED DIAGNOSIS WAS WRONG IN TWO PLACES, both found by driving it. The eight rows in the description are ACCURATE — I reproduced every one on the untouched tree — but the mechanism they were attributed to is not what produces them.

WRONG 1: "THE SEPARATOR IS EXACT ... is_interpreter_mapped_op answers TRUE for Bool.and (registered at eval/builtins.rs:92)". It answers FALSE. Instrumented at the site: reduce_op_value reaches the Bool.and operand with op=and, body=false, mapped=FALSE. eval/builtins.rs:92 is a register_if_present call, which writes the INTERPRETER OBJECT raw builtin map keyed by hardcoded qualified name; interpreter_mapped_ops -- the set is_interpreter_mapped_op reads -- is built in set_host_op_mappings (kb/mod.rs:9262) from operation_map CLAUSES only. Bool had a rust binding block with no operation_map at all. This is WI-884 split, and its own comment at eval/builtins.rs:105 states the consequence verbatim: "op_is_interpretable counts a host MAPPING and not a hardcoded registration, so String.contains reads as backed and String.concat does not though one interpreter runs both ... Unreached today because no spec declares concat". This ticket is where it was reached.

WRONG 2: the goal-vs-operand framing. ":- Bool.and(true, true) answers 1" is TRUE but not because a host op reduces at a goal. Bool.and at goal ARITY 2 is position-directed to anthill.kernel.and (POSITION_DIRECTED_BOOLEANS, kb/mod.rs:7503) and resolved by J38JE push_and, which splices two GOALS into the frame -- no host function runs. MEASURED: that row answers 1 with this ticket entire change backed out. The same is true of Bool.not / Bool.or, so J38JE own commit message rows (":- Bool.not(false) nothing -> 1") credit a widening that did not produce them.

WHAT THE DEFECT ACTUALLY IS, and it is BIGGER than filed. A host operation_map-ed op reduced NOWHERE in a rule body -- not at an operand AND NOT AT A GOAL. J38JE widened the goal-side ENTRY gate (op_reducible_in_rule_body) so a host op could take the WI-580/WI-938 relational view, but that view is IMPLEMENTED by routing the goal to eq(f(args), true), i.e. INTO the operand path, whose gate still asked "a body and nothing else". So J38JE widening opened a door onto a wall and was INERT for every host op except the three position-directed connectives, which never take that route. THE WITNESS, driven in one file: String.contains is operation_map-ed, Bool-returning, rule-less and effect-free, so the widened entry gate admits it --

  :- String.contains("abc", "b")            backed out: 0     fixed: 1
  :- String.contains("abc", "z")            backed out: 0     fixed: 0
  :- String.contains("abc", "b") = true     backed out: 0     fixed: 1
  :- String.contains("abc", "z") = true     backed out: 0     fixed: 0

Both positions broken, both fixed by ONE arm in the operand path. That is what says it is not an operand-vs-goal split.

A SECOND DEFECT THE FIX EXPOSED, and the ticket unground row is what caught it. is_unreduced_op_call (resolve.rs:7923) asked the SAME op_body_node(..).is_some() proxy -- the same defect one coordinate over. Widening the reduction without it left a WRONG ANSWER, not a missing one: an unground host call comes back un-reduced, this predicate called that bare Apply ordinary DATA, and eq compared the CALL to true structurally and decided FALSE. MEASURED: rule ung(?b) :- Bool.and(?b, true) = true answered "no solutions" where the same rule over a BODIED op answers "1 conditional (residual goals undischarged)". Now both suspend identically with residual eq(and(?_, true), true). WI-1057 had explicitly refused to widen this predicate ("folding the two broke 5 wi616 cases") -- that refusal is about the BODY-LESS SPEC OP leg, where symbolic algebra lives; a host-mapped op is a computation by construction and Set.insert is mapped nowhere. All 18 wi616 tests green.

STILL NOT REDUCED, pinned in the new test rather than left silent: (a) the eight String/Int64 HARDCODED-only registrations -- String.concat("a","b") = "ab" still answers 0, which is WI-884 split and WI-880 migration, not this ticket; (b) a host call nested in a host call ARGUMENT (Bool.and(Bool.not(false), true) = true answers 0) -- arguments are sigma-walked, never reduced, so the bridge ground check declines and the call residualizes. Both are SUSPENSIONS, not wrong answers. A host call nested in a BODIED op body DOES reduce (depth+1 recursion) and that is the control beside it.

### 2026-08-27T06:02:08Z — feedback — claude

DELIVERED. Rust 36 binaries / 5825 passed / 0 failed via rustland/scripts/test.sh; scaland 518 passed / 0 failed (no eval package there, so nothing to port -- and scaland loads stdlib/ only, not the anthill-stl/ bindings this change touches). /code-review high run on the restored tree; all four findings were real and are dispositioned below.

THE CHANGE, 11 functional lines in resolve.rs plus 3 HOST_FNS entries and a 5-line operation_map.
 1. `reduce_op_value` body match gained `None if self.host_op_reducible_at_a_value(op) => None`, so a host-implemented op takes the eval bridge that was already the whole reduction for the body-less arms beside it.
 2. `host_op_reducible_at_a_value` = `is_interpreter_mapped_op` AND effect-free. The effect clause is ZJZS7 item 2 and it did NOT hold for free -- see below.
 3. `is_unreduced_op_call` gained the same host leg, so the DELAY predicate and the reduction agree.
 4. `Bool.{and,or,not}` migrated from hardcoded-name registration to `operation_map` (3 HOST_FNS entries + the block in anthill-stl/anthill/bool.anthill), keeping the hardcoded registration beside it so a stdlib-only KB does not lose them.

WHAT THE DEFECT WAS, restated because the filed diagnosis was wrong in two places (recorded in the previous feedback). Not an operand-vs-goal split: a MAPPED host op reduced at NEITHER position. J38JE widened the goal-side entry gate, but the relational view it admits is implemented by routing the goal to `eq(f(args), true)` -- into the operand path, whose gate still asked for a body. The widening opened a door onto a wall. `String.contains` is the witness, 0 at both positions before and 1/0 at both after.

TWO DEFECTS FOUND BY DRIVING IT.
 * `is_unreduced_op_call` carried the SAME `op_body_node(..).is_some()` proxy -- the defect one coordinate over. Widening the reduction without it was a WRONG ANSWER, not a missing one: an unground host call came back un-reduced, that predicate called the bare Apply ordinary DATA, and `eq` compared the CALL to `true` and decided FALSE. `Bool.and(?b, true) = true` answered "no solutions" where a bodied op answers "1 conditional". WI-1057 had refused this widening for the BODY-LESS SPEC OP leg ("broke 5 wi616 cases"); that reason is about symbolic algebra and does not reach a host op. All 18 wi616 green.
 * THE EFFECT ROW WAS INERT. A fixture mapping two operations to the SAME host function, one pure and one `effects {Error}`, answered 1 for BOTH. The goal side reason ("the eval bridge empty effect registry would suspend on one anyway") holds for a bodied op that RAISES; a host function is opaque Rust that just runs.

CODE-REVIEW FINDINGS, all four real.
 1. HIGH, FIXED. The host leg leaked into `op_call_as_occ` Node arm, which delegates to `is_unreduced_op_call` to pick `unfold_eq_operand` case-split SUBJECT -- a different question, which needs a body. I had guarded the Term arm and written a comment saying I deliberately did not widen "this one", while the Node arm silently was. DRIVEN: `String.contains(..) = Colour.isRed(?c)` gave 1 CONDITIONAL and the operands swapped gave 1 DEFINITE -- one equation, two verdicts. Node arm now asks for a body; regression test `an_eq_between_a_host_call_and_a_bodied_call_does_not_depend_on_operand_order` asserts the two orders AGREE (an equality, not a literal, because the disagreement is what is wrong). The whole workspace was green with the defect in.
 2. MEDIUM, FIXED. My pin doc said both remainders "are SUSPENSIONS, not wrong answers". DRIVEN false for one: `not(String.concat("a","b") = "ab")` answers 1 DEFINITE -- the hardcoded-only call is DECIDED FALSE and negation turns it into a positive answer out of a call that never ran. `nest` really does suspend. The rows now assert `total` beside `answers`, which is the only thing that separates the two, and the `ncat` row pins the unsoundness explicitly. This makes WI-880 migration a CORRECTNESS item, not tidying.
 3. MEDIUM, DOC CORRECTED. My doc claimed the effect row is "the ONLY thing standing between a rule body and a real side effect". Not total: the `needs_dict` arm beside mine admits a host-mapped callee with NO effect test and reaches the same bridge. Undriven (needs an impl member that is host-mapped, which WI-818 backing check refuses) so recorded as a code-path reading and routed to WI-20260827-NFXPZ, which should settle the policy for BOTH arms rather than leave two gates disagreeing.
 4. LOW, DOC CORRECTED + FIX REVERTED + FILED. My comment at `HeadCheck::BodiedOpCall` named the wrong consumer: that gate is the OTHER-operand structural-compare guard, not a head classifier for the split subject. I widened it to count host calls (sound -- it only DECLINES more), then MEASURED the cost: `Colour.isRed(?c) = String.contains(..)` went from 1 DEFINITE to a suspension. A live completeness regression traded against an undriven hazard is the wrong trade, so it is backed out and filed as WI-20260827-XBHX3 with BOTH measurements and the reason the naive fix fails (the gate cannot tell "un-reduced and will stay so" from "not yet reduced at this position").

CONTROLS, each RUN not reasoned about, and stated in the test file header as two separable back-outs. (1) the host arm disabled: 5 of 6 tests fail -- and `a_hardcoded_registration_is_still_invisible_to_the_gate` fails through its `has` CONTROL row at line 251, not its pin rows, which I verified by reading the panic rather than assuming. `symbolic_algebra_at_an_operand_is_still_left_as_data` passes either way BY DESIGN -- every row in it pins what the arm must NOT reach. (2) the effect clause alone disabled: ONLY the effect test fails, which is why that test exists -- the whole-arm back-out cannot see that half.

STILL OPEN, pinned as failing-when-fixed rows rather than left silent: the eight String/Int64 hardcoded-only registrations (WI-880), a host call nested in a host call ARGUMENT, the OTHER-operand hole (WI-20260827-XBHX3), and the `Error` effect policy (WI-20260827-NFXPZ).

