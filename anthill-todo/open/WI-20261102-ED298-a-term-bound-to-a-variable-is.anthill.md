## Attributes

- id: WI-20261102-ED298-a-term-bound-to-a-variable-is
- created: 2026-11-02T19:19:57Z

- status: Open
- status_agent: claude
- status_at: 2026-11-02T19:19:57Z

- acceptance: cargo-test

- tags: proposal-068

## Description

A TERM BOUND TO A VARIABLE IS READ AS A CALL WHEREVER THE BINDING IS READ, so a reflected term whose functor names an operation answers nothing once it passes through a variable (068 §1.2–1.3). Found with the user 2026-11-02, delivering 12151e4f (make_fn from a rule body). PROGRAM: namespace p / import anthill.prelude.{Int64, String, Option, List} / import anthill.prelude.Option.{none} / import anthill.reflect.{Term, term_to_string, as_term, make_fn, term_as_int} / rule inline(?r) :- ?r <=> term_to_string(make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)])) / rule viaVar(?r) :- ?t <=> make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]), ?r <=> term_to_string(?t) / rule notNone(1) :- ?t <=> make_fn("anthill.prelude.Int64.add", [as_term(1), as_term(2)]), not(term_as_int(?t) = none) / end. MEASURED on 12151e4f: inline "add(1, 2)" definite — what the same text answers in an operation body, run by the interpreter; viaVar one CONDITIONAL row, two residual goals; notNone one conditional row. Truth: viaVar "add(1, 2)", notNone no row. Before 12151e4f's E repair viaVar answered "3" DEFINITE. MECHANISM: make_fn returns Value::Entity { functor: Int64.add, … }, the reflected term; <=> binds ?t to it, and every later read of the binding (the <=> walk, evaluate_at's chase into an argument) meets an operation-headed application on the Entity carrier, which WI-20260910-FDPJ8 made a CALL on the term and entity carriers (term-carried goals). 12151e4f stopped evaluate_call re-evaluating a value a call returned; a binding still cannot say it holds data. 068 §1.2: nothing stored in a binding is an unevaluated call; §1.3: a Term is a quote's product and the way back is a splice that evaluates (WI-189, open). The exception is design D7's SYMBOLIC call, kept in place where a value is built, which a test must still see as stuck. THE QUESTION: how a value evaluation produced stays a value in σ — a carrier that marks quoted data (what WI-189's quote produces), or the binding reader trusting §1.2 with D7's symbolic calls marked instead. Read 068 §1.2–1.3 and docs/design/068-implementation.md D7 first. ACCEPTANCE (cargo-test, driven): viaVar "add(1, 2)" definite and notNone no row; make_fn_rule_body_term_test::through_a_variable_it_is_undecided turned into those answers, with the back-out measured; D7's symbolic rows unchanged (a call over a proof's eigenvariable kept in a binding still delays a test); FDPJ8's term- and entity-carried goal rows (wi_fdpj8_op_call_carrier_test) unchanged.

