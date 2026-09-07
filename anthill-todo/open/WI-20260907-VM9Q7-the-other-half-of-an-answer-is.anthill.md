## Attributes

- id: WI-20260907-VM9Q7-the-other-half-of-an-answer-is
- created: 2026-09-07T00:39:06Z

- status: Open
- status_agent: user
- status_at: 2026-09-07T00:39:06Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE OTHER HALF OF "AN ANSWER IS A VALUE" -- a FACT-matched literal still answers its
hash-consed carrier, and the thing blocking the symmetric fix is a FLOAT-RENDERING
DECISION, not the fold.

WI-20260904-EMVCB established that `Value::Node` is the ACCEPTING carrier and an answer
is a value, and folded a `Const` occurrence to its scalar at `KnowledgeBase::answer_binding`.
A literal answer has TWO non-native carriers, not one, and only that one is folded:

  rule value(?r) :- ?r <=> 2                        Node(Const(Int(2)))  -> folded, Int(2)
  rule value(?r) :- code(n: ?r)   [fact code(n: 0)] Term(Term::Const)    -> NOT folded

So the contract holds for one spelling of the same query and not the other. It is not
cosmetic: `wi_emvcb_answer_is_a_value_test::sole_native_int` asserts the native carrier
and is `<=>`-SCOPED because of exactly this -- it would panic on the fact spelling. Any
future helper that encodes "an answer is a value" inherits the same half-truth.

THE SYMMETRIC FIX WAS BUILT AND MEASURED, so this ticket starts from a number rather
than a hypothesis. Extending `fold_const_occurrences` with

    Value::Term { id } => match self.get_term(id) {
        Term::Const(lit) => Value::from_literal(lit.clone()),
        _ => v,
    },

(and making it take `&self`) compiles clean and fails 9 of 6531, in TWO CLASSES:

  * ONE USER-VISIBLE REGRESSION, and it is the whole reason this is a ticket rather than
    an inline follow-on. `wi863_operator_arithmetic_test::float_division_computes`:
    `6.0 / 2.0` prints `?r = 3` where it printed `3.0`. `TermPrinter` renders a
    `Term::Const(Float)` with its decimal point; a native `Value::Float(3.0)` renders
    through Rust's `Display`, which drops it. THE HASH-CONSED CARRIER IS HOLDING A
    PRINTABLE FORM THE NATIVE ONE DOES NOT REPRODUCE -- which is what makes folding it
    unlike folding an occurrence, where nothing but a span is lost.
  * EIGHT STALE CARRIER-ENUMERATING HELPERS in four files -- `wi999_name_capture_test`,
    `wi936_field_type_load_order_test`, `wi1034_undefined_rule_body_goal_test`,
    `wi_gmg6n_metadata_slot_drift_test`. Same shape as `wi_p9y67`'s `sole_definite_int`,
    which EMVCB already repaired: a `Value::Term` arm, a `Value::Node` arm, and a
    catch-all panic, so a CORRECT `Int(7)` panics. These are cheap and the repair is
    known (read through `common::scalar_int`); they are NOT the reason this is blocked.

SO THE FIRST DECISION IS THE PRINTER, NOT THE FOLD, and it is a user-facing one:
does a native `Value::Float(3.0)` render as `3.0`? If yes -- i.e. `Value::Float`'s
rendering is a defect independent of this -- fix it FIRST, on its own, and the fold
becomes available with only the eight helper repairs behind it. If float rendering is
deliberately `Display`-based, then the fold must REFUSE `Literal::Float` and the
remaining asymmetry has to be stated rather than closed. Do not do the fold first and
discover the printer question through a failing test; it is the design question.

CHECK BEFORE ASSUMING THE PRINTER IS THE ONLY SUCH CASE: `Literal::BigInt` and
`Literal::String` also have a `TermPrinter` rendering and a native `Display`, and this
ticket has NOT measured whether they agree. `float_division_computes` is the one the
corpus happens to cover; a carrier whose two renderings differ and which no test drives
would flip silently. The census is per-`Literal`-variant, not "floats are special".

WHY IT IS WORTH DOING AT ALL, since the read side already copes. WI-20260827-14EV6 made
every reader carrier-neutral, so nothing is UNREADABLE today -- this is not a
correctness bug in that sense. It is that "an answer is a value" is a CONTRACT stated in
`answer_binding`'s doc and in a test file's header, and a contract that holds for one
spelling of a query and not another is the shape that costs a reader a day later (the
same shape WI-20260827-3ZNBC's half-widened operand set cost twice, both times found by
/code-review rather than by a test).

ACCEPTANCE. `rule value(?r) :- code(n: ?r)` over `fact code(n: 0)` answers a native
`Value::Int` -- the CARRIER asserted, since the carrier is the subject and a
carrier-neutral read passes either way; the float question ANSWERED at its site, with
whichever way it went written where a reader meets it (`TermPrinter`'s float arm, or
`fold_const_occurrences`' refusal of `Literal::Float`); and the per-`Literal`-variant
rendering census stated, not just the Float row.

CONTROLS, and say at the fixture's site which rows fail on a back-out. MUST NOT MOVE:
`wi863_operator_arithmetic_test::float_division_computes` (`6.0 / 2.0` prints `3.0`) --
this is THE control, and a repair that leaves it green while changing the fold is the
only acceptable outcome; `wi_emvcb_answer_is_a_value_test`'s three pass-either-way rows,
especially `a_non_const_occurrence_is_not_folded`, which bounds the repair. MUST FLIP:
`wi_emvcb_answer_is_a_value_test::a_fact_matched_literal_keeps_its_hash_consed_carrier`,
which exists to fail the day this lands and carries the measurement above at its site --
re-spell it rather than deleting it.

REFERENCE: `KnowledgeBase::fold_const_occurrences` and `answer_binding` (kb/mod.rs),
`Value::from_literal` (eval/value.rs), `persistence/print.rs`'s `TermPrinter`,
`wi_emvcb_answer_is_a_value_test.rs`.

