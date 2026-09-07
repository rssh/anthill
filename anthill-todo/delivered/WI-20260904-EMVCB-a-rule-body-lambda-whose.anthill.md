## Attributes

- id: WI-20260904-EMVCB-a-rule-body-lambda-whose
- created: 2026-09-04T18:07:27Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-07T00:28:57Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE-BODY LAMBDA WHOSE RESULT IS ITS ARGUMENT ANSWERS THE ARGUMENT'S NODE, NOT ITS
VALUE — where the operation-body spelling of the same program answers the value. One
program, two carriers, decided by where the call is written.

MEASURED 2026-09-04 while delivering WI-20260904-50B2K part (b), with
`operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)` and
`operation takes_int(n: Int64) -> Int64 = n` in scope. The value printed is what
`definite_unary` hands back — ONE definite solution in every row, so this is a CARRIER
difference and not a flounder:

  rule value(?r) :- ?r <=> apply1(lambda x -> x, 2)            Node(Expr::Const(Int(2)))
  rule value(?r) :- ?r <=> apply1(lambda x -> takes_int(x), 2) Node(Expr::Const(Int(2)))
  operation w()  -> Int64 = apply1(lambda x -> x, 2)                          Int(2)
  operation w2() -> Int64 = apply1(lambda x -> takes_int(x), 2)               Int(2)

AND THE NEIGHBOURING ROWS ANSWER `Value::Int` FROM THE SAME RULE-BODY POSITION, which is
what says the leak is the closure's RESULT and not "a rule body answers nodes":

  rule value(?r) :- ?r <=> apply1(lambda x -> x + x, 2)                       Int(4)
  rule value(?r) :- ?r <=> apply1(lambda x -> 0 - x, 2)                       Int(-2)

So the split is: a body whose result a BUILTIN computed comes back as a scalar; a body
whose result IS the argument (directly, or through an operation that returns its own
parameter) comes back as the occurrence the argument arrived on.

WHY IT MATTERS RATHER THAN BEING A CARRIER PREFERENCE. `Value::as_int` unwraps
`Value::Int` and nothing else, so every reader spelled that way sees `None` — a value
that exists and cannot be read. `wi_qqpq2_tuple_carrier_test::only_int` and
`wi_50b2k_binder_inference_test::only_int` are both spelled that way and both PASS on
rule-body answers elsewhere in the same files, so this is not a test-helper gap: it is
two carriers reaching one reader.

WHERE TO LOOK. WI-20260904-QQPQ2 established that `bridge_op_to_eval` (kb/resolve.rs)
hands a bridged operation each operand ON THE CARRIER THE RESOLVER PROVED IT ON, so a
written `2` arrives as a `Value::Node` occurrence. That ticket fixed the READ side
(`tuple_components` on every carrier). This is the RESULT side: when the closure's body
evaluates to the binder, the operand's node is returned unchanged and nothing normalizes
it back on the way out. The operation-body spelling never crosses that boundary, which is
why its twin answers a scalar.

NOT WI-20260904-50B2K PART (b), measured: the rows above answer identically with part
(b)'s `data_slot_arg_hints` in place and with it backed out. It is a typing change and
this is an evaluation one.

NOT WI-20260904-833DK, which is a bare operation NAME in a rule-body function slot — that
one raises `UnknownOperation` before any body runs. Here the lambda IS applied and the
answer IS definite.

ACCEPTANCE. `?r <=> apply1(lambda x -> x, 2)` answers `Value::Int(2)` — the value, read
through `as_int`, not "one solution". The CONTROLS are the operation-body twin (answers
2 today, must not move) and the `x + x` row (answers 4 today, must not move): a repair
that changed either has moved the boundary rather than normalized across it. Say at the
fixture's site which rows fail when the repair is backed out.

## Changes

### 2026-09-04T18:44:56Z — feedback — user

It's Value::as_int incorrectly does not extract 2 from Node - is Node have TermView?  How Const Node seen in TermView?

### 2026-09-04T18:45:39Z — feedback — user

I.e. I think that <=> return sourcr of 2 - is ok

### 2026-09-04T18:46:50Z — feedback — user

Also note, that this is const-folding 

### 2026-09-06T17:53:26Z — feedback — user

MEASURED 2026-09-06 while delivering WI-20260827-14EV6, which DELETED `Value::as_int` /
`as_bool` / `as_str`. This ticket's three rows were re-run against the fixture its own
description spells out (`apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 =
f(n)` plus `takes_int(n: Int64) -> Int64 = n`), read through the carrier-neutral
`TermView::literal_int64`:

  rule value(?r) :- ?r <=> apply1(lambda x -> x, 2)             Node(Const(Int(2))) -> Some(2)
  rule value(?r) :- ?r <=> apply1(lambda x -> takes_int(x), 2)  Node(Const(Int(2))) -> Some(2)
  rule value(?r) :- ?r <=> apply1(lambda x -> x + x, 2)         Int(4)              -> Some(4)   [control, unmoved]

SO THE TWO HALVES SEPARATE, and only one of them moved.

WHAT IS FIXED — the half this ticket's own user feedback named. "It's Value::as_int
incorrectly does not extract 2 from Node - is Node have TermView? How Const Node seen in
TermView?" and "I think that <=> return source of 2 - is ok". `occ_head` maps
`Expr::Const(lit)` onto the same `ViewHead::Const` a native scalar and a hash-consed
`Term::Const` answer, so `literal_int64` reads the Node as 2. The description's stated
consequence -- "every reader spelled that way sees `None` -- a value that exists and
cannot be read" -- no longer has a reader it applies to: the narrow spelling is gone from
the language, and the two helpers this ticket cites as evidence
(`wi_qqpq2_tuple_carrier_test::only_int`, `wi_50b2k_binder_inference_test::only_int`) both
read neutrally now. `wi_50b2k`'s `int_through_any_carrier` -- the hand-rolled Node descent
written to work around exactly this -- became UNREACHABLE and was deleted; its row still
passes.

WHAT IS UNTOUCHED — the carrier asymmetry itself. `?r <=> apply1(lambda x -> x, 2)` still
answers a `Value::Node` where the operation-body twin answers `Value::Int`, for the reason
the description gives: when the closure's body evaluates to the binder, the operand's node
is returned unchanged and nothing normalizes it on the way out. Nothing in WI-14EV6 went
near `bridge_op_to_eval`.

SO THE STATUS IS A DECISION, NOT A MEASUREMENT, and it is the user's. If "`<=>` returns
the source of 2 is ok" stands, this ticket is DONE and its remaining content is a note on
`const-folding` (the third feedback entry) rather than a defect. If the asymmetry itself is
still to be closed, the ACCEPTANCE needs re-spelling: it currently reads "answers
`Value::Int(2)` -- the value, read through `as_int`", and `as_int` no longer exists, so as
written it can neither pass nor fail. Its two CONTROLS are unaffected and still hold (the
operation-body twin answers 2; the `x + x` row answers 4).

### 2026-09-07T00:28:57Z — feedback — user

DELIVERED. `Value::Node` is the ACCEPTING carrier; an ANSWER is a value.

THE FRAMING IS THE USER'S AND IT IS WHAT MADE THE FIX SMALL: "Node was not about
emitting runtime value in compile time, but about accepting compile-time expression."
The carrier exists so a consumer can be HANDED an occurrence on the carrier the resolver
proved it on -- WI-20260827-3ZNBC hands every bridged operand that way, WI-20260904-QQPQ2
made the READ side cope with it. What had no owner was the way BACK. So at the boundary
where resolution hands a binding OUT, a `Const` occurrence -- which denotes a literal,
and a literal already HAS a native carrier -- folds to its scalar. Nothing else does.

THE TICKET'S OWN DIAGNOSIS WAS ONE STEP TOO NARROW, and the repair is wider for it.
"A RULE-BODY LAMBDA WHOSE RESULT IS ITS ARGUMENT" named a symptom. MEASURED: a bare
`?r <=> 2` answers `Node(Const(Int(2)))` too, and so does `?r <=> takes_int(2)`. The
occurrence reaches an answer whenever the answer IS a written operand, however it got
there; the lambda only made it easy to notice. Both spellings are pinned.

WHERE THE FOLD IS, AND THE THREE SITES THAT WERE REFUSED. `KnowledgeBase::answer_binding`,
every caller of which is an emit site: `materialize_solution`'s relation column,
`Substitution.lookup` answering anthill code what a var is bound to, and the CLI's query
printer. Refused, each for the same reason -- it is on the ACCEPT side too:
  * `reify_value` -- `bridge_op_to_eval` walks its operands through it. Folding there
    undoes WI-20260827-3ZNBC outright.
  * `reify` -- 27 callers inside `kb/`, most of them internal to resolution. Its own doc
    states the rule being narrowed ("an answer stays on the carrier it was proved on");
    that line now records the one-case exception and points at the real site.
  * `Value::node` -- the normalizing constructor, and the tempting one: it already
    collapses `node(Spliced(v))` and `node(Var(x))`, so `node(Const(l))` reads as the
    same law. MEASURED AND REJECTED: it has 2 callers against 187 raw `Value::Node(...)`
    constructions, so the law would have been inert at ~99% of producers -- a guard at a
    site nobody calls. Its own doc already says as much ("124 sites build the raw form
    and one uses it"); the ratio has since got worse. Making that the chokepoint means
    sealing the variant and migrating ~187 builders, which is its own ticket and would
    fold on the accept side anyway.

THE TEST HELPER WAS LYING, and that is why the ticket looked unfixed after the product
path was repaired. `common::query_unary` read `kb.reify(r_var, subst)` -- a RAWER read
than any product consumer performs -- so it reported `Node(Const(Int(2)))` where every
real consumer saw `Int(2)`. It now reads through `answer_binding`, with `reify` kept as
the FALLBACK so the UNBOUND case is untouched (`answer_binding` answers `None` there).
Only a BOUND answer changes, and only by folding a Const. Worth stating plainly: the
ticket's original measurement was taken through this helper, so its headline row was
measuring an instrument that disagreed with the thing measured.

WHAT IS DELIBERATELY NOT FOLDED, so the gap is a decision rather than an oversight.
`?r <=> some(2)` answers ONE occurrence whose expr is `Apply{some, x: Const(2)}` -- the
nested literal lives inside the occurrence's own `Expr` tree, not in a `Value` child, so
the recursion does not reach it and should not: an `Apply` occurrence denotes structure a
reader may still want to walk. Only a `Const` denotes a literal.

BLAST RADIUS, measured in two separable steps rather than one:
  * the fold alone (helper untouched): 36 binaries, 6528 passed, 0 FAILED. Nothing in
    reflect moved, which was the risk worth measuring -- `Expr::Const` is a legitimate
    reflect subject and a fold at a shared site would have destroyed it.
  * fold + helper repointed: ONE test failed, `wi_p9y67_connective_address_test::
    a_data_slot_keeps_its_spelling_so_a_body_matches_a_fact`, and it failed by PANICKING
    ON A CORRECT ANSWER. Its `sole_definite_int` enumerated carriers -- a `Value::Term`
    arm, a `Value::Node` arm, and a catch-all panic -- and got `Int(1)`. Its own doc
    recorded learning that lesson once already ("a helper that knows only one silently
    turns a passing row into a panic about the wrong thing (measured -- it did)"), having
    added the second arm rather than stopping enumerating. It now reads `scalar_int`.
    ENUMERATING CARRIERS IS THE DEFECT, NOT THE LENGTH OF THE LIST.

CONTROLS, MEASURED, TWO BACK-OUTS FOR TWO INDEPENDENT HALVES:
  * `Some(Self::fold_const_occurrences(reified))` -> `Some(reified)`: FOUR fail --
    `the_lambda_row_answers_the_value`, `a_bare_eq_answers_the_value`,
    `a_relation_column_answers_the_value`, `a_const_nested_in_an_entity_answers_the_value`;
  * delete ONLY the `Entity`/`Tuple` arms (keeping the top-level fold): exactly ONE fails,
    `a_const_nested_in_an_entity_answers_the_value`. Without that row the recursion would
    have been a branch nothing drives -- it took a fixture (`rule mk(pt(x: ?v)) :- ?v <=> 2`)
    to reach an `Entity` carrier holding a `Node(Const)` child at all.

PASS EITHER WAY, BY DESIGN, and each says so at its site: the ticket's own two controls
(`the_operation_body_twin_is_unmoved` -- never crosses the boundary; `a_computed_result_is_unmoved`
-- `x + x` answers 4, a value the builtin computed, with no occurrence to keep), plus
`a_non_const_occurrence_is_not_folded`, which is what BOUNDS the repair: a nullary
constructor answers a `Ref` occurrence and must ride through. A too-broad fix -- folding
every occurrence, or promoting answers to terms -- passes every other row in the file and
fails that one.

ALSO: `Value::from_literal` is now the single owner of the `Literal` -> native `Value`
mapping; `Interpreter::literal_to_value` was a second copy of the same five arms and
delegates to it.

ACCEPTANCE, RE-SPELLED. As written it read "answers `Value::Int(2)` -- the value, read
through `as_int`", and `as_int` was deleted by WI-20260827-14EV6, so it could neither pass
nor fail. What is asserted instead: the answer IS the native `Value::Int` carrier --
naming the variant on purpose, since the carrier is this ticket's subject and a
carrier-neutral read would pass with the fold backed out.

scaland: nothing to port -- it has no evaluator and no answer-materialization path.
Full workspace green via rustland/scripts/test.sh: 36 binaries, 6531 passed, 0 failed.

/code-review (high) FOUND SEVEN, ALL FIXED, and the first was a LIVE DEFECT this
ticket's own census method could not see -- for the second time in two tickets.

  1. HIGH -- `anthill-stl/src/runner.rs`'s `exit_code_from_main` matched
     `Ok(Value::Int(n))`. So `operation main(...) -> Int64 = code_n.head.n` -- a `main`
     returning a relation COLUMN -- exited 1 with `main returned non-Int64 value:
     Term { id: … }` about an Int64, while the BUNDLE GENERATED FROM THE SAME PROGRAM
     returned 0, because WI-20260827-14EV6 had fixed the template and not this. Fixed
     and controlled end to end: fact-matched column EXIT=1 backed out / EXIT=0 with the
     fix; the `<=>` spelling is EXIT=0 either way, because this ticket's own fold had
     already turned that one native. THE LESSON IS RECORDED AT THE SITE: a narrow read
     spelled as a PATTERN MATCH is invisible to the `#[deprecated]`-plus-compile census
     that caught the rest -- there is no accessor to mark. WI-14EV6 was caught by the
     same blindness in a `format!` string template.
  2. `answer_binding`'s own doc closed with "a `Value::Node` answer stays a
     `Value::Node`" -- the invariant its body now falsifies. Corrected AT that sentence,
     not only argued elsewhere.
  3. THE SET IS HALF-CLOSED, AND THAT IS NOW A MEASURED DECISION -- see below.
  4. The caller census justifying the fold's placement named 2 of 4. All four named
     (`materialize_solution`, `Substitution.lookup`, the CLI query printer,
     anthill-cpp-gen's `receiver_short_name`); the whole argument for folding HERE rests
     on that list being complete, so a partial one is not a census.
  5. `Value::from_literal`'s doc cited "`reify_value`'s `Const` fold", which does not
     exist -- `reify_value`'s own site argues at length that it must not have one.
  6. The fold reallocated BOTH child slices of every compound answer even when nothing
     folded, discarding `Rc` sharing. `materialize_solution` calls `answer_binding` once
     per column per row, so a relation of compound values paid two fresh slice
     allocations per compound column per row to return what it was given. Now behind a
     read-only `bears_const_occurrence` pre-pass.

FINDING 3, AND WHY THE SET STAYS HALF-CLOSED ON PURPOSE. A literal answer has TWO
non-native carriers: the `Value::Node` occurrence this folds, and a hash-consed
`Value::Term` over `Term::Const`, which is what a FACT-matched column rides. So the
contract holds for `?r <=> 2` and not for `code(n: ?r)` over `fact code(n: 0)`.

FOLDING BOTH WAS BUILT AND MEASURED, not argued: 9 of 6531 fail, in two classes.
  * A USER-VISIBLE REGRESSION, and it is the reason to stop:
    `wi863_operator_arithmetic_test::float_division_computes` -- `6.0 / 2.0` prints
    `?r = 3` instead of `3.0`. `TermPrinter` renders `Term::Const(Float)` with its
    decimal point; a native `Value::Float(3.0)` renders through Rust's `Display`, which
    drops it. The hash-consed carrier holds a PRINTABLE FORM the native one does not
    reproduce, so folding it is not carrier-neutral the way folding an occurrence is.
  * Four more stale carrier-enumerating helpers (`wi999`, `wi936`, `wi1034`,
    `wi_gmg6n`) -- the `wi_p9y67` shape again.
Closing that half needs a float-rendering decision first and is its own change. The
measurement is at `fold_const_occurrences`' doc so the next reader inherits it rather
than the guess, and `a_fact_matched_literal_keeps_its_hash_consed_carrier` PINS the
current asymmetry -- it fails the day someone closes it, which is when they should be
reading the float note.

FORMATTING: every touched file is at or below its HEAD hunk count. `rustfmt` on
`kb/mod.rs` follows its `mod` declarations into five untouched files; reverted at file
granularity (the same trap `wi_tests.rs` set on WI-14EV6, one directory up).

