## Attributes

- id: WI-20260904-EMVCB-a-rule-body-lambda-whose
- created: 2026-09-04T18:07:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T18:07:27Z

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

