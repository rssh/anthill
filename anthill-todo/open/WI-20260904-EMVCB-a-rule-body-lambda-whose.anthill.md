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

