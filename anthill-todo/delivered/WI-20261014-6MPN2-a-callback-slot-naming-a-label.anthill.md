## Attributes

- id: WI-20261014-6MPN2-a-callback-slot-naming-a-label
- created: 2026-10-14T08:24:38Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-14T14:12:50Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A callback slot naming a label beside its row parameter leaves the row parameter unconstrained for a callback raising the caller's own row.

PROGRAM (measured 2026-10-14, plain and ANTHILL_TEST_NODE_CARRIER=1 alike):

  operation run[EffP](p: Int64, f: (k: Int64) -> Int64 @ {Error[String], EffP}) -> Int64 effects {Error[String], EffP} = f(p)
  operation use[R](h: (n: Int64) -> Int64 @ {R}) -> Int64 effects {Error[String], R} =
    run(1, lambda (k: Int64) -> h(5))
  operation go() -> Int64 effects {Error[String]} = use(lambda (n: Int64) -> n + 40)

is refused at the call in use: "expected a type for 'EffP', got unconstrained — use run[EffP = …](…)". The same program with the slot written @ {EffP} runs to 45, and so does the written bracket run[EffP = {R}](1, …). So a label written beside the row parameter in the slot (Error[String] here; Modify[k], the callback's own parameter, is the other measured spelling) stops the callback's row {R} from binding EffP.

EXPECTED: the label in the slot takes the callback's labels it names, and EffP the rest — here EffP = {R}, and go runs to 45, as in the @ {EffP} spelling.

WHERE TO LOOK: found during 1TJQH (callback_at_slot, bind_row_tail in kb/typing/effects.rs, the slot's row decomposition); on the tree before 1TJQH as well. The family c-callback-row holds slots @ {Error[String], EffP} and @ {Modify[k], EffP}; read its verdicts for the callbacks raising R.

## Changes

### 2026-10-14T14:12:44Z — feedback — claude

DELIVERED (e0d05780). The discharge pass after the arguments (infer_discharged_row_tails) now takes a callback row whose every tail is rigid: the residual is the labels no slot label covers and the caller's rigid rows the slot does not hold, so EffP = {R} here and the ticket's program runs to 45, as the @ {EffP} spelling does; the @ {Modify[k], EffP} spelling too. Two of the caller's rows bind as their union. Measured on the way and fixed with it: a slot holding the caller's row through a receiver (@ {s.E, EffP} over s.E = {R}) was refused the same way; the pass reads the slot as the call reads it and binds no union a slot naming the tail denies (wi_0rp29's -s.E over {Error[Foo], R}); and, from /code-review, a callback at a slot read off a receiver is read in the slot's names, so one writing its own parameter is refused at the call, not at use's effects as 'undeclared effect: Modify[T = c]' (closed rows did that before as well). Rows: wi_6mpn2_label_beside_row_parameter_test (9, back-outs in its header); family c gains the slot @ {Error[String], EffP}, every verdict that of @ {EffP}; family e's 25 slot-own rows moved and the 6T5C6 exception typed=field,row=own-open (company differs by spelling) was taken off, 6T5C6's own refusal standing. Not fixed: a tail the first argument already bound decides it (WI-20260820-RDNS4), pinned by a row. Gate 9827/0; scaland 688 + 45 + 1.

