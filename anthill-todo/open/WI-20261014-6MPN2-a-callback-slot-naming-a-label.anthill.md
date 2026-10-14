## Attributes

- id: WI-20261014-6MPN2-a-callback-slot-naming-a-label
- created: 2026-10-14T08:24:38Z

- status: Open
- status_agent: user
- status_at: 2026-10-14T08:24:38Z

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

