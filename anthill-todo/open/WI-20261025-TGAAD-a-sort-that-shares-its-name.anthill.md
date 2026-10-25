## Attributes

- id: WI-20261025-TGAAD-a-sort-that-shares-its-name
- created: 2026-10-25T06:24:43Z

- status: Open
- status_agent: claude
- status_at: 2026-10-25T06:24:43Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A SORT THAT SHARES ITS NAME WITH AN OPERATION SHARES ITS SCOPE WITH THE OPERATION'S PARAMETERS AND TYPE PARAMETERS, so the sort's body reads the operation's names and the sort takes the operation's type parameter. Found delivering WI-20261023-GJVVW (44d52834), which made a name an operation's signature declares in scope in that operation only (kernel-language §8.6); measured on that tree, the same before it. The pair is one symbol (§4.4, WI-751/7EXEY), and `scan_operation_params` mints the operation's scope as `scope_id(op_sym)`, which is the sort's scope. MEASURED, three programs: (1) `namespace probe.pin  fact c(1)  sort Pos  entity pk(v: Int64)  rule inner(?x) :- c(?x)  end  operation Pos(c: Int64) -> Int64 = c  end` — `probe.pin.Pos.inner(?x)` answers nothing, silently: `c` in the sort's body is the operation's parameter, not the namespace's relation. (2) `sort Pos  entity pk  end  operation Pos[T](x: T) -> T = x` and `import probe.ptp.{T}` in another namespace loads clean, bound to the operation's type parameter (`SymbolTable::is_operation_place` admits only the value places of a pair's scope, since the operation's `T` and a sort's type parameter are both `Sort` there). (3) the same pair with `operation useSort(p: Pos[T = Int64]) -> Int64 = 1` loads, where without `operation Pos[T]` it is refused 'has no type parameter named T': `add_type_param(op_scope, …)` wrote the operation's `T` into the sort. Also: a parameter and a sort member of one name are one symbol at `ns.Pos.c`. WHAT IT TAKES: the operation's signature names in a scope of their own whose owner is still the operation (`declaring_scope(param).owner() == op` is read by region.rs and others), for every operation since which symbol is also a sort depends on declaration order; and the type-parameter readers told which they mean — `type_param_syms_of` / `type_param_sym_of` / `type_params_of_sort` take one symbol for a sort or an operation and have 273 callers in 88 files. scaland refuses the pair outright ('declaration is made again'), so this is rustland's. ACCEPTANCE: (1) answers 1; (2) is `unresolved import 'probe.ptp.T'`; (3) is refused as without the operation; the pair's existing rows (wi974, 7EXEY) hold; the operation still reads its own parameters and type parameters; each part's back-out measured.

