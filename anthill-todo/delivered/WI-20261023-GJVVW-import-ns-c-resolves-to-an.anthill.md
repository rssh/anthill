## Attributes

- id: WI-20261023-GJVVW-import-ns-c-resolves-to-an
- created: 2026-10-23T17:13:09Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-25T06:05:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

`import ns.{c}` resolves to an operation's PARAMETER named `c` rather than the relation `c` the namespace's facts define, so a goal `c(?x)` in the importing namespace answers nothing, silently. MEASURED 2026-10-23 (38a260a6): `namespace probe.imp  import anthill.prelude.{Int64}  operation useIt(c: Int64) -> Int64 = c  fact c(1)  end` and `namespace probe.imp2  import anthill.prelude.{Int64}  import probe.imp.{c}  rule r(?x) :- c(?x)  end`: `probe.imp2.r(?x)` answers no solutions; with the parameter renamed `d`, `?x = 1`. Seen first as `import probe.hand.{c}` printing the relation as `probe.hand.useVia.c`. A parameter is in its operation's scope only. ACCEPTANCE: `r(?x)` answers 1 with the parameter named `c`; a parameter is never reached by an import (selective, plain, or the qualified spelling `probe.imp.c`); in both implementations' name resolution.

## Changes

### 2026-10-25T06:05:16Z — feedback — claude

Delivered 2026-10-25 (44d52834). A name an operation's signature declares — a parameter, a type parameter, `result`, a callback's place — is in scope in that operation only (kernel-language §8.6, the sentence agreed with the user 2026-10-25). `import probe.imp.{c}` lands on the relation and `r(?x)` answers 1; the plain import and the qualified goal answer 1 as before. Refused where they loaded clean: `import lib.useIt.c`, `import lib.useIt.{c}`, `import lib.{T}` (an operation's type parameter), `import lib.{result}`, `import lib.hof.f.result`; a body goal, a type or a rule head spelling such a path (`fact useIt.c(1)` had stored its clause on the parameter); a host name at `<global>`; a wildcard or a `requires` of a sort that shares its name with an operation. Found on the way and fixed: a refused reference handed back a bare intern of its qualified name, and a fact head over an `internal` operation's path (`fact lib.secret(2)`) aborted the load on WI-581's assert, before this change too.

/code-review (xhigh, 13 findings): fixed the redundant filter in the diagnostic twin, the doubled selective filter, three spellings of the enclosing test (now `SymbolTable::written_within_declaring_scope`), the `DottedVisibility::Any` docs, the unpinned verdicts; no change for WI-752's fall-through taken by a place hit (the rule for an unusable hit), the `encloses` allocation (a place resolves at its own operation's scope), `lookup_symbol`'s silent failure (the builtin has no diagnostic channel).

NOT DONE, measured: a sort that shares its name with an operation gives the operation's parameters and type parameters the sort's scope — a rule in the sort's body reads `c` as the operation's parameter, `import ns.{T}` reaches the operation's type parameter, and the sort accepts `Pos[T = Int64]` from `operation Pos[T]`. Separating them needs the operation's own scope at the 273 callers of `type_param_syms_of` / `type_param_sym_of` / `type_params_of_sort` (88 files), each deciding sort or operation.

ROWS: tests/include/wi_gjvvw_import_reaches_no_parameter_test.rs (13), each of five parts backed out alone and listed in its header; wi913's census counts an operation's place (1208 of 3013 dotted names). scaland ImportReachesNoParameterTest (4). RUNS: rustland/scripts/test.sh 10822 passed, 0 failed; scripts/families.sh holds; scaland sbt testFull 1 + 47 + 766 passed.

