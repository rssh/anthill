## Attributes

- id: WI-20261102-2KC3A-scaland-has-no-sigil-free
- created: 2026-11-02T08:36:41Z

- status: Open
- status_agent: user
- status_at: 2026-11-02T08:36:41Z

- acceptance: scaland-sbt-test

## Description

SCALAND HAS NO SIGIL-FREE PARAMETER FORM (kernel-language.md §5.3, "The parameter form"; proposal 060 §2.1; rustland WI-742): in the head of a predicate a rule defines, `name: Type` introduces a clause variable, and `rule p(x: T) :- body` is `rule p(?x: T) :- body`. MEASURED 2026-11-02 on 6954c229, over `sort Buf { sort T = ?  sort N = ?  entity buf(v: T) }` and `fact q(buf(v: 1))`: `rule p(x: Buf[T = Int64]) :- q(x)`, `x: Buf[Int64]`, `x: Buf[W = Int64]` and `x: Buf[Int64, 3, Bool]` each load and `p(?z)` answers 0 — `x` stays a named argument over a constant, a dead clause — where the `?x: …` spelling answers 1 (scaland has no typer, so `Loader.reallocTerm` strips the `typed_var` marker to the bare variable and drops the bound: sound-conservative, by its comment). WHAT: reclassify the form where rustland does (`Loader::classify_rule_head_params`): a `(…)` argument list of a head that introduces its own predicate, never an entity constructor's head or a `[…]` bracket, and a named argument whose value names a type — a sort, a type parameter, `Self`, a constructor's name or a bracket applying one (§5.3, as amended 2026-11-02); a variable, a literal or a call stays a named argument. Each parameter is a column in the position it is written, one variable per name per rule across a multi-head rule's heads; its bound is dropped as the `?x: T` strip drops it. ACCEPTANCE (scaland-sbt-test via `sbt testFull`): the four heads above answer what their `?x:` twins answer; `rule g(x: Red, ?d)` is `g`'s first column and `rule g(?d, x: Red)` its second; `rule twin: aa(x: Red, ?d), bb(?d, x: Red) :- …` reads one `x`; controls — `rule reaches(from: ?a, to: ?b)`, `fact palette(c: red())`, `rule p(c: red())` and `rule Spec[T = Red] :- …` keep their named arguments.

