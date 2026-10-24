## Attributes

- id: WI-20261024-97QN7-a-bare-zero-arg-call-settles
- created: 2026-10-24T06:38:30Z

- status: Open
- status_agent: user
- status_at: 2026-10-24T06:38:30Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A BARE ZERO-ARG CALL SETTLES ITS TYPE PARAMETERS AS THE PARENTHESIZED CALL DOES (kernel-language §5.4, "The two readings of a bare operation name"). The zero-arg-call reading of a bare nullary operation name (`let o = pick`, `bare() -> Type = typeOf`) is typed in `check_bare_ref` (kb/typing/expr.rs) off the callee's DECLARED return type (`lookup_operation_return_type`), and none of the call's settlement runs: no bracket (none can be written), no unconstrained-parameter refusal (WI-270), no proposal 069 default (`install_type_param_defaults`), and no requirement dictionary at run time. `pick()` and `pick` are one call by §5.4 and disagree.

MEASURED 2026-10-24 (found by /code-review round 3 of WI-20261023-GBH5F; the same on the parent tree, defaults aside):
(1) over `pick[T]() -> Option[T] = none()`, `let o = pick` then `1` loads clean where `let o = pick()` is refused "expected a type for 'T', got unconstrained";
(2) over `pick[T = String]()`, `let o = pick` then `wantI(o)` (`wantI(o: Option[T = Int64])`) loads, the default not taken at the `let`, where `let o = pick()` then `wantI(o)` is refused `expected Option[T = Int64], got Option[T = String]`;
(3) over `typeOf[T]() -> Type requires TypeValue[T = T] = TypeValue.type_value[T = T]()`, `bare() -> Type = typeOf` loads and aborts at eval, `DeferToRequirement: requirement param __req_typevalue not bound in caller frame`; with `[T = String]`, `typeOf()` answers String and the bare `typeOf` aborts the same way. Eval's bare-name reduction passes no dictionary, and the typer records none for it.
(4) Two bare uses at two types (`let o = pick` / `let p = pick`, then `wantS(o) + wantI(p)`) load; whether the declared return's variable is shared between them should be read off the fix, not assumed.

WANTED: the bare zero-arg reading types as `op()` does — its type parameters fresh per reference, settled by the argument-free inference (the expected type, the receiver, the requirements), then the declared default, then WI-270 — and eval hands it the dictionary the typer selected, as for the parenthesized call. One way: route the reading through the zero-argument call path rather than a second copy of its steps.

ACCEPTANCE (cargo-test, driven): each of (1)–(3) has the parenthesized call's verdict and value, a row per shape, the parenthesized twin beside it as the control; each back-out reddens its own row; WI-2TMB5's, WI-1063's and WI-M8QWJ's rows unchanged.

