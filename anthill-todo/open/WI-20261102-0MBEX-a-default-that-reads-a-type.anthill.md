## Attributes

- id: WI-20261102-0MBEX-a-default-that-reads-a-type
- created: 2026-11-02T08:59:42Z

- status: Open
- status_agent: user
- status_at: 2026-11-02T08:59:42Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A DEFAULT THAT READS A TYPE PARAMETER AS A BARE VALUE FAILS AT EVERY CALL THAT TAKES IT, EVEN WITH ITS TypeValue CLAUSE. MEASURED on 7e211aa6 with the CLI: `operation tb3[T](x: T, y: Type = T) -> Type requires TypeValue[T = T] = y` called `tb3(3)` is refused in the CALLER, "`T` is read as a VALUE and nothing in scope requires `TypeValue[T = T]`" on `main.requires`; the inline spelling `operation tn3(x: ?t, y: Type = ?t) -> Type requires TypeValue[T = ?t] = y` called `tn3(3)` is refused "type mismatch in anthill.prelude.Int64.reference: … a plain reference to the sort — a defect in the walk that built this occurrence". Both declarations load clean (VQPRP holds a default to the rigid-read rule, so the same defaults WITHOUT the clause are refused at the declaration). The written call `t: Type = TypeValue.type_value[T = T]()` works and is pinned (wi_cx743's `typeOf`). CAUSE, read and not yet measured: `complete_defaulted_arguments` splices the stored default at the call with the call's σ (`substitute_occurrence`), which reaches type positions, but a bare `T` read is an `Expr::TypeValue { head: T }` (and `?t` an `Expr::Var`) in a VALUE position, so the copy carries the CALLEE's `T` into the caller's body, where the caller's rigid-read pass and the type-value frame read it. FIX DIRECTION, to decide: lower such a read in the spliced copy to the type the call fixed (or to the callee-side slot dispatch the declaration's typing built), so a default reads its type parameter as the body does. ACCEPTANCE: both measured programs answer the type the call fixes (`Int64` for `tb3(3)`); the unbacked defaults stay refused at their declaration; back-out measured; full gate green.

