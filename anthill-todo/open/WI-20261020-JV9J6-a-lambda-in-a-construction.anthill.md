## Attributes

- id: WI-20261020-JV9J6-a-lambda-in-a-construction
- created: 2026-10-20T14:17:05Z

- status: Open
- status_agent: user
- status_at: 2026-10-20T14:17:05Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LAMBDA IN A CONSTRUCTION PASSED STRAIGHT TO A CALL IS TYPED AT NO INSTANCE.

MEASURED on 9a33a2c4 (the same on 15a12b17, before WI-20260911-VNQTR):

  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
  sort H[A]
    entity h(f: (x: A) -> Type)
  end
  operation apply(v: H[A = Int64]) -> Type =
    match v
      case h(g) -> g(1)
  operation go() -> Type = apply(h(f: lambda (x) -> tyOf(x)))

is refused at the `tyOf(x)`: "type mismatch in ….tyOf.type_arg: expected a type for 'B', got unconstrained". The construction stands at `apply`'s parameter, `H[A = Int64]`, and the lambda's binder is typed at no instance. Since 9a33a2c4 the same lambda loads wherever the construction's instance is stated otherwise: a bracket (`apply(h[A = Int64](f: lambda …))`), a result type (`-> H[A = Int64] = h(f: lambda …)`), an annotation (`let v: H[A = Int64] = h(f: lambda …)`); and an operation name at the call loads and answers (`apply(h(f: tyOf))`), the reference read where the value is applied.

Refused alike, before and after: the positional `apply(h(lambda (x) -> tyOf(x)))`; a binder read with no requirement in sight, `runK(k(f: lambda (q) -> q.n))` over `sort K[A] { entity k(f: (q: A) -> Int64) }` and `runK(v: K[A = Foo])` — "<unresolved receiver>.n: expected operation declared on the receiver's sort, got no such member (dot dispatch)", where `runK(k[A = Foo](f: lambda (q) -> q.n))` loads; and a lambda in a construction whose field is the sort's parameter, `applyO(some(lambda (x) -> tyOf(x)))` over `applyO(o: Option[T = (x: Int64) -> Type])`, where `applyO(some(tyOf))` loads.

The spec says these load: §5.4, the function-value paragraph — "A lambda or an operation name in a construction's field is typed at the instance the construction states, by its bracket or by the type it is expected at, the field written by name or by position" — and a call's parameter is the type its argument is expected at.

MECHANISM: a call pushes its parameter type into a construction argument only through `ctor_arg_unlocks_a_field_hint` (kb/typing/arg_hints.rs), which fires for a field whose argument is a bare operation name or a construction, and only where the walk reaches what the declared field type does not already give. A lambda is neither, and `h`'s field is already an arrow, so the construction is typed with no expected type and `arrow_field_expected_from_ctor` has no instance to put for `A`.

FIX DIRECTION: count a lambda (`arg_is_function_value_literal`'s shapes) among the arguments whose field hint the parameter type unlocks, and count an instance the declared field leaves open (`A` in `(x: A) -> Type`, `T` in `some`'s field) as something unlocked. The gate's doc keeps a census of what newly receives a hint; measure it before and after, stdlib call sites included.

ACCEPTANCE: the four refused programs load and answer — `Cell[V = Int64]` for `go`, the positional and the `Option` shapes, `7` for `runK` — each a row driving the call; the bracket, result, annotation and operation-name shapes unchanged; families green; full gate green.

