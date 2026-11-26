## Attributes

- id: WI-20261126-SRY02-a-declared-type-with-its
- created: 2026-11-26T20:58:08Z

- status: Open
- status_agent: claude
- status_at: 2026-11-26T20:58:08Z

- acceptance: cargo-test

## Description

A declared type with its parameters substituted is built only inside term_ser: give DeclaredType a public closed type
WHO NEEDS IT. A caller that reaches a constructor's field at an application through DeclaredType (WI-20261125-CMQJ4) and must then compare that field's type with a type it holds as a Value. anthill-traces (private) checks that a field declared to hold the time is of the time parameter's type. For sort Held[T] with entity Held(value: T, at: Int64), reached in an operation's signature as Held[T = Int64], beside a time parameter now: Int64, the field value is of the time's type at that application. The caller compares types with views_structurally_equal, as it does everywhere else.
WHAT HAPPENS. Read from code (88a94552d): DeclaredType gives a field's type at an application as a TypeShape (DeclaredType::shape, persistence/term_ser.rs:750) or as text (display_name, :852, for display only). The substituted type itself, a Value, is built by closed_type (:1107), which is private; the codec uses it for the place a value at a sort with abstract values is used at. DeclaredType's own fields are private too. So a caller can learn that value at Held[T = Int64] has the shape Int64, but cannot compare it with a type it holds: TypeShape has no equality, and a Data shape does not give out its bindings. Until then anthill-traces refuses such a field by name (its WI-20261126-N9XCS; measured 2026-11-26 on a scratch spec of the shape above: the field value of g.Held is typed in the parameters of g.Held (T)) and compares a field's type as written otherwise.
WHY IT MATTERS. A caller's alternatives copy a rule anthill owns: comparing TypeShapes structurally is a second definition of type equality, coinductive over recursive sorts; comparing display_name strings is a text round trip of types already in memory.
WHAT IS ASKED. A public method on DeclaredType that gives its closed type, for example closed_type(&self, kb) -> Result<Value, ValueProblem>; the form is anthill's. It returns the type the declared type stands for, with every parameter its place binds substituted, and a parameter nothing binds refused by name, as shape() refuses it. With it, views_structurally_equal(kb, &field.closed_type(kb)?, &ty) is the comparison.
DONE WHEN. A test outside the crate checks four cases. (1) For sort Cell[T] with entity Cell(value: T), DataShape::fields at Cell[T = Int64] gives value a DeclaredType whose closed type is views_structurally_equal to Int64 as the loader gives it for a parameter written Int64. (2) For sort Holder[A] with entity Holder(c: Cell[T = A]), at Holder[A = Bool], c's closed type is views_structurally_equal to the loader's Cell[T = Bool]. (3) A type that names no parameter comes back as it is. (4) A parameter with neither a binding nor a default is refused by its name (UnboundParameter).

