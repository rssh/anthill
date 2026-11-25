## Attributes

- id: WI-20261125-CMQJ4-a-constructor-s-field-types-at
- created: 2026-11-25T08:45:14Z

- status: Open
- status_agent: user
- status_at: 2026-11-25T08:45:14Z

- acceptance: cargo-test

## Description

A constructor's field types at an application of its sort are read only inside term_ser: give that reading one public owner
WHO NEEDS IT. Any caller that walks a value at its declared type as the codec does. anthill-traces (private) has three: its value generator (its WI-20261122-219KE, drawing arbitrary values of a spec's types), its state-diff walker, and its evaluator's field-type reader. Each reads a constructor's fields with entity_field_types, which gives them as written, in the sort's parameters: for sort Cell[T] with entity Cell(value: T), value: T. At an application, Cell[T = Int64], the caller needs value: Int64. All three refuse a sort with type parameters other than List and Option today; the codec decodes and encodes such values.
WHAT HAPPENS. Read from code (8ed4765f3): term_ser makes this substitution privately. classify, resolve and sort_env (persistence/term_ser.rs:673, :701, :754) build an Env (:611) that maps each parameter's canonical variable (canonical_type_param_var, kb/mod.rs:3980, pub(crate)) to the type the application binds it to, by name or by position, or else to its declared default (sort_param_defaults, kb/mod.rs:2034, pub(crate)); a parameter with neither is refused by name.
A caller CAN rebuild it from public pieces. MEASURED 2026-11-25 on bb5528b38 through anthill-traces' test binary: for sort Cell[T] as above, entity_field_types(Cell) gives value a flexible variable (?_, id 4727), and type_param_of_canonical_var(VarId::new(4727, _)) (kb/mod.rs:4016, pub) answers Cell.T. Read, not measured: is_positional_label_at is pub (intern.rs), and a default is the anthill.reflect.SortParamDefault(param, default) row (reflect.anthill:1352).
WHY IT MATTERS. Rebuilt outside the crate, the rule exists twice, and nothing keeps the two copies alike: a default, a positional binding, or a binding that names a parameter of an outer place, read one way by the caller and another by the codec, gives a value the codec does not decode, or field types the codec does not use. The same reasoning that made build_list the single owner of a list's shape.
WHAT IS ASKED. One public owner of what a declared type is to a value walker, which the codec itself reads: for a type, with the bindings of the place it is written in, its shape. That is, a primitive; an Option or a List with its element type; a tuple's components; or a sort's constructors, each with its fields' types at the application (parameters substituted, defaults applied, a parameter with neither refused by name), and a nested type keeping its place's bindings. The form is anthill's to choose: term_ser's Shape and Ty made public with a constructor's fields resolved, or a function that answers one constructor's resolved fields at a type.
DONE WHEN. (1) A test outside the crate reads Cell[T = Int64]'s constructor with value at Int64; a parameter left to its default (sort Box[T = Int64], written Box) and a positional binding (Pair[Int64, String]) read alike; a nested application whose binding names an outer parameter (sort Holder[A] with entity Holder(c: Cell[T = A]), at Holder[A = Bool]) reads c.value at Bool; an unwritten parameter with no default is refused by name. (2) The codec reads its shapes through it, with no second copy of sort_env. (3) For each type the test reads, a value built from the reported field types decodes through the codec to itself.

