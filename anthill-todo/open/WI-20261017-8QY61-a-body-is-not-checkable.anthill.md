## Attributes

- id: WI-20261017-8QY61-a-body-is-not-checkable
- created: 2026-10-17T09:39:54Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T09:39:54Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A BODY IS NOT CHECKABLE AGAINST A FIELDOF / PROJECT / CONCAT RETURN TYPE -- the operation's own return check compares the UNREDUCED declared type with the body's value, though a CALL of the same operation reduces it. MEASURED: `name_of(r: Rec) -> FieldOf[T = Rec, Name = "name"] = r.name` -> 'expected FieldOf[...], got String'; `kept(r) -> Project[T = (name: String, age: Int64), Keep = (person: "name", years: "age")] = kept(r)` -> 'expected Project[...], got (person: String, years: Int64)'; `resid() -> Concat[A = Without[...], B = (c: Bool)]` likewise. Pre-existing, made visible by WI-20260909-M8QWJ: a namespace operation with such a return can no longer be declared without a body either, so it can only be written as a signature in a sort without constructors or as @[host_implemented] (wi759, wi763, wi_yqb1y, wi_0rp29_review9 fixtures were moved that way). FIX: reduce the declared return (the call site's reduction, reduce_concat_in_type / the FieldOf and Project reductions) before checking the body against it; then move those fixtures back to bodied namespace operations.

