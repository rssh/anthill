## Attributes

- id: WI-20261001-89WZR-a-let-annotation-naming-a-type
- created: 2026-10-01T11:23:15Z

- status: Open
- status_agent: user
- status_at: 2026-10-01T11:23:15Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A LET ANNOTATION NAMING A TYPE PARAMETER IN SCOPE IS A DIFFERENT TYPE FROM THE PARAMETER. operation same[T](y: T) -> T = let x: T = y  x is refused "type mismatch in x.annotation (let-binding): expected ?T, got ?T (these render alike but are not the same type)"; so is let xs: List[T = T] = cons(y, nil) ("expected List[T = ?T], got List[T = ?T]"), an operation's own parameter inside a sort (keep[U](b: Box, u: U) -> U = let x: U = u  x), and a SORT's own parameter inside one of its operations (get(b: Box) -> T = let x: T = b.v  x: "expected T, got ?T"). The un-annotated let x = y and a lambda parameter's annotation (lambda (x: T) -> x) load. MEASURED identically on the WI-20260929-0RP29 tree and the pre-ticket build; no program in the repository writes one, which is how it went unseen. Where, from code reading: the let conformance (typing/build.rs, TypeBuildFrame::LetAfterValue) relates the value's type — carrying the body's RIGID for the parameter (rigidify_op_type_params, the env's param_rigids bridge) — to the annotation AS WRITTEN (pattern_annotation_value: the parameter's canonical variable, or its bare name for a sort parameter) through types_compatible in a FRESH substitution, which binds nothing; the same annotation is the value's expected type before that. CONSEQUENCE beside WI-20260929-0RP29's row decision (user, 2026-10-01): a -R written in a let annotation is not the enclosing operation's rigid R, so use[R](g: (x: Int64) -> Bool @ {Error[Foo]}) -> Bool effects {Error[Foo]} = let h: (x: Int64) -> Bool @ {Error[Foo], -R} = g  h(1) loads, where the same callback passed to a parameter requiring -R is refused. Direction: read the annotation's references to the parameters in scope through the body's rigid bridge (env.param_rigids, the sort's own) for the check and the expected type, without writing a rigid back into the stored pattern (WI-1059: a rigid is pass-local). ACCEPTANCE: each spelling above loads and runs (an Int64 instantiation answering its value); a wrong one (let x: T = u with u: U) is still refused naming both parameters; the -R let annotation is refused as its parameter twin is; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-10-02T05:00:57Z — feedback — user

ADDENDUM (found while fixing WI-20260929-0RP29's seventh review, finding 11) — A CALL-SITE BRACKET NAMING THE ENCLOSING OPERATION'S TYPE PARAMETER HAS THE SAME DEFECT. In operation use[R](s: Strm[T = Int64, E = {R}]) -> Bool effects {R} = Strm.each[EffP = {R}](s, pure1), where Strm.each[EffP](s: Strm, f: (x: Int64) -> Bool @ {EffP, -s.E}) and pure1 is a pure callback, the bracket's R is not use's rigid R but a flexible variable of its own (MEASURED by tracing the call: the absence spliced from s.E carries the rigid, the bracket's row another term). So the callback's row, which is {R, -R} as written — uninhabitable by the user's row decision of 2026-10-01 — is read as {R', -R}, the argument's empty row then binds R' to the empty row, and the call LOADS on every build; its twin with both rows written in the bracket, each3[EffP = {R}, R = {R}](pure1), is refused "both admit and lack ?R" because there the two are one variable. The bracket is not honoured: the call charges nothing where it was told to charge R. Same direction as the let annotation: read a bracket's references to the parameters in scope through the body's rigid bridge. ACCEPTANCE addition: Strm.each[EffP = {R}](s, pure1) inside use[R] over s: Strm[E = {R}] is refused as its written twin is; an ordinary bracket naming the caller's parameter (id[A = T](y) inside same[T](y: T) -> T) still loads and runs.

