## Attributes

- id: WI-20261104-5CNY5-proposal-002-s-correction-into
- created: 2026-11-04T06:52:36Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-04T07:19:44Z

- acceptance: review

- tags: proposal-002, typing

## Description

PROPOSAL 002'S CORRECTION INTO THE SPEC: kernel-language §4.4 still says an arrow records its parameter arity (WI-791) and that a call of a function value passes exactly that many arguments (WI-792), where proposal 002 §"Correction (2026-11-03)" (decided with the user 2026-11-03 and 2026-11-04) says every arrow is a `Function`. The rule there: `(p1: T1, ..., pn: Tn) -> R` is `Function[A = (p1: T1, ..., pn: Tn), B = R]` with no parameter count; two matches relate tuples, the tuple match (a value of one tuple type against an expected one, by name with width and permutation, §4.5, unchanged) and the application match (an application's arguments against the tuple of the function applied: a positional argument to the component at its position, a named one to the component with its label); `f((x, y))` is `f(x, y)`, and one tuple is always the argument list, for a call through a value and a call of an operation by its name alike; a callable meets a function type by label when the two tuples carry the same labels, and by a mapping of labels by position otherwise; a callable's own parameter count is checked where it becomes a value (WI-801). WHAT: rewrite §4.4's "Parameter lists correspond slot by slot", "An arrow records its parameter ARITY", "Applying a function value checks its arguments" and the `Function` note ("The equivalence is not exact ... `Function` states no arity"); the lambda paragraphs ("Applying a lambda", and the binder-annotation paragraph's "a conflict surfaces through the body's use of the binder", stale since WI-794); and §8's "the parameters of a lambda of several binders, which take their types from the type around it". Define both matches where first used, state the rule with one example each, no history. Show the text to the user before committing. ACCEPTANCE: the spec states 002's correction and 002's status line says so; documentation only.

## Changes

### 2026-11-04T07:19:40Z — feedback — claude

Delivered. kernel-language states proposal 002 correction: §4.4 (every arrow is a Function, no parameter count; the tuple match and the application match; one tuple is always the argument list; a function value checked by the application match, converted at load to its tupled form; a callable at a function type by label when the tuples carry the same labels, by position otherwise; a one-parameter callable drops what its tuple lacks; the count checked where a callable becomes a value; a function value at another function type keeps its order, WI-1088; the row places aligned by the same mapping), §4.5 (an arrow parameter list has distinct labels), §4.7 (applying a lambda; an annotation contradicting its component is refused, one binder or several), §5.4 (the lambda-binder sentence the ticket placed in §8; the WI-1100 paragraph states the application match for a call by name, `add2((1, 2))`, a one-parameter operation taking its arguments as its parameter value and still naming it), §6.7 (an arrow parameter list is met by the application match, `(p: A, q: B) -> R` standing at `(x: A, y: B) -> R` by position), §8.6 (a named argument through a function value meets its type A; `Function[A = (acc, x)]` takes labels). Four decisions taken with the user 2026-11-04 and recorded in 002 with programs measured on 0eaa2e86: width dropped at a one-parameter callable (age_of(person), app(age_of, …), app(lambda (p: (age: Int64)) -> p.age, …) each 7); WI-1088 refusal kept (w3 refused); one tuple is any one argument of tuple type (`r(p)` 112 today, refused at `t` under the rule; `r(t: p)` 112; `get_a(t: …)` 1); `(a: Int64, a: Int64) -> Int64` refused (12 today). Consequences of my reading, shown to the user before the commit and not separately confirmed: row places follow the label-or-position mapping; `(p: A, q: B) -> R` stands at `(x: A, y: B) -> R`; `get_a(1, 2)` passes `(a: 1, b: 2)`. Open: a function value whose A has one component, offered a wider A (the text gives it the application match, no width; `app(g, …)` with `g: ((age: Int64)) -> Int64 = age_of` loads today). Source comments citing the retired sections (typing/callable.rs, subtype.rs, args.rs) are WI-20261104-6HVXM's. Documentation only.

### 2026-11-04T07:22:52Z — feedback — claude

Correction (user, 2026-11-04): a function value at another function type with unrelated labels is refused, as today, not mapped by position. kernel-language §4.4 "A function value at another function type" and §6.7 now say: the two tuples meet only where they carry the same labels in the same order, or one of them is positional and the two are mapped by position; labels in another order (WI-1088) and unrelated labels are refused. Measured on 0eaa2e86: inner(g: (x, y) -> Int64) = g(7, 1) given outer(f: (p, q) -> Int64) refused in both spellings; f positional 71; f (x, y) 71; g positional with f (p, q) 71. A callable written at the slot is still mapped by position (002 fg1 6, fh1 1). Proposal 002 records it. Documentation only.

