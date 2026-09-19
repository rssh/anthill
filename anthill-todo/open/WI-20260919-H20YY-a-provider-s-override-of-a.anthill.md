## Attributes

- id: WI-20260919-H20YY-a-provider-s-override-of-a
- created: 2026-09-19T13:38:40Z

- status: Open
- status_agent: user
- status_at: 2026-09-19T13:38:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROVIDER'S OVERRIDE OF A DEFAULTED, RECEIVER-LESS SPEC MEMBER IS NEVER REACHED THROUGH A REQUIREMENT SLOT -- the spec's DEFAULT body runs instead, silently. Found while writing WI-20260918-R541X's (C) fixtures (recorded in its feedback).

MEASURED 2026-09-19, on the R541X delivery commit (c3fe68ab):
      sort TypeTerm { sort T = ?  operation valueOf() -> Type = T }          -- a DEFAULT body
      sort Boom { entity boom(why: String)  provides TypeTerm[T = Boom] }
      sort Box  { sort V = ?  entity box(v: V)  provides TypeTerm[T = Box[V = V]]
                  operation valueOf() -> Type = Option[T = V] }              -- Box's OVERRIDE
      operation tagOfP[P](x: P) -> Type requires TypeTerm[T = P] = TypeTerm.valueOf()
      tagOfP(box(boom("x")))   answers `Box(V: Boom)` -- the DEFAULT's `T`; wanted the override's `Option(T: Boom)`
    Loads clean, no diagnostic. CONTROL: the same member made BODY-LESS (`TypeTermB.valueOfB`, R541X's (C) fixture) DOES dispatch to the provider's member through the slot.

CAUSE, FROM READING (NOT INSTRUMENTED). In `check_apply_iter` (kb/typing.rs), the requirement-slot routes -- the WI-239 `find_requires_location` pre-check, `defer_to_op_scoped_slot` (WI-822/1091), and the `DispatchOutcome` arms -- all sit inside the `lookup_spec_op_dispatch(kb, fn_sym).is_some()` block, which covers BODY-LESS spec ops only. A defaulted member is consumed as a NORMAL op (WI-365). WI-365's own carve-out threads a self-RECEIVER carrier (`self_receiver_spec_sort`), and eval's `resolve_carrier_override_by_value` directs by an argument VALUE. A receiver-less member has neither, so the call is a plain apply of the default: `classification = None` at eval, which was observed for this very call while debugging R541X. WI-1093's note that a receiver-less spec op has no value-directed repair applies here verbatim: only the dictionary can direct it, and nothing consults the dictionary.
    NOT MEASURED: the SORT-level `requires` spelling of the same program, and a defaulted member WITH a receiver argument reached through a slot inside a generic scope.

WHY IT MATTERS NOW. WI-20260911-3MV2C's direction is `raise(error: T) ... requires ErrorTag[T]` whose DEFAULT is the type term. A provider that overrides `ErrorTag`'s default -- the one reason to write a provision beyond the default -- would be ignored exactly like this, silently. And R541X's (A) made the default's answer RIGHT for the spec's own `T`, which makes the ignored override harder to notice.

DIRECTION, not decided here: route a defaulted spec member called inside a scope that holds a slot over its spec through the SAME slot dispatch a body-less one takes (the dictionary's provider member if it has one, else the default). That is the dictionary-passing reading 058 gives a spec op. The open question is whether a defaulted member reached with NO slot in scope should keep today's plain-default reading (probably yes: nothing selects a provider there).

ACCEPTANCE: the fixture above DRIVEN to `Option(T: Boom)` through the op-scoped slot, and through the sort-level spelling. A provider WITHOUT an override still gets the default (control: `tagOfP(boom("x"))` -> `Boom`, R541X's headline row, which must stay green). The body-less control is stated as passing either way. Each positive row names the back-out that turns it red. Full workspace green via rustland/scripts/test.sh.

