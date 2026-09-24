## Attributes

- id: WI-20260924-F3FYJ-a-provision-s-value-in-type
- created: 2026-09-24T07:50:33Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T07:50:33Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A PROVISION'S VALUE-IN-TYPE BINDING LEAKS THE SortView WRAPPER INTO THE MEMBER-FIT CHECK, so a correct member is refused. `provides Store[State = Buf[T = Int64, N = 3]]` with `operation peek(s: Buf[T = Int64, N = 3]) -> Bool = true` is refused 'parameter 1 is `Buf[T = Int64, N = 3]` where the spec's is `SortView(Buf)[T = Int64, N = 3]`'; a genuinely wrong member (N = 4) gets the same refusal, so the check cannot tell them apart. A ground nested binding (`State = Buf[T = Int64]`) loads. FOUND by WI-20260923-ZBWMC's review (verifier V7) and PRE-EXISTING: on HEAD since Z1Q8B (5ec10808) started comparing denoted-bearing types; the 09-20 binary loaded it because the comparison skipped them. MECHANISM: `assemble_binding_value` builds the plain parameterized application only when every binding is a term and no positional overflows, else it wraps the binding in a `SortView` Value::Entity; the provision's σ is `spec_param_sigma` over the view's raw named args (typing/signature.rs), while a type position builds `TypeNode::Parameterized { base: Buf, … }`, so the two never match. FIX OPTIONS: at the source (build the same parameterized application a type position builds when there is no overflow positional, keeping SortView for the overflow case; changes the stored SortProvidesInfo shape, so the WI-366 value-in-type readers need a full run), or at the reader (unwrap a nested SortView in `spec_param_sigma`; other provision readers would still see the wrapper). Also: ZBWMC's bare-spec narrowing gets no term for such a binding, so `Store.State` is not narrowed there. ACCEPTANCE: a test that drives a correct member at a value-in-type provision binding (loads, and a call through the provision runs), with the wrong member still refused as the control; full workspace green via rustland/scripts/test.sh.

