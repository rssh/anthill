## Attributes

- id: WI-20261017-090MT-an-ill-formed-type-projection
- created: 2026-10-17T09:39:56Z

- status: Open
- status_agent: user
- status_at: 2026-10-17T09:39:56Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN ILL-FORMED TYPE PROJECTION IN A SIGNATURE IS CHECKED ONLY WHEN THE OPERATION HAS A BODY -- `operation check(s: Wrapper, k: s.cell.T) -> String` over a bare `Wrapper` (its P unconstrained) loads body-less, and with any body (even `= ""`) is refused 'expected a well-formed type projection, got no requires bound on Wrapper whose carrier is this abstract type parameter declares a member T; cannot project T'; `chain(a: Outer, b: a.P, c: b.Q)` likewise ('cannot project Q off an abstract receiver with no concrete sort'). A signature is a promise every caller and provider reads, so its well-formedness cannot depend on whether a body follows. Found migrating fixtures for WI-20260909-M8QWJ (wi426, wi397, wi398 had to move such operations into a sort without constructors). DECIDE: is the projection through a bare receiver legal (then the body check must accept it) or not (then the signature check must refuse it body-less too) -- and measure the corpus either way.

