## Attributes

- id: WI-20261027-K6WFS-result-has-no-host-type
- created: 2026-10-27T20:07:12Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-28T17:55:38Z

- acceptance: cargo-test, scaland-sbt-test

- tags: effects

## Description

`Result` HAS NO HOST TYPE MAPPING, AND THE RUST GENERATOR EMITS CODE THAT DOES NOT COMPILE WHILE REPORTING NO ERROR. A part of WI-20260908-9WVT7 (the `Error` layer, `Error.reify` and `Result`), filed from its leftovers with the user, 2026-10-27.

MEASURED 2026-10-27 on e9587427, over

    namespace test.cgres
      import anthill.prelude.{Int64, String, Option, Result}
      sort Boom
        entity boom(why: String)
      end
      sort Api
        operation find(n: Int64) -> Option[T = Int64]
        operation check(n: Int64) -> Result[E = Boom, T = Int64]
      end
    end

* `anthill codegen rust` says "generated 1 file(s), 0 error(s)" and emits `use anthill::prelude::{Int64, String, Option, Result};` and `fn check(n: i64) -> Result<Boom, i64>;`. Two defects. anthill-stl's prelude (rustland/anthill-stl/src/prelude/mod.rs) exports no `Result`, so the import does not resolve. And the arguments are in anthill's declaration order (`sort E` before `sort T`, stdlib/anthill/prelude/result.anthill), where Rust's is `Result<T, E>`: an import that resolved to std's `Result` would make `Boom` the success type, in silence.
* `anthill codegen cpp -n test.cgres` refuses: "no C++ mapping for parameterized sort 'anthill.prelude.Result' — add a CarrierBinding, or a `fact TypeMapping(lang: some("cpp"), anthill_type: "Result", host_type: ...)`".
* `Option` has a `TypeMapping` in rust_std and cpp_std. scala_std maps scalars only, by design (its `type_map` comment), so Scala is not in this ticket.

WHAT IT NEEDS. A mapping for Rust (std `Result<T, E>`) and for C++ (the cpp profile is C++17/20, so not `std::expected`: a type of the runtime header, or a profile key). And a way for a mapping to give the host's argument order: a parameterized `TypeMapping` names a template and the codegen wraps the type arguments in declaration order (cpp_std.anthill, "the codegen wraps the type arguments"); the entity has no field for an order. Until a sort has a mapping, the Rust generator refuses it as the C++ one does, instead of importing a name the support crate does not export.

ACCEPTANCE: the program above generates Rust that compiles against anthill-stl with `check` returning `Result<i64, Boom>`, and a C++ header that compiles; a Rust row for a sort with no mapping that is refused naming it; full gate green.

