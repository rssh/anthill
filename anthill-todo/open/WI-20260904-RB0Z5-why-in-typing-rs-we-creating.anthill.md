## Attributes

- id: WI-20260904-RB0Z5-why-in-typing-rs-we-creating
- created: 2026-09-04T14:10:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T14:10:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

why in typing.rs we creating value with term with type_var: Value::term(type_param_var_term(kb, Var::Global(vid))), at line 11667,  we can't create Var in value itself ?

