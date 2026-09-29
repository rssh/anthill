## Attributes

- id: WI-20260929-9WXK2-a-value-in-type-written-as-a
- created: 2026-09-29T16:03:45Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T16:03:45Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A VALUE-IN-TYPE WRITTEN AS A NAME IN A PROVISION BINDING IS A SORT REFERENCE THERE AND A DENOTED VALUE IN A SIGNATURE, so a correct member is refused. `operation size() -> Int64 = 3`; `provides Store[State = Buf[T = Int64, N = size]]` with a member `peek(s: Buf[T = Int64, N = size])` is refused "parameter 1 is `Buf[T = Int64, N = size]` where the spec's is `Buf[T = Int64, N = size]`" — both sides render alike. The same for an operation bound by name (`peek = bufPeek`), a spec alias fixing the binding, a nested `Modify[counter]` (a zero-arg operation or a nullary-constructor target), and a TOP-LEVEL `provides Store[N = size]`; the literal twins (`N = 3`) load since WI-20260924-F3FYJ. FOUND by F3FYJ's review (verifier V2), PRE-EXISTING. MECHANISM: `sort_binding_to_value`'s `Simple` arm (kb/load.rs) lowers every bare name to `Ref(S)`, while the type position (`type_expr_to_child_inner`) lowers a name resolving to a value place or an operation to `denoted(Ref(x))` (and a `Modify` target's nullary constructor as a place, `type_expr_to_child_modify_target`); `subtype.rs` relates `denoted` only to `denoted`. FIX: give the binding path the type position's value-name classification, keyed per binding on whether the binding's KEY is a declared type parameter of the base, so an op-valued `peek = bufPeek` stays `Ref`: the nested recursion (every key a type parameter), `record_alias_target`, and the top-level loop in `sort_inst_to_value` — whose `sort_view_substitution` reader decides "op binding" from the value's kind and must follow. ACCEPTANCE: rows driving a correct member at a named value-in-type binding (member, op-bound, alias, nested Modify target, top level) that load and run through the provision, each with a wrong-name control refused naming both types; full workspace green via rustland/scripts/test.sh.

