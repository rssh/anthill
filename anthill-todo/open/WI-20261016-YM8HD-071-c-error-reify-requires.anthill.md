## Attributes

- id: WI-20261016-YM8HD-071-c-error-reify-requires
- created: 2026-10-16T14:51:24Z

- status: Open
- status_agent: claude
- status_at: 2026-10-16T14:51:24Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261016-SQZPQ-071-b-typepattern-and

- tags: proposal-071

## Description

071 (c): `Error.reify` REQUIRES `TypePattern[T = T1]`, AND `ErrorTag` IS RETIRED. Proposal 071 §1.4.
THE CHANGE: `operation reify[Rho, X, T1](…) requires TypePattern[T = T1]`; the boundary calls `TypePattern.admits` with the raised value's type — its head sort as a type until stage (d) — instead of reading the `TypeValue` sub-dictionary of `ErrorTag`'s evidence by position (`ErrorLayer::reify_payload_sub`). Every verdict is unchanged. Retired with it: `sort ErrorTag`, `Error provides ErrorTag[T = T] :- TypeValue[T = T]`, `is_error_tag_spec` and every gate that reads it (the rule-body refusal that is the marker exemption's exception, `former_repair`'s and `library_instances`' arm, the bridge's absence), and WI-20260908-9WVT7's finding F1.
MEASURED (2026-10-16, F1): `sort Wrapper … provides ErrorTag[T = Boom]` is selected over `Error`'s row and carries no `TypeValue`, so every `Error.reify` at `Boom` dies at run time; `provides ErrorTag[T = (a: Int64, b: String)] :- TypeValue[T = Other]` makes the tuple's boundary catch `other(n: 7)` (exit 11, where 22 is right).
ACCEPTANCE (cargo-test via rustland/scripts/test.sh, scaland sbt testFull): the reify rows re-pointed and their verdicts unchanged; `ErrorTag` named in a program is an ordinary unresolved name; F1's two programs no longer reach a boundary through a written row; the rule-body refusal of an unbuildable slot still refuses, now through `TypePattern`.

