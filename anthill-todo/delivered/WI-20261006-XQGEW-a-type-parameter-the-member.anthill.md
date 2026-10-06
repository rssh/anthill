## Attributes

- id: WI-20261006-XQGEW-a-type-parameter-the-member
- created: 2026-10-06T07:37:10Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-06T11:19:15Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing, guardians

## Description

A TYPE PARAMETER THE MEMBER SUGAR MINTS IS PRINTED BY ITS BARE NAME, NOT AS THE MEMBER THE AUTHOR WROTE. `Triage.run(self: C, box: Mailbox, llm: Llm.C, …) effects {External, Llm.E, Error}` (examples/guardians/lib/spec.anthill): the budget the checker reports for it is `[External, ?E, Error]` (`guardians_test` asserts exactly that list), and a candidate that exceeds it is told "expected declared: [External, ?E, Error], got undeclared effect: Permission[T = Outbox]" (examples/guardians/README.md). `?E` is the operation type parameter §5.4's sugar mints for `Llm.E`; printed by its own name it does not say whose `E` it is. Before WI-20261005-KSSA4 the row was written `llm.E` and printed so. TWO SPECS WITH A MEMBER OF ONE NAME ARE NOT TOLD APART, MEASURED on the tree that delivers KSSA4: `sort Tagger { sort C = ?; effects E = ?; operation tag(self: C) -> Int64 effects {E} }`, `sort Other { sort C = ?; effects E = ?; operation oth(self: C) -> Int64 effects {E} }`, `operation both(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E} = Tagger.tag(x) + Other.oth(y)` is refused "type mismatch in both.effects (op-effects): expected declared: [?E], got undeclared effect: ?_". The row the author wrote is `{Tagger.E}` and what is missing from it is `Other.E`; neither name is in the message, and the missing one is not even printed as a parameter. EXPECTED: a parameter minted for a member prints as that member — `Llm.E`, `Tagger.E`, `Other.E` — in type and effect-row diagnostics and in what reflection reports of a declared row (the guardians budget reads it through `spec_budget`). ACCEPTANCE: the guardians budget is `[External, Llm.E, Error]`, with `guardians_test`, examples/guardians/README.md and examples/guardians/docs/design/measured.md following; the `both` program is refused naming `Tagger.E` as declared and `Other.E` as undeclared; a parameter the author wrote in a bracket (`total[P, El, R]`) prints as before; full workspace green via rustland/scripts/test.sh. REFERENCE: kernel-language §5.4 (a bare spec member in a signature is a type parameter, spelled shorter); WI-20261005-KSSA4.

## Changes

### 2026-10-06T09:03:51Z — feedback — claude

SCOPE CHANGED BY THE USER, 2026-10-06, while this was being delivered. (1) OUT: the acceptance line "`Other.E` as undeclared". In `both` that effect is not a parameter the sugar minted — the signature names only `Other.C` — but the spec's own variable for `E`, left unbound: a member the signature does not name is a free variable in the body, and takes any type (`f(x: Tagger.C) -> Int64 = Tagger.out(x)` loads and returns a `String`). Naming it at the message would guess which instance it came from; it is WI-20261006-GVGSQ's, where making it an unknown of the instance gives the name. This ticket prints `Tagger.E` as declared. (2) IN: a call's bracket does not name a member's parameter. The user asked whether `X.E` beside the enclosing sort's `E` shares a key; it did — `Holder.pick[E = String](hold(v: "s"), b(n: 7))` over `pick(self: Self, x: X.C) -> X.E` in `sort Holder { sort E = ? }` bound `X.E` and was refused, `[E = Int64]` over the same holder loaded, and the receiver spelling `Holder[E = …].pick(…)` gave the other verdict both times. A key of a member's name is now the sort's parameter or no parameter, and a positional counts the written parameters; `eo[E = Int64](…)` and `eo[Int64, B](…)` over a signature that writes no bracket are load errors, where they bound the members' parameters (the second in mint order, the return type's first). ALSO FILED from the same probing, at the user's word: WI-20261006-P962X (a `requires` clause over a named member is not supplied at a call) and WI-20261006-728RW (a member written through a dotted head is not the sugar).

### 2026-10-06T11:37:45Z — feedback — claude

SPEC WORDING CONFIRMED BY THE USER, 2026-10-06 ("spec: ok"), asked with the delivery report. The two passages this ticket adds to docs/kernel-language.md §5.4, as they stand: in the member-sugar paragraph, "The parameter has no name but the spelling. A diagnostic prints it as `Spec.Member` — through an alias, as the alias is written — and a call's bracket does not bind it … where a signature leaves a call none of these, the parameter is written in the bracket instead."; and under "What a key may name", "A parameter the member sugar mints for `Spec.Member` is not declared and is not in the list." Told in the same report and left unsaid by the text: a parameter one signature writes by two spellings (`h(x: Tagger.C) -> TG.C` over `sort TG = Tagger`) prints by the first the loader meets — the return type's, then the parameters' in order — which `wi_xqgew_member_param_test::a_parameter_written_by_two_spellings_is_printed_by_the_first` pins. DELIVERED AS: 25 rows in that module with a ledger of 21 measured back-outs in its header; /code-review run twice (the first pass's 14 findings and the second sweep's fixed here); gate rustland 8669 / 0 / 14, scaland 600.

