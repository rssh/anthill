## Attributes

- id: WI-20261026-8K7W0-a-dot-call-carries-call-site
- created: 2026-10-26T22:23:27Z

- status: Open
- status_agent: claude
- status_at: 2026-10-26T22:23:27Z

- acceptance: cargo-test

- tags: typing

## Description

A DOT CALL CARRIES CALL-SITE TYPE ARGUMENTS, AS ITS APPLICATIVE SPELLING DOES, in an operation body. Today a dot is refused them (WI-20260829-BAD3V; kernel-language §5.4 "A DOT call carries no bracket"). MEASURED 2026-10-26 on 7b456a08, over ByHeat and ByName both providing Score[T = Colour] (ByHeat's score 3, ByName's 1): operation h() -> Int64 = red().score() is the tie refusal, advising the applicative spelling (WI-20260924-DG57J); red().score[Score = ByHeat]() is refused, "call-site type arguments are not supported on a dot call"; Score.score[Score = ByHeat](red()) loads and answers 3. INDEPENDENT OF proposal 068: the typer replaces a dot by the call it resolves to (the DotApply frame, typing/build.rs), built today with type_args: Vec::new(); handing the dot's type arguments to that call puts them on the path a written applicative call already takes in an operation body, which reads no rule-body weave. In a rule's own term a dot stays refused, as an applicative call is, until WI-20261024-TC54R. SITES: the converter's refusal (parse/convert.rs, the dot_application arm) and the loader's for a local-binding receiver (kb/load.rs, CallTypeArgsPosition::DotCall) give way to a slot on Expr::DotApply; the DotApply frame passes it to the synthesized call; it is refused, loudly, where the dot resolves to a field read, a dot @[simp] rule, or a sort-denoting receiver (whose reading is WI-20260824-PAPX0's); the readers that take "a dot is bracket-less by construction" as a premise read the selection instead — arbitrate_defaulted_supplier_tie and the dot's body-less supplier tie (typing/dispatch.rs, WI-842, WI-1035); a dot reaching eval or the printer untyped (Expr::DotApply arms in eval/eval.rs, eval/builtins.rs, persistence/print.rs) is measured, and refuses rather than drops. ROWS, each driven by value: red().score[Score = ByHeat]() answers 3 and [Score = ByName] 1 in an operation body; BAD3V's xs.map[Dst = Int64](f) and its chained hop xs.map(f).map[Dst = Int64](g) type as Iterable.map[Dst = Int64](…) does; a key the resolved callee does not declare is refused as on the applicative call, in the same words; the field-read and dot-rule refusals; a dot with type arguments in a rule's own term is still refused. CONTROLS: the slot dropped at the frame fails the value rows; DG57J's two_witnesses_refuse_a_dot_and_advise_the_applicative_call flips (in an operation body the tie advises the call's own type arguments again — the dot half of TieRepair::BracketElsewhere goes there), while its rule-term dot row keeps its advice until TC54R. SPEC (discuss before writing): kernel-language §5.4's "A DOT call carries no bracket, and now says so" paragraph, and the "read in exactly two positions" paragraph above it.

