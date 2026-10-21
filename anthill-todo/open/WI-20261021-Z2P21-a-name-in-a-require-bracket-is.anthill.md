## Attributes

- id: WI-20261021-Z2P21-a-name-in-a-require-bracket-is
- created: 2026-10-21T16:18:34Z

- status: Open
- status_agent: claude
- status_at: 2026-10-21T16:18:34Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A NAME IN A REQUIRE BRACKET IS RESOLVED WHERE IT IS WRITTEN: `require[Zeroable[T]]` is `require[Zeroable[T = T]]`, and at namespace level, where nothing is named `T`, it is a load error, 'T not found' (user decision 2026-10-21, on WI-20260925-0RRQP). Positional and named are one binding, so the right-hand `T` is a type argument like any other; inside a sort that declares `T` (`sort T = ?`) it is that sort's `T`, as today. 'Any instance' is spelled `require[Zeroable[?]]` or `require[Zeroable]` (an unwritten parameter is open). TODAY (measured 2026-10-21 on e059b486): over `sort Zeroable { sort T = ?; operation tag(x: T) -> Int64 = 0 }`, `rule get(?x, ?d) :- ?d = require[Zeroable[T]], Zeroable.tag(?x, ?t)` written in a namespace loads, stored as `find_dictionary(Zeroable, tag, ?x, out: ?d)`, and answers the dictionary for `?x`'s type; `require[Zeroable[?]]` (stored `find_dictionary(Zeroable(T: ?v), tag, ?x, out: ?d)`) and `require[Zeroable]` answer the same; `require[Zeroable[T = Nope]]` is refused, 'names neither a sort nor one of Zeroable's own type parameters (T)'. The exemption is deliberate — `report_dropped_spec_binding` in rustland/anthill-core/src/kb/load.rs returns early for 'the spec's own parameter name — an open binding' (WI-20260830-X9PB4's wildcard, narrowed by WI-20260909-51W18), and its census counts the corpus's free-name bindings: `Eq[T]` x24, `Desc[T]` x23, `PartialEq[T]` x15, plus `WeakOrd[T]`, `Ord[T]`, `Relatable[T]`, `Spec[T]`, `Spec[C]`, `Walk[C]`, `Bag[E]`, `Desc[T = T]`. It reads a name written in the namespace in the spec's scope. STEPS: (1) MEASURE FIRST — remove the exemption under a temporary switch and run the workspace (rustland/scripts/test.sh) and scaland testFull; count which uses are at namespace level (refused) and which sit in a sort that declares the name (unchanged). (2) Remove the exemption; the refusal names the name and the repair `Spec[?]` / `Spec`. (3) Rewrite the refused uses in stdlib, examples and tests as `require[Spec[?]]` or `require[Spec]`. (4) kernel-language.md: the 'Clause-level requirement binding (`require[X]`)' example `rule p(?x, ?y) :- require[Eq[T]], eq(?x, ?y)` and its twin are rewritten, and the bracket's name rule stated (a name in it is resolved where written). ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven): at namespace level `require[Zeroable[T]]` is refused naming `T`; `require[Zeroable[?]]` and `require[Zeroable]` load and answer the dictionary for the witness's type (`get(wrap(inner: sum()), ?d)` gives `Dictionary(Dictionary(impl: Sum), impl: Wrap)` over a conditional `Wrap provides Zeroable[T = Self] :- Zeroable[E]`); inside `sort Box { sort T = ?; … require[Zeroable[T]] … }` the bracket reads `Box`'s `T`, as before. CONTROLS: the rewritten corpus rows keep their answers; the back-out of the removal named at its site.

