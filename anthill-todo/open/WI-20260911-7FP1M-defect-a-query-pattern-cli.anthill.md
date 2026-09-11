## Attributes

- id: WI-20260911-7FP1M-defect-a-query-pattern-cli
- created: 2026-09-11T07:49:07Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T07:49:07Z

- acceptance: cargo-test, scaland-sbt-test

## Description

DEFECT: a query PATTERN (CLI `anthill query`, and `query_pattern_term`-driven tests) carrying a PARAMETERIZED TYPE as an argument never matches -- `domain(nil(), List[T = Letter])` answers nothing, while the same goal inside a rule body answers, and a BARE sort argument in a pattern (`domain(?x, Letter)`) works. Silent: the pattern lowers to something that matches no clause, rather than being refused.

MEASURED 2026-09-11 (CLI, current tree, examples/classic-mini/alphabet-words, whose rules are `rule domain(?x, Letter) :- ...` and `rule domain(?x, List[T = ?T]) :- ...`). `anthill query -p <dir> -i 'classic.alphabet.*' --max-results 0 'domain(?x, Letter)'` -> a, b, c. `anthill query -p <dir> -i 'classic.alphabet.*' -i 'anthill.prelude.List.*' --max-results 0 'domain(nil(), List[T = Letter])'` -> "no solutions"; so does `domain(?w, List[T = Letter])` under `--max-results 8`. Inside a rule, `rule any_word(?w) :- domain(?w, List[T = Letter])` answers `nil [a] [b] [c] [a, a] ...` and `rule check(?w) :- ?w <=> [a(), b(), a()], domain(?w, List[T = Letter])` answers 1. The example's README documents the rule-based query because of this and names the defect.

CAUSE (not driven; where to look first). `convert_query_term` / `convert_query_term_expecting` (kb/load.rs:17063 / :17153) shows no arm for a type application in argument position -- no `type_args`, `make_sort_ref` or type-expression path anywhere in :17063-17400 (grep) -- while the rule-body converter lowers `List[T = Letter]` in a data slot through the type-expression ladder (055: a sort is a legal argument VALUE) into the canonical sort term the rule head `List[T = ?T]` was built from; the residual printer shows that canonical shape as `List(T: Letter)`. Either the query path builds a different term for the bracket form (an application of `List` with a named argument, not the sort term), or `List` / `Letter` resolve differently under `-i` than under a namespace's imports. Print both terms for one pattern before deciding. Also check whether the FACT grammar path the test helper takes (`query_pattern_term` wraps the pattern as `fact <pattern>`) parses `X[...]` as a type application at all.

WHY IT MATTERS. Every relation with a parameterized type in an argument -- WI-743's derived `domain(?x, T)` is the first, rule-body goals like `Modifiable[?t]` are the same family -- is unqueryable from the CLI and from pattern-driven tests except through a wrapper rule, and a test that "queries the relation directly" asserts 0 rows without noticing. The loud-over-silent rule applies: if the query path cannot lower a type application it must REFUSE the pattern, never lower it to a term that matches nothing.

ACCEPTANCE (cargo-test via scripts/test.sh). Pattern-driven over the alphabet-words rules: `domain(nil(), List[T = Letter])` answers 1, and `domain(?w, List[T = Letter])` under a cap answers the cap with first rows `nil`, `[a]`, `[b]`, `[c]`. CONTROLS, each at its site: the bare-sort pattern `domain(?x, Letter)` answers 3 either way BY DESIGN; the wrapper-rule route `any_word(?w)` answers identically either way BY DESIGN; an unresolvable sort name inside the bracket stays a loud error. Say which rows fail with the fix backed out. If the decision is to REFUSE rather than lower, the acceptance row becomes a located refusal naming the pattern, and the two controls stay.

