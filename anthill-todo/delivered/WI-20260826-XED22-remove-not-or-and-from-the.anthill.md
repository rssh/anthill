## Attributes

- id: WI-20260826-XED22-remove-not-or-and-from-the
- created: 2026-08-26T19:26:25Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T04:39:12Z

- acceptance: cargo-test, scaland-sbt-test

## Description

REMOVE `not` / `or` / `and` FROM THE IMPLICIT TIER — the three P9Y67 addressed, and only those.

WHY IT IS POSSIBLE NOW, AND WAS NOT BEFORE. WI-20260825-P9Y67 gave `|` / `&` / `!` absolute addresses (`..anthill.kernel.or` / `.and` / `.not`), so the three `PRELUDE_QUALIFIED` entries no longer serve the OPERATORS at all — only WRITTEN bare `not(...)` / `or(...)` / `and(...)`. Before P9Y67 removing them would have broken every minted boolean operator in the corpus.

THE POPULATION, MEASURED. Entries deleted from `PRELUDE_QUALIFIED` (kb/load.rs) and the full workspace run: 20 failures across 8 test files, and a source census over `.anthill`:

  stdlib/anthill/reflect/typing.anthill:270,271                  not x2
  examples/guardians/lib/classify.anthill:57,63,74               not x3
  examples/guardians/lib/spec.anthill:41,44                      not x2
  examples/github-todo/rules.anthill:64                          not
  rustland/anthill-todo/anthill/rules.anthill:51                 not
  examples/webots-modelling/lf1/follower_transponder.anthill:134 and  (VALUE position, inside an `if`)

Ten real sites in six files. `stream.anthill` and `relation.anthill` match a naive grep only inside COMMENTS and need no edit. Rust-side: `push_choice_test`, `cut_test`, `lf1_real_spec_test`, `prove_tactic_test`, `wi529_boolean_operator_split_test`, `wi1046_boolean_goal_routing_test`, `wi896_labeled_predicate_head_test`, `wi873_dispatch_rewrite_completeness_test` — inline fixtures, same repair. Plus three tests that assert on the TABLE ITSELF: `wi900_implicit_tier_agreement_test`, `wi1075_absolute_path_test::rung_two_census_stays_zero`, `wi913_host_name_ladder_test`.

THE REPAIR IS MECHANICAL, AND THAT IS MEASURED RATHER THAN ASSUMED. Either import spelling serves BOTH positions, because the position routing runs on the RESOLVED symbol:
  `import anthill.kernel.{not, or}`         — goal `not(p(99))` answers 1; op-body `not(true)` answers false (routed to `Bool.not`)
  `import anthill.prelude.Bool.{not,or,and}` — op-body works; goal `p(?x) | p(99)` answers 1 (routed to `kernel.or`)
So no site needs per-site judgement. Written: `anthill.kernel.{not, or}` and `anthill.prelude.Bool.{and}`, each naming what the name means where it is usually written.

A MISSED SITE IS LOUD, never a wrong answer: "rule-body goal `or` names nothing: … Fix the spelling, or import the namespace that declares `or`", with line:col.

NOT IN SCOPE — the rest of that table, and the reason is a real difference rather than thrift. `unify` and `struct_eq` are reached by `minted_connective_symbol`, which calls `resolve_implicit` DIRECTLY, so their tier entries back the OPERATORS `<=>` and `===` and not merely written names. Removing those breaks the operators until they carry addresses of their own, which is P9Y67's move one family over and its own ticket. `push_choice` / `find_dictionary` / `cut` need their own check and are untouched here.

THE LANGUAGE RULE CHANGES, and the docs that state the old one must move with it: kernel-language.md §5.5 and `parse::pratt::CONNECTIVE_FUNCTORS` currently say "the operator is uncapturable, the WRITTEN name still resolves with no import" — the second half stops being true, and that split was P9Y67's stated reason for keeping the entries.

CONTROL: with the three entries removed and every site imported, the corpus is green; deleting any ONE import turns its site into the located "names nothing" error above (that is the row that says the import is what carries it, not a surviving fallback). And a minted `|` / `&` / `!` keeps working in a namespace with NO import at all — that is the row that says the operator half is untouched.

ACCEPTANCE: the three entries are gone from `PRELUDE_QUALIFIED`; a written bare `not(...)` with no import is a located load error; a minted `!` with no import still answers. Full workspace green via rustland/scripts/test.sh, and scaland-sbt-test.

## Changes

### 2026-08-27T03:47:58Z — feedback — claude

DELIVERED, AND THE MIGRATION COST THE TICKET PRICED WAS REMOVED RATHER THAN PAID.

WHAT LANDED. `anthill.kernel.not`, `anthill.kernel.or` and `anthill.prelude.Bool.and` are gone from `PRELUDE_QUALIFIED`. Ten source sites in six `.anthill` files carry an import instead; eleven inline fixture sites in six Rust test files do the same. `PRELUDE_QUALIFIED` is 19 entries.

THE SITES, as filed and as edited:
  stdlib/anthill/reflect/typing.anthill                          import anthill.kernel.{not}
  examples/guardians/lib/classify.anthill                        import anthill.kernel.{not}
  examples/guardians/lib/spec.anthill                            import anthill.kernel.{not}
  examples/github-todo/rules.anthill                             import anthill.kernel.{not}
  rustland/anthill-todo/anthill/rules.anthill                    import anthill.kernel.{not}
  examples/webots-modelling/lf1/follower_transponder.anthill     import anthill.prelude.Bool.{and}
Fixtures: push_choice_test x3, cut_test x2, wi529, wi873, wi896 x2, wi1046, wi_p9y67 — one import line each, no assertion or expected value touched.

THE COST THE TICKET NAMED, AND WHY IT IS NOT PAID. The body said a forgotten import is loud ("names nothing") EXCEPT in a scope that declares the same name, where it is silent. Driven, on WI-896's own fixture: `rule or(?x)` beside `rule reach896(?x) :- or(p896(?x), q896(?x))` answered 0 with exit 0 and no diagnostic — WI-896's original defect, re-created by this ticket's own migration. THAT IS NOW A LOAD ERROR, and the repair is not in this ticket's population at all.

  `goal_arg_slots` (kb/mod.rs) matched `("or" | "and", 2)` on the resolved symbol's LOCAL NAME, which a USER's own `or` answers as well as `anthill.kernel.or`. So a local arity-1 `or` was classified as the CONNECTIVE at arity 2, its arguments were read as GOALS, and the wrong-arity refusal never ran. The `pos_arity == 2` gate those tables carry stops a wrong-arity CONNECTIVE and cannot stop a right-arity WRONG SYMBOL. `is_goal_conjunction` had the same shape.

  THE SEPARATING PAIR, two identical programs differing only in the head's NAME:
    rule zz(?x) :- p(?x)  /  rule r(?x) :- zz(p(?x), q(?x))   -> LOAD ERROR, "expected a term a clause of `zz` can match (1 positional), got 2 positional"
    rule or(?x) :- p(?x)  /  rule r(?x) :- or(p(?x), q(?x))   -> 0 solutions, exit 0
  Keyed on the SYMBOL (`is_goal_connective` / `kernel_connective_is`), the second now gets the first's error verbatim. The arity check was never missing; it never ran. Pinned by `wi896_labeled_predicate_head_test::a_user_or_head_gets_the_ordinary_wrong_arity_refusal`, whose `zz` arm is the control that says the row measures the KEYING and not the arity check.

  Done INLINE rather than filed, at the user's direction and correctly: ~40 lines, most of them the doc recording the pair.

TWO TESTS NEEDED MORE THAN AN IMPORT, and one measurement explains both.

  MEASURED across all 22 tier entries: `anthill.prelude.Bool.and` is the ONLY target ABSENT from a bare KB. Every other one is pre-declared in Rust (`register_stdlib_scopes` / `register_builtin_tag`) and so present with no stdlib at all — `anthill.kernel.not` and `.or` included. An earlier claim in this session that all three were `.anthill`-only was WRONG; it came from probing short-name resolution, which consults the tier and is circular. The right question is whether the qualified TARGET exists.

  `wi900_implicit_tier_agreement_test` ran two opposite directions off ONE fixture: the stdlib-less half needs the target ABSENT, the loaded half needs the name to be a TIER ENTRY. After this ticket no single name gives both, so the loaded half moved to its own `cons` fixture (`namespace wi900.loaded`). The stdlib-less half, its fixture and its assertions are UNTOUCHED and still pass on `and` — which is the half the user identified as the one that survives. Both directions keep a witness; nothing was deleted.

  `wi913_host_name_ladder_test::make_apply_resolves_an_implicit_tier_functor` passes a bare RUNTIME STRING to the reflection API, so there is no source file and no import to add. Re-pointed `"not"` -> `"cons"`. Its subject — a host passes a bare name and the tier answers — is unchanged; it needs the name to be a tier entry and nothing more.

NOT IN SCOPE, unchanged and restated because the difference is real: `unify` and `struct_eq` are reached by `minted_connective_symbol`, which calls `resolve_implicit` DIRECTLY, so their tier entries back the OPERATORS `<=>` and `===` rather than written names. Removing those breaks the operators until they carry addresses of their own. `push_choice` / `find_dictionary` / `cut` untouched.

FINAL STATE: rustland 5818 passed / 0 failed across 36 binaries; scaland 518/518.

### 2026-08-27T04:39:08Z — feedback — claude

ADDENDUM AFTER /code-review — THE `not` HALF OF THIS MIGRATION WAS UNNECESSARY, AND THE DELIVERY'S STATED CONTROL WAS FALSE.

`not` IS A PREFIX OPERATOR, so a written `not(x)` never runs the name ladder. `tree-sitter-anthill/grammar.js` `_prefix_op: choice('!', 'not')`, and `parse::pratt::prefix_entry` mints `NOT_FUNCTOR = "..anthill.kernel.not"` for BOTH spellings — an absolute address. DRIVEN: `namespace t3 { fact p3(1) fact q3(2) rule r3(?x) :- p3(?x), not(q3(?x)) }` with NO IMPORTS AT ALL answers 1 solution, identically before and after this ticket.

CONSEQUENCES, all three:
  * The five `import anthill.kernel.{not}` lines this ticket added are INERT. REMOVED.
  * The control recorded in the previous entry — "deleting any ONE import turns its site into the located `names nothing` error" — is FALSE at 9 of the 10 migrated sites. It holds only for `and` at `follower_transponder.anthill:134` and for the `or`/`and` test fixtures. `or` and `and` are genuinely loud; `not` never was, because there was nothing to be loud about.
  * `anthill.kernel.not`'s tier entry was ALREADY DEAD before this ticket. Removing it changed nothing, which is how that was discovered. `stdlib/anthill/kernel/kernel.anthill`'s own `not` doc had credited the tier for what the OPERATOR was doing ("a bare `not` reaches this declaration ... through the implicit prelude") and said an import there "buys nothing and contradicts what this namespace is for" — the second half was right and this ticket had briefly contradicted it. Corrected at the declaration.

So the real source-side migration is ONE site: the `and` in a value position at `follower_transponder.anthill:134`. The fixture side is unchanged — `or`/`and` fixtures needed their imports.

A DEFECT THIS TICKET LEFT HALF-FIXED, filed rather than papered over. `goal_slot_readings` has five arms; XED22 moved the two goal connectives off the name match and left `("forall_in" | "some_in", 3)` and `("forall_impl", 3)` on it, plus `is_discharge_functor`'s `local_name_of(f) == "forall_impl"`. DRIVEN, the same separating pair one coordinate over: a user `rule forall_impl(?x)` beside `forall_impl(a, b, c)` LOADS CLEAN and answers one bogus `?x = ?_`, while the identical program with the head renamed `zzz` is a load error. They could NOT move with the connectives: `or`/`and` have declared kernel targets to compare against, and a marker is minted `kb.intern("forall_impl")` — a bare symbol with no qualified name and no declaration anywhere — so keying it needs the markers to carry an identity first. WI-20260827-J03AT owns it, with both routes and the census each needs; the split is documented at the table so the next reader is not told the name-keying is the design.

EIGHT DOC SITES CORRECTED, every one prose asserting the tier entries still exist: `kernel-language.md` §5.5 ("they **keep** their implicit-tier entries") and the implicit-prelude enumeration (`not`, `or` listed as members); `parse::pratt::CONNECTIVE_FUNCTORS`'s "A WRITTEN BARE `not(...)` IS UNTOUCHED"; three `PRELUDE_QUALIFIED` paragraphs in `kb/load.rs` including the one telling the next editor how the table is guarded, and the stale WI-529 comment left standing exactly where `Bool.and` was deleted from under it; `kernel.anthill`'s `not` declaration; and `goal_slot_readings`' own header, which still called the keying "by name" directly above the arm that had abandoned it.

`wi900_implicit_tier_agreement_test`'s stdlib-less half NOW PASSES FOR A DIFFERENT REASON, and says so. It used to separate "the ladder consulted the tier and the tier had no target" from "the name means nothing at all", because `Bool.and` was the only one of 22 targets absent from a bare KB. With `and` out of the tier it exercises an ordinary unknown name, indistinguishable from `zzz`. It still measures WI-900's actual defect (two sorts' same-named heads must not collapse onto one global), which is why it is kept rather than retired, and the doc records that NO name remains that could restore the sharper reading.

PERF, taken because the codebase already had the pattern and the reason written down: `or_connective_sym` / `and_connective_sym` cached beside `eq_connective_sym` (WI-627's move), so `is_goal_connective` — asked per goal node at load and again in the typer's rule-body walk — is a field compare rather than two long-string `by_qualified_name` lookups. `layer.rs`'s exhaustive destructure forced them to be classified for rollback, which is the right lifecycle: a layer that loads the kernel sets them and a discard must undo it.

FINAL STATE: rustland 5818 passed / 0 failed across 36 binaries; scaland 518/518. /code-review findings 1-12 all addressed — 1 and 2 by ticket (J03AT), the rest inline.

