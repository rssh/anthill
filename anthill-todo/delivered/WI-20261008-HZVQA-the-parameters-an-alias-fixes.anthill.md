## Attributes

- id: WI-20261008-HZVQA-the-parameters-an-alias-fixes
- created: 2026-10-08T09:06:40Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-09T06:57:55Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE PARAMETERS AN ALIAS FIXES DO NOT RIDE A COMPANION CALL THROUGH IT — over `sort Box[V]` with `operation wrap(x: V) -> V` and `sort CA = Box[V = Int64]`, `CA.wrap("s")` passes the argument check with `V` free and is refused only where its String result meets an Int64, while `Box[V = Int64].wrap("s")` is refused at `wrap.x: expected Int64, got String`. The let-bound `let t = CA; t.wrap("s")` does as the written `CA.wrap("s")` does. Measured 2026-10-08 on fd1cf282.

WHY. A member path is read through an alias to the sort it stands for (`read_path_through_aliases`, kb/load.rs: `CA.wrap` is `Box.wrap`), and the alias's bindings are not carried to the call. WI-20260824-PAPX0 made the let-bound spelling mirror that, so the two agree.

WHAT. Decide with the user whether a call through an alias is at the alias's bindings. My reading is yes: a type position reads `CA` as `Box[V = Int64]`. If so, carry them on the written route and in `denoted_sort_dot` (kb/typing/type_receiver.rs) in one change. The row `an_alias_denotes_what_it_stands_for` (wi_papx0_dot_receiver_split_test) compares the two spellings and fails if one moves alone.

CONTROL. `CA.wrap(5)` answers; `CA.wrap("s")` is refused at the argument, written and let-bound; an alias that owns members is still read as written. Say which rows fail with the change backed out.

DONE WHEN: both spellings refuse `CA.wrap("s")` at `wrap.x`; the gate is green.

## Changes

### 2026-10-09T06:57:42Z — feedback — claude

DELIVERED 2026-10-09. THE RULE AS BUILT. A member reached through a type alias is reached at the parameters the alias fixes. Over `sort CA = Box[V = Int64]`: `CA.wrap(…)` is the call `Box[V = Int64].wrap(…)` makes, written or through a name a `let` bound to the alias; `CA.mk(…)` is the construction `Box[V = Int64].mk(…)`; a rule cited `CA.rel` is cited as `Box[V = Int64].rel` is. A parameter the alias leaves open is left to the call, and an alias that fixes nothing says nothing.

DECIDED WITH THE USER in the session (2026-10-08 and 09). (1) Yes to this ticket's question. (2) A receiver names the instance the call is at and says nothing more of the result: `ints() -> Cell[V = Int64]` called `Cell[String].ints()` is a `Cell[V = Int64]`, `empty() -> Cell` called `Cell[V = Int64].empty()` is some cell ("V in output type is not V in input type"). (3) A constructor in an operation body reads its receiver: the bracket or alias binds `V`, the fields are checked at it, the value is the sort at it. (4) An operation's own parameter a call leaves unfixed stays refused (`make[A]() -> Opt[T = A]`, "refusal in make"); a variant in which the receiver fills it was written and backed out. (5) The callee's bracket on a constructor stays refused here and is WI-20261009-B6QYA.

MEASURED, before and now. `operation go() -> String = CA.wrap("s")`: loaded and answered "s"; refused `wrap.x (op-arg): expected Int64, got String`, as the let-bound spelling is. `let r = CA.rel`: refused "not determined at this citation"; loads. `BL.insert(BL.empty(), …)` over `sort BL = SortedSet[T = String, O = ByLength]`: refused, no provider; orders by length. `Cell.count(Cell[V = Int64].empty())` over `empty() -> Cell`, and `Cell.count(Cell[V = String].ints())`: refused at the call's own return; load. `Pair[L = Int64, R = String].swap(p)` over `swap(p: Self) -> Pair[L = R, R = L]`: refused at `swap.return`; a `Pair[L = String, R = Int64]`. `Box[V = Int64].mk(5)`: refused, bracket not read; a `Box[V = Int64]`. `CA.mk("s")`: built a `Box[V = String]`; refused `mk.v (entity-field): expected Int64, got String`. `CBox[V = Int64].trigger(5, a: 7)` on a variadic-capture head: answered 5, the rule not firing on a call with a receiver; 112, as `CBox.trigger` does.

WHERE. The loader's dotted join answers the alias a member path is read through (`dotted_join`, `dotted_alias_receiver`, kb/load.rs) and `build_recv_type` gives a call through it the receiver the bracket spelling writes; a bare rule citation through such an alias is the zero-argument call. `alias_receiver_type` (typing/sort_alias.rs) is the one reader, for the loader and for `denoted_sort_dot`. `Expr::Constructor` has a `recv_type` slot, carried at every rebuild site, and `check_constructor_iter` seeds from it through `seed_receiver_type_args`. `check_apply_iter` no longer compares a receiver that names the callee's own sort with the declared return. `fold_capture_redex` carries a receiver through the reshaped redex.

ONE WRONG TURN, kept here because the second /code-review found it: a construction with a receiver was first built as an application, the node that had the slot. `IF.fb(inc)` and `IH.hold(poly(), 1)` then stopped loading, the constructor node being what argument typing keys on. The slot on the constructor node replaced it.

UNCHANGED, each measured. A constructor in a rule body is a term the clause matches and takes no receiver: a written bracket is refused as unread, standing alone or under an `if`, and an alias names the sort's constructor (`?v <=> Num.n(k: "s")` loads over `n(k: Int64)` — fields of a rule-body term are not checked). `import lib.CA.{wrap}` binds the name, and `wrap("s")` loads. A macro named in a rule's right-hand side through such an alias is refused at load, as the bracket spelling is. A receiver on a member another sort declares keeps the old comparison with the return; no program reaching it was found.

FILED. WI-20261009-ZY11J: a value typed `CA` is refused by the sort's own operations (`Box.unbox(b)` at `unbox.dispatch`), with no alias call in it. WI-20261009-B6QYA: a member that uses its sort's parameter takes it as its own, so the callee's bracket binds on a constructor.

CONTROLS. `wi_hzvqa_alias_receiver_test`, 23 rows; its header lists, per piece backed out, the rows that fail, and the one that passes under every back-out. Changed rows elsewhere: `wi_papx0_dot_receiver_split_test` (an alias pins `wrap.x` in both spellings; a bracket on a constructor binds), `wi_w6jh0_companion_receiver_bracket_test` (the constructor rows are their own test), and three pins of "the receiver bracket's" now read "the receiver's", an alias call writing no bracket.

GATE. `rustland/scripts/test.sh`, full: 36 binaries, 8847 passed, 0 failed, 14 ignored. `sbt -batch testFull`: 630 passed. scaland has no alias table and no typer, so nothing mirrors this and no scaland file changed.

