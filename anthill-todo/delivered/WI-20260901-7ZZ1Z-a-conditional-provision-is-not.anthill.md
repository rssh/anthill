## Attributes

- id: WI-20260901-7ZZ1Z-a-conditional-provision-is-not
- created: 2026-09-01T08:55:17Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-01T10:00:21Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A CONDITIONAL PROVISION IS NOT ENFORCED WHEN THE TYPER RUNS INSIDE `load_phase_inner`: the SAME check, on the SAME sorts, accepts through `load_all` what it refuses when the typer is the first pass to see the KB. WI-274's rule loads clean.

Found while measuring whether `load::load` could be deleted in favour of `load_all` (WI-20260901-Q68AK). It is NOT a load/load_all API question — it is a live "loads clean while breaking a stated rule" defect in the ORDINARY entry point, and it is filed on its own because it is worth fixing whether or not that API ever changes.

THE FIXTURE is `typing_test::conditional_spec_field_rejects_eq_list_of_non_eq_elements`, shipped and green today:

    namespace test.wi274_list_bad
      import anthill.prelude.{Eq, List, Int64}
      fact Eq[T = Int64]
      sort NonEq
        entity ne(id: Int64)
      end
      sort EqList
        sort A = ?
        requires Eq[T = A]          -- the provision is CONDITIONAL on A having Eq
        fact Eq[T = List[T = A]]
      end
      sort Box
        entity Holder(item: Eq[T = List[T = NonEq]])
      end
      fact Holder(item: [ne(1)])
    end

`NonEq` provides no `Eq`, so `Eq[T = List[T = NonEq]]` must not be satisfiable and the `Holder` field must be refused. The test asserts exactly that.

MEASURED (throwaway probe, since removed), stdlib pre-loaded in both arms, SAME source:

    route 1  load::load(kb, src) then type_check_sorts(kb, &result.defined_sorts)
             -> 1 error, naming Holder
             sorts = [test.wi274_list_bad.Box, .EqList, .NonEq]

    route 2  load_all_per_file(kb, [src])
             -> Ok. ZERO errors.
             sorts = [test.wi274_list_bad.Box, .EqList, .NonEq]   -- IDENTICAL

    route 2b then type_check_sorts(kb2, &r2.defined_sorts) on that same KB
             -> 0 errors

SO IT IS NOT A DIFFERENT SORT LIST AND NOT A CONSUMED DIAGNOSTIC. The two routes hand `typing::type_check_sorts` the same three sorts and it answers differently, and on the `load_all` KB the refusal is not re-derivable by asking again. Something in the passes `load_phase_inner` runs BEFORE `type_check_sorts` (kb/load.rs:12563) leaves the KB in a state where `Eq[T = List[T = NonEq]]` is satisfied.

WHICH PASS IS NOT IDENTIFIED, and this ticket does not name one. Do not inherit a culprit from this paragraph: by ORDERING the candidates that stand between `load_with_visited` and the typer are `resolve_instantiations`, `build_sort_ops_table`, `derive_forwarded_provisions`, `seed_default_provider_index` and `validate_rigid_projection_formations`; `eq_derive::run` stands AFTER the typer and so cannot be it. The cheap next step is to bisect them — run `load_all`'s prologue with one pass neutralized at a time and watch the verdict flip.

THE OTHER RESOLUTION MUST BE RULED OUT FIRST. It is possible that `load_all` is RIGHT and the rule (or the test) is wrong — that one of those passes legitimately supplies a provision making the program well-typed, and route 1 refuses only because it asks before that supply exists. If so the defect is the TEST, which has been asserting a refusal the shipped pipeline does not make. Settle which of the two verdicts is correct BEFORE changing either side; the fixture is 30 lines and both answers are cheap to state.

WHY IT MATTERS BEYOND ITSELF. The only thing in the workspace detecting this today is a test that reaches for the PARTIAL loader (`load::load`, which runs none of `load_phase_inner`'s ~30 passes) and drives the typer by hand. So the rule is pinned only on a route no production code takes, and is unenforced on the route every caller takes. That is also why it BLOCKS WI-20260901-Q68AK: deleting `load` today would delete the sole detector of a live bug.

ACCEPTANCE: the fixture above reaches ONE verdict, reached the same way by `load_all` and by a hand-driven `type_check_sorts`, and a test asserts it through `load_all` — the route callers use. If the refusal is correct, `load_all` refuses it and the pass that was suppressing it is named at its site with the reason. If the acceptance is correct, the WI-274 test is rewritten to assert acceptance and the rule's statement in the spec is corrected to match. Either way, state which of the five candidate passes decided it, measured by neutralizing that pass alone. Regression: nothing else in the workspace suite changes verdict.

## Changes

### 2026-09-01T09:24:02Z — feedback — user

INVESTIGATION 2026-09-01. Reproduced with controls, mechanism partly located, and ONE EARLIER CLAIM OF MINE WITHDRAWN. Read the withdrawal first — the ticket's headline framing depends on it.

WITHDRAWN: "the refusal is correct, load_all has the bug". I asserted that from a control that was a BAD QUERY. I asked

    anthill query -p f.anthill -i t7z.collide.NonEq 'SortProvidesInfo(sort_ref: NonEq, spec: ?s)'

and got "no solutions", and concluded NonEq provides nothing. Scanning the relation by FUNCTOR instead shows the opposite:

    SortProvidesInfo(sort_ref: NonEq, spec: SortView(PartialEq, T: NonEq))
    SortProvidesInfo(sort_ref: NonEq, spec: SortView(Eq, T: NonEq))

This is the documented `-i` short-name footgun (cf. WI-923/924): the imported name resolved to the PRELUDE's `NonEq` spec, not to the local sort, so the pattern asked about a different symbol and answered "no". A `-i`-scoped pattern query is not a safe control for "does X provide Y"; scan by functor.

SO THE OTHER RESOLUTION IS LIVE, and is now the leading one. `sort NonEq { entity ne(id: Int64) }` is an ordinary struct whose only field is `Int64`, which HAS `Eq` — so `eq_derive` derives `Eq[T = NonEq]` for it, exactly as it does for the same sort under any other name (measured: renaming it `Widget` yields the identical two rows). The WI-274 test's premise, "NonEq provides no Eq", is FALSE of the finished KB. The name is doing no work — I briefly thought it collided with `anthill.prelude.NonEq` and that was the same bad query talking.

WHAT IS SOLID, all measured with a 5-arm fixture (both element types x EqList present/absent, plus a spec-independent field mismatch as a positive control):

  * load_all ACCEPTS `Eq[T = List[T = NonEq]]`; `load` + a hand-driven `type_check_sorts` REFUSES it.
  * CONTROL, EqList absent: BOTH routes refuse, and refuse the Int64 case too — so the provision is what makes it resolve, not some ambient Eq.
  * CONTROL, `n: Int64` given a String: BOTH routes report. The fact IS checked under load_all; only the spec-field resolution differs.
  * At typer time in load_all the goal resolves as
        Conditional(impl = EqList)
          sub: Cond[PartialEq via EqList @ T = List[T = NonEq]]
          sub: Cond[Eq       via NonEq  @ T = NonEq]
    so the condition IS descended, with `A` correctly bound, and the sub-goal SUCCEEDS.
  * `eq_derive::run` is at load.rs:12617, AFTER `type_check_sorts` at :12563. So the derived `Eq[T = NonEq]` does NOT exist yet when the typer asks. The CLI query above sees the FINISHED KB, which is a later state.

THE OPEN CONTRADICTION, stated rather than resolved. A separate arm — `H2(item: Eq[T = NonEq])` with no EqList anywhere — is refused by BOTH routes, and the instrumented resolver reports `Eq[T = t7z.direct.NonEq] -> not-resolved` at typer time. So at typer time nothing provides `Eq[T = NonEq]`, yet inside EqList's descent that same goal resolves `via NonEq`. The difference between the two asks is the PRESENCE OF EqList, which points at the descent's own scope — the WI-857 `local_provider` locality rule, or `requires_entry_covers_goal` letting `EqList requires Eq[T = A]` discharge the very sub-goal it generates (a condition proving itself). NOT CONFIRMED; it is the next thing to test, and the test is to ask the same sub-goal with that scope leg disabled.

RULED OUT INDIVIDUALLY, so the next reader does not repeat it — none of these moves the verdict: `build_provides_index` (BOTH call sites), `build_requires_index`, `build_sort_ops_table` (both), `derive_forwarded_provisions`, `seed_default_provider_index`, `build_eq_dispatch_index`, the `provides_index`/`sort_alias_index`/`sort_info_index`/`requires_index` resets, `invalidate_resolve_cache` before the typer, `invalidate_requires_chain_cache` before the typer. The passes were never the variable — which is why a pass-bisect was the wrong instrument, and the resolution-tree print found it in one step. Disabling all of them AT ONCE is not a valid experiment either: it breaks the stdlib load, so it measures loadability, not this.

THE INSTRUMENT, kept because it is what worked: wrap `spec_resolves_at_bindings`'s `resolve(...)` call and render the returned `ResolvedRequiresNode` recursively (Leaf/Cond + impl_sort + spec_sort + bindings), behind an env var.

WHICH WAY THE TICKET NOW POINTS. If the derived `Eq` is the correct reading, the defect is the ORDERING — the typer asks a question `eq_derive` has not yet answered, so field validation sees a half-built equality relation and the WI-274 pair only discriminates by accident of what has run. That is a bigger and better-founded ticket than "load_all misses a check", and it also explains why the shipped test only ever passed through the partial loader. Settle the ordering question before changing either side.

### 2026-09-01T10:00:14Z — feedback — user

RESOLVED, AND THE ANSWER IS THE ONE THIS TICKET SAID TO RULE OUT FIRST: `load_all` is RIGHT and the TEST was wrong. Both of my earlier readings — "load_all misses the check" and then "the typer runs before equality is derived" — are withdrawn; each rested on a fixture artifact, recorded below so it is not rebuilt.

THE DEFECT WAS IN THE FIXTURE. `typing_test::conditional_spec_field_rejects_eq_list_of_non_eq_elements` used

    sort NonEq
      entity ne(id: Int64)
    end

as its "non-equatable" element. That sort IS totally equatable: its only field is `Int64`, which has `Eq`, so `eq_derive::classify` puts it in `total_composites` and `derive_total_eq` asserts `provides Eq[T = NonEq]` for it — MEASURED by printing `total_composites` at the derivation site, which lists the fixture's sort beside every stdlib composite. So `Eq[T = List[T = NonEq]]` genuinely holds and refusing it was WRONG. The name asserted a property the sort did not have.

WHY IT PASSED ANYWAY. The test loaded through `load::load` and then drove `type_check_sorts` by hand. That entry point runs none of `load_phase_inner`'s passes, `derive_total_eq` among them, so on that route NOTHING is equatable by derivation: the pair could not discriminate at all, it refused both halves, and only the refusing half was asserted.

THE FOUR CELLS, which is what settles it. Vary the element's equatability AND the route:

    element `id: Int64` (Eq, derived)      load(): refuse   load_all: ACCEPT
    element `id: Float` (genuinely NonEq)  load(): refuse   load_all: REFUSE

`load_all` discriminates on the element; `load` refuses both. `derive_total_eq` runs at load.rs:12465, BEFORE `type_check_sorts` at :12563 — exactly as its own doc requires ("must run BEFORE the typer") — so there was never an ordering defect either.

THE ARTIFACT THAT SENT ME WRONG TWICE, recorded because it is subtle and cheap to rebuild. My "control" for "does NonEq provide Eq" was a fixture with NO `fact Eq[T = Int64]` in it. Without that line `Int64` is not equatable in the TEST HARNESS's KB (`common::load_stdlib_kb`, which is not the CLI's KB — cf. the known "stdlib-only KB lacks the primitive spec facts" footgun), so the element was not Total, nothing was derived, and the control answered "not-resolved" for a reason unrelated to the question. Adding that one line flips `load_all` from refuse to accept. A `-i`-scoped pattern query was the other bad control (previous feedback entry).

THE REPAIR. Both halves of the WI-274 pair now load through `load_all` — the route callers take — and the element is made non-equatable the way the kernel actually decides it: a `Float` field (eq_derive's module header, "is `NonEq` (partial) if any field is `NonEq` (reaches an IEEE `Float`)"), not by naming. They share one source builder differing in a single token, so the axis is visible. CONTROLS MEASURED, one per half: flipping the rejecting half's element to `Int64` turns it RED; flipping the accepting half's to `Float` turns THAT one red. Workspace suite 6251 passed / 0 failed, count unchanged.

WHAT THIS UNBLOCKS. WI-20260901-Q68AK was blocked on this ticket because removing `load::load` would have deleted "the sole detector of a live bug". There is no live bug — the detector was detecting its own fixture. That block is lifted, and the finding also REMOVES one of the 51 failures that ticket's migration must account for (the single "reverse direction" case), leaving 48 mechanical migrations plus two tests whose subject is `load` itself.

