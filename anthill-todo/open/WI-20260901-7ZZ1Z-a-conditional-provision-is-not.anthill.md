## Attributes

- id: WI-20260901-7ZZ1Z-a-conditional-provision-is-not
- created: 2026-09-01T08:55:17Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T08:55:17Z

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

