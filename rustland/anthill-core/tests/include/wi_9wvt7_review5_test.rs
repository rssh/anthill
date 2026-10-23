//! WI-20260908-9WVT7's fifth review — the rows of its fixes, by what each one decides.
//!
//! A. A provision matched only through the subtype relation is ranked with the rest, and a
//!    provider's own row is local to its dictionary only where it meets the sub-goal as
//!    itself (user, 2026-10-17); the bottom type's arm in the candidate matcher is gone. Since
//!    the sixth review the rank is one order on the heads (`wi_9wvt7_review6_test`), and since
//!    the seventh a provider's own row is local where no candidate is more specific, in both
//!    halves of its dictionary (user, 2026-10-17; `wi_9wvt7_review7_test`).
//! B. A payload the runtime raised keeps its cause across a catch and a raise again (user,
//!    2026-10-17); since the sixth review the cause is the payload's constructor, which no
//!    program constructs (`wi_9wvt7_review6_test`).
//! C. (Retired with `ModifyRuntime`, WI-200: `ModifyRuntime.get`/`set` at a place of a type no
//!    `Modify` fires on was refused at load, user 2026-10-17.)
//! D. The refusals' accounts: a library spec failing at another spec's goal, a former at a
//!    construction, a cycle at a call, a contract read through the program's specs.
//! E. The forward of a caller's parameter held inside a type it builds.
//! F. The one-definition check reads the clauses the source wrote; the induction axiom's name.
//!
//! G. Found while fixing: an effect of the program's own named like a row atom.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED on the fifth review's commit (b437fdbb; the subtype
//! tie-break and the raise's mark are gone since), each switched off alone in one build, over this
//! file and the files the fixes touched (`wi_n31xx_*`, `wi_xsvcs_*`, `wi939_*`, `wi_0v0f7_*`,
//! `wi4gbqv_*`, `wi_9wvt7_clock_handler_test`, `wi_hxgxf_*`, `wi_0gyw1_*`, `eval_test`,
//! `wi205_cell_test`); the typer-wide ones over the whole `wi_tests` binary too, where each
//! moves only the rows named here:
//!
//!   * locality keeping a provider's own row that a sub-goal reaches only through the subtype
//!     relation → [`a_refinements_condition_takes_the_refinements_provision`] and
//!     `wi_hxgxf_type_value_derivation_test::a_type_argument_that_is_nothing_answers_itself`;
//!   * the ranking without its subtype tie-break → that `wi_hxgxf` row, at the `[]` it infers;
//!   * the bottom type's arm put back → [`an_empty_list_takes_its_elements_provider`],
//!     [`two_providers_at_the_bottom_type_are_refused_at_load`] and
//!     [`a_raising_callback_meets_its_arrow_provision`];
//!   * the bridge's partition read off the channel →
//!     `wi_0v0f7_bridged_raise_test::the_raise_partition_is_by_cause_not_by_channel`;
//!   * the advice read off anything but the payload's constructor →
//!     [`a_drain_failure_raised_again_gets_no_boundary_advice`];
//!   * the library spec's repair chosen by the requirement's spec alone →
//!     [`a_library_requirement_failing_at_another_spec_is_told_that_spec`];
//!   * a construction's former refusal taken whatever the cause →
//!     [`a_constructions_conditional_provider_is_told_its_condition`] and
//!     [`a_former_holding_the_scopes_parameter_is_told_the_slot`];
//!   * a cycle at a call left silent → [`a_cyclic_requirement_at_a_call_is_refused_at_load`];
//!   * the contract read one hop deep, or not on a spec operation's call →
//!     [`a_programs_spec_with_a_contract_that_holds_nowhere_is_told_so`];
//!   * the hint's `requires` advice given at a ground goal →
//!     `wi_n31xx_type_value_read_rule_test::a_provision_contract_at_no_type_value_names_no_row`;
//!   * the forward read only through a base that has a row of the requirement's own spec →
//!     [`a_parameter_inside_an_application_is_forwarded_for_every_spec`] and
//!     [`a_part_with_no_instance_is_said_and_a_variant_is_its_sort`];
//!   * the former not asked before the forward → [`a_former_beside_the_callers_parameter_is_the_formers_refusal`];
//!   * the caller's own `TypeValue` not read, the application taken from the first one met, or
//!     the clauses for a sort joined as a list →
//!     [`the_refusal_names_the_parameter_the_caller_lacks_and_its_clauses_paste`];
//!   * a parametric variant not read at its sort → [`a_part_with_no_instance_is_said_and_a_variant_is_its_sort`];
//!   * the generic "pin the element" tail on the forward →
//!     [`a_parameter_inside_an_application_is_forwarded_for_every_spec`];
//!   * the one-definition check counting derived clauses → [`a_derived_clause_is_not_counted_as_hand_written`];
//!   * the induction axiom's name left to an operation → [`an_operation_named_like_the_induction_axiom_is_refused`];
//!   * the bodied branch naming arity + 1 for every clause →
//!     [`a_bodied_bool_refusal_names_the_slot_its_clause_sits_at`];
//!   * the row atoms recognised by a name's last segment →
//!     [`an_effect_named_like_a_row_atom_is_its_own_effect`].
//!
//! PASSES EITHER WAY, BY DESIGN: the controls inside the rows — the direct drain beside the one raised again, the operation named otherwise, the sort
//! named `absent` that provides `Effect` (the twin that does not is what the reading moves) —
//! and every repair a refusal advises, run: `Desc[T = Float]` provided for `Keyed`, `StrApply`
//! for the conditional former, the slot declared for the held one, the boundary's `requires`,
//! and the pasted clauses with their unequal control. A fix to an account changes what the
//! refusal says, not whether the repaired program runs.

use crate::common::{assert_refused_naming, fault_messages, load_errors_of, run_int64};

// ── A. the subtype relation and a provider's own row ─────────────────────────────────────

/// A REFINEMENT'S CONDITION TAKES THE REFINEMENT'S PROVISION. `Animal provides Desc[T = Animal]
/// :- Desc[T = Dog]`, with `Dog` a subtype of `Animal` that provides `Desc[T = Dog]` itself:
/// inside `Animal`'s dictionary the condition reached `Animal`'s own row through the subtype
/// relation, and locality kept it — a cycle the call left silent, so the program loaded and
/// died "requirement param `__req_desc` not bound in caller frame".
#[test]
fn a_refinements_condition_takes_the_refinements_provision() {
    let src = r#"
namespace test.r5.refine
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Animal
    entity animal
    provides Desc[T = Animal] :- Desc[T = Dog]
    operation describe(x: Animal) -> Int64 = 1
  end
  sort Dog
    requires Animal
    entity dog
    provides Desc[T = Dog]
    operation describe(x: Dog) -> Int64 = 2
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  operation viaAnimal() -> Int64 = Reader.probe(animal)
  operation viaDog() -> Int64 = Reader.probe(dog)
end
"#;
    assert_eq!(run_int64(src, "test.r5.refine.viaAnimal"), Ok(1));
    assert_eq!(run_int64(src, "test.r5.refine.viaDog"), Ok(2));
}

/// AN EMPTY LIST TAKES ITS ELEMENTS' PROVIDER. `useD([])` over `ListDesc provides Desc[T =
/// List[T = E]] requires Desc[T = E]` beside `IntDesc`: the element goal `Desc[T = Nothing]`
/// is answered by the one provision the bottom type reaches, and `ListDesc`'s operation runs.
/// Under the bottom type's arm it was refused at load.
#[test]
fn an_empty_list_takes_its_elements_provider() {
    let src = r#"
namespace test.r5.empty
  import anthill.prelude.{Int64, List}
  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort IntDesc
    import anthill.prelude.{Int64}
    provides Desc[T = Int64]
    operation d(x: Int64) -> Int64 = 1
  end
  sort ListDesc
    import anthill.prelude.{Int64, List}
    sort E = ?
    requires Desc[T = E]
    provides Desc[T = List[T = E]]
    operation d(x: List[T = E]) -> Int64 = 7
  end
  operation useD[B](x: B) -> Int64 requires Desc[T = B] = Desc.d(x)
  operation go() -> Int64 =
    let xs = []
    useD(xs)
end
"#;
    assert_eq!(run_int64(src, "test.r5.empty.go"), Ok(7));
}

/// TWO PROVIDERS AT THE BOTTOM TYPE ARE A TIE, REFUSED AT LOAD. `Counter.count([])` over
/// `count[A](xs: List[T = A]) requires Stamp[T = A] = Stamp.stamp[T = A]()`, `Stamp` provided at `Leaf`
/// and at `Bang`: the nullary member runs, so the dictionary matters, and the bottom type
/// reaches both. Under the bottom type's arm no provision matched, nothing reported the
/// requirement, and the program loaded and died "`__req_stamp` not bound in caller frame".
#[test]
fn two_providers_at_the_bottom_type_are_refused_at_load() {
    let errs = load_errors_of(
        r#"
namespace test.r5.tie
  import anthill.prelude.{Int64, List}
  sort Stamp
    sort T = ?
    operation stamp() -> Int64
  end
  sort Leaf
    entity leaf
    provides Stamp[T = Leaf]
    operation stamp() -> Int64 = 42
  end
  sort Bang
    entity bang
    provides Stamp[T = Bang]
    operation stamp() -> Int64 = 7
  end
  sort Counter
    operation count[A](xs: List[T = A]) -> Int64 requires Stamp[T = A] = Stamp.stamp[T = A]()
  end
  operation go() -> Int64 =
    let xs = []
    Counter.count(xs)
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["is ambiguous among providers", "test.r5.tie.Leaf", "test.r5.tie.Bang"],
        "two providers at Nothing",
    );
}

/// A CALLBACK THAT ALWAYS RAISES MEETS AN ARROW PROVISION BY ITS RESULT. `lambda (x: Int64) ->
/// Error.raise("no")` is an `(Int64) -> Nothing`, a subtype of the `(Int64) -> Int64` a
/// provision is written at. Under the bottom type's arm, which read the arrow's result too, it
/// was refused, told to give some sort a row at `Int64 -> nothing`.
#[test]
fn a_raising_callback_meets_its_arrow_provision() {
    let src = r#"
namespace test.r5.arrow
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Runner
    sort F = ?
    operation run(f: F) -> Int64 effects {Error[String]}
  end
  sort IntRunner
    import anthill.prelude.{Int64, String, Error}
    provides Runner[F = (Int64) -> Int64 @ {Error[String]}]
    operation run(f: (Int64) -> Int64 @ {Error[String]}) -> Int64 effects {Error[String]} = f(41)
  end
  operation viaRun() -> Int64 effects {Error[String]} =
    Runner.run(lambda (x: Int64) -> Error.raise("no"))
  operation go() -> Int64 =
    match Error.reify(lambda () -> viaRun())
      case ok(n) -> n
      case err(_) -> 7
end
"#;
    assert_eq!(run_int64(src, "test.r5.arrow.go"), Ok(7));
}

// ── B. who raised it ─────────────────────────────────────────────────────────────────────

/// A DRAIN'S FAILURE CAUGHT AND RAISED AGAIN IS STILL THE RUNTIME'S. `Result.reflect(Error.reify(
/// …))` catches the `evaluation_failure` of a drain whose search declined a `Clock` read — a
/// goal on `stampAt` built at run time — and raises the same value again; the rule reading it is told the effect, and no boundary. The
/// payload's constructor says whose it is, since no program constructs one (the sixth review,
/// `wi_9wvt7_review6_test`); before, a mark on the error alone made the raise again the
/// program's, and the rule was told to reach for `Error.reify`, which only hides the declined
/// read. The direct twin is the control and passes either way.
#[test]
fn a_drain_failure_raised_again_gets_no_boundary_advice() {
    let src = r#"
namespace test.r5.rethrow
  import anthill.prelude.{Int64, String, Error, Result, List, Stream, Option}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Time.{now, Clock}
  import anthill.reflect.{Term, Solution, fresh_var, as_term, ResolveStreamFailure}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query}
  operation stampAt(n: Int64) -> String effects {Clock} = now()
  rule apply2(?p, ?x, ?r) :- ?p(?x, ?r)
  sort Probes
    entity Stamp(s: String)
  end
  rule Stamp(s: ?r) :- apply2(stampAt, 1, ?r)
  operation probe() -> Int64 effects Error[ResolveStreamFailure] =
    match splitFirst(execute(kb(), pattern_query(term: as_term(Stamp(s: fresh_var[String]("x"))))))
      case none()  -> 0
      case some(_) -> 1
  operation probeAgain() -> Int64 effects Error[ResolveStreamFailure] =
    Result.reflect(Error.reify(lambda () -> probe()))
  rule direct(?n) :- ?n <=> probe()
  rule again(?n) :- ?n <=> probeAgain()
end
"#;
    for goal in ["test.r5.rethrow.direct(?n)", "test.r5.rethrow.again(?n)"] {
        let messages = fault_messages(src, goal);
        assert!(
            messages.iter().any(|m| m.contains("raised evaluation_failure")
                && m.contains("it performs `anthill.prelude.Time.Clock`")),
            "{goal}: the declined effect is reported: {messages:?}"
        );
        assert!(
            messages.iter().all(|m| !m.contains("Handle it inside the operation")),
            "{goal}: no boundary is advised: {messages:?}"
        );
    }
}

// ── D. what a refusal says ────────────────────────────────────────────────────────────────

const KEYED: &str = r#"
namespace test.r5.keyedreq
  import anthill.prelude.{Int64, Float, Type, Error, Result, ErrorTag}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{TypeValue}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation describe(x: Int64) -> Int64 = 1
  end
  sort Keyed
    sort K = ?
    requires Desc[T = K]
    entity keyed(k: K)
  end
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value[T = B]()
  operation catchIt[P](x: P) -> Int64 requires ErrorTag[T = P] =
    match Error.reify(lambda () -> Error.raise(x))
      case ok(v) -> 1
      case err(e) -> 2
"#;

/// A LIBRARY SPEC'S REQUIREMENT THAT FAILS AT ANOTHER SPEC'S GOAL IS REPAIRED AS THAT GOAL IS.
/// `TypeValue[T = Keyed[K = Float]]` and `ErrorTag[T = Keyed[K = Float]]` fail because
/// `Keyed`'s own `requires Desc[T = K]` holds nowhere at `Float`; the refusal names `Desc`, and a
/// `Desc` row at `Float` makes both answer. They were told no row of the library's spec answers
/// and to pass a value of a sort that is no spec, which `Keyed[K = Float]` is; the `ErrorTag` one
/// also to write a row of `ErrorTag`, which breaks the boundary.
#[test]
fn a_library_requirement_failing_at_another_spec_is_told_that_spec() {
    for (shape, call) in [
        ("TypeValue", "  operation ask(x: Keyed[K = Float]) -> Type = tyOf(x)\nend\n"),
        ("ErrorTag", "  operation ask(x: Keyed[K = Float]) -> Int64 = catchIt(x)\nend\n"),
    ] {
        let errs = load_errors_of(&format!("{KEYED}{call}"));
        assert_refused_naming(&errs, &["no impl provides test.r5.keyedreq.Desc"], shape);
        for wrong in [
            "no row of `anthill.reflect.TypeValue` answers here",
            "no row of `anthill.prelude.ErrorTag` answers here",
            "provides anthill.prelude.ErrorTag",
        ] {
            assert!(errs.iter().all(|e| !e.contains(wrong)), "{shape}: {errs:#?}");
        }
    }
    let repaired = format!(
        "{KEYED}  sort FloatDesc\n    provides Desc[T = Float]\n    operation describe(x: Float) -> \
         Int64 = 2\n  end\n  operation ask() -> Int64 = catchIt(keyed(1.5))\nend\n"
    );
    assert_eq!(run_int64(&repaired, "test.r5.keyedreq.ask"), Ok(2));
}

const CONDITIONAL_FORMER: &str = r#"
namespace test.r5.condformer
  import anthill.prelude.{Int64, String}
  sort Apply
    sort F = ?
    operation run(f: F) -> Int64
  end
  sort Lbl
    sort T = ?
    operation lbl(x: T) -> Int64
  end
  sort P
    sort A = ?
    requires Lbl[T = A]
    provides Apply[F = (A) -> Int64]
    operation run(f: (A) -> Int64) -> Int64 = 3
  end
  sort Holder
    import anthill.prelude.{Int64, String}
    sort F = ?
    requires Apply[F = F]
    entity holder(f: F)
    operation go(h: Self) -> Int64 = Apply.run(h.f)
  end
  operation mk() -> Int64 = Holder.go(holder(lambda (s: String) -> 1))
end
"#;

/// A CONSTRUCTION AT A FORMER A CONDITIONAL PROVISION ANSWERS IS TOLD THE CONDITION. `P provides
/// Apply[F = (A) -> Int64] :- Lbl[T = A]` answers `holder(lambda (s: String) -> 1)` but for its
/// condition `Lbl[T = String]`; the refusal names `Lbl`, and a `Lbl` row at `String` makes it run.
/// It was told nothing provides `Apply` at the arrow.
#[test]
fn a_constructions_conditional_provider_is_told_its_condition() {
    let errs = load_errors_of(CONDITIONAL_FORMER);
    assert_refused_naming(&errs, &["no impl provides test.r5.condformer.Lbl"], "conditional former");
    assert!(errs.iter().all(|e| !e.contains("STRUCTURAL FORMER")), "{errs:#?}");
    let repaired = crate::common::replace_in_fixture(
        CONDITIONAL_FORMER,
        "  operation mk()",
        "  sort StrLbl\n    import anthill.prelude.{Int64, String}\n    provides Lbl[T = String]\n    \
         operation lbl(x: String) -> Int64 = 2\n  end\n  operation mk()",
    );
    assert_eq!(run_int64(&repaired, "test.r5.condformer.mk"), Ok(3));
}

const FORMER_HOLDING_A_PARAMETER: &str = r#"
namespace test.r5.heldformer
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort Wrapper
    import anthill.prelude.{Int64}
    entity wrap(n: Int64)
    provides Desc[T = (Int64, Int64)]
    operation d(x: (Int64, Int64)) -> Int64 = 9
  end
  sort Holder
    import anthill.prelude.{Int64}
    sort T = ?
    requires Desc[T = T]
    entity holder(v: T)
    operation get(h: Self) -> Int64 = match h case holder(v) -> Desc.d(v)
  end
  operation mk[C](x: C) -> Int64 = Holder.get(holder((x, 1)))
  operation go() -> Int64 = mk(5)
end
"#;

/// A CONSTRUCTION AT A FORMER HOLDING THE CONSTRUCTING SCOPE'S PARAMETER IS TOLD TO DECLARE THE
/// SLOT, which repairs it: `holder((x, 1))` over `x: C`, and `requires Desc[T = (C, Int64)]` on
/// `mk` runs. It was told to give some sort a row at `(_1: ?C, _2: Int64)`.
#[test]
fn a_former_holding_the_scopes_parameter_is_told_the_slot() {
    let errs = load_errors_of(FORMER_HOLDING_A_PARAMETER);
    assert_refused_naming(&errs, &["declare a requirement slot for it"], "former holding C");
    assert!(errs.iter().all(|e| !e.contains("STRUCTURAL FORMER")), "{errs:#?}");
    let repaired = crate::common::replace_in_fixture(
        FORMER_HOLDING_A_PARAMETER,
        "operation mk[C](x: C) -> Int64 =",
        "operation mk[C](x: C) -> Int64 requires Desc[T = (C, Int64)] =",
    );
    assert_eq!(run_int64(&repaired, "test.r5.heldformer.go"), Ok(9));
}

/// A CYCLE AT A CALL IS REFUSED AT LOAD, as at a construction: `A provides Desc[T = A] :- Desc[T
/// = B]` and its mirror, `Reader.probe(a)`. It loaded clean and died "`__req_desc` not bound in
/// caller frame".
#[test]
fn a_cyclic_requirement_at_a_call_is_refused_at_load() {
    let errs = load_errors_of(
        r#"
namespace test.r5.cycle
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort A
    entity a
    provides Desc[T = A] :- Desc[T = B]
    operation describe(x: A) -> Int64 = 1
  end
  sort B
    entity b
    provides Desc[T = B] :- Desc[T = A]
    operation describe(x: B) -> Int64 = 2
  end
  sort Reader
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[T = HT] = Desc.describe(x)
  end
  operation viaA() -> Int64 = Reader.probe(a)
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["cannot be supplied for call to `test.r5.cycle.Reader.probe`", "construction is cyclic"],
        "a cycle at a call",
    );
}

/// A PROGRAM SPEC'S CONTRACT IS READ THROUGH THE PROGRAM'S SPECS IT NAMES, and on a spec
/// operation's call as on a generic one's: `Desc requires Mid[T = T]`, `Mid requires TypeValue[T =
/// T]`, at `Option[T = (Int64, Int64)]`. Each was advised a row of `Desc` there, refused for its
/// contract in turn.
#[test]
fn a_programs_spec_with_a_contract_that_holds_nowhere_is_told_so() {
    let two_hops = r#"
namespace test.r5.contract
  import anthill.prelude.{Int64, Option, Type}
  import anthill.prelude.Option.{some}
  import anthill.reflect.{TypeValue}
  sort Mid
    import anthill.prelude.Type
    import anthill.reflect.{TypeValue}
    sort T = ?
    requires TypeValue[T = T]
    operation m() -> Type
  end
  sort Desc
    import anthill.prelude.{Int64, Type}
    sort T = ?
    requires Mid[T = T]
    operation d() -> Type
    operation e(x: T) -> Int64
  end
  operation dOf[B](x: B) -> Type requires Desc[T = B] = Desc.d()
"#;
    for (shape, call) in [
        ("through a program spec", "  operation ask() -> Type = dOf(some((1, 2)))\nend\n"),
        ("a spec operation's call", "  operation ask() -> Int64 = Desc.e(some((1, 2)))\nend\n"),
    ] {
        let errs = load_errors_of(&format!("{two_hops}{call}"));
        assert_refused_naming(
            &errs,
            &[
                "no row of `test.r5.contract.Desc` at these bindings can answer, its own contract \
                 asking `anthill.reflect.TypeValue[",
                "no row of `anthill.reflect.TypeValue` answers here, and none may be written",
            ],
            shape,
        );
        assert!(errs.iter().all(|e| !e.contains("declare `provides")), "{shape}: {errs:#?}");
    }
}

// ── E. the forward of a parameter held inside a type ─────────────────────────────────────

/// AN `Error.reify` OF A RAISE AT AN APPLICATION HOLDING THE CALLER'S PARAMETER IS REFUSED AT
/// LOAD, and the clause it names answers: `Error.raise(some(x))` over `x: C`. `ErrorTag`'s one
/// row is at a parameter, so the reading asked for a row of `ErrorTag` at the application's sort
/// and found none: the program loaded and died "entered with no `ErrorTag` evidence". The
/// parameter's order in the spec does not decide it either: `Spec2` with `T` before `A` and after.
#[test]
fn a_parameter_inside_an_application_is_forwarded_for_every_spec() {
    let boundary = r#"
namespace test.r5.boundary
  import anthill.prelude.{Int64, Option, Error}
  import anthill.prelude.Option.{some}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{TypeValue}
  operation g[C](x: C) -> Int64 =
    match Error.reify(lambda () -> Error.raise(some(x)))
      case ok(n) -> 1
      case err(_) -> 7
  operation go() -> Int64 = g(1)
end
"#;
    let errs = load_errors_of(boundary);
    assert_refused_naming(
        &errs,
        &[
            "its carrier `anthill.prelude.Option[T = C]` holds `C`",
            "Declare `requires anthill.reflect.TypeValue[T = C]` on `test.r5.boundary.g`",
        ],
        "an ErrorTag boundary",
    );
    // The account names its repair; "pin the element at the call site" is advice for an
    // element left open, and this one the caller pinned to its own parameter.
    assert!(
        errs.iter().all(|e| !e.contains("pin the element at the call site")),
        "{errs:#?}"
    );
    let repaired = crate::common::replace_in_fixture(
        boundary,
        "operation g[C](x: C) -> Int64 =",
        "operation g[C](x: C) -> Int64 requires TypeValue[T = C] =",
    );
    assert_eq!(run_int64(&repaired, "test.r5.boundary.go"), Ok(7));
    let order = |first: &str, second: &str| {
        format!(
            r#"
namespace test.r5.order
  import anthill.prelude.{{Int64}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation describe(x: Int64) -> Int64 = 1
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort Spec2
    sort {first} = ?
    sort {second} = ?
    operation go(t: T, a: A) -> Int64
  end
  sort Quiet
    sort E = ?
    requires Desc[T = E]
    provides Spec2[T = Box[B = E], A = Int64]
    operation go(t: Box[B = E], a: Int64) -> Int64 =
      match t
        case box(inner: i) -> Desc.describe(i)
  end
  sort Reader
    sort HT = ?
    sort HA = ?
    operation probe(t: HT, a: HA) -> Int64 requires Spec2[T = HT, A = HA] = Spec2.go(t, a)
  end
  operation fwd[C](c: C) -> Int64 = Reader.probe(box(inner: c), 1)
end
"#
        )
    };
    for (first, second) in [("T", "A"), ("A", "T")] {
        assert_refused_naming(
            &load_errors_of(&order(first, second)),
            &["its carrier `test.r5.order.Box[B = C]` holds `C`"],
            &format!("`Spec2[{first}, {second}]`"),
        );
    }
}

/// A SPEC, AND A SORT APPLIED TO NOTHING, HAVE NO `TypeValue` WHATEVER THE CALLER SUPPLIES, and
/// the refusal says that and not a clause; a parametric variant is its sort. `tyOf(s)` over `s:
/// Coll[T = C]`, `Coll` a spec, and `tyOf(pair(x, s))` with `s: Shape`, a spec, beside a `C` the
/// caller covers; `tyOf(w)` over `w: Wrap.wrap[V = C]` is forwarded as `Wrap[V = C]`. The first
/// and the variant loaded clean and a query panicked; the second was told to declare the clause
/// it had.
#[test]
fn a_part_with_no_instance_is_said_and_a_variant_is_its_sort() {
    let errs = load_errors_of(
        r#"
namespace test.r5.noinst
  import anthill.prelude.{Int64, Type, Pair}
  import anthill.prelude.Pair.{pair}
  import anthill.reflect.{TypeValue}
  sort Coll
    sort T = ?
    operation size(s: Self) -> Int64
  end
  sort Bag
    sort T = ?
    provides Coll[T = T]
    entity bag(x: T)
    operation size(s: Bag[T = T]) -> Int64 = 3
  end
  sort Shape
    sort T = ?
    operation area(s: T) -> Int64
  end
  sort Wrap
    sort V = ?
    entity wrap(v: V)
    entity other(n: Int64)
  end
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value[T = B]()
  operation spec[C](s: Coll[T = C]) -> Type = tyOf(s)
  operation part[C](x: C, s: Shape) -> Type requires TypeValue[T = C] = tyOf(pair(x, s))
  operation variant[C](w: Wrap.wrap[V = C]) -> Type = tyOf(w)
end
"#,
    );
    let no_instance = "no row of `anthill.reflect.TypeValue` answers here, and none may be written";
    for (shape, want) in [
        ("a spec base", "its carrier is `test.r5.noinst.Coll[T = C]`, and "),
        ("a spec part", "holds `test.r5.noinst.Shape[T = s.T]`, and "),
    ] {
        let err = errs
            .iter()
            .find(|e| e.contains(want))
            .unwrap_or_else(|| panic!("{shape}: expected {want:?}; got {errs:#?}"));
        assert!(err.contains(no_instance), "{shape}: {err}");
        assert!(!err.contains("Declare `requires"), "{shape}: {err}");
    }
    assert_refused_naming(
        &errs,
        &[
            "its carrier `test.r5.noinst.Wrap[V = C]` holds `C`",
            "Declare `requires anthill.reflect.TypeValue[T = C]` on `test.r5.noinst.variant`",
        ],
        "a parametric variant",
    );
}

/// A TUPLE BESIDE THE CALLER'S PARAMETER IS THE FORMER'S REFUSAL, with the clause declared or
/// not: `tyOf(pair(x, (1, 2)))`. It was told to declare `requires TypeValue[T = C]`, and with it
/// declared got the same refusal.
#[test]
fn a_former_beside_the_callers_parameter_is_the_formers_refusal() {
    for clause in ["", " requires TypeValue[T = C]"] {
        let errs = load_errors_of(&format!(
            r#"
namespace test.r5.former
  import anthill.prelude.{{Int64, Pair, Type}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.reflect.{{TypeValue}}
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value[T = B]()
  operation f[C](x: C) -> Type{clause} = tyOf(pair(x, (1, 2)))
end
"#
        ));
        assert_refused_naming(
            &errs,
            &["has a STRUCTURAL FORMER", "Pass a value whose type is a sort with no tuple or arrow"],
            &format!("`{clause}`"),
        );
        assert!(errs.iter().all(|e| !e.contains("Declare `requires")), "{errs:#?}");
    }
}

/// THE REFUSAL NAMES THE PARAMETER THE CALLER LACKS EVIDENCE FOR, where it stands, and the
/// clauses it prints paste: `Holder`'s `A` is covered by its own `requires` and `probe`'s `B` is
/// not; a direct binding is no application's; two parameters of the sort take a `requires` each,
/// and a parameter of the sort beside one of the operation's go on the operation. It named `A`,
/// said `Box[B = D]` held `C`, printed `requires TypeValue[T = A], TypeValue[T = B]` for a sort,
/// and sent a clause naming the operation's `B` to the sort. A program with the clauses pasted
/// runs: the type `probe` reads is the pair's.
#[test]
fn the_refusal_names_the_parameter_the_caller_lacks_and_its_clauses_paste() {
    let holder = |decls: &str, op: &str, clause: &str| {
        format!(
            r#"
namespace test.r5.names
  import anthill.prelude.{{Int64, Type, Pair, PartialEq}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.reflect.{{TypeValue}}
  sort Ty
    operation tyOf[X](x: X) -> Type requires TypeValue[T = X] = TypeValue.type_value[T = X]()
  end
  sort Holder
{decls}
    operation {op} -> Type{clause} = Ty.tyOf(pair(fst: a, snd: b))
  end
  operation go() -> Int64 =
    if PartialEq.eq(Holder.probe(1, "s"), Ty.tyOf(pair(fst: 2, snd: "t"))) then 5 else 0
  operation swapped() -> Int64 =
    if PartialEq.eq(Holder.probe(1, "s"), Ty.tyOf(pair(fst: "t", snd: 2))) then 5 else 0
end
"#
        )
    };
    let covered = holder(
        "    sort A = ?\n    requires anthill.reflect.TypeValue[T = A]\n",
        "probe[B](a: A, b: B)",
        "",
    );
    assert_refused_naming(
        &load_errors_of(&covered),
        &[
            "holds `B`",
            "Declare `requires anthill.reflect.TypeValue[T = B]` on `test.r5.names.Holder.probe`",
        ],
        "A covered, B lacking",
    );
    let two_sort_params = holder("    sort A = ?\n    sort B = ?\n", "probe(a: A, b: B)", "");
    assert_refused_naming(
        &load_errors_of(&two_sort_params),
        &["Declare `requires anthill.reflect.TypeValue[T = A]` and `requires \
           anthill.reflect.TypeValue[T = B]` on `test.r5.names.Holder`"],
        "two sort parameters",
    );
    let pasted = holder(
        "    sort A = ?\n    sort B = ?\n    requires anthill.reflect.TypeValue[T = A]\n    \
         requires anthill.reflect.TypeValue[T = B]\n",
        "probe(a: A, b: B)",
        "",
    );
    assert_eq!(run_int64(&pasted, "test.r5.names.go"), Ok(5));
    assert_eq!(run_int64(&pasted, "test.r5.names.swapped"), Ok(0), "the pair's own type, no other");
    let mixed = holder("    sort A = ?\n", "probe[B](a: A, b: B)", "");
    assert_refused_naming(
        &load_errors_of(&mixed),
        &["Declare `requires anthill.reflect.TypeValue[T = A], anthill.reflect.TypeValue[T = B]` \
           on `test.r5.names.Holder.probe`"],
        "a sort parameter and an operation's",
    );
    let pasted = holder(
        "    sort A = ?\n",
        "probe[B](a: A, b: B)",
        " requires anthill.reflect.TypeValue[T = A], anthill.reflect.TypeValue[T = B]",
    );
    assert_eq!(run_int64(&pasted, "test.r5.names.go"), Ok(5));
    assert_refused_naming(
        &load_errors_of(
            r#"
namespace test.r5.direct
  import anthill.prelude.{Int64}
  sort Desc2
    sort T = ?
    sort U = ?
    operation describe(y: U) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
  end
  sort IntDesc
    provides Desc2[T = Int64, U = Box[B = Int64]]
    operation describe(y: Box[B = Int64]) -> Int64 = 1
  end
  sort Reader
    sort HT = ?
    sort HU = ?
    operation probe(x: HT, y: HU) -> Int64 requires Desc2[T = HT, U = HU] = Desc2.describe(y)
  end
  operation fwd[C, D](x: C, y: D) -> Int64 = Reader.probe(x, box(inner: y))
end
"#,
        ),
        &["its carrier is `C`, a type parameter of the CALLING operation `test.r5.direct.fwd`"],
        "a direct binding before an application",
    );
}

// ── F. the clauses the source wrote ──────────────────────────────────────────────────────

/// AN OPERATION UNDER THE NAME OF THE SORT'S DERIVED INDUCTION AXIOM IS REFUSED, naming the axiom:
/// `operation induction(c: Colour) -> Bool = true` beside the axiom `Colour.induction` loaded
/// clean, and `Colour.induction(red)` in a rule body answered nothing where the call answered
/// `true`. The same sort with the operation named otherwise is the control and passes either way.
#[test]
fn an_operation_named_like_the_induction_axiom_is_refused() {
    let colour = |op: &str| {
        format!(
            "namespace test.r5.induction\n  sort Colour\n    entity red\n    entity green\n    \
             operation {op}(c: Colour) -> Bool = true\n  end\nend\n"
        )
    };
    assert_refused_naming(
        &load_errors_of(&colour("induction")),
        &["`test.r5.induction.Colour.induction` names the induction axiom derived for"],
        "an operation named induction",
    );
    assert_eq!(load_errors_of(&colour("isit")), Vec::<String>::new());
}

/// A CLAUSE THE LOADER DERIVES IS NO HAND-WRITTEN CLAUSE OF AN OPERATION: beside `operation
/// domain`, a body-less `rule domain(?x)` is refused for what it is, and the derived `domain`
/// clause of the sort is not reported as a clause written at the sort's own line.
#[test]
fn a_derived_clause_is_not_counted_as_hand_written() {
    let errs = load_errors_of(
        r#"
namespace test.r5.derived
  sort Colour
    entity red
    entity green
    rule domain(?x)
    operation domain(x: Colour) -> Bool = true
  end
end
"#,
    );
    assert_refused_naming(&errs, &["a rule with no body DECLARES a predicate"], "a body-less rule");
    assert!(errs.iter().all(|e| !e.contains("hand-written clause")), "{errs:#?}");
}

/// A BODIED `Bool` OPERATION'S REFUSAL NAMES THE SLOT ITS CLAUSE SITS AT: `rule isbig(red) :- true`
/// beside `operation isbig(c: Colour) -> Bool = true` is at the operation's own arity, where it
/// said the arity + 1 goal stops answering.
#[test]
fn a_bodied_bool_refusal_names_the_slot_its_clause_sits_at() {
    assert_refused_naming(
        &load_errors_of(
            "namespace test.r5.slot\n  sort Colour\n    entity red\n    entity green\n    \
             operation isbig(c: Colour) -> Bool = true\n    rule isbig(red) :- true\n  end\nend\n",
        ),
        &["has BOTH a body and 1 hand-written clause at its own arity, as it returns `Bool`:"],
        "an own-arity clause beside a bodied Bool operation",
    );
}

// ── G. found while fixing ─────────────────────────────────────────────────────────────────

/// AN EFFECT OF THE PROGRAM'S OWN IS ITSELF, WHATEVER ITS NAME: a sort `absent` that provides
/// `Effect`, written `effects {absent[label = Int64]}`. The row's atoms were recognised by a
/// name's last segment, so this was read as the absence atom and its label as the effect, and
/// refused: "declares effect `Int64`, but `anthill.prelude.Int64` is not a REGISTERED effect
/// kind". The twin that does not provide `Effect` is what tells the readings apart: it is
/// refused naming the sort, where the last-segment reading named its label.
#[test]
fn an_effect_named_like_a_row_atom_is_its_own_effect() {
    let program = |provides: &str| {
        format!(
            "namespace test.r5.atomname\n  import anthill.prelude.{{Int64, Effect}}\n  sort absent\n    \
             sort label = ?\n{provides}  end\n  operation f(x: Int64) -> Int64 effects {{absent[label = \
             Int64]}} = x\nend\n"
        )
    };
    assert_eq!(load_errors_of(&program("    provides Effect[T = absent]\n")), Vec::<String>::new());
    let errs = load_errors_of(&program(""));
    assert_refused_naming(
        &errs,
        &["`test.r5.atomname.absent` is not a REGISTERED effect kind"],
        "a sort named `absent` that is no effect",
    );
    assert!(errs.iter().all(|e| !e.contains("anthill.prelude.Int64")), "{errs:#?}");
}
