//! WI-20260908-9WVT7's sixth review — the rows of its fixes, by what each one decides.
//!
//! A. A spec's contract is read through its transitive chain, a spec on a path read once.
//! B. The runtime's accounts are the constructor of their payload: a program matches one and
//!    raises a caught one again, and does not construct one (user, 2026-10-17).
//! C. A sort's induction axiom owns its name against an operation and a rule, in its own load
//!    and a later one, and against nothing else (user, 2026-10-17).
//! D. `ModifyRuntime.get` and `set` take a place that is itself of a modifiable type, not one
//!    that only holds a modifiable value (user, 2026-10-17); the refusal advises what repairs.
//! E. Which provision a call gets: one order on the provisions' heads, a default only among the
//!    tie, a provider's own row local by the half of its dictionary, the bottom type below every
//!    spelling of a head, an arrow's parameter met as itself.
//! F. The forward of a caller's parameter held inside a type: the requirement said as the call
//!    states it, the caller's evidence read as a call reads it, a part's missing instance told.
//! G. A structural former is the cause only where no provision answered at it and the scope
//!    cannot supply it, at a construction and at a call alike; a cycle is told its own repair.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build, over this
//! file and over the whole `wi_tests` binary, where each moves only the rows named here:
//!
//!   * the contract walked by the goals asked → [`a_contract_asking_for_a_spec_at_a_larger_type_is_refused_and_the_load_ends`];
//!   * the typer's or the loader's construction refusal off → [`a_program_does_not_construct_a_runtime_account`];
//!   * `ModifyRuntime`'s place read by `type_admits_modify` → [`a_place_that_only_holds_a_modifiable_value_is_refused_at_load`];
//!   * a provider's own row in the spec half filtered as in the provider half →
//!     [`a_bundled_witness_keeps_its_contract_half_at_a_subtype`];
//!   * the default consulted among every candidate → [`a_default_arbitrates_only_the_tie`];
//!   * an arrow's parameter matched one way → [`an_arrow_parameter_is_met_as_itself`];
//!   * a variant read at its sort for every spec → [`a_variant_carrier_is_advised_as_the_call_states_it`];
//!   * the caller's `TypeValue` read off its own clauses alone →
//!     [`the_callers_evidence_is_read_through_its_requirements_contracts`];
//!   * a part's failure kept as a bool → [`a_parts_missing_instance_is_told_by_the_goal_it_failed_at`];
//!   * a forwarded failure told apart by its spec → [`a_provision_answering_at_the_former_is_told_its_condition`];
//!   * the scope test by groundness → [`an_untyped_lambda_is_the_formers_refusal_at_every_spelling`],
//!     [`a_former_holding_the_scopes_parameter_is_told_the_slot_only_where_a_row_could_answer`]
//!     and the call-site twin of the first, `typer_capability_matrix_test::the_row_remainders`'
//!     "lambda / through a provision chain" cell;
//!   * every former holding the scope's parameter told the slot →
//!     [`a_former_holding_the_scopes_parameter_is_told_the_slot_only_where_a_row_could_answer`];
//!   * a cycle given the tie's tail and the slot tail → [`a_cycle_is_told_its_own_repair`].
//!
//! The rest are measured against the tree before this review, whose readings were deleted
//! rather than kept behind a switch — the raise's mark, the induction check at the axiom's
//! derivation, the count ranking, the bottom type at a bare head alone, the place advice: each of
//! [`a_caught_account_is_read_and_raised_again_is_the_runtimes`],
//! [`an_operation_or_a_rule_under_the_induction_axiom_is_refused_where_it_is_written`],
//! [`another_declaration_under_the_induction_axioms_name_loads`],
//! [`incomparable_heads_tie_and_a_chain_is_ranked`],
//! [`a_variant_and_its_sort_rank_alike_in_both_spellings`],
//! [`the_bottom_type_is_below_every_spelling_of_a_head`] and
//! [`the_place_refusal_advises_a_repair_that_runs`] fails there as its comment says. So does
//! every other row of this file.
//!
//! PASSES EITHER WAY, BY DESIGN: the repairs each refusal advises, run; the controls named in the
//! rows.

use crate::common::{assert_refused_naming, fault_messages, load_errors_of, run_int64};

/// `load_errors_of(src)` on a thread, failed when it does not finish: the defect a row with it
/// exists for is a load that never ends, which would stall the whole test binary.
fn load_errors_within(src: String, why: &str) -> Vec<String> {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(load_errors_of(&src));
    });
    rx.recv_timeout(std::time::Duration::from_secs(120))
        .unwrap_or_else(|_| panic!("{why}: the load did not end within 120 s"))
}

// ── A. a spec's contract, read once per spec on a path ───────────────────────────────────

const GROWING: &str = r#"
namespace test.r6.grow
  import anthill.prelude.{Int64, String, List, Option}
  sort Desc2
    sort T = ?
    requires Desc2[T = List[T = T]]
    operation d(x: T) -> String
  end
  sort A
    sort T = ?
    requires B[T = List[T = T]]
    operation a(x: T) -> String
  end
  sort B
    sort T = ?
    requires A[T = Option[T = T]]
    operation b(x: T) -> String
  end
"#;

/// A CONTRACT THAT ASKS FOR A SPEC AGAIN AT A LARGER TYPE ENDS IN ITS REFUSAL. `Desc2 requires
/// Desc2[T = List[T = T]]`, and `A` and `B` asking for each other at growing types: the account
/// of a call that no row answers read the program's specs' contracts by a list of the goals
/// asked, each new goal larger than the last, and the load never ended. The spec operation's
/// call, a generic callee's requirement and a construction each reach that account.
///
/// FAILS with the walk by goal back: the load does not end — the goal grows until the load's
/// thread overflows its stack and the test binary aborts (MEASURED unoptimized, on the first
/// shape; the CLI's main thread ran on, past 2 GB).
#[test]
fn a_contract_asking_for_a_spec_at_a_larger_type_is_refused_and_the_load_ends() {
    for (shape, call, requirement) in [
        (
            "a spec operation's call",
            "  operation go() -> String = Desc2.d(5)\nend\n",
            "Desc2[T = anthill.prelude.Int64]",
        ),
        (
            "a generic callee's requirement",
            "  operation viaD[X](x: X) -> String requires Desc2[T = X] = Desc2.d(x)\n  \
             operation go() -> String = viaD(5)\nend\n",
            "Desc2[T = anthill.prelude.Int64]",
        ),
        (
            "a construction",
            "  sort Holder\n    requires Desc2[T = Int64]\n    entity holder(n: Int64)\n  \
             end\n  operation go() -> Holder = holder(1)\nend\n",
            "Desc2[T = anthill.prelude.Int64]",
        ),
        (
            "two specs asking for each other",
            "  operation go() -> String = A.a(5)\nend\n",
            "A[T = anthill.prelude.Int64]",
        ),
    ] {
        let errs = load_errors_within(format!("{GROWING}{call}"), shape);
        assert_refused_naming(&errs, &[requirement], shape);
    }
}

// ── B. the runtime's accounts ─────────────────────────────────────────────────────────────

/// A PROGRAM DOES NOT CONSTRUCT ONE OF THE RUNTIME'S ACCOUNTS, in any place a value is built:
/// an operation body, a const, a rule body's lambda, a fact, a rule body's own term (a goal's
/// argument, an `=`), a rule head. The bridge reads a raise's cause off its payload's
/// constructor, so a constructed `relation_floundered` raised by the program would be
/// scheduled in silence as the runtime's account of a drain that did not decide. Each place is
/// refused ONCE: the typer refuses text written as an operation body, the loader a clause's own
/// term.
///
/// FAILS with either refusal backed out: the typer's (`check_constructor_iter`) — the body,
/// const and lambda shapes load; the loader's (`RuntimeAccountInClause`) — the fact and rule
/// shapes load.
#[test]
fn a_program_does_not_construct_a_runtime_account() {
    let header = "namespace test.r6.acct\n  import anthill.prelude.{Int64, String, Error, List, Option, Bool}\n  \
                  import anthill.prelude.List.{nil}\n  import anthill.prelude.Option.{none}\n  \
                  import anthill.prelude.{RelationFloundered}\n  \
                  import anthill.prelude.RelationFloundered.{relation_floundered}\n  \
                  import anthill.reflect.{LoadFailed, ResolveStreamFailure}\n  \
                  import anthill.reflect.LoadFailed.{load_failed}\n  \
                  import anthill.reflect.ResolveStreamFailure.{evaluation_failure}\n";
    for (shape, item, ctor) in [
        (
            "an operation body's raise",
            "operation forge() -> Int64 effects {Error[RelationFloundered]} = \
             Error.raise(relation_floundered(goals: nil()))",
            "anthill.prelude.RelationFloundered.relation_floundered",
        ),
        (
            "a const",
            "const forged: LoadFailed = load_failed(diagnostics: nil())",
            "anthill.reflect.LoadFailed.load_failed",
        ),
        (
            "a rule body's lambda",
            "rule r(?n) :- ?n <=> Error.reify(lambda () -> Error.raise(evaluation_failure(goals: \
             nil(), reason: \"x\", at: none())))",
            "anthill.reflect.ResolveStreamFailure.evaluation_failure",
        ),
        (
            "a fact",
            "fact held(load_failed(diagnostics: nil()))",
            "anthill.reflect.LoadFailed.load_failed",
        ),
        (
            "a goal's argument",
            "rule same(?a, ?a)\n  rule made(?x) :- same(?x, relation_floundered(goals: nil()))",
            "anthill.prelude.RelationFloundered.relation_floundered",
        ),
        (
            "a rule body's `=`",
            "rule isFail(?e) :- ?e = load_failed(diagnostics: ?d)",
            "anthill.reflect.LoadFailed.load_failed",
        ),
        (
            "a rule head",
            "rule made2(load_failed(diagnostics: nil())) :- true",
            "anthill.reflect.LoadFailed.load_failed",
        ),
    ] {
        let errs = load_errors_of(&format!("{header}  {item}\nend\n"));
        assert_refused_naming(&errs, &[ctor, "does not construct one"], shape);
        assert_eq!(
            errs.iter().filter(|e| e.contains(ctor)).count(),
            1,
            "{shape}: refused once, by the typer or by the loader: {errs:#?}"
        );
    }
}

const LOAD_BAD: &str = r#"
namespace test.r6.reraise
  import anthill.prelude.{Int64, String, Error, Result, List}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Result.{ok, err}
  import anthill.reflect.{KB, LoadFailed}
  import anthill.reflect.LoadFailed.{load_failed}
  operation loadBad() -> Int64 effects Error[LoadFailed] =
    let _ = KB.loaded(cons("namespace zz.bad fact Nope(", nil()))
    1
  operation readIt() -> Int64 =
    match Error.reify(lambda () -> loadBad())
      case ok(n) -> n
      case err(load_failed(ds)) -> 7
  operation both() -> Int64 effects Error[LoadFailed] =
    Result.reflect(Error.reify(lambda () -> loadBad()))
  rule viaOp(?n) :- ?n <=> both()
  rule split(?n) :- ?r <=> Error.reify(lambda () -> loadBad()), ?n <=> Result.reflect(?r)
end
"#;

/// A CAUGHT ACCOUNT IS MATCHED, AND RAISED AGAIN IT IS STILL THE RUNTIME'S, in the operation
/// that caught it and in a later goal of the rule. `readIt` matches `load_failed(ds)` in its
/// pattern; `split` catches in one goal and raises again in the next, where the mark the raise
/// carried before lived on the first goal's interpreter: the second goal was told to reach for
/// `Error.reify`, which it had, and a constraint over it did not load, while its one-operation
/// twin `viaOp` was silent and loaded.
///
/// FAILS with the partition read off a mark on the raise (the reading before this review):
/// `split` is reported and its constraint refused. `readIt` and `viaOp` pass either way.
#[test]
fn a_caught_account_is_read_and_raised_again_is_the_runtimes() {
    assert_eq!(run_int64(LOAD_BAD, "test.r6.reraise.readIt"), Ok(7));
    for goal in ["test.r6.reraise.viaOp(?n)", "test.r6.reraise.split(?n)"] {
        let messages = fault_messages(LOAD_BAD, goal);
        assert!(messages.is_empty(), "{goal}: the load's verdict is no fault: {messages:?}");
    }
    let constrained = crate::common::replace_in_fixture(
        LOAD_BAD,
        "end\n",
        "  fact item(1)\n  constraint allSplit: forall ?k: item(?k) -: split(?k)\nend\n",
    );
    assert_eq!(load_errors_of(&constrained), Vec::<String>::new());
}

// ── C. the induction axiom's name ─────────────────────────────────────────────────────────

/// AN OPERATION OR A RULE UNDER A SORT'S INDUCTION AXIOM IS REFUSED, NAMING WHERE IT IS
/// WRITTEN, in the sort's own load and in a later one. The refusal was made where the axiom
/// is derived, so an operation added to a library sort by the program's load (`namespace
/// anthill.prelude.Option { operation induction(…) }`) loaded, and a rule-body goal at it
/// answered nothing while the call answered `true`; a hand-written `rule induction(?x)` joined
/// the axiom's relation, which then answered through the axiom's clause; and the refusal
/// carried no location.
///
/// FAILS with the check at the axiom's derivation only (the reading before this review): the
/// later load and the rule load, and no refusal names a site.
#[test]
fn an_operation_or_a_rule_under_the_induction_axiom_is_refused_where_it_is_written() {
    for (shape, src, site) in [
        (
            "an operation in the sort",
            "namespace test.r6.ind\n  import anthill.prelude.{Bool}\n  sort Colour\n    entity red\n    \
             entity green\n    operation induction(c: Colour) -> Bool = true\n  end\nend\n",
            "declared at 6:5",
        ),
        (
            "an operation a later load adds to a library sort",
            "namespace anthill.prelude.Option\n  import anthill.prelude.{Bool, Int64}\n  \
             operation induction(o: anthill.prelude.Option[T = Int64]) -> Bool = true\nend\n",
            "declared at 3:3",
        ),
        (
            "a hand-written rule in the sort",
            "namespace test.r6.indr\n  sort Colour\n    entity red\n    entity green\n    \
             rule induction(?x) :- true\n  end\nend\n",
            "declared at 5:10",
        ),
    ] {
        let errs = load_errors_of(src);
        assert_refused_naming(
            &errs,
            &[".induction` names the induction axiom derived for", site],
            shape,
        );
    }
}

/// ANOTHER DECLARATION UNDER THE AXIOM'S NAME LOADS, AND THE FACTS ABOUT AN ENTITY OF THAT NAME
/// ARE ITS DATA. `entity induction(depth: Int64)` beside `entity deduction`, matched by an
/// operation and stated by a fact; a const and a nested sort of the name. The check by a
/// symbol's first-declared kind refused each, with no location, where each had loaded and run.
///
/// FAILS with the refusal of every kind but a rule's (the reading before this review): every
/// shape is refused.
#[test]
fn another_declaration_under_the_induction_axioms_name_loads() {
    let entity = r#"
namespace test.r6.inde
  import anthill.prelude.{Int64}
  sort ProofMethod
    entity induction(depth: Int64)
    entity deduction
  end
  operation score(m: ProofMethod) -> Int64 =
    match m
      case induction(d) -> d
      case deduction -> 2
  operation go() -> Int64 = score(induction(depth: 5)) + score(deduction)
  fact ProofMethod.induction(depth: 7)
end
"#;
    assert_eq!(run_int64(entity, "test.r6.inde.go"), Ok(7));
    for (shape, src) in [
        (
            "a const",
            "namespace test.r6.indc\n  import anthill.prelude.{Int64}\n  sort Colour\n    entity red\n    \
             entity green\n    const induction: Int64 = 3\n  end\nend\n",
        ),
        (
            "a nested sort",
            "namespace test.r6.indn\n  sort Colour\n    entity red\n    entity green\n    \
             sort induction\n      entity proof\n    end\n  end\nend\n",
        ),
    ] {
        assert_eq!(load_errors_of(src), Vec::<String>::new(), "{shape}");
    }
}

// ── D. the place `ModifyRuntime` reads and writes ─────────────────────────────────────────

/// `get` / `set` run with the standard handlers, answering an `Int64`.
fn run_with_handlers(src: &str, entry: &str) -> Result<i64, String> {
    let mut interp = crate::common::interp_for(src);
    interp
        .register_standard_effect_handlers()
        .expect("register the standard effect handlers");
    match interp.call(entry, &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => Ok(n),
        other => Err(format!("`{entry}` did not answer an Int64: {other:?}")),
    }
}

/// A PLACE THAT ONLY HOLDS A MODIFIABLE VALUE IS NO PLACE THE HANDLER KEEPS, AND IS REFUSED AT
/// LOAD. `get` and `set` read and write the place they are handed, and the standard handler keys
/// a place by its constructor: an empty `List[T = Cell]` was written at `set(xs, 42)` and read
/// back through ANOTHER empty list (42 — every `nil` one slot), a tuple with a `Cell` part and a
/// function value returning one loaded and died at run time, an entity with a `Cell` field of a
/// sort with no `Modifiable` loaded and died naming WI-200. The check asked whether a `Modify`
/// could fire somewhere under the type, which each of these answers yes.
///
/// FAILS with the check reading `type_admits_modify` (the reading before this review): every
/// shape loads.
#[test]
fn a_place_that_only_holds_a_modifiable_value_is_refused_at_load() {
    let program = |decls: &str, body: &str| {
        format!(
            "namespace test.r6.hold\n  import anthill.prelude.{{Int64, Unit, Modify, Modifiable, Cell, List}}\n  \
             import anthill.prelude.List.{{nil}}\n  import anthill.prelude.ModifyRuntime.{{set, get}}\n\
             {decls}  operation go() -> Int64 =\n{body}end\n"
        )
    };
    for (shape, decls, body, place) in [
        (
            "an empty list of cells",
            "  operation write(xs: List[T = Cell[V = Int64]]) -> Unit effects Modify[xs] = set(xs, 42)\n",
            "    let xs: List[T = Cell[V = Int64]] = nil()\n    let _ = write(xs)\n    0\n",
            "List[T = Cell[V = Int64]]",
        ),
        (
            "a tuple with a cell part",
            "",
            "    let t = (Cell.new(1), 2)\n    let _ = set(t, 5)\n    0\n",
            "(_1: Cell[V = Int64], _2: Int64)",
        ),
        (
            "an entity with a cell field",
            "  sort W\n    entity w(c: Cell[V = Int64])\n  end\n  \
             operation put(x: W, n: Int64) -> Unit effects Modify[x] = set(x, n)\n",
            "    let x = w(c: Cell.new(1))\n    let _ = put(x, 5)\n    0\n",
            "W",
        ),
    ] {
        let errs = load_errors_of(&program(decls, body));
        assert_refused_naming(
            &errs,
            &["expected a place of a modifiable type", &format!("got a place of type `{place}`")],
            shape,
        );
    }
}

/// THE REFUSAL ADVISES A REPAIR THAT RUNS. `sort Plain { entity plain(n: Int64) }` given to
/// `set` was told to give it a sort declaring `provides Modifiable[T = Self]`, and that program
/// loaded and died on the standard handler's refusal of a resource built with fields (WI-200).
/// The advice names a `Cell` first, and `Modifiable` only for a sort whose constructors take no
/// fields: both run, answering what they wrote.
///
/// FAILS with the advice as it was (the text asserted). The two repairs pass either way: they
/// are programs that ran before the refusal named them.
#[test]
fn the_place_refusal_advises_a_repair_that_runs() {
    let refused = "namespace test.r6.plain\n  import anthill.prelude.{Int64, Unit}\n  \
                   import anthill.prelude.ModifyRuntime.{set}\n  sort Plain\n    entity plain(n: Int64)\n  \
                   end\n  operation put(p: Plain, n: Int64) -> Unit = set(p, n)\nend\n";
    assert_refused_naming(
        &load_errors_of(refused),
        &[
            "Make the place a `Cell`",
            "a sort of the program's own whose constructors take no fields may instead declare \
             `provides Modifiable[T = Self]`",
        ],
        "a constructor with fields",
    );
    let as_cell = r#"
namespace test.r6.ascell
  import anthill.prelude.{Int64, Unit, Modify, Cell}
  import anthill.prelude.ModifyRuntime.{set, get}
  operation put(p: Cell[V = Int64], n: Int64) -> Unit effects Modify[p] = set(p, n)
  operation go() -> Int64 =
    let p = Cell.new(3)
    let _ = put(p, 5)
    get(p)
end
"#;
    assert_eq!(run_with_handlers(as_cell, "test.r6.ascell.go"), Ok(5));
    let as_nullary = r#"
namespace test.r6.asnull
  import anthill.prelude.{Int64, Unit, Modify, Modifiable}
  import anthill.prelude.ModifyRuntime.{set, get}
  sort Plain
    provides Modifiable[T = Self]
    entity plain
  end
  operation put(p: Plain, n: Int64) -> Unit effects Modify[p] = set(p, n)
  operation go() -> Int64 effects Modify[plain] =
    let _ = put(plain, 6)
    get(plain)
end
"#;
    assert_eq!(run_with_handlers(as_nullary, "test.r6.asnull.go"), Ok(6));
}

// ── E. which provision a call gets ────────────────────────────────────────────────────────

const DESC_AT: &str = "  sort Desc\n    sort T = ?\n    operation describe(x: T) -> Int64\n  end\n  \
                       sort Reader\n    sort HT = ?\n    operation probe(x: HT) -> Int64 requires \
                       Desc[T = HT] = Desc.describe(x)\n  end\n";

/// TWO HEADS NEITHER MORE SPECIFIC THAN THE OTHER TIE, AND A CHAIN IS RANKED. Ranking counted
/// what a head fixes and then the leaves the call reached through the subtype relation: at a
/// `Tri[Dog, Dog, Dog]` the provision at `Tri[A = Animal, B = Dog, C = Dog]` silently beat the one
/// at `Tri[A = Dog, B = Animal, C = Animal]` (two leaves fewer), and at `Duo[Dog, Dog]` the one at
/// `Duo[A = Animal, B = Animal]` beat the one at `Duo[A = Dog, B = X]` (one fixed part more),
/// where each answers a call the other does not; and at a `Dog`, provisions at `Being` and at
/// `Animal` (`Dog < Animal < Being`) tied, though `Animal`'s is the more specific. The order: one
/// head is more specific than another where the other answers at it and it does not answer at the
/// other.
///
/// FAILS with the count ranking back: the two pairs load and pick, the chain is refused as a tie.
#[test]
fn incomparable_heads_tie_and_a_chain_is_ranked() {
    let animals = "  sort Being\n    entity being\n  end\n  sort Animal\n    requires Being\n    \
                   entity animal\n  end\n  sort Dog\n    requires Animal\n    entity dog\n  end\n";
    let tri = format!(
        "namespace test.r6.three\n  import anthill.prelude.{{Int64}}\n{DESC_AT}{animals}  sort Tri\n    \
         sort A = ?\n    sort B = ?\n    sort C = ?\n    entity tri(a: A, b: B, c: C)\n  end\n  \
         sort P1\n    provides Desc[T = Tri[A = Dog, B = Animal, C = Animal]]\n    operation \
         describe(x: Tri[A = Dog, B = Animal, C = Animal]) -> Int64 = 1\n  end\n  sort P2\n    \
         provides Desc[T = Tri[A = Animal, B = Dog, C = Dog]]\n    operation describe(x: Tri[A = \
         Animal, B = Dog, C = Dog]) -> Int64 = 2\n  end\n  operation mk() -> Tri[A = Dog, B = Dog, \
         C = Dog] = tri(a: dog, b: dog, c: dog)\n  operation go() -> Int64 = Reader.probe(mk())\nend\n"
    );
    assert_refused_naming(&load_errors_of(&tri), &["ambiguous among providers", "P1", "P2"], "Tri");
    let duo = format!(
        "namespace test.r6.two\n  import anthill.prelude.{{Int64}}\n{DESC_AT}{animals}  sort Duo\n    \
         sort A = ?\n    sort B = ?\n    entity duo(a: A, b: B)\n  end\n  sort P1\n    provides \
         Desc[T = Duo[A = Animal, B = Animal]]\n    operation describe(x: Duo[A = Animal, B = \
         Animal]) -> Int64 = 1\n  end\n  sort P2\n    sort X = ?\n    provides Desc[T = Duo[A = \
         Dog, B = X]]\n    operation describe(x: Duo[A = Dog, B = X]) -> Int64 = 2\n  end\n  \
         operation mk() -> Duo[A = Dog, B = Dog] = duo(a: dog, b: dog)\n  operation go() -> Int64 = \
         Reader.probe(mk())\nend\n"
    );
    assert_refused_naming(&load_errors_of(&duo), &["ambiguous among providers", "P1", "P2"], "Duo");
    let chain = format!(
        "namespace test.r6.chain\n  import anthill.prelude.{{Int64}}\n{DESC_AT}{animals}  sort AtBeing\n    \
         provides Desc[T = Being]\n    operation describe(x: Being) -> Int64 = 1\n  end\n  sort \
         AtAnimal\n    provides Desc[T = Animal]\n    operation describe(x: Animal) -> Int64 = 2\n  \
         end\n  operation go() -> Int64 = Reader.probe(dog)\nend\n"
    );
    assert_eq!(run_int64(&chain, "test.r6.chain.go"), Ok(2));
}

/// A VARIANT AND ITS SORT RANK ALIKE IN BOTH SPELLINGS, as a head and as a condition. A provision
/// at a variant (`Colour.red`, `Wrap.wrap[V = V]`) is more specific than one at its sort; ranked by
/// a count of the leaves reached through the subtype relation, the bare variant was and the
/// parametric one was not (read at its sort, it counted none) — the bare spelling picked the
/// variant's provision and the parametric one was refused as a tie; and `Wrap provides Desc[T =
/// Wrap[V = V]] :- Desc[T = Wrap.wrap[V = V]]` kept `Wrap`'s own row for its condition, a cycle
/// refused at load, where the bare twin ran.
///
/// FAILS with the count ranking back: the parametric shapes are refused.
#[test]
fn a_variant_and_its_sort_rank_alike_in_both_spellings() {
    let bare = format!(
        "namespace test.r6.vbare\n  import anthill.prelude.{{Int64}}\n{DESC_AT}  sort Colour\n    \
         entity red\n    entity blue\n    provides Desc[T = Colour]\n    operation describe(x: \
         Colour) -> Int64 = 1\n  end\n  sort RedDesc\n    provides Desc[T = Colour.red]\n    \
         operation describe(x: Colour.red) -> Int64 = 2\n  end\n  operation at(x: Colour.red) -> \
         Int64 = Desc.describe(x)\n  operation go() -> Int64 = at(red)\nend\n"
    );
    assert_eq!(run_int64(&bare, "test.r6.vbare.go"), Ok(2));
    let wrap = "  sort Wrap\n    sort V = ?\n    entity wrap(v: V)\n    entity other(n: Int64)\n";
    let wrap_desc = "  sort WrapDesc\n    sort V = ?\n    provides Desc[T = Wrap.wrap[V = V]]\n    \
                     operation describe(x: Wrap.wrap[V = V]) -> Int64 = 2\n  end\n";
    let param = format!(
        "namespace test.r6.vparam\n  import anthill.prelude.{{Int64}}\n{DESC_AT}{wrap}    provides \
         Desc[T = Wrap[V = V]]\n    operation describe(x: Wrap[V = V]) -> Int64 = 1\n  end\n{wrap_desc}  \
         operation at(x: Wrap.wrap[V = Int64]) -> Int64 = Desc.describe(x)\n  operation go() -> \
         Int64 = at(wrap(v: 5))\nend\n"
    );
    assert_eq!(run_int64(&param, "test.r6.vparam.go"), Ok(2));
    let condition = format!(
        "namespace test.r6.vcond\n  import anthill.prelude.{{Int64}}\n{DESC_AT}{wrap}    provides \
         Desc[T = Wrap[V = V]] :- Desc[T = Wrap.wrap[V = V]]\n    operation describe(x: Wrap[V = \
         V]) -> Int64 = 1\n  end\n{wrap_desc}  operation mk() -> Wrap[V = Int64] = other(n: 3)\n  \
         operation go() -> Int64 = Reader.probe(mk())\nend\n"
    );
    assert_eq!(run_int64(&condition, "test.r6.vcond.go"), Ok(1));
}

/// A BUNDLED WITNESS KEEPS ITS CONTRACT HALF AT A SUBTYPE. `AscW` provides `TOrd[T = Animal]` and
/// `POrd[T = Animal]`, `TOrd requires POrd[T = T]`, `Dog` (a subtype of `Animal`) provides its own
/// `POrd`: at a `Dog`, `AscW`'s `TOrd` dictionary took `Dog`'s `POrd` for its contract once a
/// provider's own row was local only where met as itself, and `TOrd`'s default `cmp` answered
/// from it — 20 where `AscW`'s ordering says 10, in silence. The provision's own conditions are the
/// other half, where its own row yields to a more specific one (the refinement row of the fifth
/// review, `a_refinements_condition_takes_the_refinements_provision`).
///
/// FAILS with locality by the subtype reach in both halves (the fifth review's): 20.
#[test]
fn a_bundled_witness_keeps_its_contract_half_at_a_subtype() {
    let src = r#"
namespace test.r6.bundle
  import anthill.prelude.{Int64, Bool}
  sort POrd
    sort T = ?
    operation lt(a: T, b: T) -> Bool
  end
  sort TOrd
    sort T = ?
    requires POrd[T = T]
    operation cmp(a: T, b: T) -> Int64 = if POrd.lt(a, b) then 10 else 20
  end
  sort Animal
    entity animal(n: Int64)
  end
  sort Dog
    requires Animal
    entity dog(n: Int64)
    provides POrd[T = Dog]
    operation lt(a: Dog, b: Dog) -> Bool = false
  end
  sort AscW
    provides TOrd[T = Animal]
    provides POrd[T = Animal]
    operation lt(a: Animal, b: Animal) -> Bool = true
  end
  operation useT[X](a: X, b: X) -> Int64 requires TOrd[T = X] = TOrd.cmp(a, b)
  operation go() -> Int64 = useT(dog(1), dog(2))
end
"#;
    assert_eq!(run_int64(src, "test.r6.bundle.go"), Ok(10));
}

/// THE BOTTOM TYPE IS BELOW EVERY SPELLING OF A HEAD, and a provision met there with a condition
/// on a parameter it left open is no candidate. `Counter.count([])` asks `Stamp[T = Nothing]`:
/// beside `Leaf provides Stamp[T = Leaf]`, a rival written `Stamp[T = Box]` tied while the same
/// rival written `Stamp[T = Box[V = V]]`, at a tuple or at an arrow was never met and `Leaf`
/// answered in silence. `useD([])` over `ListDesc provides Desc[T = List[T = E]] :- Desc[T = E]` asks
/// `Desc[T = Nothing]` for its condition, which `ListDesc` itself meets with `E` open — a guess it
/// does not take, so `IntDesc` answers.
///
/// FAILS with the bottom type meeting bare heads alone: the application-headed rival loads and
/// answers 42.
#[test]
fn the_bottom_type_is_below_every_spelling_of_a_head() {
    let stamp = |rival: &str| {
        format!(
            "namespace test.r6.bottom\n  import anthill.prelude.{{Int64, List}}\n  sort Stamp\n    \
             sort T = ?\n    operation stamp() -> Int64\n  end\n  sort Leaf\n    entity leaf\n    \
             provides Stamp[T = Leaf]\n    operation stamp() -> Int64 = 42\n  end\n  sort Box\n    \
             sort V = ?\n    entity box(v: V)\n    provides Stamp[T = {rival}]\n    operation \
             stamp() -> Int64 = 7\n  end\n  operation count[A](xs: List[T = A]) -> Int64 requires \
             Stamp[T = A] = Stamp.stamp()\n  operation go() -> Int64 =\n    let xs = []\n    \
             count(xs)\nend\n"
        )
    };
    for rival in ["Box", "Box[V = V]", "(Int64, Int64)", "(Int64) -> Int64"] {
        assert_refused_naming(
            &load_errors_of(&stamp(rival)),
            &["ambiguous among providers", "Leaf", "Box"],
            rival,
        );
    }
    let list = r#"
namespace test.r6.bottomlist
  import anthill.prelude.{Int64, List}
  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation d(x: Int64) -> Int64 = 1
  end
  sort ListDesc
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
    assert_eq!(run_int64(list, "test.r6.bottomlist.go"), Ok(7));
}

/// A DEFAULT ARBITRATES ONLY THE TIE. `Box provides Desc[T = Box[B = B]]` is the self-provision
/// default; `W1` and `W2` both provide `Desc[T = Box[B = Int64]]`, more specific than it and tied:
/// handed every candidate, the default answered over them (3) where the dispatch must name the two.
///
/// FAILS with the default consulted among every candidate: it loads and answers 3.
#[test]
fn a_default_arbitrates_only_the_tie() {
    let src = r#"
namespace test.r6.dflt
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation d(x: T) -> Int64
  end
  sort Box
    sort B = ?
    entity box(inner: B)
    provides Desc[T = Box[B = B]]
    operation d(x: Box[B = B]) -> Int64 = 3
  end
  sort W1
    provides Desc[T = Box[B = Int64]]
    operation d(x: Box[B = Int64]) -> Int64 = 1
  end
  sort W2
    provides Desc[T = Box[B = Int64]]
    operation d(x: Box[B = Int64]) -> Int64 = 2
  end
  operation useD[X](x: X) -> Int64 requires Desc[T = X] = Desc.d(x)
  operation go() -> Int64 = useD(box(inner: 5))
end
"#;
    let errs = load_errors_of(src);
    assert_refused_naming(&errs, &["ambiguous among providers", "W1", "W2"], "the tie");
    assert!(
        errs.iter().all(|e| !e.contains("test.r6.dflt.Box,") && !e.contains("test.r6.dflt.Box ")),
        "the default outranked by both is not in the tie: {errs:#?}"
    );
}

/// AN ARROW'S PARAMETER IS MET AS ITSELF, ITS RESULT THROUGH THE SUBTYPE RELATION. A provision at
/// `(Animal) -> Int64`, whose member hands the callback an `animal`, answered a callback taking a
/// `Dog`, a `List[T = Dog]`, or — once the bottom type no longer stopped it — `Nothing`: each
/// loaded and died at run time. A result below the provision's is still met
/// (`a_raising_callback_meets_its_arrow_provision`). The callback at the provision's own
/// parameter is the control and passes either way.
///
/// FAILS with the parameter matched one way: the three callbacks load.
#[test]
fn an_arrow_parameter_is_met_as_itself() {
    let program = |callback: &str| {
        format!(
            "namespace test.r6.arrow\n  import anthill.prelude.{{Int64, String, List}}\n  sort Runner\n    \
             sort F = ?\n    operation run(f: F) -> Int64\n  end\n  sort Animal\n    entity animal\n  \
             end\n  sort Dog\n    requires Animal\n    entity dog\n  end\n  sort AnimalRunner\n    \
             provides Runner[F = (Animal) -> Int64]\n    operation run(f: (Animal) -> Int64) -> \
             Int64 = f(animal)\n  end\n  operation go() -> Int64 = Runner.run({callback})\nend\n"
        )
    };
    for (shape, callback) in [
        ("a Dog parameter", "lambda (d: Dog) -> 1"),
        ("a List of Dog parameter", "lambda (d: List[T = Dog]) -> 1"),
        ("a Nothing parameter", "lambda (d: Nothing) -> 1"),
    ] {
        assert_refused_naming(
            &load_errors_of(&program(callback)),
            &["expected a requirement suppliable at this call site"],
            shape,
        );
    }
    assert_eq!(run_int64(&program("lambda (a: Animal) -> 5"), "test.r6.arrow.go"), Ok(5));
}

// ── F. the forward's account ──────────────────────────────────────────────────────────────

/// A VARIANT CARRIER IS ADVISED AS THE CALL STATES IT, and the clause runs. `fwd[C](w:
/// Wrap.wrap[V = C]) = Reader.probe(w)` was told to declare `requires Desc[T = Wrap[V = C]]` —
/// the variant read at its sort, which a scope clause does not cover — and with it pasted, the
/// same refusal came back. The library's two specs still read a variant at its sort, whose
/// derived instance answers for it.
///
/// FAILS with the variant read at its sort for every spec: the advice names `Wrap[V = C]` and the
/// pasted program is refused again.
#[test]
fn a_variant_carrier_is_advised_as_the_call_states_it() {
    let program = |clause: &str| {
        format!(
            "namespace test.r6.var\n  import anthill.prelude.{{Int64}}\n{DESC_AT}  sort Wrap\n    sort V = ?\n    \
             entity wrap(v: V)\n    entity other(n: Int64)\n  end\n  sort IntWrapDesc\n    provides \
             Desc[T = Wrap[V = Int64]]\n    operation describe(x: Wrap[V = Int64]) -> Int64 = 3\n  end\n  \
             operation fwd[C](w: Wrap.wrap[V = C]) -> Int64{clause} = Reader.probe(w)\n  operation \
             go() -> Int64 = fwd(wrap(v: 5))\nend\n"
        )
    };
    let advised = "requires test.r6.var.Desc[T = test.r6.var.Wrap.wrap[V = C]]";
    assert_refused_naming(&load_errors_of(&program("")), &[advised], "the forward");
    assert_eq!(run_int64(&program(&format!(" {advised}")), "test.r6.var.go"), Ok(3));
}

/// THE CALLER'S EVIDENCE IS READ AS A CALL READS IT, through another requirement's contract.
/// `Holder requires Desc[T = A]`, `Desc requires TypeValue[T = T]`: the forward of `pair(a, b)`
/// into `tyOf` was refused naming `A` ("holds nothing for `A`") and advising `TypeValue` at both
/// parameters, where only `B` lacks it — the reading looked at the caller's direct `TypeValue`
/// clauses alone.
///
/// FAILS with the direct reading: the refusal names `A`.
#[test]
fn the_callers_evidence_is_read_through_its_requirements_contracts() {
    let program = |clause: &str| {
        format!(
            "namespace test.r6.chain\n  import anthill.prelude.{{Int64, Pair}}\n  import \
             anthill.prelude.Pair.{{pair}}\n  import anthill.reflect.{{TypeValue}}\n  sort Desc\n    \
             sort T = ?\n    requires TypeValue[T = T]\n    operation describe(x: T) -> Int64\n  end\n  \
             operation tyOf[X](x: X) -> Int64 requires TypeValue[T = X] = 1\n  sort Holder\n    sort A \
             = ?\n    requires Desc[T = A]\n    operation probe[B](a: A, b: B) -> Int64{clause} = \
             tyOf(pair(fst: a, snd: b))\n  end\nend\n"
        )
    };
    let errs = load_errors_of(&program(""));
    assert_refused_naming(&errs, &["holds nothing for `B`", "requires anthill.reflect.TypeValue[T = B]` on"], "B");
    assert!(errs.iter().all(|e| !e.contains("holds nothing for `A`")), "{errs:#?}");
    assert_eq!(
        load_errors_of(&program(" requires anthill.reflect.TypeValue[T = B]")),
        Vec::<String>::new()
    );
}

/// A PART'S MISSING INSTANCE IS TOLD BY THE GOAL IT FAILED AT. `part[C](x: C, k: Keyed[K =
/// Float]) requires TypeValue[T = C] = tyOf(pair(x, k))`, with `Keyed requires Desc[T = K]`: the
/// part `Keyed[K = Float]` has no `TypeValue` because no `Desc[T = Float]` exists, and it was told
/// to pass a value of a sort with every type argument written, which it is. Its direct twin
/// `tyOf(k)` is told the missing `Desc`; so is the part now, and the provision repairs both.
///
/// FAILS with the part kept as a bool: the library's advice.
#[test]
fn a_parts_missing_instance_is_told_by_the_goal_it_failed_at() {
    let program = |extra: &str| {
        format!(
            "namespace test.r6.keyed\n  import anthill.prelude.{{Int64, Float, Pair}}\n  import \
             anthill.prelude.Pair.{{pair}}\n  import anthill.reflect.{{TypeValue}}\n  sort Desc\n    \
             sort T = ?\n    operation describe(x: T) -> Int64\n  end\n{extra}  sort Keyed\n    sort K = \
             ?\n    requires Desc[T = K]\n    entity keyed(k: K)\n  end\n  operation tyOf[B](x: B) -> \
             Int64 requires TypeValue[T = B] = 1\n  operation part[C](x: C, k: Keyed[K = Float]) -> \
             Int64 requires TypeValue[T = C] = tyOf(pair(x, k))\nend\n"
        )
    };
    let errs = load_errors_of(&program(""));
    assert_refused_naming(
        &errs,
        &["holds `test.r6.keyed.Keyed[K = anthill.prelude.Float]`", "no impl provides test.r6.keyed.Desc"],
        "the part",
    );
    assert!(errs.iter().all(|e| !e.contains("every type argument of it written")), "{errs:#?}");
    let repaired = program(
        "  sort FloatDesc\n    provides Desc[T = Float]\n    operation describe(x: Float) -> Int64 = 2\n  end\n",
    );
    assert_eq!(load_errors_of(&repaired), Vec::<String>::new());
}

// ── G. the former's refusal, and a cycle's ────────────────────────────────────────────────

const APPLY: &str = "  sort Apply\n    sort F = ?\n    operation run(f: F) -> Int64\n  end\n  sort Holder\n    \
                     sort F = ?\n    requires Apply[F = F]\n    entity holder(f: F)\n    operation go(h: Self) \
                     -> Int64 = Apply.run(h.f)\n  end\n  operation run2[G](f: G) -> Int64 requires Apply[F \
                     = G] = Apply.run(f)\n";

/// A PROVISION THAT ANSWERED AT THE FORMER IS TOLD ITS CONDITION, AT A CONSTRUCTION AND AT A CALL.
/// `P provides Apply[F = (A) -> Int64]` under `P requires Apply[F = A]`: at a callback taking a
/// `String`, `P` answers at the arrow and its own requirement `Apply[F = String]` fails. The test
/// that read the failure's spec saw `Apply` both times and told the program nothing provides
/// `Apply` at the former; the call path named the former whatever the cause. The account is the
/// condition's, and the provision it names repairs both spellings (answering `P`'s 3).
///
/// FAILS with the spec comparison back: the former's refusal at the construction.
#[test]
fn a_provision_answering_at_the_former_is_told_its_condition() {
    let program = |extra: &str, call: &str| {
        format!(
            "namespace test.r6.cond\n  import anthill.prelude.{{Int64, String}}\n{APPLY}  sort P\n    \
             sort A = ?\n    requires Apply[F = A]\n    provides Apply[F = (A) -> Int64]\n    operation \
             run(f: (A) -> Int64) -> Int64 = 3\n  end\n{extra}  operation mk() -> Int64 = {call}\nend\n"
        )
    };
    let str_apply = "  sort StrApply\n    provides Apply[F = String]\n    operation run(f: String) \
                     -> Int64 = 2\n  end\n";
    for (shape, call) in [
        ("a construction", "Holder.go(holder(lambda (s: String) -> 1))"),
        ("a call", "run2(lambda (s: String) -> 1)"),
    ] {
        let errs = load_errors_of(&program("", call));
        assert_refused_naming(&errs, &["no impl provides test.r6.cond.Apply"], shape);
        assert!(errs.iter().all(|e| !e.contains("STRUCTURAL FORMER")), "{shape}: {errs:#?}");
        assert_eq!(run_int64(&program(str_apply, call), "test.r6.cond.mk"), Ok(3), "{shape}");
    }
}

/// THE PARAMETER OF A LAMBDA WRITTEN WITHOUT ITS TYPE IS NO PARAMETER OF THE SCOPE, so the former
/// is the cause at a construction as at a call. `holder(lambda s -> 1)` and `Runner.run2(lambda s ->
/// 1)` through a sort-level `requires` were told to declare a requirement slot for `Apply[F =
/// ??param -> Int64]`, which no declaration can name, while the operation-level call named the
/// former; a ground former beside another, open binding was told the slot too.
///
/// FAILS with groundness for the scope test: the construction is told to declare a requirement
/// slot, and `typer_capability_matrix_test`'s cell for the call is told no impl provides the spec.
#[test]
fn an_untyped_lambda_is_the_formers_refusal_at_every_spelling() {
    for call in ["Holder.go(holder(lambda s -> 1))", "run2(lambda s -> 1)"] {
        let src = format!(
            "namespace test.r6.untyped\n  import anthill.prelude.{{Int64, String}}\n{APPLY}  operation mk() -> \
             Int64 = {call}\nend\n"
        );
        let errs = load_errors_of(&src);
        assert_refused_naming(&errs, &["STRUCTURAL FORMER"], call);
        assert!(errs.iter().all(|e| !e.contains("declare a requirement slot")), "{call}: {errs:#?}");
    }
}

/// A FORMER HOLDING THE SCOPE'S PARAMETER IS TOLD THE SLOT ONLY WHERE A ROW COULD ANSWER IT. With
/// no provision of `Desc` at any pair, `mk[C](x: C) = Reader.get((x, 1))` is the former's refusal
/// (told the slot, it only moved the refusal to `mk(5)`); with `Wrapper provides Desc[T = (Int64,
/// Int64)]` the call is told to declare the requirement on `mk` — in the caller's spelling, where
/// it printed the body's `?C` — and the clause pasted answers `Wrapper`'s 9.
///
/// FAILS with every former holding the scope's parameter told the slot, and with groundness for the
/// scope test: the program with no row is told it.
#[test]
fn a_former_holding_the_scopes_parameter_is_told_the_slot_only_where_a_row_could_answer() {
    let program = |extra: &str, clause: &str| {
        format!(
            "namespace test.r6.held\n  import anthill.prelude.{{Int64}}\n  sort Desc\n    sort T = ?\n    \
             operation d(x: T) -> Int64\n  end\n{extra}  sort Reader\n    sort G = ?\n    operation get(v: G) \
             -> Int64 requires Desc[T = G] = Desc.d(v)\n  end\n  operation mk[C](x: C) -> Int64{clause} = \
             Reader.get((x, 1))\n  operation go() -> Int64 = mk(5)\nend\n"
        )
    };
    let none = load_errors_of(&program("", ""));
    assert_refused_naming(&none, &["STRUCTURAL FORMER"], "no row at a pair");
    let wrapper = "  sort Wrapper\n    entity wrap(n: Int64)\n    provides Desc[T = (Int64, Int64)]\n    \
                   operation d(x: (Int64, Int64)) -> Int64 = 9\n  end\n";
    let clause = "requires test.r6.held.Desc[T = (C, anthill.prelude.Int64)]";
    assert_refused_naming(&load_errors_of(&program(wrapper, "")), &[clause], "a row at a pair");
    assert_eq!(run_int64(&program(wrapper, &format!(" {clause}")), "test.r6.held.go"), Ok(9));
}

/// A CYCLE IS TOLD ITS OWN REPAIR. `A provides Desc[T = A] :- Desc[T = B]` and its mirror: the
/// cycle refused at a call was told to pin the element — `Reader.probe[HT = A](a)` gets the same
/// refusal — and at a construction to declare a requirement slot, which moves the cycle to the
/// caller. Dropping a condition is the repair, and the program then answers.
///
/// FAILS with the tie's tail on the call's refusal and the slot tail on the construction's.
#[test]
fn a_cycle_is_told_its_own_repair() {
    let program = |b_provides: &str| {
        format!(
            "namespace test.r6.cyc\n  import anthill.prelude.{{Int64}}\n{DESC_AT}  sort A\n    entity a\n    \
             provides Desc[T = A] :- Desc[T = B]\n    operation describe(x: A) -> Int64 = 1\n  end\n  sort \
             B\n    entity b\n    {b_provides}\n    operation describe(x: B) -> Int64 = 2\n  end\n  sort \
             Holder\n    sort T = ?\n    requires Desc[T = T]\n    entity holder(v: T)\n  end\n  operation \
             viaA() -> Int64 = Reader.probe(a)\n  operation viaCtor() -> Holder[T = A] = holder(a)\nend\n"
        )
    };
    let errs = load_errors_of(&program("provides Desc[T = B] :- Desc[T = A]"));
    assert_refused_naming(&errs, &["construction is cyclic", "drop one of these conditions"], "the cycle");
    assert!(
        errs.iter().all(|e| !e.contains("pin the element") && !e.contains("declare a requirement slot")),
        "{errs:#?}"
    );
    assert_eq!(run_int64(&program("provides Desc[T = B]"), "test.r6.cyc.viaA"), Ok(1));
}
