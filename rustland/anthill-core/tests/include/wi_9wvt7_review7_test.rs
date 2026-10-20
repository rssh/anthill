//! WI-20260908-9WVT7's seventh review — the rows of its fixes, by what each one decides.
//!
//! A. The runtime's accounts are constructed by no program on any route: reflection, a query, a
//!    data file; a bare constructor name is no account.
//! B. A place written through a variant of a modifiable sort is a place of that sort.
//! C. A direct call of a defaulted spec member dispatches as a generic call does.
//! D. A `requires` in scope covers a call at an arrow only where the two are one binding: the
//!    parameters and the result the same (§5.2); a provision answers a result below its own.
//! E. `ModifyRuntime.get` at an argument that names no place is refused at load, as its `let`
//!    twin is.
//! F. The bottom type meets a bare parametric head as it meets the written one.
//! G. A spec whose contract asks for itself at a larger type is refused at its declaration.
//! H. Ranking provisions interns nothing per comparison, and an arrow nested in a parameter costs
//!    once.
//! I. A refusal names the condition that failed and no repair that moves it: a requirement no
//!    caller can say is told no slot, a ground goal no `requires`, a cycle only its condition.
//! J. The induction axiom's name: an entity with fields and an equation under it are refused.
//! K. A provider's own row is local where no candidate is more specific, in both halves of its
//!    dictionary (user, 2026-10-17).
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build, over this
//! file, the fifth and sixth reviews' and the whole `wi_tests` binary, where each moves only the
//! rows named here:
//!
//!   * reflection's builders constructing an account → [`an_account_built_through_reflection_faults`];
//!   * a query's account left to the converter → [`a_query_does_not_write_an_account`];
//!   * a data file's account loaded → [`a_data_file_does_not_hold_an_account`];
//!   * a variant read as its own sort for `Modify` → [`a_variants_place_is_a_place_of_its_sort`];
//!   * the defaulted member's call taken by its spec's default body →
//!     [`a_direct_call_of_a_defaulted_member_dispatches_as_a_generic_one`];
//!   * an arrow's part met through the subtype relation in both directions by the cover →
//!     [`a_requirement_in_scope_covers_an_arrow_only_at_its_own_binding`];
//!   * the place check skipped for an argument written inline at `get` →
//!     [`get_at_no_place_is_refused_at_load`];
//!   * the bottom type at a bare head noting nothing open →
//!     [`the_bottom_type_meets_a_bare_head_as_the_written_one`];
//!   * the growing contract left to the call →
//!     [`a_contract_asking_for_its_spec_at_a_larger_type_is_refused_at_the_spec`];
//!   * a rigid minted per comparison →
//!     [`ranking_provisions_at_a_run_time_dispatch_interns_nothing_after_the_first`];
//!   * an arrow in a parameter matching its own parameters back →
//!     [`an_arrow_nested_in_parameters_is_matched_once`] (the load runs past its budget);
//!   * the forwarded failure rendered by its hint alone, and the slot advised at a requirement no
//!     caller can say, each → [`a_failed_condition_is_named_and_no_slot_advised`];
//!   * `requires` advised at a ground goal → the same row, and
//!     `wi1102_unsatisfiable_requirement_test::the_refusal_advises_provides_and_never_the_retired_fact_spelling`;
//!   * the cycle's second repair → [`a_cycle_is_told_only_to_drop_a_condition`];
//!   * an entity with fields left alone → [`an_entity_with_fields_under_the_induction_axioms_name_is_refused`];
//!   * equations looked for under the axiom's functor alone →
//!     [`an_equation_under_the_induction_axioms_name_is_refused`].
//!
//! [`a_bundled_witness_takes_the_more_specific_instance_in_its_contract_half`] is measured against
//! the tree before this review (cef5913b), whose locality by the half of the dictionary was
//! replaced rather than kept behind a switch: its program answers 10 there.
//!
//! PASSES EITHER WAY, BY DESIGN: the controls inside the rows — an account matched and raised
//! again, a data file of the program's own sort, a variant place declared, a cover at the call's
//! own arrow, `get` at a cell, the repaired programs, run.

use anthill_core::kb::load;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::parse;
use anthill_core::persistence::term_ser;

use crate::common::{
    assert_refused_naming, fault_messages, interp_for, load_errors_of, load_kb_with,
    query_pattern_term, register_modify_handler, run_int64,
};

/// `entry` run with the `Modify` handler a program's places need.
fn run_with_modify(src: &str, entry: &str) -> Result<i64, String> {
    let mut interp = interp_for(src);
    register_modify_handler(&mut interp);
    match interp.call(entry, &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => Ok(n),
        other => Err(format!("`{entry}` did not answer an Int64: {other:?}")),
    }
}

/// `load_errors_of(src)` on a thread, failed when it does not finish: the defects these rows
/// exist for are loads that never end, which would stall the whole test binary.
fn load_errors_within(src: String, why: &str) -> Vec<String> {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(load_errors_of(&src));
    });
    rx.recv_timeout(std::time::Duration::from_secs(120))
        .unwrap_or_else(|_| panic!("{why}: the load did not end within 120 s"))
}

// ── A. the runtime's accounts ─────────────────────────────────────────────────────────────

const FORGED: &str = r#"
namespace test.r7.forge
  import anthill.prelude.{Int64, Error, List, Option, RelationFloundered}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, make_fn, term_as_entity}
  operation viaTerm() -> Int64 effects Error[Term] =
    Error.raise(make_fn("anthill.prelude.RelationFloundered.relation_floundered", nil()))
  operation viaEntity() -> Int64 effects {Error[RelationFloundered]} =
    match term_as_entity[RelationFloundered](make_fn("anthill.prelude.RelationFloundered.relation_floundered", cons(make_fn("anthill.prelude.List.nil", nil()), nil())))
      case some(e) -> Error.raise(e)
      case none -> 0
  rule byTerm(?n) :- ?n <=> viaTerm()
  rule byEntity(?n) :- ?n <=> viaEntity()
end
"#;

/// AN ACCOUNT BUILT THROUGH REFLECTION FAULTS. `make_fn` named `relation_floundered`, raised as a
/// term or turned into the entity and raised: the bridge took the raise for the runtime's own
/// account of a drain that did not decide, and the goal answered a silent residual.
///
/// FAILS with the builders constructing an account: no fault is reported.
#[test]
fn an_account_built_through_reflection_faults() {
    for goal in ["test.r7.forge.byTerm(?n)", "test.r7.forge.byEntity(?n)"] {
        let messages = fault_messages(FORGED, goal);
        assert!(
            messages.iter().any(|m| m.contains("expected a functor a program may construct")),
            "{goal}: {messages:#?}"
        );
    }
}

const ACCOUNT_IN_DATA: &str = r#"
namespace test.r7.data
  import anthill.prelude.{Int64, String, Error, List}
  import anthill.reflect.{LoadFailed}
  sort Mine
    entity mine(diagnostics: List[T = String])
  end
  sort Held
    entity Held(e: LoadFailed)
  end
  sort HeldMine
    entity HeldMine(e: Mine)
  end
  operation reraise(e: LoadFailed) -> Int64 effects Error[LoadFailed] = Error.raise(e)
  rule via(?e, ?n) :- Held(e: ?e), ?n <=> reraise(?e)
end
"#;

/// A QUERY DOES NOT WRITE AN ACCOUNT. `via(load_failed(diagnostics: nil()), ?r)` built one the
/// bridge then took for the runtime's. The program's own sort at the same place scans clean.
///
/// FAILS with the query's account left to the converter: the pattern scans clean.
#[test]
fn a_query_does_not_write_an_account() {
    let mut kb = load_kb_with(ACCOUNT_IN_DATA);
    let scan = |kb: &mut anthill_core::kb::KnowledgeBase, pattern: &str| {
        let parsed = parse::parse(&format!("fact {pattern}")).unwrap();
        let errors = load::scan_query_definitions(kb, &[&parsed]);
        load::LoadError::render_all(&errors).collect::<Vec<_>>()
    };
    let refused = scan(
        &mut kb,
        "test.r7.data.via(anthill.reflect.LoadFailed.load_failed(diagnostics: anthill.prelude.List.nil()), ?r)",
    );
    assert!(
        refused.iter().any(|m| m.contains("is an account the runtime gives of something it could not do")),
        "{refused:#?}"
    );
    let own = scan(&mut kb, "test.r7.data.HeldMine(e: test.r7.data.Mine.mine(diagnostics: anthill.prelude.List.nil()))");
    assert!(own.is_empty(), "{own:#?}");
}

/// A DATA FILE DOES NOT HOLD AN ACCOUNT. An `anthill.json` stating `Held(e: load_failed(…))`
/// loaded one, which a rule then raised as the runtime's. The program's own sort loads.
///
/// FAILS with the data file's account loaded: the file loads one fact.
#[test]
fn a_data_file_does_not_hold_an_account() {
    let mut kb = load_kb_with(ACCOUNT_IN_DATA);
    let domain = kb.intern("r7_data");
    let refused = term_ser::load_json(
        &mut kb,
        r#"{ "meta": { "entity": "test.r7.data.Held" },
             "data": [ { "e": { "load_failed": { "diagnostics": ["forged"] } } } ] }"#,
        domain,
    );
    let errors = refused.expect_err("an account in a data file is refused");
    assert!(
        errors.iter().any(|e| e.to_string().contains("a data file does not hold one")),
        "{:?}",
        errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
    let own = term_ser::load_json(
        &mut kb,
        r#"{ "meta": { "entity": "test.r7.data.HeldMine" },
             "data": [ { "e": { "mine": { "diagnostics": ["mine"] } } } ] }"#,
        domain,
    );
    assert_eq!(own.map_err(|e| e.iter().map(|e| e.to_string()).collect::<Vec<_>>()), Ok(1));
}

// ── B. a variant's place ──────────────────────────────────────────────────────────────────

/// A VARIANT'S PLACE IS A PLACE OF ITS SORT. `set(p, n)` at `p: Plain.plain`, `Plain` providing
/// `Modifiable`: the place was admitted, and the `Modify[p]` it raises was dropped as being over a
/// type no `Modify` fires on, so an operation declared pure wrote the place and read it back
/// (42), and declaring the effect was refused. Declared, it loads and runs.
///
/// FAILS with the variant read as its own sort: the pure one loads and the declared one is
/// refused.
#[test]
fn a_variants_place_is_a_place_of_its_sort() {
    let program = |row: &str, caller: &str| {
        format!(
            "namespace test.r7.place\n  import anthill.prelude.{{Int64, Unit, Modify, Modifiable}}\n  import \
             anthill.prelude.ModifyRuntime.{{set, get}}\n  sort Plain\n    provides Modifiable[T = Self]\n    \
             entity plain\n    entity other\n  end\n  operation putVariant(p: Plain.plain, n: Int64) -> Unit \
             effects {row} = set(p, n)\n  operation readVariant(p: Plain.plain) -> Int64 = get(p)\n  \
             operation run() -> Int64 effects {caller} =\n    let p: Plain.plain = plain\n    \
             let _ = putVariant(p, 42)\n    readVariant(p)\nend\n"
        )
    };
    assert_refused_naming(
        &load_errors_of(&program("{}", "{}")),
        &["undeclared effect: Modify[T = p]"],
        "the pure-looking writer",
    );
    // The caller's place is a binding: ambient places are retired (WI-20260902-JB6RS), so
    // `run` declares nothing — the write is to its own local.
    assert_eq!(run_with_modify(&program("Modify[p]", "{}"), "test.r7.place.run"), Ok(42));
}

// ── C. a direct call of a defaulted member ────────────────────────────────────────────────

const BUNDLE: &str = r#"
namespace test.r7.bundle
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
    OWN_CMP
  end
  operation useT[X](a: X, b: X) -> Int64 requires TOrd[T = X] = TOrd.cmp(a, b)
  operation generic() -> Int64 = useT(dog(1), dog(2))
  operation direct() -> Int64 = TOrd.cmp(dog(1), dog(2))
  operation twoLevel[Y](a: Y, b: Y) -> Int64 requires TOrd[T = Y] = useT(a, b)
  operation viaTwo() -> Int64 = twoLevel(dog(1), dog(2))
end
"#;

/// A DIRECT CALL OF A DEFAULTED MEMBER DISPATCHES AS A GENERIC ONE. `TOrd.cmp(dog(1), dog(2))`
/// reaches `AscW`'s provision at `Animal` only through the subtype relation, and ran `TOrd`'s
/// default body with the instance it had at `Dog`, where `useT(dog(1), dog(2))` dispatched to
/// `AscW`: with `AscW`'s own `cmp` (30) the direct call still answered the default's 20. A spec
/// with no default answers its provision's member at the subtype too (`QD.qd(dog(1))`, 6).
///
/// FAILS with the call taken by the spec's default body: the direct call answers 20 where `AscW`
/// writes 30, and `QD.qd(dog(1))` the default's 1.
#[test]
fn a_direct_call_of_a_defaulted_member_dispatches_as_a_generic_one() {
    let with_default = BUNDLE.replace("    OWN_CMP\n", "");
    let with_own = BUNDLE.replace("OWN_CMP", "operation cmp(a: Animal, b: Animal) -> Int64 = 30");
    for entry in ["generic", "direct", "viaTwo"] {
        let entry = format!("test.r7.bundle.{entry}");
        assert_eq!(run_int64(&with_default, &entry), Ok(20), "{entry}, the default body");
        assert_eq!(run_int64(&with_own, &entry), Ok(30), "{entry}, `AscW`'s own `cmp`");
    }
    let nodefault = r#"
namespace test.r7.nd
  import anthill.prelude.{Int64}
  sort QD
    sort T = ?
    operation qd(a: T) -> Int64 = 1
  end
  sort Animal
    entity animal(n: Int64)
  end
  sort Dog
    requires Animal
    entity dog(n: Int64)
  end
  sort AscW
    provides QD[T = Animal]
    operation qd(a: Animal) -> Int64 = 6
  end
  operation go() -> Int64 = QD.qd(dog(1)) * 10 + QD.qd(animal(1))
end
"#;
    assert_eq!(run_int64(nodefault, "test.r7.nd.go"), Ok(66));
}

// ── D. a cover at an arrow ────────────────────────────────────────────────────────────────

/// A REQUIREMENT IN SCOPE COVERS AN ARROW ONLY AT ITS OWN BINDING: two arrows are one binding
/// where their parameters relate and their results are the same (§5.2). `useR(f: (Dog) -> Int64)
/// requires Runner[F = (Animal) -> Int64]` passed `f` on to `Runner.run`, whose member hands it an
/// `animal`, and the run died "entity has no field n"; `requires Runner[F = (Int64) -> Dog]`
/// covered a callback returning an `Animal` the same way. A result below the requirement's is
/// another binding as well. A provision is what answers a result below its own: `Runner.run` of a
/// callback returning a `Dog` takes the provision at `(Int64) -> Animal`. The requirement at the
/// call's own arrow is the other control.
///
/// FAILS with the cover meeting the parts through the subtype relation both ways: the three load.
#[test]
fn a_requirement_in_scope_covers_an_arrow_only_at_its_own_binding() {
    let program = |provider: &str, param: &str, required: &str, callback: &str| {
        format!(
            "namespace test.r7.cover\n  import anthill.prelude.{{Int64}}\n  sort Runner\n    sort F = ?\n    \
             operation run(f: F) -> Int64\n  end\n  sort Animal\n    entity animal(n: Int64)\n  end\n  sort \
             Dog\n    requires Animal\n    entity dog(n: Int64)\n  end\n{provider}  operation useR(f: {param}) \
             -> Int64 requires Runner[F = {required}] = Runner.run(f)\n  operation go() -> Int64 = \
             useR({callback})\nend\n"
        )
    };
    let animal_runner = "  sort AnimalRunner\n    provides Runner[F = (Animal) -> Int64]\n    operation \
                         run(f: (Animal) -> Int64) -> Int64 = f(animal(n: 1))\n  end\n";
    let dog_maker = "  sort DogMaker\n    provides Runner[F = (Int64) -> Dog]\n    operation run(f: \
                     (Int64) -> Dog) -> Int64 = f(1).n\n  end\n";
    for (shape, src, carrier) in [
        (
            "a parameter",
            program(animal_runner, "(Dog) -> Int64", "(Animal) -> Int64", "lambda (d: Dog) -> d.n"),
            "Runner[F = Dog -> Int64]",
        ),
        (
            "a result above",
            program(dog_maker, "(Int64) -> Animal", "(Int64) -> Dog", "lambda (k: Int64) -> animal(n: k)"),
            "Runner[F = Int64 -> Animal]",
        ),
        (
            "a result below",
            program("", "(Int64) -> Dog", "(Int64) -> Animal", "lambda (k: Int64) -> dog(n: k)"),
            "Runner[F = Int64 -> Dog]",
        ),
    ] {
        assert_refused_naming(&load_errors_of(&src), &[carrier, "no provision of"], shape);
    }
    let dog_runner = "  sort DogRunner\n    provides Runner[F = (Dog) -> Int64]\n    operation run(f: \
                      (Dog) -> Int64) -> Int64 = f(dog(n: 7))\n  end\n";
    let own_binding = program(dog_runner, "(Dog) -> Int64", "(Dog) -> Int64", "lambda (d: Dog) -> d.n");
    assert_eq!(run_int64(&own_binding, "test.r7.cover.go"), Ok(7));
    let provided_below = "namespace test.r7.below\n  import anthill.prelude.{Int64}\n  sort Runner\n    sort F = \
                          ?\n    operation run(f: F) -> Int64\n  end\n  sort Animal\n    entity animal(n: Int64)\n  \
                          end\n  sort Dog\n    requires Animal\n    entity dog(n: Int64)\n  end\n  sort AnimalMaker\n    \
                          provides Runner[F = (Int64) -> Animal]\n    operation run(f: (Int64) -> Animal) -> Int64 = \
                          f(4).n\n  end\n  operation go() -> Int64 = Runner.run(lambda (k: Int64) -> dog(n: k))\nend\n";
    assert_eq!(run_int64(provided_below, "test.r7.below.go"), Ok(4));
}

// ── E. `get` at no place ──────────────────────────────────────────────────────────────────

/// `get` AT AN ARGUMENT THAT NAMES NO PLACE IS REFUSED AT LOAD, as its `let` twin is. A tuple
/// holding a cell, an entity holding one and an integer written inline loaded and died at run
/// time; the refusal of a placeless argument was `set`'s alone.
///
/// FAILS with the place check skipped for an argument written inline: the three load.
#[test]
fn get_at_no_place_is_refused_at_load() {
    let program = |arg: &str| {
        format!(
            "namespace test.r7.get\n  import anthill.prelude.{{Int64, Cell}}\n  import \
             anthill.prelude.ModifyRuntime.{{get}}\n  sort W\n    entity w(c: Cell[V = Int64])\n  end\n  \
             operation go() -> Int64 = get({arg})\nend\n"
        )
    };
    for arg in ["(Cell.new(1), 2)", "w(c: Cell.new(1))", "5"] {
        assert_refused_naming(
            &load_errors_of(&program(arg)),
            &["expected a place of a modifiable type"],
            arg,
        );
    }
    assert_eq!(run_with_modify(&program("Cell.new(1)"), "test.r7.get.go"), Ok(1));
}

// ── F. the bottom type at a bare head ─────────────────────────────────────────────────────

/// THE BOTTOM TYPE MEETS A BARE HEAD AS THE WRITTEN ONE. `useD([])` asks `Desc[T = Nothing]` beside
/// `IntDesc provides Desc[T = Int64]` and `Box`'s provision under `:- Desc[T = V]`, which leaves
/// `V` open there: written `Desc[T = Box[V = V]]` it was no candidate and the call loaded, written
/// `Desc[T = Box]` it tied with `IntDesc`. And `PartialEq.eq([], [])` is told the tie, where it
/// was told `unresolved: PartialEq[T = anthill.prelude.List.T]`, `List`'s own parameter.
///
/// FAILS with the bare head noting nothing open: the bare spelling is refused as a tie, and the
/// comparison names `List.T`.
#[test]
fn the_bottom_type_meets_a_bare_head_as_the_written_one() {
    for head in ["Box[V = V]", "Box"] {
        let src = format!(
            "namespace test.r7.bare\n  import anthill.prelude.{{Int64, List}}\n  sort Desc\n    sort T = ?\n    \
             operation d(x: T) -> Int64\n  end\n  sort IntDesc\n    provides Desc[T = Int64]\n    operation \
             d(x: Int64) -> Int64 = 1\n  end\n  sort Box\n    sort V = ?\n    entity box(v: V)\n    provides \
             Desc[T = {head}] :- Desc[T = V]\n    operation d(x: Box[V = V]) -> Int64 = 7\n  end\n  operation \
             useD[B](x: List[T = B]) -> Int64 requires Desc[T = B] = 3\n  operation go() -> Int64 =\n    \
             let xs = []\n    useD(xs)\nend\n"
        );
        assert_eq!(run_int64(&src, "test.r7.bare.go"), Ok(3), "{head}");
    }
    let errs = load_errors_of(
        "namespace test.r7.neq\n  import anthill.prelude.{Bool, PartialEq}\n  operation go() -> Bool =\n    \
         let xs = []\n    let ys = []\n    PartialEq.eq(xs, ys)\nend\n",
    );
    assert_refused_naming(&errs, &["ambiguous dispatch of `anthill.prelude.PartialEq.eq`"], "eq at []");
    assert!(errs.iter().all(|e| !e.contains("anthill.prelude.List.T")), "{errs:#?}");
}

// ── G. a growing contract ─────────────────────────────────────────────────────────────────

/// A CONTRACT ASKING FOR ITS SPEC AT A LARGER TYPE IS REFUSED AT THE SPEC, and the load ends. `Desc2
/// requires Desc2[T = List[T = T]]` beside a provision at every list: the provision check asked
/// `Desc2[T = List[T = List[…]]]` without end, with no call written. Refused where the spec is
/// declared, saying what to ask instead.
///
/// FAILS with the contract refused at the call alone: the load does not end.
#[test]
fn a_contract_asking_for_its_spec_at_a_larger_type_is_refused_at_the_spec() {
    let src = "namespace test.r7.grow\n  import anthill.prelude.{Int64, String, List}\n  sort Desc2\n    sort T = \
               ?\n    requires Desc2[T = List[T = T]]\n    operation d(x: T) -> String\n  end\n  sort IntD\n    \
               provides Desc2[T = Int64]\n    operation d(x: Int64) -> String = \"i\"\n  end\n  sort ListD\n    sort \
               E = ?\n    provides Desc2[T = List[T = E]]\n    operation d(x: List[T = E]) -> String = \"l\"\n  \
               end\nend\n";
    let errs = load_errors_within(src.to_string(), "the growing contract");
    assert_refused_naming(
        &errs,
        &["3:3", "asks for `test.r7.grow.Desc2` again at a larger type", "Ask for it at the spec's own parameters"],
        "the spec",
    );
}

// ── H. what ranking and matching cost ─────────────────────────────────────────────────────

/// Two provisions answer one run-time dispatch, the more specific one taken: `Box`'s at any
/// `Box`, `W1`'s at `Box[B = Int64]`.
const RANKED_AT_RUN_TIME: &str = r#"
namespace test.r7.rank
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
  operation useD[X](x: X) -> Int64 requires Desc[T = X] = Desc.d(x)
  rule r(?x, ?n) :- item(?x), ?n <=> useD(?x)
  fact item(box(inner: 0))
  fact item(box(inner: 1))
  operation go() -> Int64 = useD(box(inner: 5))
end
"#;

/// RANKING PROVISIONS READS EACH ONE'S PARAMETERS AS RIGIDS MINTED ONCE: one minted at each
/// comparison grew the store at every dispatch that ranked candidates (+4 terms a query here).
///
/// FAILS with a rigid minted per comparison: the store grows by 4 a round.
#[test]
fn ranking_provisions_at_a_run_time_dispatch_interns_nothing_after_the_first() {
    let mut kb = load_kb_with(RANKED_AT_RUN_TIME);
    let cfg = ResolveConfig::default();
    let pattern = "test.r7.rank.r(?x, ?n)";
    let warm = query_pattern_term(&mut kb, pattern);
    assert_eq!(kb.resolve(&[warm], &cfg).len(), 2, "both items must answer, or this measures nothing");
    let after_first = kb.term_store_len();
    for round in 0..4 {
        let goal = query_pattern_term(&mut kb, pattern);
        assert_eq!(kb.resolve(&[goal], &cfg).len(), 2);
        let now = kb.term_store_len();
        assert_eq!(now, after_first, "round #{round}: the store grew by {}", now as i64 - after_first as i64);
    }
    assert_eq!(
        run_int64(RANKED_AT_RUN_TIME, "test.r7.rank.go"),
        Ok(1),
        "`W1`'s provision is the more specific at `Box[B = Int64]`"
    );
}

/// AN ARROW NESTED IN PARAMETERS IS MATCHED ONCE. Each arrow in a parameter matched its own
/// parameters back the other way, inside its enclosing arrow's matching back, so the work doubled
/// at each level: depth 22 took a minute unoptimized. At depth 30 the call is met (`7`).
///
/// FAILS with an arrow in a parameter matching its own parameters back: the load does not end
/// within the budget.
#[test]
fn an_arrow_nested_in_parameters_is_matched_once() {
    let nested = |depth: usize| (0..depth).fold("Int64".to_string(), |t, _| format!("({t}) -> Int64"));
    let src = format!(
        "namespace test.r7.deep\n  import anthill.prelude.{{Int64}}\n  sort Runner\n    sort F = ?\n    operation \
         run(f: F) -> Int64\n  end\n  sort DeepRunner\n    provides Runner[F = {f}]\n    operation run(f: {f}) -> \
         Int64 = 7\n  end\n  operation go() -> Int64 = Runner.run(lambda (x: {x}) -> 1)\nend\n",
        f = nested(30),
        x = nested(29),
    );
    assert_eq!(load_errors_within(src.clone(), "depth 30"), Vec::<String>::new());
    assert_eq!(run_int64(&src, "test.r7.deep.go"), Ok(7));
}

// ── I. what a refusal says ────────────────────────────────────────────────────────────────

const APPLY: &str = "  sort Apply\n    sort F = ?\n    operation run(f: F) -> Int64\n  end\n  sort Holder\n    \
                     sort F = ?\n    requires Apply[F = F]\n    entity holder(f: F)\n    operation go(h: Self) \
                     -> Int64 = Apply.run(h.f)\n  end\n  operation run2[G](f: G) -> Int64 requires Apply[F = G] \
                     = Apply.run(f)\n  sort P\n    sort A = ?\n    requires Apply[F = A]\n    provides Apply[F \
                     = (A) -> Int64]\n    operation run(f: (A) -> Int64) -> Int64 = 3\n  end\n";

/// A FAILED CONDITION IS NAMED, AND NO SLOT ADVISED. `P provides Apply[F = (A) -> Int64]` under
/// `requires Apply[F = A]` answers `Apply[F = (String) -> Int64]` on a condition that does not
/// hold: the construction was told "no impl provides Apply" and to declare a requirement slot —
/// which loads `mk` and moves the refusal to its caller, no caller being able to say a ground
/// requirement — and the call the same without the slot; neither named `Apply[F = String]`. Both
/// now name it, and neither advises a slot or a `requires` in scope; the provision the account
/// asks for repairs both (`P`'s 3).
///
/// FAILS with the forwarded failure rendered by its hint alone (no condition named), with the
/// slot advised at a ground requirement, and with `requires` advised at a ground goal.
#[test]
fn a_failed_condition_is_named_and_no_slot_advised() {
    let program = |extra: &str, call: &str| {
        format!(
            "namespace test.r7.cond\n  import anthill.prelude.{{Int64, String}}\n{APPLY}{extra}  operation mk() -> \
             Int64 = {call}\nend\n"
        )
    };
    let str_apply = "  sort StrApply\n    provides Apply[F = String]\n    operation run(f: String) -> Int64 = \
                     2\n  end\n";
    for (shape, call) in [
        ("a construction", "Holder.go(holder(lambda (s: String) -> 1))"),
        ("a call", "run2(lambda (s: String) -> 1)"),
    ] {
        let errs = load_errors_of(&program("", call));
        assert_refused_naming(
            &errs,
            &[
                "a provision answers it, but `test.r7.cond.Apply[F = anthill.prelude.String]` beneath it does not hold",
                "declare `provides test.r7.cond.Apply[…]` on the carrier or on a witness sort",
            ],
            shape,
        );
        assert!(
            errs.iter().all(|e| !e.contains("declare a requirement slot") && !e.contains("add `requires")),
            "{shape}: {errs:#?}"
        );
        assert_eq!(run_int64(&program(str_apply, call), "test.r7.cond.mk"), Ok(3), "{shape}");
    }
}

/// A CYCLE IS TOLD ONLY TO DROP A CONDITION. `A provides Desc[T = A] :- Desc[T = B]` and its mirror
/// were also told to "provide one of the goals directly", and `W provides Desc[T = B]` written
/// beside them leaves the cycle refused as before. Dropping a condition answers (`A`'s 1).
///
/// FAILS with the cycle's second repair: the refusal advises providing a goal directly.
#[test]
fn a_cycle_is_told_only_to_drop_a_condition() {
    let program = |b_provides: &str, extra: &str| {
        format!(
            "namespace test.r7.cyc\n  import anthill.prelude.{{Int64}}\n  sort Desc\n    sort T = ?\n    operation \
             describe(x: T) -> Int64\n  end\n  sort Reader\n    sort HT = ?\n    operation probe(x: HT) -> Int64 \
             requires Desc[T = HT] = Desc.describe(x)\n  end\n  sort A\n    entity a\n    provides Desc[T = A] :- \
             Desc[T = B]\n    operation describe(x: A) -> Int64 = 1\n  end\n  sort B\n    entity b\n    {b_provides}\n    \
             operation describe(x: B) -> Int64 = 2\n  end\n{extra}  operation viaA() -> Int64 = Reader.probe(a)\nend\n"
        )
    };
    let witness = "  sort W\n    provides Desc[T = B]\n    operation describe(x: B) -> Int64 = 3\n  end\n";
    for (shape, extra) in [("the cycle", ""), ("with a witness beside it", witness)] {
        let errs = load_errors_of(&program("provides Desc[T = B] :- Desc[T = A]", extra));
        assert_refused_naming(&errs, &["construction is cyclic", "drop one of these conditions"], shape);
        assert!(errs.iter().all(|e| !e.contains("directly")), "{shape}: {errs:#?}");
    }
    assert_eq!(run_int64(&program("provides Desc[T = B]", ""), "test.r7.cyc.viaA"), Ok(1));
}

// ── J. the induction axiom's name ─────────────────────────────────────────────────────────

/// AN ENTITY WITH FIELDS UNDER THE INDUCTION AXIOM'S NAME IS REFUSED (user, 2026-10-17), naming
/// where it is declared. `entity induction(depth: Int64)` took every goal at the name: the query
/// `ProofMethod.induction(ok)` answered nothing where `induct`'s twin holds, and in a rule body it
/// was refused as a field mismatch. An entity of the name without fields loads
/// (`wi_9wvt7_review6_test::another_declaration_under_the_induction_axioms_name_loads`).
///
/// FAILS with the entity left alone: it loads.
#[test]
fn an_entity_with_fields_under_the_induction_axioms_name_is_refused() {
    let src = "namespace test.r7.inde\n  import anthill.prelude.{Int64}\n  sort ProofMethod\n    entity \
               induction(depth: Int64)\n    entity deduction\n  end\n  fact ProofMethod.induction(depth: 7)\nend\n";
    assert_refused_naming(
        &load_errors_of(src),
        &[
            "`test.r7.inde.ProofMethod.induction` names the induction axiom derived for `test.r7.inde.ProofMethod`",
            "an entity with fields declared at",
            "4:5",
        ],
        "the entity",
    );
}

/// AN EQUATION UNDER THE INDUCTION AXIOM'S NAME IS REFUSED, tagged or not, as the spec says of a
/// rule. `rule induction(?x) <=> true` in `sort Colour` is filed under the connective, or under no
/// functor at all without `@[simp]`, and the check looked under the axiom's own functor alone, so
/// it loaded where the sixth review's parent refused it.
///
/// FAILS with equations looked for under the axiom's functor alone: both load.
#[test]
fn an_equation_under_the_induction_axioms_name_is_refused() {
    for (shape, tag, at) in [("untagged", "", "6:10"), ("with @[simp]", "@[simp] ", "6:18")] {
        let src = format!(
            "namespace test.r7.indq\n  import anthill.prelude.{{Bool}}\n  sort Colour\n    entity red\n    entity \
             green\n    {tag}rule induction(?x) <=> true\n  end\nend\n"
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &[".induction` names the induction axiom derived for", "a rule declared at", at],
            shape,
        );
    }
}

// ── K. a provider's own row ───────────────────────────────────────────────────────────────

/// A BUNDLED WITNESS TAKES THE MORE SPECIFIC INSTANCE IN ITS CONTRACT HALF (user, 2026-10-17).
/// `AscW` provides `TOrd[T = Animal]` and `POrd[T = Animal]`, `TOrd requires POrd[T = T]`, `Dog`
/// (a subtype of `Animal`) provides its own `POrd`: at a `Dog`, `AscW`'s `TOrd` dictionary takes
/// `Dog`'s `POrd` for its contract, as its conditions half takes a more specific provision
/// (`wi_9wvt7_review5_test::a_refinements_condition_takes_the_refinements_provision`), and `TOrd`'s
/// default `cmp` answers from it: `Dog`'s `lt` is false, 20. The sixth review kept `AscW`'s own
/// `POrd` there, 10.
///
/// FAILS with the contract half's own row kept wherever its provision answers: 10.
#[test]
fn a_bundled_witness_takes_the_more_specific_instance_in_its_contract_half() {
    let src = BUNDLE.replace("    OWN_CMP\n", "");
    assert_eq!(run_int64(&src, "test.r7.bundle.generic"), Ok(20));
}
