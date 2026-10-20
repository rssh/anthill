//! WI-20261016-SQZPQ (proposal 071 stage (b)) — `anthill.reflect.TypePattern` and its one
//! row, `TypeValuePattern provides TypePattern[T = T] :- TypeValue[T = T]`, whose `admits`
//! asks the one subtype test `type_admits` (`kb/typing/type_pattern.rs`). Nothing reads
//! `TypePattern` yet.
//!
//! Every `admits` row below calls it THROUGH A REQUIREMENT SLOT — `admitsAt[P](t) requires
//! TypePattern[T = P]` — or at a ground instance, so the answer comes from the row's member
//! reading `T` as a value under the row's own condition.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ──────────────────────────────────
//!
//! On the parent tree a row naming `TypePattern`, `TypeValuePattern` or `type_admits` fails
//! to load, the names being new. Rows that load there: `a_question_mark_argument_is_an_open_slot`
//! dies at run time, "unknown operation: _", in every op but its control `written`;
//! `a_sorts_own_type_value_is_held_to_no_contract_of_it` is refused at load, as each of its
//! sorts overriding `TypeValue.type_value`; `an_open_slot_of_a_programs_spec_gets_the_left_out_account`
//! loads its refused programs clean and dies at run time; and `type_value_gains_no_member`
//! passes, by design — it is what the row broke while it stood on `TypeValue`.
//!
//! On this tree, each part out alone (MEASURED with a temporary switch per part):
//!
//! * The derived-only check (`written_type_pattern_provisions`):
//!   `a_written_type_pattern_row_is_refused`, whose first program then loads clean; its
//!   binding half alone: the same row's `other_binding`.
//! * `?` left out where the typer types a type value: `a_question_mark_argument_is_an_open_slot`
//!   and the variance row's two `?` cases die "unknown operation: _"; the `?_` mentions
//!   counted over the operation: the `?` row's tie assertions, nested and apart.
//! * An operation whose answer is its dictionary kept on its builtin:
//!   `a_sorts_own_type_value_answers_no_type_read` — `resolve_op_target` and
//!   `resolve_at_goal` each fail one of its ops, as its doc says — and the override and
//!   member checks reading it: `a_sorts_own_type_value_is_held_to_no_contract_of_it`.
//! * The refusal of a slot call at a type with an open slot:
//!   `a_slot_call_at_an_open_slot_is_refused_at_load`, which then loads clean; its account:
//!   that row and `an_open_slot_of_a_programs_spec_gets_the_left_out_account`.
//! * The resolver's advice for a goal that is not ground: `a_ground_call_at_an_open_slot_advises_both_repairs`.
//! * `TypePattern` among the library's specs (`library_instances`):
//!   `a_refused_pattern_advises_no_row`.
//! * The lowered read's bracket, keyed by the bare parameter: `a_body_typed_again_by_a_later_load_answers`
//!   (the bracket) and `a_lowered_read_typed_again_by_a_rewrite_answers` (the keys).
//! * The predicate: each row of `the_test_reads_variance_open_slots_and_the_bottom_type`,
//!   `an_arrow_is_the_function_it_is`, `a_refining_sort_is_each_instance_its_clauses_give_it`
//!   and `what_the_test_does_not_judge_is_an_error` says which arm it holds; each arm answered
//!   otherwise fails one of them.

use anthill_core::eval::value::Value;

/// The harness: the slot every `admits` row dispatches through, and the sorts the rows
/// compare.
fn program(ops: &str) -> String {
    format!(
        r#"
namespace wisqzpq.tp
  import anthill.prelude.{{Int64, Type, Bool, Option, Result, Stream, Nothing, Function}}
  import anthill.prelude.Console.{{ConsoleOutput}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.reflect.{{TypeValue, TypePattern, TypeValuePattern, type_admits, term_as_sort, as_term}}
  import anthill.reflect.typing.{{Contravariant}}
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  sort IoError
    entity io_error
  end
  sort FileNotFound
    requires IoError
    entity file_not_found
  end
  sort Animal
    entity animal
  end
  sort Cat
    requires Animal
    entity cat
  end
  sort Bag
    sort T = ?
  end
  sort Sink
    sort T = ?
  end
  fact Contravariant(sort: Sink, param: T)
  sort Box
    sort V = ?
  end
  sort Wide
    sort W = ?
  end
  sort Narrow
    requires Wide[W = Int64]
  end
  sort Narrow2
    sort Q = ?
    requires Wide[W = Q]
  end
  sort Narrower
    requires Narrow2[Q = String]
  end
  sort NestedQ
    sort Q = ?
    requires Wide[W = Option[T = Q]]
  end
  sort Pr
    sort L = ?
    entity left(l: L)
  end
  entity Point(x: Int64)
  sort Crate
    sort V = ?
    entity crate(V: V)
  end
  sort IntFn = (Int64) -> Int64
  sort CatOut = (Int64) -> Cat
  sort AnimalIn = (Animal) -> Int64
  sort CatIn = (Cat) -> Int64
  sort Forger
    entity forger
    operation type_value() -> Type = Animal
  end
  sort Forger2
    entity forger2
    operation type_value(n: Int64) -> Bool = true
  end
  sort Shape
    operation area(s: Shape) -> Int64
  end
  sort Square
    entity square
    provides Shape
    operation area(s: Square) -> Int64 = 1
  end
  sort D
    operation admitsAt[P](t: Type) -> Bool requires TypePattern[T = P] =
      TypePattern.admits[T = P](t)
{ops}
  end
end
"#
    )
}

use crate::common::load_errors_of as refusals;

/// Run each `(op, want)` of a program that must load clean, every op `(n: Int64) -> Bool`.
/// `interp_for` fails the test with the load's errors, listed.
fn assert_answers(src: &str, rows: &[(&str, bool)]) {
    assert_ops_answer(&mut crate::common::interp_for(src), rows);
}

fn assert_ops_answer(interp: &mut anthill_core::eval::Interpreter, rows: &[(&str, bool)]) {
    for (op, want) in rows {
        match interp.call(&format!("wisqzpq.tp.D.{op}"), &[Value::Int(0)]) {
            Ok(Value::Bool(got)) => assert_eq!(got, *want, "{op}"),
            other => panic!("{op}: expected a Bool, got {other:?}"),
        }
    }
}

/// Each `(op, says)` of a program that must load clean fails its run with an error saying
/// `says`.
fn assert_runs_fail(src: &str, rows: &[(&str, &str)]) {
    let mut interp = crate::common::interp_for(src);
    for (op, says) in rows {
        match interp.call(&format!("wisqzpq.tp.D.{op}"), &[Value::Int(0)]) {
            Err(e) => {
                let err = e.to_string();
                assert!(err.contains(says), "{op}: expected an error saying `{says}`, got: {err}");
            }
            other => panic!("{op}: expected the run to fail, got {other:?}"),
        }
    }
}

/// THE ACCEPTANCE. `admits` driven through a slot: a pattern at `Boom[Reason = String]`
/// admits that type and not `Boom[Reason = Int64]`, and a pattern at `IoError` admits
/// `FileNotFound` (`sort FileNotFound requires IoError`) and not the other way round. At a
/// ground instance the evidence is resolved where the call is written, the same row.
#[test]
fn admits_through_a_slot() {
    let src = program(
        r#"    operation sameReason(n: Int64) -> Bool =
      admitsAt[P = Boom[Reason = String]](Boom[Reason = String])
    operation otherReason(n: Int64) -> Bool =
      admitsAt[P = Boom[Reason = String]](Boom[Reason = Int64])
    operation subsort(n: Int64) -> Bool = admitsAt[P = IoError](FileNotFound)
    operation supersort(n: Int64) -> Bool = admitsAt[P = FileNotFound](IoError)
    operation ground(n: Int64) -> Bool =
      TypePattern.admits[T = Boom[Reason = String]](Boom[Reason = String])
    operation groundOther(n: Int64) -> Bool =
      TypePattern.admits[T = Boom[Reason = String]](Boom[Reason = Int64])"#,
    );
    assert_answers(
        &src,
        &[
            ("sameReason", true),
            ("otherReason", false),
            ("subsort", true),
            ("supersort", false),
            ("ground", true),
            ("groundOther", false),
        ],
    );
}

/// A BODY TYPED A SECOND TIME. When nothing is sealed a later load types every body again,
/// the library's too, and the row's `T` read is typed there as the call it was lowered to,
/// `TypeValue.type_value[T = T]()`. NOT THE RECIPE, BY NAME: every recipe seals the library,
/// and a sealed body is typed once — this KB is the library loaded unsealed.
/// BACK-OUT: the lowered call made without its bracket, the later load is refused, "names
/// no instance of `anthill.reflect.TypeValue`" at the row's body (MEASURED).
#[test]
fn a_body_typed_again_by_a_later_load_answers() {
    let mut kb = crate::common::load_unsealed(&[]);
    let src = program(
        r#"    operation sameReason(n: Int64) -> Bool =
      admitsAt[P = Boom[Reason = String]](Boom[Reason = String])
    operation otherReason(n: Int64) -> Bool =
      admitsAt[P = Boom[Reason = String]](Boom[Reason = Int64])
    operation subsort(n: Int64) -> Bool = admitsAt[P = IoError](FileNotFound)"#,
    );
    crate::common::expect_loaded(crate::common::load_in_a_later_call(
        &mut kb,
        &src,
        anthill_core::kb::load::LoadOptions::default(),
    ));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    assert_ops_answer(
        &mut interp,
        &[("sameReason", true), ("otherReason", false), ("subsort", true)],
    );
}

/// A GENERIC CALLER: the pattern's evidence forwarded through a `requires TypePattern`, and
/// built from a `requires TypeValue` alone — the row's condition answered by the caller's
/// own slot, which is the route a generic boundary takes.
#[test]
fn a_generic_caller_forwards_or_builds_the_pattern() {
    let src = program(
        r#"    operation forward[Q](t: Type) -> Bool requires TypePattern[T = Q] = admitsAt[P = Q](t)
    operation fromValue[Q](t: Type) -> Bool requires TypeValue[T = Q] =
      TypePattern.admits[T = Q](t)
    operation forwarded(n: Int64) -> Bool = forward[Q = Animal](Cat)
    operation forwardedNot(n: Int64) -> Bool = forward[Q = Cat](Animal)
    operation built(n: Int64) -> Bool = fromValue[Q = Option[T = Animal]](Option[T = Cat])
    operation builtNot(n: Int64) -> Bool = fromValue[Q = Bag[T = Animal]](Bag[T = Cat])"#,
    );
    assert_answers(
        &src,
        &[
            ("forwarded", true),
            ("forwardedNot", false),
            ("built", true),
            ("builtNot", false),
        ],
    );
}

/// THE ONE SUBTYPE TEST, asked directly: by the declared variance of each parameter —
/// `Option` covariant, `Bag` with no fact invariant, `Sink` contravariant by the program's
/// own fact — nested, with the bottom type, and with an open slot on either side. A tuple
/// is admitted by no sort. A variant's arguments are its sort's, compared as the sort's are,
/// and a variant is below its own sort at the same arguments. An effect row is admitted by
/// the same row (`sameRow`).
///
/// AN ARGUMENT THAT DECIDES IS NOT UNDONE BY ONE THAT IS NOT JUDGED: `Result` declares `E`
/// before `T`, and `decidedFirst` / `decidedSecond` hold the tuple pair at either place.
/// BACK-OUT: with the first unjudged argument returned, `decidedSecond` errors "both named
/// tuples" while `decidedFirst` answers `no`; with a variant read at its own
/// (empty) parameter list, `variantArgs` and `variantArgsInvariant` answer `yes`; with the
/// variant-to-its-sort edge read as `requires`, `variantBelowItsSort` errors.
#[test]
fn the_test_reads_variance_open_slots_and_the_bottom_type() {
    let src = program(
        r#"    operation covariant(n: Int64) -> Bool = type_admits(Option[T = Animal], Option[T = Cat])
    operation covariantNot(n: Int64) -> Bool = type_admits(Option[T = Cat], Option[T = Animal])
    operation invariant(n: Int64) -> Bool = type_admits(Bag[T = Animal], Bag[T = Cat])
    operation invariantSame(n: Int64) -> Bool = type_admits(Bag[T = Cat], Bag[T = Cat])
    operation contravariant(n: Int64) -> Bool = type_admits(Sink[T = Cat], Sink[T = Animal])
    operation contravariantNot(n: Int64) -> Bool = type_admits(Sink[T = Animal], Sink[T = Cat])
    operation nested(n: Int64) -> Bool =
      type_admits(Option[T = Option[T = Animal]], Option[T = Option[T = Cat]])
    operation bottom(n: Int64) -> Bool = type_admits(Animal, Nothing)
    operation bottomNot(n: Int64) -> Bool = type_admits(Nothing, Animal)
    operation openPattern(n: Int64) -> Bool = type_admits(Boom, Boom[Reason = Int64])
    operation openType(n: Int64) -> Bool = type_admits(Boom[Reason = Int64], Boom)
    operation openWritten(n: Int64) -> Bool = type_admits(Boom[Reason = ?], Boom[Reason = Int64])
    operation openWrittenType(n: Int64) -> Bool = type_admits(Boom[Reason = Int64], Boom[?])
    operation refined(n: Int64) -> Bool = type_admits(Wide, Narrow)
    operation tupleNot(n: Int64) -> Bool = type_admits(Option[T = Animal], Option[T = (a: Int64)])
    operation tupleInvariantNot(n: Int64) -> Bool = type_admits(Box[V = Animal], Box[V = (a: Int64)])
    operation decidedFirst(n: Int64) -> Bool =
      type_admits(Result[E = Cat, T = (a: Int64)], Result[E = Animal, T = (a: Int64)])
    operation decidedSecond(n: Int64) -> Bool =
      type_admits(Result[E = (a: Int64), T = Cat], Result[E = (a: Int64), T = Animal])
    operation variantArgs(n: Int64) -> Bool =
      type_admits(Option[T = Option.some[T = Int64]], Option[T = Option.some[T = String]])
    operation variantArgsSame(n: Int64) -> Bool =
      type_admits(Bag[T = Pr.left[L = Int64]], Bag[T = Pr.left[L = Int64]])
    operation variantArgsInvariant(n: Int64) -> Bool =
      type_admits(Bag[T = Pr.left[L = Int64]], Bag[T = Pr.left[L = String]])
    operation variantBelowItsSort(n: Int64) -> Bool =
      type_admits(Option[T = Option[T = Animal]], Option[T = Option.some[T = Cat]])
    operation sortNotBelowItsVariant(n: Int64) -> Bool =
      type_admits(Option[T = Option.some[T = Cat]], Option[T = Option[T = Cat]])
    operation sameRow(n: Int64) -> Bool =
      type_admits(Box[V = Stream[T = Int64, E = {}]], Box[V = Stream[T = Int64, E = {}]])"#,
    );
    assert_answers(
        &src,
        &[
            ("covariant", true),
            ("covariantNot", false),
            ("invariant", false),
            ("invariantSame", true),
            ("contravariant", true),
            ("contravariantNot", false),
            ("nested", true),
            ("bottom", true),
            ("bottomNot", false),
            ("openPattern", true),
            ("openType", true),
            ("openWritten", true),
            ("openWrittenType", true),
            ("refined", true),
            ("tupleNot", false),
            ("tupleInvariantNot", false),
            ("decidedFirst", false),
            ("decidedSecond", false),
            ("variantArgs", false),
            ("variantArgsSame", true),
            ("variantArgsInvariant", false),
            ("variantBelowItsSort", true),
            ("sortNotBelowItsVariant", false),
            ("sameRow", true),
        ],
    );
}

/// A TYPE ARGUMENT WRITTEN `?` IS A SLOT LEFT UNWRITTEN (kernel-language.md §8.1) in a type
/// written in an operation body, as in a type position — the spelling of an open slot a
/// pattern is written with. Named or positional, a positional beside it still binding the
/// parameter it binds. It is left out where the typer types the type value, so the typed
/// body every later reader takes holds the one type. BACK-OUT: evaluated as an expression,
/// each `?` was a call of `_`, and every op here but `written`, the control, died "unknown
/// operation: _" on a program that loaded clean.
#[test]
fn a_question_mark_argument_is_an_open_slot() {
    let src = r#"
namespace wisqzpq.q
  import anthill.prelude.{Int64, String, Type}
  sort Boom
    sort Reason = ?
  end
  sort Duo
    sort L = ?
    sort R = ?
  end
  sort D
    operation named(n: Int64) -> Type = Boom[Reason = ?]
    operation positional(n: Int64) -> Type = Boom[?]
    operation namedBesidePositional(n: Int64) -> Type = Duo[L = ?, Int64]
    operation positionalFirst(n: Int64) -> Type = Duo[?, Int64]
    operation positionalSecond(n: Int64) -> Type = Duo[Int64, ?]
    operation both(n: Int64) -> Type = Duo[?, ?]
    operation wildcardOnce(n: Int64) -> Type = Boom[Reason = ?_]
    operation written(n: Int64) -> Type = Duo[Int64, String]
  end
end
"#;
    let mut interp = crate::common::interp_for(src);
    for (op, want) in [
        ("named", "Boom"),
        ("positional", "Boom"),
        ("namedBesidePositional", "Duo[R = Int64]"),
        ("positionalFirst", "Duo[R = Int64]"),
        ("positionalSecond", "Duo[L = Int64]"),
        ("both", "Duo"),
        ("wildcardOnce", "Boom"),
        ("written", "Duo[L = Int64, R = String]"),
    ] {
        match interp.call(&format!("wisqzpq.q.D.{op}"), &[Value::Int(0)]) {
            Ok(v) => assert_eq!(
                anthill_core::kb::typing::type_display_name_value(interp.kb(), &v),
                want,
                "{op}"
            ),
            other => panic!("{op}: expected a type, got {other:?}"),
        }
    }
    // A `?_` WRITTEN AGAIN IS NO OPEN SLOT: the parser reads it as one variable over the
    // operation's declaration, tying the places, which a value of a type cannot hold, and it
    // is refused where it is written — in one type, nested in two, in two types of one body,
    // in the signature and the body. Written once it is a `?` (`wildcardOnce` above).
    // BACK-OUT: with the mentions counted among one type value's arguments alone, the nested
    // and the apart ties were each left out, the tie dropped in silence, and `Duo[L =
    // Option[T = ?_], R = Option[T = ?_]]` built `Duo(L: Option, R: Option)`. A NAMED
    // variable stays the frame's variable of that name, read when the body runs —
    // `wi_q0093_type_value_occurrence_matrix_test`'s `wrap(t: Type) = Cell[V = ?t]` reads its
    // parameter, and fails if a named variable is read as a slot.
    for (from, to) in [
        ("Duo[Int64, String]", "Duo[L = ?_, R = ?_]"),
        ("Duo[Int64, String]", "Duo[?_, ?_]"),
        ("Duo[Int64, String]", "Duo[L = Boom[Reason = ?_], R = Boom[Reason = ?_]]"),
        ("Duo[Int64, String]", "Duo[L = ?_, R = Boom[Reason = ?_]]"),
        (
            "operation written(n: Int64) -> Type = Duo[Int64, String]",
            "operation written(n: Int64) -> Type =\n      let a = Boom[Reason = ?_]\n      Boom[Reason = ?_]",
        ),
        (
            "operation written(n: Int64) -> Type = Duo[Int64, String]",
            "operation written(n: Duo[L = ?_, R = Int64]) -> Type = Boom[Reason = ?_]",
        ),
    ] {
        let tied = src.replace(from, to);
        assert_ne!(tied, src, "the substitution `{to}` must apply");
        let errs = refusals(&tied);
        assert!(
            errs.iter().any(|e| e.contains("is given `?_`, in a type an operation body builds, and the operation writes that `?_` again")),
            "`{to}` in an operation must be refused for its tie; got {errs:?}"
        );
    }
}

/// A SORT'S OWN OPERATION NAMED `type_value` ANSWERS NO TYPE READ. Every `TypeValue`
/// instance is the loader's and none may be written, so the builtin answers it at every
/// provider; the sort's operation stays its own, callable as such. BACK-OUT: with the
/// carrier's member taken where a dictionary is dispatched (`resolve_op_target`), `forged`
/// and `viaSlot` answer `yes` — `Forger.type_value()` names `Animal`, and the pattern at
/// `Forger` admits what it names; with it taken where the typer pins a ground call
/// (`resolve_at_goal`), `directRead` dies "expected 1 args, got 0".
#[test]
fn a_sorts_own_type_value_answers_no_type_read() {
    let src = program(
        r#"    operation forged(n: Int64) -> Bool = TypePattern.admits[T = Forger](Animal)
    operation own(n: Int64) -> Bool = TypePattern.admits[T = Forger](Forger)
    operation viaSlot(n: Int64) -> Bool = admitsAt[P = Forger](Animal)
    operation otherSignature(n: Int64) -> Bool = TypePattern.admits[T = Forger2](Forger2)
    operation directRead(n: Int64) -> Bool =
      type_admits(TypeValue.type_value[T = Forger2](), Forger2)
    operation stillItsOwn(n: Int64) -> Bool = Forger2.type_value(1)"#,
    );
    assert_answers(
        &src,
        &[
            ("forged", false),
            ("own", true),
            ("viaSlot", false),
            ("otherSignature", true),
            ("directRead", true),
            ("stillItsOwn", true),
        ],
    );
}

/// A REQUIREMENT AT A TYPE WITH AN OPEN SLOT is answered by a provision that leaves the slot
/// open, and not by one at an instance (kernel-language.md §8.1); the library's specs derive
/// no row at an open slot. A call naming such a type — `[P = Boom]` over `sort Boom { sort
/// Reason = ? }`, or `[P = Boom[Reason = ?]]` — is refused where it is written, with the
/// account the slot inferred and left out gets: the library spec's own repair, a sort named
/// with every type argument. BACK-OUT: no provision answered and nothing said so; the program
/// loaded clean and the callee's read died at run time, "requirement param
/// `__req_typepattern` not bound in caller frame"; with the account of the arm alone, the
/// refusal said no provision answers any open slot, which a program's spec contradicts
/// (`an_open_slot_of_a_programs_spec_gets_the_left_out_account`).
#[test]
fn a_slot_call_at_an_open_slot_is_refused_at_load() {
    for (call, says) in [
        (
            "open(n: Int64) -> Bool = admitsAt[P = Boom](Boom[Reason = Int64])",
            "no row of `anthill.reflect.TypePattern` answers here, and none may be written",
        ),
        (
            "open(n: Int64) -> Bool = admitsAt[P = Boom[Reason = ?]](Boom[Reason = Int64])",
            "no row of `anthill.reflect.TypePattern` answers here, and none may be written",
        ),
        (
            "open(n: Int64) -> Type = tvAt[P = Boom](0)",
            "no row of `anthill.reflect.TypeValue` answers here, and none may be written",
        ),
    ] {
        let src = program(&format!(
            "    operation tvAt[P](n: Int64) -> Type requires TypeValue[T = P] = TypeValue.type_value[T = P]()\n    operation {call}"
        ));
        let errs = refusals(&src);
        assert!(
            errs.iter()
                .any(|e| e.contains(says) && e.contains("every type argument of it written")),
            "`{call}` must be refused at load for its open slot, saying `{says}`; got {errs:?}"
        );
    }
}

/// A PROGRAM'S SPEC AT AN OPEN SLOT: the account says what its own provisions do there. With
/// a provision at one instance of the sort only, that a row of it answers at none of these
/// bindings; with none, that the sort provides no row, which a provision leaving the slot
/// open would be — and that one answers the call (`answered`). BACK-OUT: the program loaded
/// clean on the parent tree and died at run time, and with only `Show[T = Boom[Reason =
/// String]]` it answered at `Boom` with that instance's member, the bracket not read.
#[test]
fn an_open_slot_of_a_programs_spec_gets_the_left_out_account() {
    let src = |provision: &str| {
        format!(
            r#"
namespace wisqzpq.open
  import anthill.prelude.{{Int64, String}}
  sort Show
    sort T = ?
    operation tag() -> Int64
  end
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  sort W1
{provision}
  end
  sort D
    operation tagAt[P](n: Int64) -> Int64 requires Show[T = P] = Show.tag[T = P]()
    operation atTheOpenSlot(n: Int64) -> Int64 = tagAt[P = Boom](0)
  end
end
"#
        )
    };
    let at_an_instance = src(
        "    provides Show[T = Boom[Reason = String]] where\n      operation tag() -> Int64 = 1\n    end",
    );
    let errs = refusals(&at_an_instance);
    assert!(
        errs.iter().any(|e| e.contains("does provide `wisqzpq.open.Show`, but no row of it answers at these bindings")),
        "a provision at an instance answers no open slot; got {errs:?}"
    );
    let none = src("");
    let errs = refusals(&none);
    assert!(
        errs.iter().any(|e| e.contains("`wisqzpq.open.Boom` provides no `wisqzpq.open.Show`")),
        "with no provision the account names the one to write; got {errs:?}"
    );
    let answered = src(
        "    provides Show[T = Boom] where\n      operation tag() -> Int64 = 2\n    end",
    );
    let mut interp = crate::common::interp_for(&answered);
    match interp.call("wisqzpq.open.D.atTheOpenSlot", &[Value::Int(0)]) {
        Ok(Value::Int(2)) => {}
        other => panic!("the provision at the open slot answers it; got {other:?}"),
    }
}

/// THE RESOLVER'S ADVICE FOR A GOAL THAT IS NOT GROUND names both things its open part can
/// be: a ground call naming a type with a slot open asks `TypeValue[T = Boom.Reason]`, whose
/// `Boom.Reason` no caller holds. BACK-OUT: the advice was a `requires` in scope alone, which
/// names a parameter no caller has.
#[test]
fn a_ground_call_at_an_open_slot_advises_both_repairs() {
    let src = program(
        "    operation ground(n: Int64) -> Bool = TypePattern.admits[T = Boom](Boom[Reason = Int64])",
    );
    let errs = refusals(&src);
    assert!(
        errs.iter().any(|e| e.contains(
            "where it holds a parameter of the caller, add `requires anthill.reflect.TypeValue[…]` in scope to take it from the caller, and where it holds a slot a type the call states leaves open, write every type argument of that type"
        )),
        "the advice must name both repairs; got {errs:?}"
    );
}

/// A PARAMETER OF THE CALLEE LEFT UNBOUND IS NO TYPE THE CALL STATES. At a library spec no
/// slot of the frame is filled at run time, every instance being derived at a type, and the
/// call is refused with the unconstrained element's account — `Holder.tv(0)`, `Catch.catches(…)`
/// — as a sort's own clause is; the receiver written in full answers (`Catch[P = IoError]`). At
/// a program's spec the provider facts complete the element to one provision: `Box.tagOf2(0)`
/// answers through `Animal`'s. BACK-OUT: with the open-slot arm taking every open element,
/// `Box.tagOf2(0)` was refused with the open-slot account; with no arm for an unbound
/// parameter, the two library calls loaded clean and died at run time, "requirement param
/// not bound in caller frame". `completed` PASSES ON THE PARENT TREE, BY DESIGN.
#[test]
fn a_parameter_left_unbound_is_no_open_type() {
    let src = |ops: &str| {
        format!(
            r#"
namespace wisqzpq.tp
  import anthill.prelude.{{Int64, Type, Bool}}
  import anthill.reflect.{{TypeValue, TypePattern}}
  sort Tag
    sort T = ?
    operation tag() -> Int64
  end
  sort Animal
    entity animal
    provides Tag[T = Animal] where
      operation tag() -> Int64 = 7
    end
  end
  sort IoError
    entity io_error
  end
  sort FileNotFound
    requires IoError
    entity file_not_found
  end
  sort Box
    sort V = ?
    entity box(v: V)
    operation tagOf2(n: Int64) -> Int64 requires Tag[T = V] = Tag.tag[T = V]()
  end
  sort Holder
    sort V = ?
    entity holder(v: V)
    operation tv(n: Int64) -> Type requires TypeValue[T = V] = V
  end
  sort Catch
    sort P = ?
    operation catches(t: Type) -> Bool requires TypePattern[T = P] = TypePattern.admits[T = P](t)
  end
  sort D
{ops}
  end
end
"#
        )
    };
    let mut interp = crate::common::interp_for(&src(
        "    operation completed(n: Int64) -> Int64 = Box.tagOf2(0)\n    operation stated(n: Int64) -> Bool = Catch[P = IoError].catches(FileNotFound)",
    ));
    match interp.call("wisqzpq.tp.D.completed", &[Value::Int(0)]) {
        Ok(Value::Int(7)) => {}
        other => panic!("the one provider completes `Box.V`; got {other:?}"),
    }
    match interp.call("wisqzpq.tp.D.stated", &[Value::Int(0)]) {
        Ok(Value::Bool(true)) => {}
        other => panic!("the receiver written in full answers; got {other:?}"),
    }
    for (call, element) in [
        ("operation library(n: Int64) -> Type = Holder.tv(0)", "`T = wisqzpq.tp.Holder.V`"),
        ("operation pattern(n: Int64) -> Bool = Catch.catches(FileNotFound)", "`T = wisqzpq.tp.Catch.P`"),
    ] {
        let errs = refusals(&src(&format!("    {call}")));
        assert!(
            errs.iter().any(|e| e.contains(&format!("element {element} is unconstrained at this call site"))),
            "`{call}` must be refused for its unbound element; got {errs:?}"
        );
    }
}

/// A REFUSED `TypePattern` REQUIREMENT ADVISES NO ROW TO WRITE: its one row is
/// `TypeValuePattern`'s, and a written one is refused. BACK-OUT: with `TypePattern` not among the
/// library's specs (`library_instances`), the refusal advised "declare `provides
/// anthill.reflect.TypePattern[T = Shape]` … or on a witness sort", which the derived-only
/// check then refused.
#[test]
fn a_refused_pattern_advises_no_row() {
    let src = program("    operation shape(n: Int64) -> Bool = admitsAt[P = Shape](Square)");
    let errs = refusals(&src);
    assert!(
        errs.iter().any(|e| e.contains("no row of `anthill.reflect.TypePattern` answers here")),
        "the refusal must say no row may be written; got {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("declare `provides anthill.reflect.TypePattern")),
        "the refusal must not advise writing a row; got {errs:?}"
    );
}

/// WHAT THE TEST DOES NOT JUDGE IS AN ERROR, never an answer: two tuples, two effect rows
/// that are not one row, a data value handed in as a `Type` — a constructor's, a free-standing
/// entity's whose head is its own sort, and a constructor's whose field is keyed like its
/// sort's parameter — and two types nested deeper than the walk descends. BACK-OUT: with the
/// head read alone, `entityValue` answered `yes`, the value read as the type `Point`; with
/// the arguments' keys read alone, `fieldNamedLikeParam` answered `yes`; with no bound,
/// `deep` overflowed the stack (MEASURED at 5 500 levels, here 600).
#[test]
fn what_the_test_does_not_judge_is_an_error() {
    let src = program(
        r#"    operation twoTuples(n: Int64) -> Bool =
      type_admits(Box[V = (a: Int64)], Box[V = (a: Int64)])
    operation twoRows(n: Int64) -> Bool =
      type_admits(Box[V = Stream[T = Int64, E = {}]], Box[V = Stream[T = Int64, E = {ConsoleOutput}]])
    operation dataValue(n: Int64) -> Bool =
      match term_as_sort(as_term(boom(reason: "s")))
        case some(t) -> type_admits(Boom, t)
        case none() -> false
    operation entityValue(n: Int64) -> Bool =
      match term_as_sort(as_term(Point(x: 3)))
        case some(t) -> type_admits(Point[], t)
        case none() -> false
    operation fieldNamedLikeParam(n: Int64) -> Bool =
      match term_as_sort(as_term(crate(V: 3)))
        case some(t) -> type_admits(Crate, t)
        case none() -> false
    operation wrap(t: Type, n: Int64) -> Type = match n
      case 0 -> t
      case _ -> wrap(Box[V = ?t], n - 1)
    operation deep(n: Int64) -> Bool = type_admits(wrap(Int64, 600), wrap(Int64, 600))"#,
    );
    assert_runs_fail(
        &src,
        &[
            ("twoTuples", "are both named tuples"),
            ("twoRows", "are two effect rows"),
            ("dataValue", "is a data value, not a type"),
            ("entityValue", "is a data value, not a type"),
            ("fieldNamedLikeParam", "is a data value, not a type"),
            ("deep", "nest deeper than 512 levels"),
        ],
    );
}

/// AN ARROW IS THE `Function` IT IS (kernel-language.md §4.4: `(A) -> B` is `Function[A, B,
/// E = {}]`), compared as that application by `Function`'s declared variance — contravariant
/// in its parameter, covariant in its result and row — and the empty row is one row, written
/// `{}` or reported `Nothing` by a `TypeValue` (`throughTheRow`). BACK-OUT: with an arrow a
/// former of its own, every `Function` pattern answered `no` of an arrow, and `selfAdmits`
/// errored as two formers.
#[test]
fn an_arrow_is_the_function_it_is() {
    let src = program(
        r#"    operation applied(n: Int64) -> Bool = type_admits(Function[A = Int64, B = Int64], IntFn)
    operation bare(n: Int64) -> Bool = type_admits(Function, IntFn)
    operation selfAdmits(n: Int64) -> Bool = type_admits(IntFn, IntFn)
    operation result(n: Int64) -> Bool = type_admits(Function[A = Int64, B = Animal], CatOut)
    operation param(n: Int64) -> Bool = type_admits(Function[A = Cat, B = Int64], AnimalIn)
    operation paramNot(n: Int64) -> Bool = type_admits(Function[A = Animal, B = Int64], CatIn)
    operation emptyRow(n: Int64) -> Bool = type_admits(Function[A = Int64, B = Int64, E = {}], IntFn)
    operation throughTheRow(n: Int64) -> Bool =
      TypePattern.admits[T = Function[A = Int64, B = Int64, E = {}]](IntFn)"#,
    );
    assert_answers(
        &src,
        &[
            ("applied", true),
            ("bare", true),
            ("selfAdmits", true),
            ("result", true),
            ("param", true),
            ("paramNot", false),
            ("emptyRow", true),
            ("throughTheRow", true),
        ],
    );
}

/// A SORT THAT REFINES ANOTHER THROUGH `requires` IS EACH INSTANCE ITS CLAUSES GIVE IT, its
/// own arguments put for the parameters a clause names, clause by clause: `sort Narrow
/// requires Wide[W = Int64]` is admitted at `Wide[W = Int64]` and not at `Wide[W = String]`;
/// `Narrow2[Q = String]` at `Wide[W = String]`, through `requires Wide[W = Q]`; `Narrower`
/// two clauses down; a parameter left out an open slot (`openParam`); nested in an argument
/// (`nested`). BACK-OUT: with the clauses not read, every pattern writing `W` was an error,
/// "writes `W` of `Wide`, which `Narrow` reaches only through `requires`".
#[test]
fn a_refining_sort_is_each_instance_its_clauses_give_it() {
    let src = program(
        r#"    operation clause(n: Int64) -> Bool = type_admits(Wide[W = Int64], Narrow)
    operation clauseNot(n: Int64) -> Bool = type_admits(Wide[W = String], Narrow)
    operation clauseOpen(n: Int64) -> Bool = type_admits(Wide, Narrow)
    operation param(n: Int64) -> Bool = type_admits(Wide[W = String], Narrow2[Q = String])
    operation paramNot(n: Int64) -> Bool = type_admits(Wide[W = Int64], Narrow2[Q = String])
    operation openParam(n: Int64) -> Bool = type_admits(Wide[W = Int64], Narrow2)
    operation twoDown(n: Int64) -> Bool = type_admits(Wide[W = String], Narrower)
    operation twoDownNot(n: Int64) -> Bool = type_admits(Wide[W = Int64], Narrower)
    operation nested(n: Int64) -> Bool = type_admits(Wide[W = Option[T = Animal]], NestedQ[Q = Animal])
    operation nestedNot(n: Int64) -> Bool = type_admits(Wide[W = Option[T = Cat]], NestedQ[Q = Animal])
    operation throughTheRow(n: Int64) -> Bool = TypePattern.admits[T = Wide[W = Int64]](Narrow)"#,
    );
    assert_answers(
        &src,
        &[
            ("clause", true),
            ("clauseNot", false),
            ("clauseOpen", true),
            ("param", true),
            ("paramNot", false),
            ("openParam", true),
            ("twoDown", true),
            ("twoDownNot", false),
            ("nested", true),
            ("nestedNot", false),
            ("throughTheRow", true),
        ],
    );
}

/// DERIVED-ONLY (071 §1.2): `TypePattern` has one row, `TypeValuePattern`'s, and a written
/// one is refused wherever it is written — a sort's own body, a witness sort, and a
/// `namespace` block at `TypeValuePattern`'s address at another binding. Each names the
/// provider it was written for. A second clause of the row itself, conditioned or not, is
/// refused by the row's `where` block (proposal 066 §7.5). BACK-OUT: with the check gone,
/// the first program loads clean, and its `admits` answers for `Boom`; with its binding half
/// gone (the provider alone read), `other_binding` loads clean.
///
/// CONTROL: the stdlib presented to a KB a second time is the same row and the same clause
/// — the idempotent-across-loads suites (`scope_axiom_witness_test` and its siblings,
/// `wi_4zrtg_sealed_library_test`) load clean.
#[test]
fn a_written_type_pattern_row_is_refused() {
    let own_body = r#"
namespace wisqzpq.own
  import anthill.prelude.{Type, Bool}
  import anthill.reflect.{TypePattern}
  sort Boom
    entity boom
    provides TypePattern[T = Boom] where
      operation admits(t: Type) -> Bool = true
    end
  end
end
"#;
    let witness = r#"
namespace wisqzpq.witness
  import anthill.prelude.{Type, Bool}
  import anthill.reflect.{TypePattern}
  sort Boom
    entity boom
  end
  sort Wrapper
    provides TypePattern[T = Boom] where
      operation admits(t: Type) -> Bool = true
    end
  end
end
"#;
    let other_binding = r#"
namespace wisqzpq.other
  sort Boom
    entity boom
  end
end
namespace anthill.reflect.TypeValuePattern
  import anthill.reflect.{TypePattern, TypeValue}
  import wisqzpq.other.{Boom}
  provides TypePattern[T = Boom] :- TypeValue[T = T]
end
"#;
    let second_clause = r#"
namespace anthill.reflect.TypeValuePattern
  import anthill.reflect.{TypePattern}
  provides TypePattern[T = T] :- TypePattern[T = T]
end
"#;
    let unconditioned_clause = r#"
namespace anthill.reflect.TypeValuePattern
  import anthill.reflect.{TypePattern}
  provides TypePattern[T = T]
end
"#;
    for (src, provider) in [
        (own_body, "wisqzpq.own.Boom"),
        (witness, "wisqzpq.witness.Wrapper"),
        (other_binding, "anthill.reflect.TypeValuePattern"),
    ] {
        let errs = refusals(src);
        assert!(
            errs.iter().any(|e| e.contains(&format!(
                "a `provides anthill.reflect.TypePattern[…]` is written for '{provider}'"
            ))),
            "a written `provides TypePattern` must be refused naming `{provider}`; got {errs:?}"
        );
    }
    for src in [second_clause, unconditioned_clause] {
        let errs = refusals(src);
        assert!(
            errs.iter().any(|e| e.contains(
                "`anthill.reflect.TypeValuePattern` provides `anthill.reflect.TypePattern` in 2 clauses, and one of them has a `where` block"
            )),
            "a second clause of the row must be refused; got {errs:?}"
        );
    }
}

/// THE ROW'S MEMBER IS ITS OWN SORT'S, called directly: `TypeValuePattern.admits[T = X](t)`
/// builds the row's dictionary where it is written, at a ground instance and from a
/// caller's `requires TypeValue`, and reads the instance the bracket names — beside a
/// second `TypeValue` slot as well (`two`). That last is the program that read the first
/// slot when the row stood on `TypeValue`, a sort every sort provides.
#[test]
fn the_rows_member_is_called_directly() {
    let src = program(
        r#"    operation direct(n: Int64) -> Bool = TypeValuePattern.admits[T = Animal](Cat)
    operation directNot(n: Int64) -> Bool = TypeValuePattern.admits[T = Cat](Animal)
    operation viaValue[Q](t: Type) -> Bool requires TypeValue[T = Q] =
      TypeValuePattern.admits[T = Q](t)
    operation generic(n: Int64) -> Bool = viaValue[Q = Animal](Cat)
    operation two[P, Q](t: Type) -> Bool requires TypeValue[T = P], TypeValue[T = Q] =
      TypeValuePattern.admits[T = Q](t)
    operation secondSlot(n: Int64) -> Bool = two[P = IoError, Q = FileNotFound](IoError)
    operation secondSlotHolds(n: Int64) -> Bool = two[P = FileNotFound, Q = IoError](FileNotFound)"#,
    );
    assert_answers(
        &src,
        &[
            ("direct", true),
            ("directNot", false),
            ("generic", true),
            ("secondSlot", false),
            ("secondSlotHolds", true),
        ],
    );
}

/// A CALL OF `admits` NAMES ITS INSTANCE: no argument or result stands at `T`, so the bare
/// `TypePattern.admits(t)` is refused at load, as `TypeValue.type_value()` is, the refusal
/// naming the bracket to write. BACK-OUT: with the row on `TypeValue`, every sort provided
/// `TypePattern` through its derived `TypeValue` row, and the bare call loaded and died at
/// run time. On the parent tree it is refused for the names alone, which these words are not.
#[test]
fn a_bare_admits_call_is_refused() {
    let src = program("    operation bare(t: Type) -> Bool = TypePattern.admits(t)");
    let errs = refusals(&src);
    assert!(
        errs.iter().any(|e| e.contains("no provider can be selected here")
            && e.contains("Name the instance in the call's bracket")),
        "a bare `TypePattern.admits(t)` must be refused at load, naming the bracket; got {errs:?}"
    );
}

/// `TypeValue` GAINS NO MEMBER, which is why the row is a sort of its own. A sort's own
/// `admits` is its own, called inside it (`Club.check`) or on a value through another spec's
/// row (`door().admits(…)`). PASSES ON THE PARENT TREE, BY DESIGN: it is what the row broke
/// while it stood on `TypeValue`, whose member every sort then had — `Club.check(1)` answered
/// `true` through `TypeValue.admits`, and `door().admits(Door)` was refused for its arity.
#[test]
fn type_value_gains_no_member() {
    let src = r#"
namespace wisqzpq.tp
  import anthill.prelude.{Type, Bool, Int64}
  sort Gate
    sort T = ?
    operation admits(g: T, t: Type) -> Bool
  end
  sort Door
    entity door
    provides Gate[T = Door] where
      operation admits(g: Door, t: Type) -> Bool = true
    end
  end
  sort Club
    sort T = ?
    entity club(v: T)
    operation admits(t: Type) -> Bool = false
    operation check(n: Int64) -> Bool = admits[T = Int64](Int64)
  end
  sort D
    operation opens(n: Int64) -> Bool = door().admits(Door)
    operation clubs(n: Int64) -> Bool = Club.check(1)
  end
end
"#;
    assert_answers(src, &[("opens", true), ("clubs", false)]);
}

/// A SORT'S OWN `type_value` IS HELD TO NO CONTRACT OF `TypeValue`'s: it answers no type read
/// (`a_sorts_own_type_value_answers_no_type_read`), so it overrides nothing and no provision
/// owes it — with an effect of its own, a precondition of its own, or written in another
/// spec's `where` block. BACK-OUT: with the override and member checks reading it as
/// `TypeValue.type_value`'s, each is refused at load — "overrides
/// 'anthill.reflect.TypeValue.type_value' but does not refine it", and "`provides
/// anthill.reflect.TypeValue[…]` on `…Y` has no `type_value`" — as on the parent tree.
#[test]
fn a_sorts_own_type_value_is_held_to_no_contract_of_it() {
    let src = r#"
namespace wisqzpq.tp
  import anthill.prelude.{Int64, Error}
  import anthill.prelude.PartialOrd.{gt}
  sort Fault
    entity fault
  end
  sort Version
    entity version(n: Int64)
    operation type_value(n: Int64) -> Int64 effects {Error[Fault]} = n
  end
  sort Checked
    entity checked(n: Int64)
    operation type_value(n: Int64) -> Int64 requires gt(n, 0) = n
  end
  sort Typed
    sort T = ?
    operation type_value() -> Int64
  end
  sort Y
    entity y
    provides Typed[T = Y] where
      operation type_value() -> Int64 = 4
    end
  end
  sort D
    operation effectful(n: Int64) -> Int64 effects {Error[Fault]} = Version.type_value(3)
    operation preconditioned(n: Int64) -> Int64 = Checked.type_value(3)
    operation inABlock(n: Int64) -> Int64 = Typed.type_value[T = Y]()
  end
end
"#;
    let mut interp = crate::common::interp_for(src);
    for (op, want) in [("effectful", 3), ("preconditioned", 3), ("inABlock", 4)] {
        match interp.call(&format!("wisqzpq.tp.D.{op}"), &[Value::Int(0)]) {
            Ok(Value::Int(got)) => assert_eq!(got, want, "{op}"),
            other => panic!("{op}: expected an Int64, got {other:?}"),
        }
    }
}

/// A LOWERED READ TYPED AGAIN BY A REWRITE: a `@[simp]` rule that fires on a body types what
/// it rewrote, and the read of `T` there is the call it was lowered to, its bracket keyed as a
/// written one is — by the bare parameter, for a clause written positionally
/// (`requires TypeValue[P]`) and for a sort's own clause, whose chain carries an operation's
/// binding beside `T`. BACK-OUT: with the clause's keys copied as they are held, both are
/// refused, "unknown type-param 'T'".
#[test]
fn a_lowered_read_typed_again_by_a_rewrite_answers() {
    let src = r#"
namespace wisqzpq.tp
  import anthill.prelude.{Int64, String, Type}
  import anthill.reflect.{TypeValue}
  operation idT(t: Type) -> Type
  rule idT(?x) <=> ?x @[simp]
  sort Err2
    sort T = ?
    requires TypeValue[T = T]
    operation tagOf(error: T) -> Type = idT(T)
  end
  sort D
    operation tyOf[P](n: Int64) -> Type requires TypeValue[P] = idT(P)
    operation positional(n: Int64) -> Type = tyOf[P = Int64](0)
    operation sortLevel(n: Int64) -> Type = Err2.tagOf("s")
  end
end
"#;
    let mut interp = crate::common::interp_for(src);
    for (op, want) in [("positional", "Int64"), ("sortLevel", "String")] {
        match interp.call(&format!("wisqzpq.tp.D.{op}"), &[Value::Int(0)]) {
            Ok(v) => assert_eq!(
                anthill_core::kb::typing::type_display_name_value(interp.kb(), &v),
                want,
                "{op}"
            ),
            other => panic!("{op}: expected a type, got {other:?}"),
        }
    }
}
