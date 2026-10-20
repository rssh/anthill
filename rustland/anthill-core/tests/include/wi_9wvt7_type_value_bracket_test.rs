//! WI-20260908-9WVT7 — `TypeValue.type_value` always takes its type-argument, and a call of a
//! member of any provided sort whose signature names nothing of that sort names its instance
//! in its bracket (user, 2026-10-17).
//!
//! A. `type_value[X]()` answers `X`: named or positional, at a ground type, a parameter the
//!    scope's `requires` covers, or a type built over such parameters — the type written in
//!    value position. `type_value()` is refused at load, and so is a type-argument nothing
//!    supplies, a tuple or an arrow among them.
//! B. Every spec: a `requires` in scope supplies the evidence for the instance a call names
//!    and does not name it. With no bracket the call is refused, advising one; with it the
//!    call runs at that instance, a default body included. A sort nothing provides runs its
//!    own operation, and a member whose argument, result or effect names the sort is
//!    inferred from the call's types.
//! C. The wrong answers the one-clause reading gave: a member of `Box` writing `type_value()`
//!    under `requires TypeValue[T = V]` answered `V`.
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build, over this
//! file and the whole `wi_tests` binary, where each moves only the rows named:
//!
//!   * the refusal of a call that names no instance off →
//!     [`a_type_value_call_names_its_type_argument_or_is_refused`],
//!     [`a_requirement_in_scope_does_not_name_the_instance`],
//!     [`a_clause_in_scope_no_longer_answers_for_the_call`], and the rewritten bare-call rows of
//!     `wi_nr6fj` (three), `wi_r541x` (the two clauses) and `wi_2kv4y` (the callee's own spec);
//!   * a positional held to the operation's own parameters →
//!     [`a_positional_type_argument_is_the_named_one`],
//!     [`a_requirement_in_scope_does_not_name_the_instance`] and `wi841`'s two positional rows;
//!   * the instance withheld from an operation its provider has no member for →
//!     [`a_ground_or_built_type_argument_answers_its_type`],
//!     [`the_answer_equals_the_type_written_in_value_position`],
//!     [`a_clause_in_scope_no_longer_answers_for_the_call`];
//!   * the builtin keying a type's argument by the parameter's qualified symbol → the same three;
//!   * the bracket's binding no carrier source, or the operation's own `requires` left out of
//!     the instance's resolution → [`a_defaulted_member_runs_at_the_instance_its_bracket_names`];
//!   * the parameter a signature never writes skipped by the abstract-call check →
//!     [`a_type_argument_nothing_supplies_is_refused_at_load`];
//!   * the slot deferral asking for a sole clause → [`two_clauses_and_the_bracket_says_which`];
//!   * a sub-interface counted as a provider → [`what_needs_no_bracket_runs`] and
//!     `wi752_dotted_ladder_test`;
//!   * the builtin counted as serving every carrier → [`a_tuple_or_an_arrow_has_no_instance`].

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// A program in `probe.<ns>` with the reflect and prelude names in scope, and `main`.
fn program(ns: &str, decls: &str, main: &str) -> String {
    format!(
        "namespace probe.{ns}\n  import anthill.prelude.{{Int64, String, List, Type, Option, Pair, \
         PartialEq, Eq}}\n  import anthill.prelude.Option.{{some}}\n  import anthill.reflect.\
         {{TypeValue}}\n{decls}  operation bit(c: Bool) -> Int64 = if c then 1 else 0\n  operation \
         main() -> Int64 =\n    {main}\nend\n"
    )
}

fn run(ns: &str, decls: &str, main: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, main), &format!("probe.{ns}.main"))
}

// ── A. `type_value[X]()` ──────────────────────────────────────────────────────────────────

/// A CALL WITH NO TYPE-ARGUMENT IS REFUSED, advising the bracket; the bracketed call answers
/// the type it names. On an operation's `requires` and on a sort's alike: the one clause in
/// scope decided what `type_value()` answered, and now it is evidence only.
///
/// FAILS with the refusal off: the bare calls load.
#[test]
fn a_type_value_call_names_its_type_argument_or_is_refused() {
    let op = "  operation tv[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value{b}()\n";
    let srt = "  sort H\n    sort A = ?\n    requires TypeValue[T = A]\n    entity h(a: A)\n    \
               operation ty(x: H[A = A]) -> Type = TypeValue.type_value{b}()\n  end\n";
    for (shape, decls, advice) in [
        ("an operation's requires", op, "`anthill.reflect.TypeValue.type_value[T = B]()`"),
        ("a sort's requires", srt, "`anthill.reflect.TypeValue.type_value[T = A]()`"),
    ] {
        assert_refused_naming(
            &load_errors_of(&program("tvbare", &decls.replace("{b}", ""), "0")),
            &[
                "a call of `anthill.reflect.TypeValue.type_value` that names no instance of \
                 `anthill.reflect.TypeValue`",
                advice,
            ],
            shape,
        );
    }
    assert_eq!(
        run(
            "tvnamed",
            &op.replace("{b}", "[T = B]"),
            "bit(PartialEq.eq(tv(1), Int64)) + 2 * bit(PartialEq.eq(tv(\"s\"), String))"
        ),
        Ok(3)
    );
    assert_eq!(
        run("tvsort", &srt.replace("{b}", "[T = A]"), "bit(PartialEq.eq(H.ty(h(1)), Int64))"),
        Ok(1)
    );
}

/// A POSITIONAL TYPE-ARGUMENT IS THE NAMED ONE: `type_value[B]()` binds the spec's `T` as
/// `type_value[T = B]()` does. It was refused as over-applied, the positional reaching the
/// operation's own parameters alone.
///
/// FAILS with the positional held to the operation's own list: refused, over-applied.
#[test]
fn a_positional_type_argument_is_the_named_one() {
    let decls = "  operation tv[B](x: B) -> Type requires TypeValue[T = B] = TypeValue.type_value[B]()\n";
    assert_eq!(
        run(
            "tvpos",
            decls,
            "bit(PartialEq.eq(tv(1), Int64)) + 2 * bit(PartialEq.eq(tv(\"s\"), String))"
        ),
        Ok(3)
    );
}

/// A GROUND TYPE-ARGUMENT NEEDS NO REQUIREMENT, and a type built over evidence answers the
/// type it builds — in a free operation and in a provision's member. The call reached the
/// builtin with no dictionary and died "no dispatching dictionary"; the dispatch had chosen
/// the instance and handed it to nothing, the provider having no member of its own.
///
/// FAILS with the instance withheld from an operation the provider has no member for, and with
/// the builtin's qualified key (the built type is not the written one).
#[test]
fn a_ground_or_built_type_argument_answers_its_type() {
    assert_eq!(
        run(
            "tvground",
            "  operation tv() -> Type = TypeValue.type_value[T = Int64]()\n",
            "bit(PartialEq.eq(tv(), Int64))"
        ),
        Ok(1)
    );
    assert_eq!(
        run(
            "tvbuilt",
            "  operation tv[E](x: E) -> Type requires TypeValue[T = E] = \
             TypeValue.type_value[T = Option[T = E]]()\n",
            "bit(PartialEq.eq(tv(1), Option[T = Int64])) + 2 * bit(PartialEq.eq(tv(\"s\"), \
             Option[T = Int64]))"
        ),
        Ok(1)
    );
    let member = "  sort Desc\n    sort T = ?\n    operation d(x: T) -> Type\n  end\n  sort W\n    \
                  sort E = ?\n    requires TypeValue[T = E]\n    provides Desc[T = Option[T = E]]\n    \
                  operation d(x: Option[T = E]) -> Type = TypeValue.type_value[T = Option[T = E]]()\n  \
                  end\n  operation dOf[X](x: X) -> Type requires Desc[T = X] = Desc.d(x)\n";
    assert_eq!(
        run("tvmember", member, "bit(PartialEq.eq(dOf(some(1)), Option[T = Int64]))"),
        Ok(1)
    );
}

/// THE ANSWER IS THE TYPE WRITTEN IN VALUE POSITION, whatever order the arguments are written
/// in, the order the sort declares its parameters in, how deep it nests, and whether the
/// sort's own `requires` shifts its dictionary's slots. The builtin keyed an argument by the
/// parameter's qualified symbol, so `type_value[T = Option[T = E]]()` printed `Option(T:
/// Int64)` and was not equal to the written `Option[T = Int64]`.
///
/// FAILS with the qualified key back, and with the instance withheld (the calls die).
#[test]
fn the_answer_equals_the_type_written_in_value_position() {
    let decls = "  sort Two\n    sort B = ?\n    sort A = ?\n    entity two(a: A, b: B)\n  end\n  \
                 sort Keyed\n    sort K = ?\n    requires Eq[T = K]\n    entity keyed(k: K)\n  end\n  \
                 operation pairOf[X, Y](x: X, y: Y) -> Type requires TypeValue[T = X], TypeValue[T = Y] \
                 =\n    TypeValue.type_value[T = Pair[A = X, B = Y]]()\n  operation twoOf[X, Y](x: X, y: \
                 Y) -> Type requires TypeValue[T = X], TypeValue[T = Y] =\n    TypeValue.type_value[T = \
                 Two[A = X, B = Y]]()\n  operation nested[X](x: X) -> Type requires TypeValue[T = X] =\n    \
                 TypeValue.type_value[T = Option[T = Option[T = X]]]()\n  operation keyedOf() -> Type = \
                 TypeValue.type_value[T = Keyed[K = Int64]]()\n";
    assert_eq!(
        run(
            "tvkeys",
            decls,
            "bit(PartialEq.eq(pairOf(1, \"s\"), Pair[B = String, A = Int64])) + 2 * \
             bit(PartialEq.eq(twoOf(1, \"s\"), Two[A = Int64, B = String])) + 4 * \
             bit(PartialEq.eq(nested(1), Option[T = Option[T = Int64]])) + 8 * \
             bit(PartialEq.eq(keyedOf(), Keyed[K = Int64])) + 16 * \
             bit(PartialEq.eq(pairOf(1, \"s\"), Pair[A = String, B = Int64]))"
        ),
        Ok(15),
        "the four agree, and the pair at swapped arguments does not"
    );
}

/// A TYPE-ARGUMENT NOTHING SUPPLIES IS REFUSED AT LOAD, as a call is: `type_value[T = B]()`
/// in `f[B](x: B)` with no `requires TypeValue[T = B]` loaded and died "no dispatching
/// dictionary". The parameter the signature never writes was skipped by the abstract-call
/// check, on the reading that a receiver-less call could not name it.
///
/// FAILS with the skip back: the program loads.
#[test]
fn a_type_argument_nothing_supplies_is_refused_at_load() {
    assert_refused_naming(
        &load_errors_of(&program(
            "tvnone",
            "  operation tv[B](x: B) -> Type = TypeValue.type_value[T = B]()\n",
            "0",
        )),
        &["covering abstract type parameter"],
        "a type parameter nothing covers",
    );
}

const DESC_AT: &str = "  sort Desc\n    sort T = ?\n    operation d(x: T) -> Type\n  end\n  sort \
                       Box\n    entity box(n: Int64)\n    provides Desc[T = Box]\n    operation d(x: \
                       Box) -> Type = TypeValue.type_value[T = {at}]()\n  end\n  operation dOf[X](x: \
                       X) -> Type requires Desc[T = X] = Desc.d(x)\n";

/// A TUPLE OR AN ARROW HAS NO INSTANCE, so `type_value` at one is refused at load, in a free
/// operation and in a provision's member alike, advising a sort in the bracket. The
/// builtin's `@[host_implemented]` claim exempted the call from the refusal a callee nobody
/// implements gets; the call loaded with no dictionary to hand it, and in `Box.d`, entered
/// through `Desc`, it answered `Box`, through the dictionary `d`'s own frame was entered
/// with. A sort at the same place runs.
///
/// FAILS with the builtin counted as serving every carrier: the three calls load, and
/// `dOf(box(1))` answers `Box`.
#[test]
fn a_tuple_or_an_arrow_has_no_instance() {
    let decls = format!(
        "  operation tup() -> Type = TypeValue.type_value[T = (Int64, String)]()\n  operation \
         arr() -> Type = TypeValue.type_value[T = (x: Int64) -> Int64]()\n{}",
        DESC_AT.replace("{at}", "(Int64, String)")
    );
    let errs = load_errors_of(&program("tvformer", &decls, "0"));
    assert_refused_naming(
        &errs,
        &[
            "its carrier is `(_1: Int64, _2: String)`, a tuple or an arrow",
            "its carrier is `Int64 -> Int64`, a tuple or an arrow",
            "the derived instances cover sorts only",
            "Name a sort in the call's bracket",
        ],
        "a type-argument at a former",
    );
    assert_eq!(errs.len(), 3, "one refusal per call: {errs:#?}");
    assert_eq!(
        run(
            "tvformersort",
            &DESC_AT.replace("{at}", "Pair[A = Int64, B = String]"),
            "bit(PartialEq.eq(dOf(box(1)), Pair[A = Int64, B = String])) + 2 * \
             bit(PartialEq.eq(dOf(box(1)), Box))"
        ),
        Ok(1)
    );
}

// ── B. every spec ─────────────────────────────────────────────────────────────────────────

const STAMP: &str = "  sort Stamp\n    sort T = ?\n    operation stamp() -> Int64\n    operation twice() \
                     -> Int64 = stamp() * 2\n  end\n  sort A1\n    entity a1\n    provides Stamp[T = A1]\n    \
                     operation stamp() -> Int64 = 7\n  end\n  sort A2\n    entity a2\n    provides Stamp[T = \
                     A2]\n    operation stamp() -> Int64 = 8\n  end\n";

/// A REQUIREMENT IN SCOPE DOES NOT NAME THE INSTANCE, for any spec. `Stamp.stamp()` under
/// `requires Stamp[T = A]` is refused, advising `Stamp.stamp[T = A]()`; named, positional and
/// ground brackets each run at the instance they name.
///
/// FAILS with the refusal off (the bare call loads), and with a positional held to the
/// operation's own parameters (`Stamp.stamp[A]()` is refused as over-applied).
#[test]
fn a_requirement_in_scope_does_not_name_the_instance() {
    let use_s = |call: &str| {
        format!("{STAMP}  operation useS[A](x: A) -> Int64 requires Stamp[T = A] = {call}\n")
    };
    assert_refused_naming(
        &load_errors_of(&program("stbare", &use_s("Stamp.stamp()"), "useS(a1)")),
        &[
            "a call of `probe.stbare.Stamp.stamp` that names no instance of `probe.stbare.Stamp`",
            "`probe.stbare.Stamp.stamp[T = A]()`",
        ],
        "a bare call under one clause",
    );
    for call in ["Stamp.stamp[T = A]()", "Stamp.stamp[A]()"] {
        assert_eq!(run("stnamed", &use_s(call), "useS(a1) + useS(a2) * 10"), Ok(87), "{call}");
    }
    assert_eq!(
        run("stground", STAMP, "Stamp.stamp[T = A1]() + Stamp.stamp[T = A2]() * 10"),
        Ok(87)
    );
}

/// TWO CLAUSES OVER ONE SPEC, AND THE BRACKET SAYS WHICH — for a body-less member and a
/// defaulted one alike. The defaulted call's deferral to a slot needed exactly one clause, so
/// `Stamp.twice[T = B]()` beside two died "operation has no body".
///
/// FAILS with the deferral asking for a sole clause: the defaulted call dies.
#[test]
fn two_clauses_and_the_bracket_says_which() {
    let decls = format!(
        "{STAMP}  operation second[A, B](x: A, y: B) -> Int64 requires Stamp[T = A], Stamp[T = B] = \
         Stamp.stamp[T = B]()\n  operation secondTwice[A, B](x: A, y: B) -> Int64 requires Stamp[T \
         = A], Stamp[T = B] = Stamp.twice[T = B]()\n"
    );
    assert_eq!(
        run("sttwo", &decls, "second(a1, a2) + 10 * secondTwice(a1, a2)"),
        Ok(168),
        "8, and 16 through the default at `A2`"
    );
}

/// A DEFAULTED MEMBER RUNS AT THE INSTANCE ITS BRACKET NAMES, at a ground type and at one built
/// over the scope's evidence. Its default body's sibling call `name()` died "operation has no
/// body": the call reached the default with no instance at all, the bracket's binding read as
/// a carrier by no route.
///
/// FAILS with the bracket's binding no carrier source: both die. With the operation's own
/// `requires` left out of the instance's resolution the built one dies alone.
#[test]
fn a_defaulted_member_runs_at_the_instance_its_bracket_names() {
    let decls = "  sort Desc\n    sort T = ?\n    operation name() -> Int64\n    operation twice() -> \
                 Int64 = name() * 2\n  end\n  sort IntDesc\n    provides Desc[T = Int64]\n    operation \
                 name() -> Int64 = 21\n  end\n  sort OptDesc\n    sort E = ?\n    requires Desc[T = E]\n    \
                 provides Desc[T = Option[T = E]]\n    operation name() -> Int64 = Desc.name[T = E]() + \
                 100\n  end\n  operation viaOpt[E](x: E) -> Int64 requires Desc[T = E] = \
                 Desc.twice[T = Option[T = E]]()\n";
    assert_eq!(run("dground", decls, "Desc.twice[T = Int64]()"), Ok(42));
    assert_eq!(run("dbuilt", decls, "viaOpt(1)"), Ok(242), "(21 + 100) * 2");
}

/// A SORT NOTHING PROVIDES RUNS ITS OWN OPERATION — there is no instance to choose — and so
/// does one only a sub-interface provides (`Mid provides Base[T = T]`, whose values are its
/// providers'). A member whose result names the sort is inferred from the type expected of
/// it, as before.
///
/// These are the calls the refusal must not reach. FAILS with a sub-interface counted as a
/// provider: `Mid.f()` is refused. The rest passes either way, by design.
#[test]
fn what_needs_no_bracket_runs() {
    assert_eq!(
        run(
            "ownop",
            "  sort Util\n    sort T = ?\n    operation helper() -> Int64 = 3\n  end\n  sort Base\n    \
             sort T = ?\n    operation f() -> Int64 = 41\n  end\n  sort Mid\n    sort T = ?\n    \
             provides Base[T = T]\n  end\n",
            "Util.helper() + Mid.f()"
        ),
        Ok(44)
    );
    assert_eq!(
        run(
            "inferred",
            "  sort Zero\n    sort T = ?\n    operation zero() -> T\n  end\n  sort IZ\n    provides \
             Zero[T = Int64]\n    operation zero() -> Int64 = 4\n  end\n  sort SZ\n    provides \
             Zero[T = String]\n    operation zero() -> String = \"z\"\n  end\n",
            "let z: Int64 = Zero.zero()\n    z + 1"
        ),
        Ok(5)
    );
}

// ── C. what the one-clause reading answered ───────────────────────────────────────────────

/// A MEMBER OF `Box` WRITING `type_value()` UNDER `requires TypeValue[T = V]` ANSWERED `V`,
/// the clause's instance, where the author asking for the type of the box gets nothing
/// telling them so. It is refused now, and the two calls the author could mean each answer
/// what they say.
///
/// FAILS with the refusal off (the bare call loads), and with the instance withheld or the
/// qualified key (the box's own type is not answered).
#[test]
fn a_clause_in_scope_no_longer_answers_for_the_call() {
    let decls = |call: &str| {
        format!(
            "  sort Box\n    sort V = ?\n    entity box(v: V)\n    requires TypeValue[T = V]\n    \
             operation self(b: Self) -> Type = {call}\n    operation elem(b: Self) -> Type = \
             TypeValue.type_value[T = V]()\n  end\n"
        )
    };
    assert_refused_naming(
        &load_errors_of(&program("boxbare", &decls("TypeValue.type_value()"), "0")),
        &["names no instance of `anthill.reflect.TypeValue`"],
        "the bare call in a member of `Box`",
    );
    assert_eq!(
        run(
            "boxnamed",
            &decls("TypeValue.type_value[T = Box[V = V]]()"),
            "bit(PartialEq.eq(Box.self(box(v: 1)), Box[V = Int64])) + 2 * \
             bit(PartialEq.eq(Box.elem(box(v: 1)), Int64))"
        ),
        Ok(3)
    );
}
