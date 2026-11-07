//! WI-20261021-Z2P21 — a guard element at a parameter of the sort the rule is written in is
//! fixed where the rule is cited, as a call of the sort's operation fixes it
//! (kernel-language §8, "One principle, two engines": the receiver bracket, an applied
//! argument, a default; a parameter none of them fixes is a load error).
//!
//! Over `sort Box { sort P = ?; rule g[A](?x: A, ?r) :- Sp[C = A, P = P], Sp.crecv(?x, ?r) }`
//! the guard's `P` is `Box`'s. On 7c203fd9 a goal `Box[P = Bool].g(red(), ?r)` built the guard
//! with `P` free: refused ("not decided by the goal's types") beside two witnesses at
//! `C = Red`, and answering `Red`'s own 5 beside `Red`'s provision, where the operation twin
//! `Box[P = Bool].h(red())` answers 6; a citation from an operation body answered 5 at every
//! bracket, and with none, beside `Red`'s provision, and conditionally beside the two witnesses
//! alone.
//!
//! What fails with each part backed out (temporary switches, measured, then removed):
//! - the rule-body goal's read of the sort's parameter (`dictionary_at_goal`): the six rows on
//!   a goal — [`the_goals_bracket_fixes_the_guards_sort_parameter`],
//!   [`an_argument_at_a_column_typed_with_it_fixes_it`], [`a_default_fixes_it`],
//!   [`a_goal_that_fixes_nothing_is_refused_naming_the_bracket`],
//!   [`a_member_that_declares_the_guard_passes_it`],
//!   [`a_bracket_that_leaves_it_unfixed_is_refused_once`] (refused twice, "not decided") — and
//!   wi_51w18's `the_name_is_the_enclosing_sorts_parameter_where_one_is_declared`;
//! - the guard's build left silent where the bracket's citation refused the parameter
//!   (`GoalDictMiss::Unfixed` read as `NoGuard`): [`a_bracket_that_leaves_it_unfixed_is_refused_once`];
//! - a goal that cannot be read as a citation refused for it (`goal_sort_param_values`' error,
//!   where the defaults alone were read): [`a_goal_that_cannot_be_read_as_a_citation_is_refused_for_its_arguments`];
//! - the citation read of a goal with no bracket (`goal_sort_param_values`, the defaults
//!   alone): [`an_argument_at_a_column_typed_with_it_fixes_it`]; [`a_default_fixes_it`] passes,
//!   the defaults being read either way;
//! - the citation's read in the guard's route (`route_requirement_read`):
//!   [`cited_from_an_operation_body`];
//! - an element at a type parameter of the citing operation read as concrete there (the
//!   `value_contains_rigid` test beside `at_concrete`): [`a_generic_callers_bracket_passes_its_requirement`].
//!
//! [`the_operation_twin_answers_either_way`] and
//! [`an_element_at_an_introducer_is_fixed_by_the_citation_either_way`] pass under each, by
//! design.

use anthill_core::eval::Value;

/// `Sp`, its carrier `C` and a content `P` no operation names; `Red` provides nothing, the two
/// witnesses provide `Sp` at `C = Red`, `IntW` at `P = Int64` (5) and `BoolW` at `P = Bool` (6),
/// so only a fixed `P` can choose between them. `tail` is the rest of the namespace.
fn program(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, Error, EmptyStream}}

  sort Sp
    import anthill.prelude.Int64
    sort C = ?
    sort P = ?
    operation crecv(x: C) -> Int64 = 0
  end

  sort Red
    entity red
  end

  sort IntW
    import anthill.prelude.Int64
    provides Sp[C = Red, P = Int64]
    operation crecv(x: Red) -> Int64 = 5
  end

  sort BoolW
    import anthill.prelude.{{Int64, Bool}}
    provides Sp[C = Red, P = Bool]
    operation crecv(x: Red) -> Int64 = 6
  end
{tail}
end
"#
    )
}

/// `sort Box` with `P` declared as `p_decl` and the members `members`.
fn boxed(p_decl: &str, members: &str) -> String {
    format!("  sort Box\n    import anthill.prelude.Int64\n    {p_decl}\n{members}  end\n")
}

const G: &str = "    rule g[A](?x: A, ?r) :- Sp[C = A, P = P], Sp.crecv(?x, ?r)\n";

/// The definite `Int64` answers of `{ns}.{rel}`, sorted.
fn answers(src: &str, rel: &str) -> Vec<i64> {
    let mut kb = crate::common::load_kb_with(src);
    let mut out: Vec<i64> = crate::common::query_unary(&mut kb, rel)
        .iter()
        .map(|sol| match sol {
            (Value::Int(i), true) => *i,
            other => panic!("`{rel}` must answer definite Ints, got {other:?}"),
        })
        .collect();
    out.sort_unstable();
    out
}

fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("must be refused; it loaded clean:\n{src}"))
        .join("\n")
}

/// THE GOAL'S BRACKET FIXES IT: `Box[P = Bool].g` is `BoolW`'s 6, `Box[P = Int64].g` `IntW`'s
/// 5. And beside `Red`'s own provision at `P = Int64`, the default among the two at `Red`,
/// `Box[P = Bool].g` still answers `BoolW`'s 6 (it answered 5).
#[test]
fn the_goals_bracket_fixes_the_guards_sort_parameter() {
    let tail = format!(
        "{}  rule viaBool(?r) :- Box[P = Bool].g(red(), ?r)\n  rule viaInt(?r) :- Box[P = Int64].g(red(), ?r)\n",
        boxed("sort P = ?", G)
    );
    let src = program("test.z2p21.br", &tail);
    assert_eq!(answers(&src, "test.z2p21.br.viaBool"), vec![6]);
    assert_eq!(answers(&src, "test.z2p21.br.viaInt"), vec![5]);
    let int_w = "  sort IntW\n    import anthill.prelude.Int64\n    provides Sp[C = Red, P = Int64]\n    \
                 operation crecv(x: Red) -> Int64 = 5\n  end\n";
    assert!(src.contains(int_w), "the fixture moved:\n{src}");
    let own = src.replace(int_w, "").replace(
        "  sort Red\n    entity red\n  end",
        "  sort Red\n    import anthill.prelude.Int64\n    entity red\n    provides Sp[C = Red, P = Int64]\n    \
         operation crecv(x: Red) -> Int64 = 5\n  end",
    );
    assert_eq!(answers(&own, "test.z2p21.br.viaBool"), vec![6]);
    assert_eq!(answers(&own, "test.z2p21.br.viaInt"), vec![5]);
}

/// AN ARGUMENT AT A COLUMN TYPED WITH IT FIXES IT: over `?p: P`, `Box.g(red(), true, ?r)` is at
/// `P = Bool`; with the bracket beside it, an argument of another type matches no solution.
#[test]
fn an_argument_at_a_column_typed_with_it_fixes_it() {
    let g = "    rule g[A](?x: A, ?p: P, ?r) :- Sp[C = A, P = P], Sp.crecv(?x, ?r)\n";
    let tail = format!(
        "{}  rule viaArg(?r) :- Box.g(red(), true, ?r)\n  rule both(?r) :- Box[P = Bool].g(red(), true, ?r)\n  rule other(?r) :- Box[P = Bool].g(red(), 3, ?r)\n",
        boxed("sort P = ?", g)
    );
    let src = program("test.z2p21.arg", &tail);
    assert_eq!(answers(&src, "test.z2p21.arg.viaArg"), vec![6]);
    assert_eq!(answers(&src, "test.z2p21.arg.both"), vec![6]);
    assert_eq!(answers(&src, "test.z2p21.arg.other"), Vec::<i64>::new());
}

/// THE PARAMETER'S DEFAULT FIXES IT where the goal writes nothing.
#[test]
fn a_default_fixes_it() {
    let tail = format!("{}  rule q(?r) :- Box.g(red(), ?r)\n", boxed("sort P = ? default Bool", G));
    assert_eq!(answers(&program("test.z2p21.dflt", &tail), "test.z2p21.dflt.q"), vec![6]);
}

/// A GOAL THAT FIXES NOTHING IS REFUSED, naming the parameter and the bracket — at namespace
/// level, and for a sibling's goal inside the sort, whose `P` is its own and which declares no
/// guard at it. Each advised repair answers: the bracket written, in either place.
#[test]
fn a_goal_that_fixes_nothing_is_refused_naming_the_bracket() {
    let want = "the guard names `Box`'s `P`, and nothing at the goal fixes it: write it in the goal's bracket, `Box[P = …].g(…)`";
    let uncited = program("test.z2p21.none", &format!("{}  rule q(?r) :- Box.g(red(), ?r)\n", boxed("sort P = ?", G)));
    let errs = refusal(&uncited);
    assert!(errs.contains(want), "got:\n{errs}");
    let sibling = program(
        "test.z2p21.sib",
        &format!("{}  rule q(?r) :- Box[P = Bool].inner(?r)\n", boxed("sort P = ?", &format!("{G}    rule inner(?r) :- g(red(), ?r)\n"))),
    );
    let errs = refusal(&sibling);
    assert!(errs.contains(want) && errs.contains("inner.body"), "got:\n{errs}");
    let repaired = sibling
        .replace("rule inner(?r) :- g(red(), ?r)", "rule inner(?r) :- Box[P = Bool].g(red(), ?r)")
        .replace("Box[P = Bool].inner(?r)", "Box.inner(?r)");
    assert_eq!(answers(&repaired, "test.z2p21.sib.q"), vec![6]);
    let repaired = uncited.replace("Box.g(red(), ?r)", "Box[P = Bool].g(red(), ?r)");
    assert_eq!(answers(&repaired, "test.z2p21.none.q"), vec![6]);
}

/// A MEMBER THAT DECLARES THE GUARD PASSES IT: `inner` holds `Sp[C = A, P = P]`, built at its
/// citation's `P = Bool`, and hands it to `g`.
#[test]
fn a_member_that_declares_the_guard_passes_it() {
    let members = format!("{G}    rule inner[A](?x: A, ?r) :- Sp[C = A, P = P], g(?x, ?r)\n");
    let tail = format!("{}  rule q(?r) :- Box[P = Bool].inner(red(), ?r)\n", boxed("sort P = ?", &members));
    assert_eq!(answers(&program("test.z2p21.decl", &tail), "test.z2p21.decl.q"), vec![6]);
}

/// CITED FROM AN OPERATION BODY the bracket fixes it as from a goal (6 and 5), and a citation
/// that fixes nothing is refused naming the bracket.
#[test]
fn cited_from_an_operation_body() {
    let src = |ns: &str, citation: &str| {
        program(
            ns,
            &format!(
                "{}  sort U\n    import anthill.prelude.{{Int64, Error, EmptyStream}}\n    \
                 operation cited() -> Int64 effects {{Error, Error[EmptyStream]}} = {citation}.head.r\n  end\n",
                boxed("sort P = ?", G)
            ),
        )
    };
    for (ns, bracket, want) in [("test.z2p21.opb", "Bool", 6), ("test.z2p21.opi", "Int64", 5)] {
        let mut interp = crate::common::interp_for(&src(ns, &format!("Box[P = {bracket}].g(red())")));
        match interp.call(&format!("{ns}.U.cited"), &[]) {
            Ok(Value::Int(n)) if n == want => {}
            other => panic!("`Box[P = {bracket}]`: expected {want}, got {other:?}"),
        }
    }
    let errs = refusal(&src("test.z2p21.opn", "Box.g(red())"));
    assert!(
        errs.contains("type parameter 'P' of `test.z2p21.opn.Box` is not determined at this citation")
            && errs.contains("`Box[P = …].g`"),
        "got:\n{errs}"
    );
}

/// A GENERIC CALLER'S BRACKET SELECTS ITS OWN INSTANCE: in `kr[X]() requires Sp[C = Red, P =
/// X]`, `Box[P = X].g(red())` is handed the dictionary `kr`'s caller chose — `kr[X = Bool]` 6,
/// `kr[X = Int64]` 5 — as the operation twin `Box[P = X].h(red())` is. On 7c203fd9 each was
/// undecided at load and answered conditionally.
#[test]
fn a_generic_callers_bracket_passes_its_requirement() {
    let tail = format!(
        "{}  sort U\n    import anthill.prelude.{{Int64, Bool, Error, EmptyStream}}\n    \
         operation kr[X]() -> Int64 effects {{Error, Error[EmptyStream]}} requires Sp[C = Red, P = X] = \
         Box[P = X].g(red()).head.r\n    \
         operation atBool() -> Int64 effects {{Error, Error[EmptyStream]}} = kr[X = Bool]()\n    \
         operation atInt() -> Int64 effects {{Error, Error[EmptyStream]}} = kr[X = Int64]()\n  end\n",
        boxed("sort P = ?", G)
    );
    let mut interp = crate::common::interp_for(&program("test.z2p21.gen", &tail));
    for (op, want) in [("atBool", 6), ("atInt", 5)] {
        match interp.call(&format!("test.z2p21.gen.U.{op}"), &[]) {
            Ok(Value::Int(n)) if n == want => {}
            other => panic!("`{op}`: expected {want}, got {other:?}"),
        }
    }
}

/// ONE FAULT, ONE REFUSAL: a bracket that writes another parameter (`Box[Q = Bool]`) and leaves
/// the guard's `P` unfixed is refused by the citation, naming `P`, and not again by the guard's
/// build.
#[test]
fn a_bracket_that_leaves_it_unfixed_is_refused_once() {
    let g = "    sort Q = ?\n    rule g[A](?x: A, ?q: Q, ?r) :- Sp[C = A, P = P], Sp.crecv(?x, ?r)\n";
    let tail = format!("{}  rule q(?r) :- Box[Q = Bool].g(red(), true, ?r)\n", boxed("sort P = ?", g));
    let errs = crate::common::try_load_kb_with(&program("test.z2p21.once", &tail))
        .err()
        .expect("the goal must be refused");
    assert_eq!(errs.len(), 1, "one refusal, got:\n{}", errs.join("\n"));
    assert!(errs[0].contains("type parameter 'P'") && errs[0].contains("`Box[P = …].g`"), "got: {}", errs[0]);
}

/// A GOAL THAT CANNOT BE READ AS A CITATION is refused for what is wrong with it: an argument
/// with no column to bind, not "nothing at the goal fixes it" (the citation it could not read).
#[test]
fn a_goal_that_cannot_be_read_as_a_citation_is_refused_for_its_arguments() {
    let tail = format!("{}  rule q(?r) :- Box.g(red(), ?r, 7)\n", boxed("sort P = ? default Bool", G));
    let errs = refusal(&program("test.z2p21.unread", &tail));
    assert!(errs.contains("positional argument #3 has no free column to bind"), "got:\n{errs}");
    assert!(!errs.contains("nothing at the goal fixes it") && !errs.contains("not decided"), "got:\n{errs}");
}

/// CONTROL, passes either way: a guard element at the rule's own introducer is fixed by the
/// citation's bracket on the introducer, from a rule body (`g[B = Bool]`, 6) and from a generic
/// operation that holds the requirement (`kr(true)` 6, `kr(3)` 5).
#[test]
fn an_element_at_an_introducer_is_fixed_by_the_citation_either_way() {
    let tail = "  rule g[A, B](?x: A, ?b: B, ?r) :- Sp[C = A, P = B], Sp.crecv(?x, ?r)
  rule viaBool(?r) :- g[B = Bool](red(), true, ?r)
  sort U
    import anthill.prelude.{Int64, Bool, Error, EmptyStream}
    operation kr[X](v: X) -> Int64 effects {Error, Error[EmptyStream]} requires Sp[C = Red, P = X] = \
      g[B = X](red(), v).head.r
    operation rBool() -> Int64 effects {Error, Error[EmptyStream]} = kr(true)
    operation rInt() -> Int64 effects {Error, Error[EmptyStream]} = kr(3)
  end
";
    let src = program("test.z2p21.intro", tail);
    assert_eq!(answers(&src, "test.z2p21.intro.viaBool"), vec![6]);
    let mut interp = crate::common::interp_for(&src);
    for (op, want) in [("rBool", 6), ("rInt", 5)] {
        match interp.call(&format!("test.z2p21.intro.U.{op}"), &[]) {
            Ok(Value::Int(n)) if n == want => {}
            other => panic!("`{op}`: expected {want}, got {other:?}"),
        }
    }
}

/// CONTROL, passes either way: the operation twin reads `Box`'s `P` from its receiver bracket.
#[test]
fn the_operation_twin_answers_either_way() {
    let h = "    operation h[A](x: A) -> Int64 requires Sp[C = A, P = P] = Sp.crecv(x)\n";
    let tail = format!("{}  rule q(?r) :- ?r <=> Box[P = Bool].h(red())\n", boxed("sort P = ?", h));
    assert_eq!(answers(&program("test.z2p21.op", &tail), "test.z2p21.op.q"), vec![6]);
}
