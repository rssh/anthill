//! WI-20261025-7K84M — ONE ANSWER TO "WHICH IMPLEMENTATION RUNS THIS CALL" ON THE BODY-LESS PATH
//! TOO (`docs/design/supplier-question-map.md`).
//!
//! WI-20261025-ZAWX9 gave a DEFAULTED spec operation one answer through a dictionary. A
//! body-less one was still answered by readers with rules of their own. MEASURED on 1373e04f,
//! 13 of the map's 112 programs against §8.7, every one body-less:
//!
//! | | supplied by | the call | answered | §8.7 |
//! |---|---|---|---|---|
//! | D1 | `Leaf`'s own member and its provision's binding | through a dictionary | the member | tie |
//! | D1 | the same, receiver-less | by name | the member | tie |
//! | D3 | the binding alone, receiver-less | by name | loads, dies `OperationBodyMissing` | the binding |
//! | D5 | `provides` in `Leaf`'s body, the binding in a `namespace Leaf` entry | every route | refused "backs no operation" | the binding |
//!
//! and a tie through a dictionary — defaulted since ZAWX9, body-less once D1 was mended — was
//! refused only when the call ran, where the call by name refuses it at load.
//!
//! One answer now, in four parts. `resolve_op_target_at` resolves a body-less operation by the
//! provider's suppliers as it resolves a defaulted one (the default only fills an empty set).
//! The dispatch's projection (`resolve_at_goal`) asks it, where it read the provider's table
//! row, which holds no binding. The backing check reads the provider's merged view of the spec
//! (§8.7, *One carrier declaring one spec twice*). And a dictionary a call builds from an
//! instance whose provider supplies an operation twice is refused at that call, at load — the
//! user, 2026-10-25: the tie is no error where provisions are written, since `default provides`
//! chooses between providers, but none can choose between two texts of one (WI-861), and the
//! dictionary is resolved at the call.
//!
//! BACK-OUTS, MEASURED over this file, `wi_zawx9_defaulted_dictionary_dispatch_test` and the
//! family `f-supplier-routes`, each alone, on one temporary build:
//!
//!  * K1 — `resolve_op_target_at`'s body-less branch the first-match `own.or_else(binding)`;
//!  * K2 — `resolve_at_goal` projecting through the provider's table row;
//!  * K3 — the backing check reading the provision's own bindings;
//!  * K4 — the construction not asking `instance_supplier_tie`;
//!  * K5 — the higher-kinded arm reading the provision's binding alone;
//!  * K6 — `resolve_nullary_result_carrier` reading the carrier's table row;
//!  * K7 — `spec_op_backed_by` asking an own-member row by its spec operation for a defaulted
//!    operation only (`Dictionary.ops`);
//!  * EQ — `resolve_at_goal`'s semantic-equality clause dropped.
//!
//! | row | fails under |
//! |---|---|
//! | `a_binding_alone_answers_a_receiverless_call_by_name` | K2 |
//! | `an_own_member_beside_a_binding_is_refused_by_name_without_a_receiver` | K1 K2 |
//! | `a_tie_through_a_dictionary_is_refused_where_the_dictionary_is_built` | K1 K4 |
//! | `the_dictionary_is_refused_whichever_operation_its_callee_dispatches` | K1 K4 |
//! | `a_tie_in_an_instance_a_condition_resolved_to_is_refused_too` | K1 K4 |
//! | `a_binding_in_a_namespace_entry_backs_the_provision_in_the_body` | K2 K3 |
//! | `a_result_only_operation_reaches_the_binding_its_carrier_writes` | K2 |
//! | `a_result_only_operation_with_a_parameter_left_open_reaches_the_binding` | K6 |
//! | `a_higher_kinded_carriers_member_beside_its_binding_is_refused` | K1 K5 |
//! | `wi_zawx9…::an_own_member_beside_a_binding_is_refused_where_the_dictionary_is_built` | K4 |
//! | `wi453_hk_concrete_fill_test::arg_carrier_dispatches_to_instance_impl` | K1 |
//! | `the_reflect_faces_agree_on_a_bodyless_tie` | K7 |
//! | `semantic_equality_is_left_to_its_builtin` | EQ |
//! | `wi625_eval_semantic_eq_test::eval_undecidable_instance_fact_eq_is_loud_not_false` | EQ (never returns) |
//! | the family `f-supplier-routes` | K1 (3 verdicts moved), K2 (4), K3 (6), K4 (4) |
//!
//! K1 fails the rows of the other parts too: every reader made to ask `resolve_op_target_at`
//! asks it. `wi453`'s row is the old chain's other wrong answer: `Option`'s table row for
//! `flatMap` is an operation it inherits, which beat its provision's binding.
//!
//! PASSES EITHER WAY BY DESIGN: `one_supplier_runs_on_every_route`, one supplier on every route.
//!
//! SEMANTIC EQUALITY KEEPS ITS OWN DISPATCH (`resolve_at_goal`): a call of `PartialEq.eq` is not
//! pinned to a provision's binding. Without that clause the workspace gate never finished, at
//! `wi625…`'s circular `loopEq(x, y) = eq(x, y)`, pinned to itself where the equality builtin's
//! bridge refuses it at its re-entry cap; `semantic_equality_is_left_to_its_builtin` fails at once.
//!
//! K5'S OTHER HALF IS UNOBSERVABLE, measured: the higher-kinded arm now pins a carrier's own
//! member where nothing binds the operation, and the dispatch reached the same member at run
//! time. A member whose effects would make the two differ is refused at its declaration
//! (`check_override_refinement`: effects must not widen).

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `Desc`, its operation `op` declared `decl` (with or without a default body), a `Leaf` that
/// provides it, `leaf_body` and `supply` written beside them, and the call written three ways
/// over `receiving` — `describe(x: T)` takes the carrier, `name()` takes nothing.
fn program(ns: &str, receiving: bool, defaulted: bool, leaf_body: &str, supply: &str) -> String {
    let default = if defaulted { " = 1" } else { "" };
    let (decl, via, by, through) = if receiving {
        (
            format!("operation describe(x: T) -> Int64{default}"),
            "operation viaDict[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)",
            "operation byName() -> Int64 = Desc.describe(leaf())",
            "operation throughDictionary() -> Int64 = viaDict(leaf())",
        )
    } else {
        (
            format!("operation name() -> Int64{default}"),
            "operation viaDict[A]() -> Int64 requires Desc[T = A] = Desc.name[T = A]()",
            "operation byName() -> Int64 = Desc.name[T = Leaf]()",
            "operation throughDictionary() -> Int64 = viaDict[A = Leaf]()",
        )
    };
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    {decl}
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
{leaf_body}  end
{supply}
  {via}
  {by}
  {through}
end
"#
    )
}

/// The binding a `namespace Leaf` entry writes: `other`, answering 3.
fn entry_binding(receiving: bool) -> &'static str {
    if receiving {
        "\n  operation other(x: Leaf) -> Int64 = 3\n\n  namespace Leaf\n    \
         provides Desc[T = Leaf, describe = other]\n  end\n"
    } else {
        "\n  operation other() -> Int64 = 3\n\n  namespace Leaf\n    \
         provides Desc[T = Leaf, name = other]\n  end\n"
    }
}

/// `Leaf`'s own member, answering 2.
fn own_member(receiving: bool) -> &'static str {
    if receiving {
        "    operation describe(x: Leaf) -> Int64 = 2\n"
    } else {
        "    operation name() -> Int64 = 2\n"
    }
}

fn op_of(receiving: bool) -> &'static str {
    if receiving {
        "describe"
    } else {
        "name"
    }
}

/// The program with one of its calls taken out, so a refusal of the other is that call's own.
fn without(src: &str, call: &str) -> String {
    src.lines()
        .filter(|l| !l.trim_start().starts_with(&format!("operation {call}()")))
        .collect::<Vec<_>>()
        .join("\n")
}

/// D3. The binding is the only supplier and the call names no carrier value, so nothing at
/// run time could find it: the call by name is pinned to it at load. It was left the spec
/// operation and died "operation has no body".
#[test]
fn a_binding_alone_answers_a_receiverless_call_by_name() {
    let ns = "test.k84m.d3";
    // The binding in `Leaf`'s own provision, as the family's `binding-in-body` writes it.
    let src = program(ns, false, false, "", "\n  operation other() -> Int64 = 3\n").replace(
        "provides Desc[T = Leaf]\n",
        "provides Desc[T = Leaf, name = other]\n",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.byName")), Ok(3));
    assert_eq!(run_int64(&src, &format!("{ns}.throughDictionary")), Ok(3));
}

/// D1 BY NAME, with no receiver: the member and the binding are both `Leaf`'s, and the call is
/// refused at load as the receiving shape always was. It answered the member's 2.
#[test]
fn an_own_member_beside_a_binding_is_refused_by_name_without_a_receiver() {
    let ns = "test.k84m.d1name";
    let src = without(
        &program(ns, false, false, own_member(false), entry_binding(false)),
        "throughDictionary",
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            &format!("ambiguous dispatch of `{ns}.Desc.name` on carrier `{ns}.Leaf`"),
            "the carrier's own member",
            "an instance fact binding `name = ",
        ],
        "a receiver-less call by name of a body-less operation supplied twice",
    );
}

/// D1 THROUGH A DICTIONARY, both shapes, both halves: refused at load where the dictionary is
/// built, `viaDict(leaf())`, in the words the call by name uses. The body-less one answered the
/// member's 2; the defaulted one loaded and was refused only when it ran.
#[test]
fn a_tie_through_a_dictionary_is_refused_where_the_dictionary_is_built() {
    for receiving in [false, true] {
        for defaulted in [false, true] {
            let ns = format!("test.k84m.d1dict{}{}", receiving as u8, defaulted as u8);
            let src = without(
                &program(
                    &ns,
                    receiving,
                    defaulted,
                    own_member(receiving),
                    entry_binding(receiving),
                ),
                "byName",
            );
            assert_refused_naming(
                &load_errors_of(&src),
                &[
                    &format!(
                        "ambiguous dispatch of `{ns}.Desc.{}` on carrier `{ns}.Leaf`",
                        op_of(receiving)
                    ),
                    "the carrier's own member",
                    "an instance fact binding",
                ],
                &format!("through a dictionary, receiving: {receiving}, defaulted: {defaulted}"),
            );
        }
    }
}

/// THE DICTIONARY IS REFUSED, NOT THE OPERATION THE BODY CALLS: `viaDict`'s body calls `tag`,
/// which `Leaf` supplies once, and `describe` — which it supplies twice — is no call of it. A
/// dictionary answers every operation of its spec, and nothing at the call site knows which its
/// callee dispatches. It answered `tag`'s 9.
#[test]
fn the_dictionary_is_refused_whichever_operation_its_callee_dispatches() {
    let ns = "test.k84m.unused";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
    operation tag(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 2
    operation tag(x: Leaf) -> Int64 = 9
  end
  operation other(x: Leaf) -> Int64 = 3
  namespace Leaf
    provides Desc[T = Leaf, describe = other]
  end
  operation viaDict[A](x: A) -> Int64 requires Desc[T = A] = Desc.tag(x)
  operation go() -> Int64 = viaDict(leaf())
end
"#
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[&format!(
            "ambiguous dispatch of `{ns}.Desc.describe` on carrier `{ns}.Leaf`"
        )],
        "a dictionary whose provider supplies another of its operations twice",
    );
}

/// A TIE INSIDE THE INSTANCE: `Wrap`'s provision holds on `Desc[T = V]`, and at `wrap(v:
/// leaf())` that condition is `Leaf`'s dictionary, which supplies `describe` twice. The
/// dictionary built for `Wrap` carries it, so the call building it is refused. It answered
/// `Wrap`'s own 10, the inner tie never dispatched.
#[test]
fn a_tie_in_an_instance_a_condition_resolved_to_is_refused_too() {
    let ns = "test.k84m.nested";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 2
  end
  operation other(x: Leaf) -> Int64 = 3
  namespace Leaf
    provides Desc[T = Leaf, describe = other]
  end
  sort Wrap
    sort V = ?
    entity wrap(v: V)
    provides Desc[T = Wrap[V = V]] :- Desc[T = V]
    operation describe(x: Wrap[V = V]) -> Int64 = 10
  end
  operation viaDict[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)
  operation go() -> Int64 = viaDict(wrap(v: leaf()))
end
"#
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[&format!(
            "ambiguous dispatch of `{ns}.Desc.describe` on carrier `{ns}.Leaf`"
        )],
        "a tie in the dictionary a provision's condition resolved to",
    );
}

/// D5. A provision written in `Leaf`'s body and its binding written in a `namespace Leaf` entry
/// are one view of `Desc` (§8.7), so the binding backs the provision, and every route runs it.
/// Body-less, the pair was refused "backs no operation"; defaulted, it always ran the binding.
#[test]
fn a_binding_in_a_namespace_entry_backs_the_provision_in_the_body() {
    for receiving in [false, true] {
        let ns = format!("test.k84m.d5{}", receiving as u8);
        let src = program(&ns, receiving, false, "", entry_binding(receiving));
        for call in ["byName", "throughDictionary"] {
            assert_eq!(
                run_int64(&src, &format!("{ns}.{call}")),
                Ok(3),
                "{call}, receiving: {receiving}"
            );
        }
    }
}

/// A RESULT-ONLY OPERATION reaches its binding: `Mk.make()` at an expected `Box` is resolved
/// from the carrier the type names (`resolve_nullary_result_carrier`), which read `Box`'s table
/// row and found no member. It loaded and died "operation has no body: Mk.make".
#[test]
fn a_result_only_operation_reaches_the_binding_its_carrier_writes() {
    let ns = "test.k84m.result";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, PartialEq}}
  sort Mk
    sort C = ?
    operation make() -> C
    operation size(c: C) -> Int64
  end
  sort Box
    entity small
    entity big
    provides Mk[C = Box, make = mkBox]
    operation size(c: Box) -> Int64 = if PartialEq.eq(c, big) then 7 else 1
  end
  operation mkBox() -> Box = big
  operation go() -> Int64 =
    let b: Box = Mk.make()
    Mk.size(b)
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

/// … AND WHERE THE CALL LEAVES ANOTHER PARAMETER OPEN, so the dispatch finds no candidate and
/// the carrier is read off the type expected of the result (`resolve_nullary_result_carrier`,
/// WI-508): that reader took `Box`'s table row too. It loaded and died "operation has no body:
/// Maker.make".
#[test]
fn a_result_only_operation_with_a_parameter_left_open_reaches_the_binding() {
    let ns = "test.k84m.result2";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, PartialEq}}
  sort Maker
    sort C = ?
    sort Element = ?
    operation make() -> C
  end
  sort Box
    entity small
    entity big
    provides Maker[C = Box, Element = Box, make = mkBox]
  end
  operation mkBox() -> Box = big
  operation go() -> Int64 =
    let b: Box = Maker.make()
    if PartialEq.eq(b, big) then 7 else 1
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7));
}

/// A HIGHER-KINDED CARRIER'S OWN MEMBER BESIDE ITS BINDING is the tie the call by name refuses
/// elsewhere: `CpsMonad.unit(42)` at `MyBox`, whose own `unit` and whose provision's `unit =
/// boxUnit` both supply it. The arm that reads such a carrier (WI-453) took the binding alone,
/// and the call ran it.
#[test]
fn a_higher_kinded_carriers_member_beside_its_binding_is_refused() {
    let ns = "test.k84m.hk";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64}}
  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
  end
  sort MyBox
    sort T = ?
    entity mybox(v: T)
    operation unit[A](a: A) -> MyBox[T = A] = mybox(v: a)
  end
  operation boxUnit[A](a: A) -> MyBox[T = A] = mybox(v: a)
  namespace MyBox
    provides CpsMonad[F = Self, unit = {ns}.boxUnit]
  end
  operation useResult() -> MyBox[T = Int64] = CpsMonad.unit(42)
end
"#
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            &format!("ambiguous dispatch of `{ns}.CpsMonad.unit` on carrier `{ns}.MyBox`"),
            "the carrier's own member",
            &format!("an instance fact binding `unit = {ns}.boxUnit`"),
        ],
        "a higher-kinded carrier supplying `unit` twice",
    );
}

/// THE TWO REFLECT FACES AGREE ON A BODY-LESS TIE: `Dictionary.resolveOp(d, Desc.name)` refuses
/// the member beside the binding, and so does `Dictionary.ops(d)`, which asks the member's row
/// by the spec operation it backs. It asked that only of a defaulted operation, and listed
/// `Leaf.name` (found by /code-review). The dictionary is made by hand: no call of this
/// program could build it, since the call that would is refused at load.
#[test]
fn the_reflect_faces_agree_on_a_bodyless_tie() {
    const DICT: &str = "anthill.realization.runtime.Dictionary";
    let ns = "test.k84m.reflect";
    let src = without(
        &without(
            &program(ns, false, false, own_member(false), entry_binding(false)),
            "byName",
        ),
        "throughDictionary",
    );
    let mut interp = crate::common::interp_for(&src);
    let leaf = interp
        .kb()
        .try_resolve_symbol(&format!("{ns}.Leaf"))
        .expect("Leaf");
    let d = crate::common::dict(&interp, leaf, []).into_value();
    let spec_op = crate::common::symbol_term(&mut interp, &format!("{ns}.Desc.name"));
    for (face, args) in [("resolveOp", vec![d.clone(), spec_op]), ("ops", vec![d])] {
        let err = interp
            .call(&format!("{DICT}.{face}"), &args)
            .expect_err("the provider supplies `name` twice");
        assert!(
            matches!(
                err,
                anthill_core::eval::EvalError::AmbiguousSpecOpDispatch { .. }
            ),
            "{face}: {err:?}"
        );
    }
}

/// SEMANTIC EQUALITY IS LEFT TO ITS BUILTIN, which dispatches itself: `PartialEq.eq(lp(v: 1),
/// lp(v: 1))` beside `provides PartialEq[T = Loop, eq = neverEq]` is answered by the builtin's
/// reflexivity, as before. MEASURED with `resolve_at_goal`'s equality clause backed out: the
/// call was pinned to `neverEq` and answered 0 — and a circular binding never returned
/// (`wi625_eval_semantic_eq_test::eval_undecidable_instance_fact_eq_is_loud_not_false`), which
/// this row reports as a failure where that one hangs.
#[test]
fn semantic_equality_is_left_to_its_builtin() {
    let ns = "test.k84m.eq";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  sort Loop
    entity lp(v: Int64)
  end
  operation neverEq(x: Loop, y: Loop) -> Bool = false
  namespace Loop
    provides PartialEq[T = Loop, eq = neverEq]
  end
  operation go() -> Int64 = if PartialEq.eq(lp(v: 1), lp(v: 1)) then 1 else 0
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(1));
}

/// CONTROLS, which pass either way by design: one supplier runs on every route — `Leaf`'s
/// member alone, a witness's member alone, and, for the shape that receives the carrier, the
/// binding alone in `Leaf`'s own provision, which a call reached by the value it dispatches on.
#[test]
fn one_supplier_runs_on_every_route() {
    let ns = "test.k84m.c";
    for receiving in [false, true] {
        let witness = if receiving {
            "\n  sort W\n    provides Desc[T = Leaf]\n    operation describe(x: Leaf) -> Int64 = 4\n  end\n"
        } else {
            "\n  sort W\n    provides Desc[T = Leaf]\n    operation name() -> Int64 = 4\n  end\n"
        };
        let mut cases: Vec<(&str, String, i64)> = vec![
            (
                "own",
                program(ns, receiving, false, own_member(receiving), ""),
                2,
            ),
            (
                "witness",
                program(ns, receiving, false, "", witness)
                    .replace("    provides Desc[T = Leaf]\n  end", "  end"),
                4,
            ),
        ];
        if receiving {
            cases.push((
                "binding",
                program(
                    ns,
                    true,
                    false,
                    "",
                    "\n  operation other(x: Leaf) -> Int64 = 3\n",
                )
                .replace(
                    "provides Desc[T = Leaf]\n",
                    "provides Desc[T = Leaf, describe = other]\n",
                ),
                3,
            ));
        }
        for (what, src, want) in cases {
            for call in ["byName", "throughDictionary"] {
                assert_eq!(
                    run_int64(&src, &format!("{ns}.{call}")),
                    Ok(want),
                    "{what}, {call}, receiving: {receiving}"
                );
            }
        }
    }
}
