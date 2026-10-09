//! A type that holds a value (`Foo[T = Int64, N = 3]`) is not a hash-consed term: it rides
//! an occurrence, and a type applied to one (`Bag[T = Foo[T = Int64, N = 3]]` once a
//! substitution put it there) an entity. Four readers in the typer answered for the term
//! carrier alone, and each gave such a type a different verdict from its term twin.
//!
//! THE RULE. A reader of a type gives one answer for the type, whichever carrier it rides.
//!
//! BEFORE, each measured:
//!
//!   * `Bag.merge(a, b)` over `merge(a: Self, b: Self)`, with `a: Bag[T = Foo[T = Int64, N
//!     = 3]]` and `b: Bag[T = Foo[T = String, N = 3]]`, LOADED, and so did `both[A](x:
//!     Bag[T = A], y: Bag[T = A])` given the same two bags. The second argument is compared
//!     with what the first bound, which the substitution hands back as an entity; "does
//!     this type contain a function type" answered yes for an entity, as for anything it
//!     could not read, and the comparison was withheld as a callable's.
//!   * `takePair((a: red(v: 7), b: mk(2)))` over `p: (a: Colour.red, b: Foo[T = Int64, N =
//!     3])` was REFUSED, "expected (a: red, …), got (a: Colour, …)": the hint that types
//!     `red(v: 7)` at its variant looked for a constructor name in a term only.
//!   * a `requires` shadow whose parameter types differ WARNED as confusable when the
//!     parameter held a value: the comparison was made on terms and fell open off them.
//!   * `Sp.each(Car.car(1), lambda q -> mk(q.n))` over `each(s: Self, f: (q: T) -> Foo[T =
//!     Int64, N = 3])` was REFUSED, "Sp.T.n: … no such member": the gate that types a
//!     receiver before the lambda it hints read a callback's type as a term only.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   an entity read by `type_contains_callable` (answering `true` for it) — FAIL:
//!     two_instances_at_types_holding_a_value_are_held_to_one
//!     an_operations_own_parameter_at_types_holding_a_value_is_held_to_one
//!   the variant hint off the term carrier (`type_mentions_an_entity` answering `false`)
//!   — FAIL:
//!     a_tuple_component_keeps_its_variant_beside_a_type_holding_a_value
//!   the shadow comparison on terms alone (`requires_shadow_is_confusable` skipping a
//!   type that is no term) — FAIL:
//!     a_shadow_whose_parameter_types_differ_is_not_confusable
//!   a value in a type read as a proof of difference (`types_definitely_differ` without
//!   its `Denoted` arm) — FAIL:
//!     a_shadow_over_callbacks_naming_their_own_parameter_still_warns
//!     a_shadow_over_rows_written_in_another_order_still_warns
//!   a row compared child by child (`types_definitely_differ` without its row arm) — FAIL:
//!     a_shadow_over_rows_written_in_another_order_still_warns
//!   the staging gate off the term carrier (`type_mentions_op_tp` answering `false`) —
//!   FAIL:
//!     a_lambda_is_hinted_from_a_computed_receiver_beside_a_type_holding_a_value
//!     a_lambda_is_hinted_from_a_computed_sibling_beside_a_dependent_absence
//!
//!   The two `still_warns` rows above also pass with the shadow comparison on terms alone,
//!   where such a type was never compared: they guard the comparison this change adds.
//!
//!   PASS EITHER WAY, by design:
//!     two_instances_at_one_type_holding_a_value_conform — the fence: what must keep
//!       loading, and running.
//!     a_shadow_whose_parameter_types_agree_still_warns — the other direction of the
//!       shadow comparison.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of, load_outcome};

fn source(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Int64, String, Bool, List, Modify, Effect}}
  sort Foo
    sort T = ?
    sort N = ?
    entity foo(v: T)
  end
  operation mk(x: Int64) -> Foo[T = Int64, N = 3] = foo(v: x)
  sort Bag
    sort T = ?
    entity bag(items: List[T = T])
    operation merge(a: Self, b: Self) -> Self = a
    operation size(a: Self) -> Int64 =
      match a
        case bag(xs) -> List.length(xs)
  end
  sort Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
{body}
end
"#
    )
}

/// Load, call `test.<ns>.go()`, and hand back the integer it answers.
fn run(ns: &str, body: &str) -> i64 {
    let mut interp = interp_for(&source(ns, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The one refusal of a source that must not load.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
    errs.into_iter().next().unwrap()
}

/// The shadow warnings a clean load reports about `test.<ns>`.
fn shadow_warnings(ns: &str, body: &str) -> Vec<String> {
    load_outcome(&source(ns, body))
        .rendered_warnings()
        .unwrap_or_else(|errs| panic!("{ns}: a shadow is advisory, the load is clean: {errs:#?}"))
        .into_iter()
        .filter(|w| w.contains(&format!("test.{ns}")))
        .collect()
}

const TWO_BAGS: &str =
    "a: Bag[T = Foo[T = Int64, N = 3]], b: Bag[T = Foo[T = String, N = 3]]";

// ── one instance per call ───────────────────────────────────────────────────

/// `merge(a: Self, b: Self)` takes two bags of ONE element type, also when that type holds
/// a value.
#[test]
fn two_instances_at_types_holding_a_value_are_held_to_one() {
    let refused = refusal(
        "vhself",
        &format!("  operation go({TWO_BAGS}) -> Int64 = Bag.size(Bag.merge(a, b))"),
    );
    assert!(
        refused.contains(
            "merge.b (op-arg): expected Bag[T = Foo[T = Int64, N = 3]], got Bag[T = Foo[T = \
             String, N = 3]]"
        ),
        "{refused}"
    );
}

/// … and so does an operation's own type parameter, which the substitution reaches by
/// another road.
#[test]
fn an_operations_own_parameter_at_types_holding_a_value_is_held_to_one() {
    let refused = refusal(
        "vhown",
        &format!(
            "  operation both[A](x: Bag[T = A], y: Bag[T = A]) -> Int64 = Bag.size(x)\n  \
             operation go({TWO_BAGS}) -> Int64 = both(a, b)"
        ),
    );
    assert!(
        refused.contains("both.y (op-arg): expected Bag[T = Foo[T = Int64, N = 3]]"),
        "{refused}"
    );
}

/// Two bags at one such type conform, through `Self` and through the operation's own
/// parameter, and the call runs.
#[test]
fn two_instances_at_one_type_holding_a_value_conform() {
    let both = "  operation both[A](x: Bag[T = A], y: Bag[T = A]) -> Int64 = Bag.size(y)\n";
    for (name, call, answer) in [
        ("self", "Bag.size(Bag.merge(bag(items: [mk(1)]), bag(items: [mk(2), mk(3)])))", 1),
        ("own", "both(bag(items: [mk(1)]), bag(items: [mk(2), mk(3)]))", 2),
    ] {
        let ns = format!("vhsame{name}");
        assert_eq!(run(&ns, &format!("{both}  operation go() -> Int64 = {call}")), answer, "{ns}");
    }
}

// ── the variant hint ────────────────────────────────────────────────────────

/// A tuple literal's component is typed at the variant its slot names, also when a sibling
/// component's type holds a value; a constructor of another variant is still refused.
#[test]
fn a_tuple_component_keeps_its_variant_beside_a_type_holding_a_value() {
    let take = "  operation takePair(p: (a: Colour.red, b: Foo[T = Int64, N = 3])) -> Int64 = p.a.v\n";
    assert_eq!(
        run("vhtuple", &format!("{take}  operation go() -> Int64 = takePair((a: red(v: 7), b: mk(2)))")),
        7
    );
    let refused = refusal(
        "vhtupleblue",
        &format!("{take}  operation go() -> Int64 = takePair((a: blue(v: 7), b: mk(2)))"),
    );
    assert!(refused.contains("takePair.p (op-arg)") && refused.contains("blue"), "{refused}");
}

// ── the shadow warning ──────────────────────────────────────────────────────

/// `BReq.b_op` beside the `BSpec.b_op` its `requires` brings in, `tag` typed `local`.
fn shadow(local: &str) -> String {
    format!(
        "  sort BSpec\n    sort T = ?\n    operation b_op(x: T, tag: Foo[T = Int64, N = 3]) -> T\n  end\n  \
         sort BCarrier\n    entity bc(id: Int64)\n  end\n  \
         sort BReq\n    requires BSpec[T = BCarrier]\n    \
         operation b_op(x: BCarrier, tag: {local}) -> BCarrier = x\n  end"
    )
}

/// Two operations whose parameter types differ cannot be confused at a call site, and are
/// not reported, also when the parameter's type holds a value.
#[test]
fn a_shadow_whose_parameter_types_differ_is_not_confusable() {
    let warnings = shadow_warnings("vhshadowdiff", &shadow("Foo[T = String, N = 3]"));
    assert!(warnings.is_empty(), "{warnings:#?}");
}

/// The same parameter type on both is the collision the warning is for.
#[test]
fn a_shadow_whose_parameter_types_agree_still_warns() {
    let warnings = shadow_warnings("vhshadowsame", &shadow("Foo[T = Int64, N = 3]"));
    assert_eq!(warnings.len(), 1, "{warnings:#?}");
    assert!(warnings[0].contains("shadows the inherited"), "{}", warnings[0]);
}

/// Two callbacks whose rows each name their OWN operation's parameter agree: `Modify[c]`
/// is one type in both, although the two `c` are two parameters. A value in a type is no
/// proof of a difference.
#[test]
fn a_shadow_over_callbacks_naming_their_own_parameter_still_warns() {
    let own_place = "  sort Cell\n    entity cell(n: Int64)\n  end\n  \
         sort CSpec\n    sort T = ?\n    \
         operation c_op(c: Cell, k: (x: Int64) -> Int64 @ {Modify[c]}) -> Int64\n  end\n  \
         sort CCarrier\n    entity cc(id: Int64)\n  end\n  \
         sort CReq\n    requires CSpec[T = CCarrier]\n    \
         operation c_op(c: Cell, k: (x: Int64) -> Int64 @ {Modify[c]}) -> Int64 = 1\n  end";
    let warnings = shadow_warnings("vhshadowplace", own_place);
    assert_eq!(warnings.len(), 1, "{warnings:#?}");
}

/// … and so do two rows that list the same labels in another order: a row is a set.
#[test]
fn a_shadow_over_rows_written_in_another_order_still_warns() {
    let rows = |local: &str| {
        format!(
            "  sort Boom\n    entity bang\n  end\n  namespace Boom\n    provides Effect[T = Boom]\n  end\n  \
             sort Cell\n    entity cell(n: Int64)\n  end\n  \
             sort RSpec\n    sort T = ?\n    \
             operation r_op(c: Cell, k: (x: Int64) -> Int64 @ {{Modify[c], Boom}}) -> Int64\n  end\n  \
             sort RCarrier\n    entity rc(id: Int64)\n  end\n  \
             sort RReq\n    requires RSpec[T = RCarrier]\n    \
             operation r_op(c: Cell, k: (x: Int64) -> Int64 @ {{{local}}}) -> Int64 = 1\n  end"
        )
    };
    for (name, local) in [("same", "Modify[c], Boom"), ("swapped", "Boom, Modify[c]")] {
        let ns = format!("vhshadowrow{name}");
        let warnings = shadow_warnings(&ns, &rows(local));
        assert_eq!(warnings.len(), 1, "{ns}: {warnings:#?}");
    }
}

// ── the receiver before the lambda ──────────────────────────────────────────

/// A lambda's parameter is typed from what the receiver's provision binds, also when the
/// receiver is computed and the callback's type holds a value.
#[test]
fn a_lambda_is_hinted_from_a_computed_receiver_beside_a_type_holding_a_value() {
    let decls = "  sort Rec\n    entity rec(n: Int64)\n  end\n  \
                 sort Sp[T]\n    operation each(s: Self, f: (q: T) -> Foo[T = Int64, N = 3]) -> Int64\n  end\n  \
                 sort Car[A]\n    entity car(a: A)\n    provides Sp[T = Rec]\n    \
                 operation each(s: Car[A], f: (q: Rec) -> Foo[T = Int64, N = 3]) -> Int64 = f(rec(n: 4)).v\n  end\n";
    assert_eq!(
        run(
            "vhhint",
            &format!("{decls}  operation go() -> Int64 = Sp.each(Car.car(1), lambda q -> mk(q.n))")
        ),
        4
    );
}

/// … and from a computed sibling that pins the operation's own type parameter, where the
/// callback's row holds an absence over its own binder.
#[test]
fn a_lambda_is_hinted_from_a_computed_sibling_beside_a_dependent_absence() {
    let decls = "  sort Rec\n    entity rec(n: Int64)\n  end\n  \
                 sort Wrap\n    sort A = ?\n    entity wrap(a: A)\n  end\n  \
                 operation mkWrap() -> Wrap[A = Rec] = wrap(a: rec(n: 9))\n  \
                 operation apply[X, EffP](w: Wrap[A = X], f: (x: X) -> Int64 @ {EffP, -Modify[x]}) -> Int64 effects {EffP} =\n    \
                 match w\n      case wrap(a) -> f(a)\n";
    assert_eq!(
        run("vhhintabsence", &format!("{decls}  operation go() -> Int64 = apply(mkWrap(), lambda x -> x.n)")),
        9
    );
}
