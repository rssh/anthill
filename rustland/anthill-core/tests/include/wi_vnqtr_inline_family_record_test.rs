//! WI-20260911-VNQTR — THE OPERATION'S RECORD LISTS THE VARIABLES ITS SIGNATURE WRITES INLINE,
//! so a reader of "the operation's own type parameters" reads `?t` as it reads `[T]`.
//!
//! §5.4 quantifies a variable written in a parameter type exactly as an `[A]` binder. The
//! body check knew it (WI-1FKR2); the record did not: it listed the brackets and the
//! parameters the member sugar mints, and each reader that asks the record which parameters
//! an operation has gave the two spellings of one signature two verdicts. The loader now
//! mints such a variable under a name of its own (`KnowledgeBase::mint_inline_param_name`)
//! and lists it after the members; a call's bracket still cannot bind it
//! (`op_info::bracket_type_params`). Each row sets the inline spelling beside its bracketed
//! twin, which was already right.
//!
//! BACK-OUTS, temporary switches in one build, over the whole `wi_tests` binary (7552 rows):
//!
//! * **the record without the inline family** (the loader minting the variables and not
//!   listing them): **9 red** here — every row but
//!   [`an_inline_variable_read_as_a_value_is_read_through_its_clause`] and
//!   [`a_bracket_cannot_bind_an_inline_variable`], which the next two switches own.
//! * **the name off** (an inline variable minted under the plain name it is written with):
//!   **4 red** here — [`a_bracket_cannot_bind_an_inline_variable`],
//!   [`an_unconstrained_inline_variable_is_refused_without_a_bracket_to_advise`],
//!   [`an_inline_variable_read_as_a_value_is_read_through_its_clause`] and
//!   [`the_diagnostics_spell_an_inline_variable_as_written`].
//! * **the value read off** (a body's `?t` not lowered to its slot, nor counted as a read):
//!   **1 red**, [`an_inline_variable_read_as_a_value_is_read_through_its_clause`].

use crate::common::{load_errors_of, replace_in_fixture};
use crate::wi_vnqtr_inline_param_forward_test::{answers, the_one_refusal};

/// Two arguments that bind one variable are joined, as a bracket's are. `same(c, s)` with `c:
/// Circle` (which provides `Shape`) and `s: Shape` took `?a` from the first and refused the
/// second, where `same(s, c)` loaded: the typing depended on the arguments' order.
#[test]
fn the_arguments_that_bind_an_inline_variable_are_joined() {
    let src = r#"
namespace test.vnqtr.join
  import anthill.prelude.{Int64}
  sort Shape
  end
  sort Circle
    provides Shape
    entity circle
  end
  operation same(x: ?a, y: ?a) -> Int64 = 1
  operation cs(c: Circle, s: Shape) -> Int64 = same(c, s)
  operation sc(c: Circle, s: Shape) -> Int64 = same(s, c)
  operation go() -> Int64 = cs(circle(), circle()) + sc(circle(), circle())
end
"#;
    assert_eq!(answers(src, &["test.vnqtr.join.go"]), ["2"]);
}

/// A provider's member written with an inline variable has it bound at a call dispatched to
/// it, as a bracketed member's is: `Sp.op(x, "str")` reached `Car.op(c: Self, w: ?w)` with
/// `?w` unbound, and its `Error[?w]` was "undeclared" in a caller declaring `Error[String]`.
#[test]
fn a_members_inline_variable_is_bound_at_a_dispatched_call() {
    let src = r#"
namespace test.vnqtr.disp
  import anthill.prelude.{Int64, String, Error}
  sort Sp
    sort T = ?
    effects E = ?
    operation op[U](s: Self, w: U) -> Int64 effects {s.E, Error[U]}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation op(c: Self, w: ?w) -> Int64 effects {EC, Error[?w]} = 1
  end
  operation via[R](x: Car[V = Int64, EC = R]) -> Int64 effects {R, Error[String]} = Sp.op(x, "str")
  operation go() -> Int64 effects {Error[String]} = via[R = {}](car(v: 1))
end
"#;
    assert_eq!(answers(src, &["test.vnqtr.disp.go"]), ["1"]);
}

/// A lambda's parameter typed by an inline variable is typed through the sibling argument
/// that binds it, as a bracket's is: `app(lambda (q) -> q.n, foo(n: 1))` read `q.n` on an
/// unresolved receiver.
#[test]
fn a_lambda_is_typed_through_the_sibling_that_binds_its_inline_variable() {
    let src = r#"
namespace test.vnqtr.hint
  import anthill.prelude.{Int64}
  sort Foo
    entity foo(n: Int64)
  end
  operation app(f: (q: ?t) -> Int64, x: ?t) -> Int64 = f(x)
  operation go() -> Int64 = app(lambda (q) -> q.n, foo(n: 41))
end
"#;
    assert_eq!(answers(src, &["test.vnqtr.hint.go"]), ["41"]);
}

/// A handler's row tail written inline is bound to what the body leaves, as a bracketed
/// `Rho` is: with `?rho` the residual of a body that performs no `Error` was "undeclared
/// effect: ?rho".
#[test]
fn a_handlers_inline_row_tail_takes_what_the_body_leaves() {
    let src = r#"
namespace test.vnqtr.tail
  import anthill.prelude.{Int64, Error, Clock}
  operation pure_body() -> Int64 effects {} = 7
  operation clocked() -> Int64 effects {Clock} = 5
  operation handle_Error(body: () -> Int64 @ {Error[Int64], ?rho}) -> Int64 effects {?rho} = 0
  operation t1() -> Int64 effects {} = handle_Error(lambda () -> pure_body())
  operation t2() -> Int64 effects {Clock} = handle_Error(lambda () -> clocked())
end
"#;
    assert_eq!(load_errors_of(src), Vec::<String>::new());
    assert_eq!(answers(src, &["test.vnqtr.tail.t1"]), ["0"]);
}

/// The elements of a list literal at a slot an inline variable names are joined, as at a
/// bracket's: `fixedX(xs: List[T = Sp[T = ?x]], w: ?x)` took a `Car` (an `Sp[T = Int64]`)
/// beside a `Bike` (an `Sp[T = String]`), one `?x` standing for two types. One provision's
/// elements still answer. (`w` fixes `?x`: nothing infers a variable through a provision,
/// and without it the call is refused "unconstrained" in either spelling.)
#[test]
fn a_list_literal_at_an_inline_variable_is_one_type() {
    let src = r#"
namespace test.vnqtr.lit
  import anthill.prelude.{Int64, List, String}
  sort Sp
    sort T = ?
    operation size(s: Sp) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp[T = Int64]
    operation size(c: Car) -> Int64 = 40
  end
  sort Bike
    entity bike(n: Int64)
    provides Sp[T = String]
    operation size(b: Bike) -> Int64 = 5
  end
  operation fixedX(xs: List[T = Sp[T = ?x]], w: ?x) -> Int64 = List.length(xs)
  operation cars() -> Int64 = fixedX([car(n: 1), car(n: 2)], 5)
  operation mixed() -> Int64 = fixedX([car(n: 1), bike(n: 2)], 5)
end
"#;
    the_one_refusal(src, &["collection-element-join", "expected Car, got Bike"]);
    let ok = replace_in_fixture(src, "  operation mixed() -> Int64 = fixedX([car(n: 1), bike(n: 2)], 5)\n", "");
    assert_eq!(answers(&ok, &["test.vnqtr.lit.cars"]), ["2"]);
}

/// An inline variable nothing at a call fixes is refused, as a bracket's is, and the advice
/// names no bracket: none can name `?t`. A typed argument fixes it, and the call answers.
#[test]
fn an_unconstrained_inline_variable_is_refused_without_a_bracket_to_advise() {
    let src = r#"
namespace test.vnqtr.unc
  import anthill.prelude.{Int64, List, nil}
  operation hd(xs: List[T = ?t], d: Int64) -> Int64 = d
  operation q() -> Int64 = hd(nil, 3)
end
"#;
    let e = the_one_refusal(src, &["a type for '?t'", "no bracket names a variable the signature writes"]);
    assert!(!e.contains("hd[?t"), "no bracket can bind `?t`, so none is advised: {e}");
    let typed = replace_in_fixture(
        src,
        "operation q() -> Int64 = hd(nil, 3)",
        "operation q() -> Int64 =\n    let xs: List[T = Int64] = nil\n    hd(xs, 3)",
    );
    assert_eq!(answers(&typed, &["test.vnqtr.unc.q"]), ["3"]);
}

/// A provider that widens the row a spec operation writes inline is refused, as at a
/// bracketed row: the check treated `?r` as an unknown spec parameter and was skipped for
/// the whole row, so `run(…) effects {?r, Eff2}` provided `run(…) effects {?r}`.
#[test]
fn a_provider_widening_an_inline_row_is_refused() {
    let src = r#"
namespace test.vnqtr.widen
  import anthill.prelude.{Effect, Int64}
  sort Eff2 end
  namespace Eff2
    provides Effect[T = Eff2]
  end
  sort Runner
    sort C = ?
    operation run(self: C, f: () -> Int64 @ {?r}) -> Int64 effects {?r}
  end
  sort Mine
    entity mine(n: Int64)
    provides Runner[C = Mine]
    operation run(self: Mine, f: () -> Int64 @ {?r}) -> Int64 effects {?r, Eff2} = f()
  end
end
"#;
    the_one_refusal(src, &["does not refine it", "effects must not widen"]);
}

/// An inline variable read as a VALUE is read through its `TypeValue` clause, as a bracket's
/// `U` is, and without the clause the read is refused at load naming it. It loaded and died
/// "unknown operation: t", the clause written or not.
#[test]
fn an_inline_variable_read_as_a_value_is_read_through_its_clause() {
    let src = r#"
namespace test.vnqtr.read
  import anthill.prelude.{Cell, Int64, List, Type}
  import anthill.reflect.{TypeValue}
  operation m(y: ?t) -> Type requires TypeValue[T = ?t] = Cell[V = ?t]
  operation bare(y: ?t) -> Type requires TypeValue[T = ?t] = ?t
  operation one() -> Type = m(1)
  operation two() -> Type = bare("s")
end
"#;
    assert_eq!(
        answers(src, &["test.vnqtr.read.one", "test.vnqtr.read.two"]),
        ["Cell(V: Int64)", "String"]
    );
    let unbacked = replace_in_fixture(
        src,
        "operation bare(y: ?t) -> Type requires TypeValue[T = ?t] = ?t",
        "operation bare(y: ?t) -> Type = ?t",
    );
    the_one_refusal(&unbacked, &["`requires anthill.reflect.TypeValue[T = ?t]`", "read as a VALUE"]);
}

/// A provider's member written with an inline variable restates the spec operation's clause
/// over its own: the member's variable pairs with the spec's, as `d[W]` pairs with `d[U]`.
/// The clause was refused as strengthening the precondition.
#[test]
fn a_member_restates_the_specs_clause_over_its_inline_variable() {
    let src = r#"
namespace test.vnqtr.member
  import anthill.prelude.{Cell, Int64, Type}
  import anthill.reflect.{TypeValue}
  operation tyOf[T](x: T) -> Type requires TypeValue[T = T] = Cell[V = T]
  sort Desc
    sort T = ?
    operation d(x: T, y: ?t) -> Type requires TypeValue[T = ?t]
  end
  sort Leaf
    entity leaf(n: Int64)
    provides Desc[T = Leaf]
    operation d(x: Leaf, y: ?t) -> Type requires TypeValue[T = ?t] = tyOf(y)
  end
  operation go() -> Type = Desc.d(leaf(n: 1), 5)
end
"#;
    assert_eq!(answers(src, &["test.vnqtr.member.go"]), ["Cell(V: Int64)"]);
}

/// The diagnostics that name a caller's parameter print an inline one as written, so what
/// they advise can be pasted: a construction's requirement over a member's parameter beside
/// it (`Pair2[A = ?t, B = Tagger.C]`), a projection off a requirement (`Coll[C =
/// ?t].Element`), and a named slot bound to it, which has no declaration to put a slot on.
#[test]
fn the_diagnostics_spell_an_inline_variable_as_written() {
    let construction = r#"
namespace test.vnqtr.say1
  import anthill.prelude.{Int64}
  sort Tagger
    sort C = ?
    effects E = ?
    operation tag(self: C) -> Int64 effects {E}
  end
  sort Pair2
    sort A = ?
    sort B = ?
    operation both(a: A, b: B) -> Int64
  end
  sort Box2
    sort T = ?
    sort S = ?
    requires Pair2[A = T, B = S]
    entity box2(a: T, b: S)
  end
  operation f(x: ?t, w: Tagger.C) -> Int64 =
    let b = box2(a: x, b: w)
    1
end
"#;
    let e = the_one_refusal(construction, &["requires test.vnqtr.say1.Pair2[A = ?t, B = Tagger.C]"]);
    assert!(!e.contains("A = t,"), "a variable is printed as written: {e}");

    let label = r#"
namespace test.vnqtr.say2
  import anthill.prelude.{Int64}
  sort Coll
    sort C = ?
    sort Element = ?
    operation first(c: C) -> Element
  end
  operation f(x: ?t) -> Int64 requires Coll[C = ?t] = Coll.first(x)
end
"#;
    the_one_refusal(label, &["Coll[C = ?t].Element"]);

    let slot = r#"
namespace test.vnqtr.say3
  import anthill.prelude.{Int64, String, WeakOrd, SortedSet}
  import anthill.prelude.String.{length}
  import anthill.prelude.Numeric.{sub}
  sort ByLength
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
  operation addI(s: SortedSet[T = String, O = ?p], x: String) -> SortedSet[T = String, O = ?p] =
    SortedSet.insert(s, x)
end
"#;
    let e = the_one_refusal(slot, &["`?p` is a variable the signature writes"]);
    assert!(!e.contains("requires ?p:"), "a slot binder must be a name a declaration has: {e}");
}

/// A call's bracket binds the parameters the bracket declares, and a variable written inline
/// is not one of them: `op_info::bracket_type_params` leaves it out. By position there is no
/// place for it — `hd[Int64](…)` over-applies an operation whose bracket declares none, and
/// `hd2[Int64, String](…)` one that declares one — and by name its key is no key: its name
/// is its own, and minted under the plain `t` it was a bracket target that `hd[t = Int64]`
/// bound.
#[test]
fn a_bracket_cannot_bind_an_inline_variable() {
    let src = r#"
namespace test.vnqtr.bracket
  import anthill.prelude.{Int64, String, List, nil}
  operation hd(xs: List[T = ?t], d: Int64) -> Int64 = d
  operation hd2[A](xs: List[T = ?t], d: A) -> A = d
  operation q() -> Int64 = hd[Int64](nil, 3)
  operation q2() -> Int64 = hd2[Int64, String](nil, 3)
  operation q3() -> Int64 = hd[t = Int64](nil, 3)
end
"#;
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 3, "one refusal per call: {errs:#?}");
    assert!(errs[0].contains("expected at most 0 positional type argument(s), got 1"), "{errs:#?}");
    assert!(errs[1].contains("expected at most 1 positional type argument(s), got 2"), "{errs:#?}");
    assert!(errs[2].contains("unknown type-param 't'"), "{errs:#?}");
}
