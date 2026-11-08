//! WI-20261105-89J6K (proposal 073 stage 2) — EVERY CALL PASSES WHAT ITS CALLEE READS. No
//! operation's own requirement slot is filled from argument values when its body is entered:
//! the fill that did it (`fill_missing_op_scoped_slots`, at `enter_operation`, the bridge's
//! dispatched-through path and the host raise) is gone, and each case it served has its
//! dictionary from the call, built at load, or from a host's entry. Measured on 4b97d746
//! with the fill switched off: 29 of 11,809 rows failed — 19 raises, 4 requirements fixed in
//! part, 4 spec bodies, 2 function values; the 48 rows that got an effect row's slot from it
//! passed, nothing reading the slot.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT — measured 2026-11-08, one at a time ──
//!
//! * A host's call of a builtin given its op-scoped slots (`Interpreter::call_op_sym`):
//!   [`a_host_call_of_a_raising_builtin_is_passed_its_type_value`].
//! * `type_value_of` composing the value's `TypeValue` at its entry:
//!   [`a_handler_reads_a_values_type_value_off_its_type`].
//! * A spec body entered through a provider's dictionary given the provision's slots
//!   (`push_spec_body_slots`, `kb::typing::spec_body_supply`):
//!   [`a_provision_passes_the_requirement_of_a_spec_body_it_takes`].
//! * A requirement fixed in part completed by §8.7's order (`dep_completed_by_provisions`):
//!   [`a_requirement_fixed_in_part_takes_the_provision_that_answers_it`],
//!   [`two_provisions_neither_more_specific_are_refused_at_load`].
//! * A construction's instance given to a function value in an arrow field
//!   (`ctor_arg_unlocks_a_field_hint`), and a function value held in a construction or a
//!   literal staging its sibling (`arg_holds_function_value`): each alone,
//!   [`a_function_value_is_typed_at_the_instance_its_call_fixes`].
//! * A spec member taken as a function value read as its calling lambda
//!   (`spec_member_as_lambda`): [`a_spec_member_taken_as_a_function_value_is_its_call_at_the_instance`].
//! * A requirement leaving a slot unwritten held to cover a call that fixes it at a type of
//!   its own (`slot_the_call_fixes_and_the_entry_leaves`, read by the deferral match and by
//!   `reached_carrier_matches_call`): [`a_body_using_an_unwritten_slot_at_a_type_of_its_own_is_refused`]
//!   (beside `Both` it loads clean).
//! * The effect row's anchor left out of the requires tree (`build_requires_tree`): every row
//!   — the stdlib no longer loads, the anchor reaching the resolver as a requirement nothing
//!   provides (its structural leaves went with the slot).

use crate::common::{assert_refused_naming, interp_for, load_errors_of, load_kb_with, query_unary, run_int64, show_value};
use anthill_core::eval::{EvalError, Value};

// ── (1) An operation used as a function value is the lambda that calls it ─────────────────

/// `tyOf`'s `B` is open where it is named and fixed later in the same call — by `apply`'s
/// parameter `H[A = Int64]`, by the sibling `"s"`, by `5` — and the function value is typed
/// there, its `TypeValue[T = B]` built at load. The lambda that calls it is the same value.
const LATER: &str = r#"
namespace test.j6k.later
  import anthill.prelude.{Cell, Int64, String, Type, List, Option, cons, nil, some, none}
  import anthill.reflect.{TypeValue}
  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
  sort H[A]
    entity h(f: (x: A) -> Type)
  end
  operation apply(v: H[A = Int64]) -> Type =
    match v
      case h(g) -> g(1)
  operation applyO[X](y: X, o: Option[T = (x: X) -> Type]) -> Type =
    match o
      case some(g) -> g(y)
      case none() -> Int64
  operation applyL[X](y: X, gs: List[T = (x: X) -> Type]) -> Type =
    match gs
      case cons(g, rest) -> g(y)
      case nil() -> Int64
  operation inCtor() -> Type = apply(h(f: tyOf))
  operation inOption() -> Type = applyO("s", some(tyOf))
  operation inList() -> Type = applyL(5, [tyOf])
  operation inCtorL() -> Type = apply(h(f: lambda (x) -> tyOf(x)))
  operation inOptionL() -> Type = applyO("s", some(lambda (x) -> tyOf(x)))
  operation inListL() -> Type = applyL(5, [lambda (x) -> tyOf(x)])
end
"#;

#[test]
fn a_function_value_is_typed_at_the_instance_its_call_fixes() {
    let mut interp = interp_for(LATER);
    let got: Vec<(String, String)> = ["inCtor", "inOption", "inList", "inCtorL", "inOptionL", "inListL"]
        .iter()
        .map(|op| {
            let v = match interp.call(&format!("test.j6k.later.{op}"), &[]) {
                Ok(v) => show_value(interp.kb(), &v),
                Err(e) => format!("{e:?}"),
            };
            (op.to_string(), v)
        })
        .collect();
    let want = [
        ("inCtor", "Cell[V = Int64]"),
        ("inOption", "Cell[V = String]"),
        ("inList", "Cell[V = Int64]"),
        ("inCtorL", "Cell[V = Int64]"),
        ("inOptionL", "Cell[V = String]"),
        ("inListL", "Cell[V = Int64]"),
    ];
    let wrong: Vec<_> = got
        .iter()
        .zip(want)
        .filter(|((_, g), (_, w))| g != w)
        .collect();
    assert!(wrong.is_empty(), "each spelling answers at its instance; got {got:?}");
}

/// A spec's member taken as a function value through the spec application is the lambda that
/// calls it at that instance: `Additive[T = Int64].zero` where `() -> Int64` is expected is
/// `lambda () -> Additive[T = Int64].zero()`, as `Int64.zero` is; in a generic body
/// `Additive[T = X].zero` is that call through the caller's `Additive[T = X]`, applied or not.
/// Refused "expected () -> Int64, got Int64", and the generic ones loaded and died.
const ZERO: &str = r#"
namespace test.j6k.zero
  import anthill.prelude.{Int64, Additive}
  import anthill.kernel.{unify}
  operation call0(f: () -> Int64) -> Int64 = f()
  operation passed() -> Int64 = call0(Additive[T = Int64].zero)
  operation bound() -> Int64 =
    let z: () -> Int64 = Additive[T = Int64].zero
    z()
  operation carrier() -> Int64 =
    let z: () -> Int64 = Int64.zero
    z()
  operation mkZero[X]() -> X requires Additive[T = X] =
    let z: () -> X = Additive[T = X].zero
    z()
  operation mkZeroUnused[X]() -> X requires Additive[T = X] =
    let z: () -> X = Additive[T = X].zero
    Additive[T = X].zero()
  operation applied() -> Int64 = mkZero[X = Int64]()
  operation unused() -> Int64 = mkZeroUnused[X = Int64]()
  rule viaQuery(?r) :- unify(?r, applied())
end
"#;

#[test]
fn a_spec_member_taken_as_a_function_value_is_its_call_at_the_instance() {
    for op in ["passed", "bound", "carrier", "applied", "unused"] {
        assert_eq!(run_int64(ZERO, &format!("test.j6k.zero.{op}")), Ok(0), "{op}");
    }
    let mut kb = load_kb_with(ZERO);
    let rows = query_unary(&mut kb, "test.j6k.zero.viaQuery");
    assert!(
        matches!(rows.as_slice(), [(Value::Int(0), true)]),
        "the rule answers 0, definite; got {rows:?}"
    );
}

// ── (2) An effect row has nothing at run time ──────────────────────────────────────────────

/// `effects E = ?` is `sort E = ? requires EffectsRuntime[Effects = E]`, and the anchor holds
/// no dictionary slot: a stream's chain names none, and a chain of two stream transforms (two
/// effect rows each) runs. Until 89J6K the slot held a constant leaf, kept for the positions.
#[test]
fn an_effect_row_holds_no_dictionary_slot() {
    let src = r#"
namespace test.j6k.rows
  import anthill.prelude.{List, Int64}
  import anthill.prelude.FiniteCollection.{collect}
  operation digits(xs: List[T = Int64]) -> Int64 =
    List.foldLeft(xs, 0, lambda (acc, x) -> acc * 10 + x)
  operation mapped() -> Int64 =
    digits([1, 2, 3, 4].map(lambda n -> n * 2).map(lambda n -> n + 1).collect())
end
"#;
    let mut kb = load_kb_with(src);
    for sort in ["anthill.prelude.Stream", "anthill.prelude.MappedStreamFinite"] {
        let sym = kb.try_resolve_symbol(sort).expect("a stdlib sort");
        let chain = anthill_core::kb::typing::direct_requires_chain(&mut kb, sym);
        let named: Vec<String> =
            chain.iter().map(|e| kb.qualified_name_of(e.required_sort).to_string()).collect();
        assert!(
            !named.iter().any(|n| n == "anthill.prelude.EffectsRuntime"),
            "`{sort}`'s chain holds no effect row anchor; got {named:?}"
        );
    }
    assert_eq!(run_int64(src, "test.j6k.rows.mapped"), Ok(3579));
}

// ── (3) A raise is passed the `TypeValue` of what it raises ────────────────────────────────

/// A host's call of a builtin that raises is passed its `TypeValue` at its entry, composed at
/// the arguments' types as a host call's requirements are (proposal 073 §6.1): `Error.raise`
/// at `String`, and `KB.loaded`, whose `TypeValue[T = LoadFailed]` its declaration states.
/// Each was refused "raised with no `TypeValue` evidence" once nothing filled it at the raise.
#[test]
fn a_host_call_of_a_raising_builtin_is_passed_its_type_value() {
    let mut interp = interp_for("namespace test.j6k.raise end\n");
    interp
        .register_standard_effect_handlers()
        .expect("register standard effect handlers");
    match interp.call("anthill.prelude.Error.raise", &[Value::Str("kaboom".into())]) {
        Err(EvalError::Raised { .. }) => {}
        other => panic!("`Error.raise` raises its payload; got {other:?}"),
    }
    let mut interp = interp_for("namespace test.j6k.loaded end\n");
    let sources = interp
        .build_list_value(vec![Value::Str("namespace ( ) ] not anthill".to_string())], &[])
        .expect("build List[String]");
    match interp.call("anthill.reflect.KB.loaded", &[sources]) {
        Err(EvalError::Raised { .. }) => {}
        other => panic!("`KB.loaded` of a source that does not parse raises; got {other:?}"),
    }
}

/// A handler's own value is given the `TypeValue` its type has, as a host's call of
/// `Error.raise` reads it ([`anthill_core::eval::Interpreter::type_value_of`]).
#[test]
fn a_handler_reads_a_values_type_value_off_its_type() {
    let mut interp = interp_for("namespace test.j6k.tv end\n");
    let tv = interp
        .type_value_of(&Value::Str("x".into()))
        .unwrap_or_else(|e| panic!("a `String` has its `TypeValue`; got {e:?}"));
    let provider = interp.kb().qualified_name_of(tv.impl_sort()).to_string();
    assert!(provider.contains("String"), "the `TypeValue` of `String`; got {provider}");
}

// ── (4) A requirement a call fixes only in part ────────────────────────────────────────────

/// `useB[P](b: P) requires Spec2[B = P]` leaves `A` unwritten, and its body uses no `A`.
/// `providers` provide `Spec2`; `call` is `go`'s body.
fn partial(providers: &str, call: &str) -> String {
    format!(
        r#"
namespace test.j6k.partial
  import anthill.prelude.{{Int64}}
  sort WIS
    entity wis(n: Int64)
  end
  sort NoSp
    entity nosp(n: Int64)
  end
  sort Spec2
    sort A = ?
    sort B = ?
    operation onlyB(b: B) -> Int64
  end
{providers}
  operation useB[P](b: P) -> Int64 requires Spec2[B = P] = Spec2.onlyB(b)
  operation go() -> Int64 = {call}
end
"#
    )
}

const BOTH: &str = "  sort Both\n    provides Spec2[A = WIS, B = NoSp]\n    \
                    operation onlyB(b: NoSp) -> Int64 = b.n + 4\n  end\n";
const BOTH2: &str = "  sort Both2\n    provides Spec2[A = Int64, B = NoSp]\n    \
                     operation onlyB(b: NoSp) -> Int64 = 100\n  end\n";
const ANY_A: &str = "  sort AnyA\n    sort X = ?\n    provides Spec2[A = X, B = NoSp]\n    \
                     operation onlyB(b: NoSp) -> Int64 = 50\n  end\n";

/// Built at load by §8.7's order over the provisions that agree with `B = NoSp`: the one
/// (`Both`, 9), the more specific of two (`Both` over `AnyA`, 9), and one the call names
/// (`Both2`, 100); after the forwards, so a caller holding the requirement hands on its own. `Box.tagOf2(0)` leaves `Box.V`, so its `requires Tag[T = V]` is answered
/// by the one provision of `Tag`. Each loaded and died "`__req_…` not bound" with nothing
/// filling the slot from the arguments.
#[test]
fn a_requirement_fixed_in_part_takes_the_provision_that_answers_it() {
    let rows = [
        (partial(BOTH, "useB(nosp(n: 5))"), 9),
        (partial(&format!("{BOTH}{ANY_A}"), "useB(nosp(n: 5))"), 9),
        (partial(BOTH2, "useB(nosp(n: 5))"), 100),
        // A provision leaving `A` to its own parameter answers at any `A`.
        (partial(ANY_A, "useB(nosp(n: 5))"), 50),
        (partial(&format!("{BOTH}{BOTH2}"), "useB[Spec2 = Both2](nosp(n: 5))"), 100),
        (partial(&format!("{BOTH}{BOTH2}"), "useB[Spec2 = Both](nosp(n: 5))"), 9),
        // A caller holding the requirement hands its own dictionary on: `AnyA`'s, though
        // `Both` is the more specific of the two.
        (
            partial(
                &format!(
                    "{BOTH}{ANY_A}  operation outer() -> Int64 requires Spec2[B = NoSp] = \
                     useB(nosp(n: 5))\n"
                ),
                "outer[Spec2 = AnyA]()",
            ),
            50,
        ),
    ];
    for (src, want) in rows {
        assert_eq!(run_int64(&src, "test.j6k.partial.go"), Ok(want), "{src}");
    }
    let tag = r#"
namespace test.j6k.tag
  import anthill.prelude.{Int64}
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
  sort Box
    sort V = ?
    entity box(v: V)
    operation tagOf2(n: Int64) -> Int64 requires Tag[T = V] = Tag.tag[T = V]()
  end
  operation go() -> Int64 = Box.tagOf2(0)
end
"#;
    assert_eq!(run_int64(tag, "test.j6k.tag.go"), Ok(7));
}

/// Two provisions that agree with what the call fixes, neither more specific than the other,
/// leave the requirement saying neither: refused at load naming them. It loaded and died.
#[test]
fn two_provisions_neither_more_specific_are_refused_at_load() {
    let errors = load_errors_of(&partial(&format!("{BOTH}{BOTH2}"), "useB(nosp(n: 5))"));
    assert_refused_naming(
        &errors,
        &[
            "the requirement leaves `A` unwritten",
            "`test.j6k.partial.Both` and `test.j6k.partial.Both2` answer",
        ],
        "`Both` beside `Both2`",
    );
}

/// A slot a requirement leaves unwritten is any type, its instance's own (§5.4, decided with
/// the user 2026-11-08): a body that hands the spec's operation a type of its own there is
/// refused at load, as one handing a written-around member is (GVGSQ). `useB` hands `both`
/// the `WIS` value `a` where `requires Spec2[B = P]` leaves `A` open — refused beside `Both`
/// at `A = WIS`, and beside `Both2` at `A = Int64` alone, where it ran to 100 handing
/// `Both2.both` a `WIS`; the same with `Tagger`'s carrier left open and a `B` handed there.
#[test]
fn a_body_using_an_unwritten_slot_at_a_type_of_its_own_is_refused() {
    let both = "  operation both(a: A, b: B) -> Int64\n";
    let hole = |providers: &str| {
        partial(providers, "useB2(wis(n: 4), nosp(n: 5))")
            .replace("    operation onlyB(b: B) -> Int64\n", &format!("    operation onlyB(b: B) -> Int64\n  {both}"))
            .replace(
                "  operation go()",
                "  operation useB2[P](a: WIS, b: P) -> Int64 requires Spec2[B = P] = Spec2.both(a, b)\n  operation go()",
            )
    };
    let both_wis = "  sort Both\n    provides Spec2[A = WIS, B = NoSp]\n    \
                    operation onlyB(b: NoSp) -> Int64 = b.n + 4\n    \
                    operation both(a: WIS, b: NoSp) -> Int64 = a.n + b.n\n  end\n";
    let both_int = "  sort Both2\n    provides Spec2[A = Int64, B = NoSp]\n    \
                    operation onlyB(b: NoSp) -> Int64 = 100\n    \
                    operation both(a: Int64, b: NoSp) -> Int64 = 100\n  end\n";
    assert_refused_naming(
        &load_errors_of(&hole(both_wis)),
        &["`A` as `requires test.j6k.partial.Spec2[B = test.j6k.partial.useB2.P]` leaves it", "`A = test.j6k.partial.WIS` at this call"],
        "beside `Both`",
    );
    assert_refused_naming(
        &load_errors_of(&hole(both_int)),
        &["`test.j6k.partial.Spec2[A = test.j6k.partial.WIS, B = ?P]` cannot be supplied"],
        "beside `Both2` alone",
    );
    let tagger = r#"
namespace test.j6k.tagger
  import anthill.prelude.{Int64, String}
  sort Tagger
    sort C = ?
    sort Out = ?
    operation useOut(self: C, o: Out) -> Int64
  end
  sort B
    entity b(n: Int64)
    provides Tagger[C = B, Out = String]
    operation useOut(self: B, o: String) -> Int64 = 3
  end
  operation h[P](o: P, x: B) -> Int64 requires Tagger[Out = P] = Tagger.useOut(x, o)
end
"#;
    assert_refused_naming(
        &load_errors_of(tagger),
        &["`C` as `requires test.j6k.tagger.Tagger[Out = test.j6k.tagger.h.P]` leaves it", "`C = test.j6k.tagger.B` at this call"],
        "`Tagger`'s carrier left open",
    );
}

// ── (5) A body written in a spec, taken by a provision ─────────────────────────────────────

/// `Cell` provides `PartialOrd` under `:- WeakOrd[E]` and writes `compare` alone, so it takes
/// `PartialOrd.gt`'s body, whose `requires WeakOrd[T]` its provision owes: `WeakOrd[T =
/// Cell[E]]`, built at `Cell`'s own parameters and read through the condition's slot of the
/// dictionary the body is entered with — from an operation body, through a generic caller
/// holding `PartialOrd[T = A]`, nested, at `String`, and from a rule-body goal. Through the
/// generic caller and the goal it died "`__req_weakord` not bound" once nothing read the
/// arguments for it.
#[test]
fn a_provision_passes_the_requirement_of_a_spec_body_it_takes() {
    let src = r#"
namespace test.j6k.cell
  import anthill.prelude.{Bool, Int64, String, PartialEq, Eq, PartialOrd, Ord, WeakOrd}
  enum Cell
    sort E = ?
    entity cell(v: E)
    provides PartialEq[Self] :- PartialEq[E] where
      operation eq(a: Self, b: Self) -> Bool =
        match a
          case cell(x) ->
            match b
              case cell(y) -> PartialEq.eq(x, y)
    end
    provides Eq[Self] :- Eq[E]
    provides PartialOrd[Self] :- WeakOrd[E]
    provides WeakOrd[Self] :- WeakOrd[E] where
      operation compare(a: Self, b: Self) -> Int64 =
        match a
          case cell(x) ->
            match b
              case cell(y) -> WeakOrd.compare(x, y)
    end
    provides Ord[Self] :- Ord[E]
  end
  import test.j6k.cell.Cell.cell
  operation viaOp() -> Bool = PartialOrd.gt(cell(2), cell(1))
  operation viaOpLt() -> Bool = PartialOrd.lt(cell(2), cell(1))
  operation bigger[A](a: A, b: A) -> Bool requires PartialOrd[T = A] = PartialOrd.gt(a, b)
  operation viaGen() -> Bool = bigger(cell(2), cell(1))
  operation viaGenNested() -> Bool = bigger(cell(cell(2)), cell(cell(5)))
  operation viaGenStr() -> Bool = bigger(cell("b"), cell("a"))
  rule goal(?r) :- PartialOrd.gt(cell(2), cell(1), ?r)
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [
        ("viaOp", true),
        ("viaOpLt", false),
        ("viaGen", true),
        ("viaGenNested", false),
        ("viaGenStr", true),
    ] {
        let got = interp.call(&format!("test.j6k.cell.{op}"), &[]);
        assert!(matches!(got, Ok(Value::Bool(b)) if b == want), "{op} answers {want}; got {got:?}");
    }
    let mut kb = load_kb_with(src);
    let rows = query_unary(&mut kb, "test.j6k.cell.goal");
    assert!(
        matches!(rows.as_slice(), [(Value::Bool(true), true)]),
        "the goal answers `true`, definite; got {rows:?}"
    );
}
