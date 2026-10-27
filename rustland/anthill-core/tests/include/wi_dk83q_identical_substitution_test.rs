//! WI-20261024-DK83Q — AN IDENTICAL SUBSTITUTION IS NOT WRITTEN, in every position a type is
//! written in. A `?` at a slot that declares no default leaves the slot as it is, so
//! `Error[T = ?]`, `Error[?]` and `Error` are one type (user, 2026-10-24; `kernel-language.md`
//! §8.1, "the four ways of leaving a parameter unwritten … all mean the same thing"). Both type
//! lowerings leave such a binding out (`Loader::leaves_its_slot_as_it_is`): a type position
//! (`Loader::type_expr_to_child_inner`) and a clause's binding value
//! (`Loader::sort_binding_to_value`).
//!
//! Before it, an effect label kept a written `?` as a variable, which a boundary unified with
//! its payload, where the bare label is compared by identity: `Error.reify[T1 = Boom]` over a
//! thunk declaring `{Error[T = ?]}` loaded, and over one declaring `{Error}` was refused. What a
//! host function under such a row raises carries the unknown type, which no boundary at `Boom`
//! catches, so stage (d) of proposal 071 refused a host operation writing `Error[T = ?]` out.
//! That refusal is gone with the difference.
//!
//! THE ONE VERDICT IS THE USER'S (2026-10-24): `Error` raises at a type not known, which only a
//! boundary whose pattern is `?` catches. A boundary at a specific type does not discharge it:
//! the label pairs with no `Error[Boom]` (`effects::bare_against_written`), passes into the
//! boundary's `Rho`, and is the caller's to declare — `Error.reify[T1 = Boom](lambda () ->
//! go())` over `go … effects {Error}` loads inside a caller declaring `effects {Error}` and is
//! refused inside one declaring nothing.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ── measured 2026-10-24, each alone ──
//!
//! * A bare label paired with a written one of its sort (`effects::bare_against_written`
//!   answering no): `an_open_payload_is_one_label_however_it_is_written`,
//!   `a_host_row_written_out_is_the_bare_row` — the boundary at `Boom` is refused at its
//!   argument instead of leaving `Error` to the caller.
//! * The binding kept in a type position (`type_expr_to_child_inner`):
//!   `an_open_payload_is_one_label_however_it_is_written`, `rows_written_either_way_meet`,
//!   `a_callback_slot_reads_its_label_as_written_bare`, `a_host_row_written_out_is_the_bare_row`,
//!   `a_binding_value_written_with_a_question_mark_is_the_bare_sort`,
//!   `wi_cbrsw_permission_effect_test::a_question_mark_argument_in_a_lacks_constraint_is_the_bare_denial`
//!   and `wi_5cdn5_raise_carries_its_type_test::a_host_operation_that_raises_states_what_it_raises`.
//!   Their bare-`Error` rows pass either way by design.
//! * The binding left out at a DEFAULTED slot too: `a_defaulted_slot_keeps_its_question_mark`.
//! * The binding kept in a binding value (`sort_binding_to_value`):
//!   `a_binding_value_written_with_a_question_mark_is_the_bare_sort` (the type position's
//!   back-out fails it too). `a_provision_written_with_a_question_mark_dispatches_as_the_bare_one`
//!   passes either way by design.
//! * Where a reader read the BARE spelling otherwise than the `?` one, the `?` one's verdict
//!   is kept, the bare spelling being what the `?` one now is; each measured alone with the
//!   reader's new arm answering no (`typing::leaves_a_slot_open` the shared question):
//!   a carrier's provision binding `B = Other` (`bind_spec_params_from_carrier_param`) —
//!   `wi_80zv8_written_wildcard_test::a_wildcard_binding_holds_its_argument_to_the_sort_it_names`;
//!   an operation's default `[T = List]` (`record_operation_type_param_defaults`) —
//!   `wi_gbh5f_operation_type_param_defaults_test::a_default_that_cannot_mean_anything_is_refused_at_the_declaration`;
//!   a block's `provides Store[State = List]` (`scan_sort_carrier_bindings`) —
//!   `wi_zbwmc_provision_narrowing_test::a_family_keeps_the_generic_reading`; a `let`
//!   the type expected of a call's result, `let c: Car = Mk.make[E = R]()`, with its slot left
//!   out a variable of the call (`apply`'s expected-type seeding) —
//!   `wi_gjw9z_spec_call_charges_the_callers_row_test::an_override_row_left_open_keeps_the_spec_row`.
//!   Expanded once at the `let` instead, both branches of an `if` were held to one instance
//!   and `let s: KVStore = if p then a else b` over two `KVStore`s was refused — the reading
//!   `KVStore[K = ?, V = ?]` had before (MEASURED); `wi457_join_escape_gate_test` holds it.
//! * A slot that declares a default read as open where it is left out (`leaves_a_slot_open`):
//!   `a_defaulted_slot_left_out_is_no_family`.
//! * A higher-kinded slot read as an open one (`slot_is_higher_kinded` not asked at the three
//!   new sites): at the carrier binding, `a_higher_kinded_binding_is_no_open_slot`; at the
//!   narrowing scan and inside `leaves_a_slot_open`,
//!   `the_sugar_narrows_through_a_higher_kinded_binding`. An operation's type parameter is
//!   never higher-kinded, so the default check asks nothing.
//! * A variable payload of a host row read as `?` again (`typing::host_raise_type`, as stage
//!   (d) read it), or the operation's own parameter compared with its clause by one spelling
//!   (`same_type`'s `named_type_param`): `a_host_raise_at_a_type_parameter_is_threaded` and
//!   `wi_5cdn5_raise_carries_its_type_test::a_host_operation_that_raises_states_what_it_raises`.

use anthill_core::eval::{EvalError, Interpreter};

/// `go` declares `ROW`; `caller` reifies it at `Boom` written and declares `effects
/// CALLER_ROW`; `inferred` reifies it at the `T1` its thunk's row gives, declaring no effect.
fn reified(row: &str, caller_row: &str) -> String {
    format!(
        r#"
namespace test.dk
  import anthill.prelude.{{Int64, String, Error, Result}}
  sort Boom
    entity boom(why: String)
  end
  operation go() -> Int64 effects {row} = 1
  operation caller() -> Result[E = Boom, T = Int64] effects {caller_row} =
    Error.reify[T1 = Boom](lambda () -> go())
  operation inferred() -> Result[T = Int64] =
    Error.reify(lambda () -> go())
end
"#
    )
}

/// THE TICKET'S TWO PROGRAMS GET ONE VERDICT, the bare `Error`'s as the user stated it
/// (2026-10-24): `Error` raises at a type not known, which only a boundary whose pattern is `?`
/// catches. A boundary at `Boom` does not discharge it — it is no `Error[Boom]`, and passes into
/// the boundary's `Rho`, as an `Error[Other]` does — so `caller` incurs `Error`: refused declaring
/// `{}` ("undeclared effect: Error"), loading declaring `{Error}`, for each of the three
/// spellings. `inferred`, whose `T1` is unwritten, reifies at `?` — the pattern over a thunk
/// whose only `Error` label is the bare one (proposal 071 §7 Q1, decided with the user
/// 2026-10-27) — which discharges the label: it loads declaring nothing, its result `Result[E =
/// ?]`. Until then `T1` was the `Boom` its declared result `Result[E = Boom, …]` fixed, and the
/// caller incurred `Error` as `caller` does. BACK-OUT: with a bare label paired with
/// `Error[Boom]` (`effects::bare_against_written` answering no), `caller` is refused at the
/// `reify` argument, "the lambda argument declares `Error`, which the closed row does not
/// admit", the verdict this ticket found the bare `Error` given; with the written `?` kept a
/// variable as well, `{Error[T = ?]}` loads declaring `{}`, the label discharged by `?` :=
/// `Boom`.
#[test]
fn an_open_payload_is_one_label_however_it_is_written() {
    for row in [
        "Error",
        "{Error}",
        "Error[?]",
        "{Error[?]}",
        "Error[T = ?]",
        "{Error[T = ?]}",
    ] {
        let errs = crate::common::load_errors_of(&reified(row, "{}"));
        assert_eq!(
            errs.iter()
                .filter(|e| e.contains("expected declared: [], got undeclared effect: Error"))
                .count(),
            1,
            "{row}: `caller` incurs `Error`, past the boundary at `Boom`; got {errs:#?}"
        );
        assert!(
            errs.iter().all(|e| !e.contains("inferred")),
            "{row}: `inferred` discharges it at `?`; got {errs:#?}"
        );
        let errs = crate::common::load_errors_of(&reified(row, "{Error}"));
        assert!(errs.is_empty(), "{row}: declaring `Error`, both load; got {errs:#?}");
    }
}

/// A CALLER AND A CALLEE MEET WHICHEVER SPELLING EACH WRITES. Before, `Error[?]` and `Error`
/// were two labels: a caller declaring one was refused calling a callee declaring the other,
/// "undeclared effect". BACK-OUT: the mixed pairs refused.
#[test]
fn rows_written_either_way_meet() {
    let spellings = ["Error", "Error[?]", "Error[T = ?]"];
    for callee in spellings {
        for caller in spellings {
            let src = format!(
                r#"
namespace test.dkrow
  import anthill.prelude.{{Int64, Error}}
  operation g() -> Int64 effects {{{callee}}} = 1
  operation c() -> Int64 effects {{{caller}}} = g()
end
"#
            );
            let errs = crate::common::load_errors_of(&src);
            assert!(errs.is_empty(), "caller {caller} of callee {callee}: loads clean, got {errs:#?}");
        }
    }
}

/// A CALLBACK SLOT WRITTEN `@ {Error[?]}` IS THE SLOT `@ {Error}`: it takes a callback raising
/// `Error`, and one raising `Error[Boom]` — the bare label is the pattern `?`, and a row admits
/// what a boundary at it catches (user, 2026-10-27; it refused the `Boom` callback before).
/// BACK-OUT: with a declared bare `Error` admitting no written payload in the callback check
/// (`labels_match_by_subsumption`), all three slots refuse the `Boom` callback.
#[test]
fn a_callback_slot_reads_its_label_as_written_bare() {
    for slot in ["Error", "Error[?]", "Error[T = ?]"] {
        let src = |arg: &str| {
            format!(
                r#"
namespace test.dkslot
  import anthill.prelude.{{Int64, String, Error}}
  sort Boom
    entity boom(why: String)
  end
  operation h(f: () -> Int64 @ {{{slot}}}) -> Int64 = 1
  operation g() -> Int64 effects {{Error}} = 1
  operation c() -> Int64 = h({arg})
end
"#
            )
        };
        let errs = crate::common::load_errors_of(&src("lambda () -> g()"));
        assert!(errs.is_empty(), "@ {{{slot}}} given an `Error` callback: loads clean, got {errs:#?}");
        let errs =
            crate::common::load_errors_of(&src(r#"lambda () -> Error.raise(boom(why: "x"))"#));
        assert!(errs.is_empty(), "@ {{{slot}}} given an `Error[Boom]` callback: loads clean, got {errs:#?}");
    }
}

/// A SLOT THAT DECLARES A DEFAULT IS WRITTEN WHEN IT IS WRITTEN `?`: left out it takes the
/// default, and `?` opts out of it (proposal 069). `open(c: Cfg[T = ?])` takes any `Cfg`,
/// `closed(c: Cfg)` the `Cfg[T = Int64]` the default makes it. BACK-OUT: the `?` left out at a
/// defaulted slot as well, and `open` refuses the `String` cell as `closed` does.
#[test]
fn a_defaulted_slot_keeps_its_question_mark() {
    let src = |param: &str| {
        format!(
            r#"
namespace test.dkdef
  import anthill.prelude.{{Int64, String}}
  sort Cfg[T = Int64]
    entity cfg(v: T)
  end
  operation take(c: {param}) -> Int64 = 1
  operation c() -> Int64 = take(cfg(v: "s"))
end
"#
        )
    };
    let errs = crate::common::load_errors_of(&src("Cfg[T = ?]"));
    assert!(errs.is_empty(), "`Cfg[T = ?]` is any `Cfg`: loads clean, got {errs:#?}");
    let errs = crate::common::load_errors_of(&src("Cfg[?]"));
    assert!(errs.is_empty(), "`Cfg[?]` is any `Cfg`: loads clean, got {errs:#?}");
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&src("Cfg")),
        &["take.c", "Cfg[T = Int64]"],
        "`Cfg` is `Cfg[T = Int64]`",
    );
}

/// A BINDING VALUE IS A WRITTEN TYPE TOO, and a clause and a row that write one type hold one
/// term: a sort-level `requires TypeValue[T = Box[V = ?]]` is the clause a host row raising
/// `Error[Box[V = ?]]` states. Before, each `?` was a variable of its own, and the declaration
/// was refused, "does not require `TypeValue[T = Box[V = ?_]]`". BACK-OUT: the binding kept in
/// the clause, and the row's `Box` meets the clause's `Box[V = ?_]` — refused; the type
/// position's back-out refuses it the other way round.
#[test]
fn a_binding_value_written_with_a_question_mark_is_the_bare_sort() {
    let src = r#"
namespace test.dkclause
  import anthill.prelude.{Int64, Error}
  import anthill.reflect.{TypeValue}
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort Holder
    import anthill.prelude.{Int64, Error}
    import anthill.reflect.{TypeValue}
    import test.dkclause.{Box}
    requires TypeValue[T = Box[V = ?]]
    entity holder
    operation fail(b: Box) -> Int64 effects {Error[Box[V = ?]]} @[host_implemented]
  end
  provides Holder language rust
    artifact "nowhere.rs"
    operation_map { fail: "error_raise" }
  end
end
"#;
    let errs = crate::common::load_errors_of(src);
    assert!(errs.is_empty(), "the clause answers the row: loads clean, got {errs:#?}");
}

/// A provision's binding written `Box[V = ?]` or `Box[?]` dispatches as `Box` does, at a `Box` of
/// any element. PASSES EITHER WAY by design: dispatch reads a bare sort as the sort at a fresh
/// variable in each slot (§8.1), so the two terms were already one provision to it; the row
/// guards that leaving the binding out keeps it so.
#[test]
fn a_provision_written_with_a_question_mark_dispatches_as_the_bare_one() {
    for written in ["Box", "Box[V = ?]", "Box[?]"] {
        let src = format!(
            r#"
namespace test.dkbind
  import anthill.prelude.{{Int64, String}}
  sort Show
    sort T = ?
    operation show(x: T) -> String
  end
  sort Box
    sort V = ?
    entity box(v: V)
    provides Show[T = {written}] where
      operation show(x: Box) -> String = "box"
    end
  end
  operation direct() -> String = Show.show(box(v: 1))
  operation generic[X](b: Box[V = X]) -> String = Show.show(b)
  operation viaGeneric() -> String = generic(box(v: "s"))
end
"#
        );
        let mut interp = crate::common::interp_for(&src);
        for op in ["direct", "viaGeneric"] {
            let v = interp
                .call(&format!("test.dkbind.{op}"), &[])
                .unwrap_or_else(|e| panic!("{written}, {op}: {e}"));
            assert_eq!(
                crate::common::scalar_str(interp.kb(), &v).as_deref(),
                Some("box"),
                "{written}, {op}"
            );
        }
    }
}

/// A host operation, `go`, at the row `ROW`, whose host function raises its argument.
fn host_program(row: &str) -> String {
    format!(
        r#"
namespace test.dkh
  import anthill.prelude.{{Int64, String, Error, Result}}
  import anthill.prelude.Result.{{ok, err}}
  import anthill.reflect.{{TypeValue}}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(n: Int64)
  end
  sort Host
    import anthill.prelude.{{Int64, Error}}
    import anthill.reflect.{{TypeValue}}
    import test.dkh.{{Boom, Other}}
    entity host
    operation go{row} @[host_implemented]
  end
  provides Host language rust
    artifact "nowhere.rs"
    operation_map {{ go: "dk_raise_arg" }}
  end
  ENTRY
end
"#
    )
}

fn host_interp(src: &str) -> Interpreter {
    // NOT THE RECIPE, BY NAME: the host function must be registered before the load, whose
    // `operation_map` names it.
    let kb = crate::common::try_load_kb_prepared(src, |kb| {
        kb.register_host_fn("dk_raise_arg", 1, |interp, args| Err(interp.raise_error(args[0].clone())))
            .expect("register dk_raise_arg");
    })
    .unwrap_or_else(|errs| panic!("the fixture must load: {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    interp
}

/// A HOST ROW WRITTEN `Error[T = ?]` IS THE BARE ROW: it loads, needing no clause, and what its
/// host function raises carries the unknown type. A boundary at `Boom` does not catch it — the
/// typer leaves the label to the caller's row, and at run time the raise passes the boundary and
/// leaves the caller. Stage (d) refused the declaration, since the typer let a boundary at `Boom`
/// discharge the written spelling. BACK-OUT: with the bare label paired with `Error[Boom]`, the
/// reifying caller is refused at the `reify` argument.
#[test]
fn a_host_row_written_out_is_the_bare_row() {
    let src = host_program("(b: Boom) -> Int64 effects {Error[T = ?]}").replace(
        "ENTRY",
        "operation passes() -> Result[E = Boom, T = Int64] effects {Error} =\n    \
         Error.reify[T1 = Boom](lambda () -> Host.go(boom(why: \"x\")))",
    );
    let mut interp = host_interp(&src);
    match interp.call("test.dkh.passes", &[]) {
        Err(EvalError::Raised { .. }) => {}
        other => panic!("the raise passes the boundary at `Boom` and leaves `passes`, got {other:?}"),
    }
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&src.replace("effects {Error} =", "=")),
        &["passes.effects", "undeclared effect: Error"],
        "a caller declaring nothing beside a boundary at `Boom`",
    );
}

/// A HOST RAISE AT THE OPERATION'S TYPE PARAMETER IS THREADED: `go[P](p: P)` raising
/// `Error[P]` under `requires TypeValue[T = P]` raises at the type its call fixes. Nested
/// boundaries at `Other` (inner) and `Boom` (outer) answer through the outer for a `Boom` and
/// the inner for an `Other`. Before, any variable payload of a host row was read as `?`, and
/// the declaration was refused as raising `Error[T = ?]`, its clause written. BACK-OUT: the
/// fixture is refused at load.
#[test]
fn a_host_raise_at_a_type_parameter_is_threaded() {
    let src = host_program("[P](p: P) -> Int64 effects {Error[P]} requires TypeValue[T = P]")
        .replace(
            "ENTRY",
            r#"operation innerB() -> String effects {Error[Boom]} =
    match Error.reify[T1 = Other](lambda () -> Host.go(boom(why: "x")))
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedB() -> String =
    match Error.reify[T1 = Boom](lambda () -> innerB())
      case ok(s) -> s
      case err(_) -> "outer"
  operation innerO() -> String effects {Error[Boom]} =
    match Error.reify[T1 = Other](lambda () -> Host.go(other(n: 1)))
      case ok(_) -> "none"
      case err(_) -> "inner"
  operation nestedO() -> String =
    match Error.reify[T1 = Boom](lambda () -> innerO())
      case ok(s) -> s
      case err(_) -> "outer""#,
        );
    let mut interp = host_interp(&src);
    for (op, want) in [("nestedB", "outer"), ("nestedO", "inner")] {
        let v = interp
            .call(&format!("test.dkh.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(crate::common::scalar_str(interp.kb(), &v).as_deref(), Some(want), "{op}");
    }
}

/// A HIGHER-KINDED SLOT TAKES A CONSTRUCTOR UNAPPLIED: behind `provides Lift[C = Self, F =
/// Option]`, `F = Option` leaves no slot open, and is not bound as the instance `Option[T =
/// ?]` a slot left out elsewhere is. So `Lift.lift(car(n: 1), 5)` is refused, as before the
/// open-slot arm. BACK-OUT: with `slot_is_higher_kinded` not asked at the carrier binding
/// (`bind_spec_params_from_carrier_param`), `F` binds `Option[T = ?]` and the call LOADS,
/// the `Int64` passed where an `F[T = Int64]` is taken (MEASURED).
///
/// NOT THE CAPABILITY'S VERDICT: the well-typed `Lift.lift(car(n: 1), some(1))` is refused as
/// well ("no impl matches"), before this ticket and after — a dispatch at a bare
/// higher-kinded binding finds no impl. The row pins only that the ill-typed call stays
/// refused.
#[test]
fn a_higher_kinded_binding_is_no_open_slot() {
    let src = |arg: &str| {
        format!(
            r#"
namespace test.dkhk
  import anthill.prelude.Option.{{none, some}}
  import anthill.prelude.{{Option, Int64}}
  sort Lift[C, F[T]]
    operation lift(c: C, x: F[T = Int64]) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Lift[C = Self, F = Option]
    operation lift(c: Self, x: Option[T = Int64]) -> Int64 = 1
  end
  operation go() -> Int64 = Lift.lift(car(n: 1), {arg})
end
"#
        )
    };
    let errs = crate::common::load_errors_of(&src("5"));
    assert!(!errs.is_empty(), "an `Int64` where an `F[T = Int64]` is taken is refused");
}

/// …AND THE BARE-SPEC SUGAR NARROWS THROUGH ONE, at a higher-kinded member and beneath a
/// higher-kinded slot of a binding: `provides CpsMonad[F = Option]` makes `CpsMonad.F` the
/// `Option` it binds, and `provides Store[State = Tagged[F = Option, A = Int64]]` makes
/// `Store.State` that `Tagged`, whose `F = Option` is a constructor and no open slot. Both
/// load, as before the open-slot reading. BACK-OUT: with `slot_is_higher_kinded` not asked
/// in `scan_sort_carrier_bindings` and in `leaves_a_slot_open`, each binding reads as a family
/// and the generic reading refuses `id`'s return and `count`'s `s.n` (MEASURED).
#[test]
fn the_sugar_narrows_through_a_higher_kinded_binding() {
    let member = r#"
namespace test.dkhkm
  import anthill.prelude.Option.{none, some}
  import anthill.prelude.{Option, Int64}
  sort Tagged[F[T], A]
    entity tagged(n: Int64)
  end
  sort CpsMonad[F[T]]
    operation unit[A](a: A) -> F[T = A]
  end
  operation optionUnit[A](a: A) -> Option[T = A] = some(a)
  sort OptM
    provides CpsMonad[F = Option, unit = test.dkhkm.optionUnit]
    operation id(t: Tagged[F = CpsMonad.F, A = Int64]) -> Tagged[F = Option, A = Int64] = t
  end
end
"#;
    let errs = crate::common::load_errors_of(member);
    assert!(errs.is_empty(), "`CpsMonad.F` is `Option` in the block: {errs:#?}");
    let beneath = r#"
namespace test.dkhkb
  import anthill.prelude.{Option, Int64, Bool}
  sort Tagged[F[T], A]
    entity tagged(n: Int64)
  end
  sort Store
    sort State = ?
    operation peek(s: State) -> Bool
  end
  sort FileStore
    provides Store[State = Tagged[F = Option, A = Int64]]
    operation peek(s: Store.State) -> Bool = true
    operation count(s: Store.State) -> Int64 = s.n
  end
  operation go() -> Int64 = FileStore.count(tagged(n: 7))
end
"#;
    let mut interp = crate::common::interp_for(beneath);
    let v = interp.call("test.dkhkb.go", &[]).expect("`go` runs");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(7));
}

/// A SLOT THAT DECLARES A DEFAULT IS NO OPEN SLOT, left out: it takes the default. Behind
/// `provides Store[State = Cfg]` over `sort Cfg[T = Int64]` the sugar narrows `Store.State` to
/// `Cfg`, as before the open-slot reading, and `mk() -> Store.State = cfg(v: 1)` loads.
/// BACK-OUT: with `leaves_a_slot_open` reading a defaulted slot as open, the binding is a family,
/// the sugar keeps its generic reading, and `mk` is refused "expected Store.State, got Cfg[T =
/// Int64]" (MEASURED; found by /code-review).
#[test]
fn a_defaulted_slot_left_out_is_no_family() {
    let src = r#"
namespace test.dkcfg
  import anthill.prelude.{Int64, Bool}
  sort Cfg[T = Int64]
    entity cfg(v: T)
  end
  sort Store
    sort State = ?
    operation peek(s: State) -> Bool
  end
  sort FileStore
    provides Store[State = Cfg]
    operation peek(s: Store.State) -> Bool = true
    operation mk() -> Store.State = cfg(v: 1)
  end
end
"#;
    let errs = crate::common::load_errors_of(src);
    assert!(errs.is_empty(), "`Store.State` is `Cfg` in the block: {errs:#?}");
}
