//! WI-20261023-GBH5F (proposal 069 stage 2) — an operation's type parameter declares a
//! DEFAULT (`operation which[T = String](…)`, §1.3), and a call whose inference leaves the
//! parameter unbound takes it (§2 steps 4–5). Until this stage the form was refused at the
//! converter (WI-850), its default having no reader.
//!
//! At a call a parameter is settled by (1) an explicit binding at the call, (2) inference
//! from the arguments, the requirements, the receiver and the expected result, (3) its
//! default, (4) WI-270's unconstrained-parameter refusal. The rows read WHICH `T` a call
//! took as a value: `which` answers `TypeValue.type_value[T = T]()`, the type itself.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ──────────────────────────────────
//!
//! On the parent tree every row naming a default fails to load (WI-850's refusal). On this
//! tree, each part out alone (MEASURED with a temporary switch per part, over this file,
//! `wi850_type_param_default_test`, `wi_v25n3_written_row_label_test` and
//! `wi_qv5w5_sort_parameter_defaults_test`):
//!
//! * The installation at a call (`install_type_param_defaults`): the default, dependent,
//!   return-only, row-default, row-slot and enclosing-parameter rows here, and WI-850's
//!   three driven rows.
//! * The installation in the override fallback (`concrete_override_threaded`): the fallback
//!   row.
//! * The record at the declaration (`Loader::record_operation_type_param_defaults`): the
//!   rows of both installations, the refusal, quoting and reflect rows, and v25n3's row in
//!   a default.
//! * Each declaration refusal (order, kind, a variable that is no parameter): the refusal
//!   row; the order and kind ones the quoting row too; the kind one the row-slot and
//!   enclosing-parameter rows, whose wrong-kind controls it is.
//! * A sort's effect-row slot read as a row use (`Loader::binds_a_row_slot`), and an
//!   enclosing sort's `effects E` read as a row (`Loader::names_enclosing_row_param`): the
//!   row-slot row.
//! * The reflect row (`Loader::file_operation_type_param_default`): `a_default_is_reflected`
//!   and the enclosing-parameter row's reflect half.
//! * `[T = ?]` read as no default (the converter's filter): `a_bare_hole_declares_no_default`;
//!   the filter reading the node's text, its `bareD` half.
//! * A construction's default at the `let` (`fill_inferred_defaults`): both construction
//!   rows.
//! * The grammar's `_common_type_expr` (back to `_type`): `[E = {}]` is a syntax error
//!   (MEASURED before the change).
//!
//! Stage 1's rows pass under every one of these.

use crate::common::{interp_for, load_errors_of};

const PROGRAM: &str = r#"
namespace test.gbh5f
  import anthill.prelude.{Int64, String, Bool, Option, List, Type}
  import anthill.prelude.Option.{none, some}
  import anthill.reflect.{TypeValue}

  operation which[T = String](o: Option[T]) -> Type requires TypeValue[T = T] =
    TypeValue.type_value[T = T]()
  operation byDefault() -> Type = which(none())
  operation byInference() -> Type = which(some(42))
  operation byBinding() -> Type = which[T = Bool](none())
  operation byExpected() -> Type =
    let o: Option[T = Int64] = none()
    which(o)

  -- A default naming an earlier parameter is read at what the call has there.
  operation dep[T, U = List[T = T]](t: T) -> Type requires TypeValue[T = U] =
    TypeValue.type_value[T = U]()
  operation dependent() -> Type = dep(1)
  operation dependentBound() -> Type = dep[U = Bool](1)

  -- A return-only parameter: the `let` is the boundary, and with no evidence there the
  -- default is the type the binding has.
  operation pick[T = String]() -> Option[T] = none()
  operation wantS(o: Option[T = String]) -> Int64 = 1
  operation wantI(o: Option[T = Int64]) -> Int64 = 2
  operation letTakesDefault() -> Int64 =
    let o = pick()
    wantS(o)
  operation argTakesEvidence() -> Int64 = wantI(pick())
end
"#;

fn type_of(op: &str) -> String {
    let mut interp = interp_for(PROGRAM);
    let v = interp
        .call(&format!("test.gbh5f.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op}: {e}"));
    anthill_core::kb::typing::type_display_name_value(interp.kb(), &v)
}

/// THE ORDER OF §1.3: the default answers only where nothing else does. `which(none())`
/// takes `String`; `which(some(42))` infers `Int64`, the default not overriding evidence;
/// `which[T = Bool](none())` is what the call writes; an argument whose type the expected
/// result fixed (`let o: Option[T = Int64]`) is evidence too.
///
/// FAILS with the installation backed out (`install_type_param_defaults` a no-op):
/// `byDefault` is refused at load as an unconstrained `T` — the program does not load, and
/// every row fails. The three others pass either way by design: evidence is read before the
/// default would be.
#[test]
fn a_default_answers_only_where_nothing_else_binds_the_parameter() {
    for (op, want) in [
        ("byDefault", "String"),
        ("byInference", "Int64"),
        ("byBinding", "Bool"),
        ("byExpected", "Int64"),
    ] {
        assert_eq!(type_of(op), want, "{op}");
    }
}

/// A DEFAULT NAMING AN EARLIER PARAMETER is instantiated at what the call has there:
/// `dep(1)` infers `T = Int64` and takes `U = List[T = Int64]`; a call that writes `U`
/// keeps it.
#[test]
fn a_dependent_default_is_read_after_the_parameter_it_names() {
    assert_eq!(type_of("dependent"), "List[T = Int64]");
    assert_eq!(type_of("dependentBound"), "Bool");
}

/// A RETURN-ONLY PARAMETER takes its default at the `let` that has no evidence for it, and
/// keeps the evidence of a call that has: `wantI(pick())` reads `Int64` from `wantI`'s
/// parameter before the default would be read, and `let o = pick()` is an `Option[T =
/// String]`, which `wantS` takes — and `wantI` refuses (the next row).
#[test]
fn a_return_only_parameter_takes_the_evidence_of_its_call_and_the_default_without() {
    let mut interp = interp_for(PROGRAM);
    for (op, want) in [("letTakesDefault", 1), ("argTakesEvidence", 2)] {
        let v = interp
            .call(&format!("test.gbh5f.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(want), "{op}");
    }
    let errs = load_errors_of(
        r#"
namespace test.gbh5f.let
  import anthill.prelude.{Int64, String, Option}
  import anthill.prelude.Option.{none}
  operation pick[T = String]() -> Option[T] = none()
  operation wantI(o: Option[T = Int64]) -> Int64 = 2
  operation letThenOther() -> Int64 =
    let o = pick()
    wantI(o)
end
"#,
    );
    crate::common::assert_refused_naming(
        &errs,
        &["Option[T = Int64]", "Option[T = String]"],
        "the `let`'s default is the type `wantI` is handed",
    );
}

/// A DEFAULT IS REFUSED AT ITS DECLARATION where it cannot mean anything, and not recorded:
/// one naming a later parameter or its own (defaults are ordered, so a chain of them ends
/// at a slot something else decides); one of the wrong kind — a type for a parameter the
/// signature uses as an effect row; and a default holding a variable that is no parameter
/// (`[T = List[T = ?]]`), a slot it would leave open.
///
/// FAILS with `Loader::record_operation_type_param_defaults`' refusals taken out: each
/// program loads (the order and stray-variable ones then type a call against a default
/// over a variable nothing binds).
#[test]
fn a_default_that_cannot_mean_anything_is_refused_at_the_declaration() {
    for (shape, decl, want) in [
        (
            "a later parameter",
            "operation fwd[U = List[T = T], T](t: T) -> Int64 = 1",
            "the default of `U` (`U = List[T = T]`) names `T`, which is declared after it",
        ),
        (
            "its own parameter",
            "operation selfref[T = Option[T = T]](t: T) -> Int64 = 1",
            "the default of `T` (`T = Option[T = T]`) names `T` itself",
        ),
        (
            "a type for a row",
            "operation typeForRow[E = Int64](f: () -> Int64 @ E) -> Int64 effects E = f()",
            "the default of `E` (`E = Int64`) is of the wrong kind: `E` is an effect-row \
             parameter of `test.gbh5f.decl.typeForRow`",
        ),
        (
            "a variable that is no parameter",
            "operation holeInside[T = List[T = ?]](x: Int64) -> Int64 = x",
            "the default of `T` (`T = List[T = ?_]`) holds a type variable that names no \
             earlier parameter",
        ),
    ] {
        let errs = load_errors_of(&format!(
            "namespace test.gbh5f.decl\n  import anthill.prelude.{{Int64, List, Option}}\n  \
             {decl}\nend\n"
        ));
        crate::common::assert_refused_naming(&errs, &[want], shape);
    }
}

/// A REFUSAL QUOTES THE DEFAULT AS THE TYPE IT IS, never its source text — carried from
/// WI-951, which measured the WI-850 refusal quoting a raw CST slice. (1) An interior block
/// comment and line break are trivia, and gone. (2) A string literal holding a comment
/// opener is a value of the type, kept whole. (3) CONTROL — a hyphenated identifier is one
/// token (`[A-Za-z_][A-Za-z0-9_-]*`), quoted in full: it passes on raw text too, and is the
/// case a fix that strips comment forms from the text breaks (it quoted `my`).
///
/// PASSES EITHER WAY BY DESIGN against this stage: the IR carries the converted type and no
/// source text, so no quote can be taken from the text. On the parent tree WI-850's refusal
/// quoted the CST slice, and (1) quoted the comment and the line break (WI-951's
/// measurement, 2026-08-03).
#[test]
fn a_refusal_quotes_the_default_as_its_type() {
    let src = "namespace test.gbh5f.quote\n  import anthill.prelude.{Int64, List}\n  \
               sort Pair2\n    sort A = ?\n    sort B = ?\n  end\n  sort my--type\n  end\n  \
               operation comment[T = List[ {- note -} U\n    ], U](u: U) -> Int64 = 1\n  \
               operation strLit[T = Pair2[\"a -- b\", U], U](u: U) -> Int64 = 1\n  \
               operation hyphen[E = my--type](f: () -> Int64 @ E) -> Int64 effects E = f()\n\
               end\n";
    let errs = load_errors_of(src);
    let of = |op: &str| -> String {
        errs.iter()
            .find(|e| e.contains(&format!("test.gbh5f.quote.{op}")) || e.contains(op))
            .cloned()
            .unwrap_or_else(|| panic!("{op} is refused: {errs:#?}"))
    };
    let comment = errs
        .iter()
        .find(|e| e.contains("the default of `T` (`T = List[T = U]`)"))
        .unwrap_or_else(|| panic!("(1) quoted as its type: {errs:#?}"));
    assert!(!comment.contains("note") && !comment.contains('\n'), "(1) no trivia: {comment}");
    assert!(
        errs.iter().any(|e| e.contains("`T = Pair2[A = \"a -- b\", B = U]`")),
        "(2) the literal kept whole: {errs:#?}"
    );
    assert!(of("hyphen").contains("`E = my--type`"), "(3) the identifier in full: {errs:#?}");
}

/// A rule reads a declared default through `anthill.reflect.OperationTypeParamDefault`, an
/// earlier parameter named by reference: `which`'s `T` is `String`, and `dep`'s `U` is
/// `List[T = T]` with `T` the parameter's name.
///
/// FAILS with the row not filed (`Loader::file_operation_type_param_default` a no-op): the
/// rule answers nothing.
#[test]
fn a_default_is_reflected() {
    let src = "\
namespace test.gbh5f.reflect
  import anthill.prelude.{Int64, String, List, Type}
  import anthill.reflect.OperationTypeParamDefault
  operation which[T = String](x: Int64) -> Int64 = x
  operation dep[T, U = List[T = T]](t: T) -> Int64 = 1
  rule defaultOf(?d) :- OperationTypeParamDefault(op: ?, param: ?, default: ?d)
end
";
    let mut kb = crate::common::load_kb_with(src);
    let rows: Vec<String> = crate::common::shown_rows(&mut kb, "test.gbh5f.reflect.defaultOf")
        .into_iter()
        .map(|(r, _)| r)
        .collect();
    assert!(rows.iter().any(|r| r == "String"), "{rows:?}");
    assert!(rows.iter().any(|r| r == "List[T = T]"), "{rows:?}");
}

/// THE POSITIONS A CONSTRUCTION'S CONTEXT REACHES IT FROM — an annotation over an enclosing
/// construction, another constructor's field, an `Option`-coerced slot, a generic slot a
/// sibling argument fixes. Each is evidence the default must not come before: installed at
/// the construction, all four were refused (found by /code-review); with the default at the
/// `let` they load, as under stage 1.
#[test]
fn a_constructions_context_is_evidence_before_its_default() {
    let src = r#"
namespace test.gbh5f.ctx
  import anthill.prelude.{Int64, String, Option}
  import anthill.prelude.Option.{none, some}
  sort Tag[T = Int64]
    entity tag(n: Int64)
  end
  sort Holder
    entity holder(t: Tag[T = String])
  end
  operation wantO(o: Option[T = Tag[T = String]]) -> Int64 = 1
  operation both[X](t: Tag[T = X], x: X) -> Int64 = 2
  operation inSome() -> Int64 =
    let x: Option[T = Tag[T = String]] = some(tag(n: 1))
    3
  operation inField() -> Holder = holder(t: tag(n: 1))
  operation coerced() -> Int64 = wantO(tag(n: 1))
  operation generic() -> Int64 = both(tag(n: 1), "s")
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [("inSome", 3), ("coerced", 1), ("generic", 2)] {
        let v = interp
            .call(&format!("test.gbh5f.ctx.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(want), "{op}");
    }
    interp.call("test.gbh5f.ctx.inField", &[]).expect("inField");
}

const CONSTRUCTIONS: &str = r#"
namespace test.gbh5f.ctor
  import anthill.prelude.{Int64, String, Type}
  import anthill.reflect.{TypeValue}
  sort Tag[T = Int64]
    entity tag(n: Int64)
  end
  sort AP[T1, T2 = T1]
    entity ap(first: T1)
  end
  operation tagOf[X](t: Tag[T = X]) -> Type requires TypeValue[T = X] = TypeValue.type_value[T = X]()
  operation secondOf[A, B](p: AP[T1 = A, T2 = B]) -> Type requires TypeValue[T = B] =
    TypeValue.type_value[T = B]()
  operation wantS(x: Tag[T = String]) -> Int64 = 1
  operation wantI(x: Tag[T = Int64]) -> Int64 = 2
  -- An argument: the slot's type is the call's evidence.
  operation asArgument() -> Int64 = wantS(tag(n: 1))
  -- A `let` with no evidence: the default.
  operation atLet() -> Type =
    let t = tag(n: 1)
    tagOf(t)
  -- A default naming an earlier parameter, at what the construction has there.
  operation dependent() -> Type =
    let p = ap(first: 1)
    secondOf(p)
end
"#;

/// A CONSTRUCTION'S SORT PARAMETER its inference leaves free takes the sort's default where
/// the value is finalized — an unannotated `let` (069 §2 steps 4–5, moved here from stage
/// 1): `let t = tag(n: 1)` under `sort Tag[T = Int64]` is a `Tag[T = Int64]`, and `let p =
/// ap(first: 1)` under `sort AP[T1, T2 = T1]` an `AP[T1 = Int64, T2 = Int64]` — each read
/// back as a value. A construction a call consumes takes the call's type: `wantS(tag(n:
/// 1))` is at `String`, the parameter having flowed out of the construction free.
///
/// FAILS with the `let`'s fill backed out (`fill_inferred_defaults` not called): `atLet` and
/// `dependent` are refused at load, the slot opened as the binding's projection (`t.T`).
/// `asArgument` passes either way by design: no default is installed at the construction.
#[test]
fn a_constructions_free_parameter_takes_its_sorts_default_after_its_evidence() {
    let mut interp = interp_for(CONSTRUCTIONS);
    let v = interp.call("test.gbh5f.ctor.asArgument", &[]).expect("asArgument");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(1));
    for (op, want) in [("atLet", "Int64"), ("dependent", "Int64")] {
        let t = interp
            .call(&format!("test.gbh5f.ctor.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e}"));
        assert_eq!(anthill_core::kb::typing::type_display_name_value(interp.kb(), &t), want, "{op}");
    }
}

/// THE `let` IS THE BOUNDARY: a later use at another instance is refused, the default having
/// been the binding's type. FAILS with the `let`'s fill backed out: the use is refused too,
/// but naming the projection `t.T` the `let` opened, not `Int64`.
#[test]
fn a_construction_defaulted_at_a_let_is_refused_at_another_instance() {
    let errs = load_errors_of(
        r#"
namespace test.gbh5f.ctorlet
  import anthill.prelude.{Int64, String}
  sort Tag[T = Int64]
    entity tag(n: Int64)
  end
  operation wantS(x: Tag[T = String]) -> Int64 = 1
  operation letThenOther() -> Int64 =
    let t = tag(n: 1)
    wantS(t)
end
"#,
    );
    crate::common::assert_refused_naming(
        &errs,
        &["expected Tag[T = String], got Tag[T = Int64]"],
        "the `let`'s default is the type `wantS` is handed",
    );
}

/// `[T = ?]` IS THE BARE `T` (user, 2026-10-24; proposal 042's explicit form): a parameter
/// with no default. `bareQ(1)` infers it, and `mkQ()` with nothing to bind it is refused as
/// unconstrained — which a default would have answered. A described hole (`? {< … >}?`) is
/// one too (`bareD`).
///
/// FAILS with the converter reading `?` as a default (the `variable_term` filter in
/// `convert_operation_type_param` taken out): the declarations are refused as a default
/// holding a variable. `bareD` alone FAILS with the filter reading the node's text rather
/// than its `variable` token (the description is in the text).
#[test]
fn a_bare_hole_declares_no_default() {
    let src = r#"
namespace test.gbh5f.hole
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{none}
  operation bareQ[T = ?](x: T) -> T = x
  operation useBareQ() -> Int64 = bareQ(1)
  operation bareD[T = ? {< the element >}?](x: T) -> T = x
  operation useBareD() -> Int64 = bareD(2)
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [("useBareQ", 1), ("useBareD", 2)] {
        let v = interp.call(&format!("test.gbh5f.hole.{op}"), &[]).expect(op);
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(want), "{op}");
    }
    let errs = load_errors_of(
        r#"
namespace test.gbh5f.hole2
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{none}
  operation mkQ[T = ?]() -> Option[T] = none()
  operation useMkQ() -> Int64 =
    let o = mkQ()
    1
end
"#,
    );
    crate::common::assert_refused_naming(
        &errs,
        &["test.gbh5f.hole2.mkQ.type_arg: expected a type for 'T', got unconstrained"],
        "a bare `?` is no default",
    );
}

/// A ROW PARAMETER'S DEFAULT IS WRITTEN `{}` (user, 2026-10-24: the bracket's value is a
/// type argument's, as a sort parameter's default is). `tick()` over `tick[E = {}]() ->
/// Int64 effects E` is pure, so a caller declaring nothing loads; the evidence of a call
/// still wins — `run(lambda () -> boom())` over `run[E = {}](f: () -> Int64 @ E)` is at the
/// thunk's row, so a caller that declares it loads and one that declares nothing is refused.
///
/// FAILS with the grammar's `_common_type_expr` back to `_type`: `[E = {}]` is a syntax
/// error. FAILS with the installation backed out: `useTick` is refused as an unconstrained
/// `E`. The `run` rows pass either way by design: evidence is read before the default.
#[test]
fn a_row_parameters_default_is_a_written_row_and_evidence_still_wins() {
    let src = r#"
namespace test.gbh5f.row
  import anthill.prelude.{Int64, String, Error}
  operation tick[E = {}]() -> Int64 effects E = 1
  operation useTick() -> Int64 = tick()
  operation boom() -> Int64 effects {Error[String]} = Error.raise("boom")
  operation run[E = {}](f: () -> Int64 @ E) -> Int64 effects E = f()
  operation useRunDeclared() -> Int64 effects {Error[String]} = run(lambda () -> boom())
end
"#;
    let mut interp = interp_for(src);
    let v = interp.call("test.gbh5f.row.useTick", &[]).expect("useTick");
    assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(1));
    let errs = load_errors_of(
        r#"
namespace test.gbh5f.row2
  import anthill.prelude.{Int64, String, Error}
  operation boom() -> Int64 effects {Error[String]} = Error.raise("boom")
  operation run[E = {}](f: () -> Int64 @ E) -> Int64 effects E = f()
  operation useRunPure() -> Int64 = run(lambda () -> boom())
end
"#,
    );
    crate::common::assert_refused_naming(
        &errs,
        &["useRunPure", "Error[T = String]"],
        "the thunk's row is the call's, its default not applying",
    );
}

/// AN OPERATION TYPE PARAMETER'S KIND IS ITS USE, and a sort's effect-row slot is a row
/// use: `noF[E = {}]() -> Option[T = Function[A = Int64, B = Int64, E = E]]`, named or
/// positional, is a row parameter, so `{}` is its default and the call `let o = noF()`,
/// which nothing else settles, takes it. A default naming an enclosing sort's `effects E`
/// is a row too (`go[F = E]() effects F`). CONTROLS: a type default at such a slot is
/// refused as of the wrong kind; the same `noF` with no default is refused as unconstrained
/// (so the call does need the default); a row default for a parameter used as a type
/// (`goT[F = E](x: F)`) is refused; a type default (the enclosing sort's `sort C = ?`) for
/// one used as a row (`goC[F = C]() effects F`) is refused.
///
/// FAILS with `Loader::binds_a_row_slot` answering no: `noF` and `noP` are refused as of
/// the wrong kind, and `typeAtRow`/`typeAtRowP` load. FAILS with
/// `Loader::names_enclosing_row_param` answering no: `go` is refused and `goT` loads. The
/// `goC` refusal and the bare control pass either way by design.
#[test]
fn a_parameter_given_to_a_sorts_row_slot_is_a_row_and_takes_a_row_default() {
    let src = r#"
namespace test.gbh5f.slot
  import anthill.prelude.{Function, Option, Int64}
  import anthill.prelude.Option.{none}
  operation noF[E = {}]() -> Option[T = Function[A = Int64, B = Int64, E = E]] = none()
  operation useNoF() -> Int64 =
    let o = noF()
    1
  operation noP[E = {}]() -> Option[T = Function[Int64, Int64, E]] = none()
  operation useNoP() -> Int64 =
    let o = noP()
    2
  sort Holder
    effects E = ?
    operation go[F = E]() -> Int64 effects F = 3
  end
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [("useNoF", 1), ("useNoP", 2)] {
        let v = interp.call(&format!("test.gbh5f.slot.{op}"), &[]).expect(op);
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(want), "{op}");
    }
    let errs = load_errors_of(
        r#"
namespace test.gbh5f.slot2
  import anthill.prelude.{Function, Option, Int64}
  operation typeAtRow[E = Int64](o: Option[T = Function[A = Int64, B = Int64, E = E]]) -> Int64 = 1
  operation typeAtRowP[E = Int64](o: Option[T = Function[Int64, Int64, E]]) -> Int64 = 1
  sort Holder
    effects E = ?
    operation goT[F = E](x: F) -> Int64 = 0
    sort C = ?
    operation goC[F = C]() -> Int64 effects F = 0
  end
end
"#,
    );
    for (op, kind) in [
        ("typeAtRow", "an effect-row parameter"),
        ("typeAtRowP", "an effect-row parameter"),
        ("Holder.goT", "a type parameter"),
        ("Holder.goC", "an effect-row parameter"),
    ] {
        let want = format!("is {kind} of `test.gbh5f.slot2.{op}`");
        assert!(
            errs.iter().any(|e| e.contains("is of the wrong kind") && e.contains(&want)),
            "{op}: refused as {kind}: {errs:#?}"
        );
    }
    let bare = load_errors_of(
        r#"
namespace test.gbh5f.slot3
  import anthill.prelude.{Function, Option, Int64}
  import anthill.prelude.Option.{none}
  operation noF[E]() -> Option[T = Function[A = Int64, B = Int64, E = E]] = none()
  operation useNoF() -> Int64 =
    let o = noF()
    1
end
"#,
    );
    crate::common::assert_refused_naming(
        &bare,
        &["expected a type for 'E', got unconstrained"],
        "CONTROL: without the default the call leaves `E` open",
    );
}

/// A SPEC CALL THREADED TO ITS OVERRIDE TAKES THE SPEC'S DEFAULT TOO (the WI-606 fallback,
/// WI-20260930-JPSDH's program): `Sp.pick2(a, b)` over `pick2[W = Int64]`, whose return
/// projects the receiver, threads `Car.pick2`, and the `W` nothing at the call binds is the
/// default there as it is on the spec's own path. The expected result is still evidence
/// before it: annotated `B = String`, the call is at `String` (had the default come first,
/// the annotation would contradict it). CONTROL: with no default the call is refused as an
/// unconstrained `W`.
///
/// FAILS with the fallback's installation backed out (`install_type_param_defaults_of` not
/// called in `concrete_override_threaded`): the defaulted program is refused as an
/// unconstrained `W`. The annotated row and the control pass either way by design.
#[test]
fn a_spec_call_threaded_to_its_override_takes_the_specs_default() {
    let program = |ns: &str, spec_w: &str, annotation: Option<&str>| {
        let call = match annotation {
            Some(t) => format!("let r: {t} = Sp.pick2(a, b)\n    match r"),
            None => "match Sp.pick2(a, b)".to_owned(),
        };
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Option, Pair, String}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    effects E = ?
    operation pick2[{spec_w}](x: T, s: Self) -> Option[T = Pair[A = s.T, B = W]] effects s.E
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Self, E = {{EC}}]
    operation pick2[W = Int64, U, R](x: Car[V = U, EC = R], s: Self) -> Option[T = Pair[A = Car[V = V, EC = EC], B = W]] effects {{EC}} = none
  end
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    {call}
      case some(p) -> 1
      case none() -> 7
  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 1)
    use(a, a)
end
"#
        )
    };
    for (ns, annotation) in [
        ("test.gbh5f.fallback", None),
        ("test.gbh5f.fallback_ann", Some("Option[T = Pair[A = Car, B = String]]")),
    ] {
        let mut interp = interp_for(&program(ns, "W = Int64", annotation));
        let v = interp.call(&format!("{ns}.go"), &[]).expect(ns);
        assert_eq!(crate::common::scalar_int(interp.kb(), &v), Some(7), "{ns}");
    }
    crate::common::assert_refused_naming(
        &load_errors_of(&program("test.gbh5f.fallback_bare", "W", None)),
        &["expected a type for 'W', got unconstrained"],
        "CONTROL: with no default the fallback refuses the open `W`",
    );
}

/// A DEFAULT MAY NAME THE ENCLOSING SORT'S PARAMETER, read at the call's instance:
/// `kind[T = C](h: Self)` inside `sort Holder` (`sort C = ?`) answers `Int64` for
/// `holder(c: 5)` and `String` for `holder(c: "s")`. The reflect row and a refusal quote
/// show it by its name, `C`.
///
/// FAILS with the installation at a call backed out: `useKind` is refused as an
/// unconstrained `T`. FAILS with the kind refusal or the reflect row backed out, at its
/// refusal or its reflect half, which read the declaration's record and not the call.
#[test]
fn a_default_naming_the_enclosing_sorts_parameter_is_read_at_the_instance() {
    let src = r#"
namespace test.gbh5f.encl
  import anthill.prelude.{Int64, String, Type}
  import anthill.reflect.{TypeValue, OperationTypeParamDefault}
  sort Holder
    sort C = ?
    entity holder(c: C)
    operation kind[T = C](h: Self) -> Type requires TypeValue[T = T] = TypeValue.type_value[T = T]()
  end
  operation useKind() -> Type = Holder.kind(holder(c: 5))
  operation useKindS() -> Type = Holder.kind(holder(c: "s"))
  rule defaultOf(?d) :- OperationTypeParamDefault(op: ?, param: ?, default: ?d)
end
"#;
    let mut interp = interp_for(src);
    for (op, want) in [("useKind", "Int64"), ("useKindS", "String")] {
        let v = interp.call(&format!("test.gbh5f.encl.{op}"), &[]).expect(op);
        assert_eq!(anthill_core::kb::typing::type_display_name_value(interp.kb(), &v), want, "{op}");
    }
    let mut kb = crate::common::load_kb_with(src);
    let rows: Vec<String> = crate::common::shown_rows(&mut kb, "test.gbh5f.encl.defaultOf")
        .into_iter()
        .map(|(r, _)| r)
        .collect();
    assert_eq!(rows, ["C"], "the reflect row names the sort's parameter");
    let errs = load_errors_of(
        r#"
namespace test.gbh5f.encl2
  import anthill.prelude.{Int64}
  sort Holder
    sort C = ?
    operation bad[E = C]() -> Int64 effects E = 0
  end
end
"#,
    );
    crate::common::assert_refused_naming(
        &errs,
        &["the default of `E` (`E = C`) is of the wrong kind"],
        "the refusal quotes the sort's parameter by its name",
    );
}
