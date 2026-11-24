//! WI-20261113-FCMJA — proposal 074 stage 6: `x.T` READ AS A VALUE IS 065'S DISPATCH
//! (`docs/proposals/074-typeclass-instance-is-a-dictionary.md` §3; T10; kernel-language §8.2).
//!
//! In value position `x.T`, where `x`'s type leaves the member open, is the call
//! `TypeValue.type_value[T = x.T]()`, as a type parameter read as a value is. Its clause,
//! `requires TypeValue[T = x.T]`, is WRITTEN, not inferred: refused without it, over `Num` too,
//! whose `requires TypeValue[T = T]` gives `x`'s dictionary that `TypeValue` (part 2). Where `x`'s
//! spec states it, the clause is supplied from `x`'s dictionary: a call site supplies nothing for
//! it, and a list of such dictionaries mapped through `tOf` answers (part 3). Before the stage,
//! `x.T` read as a value was refused "the receiver's type leaves it open here, so it is no type
//! value"; the spelled call answered over `Additive`; and over `Num` the `map` was refused "cannot
//! be supplied for `tOf` used as a function value", while the same `tOf` with no clause loaded.
//!
//! CONTROLS — the back-out ledger at the end of this file.

use anthill_core::eval::Interpreter;

use crate::common::{interp_for, load_errors_of, show_value};

fn call(interp: &mut Interpreter, op: &str) -> String {
    match interp
        .call(op, &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
    {
        Ok(v) => show_value(interp.kb(), &v),
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

/// T10's declarations: `Num`, which states `requires TypeValue[T = T]`, provided at `Int64` and
/// `Float`; and a dictionary of `Additive` and of `Num` at each.
const T10: &str = "
  sort Num
    sort T = ?
    requires TypeValue[T = T]
    operation add(a: T, b: T) -> T
  end
  sort NumInt
    provides Num[T = Int64]
    operation add(a: Int64, b: Int64) -> Int64 = a + b
  end
  sort NumFloat
    provides Num[T = Float]
    operation add(a: Float, b: Float) -> Float = a + b
  end
  operation ai() -> Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()
  operation af() -> Additive[T = Float] = Dictionary.instance[Additive[T = Float]]()
  operation ni() -> Num[T = Int64] = Dictionary.instance[Num[T = Int64]]()
  operation nf() -> Num[T = Float] = Dictionary.instance[Num[T = Float]]()
";

fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace p074s6.{ns}\n  import anthill.prelude.{{Int64, Float, Bool, Additive, Ord, PartialEq, Type, List}}\n  import anthill.reflect.TypeValue\n  import anthill.realization.runtime.Dictionary\n{T10}{body}\nend\n"
    )
}

fn answers(ns: &str, body: &str, ops: &[(&str, &str)]) {
    let mut interp = interp_for(&program(ns, body));
    for (op, want) in ops {
        assert_eq!(
            call(&mut interp, &format!("p074s6.{ns}.{op}")),
            *want,
            "{op}"
        );
    }
}

fn refusal(ns: &str, body: &str) -> String {
    let errors = load_errors_of(&program(ns, body));
    assert!(!errors.is_empty(), "{ns}: expected a refusal");
    errors.join("\n")
}

/// The refusal part 2 gives, naming the clause to add.
fn names_the_clause(text: &str, read: &str) -> bool {
    text.contains(&format!(
        "expected `requires anthill.reflect.TypeValue[T = {read}]`"
    )) && text.contains(&format!("`{read}` is read as a VALUE"))
}

// ── Part 1: `x.T` in value position is the call ───────────────────────────────────────────

/// T10, first half: under the clause, `x.T` answers the type `x` is at, by key and by position.
#[test]
fn t10_a_member_read_as_a_value_under_its_clause() {
    let body = "  operation tOf(x: Additive) -> Type requires TypeValue[T = x.T] = x.T
  operation byPos(x: Additive) -> Type requires TypeValue[x.T] = x.T
  operation spelled(x: Additive) -> Type requires TypeValue[T = x.T] = TypeValue.type_value[T = x.T]()
  operation go() -> (Type, Type) = (tOf(ai()), tOf(af()))
  operation goPos() -> (Type, Type) = (byPos(ai()), byPos(af()))
  operation goSpelled() -> (Type, Type) = (spelled(ai()), spelled(af()))";
    answers(
        "t10a",
        body,
        &[
            ("go", "(Int64, Float)"),
            ("goPos", "(Int64, Float)"),
            ("goSpelled", "(Int64, Float)"),
        ],
    );
}

/// CONTROL, passes either way by design: a member the parameter's type fixes is that type, and
/// needs no clause.
#[test]
fn a_member_the_parameters_type_fixes_needs_no_clause() {
    let body = "  operation tOf(x: Num[T = Int64]) -> Type = x.T
  operation spelled(x: Num[T = Int64]) -> Type = TypeValue.type_value[T = x.T]()
  operation go() -> (Type, Type) = (tOf(ni()), spelled(ni()))";
    answers("fixed", body, &[("go", "(Int64, Int64)")]);
}

/// Under `x: Num[T = X]`, `x.T` is `X`, read as a value: 065's own clause backs it.
#[test]
fn a_member_the_parameters_type_writes_as_a_type_parameter_is_that_parameter() {
    let body = "  operation byX[X](x: Num[T = X]) -> Type requires TypeValue[T = X] = x.T
  operation go() -> (Type, Type) = (byX(ni()), byX(nf()))";
    answers("rigid", body, &[("go", "(Int64, Float)")]);
}

// ── Part 2: the clause is written, not inferred ───────────────────────────────────────────

/// Without the clause, over `Additive`: refused, naming it.
#[test]
fn without_its_clause_a_member_read_is_refused_naming_it() {
    let text = refusal("noclause", "  operation tOf(x: Additive) -> Type = x.T");
    assert!(names_the_clause(&text, "x.T"), "{text}");
}

/// Over `Num`, whose dictionary holds `TypeValue`, the clause is still written: `x.T`, the
/// spelled call, and the `tOf` mapped over a list are each refused without it. MEASURED before
/// the stage: the spelled `tOf` and the `map` loaded, `Num`'s requirement answering the call.
#[test]
fn over_num_the_clause_is_written_too() {
    let text = refusal("numvalue", "  operation tOf(x: Num) -> Type = x.T");
    assert!(names_the_clause(&text, "x.T"), "{text}");
    let text = refusal(
        "numspelled",
        "  operation tOf(x: Num) -> Type = TypeValue.type_value[T = x.T]()",
    );
    assert!(names_the_clause(&text, "x.T"), "{text}");
    let text = refusal(
        "nummap",
        "  operation tOf(x: Num) -> Type = TypeValue.type_value[T = x.T]()
  operation go() -> List[T = Type] =
      let l: List[T = Num] = [ni(), nf()]
      l.map(tOf).collect()",
    );
    assert!(names_the_clause(&text, "x.T"), "{text}");
}

/// A clause at one parameter's member backs no other's: `y.T` is refused, named.
#[test]
fn a_clause_at_one_parameter_backs_no_other() {
    let text = refusal(
        "twoparams",
        "  operation tOf(x: Num, y: Num) -> (Type, Type) requires TypeValue[T = x.T] = (x.T, y.T)",
    );
    assert!(
        names_the_clause(&text, "y.T") && !names_the_clause(&text, "x.T"),
        "{text}"
    );
    answers(
        "twoclauses",
        "  operation tOf(x: Num, y: Num) -> (Type, Type) requires TypeValue[T = x.T], TypeValue[T = y.T] = (x.T, y.T)
  operation go() -> (Type, Type) = tOf(ni(), nf())",
        &[("go", "(Int64, Float)")],
    );
}

/// Under `x: Num[T = X]`, `x.T` reads `X`, and is refused as `X` is, naming 065's clause: with
/// no clause, and with one at `x.T`, which names the same type by the projection.
#[test]
fn a_member_that_is_a_type_parameter_is_refused_as_the_parameter() {
    for (ns, body) in [
        (
            "rigidnone",
            "  operation tOf[X](x: Num[T = X]) -> Type = x.T",
        ),
        (
            "rigidmember",
            "  operation tOf[X](x: Num[T = X]) -> Type requires TypeValue[T = x.T] = x.T",
        ),
    ] {
        let text = refusal(ns, body);
        assert!(
            text.contains("expected `requires anthill.reflect.TypeValue[T = X]`")
                && text.contains("`X` is read as a VALUE"),
            "{ns}: {text}"
        );
    }
}

/// Off a lambda's binder no clause can be written, and a member it leaves open is refused,
/// pointing to an operation (decided with the user 2026-11-24): `x.T` and the spelled call
/// alike. MEASURED before the stage: the spelled call answered `[Int64, Float]` through `y`'s
/// dictionary, the one read no signature declares.
#[test]
fn off_a_lambdas_binder_an_open_member_is_refused() {
    for (ns, read) in [
        ("lamvalue", "y.T"),
        ("lamspelled", "TypeValue.type_value[T = y.T]()"),
    ] {
        let text = refusal(
            ns,
            &format!(
                "  operation go() -> List[T = Type] =
      let l: List[T = Num] = [ni(), nf()]
      l.map(lambda (y: Num) -> {read}).collect()"
            ),
        );
        assert!(
            text.contains(
                "`y.T` is read as a VALUE off `y`, which is no parameter of the operation"
            ) && text.contains("hand `y` to an operation"),
            "{ns}: {text}"
        );
    }
}

/// A `let` is read at the type it writes: `let y: Num = ni()` leaves `y.T` open, though its
/// value is at `Int64`, and the spelled call off it is refused as off a lambda's binder.
#[test]
fn off_a_let_that_writes_an_open_type_the_member_is_refused() {
    let text = refusal(
        "letann",
        "  operation go() -> Type =
      let y: Num = ni()
      TypeValue.type_value[T = y.T]()",
    );
    assert!(
        text.contains("`y.T` is read as a VALUE off `y`, which is no parameter of the operation"),
        "{text}"
    );
}

/// CONTROL, passes either way by design: a member a binder's type fixes is that type, off a
/// lambda's binder and off a `let`; and a `let` that is a parameter reads the parameter's.
#[test]
fn a_binder_whose_type_fixes_the_member_reads_it() {
    let body = "  operation lam() -> List[T = Type] =
      let l: List[T = Num[T = Int64]] = [ni(), ni()]
      l.map(lambda (y: Num[T = Int64]) -> y.T).collect()
  operation viaLet() -> Type =
      let y = ni()
      y.T
  operation alias(x: Num) -> Type requires TypeValue[T = x.T] =
      let z = x
      z.T
  operation viaAlias() -> Type = alias(nf())";
    answers(
        "binders",
        body,
        &[
            ("lam", "[Int64, Int64]"),
            ("viaLet", "Int64"),
            ("viaAlias", "Float"),
        ],
    );
}

/// Off a field path no clause can be written (a contract clause carries a single reference):
/// refused, saying where one can.
#[test]
fn a_member_off_a_field_path_is_refused_saying_where_a_clause_goes() {
    let text = refusal(
        "compound",
        "  sort Holder
    entity h(s: Num)
  end
  operation tOf(k: Holder) -> Type = k.s.T",
    );
    assert!(
        text.contains("`k.s.T` is read as a VALUE off the field path `k.s`")
            && text.contains("hand `k.s` to an operation"),
        "{text}"
    );
}

/// CONTROL, passes either way by design: a type parameter read as a value is 065's, unchanged.
#[test]
fn a_type_parameter_read_as_a_value_is_unchanged() {
    answers(
        "tparam",
        "  operation tOf[X](y: X) -> Type requires TypeValue[T = X] = X
  operation go() -> Type = tOf(3)",
        &[("go", "Int64")],
    );
    let text = refusal("tparamnone", "  operation tOf[X](y: X) -> Type = X");
    assert!(text.contains("`X` is read as a VALUE"), "{text}");
}

// ── Part 3: where `x`'s spec states it, the clause is supplied from `x` ──────────────────

/// T10, second half: over `Num`, a call site supplies nothing for the clause, so the direct
/// calls answer and the list mapped through `tOf` answers `[Int64, Float]`. MEASURED before the
/// stage: the `map` was refused "cannot be supplied for `tOf` used as a function value"; and,
/// since stage 9, the direct call was refused too, the clause and `x` two handed dictionaries.
#[test]
fn t10_over_num_the_clause_is_supplied_from_the_parameter() {
    let body = "  operation tOf(x: Num) -> Type requires TypeValue[T = x.T] = x.T
  operation spelled(x: Num) -> Type requires TypeValue[T = x.T] = TypeValue.type_value[T = x.T]()
  operation direct() -> (Type, Type) = (tOf(ni()), spelled(nf()))
  operation mapped() -> List[T = Type] =
      let l: List[T = Num] = [ni(), nf()]
      l.map(tOf).collect()
  operation mappedSpelled() -> List[T = Type] =
      let l: List[T = Num] = [ni(), nf()]
      l.map(spelled).collect()
  operation outer(x: Num) -> Type requires TypeValue[T = x.T] = tOf(x)
  operation through() -> (Type, Type) = (outer(ni()), outer(nf()))";
    answers(
        "t10b",
        body,
        &[
            ("direct", "(Int64, Float)"),
            ("mapped", "[Int64, Float]"),
            ("mappedSpelled", "[Int64, Float]"),
            ("through", "(Int64, Float)"),
        ],
    );
}

/// Not `TypeValue` alone: any clause written at a parameter's own member that its dictionary
/// holds through its chain is supplied from it. `o: Ord` holds `PartialEq` at `o.T` (through
/// `WeakOrd` and `Eq`), so `requires PartialEq[T = o.T]` beside it is `o`'s. MEASURED before
/// the stage: refused, "two providers of `PartialEq` the operation is handed answer, the
/// parameter `o` and the clause" (stage 9's rule).
#[test]
fn a_clause_the_parameters_chain_holds_is_supplied_from_it() {
    let body = "  operation oi() -> Ord[T = Int64] = Dictionary.instance[Ord[T = Int64]]()
  operation same(o: Ord, a: o.T, b: o.T) -> Bool requires PartialEq[T = o.T] = PartialEq.eq(a, b)
  operation go() -> (Bool, Bool) = (same(oi(), 2, 2), same(oi(), 2, 3))";
    answers("ord", body, &[("go", "(true, false)")]);
}

/// CONTROL, passes either way by design (it was refused before the stage too): over
/// `Additive`, which states no `TypeValue`, the same `map` is refused, since nothing supplies
/// it at each element's `T`.
#[test]
fn over_additive_the_map_is_refused() {
    let text = refusal(
        "addmap",
        "  operation tOf(x: Additive) -> Type requires TypeValue[T = x.T] = x.T
  operation go() -> List[T = Type] =
      let l: List[T = Additive] = [ai(), af()]
      l.map(tOf).collect()",
    );
    assert!(
        text.contains("cannot be supplied for `p074s6.addmap.tOf` used as a function value"),
        "{text}"
    );
}

// ── kernel-language §8.2's program, as written there ──────────────────────────────────────

/// §8.2's program, spelled as the spec spells it (positional type arguments where a sort has
/// one parameter), with the values its comments give. The same program as the `t10_*` rows and
/// `a_clause_the_parameters_chain_holds_is_supplied_from_it`, in the other spelling; added after
/// the back-out runs, so not itself measured under the switches.
const SPEC_PROGRAM: &str = "namespace p074s6.spec
  import anthill.prelude.{Int64, Float, Bool, Additive, Ord, PartialEq, Type, List}
  import anthill.reflect.TypeValue
  import anthill.realization.runtime.Dictionary
  sort Num
    sort T = ?
    requires TypeValue[T]
    operation add(a: T, b: T) -> T
  end
  sort NumInt
    provides Num[Int64]
    operation add(a: Int64, b: Int64) -> Int64 = a + b
  end
  sort NumFloat
    provides Num[Float]
    operation add(a: Float, b: Float) -> Float = a + b
  end
  operation ni() -> Num[Int64] = Dictionary.instance[Num[Int64]]()
  operation nf() -> Num[Float] = Dictionary.instance[Num[Float]]()
  operation ai() -> Additive[Int64] = Dictionary.instance[Additive[Int64]]()
  operation af() -> Additive[Float] = Dictionary.instance[Additive[Float]]()
  operation numOf(x: Num) -> Type requires TypeValue[x.T] = x.T
  operation addOf(x: Additive) -> Type requires TypeValue[x.T] = x.T
  operation viaNum() -> (Type, Type) = (numOf(ni()), numOf(nf()))
  operation viaAdd() -> (Type, Type) = (addOf(ai()), addOf(af()))
  operation mapNum() -> List[Type] =
    let l: List[Num] = [ni(), nf()]
    l.map(numOf).collect()
  operation same(o: Ord, a: o.T, b: o.T) -> Bool requires PartialEq[o.T] = PartialEq.eq(a, b)
  operation go() -> (Bool, Bool) =
    (same(Dictionary.instance[Ord[Int64]](), 2, 2),
     same(Dictionary.instance[Ord[Int64]](), 2, 3))
  operation fixedOf(x: Num[Int64]) -> Type = x.T
  operation rigidOf[X](x: Num[X]) -> Type requires TypeValue[X] = x.T
  operation goFixed() -> (Type, Type) = (fixedOf(ni()), rigidOf(nf()))
";

#[test]
fn the_spec_program_answers_as_written() {
    let mut interp = interp_for(&format!("{SPEC_PROGRAM}end\n"));
    for (op, want) in [
        ("viaNum", "(Int64, Float)"),
        ("viaAdd", "(Int64, Float)"),
        ("mapNum", "[Int64, Float]"),
        ("go", "(true, false)"),
        ("goFixed", "(Int64, Float)"),
    ] {
        assert_eq!(call(&mut interp, &format!("p074s6.spec.{op}")), want, "{op}");
    }
}

/// §8.2's refusals of the same program: `mapAdd`, and `numOf` / `addOf` without their clauses.
#[test]
fn the_spec_programs_refusals() {
    let text = load_errors_of(&format!(
        "{SPEC_PROGRAM}  operation mapAdd() -> List[Type] =
    let l: List[Additive] = [ai(), af()]
    l.map(addOf).collect()
end
"
    ))
    .join("\n");
    assert!(
        text.contains("cannot be supplied for `p074s6.spec.addOf` used as a function value"),
        "{text}"
    );
    let text = load_errors_of(&format!(
        "{SPEC_PROGRAM}  operation numBare(x: Num) -> Type = x.T
  operation addBare(x: Additive) -> Type = x.T
end
"
    ))
    .join("\n");
    assert!(
        text.contains("p074s6.spec.numBare") && text.contains("p074s6.spec.addBare"),
        "{text}"
    );
    assert!(names_the_clause(&text, "x.T"), "{text}");
}

// ── Back-out ledger ───────────────────────────────────────────────────────────────────────
//
// MEASURED 2026-11-24: each part backed out by a temporary switch, every row of anthill-core
// run (control 11640 passed, 0 failed); the rows each fails, beside this file's.
//
// Part 1, `x.T` in value position is the call, and `X` where the type writes a type parameter
// (`type_member_as_value`): 11 rows — `t10_a_member_read_as_a_value_under_its_clause`,
// `a_member_the_parameters_type_writes_as_a_type_parameter_is_that_parameter`,
// `without_its_clause_a_member_read_is_refused_naming_it`, `over_num_the_clause_is_written_too`,
// `a_clause_at_one_parameter_backs_no_other`,
// `a_member_that_is_a_type_parameter_is_refused_as_the_parameter`,
// `off_a_lambdas_binder_an_open_member_is_refused`, `a_binder_whose_type_fixes_the_member_reads_it`,
// `a_member_off_a_field_path_is_refused_saying_where_a_clause_goes`,
// `t10_over_num_the_clause_is_supplied_from_the_parameter`, and wi_qk77s's
// `a_type_member_in_a_value_bracket_is_the_member` (its `vb2` refused "the receiver's type leaves
// it open here" again).
//
// Part 2, the clause is written, not inferred (`unwritten_member_value_read`): 6 rows —
// `without_its_clause_a_member_read_is_refused_naming_it`, `over_num_the_clause_is_written_too`,
// `a_clause_at_one_parameter_backs_no_other`, `off_a_lambdas_binder_an_open_member_is_refused`,
// `a_member_off_a_field_path_is_refused_saying_where_a_clause_goes`, and wi_qk77s's
// `a_type_member_in_a_value_bracket_is_the_member`.
//
// Part 3, a clause the parameter's dictionary holds is supplied from it (`op_requires_chain_rc`):
// 4 rows — `t10_over_num_the_clause_is_supplied_from_the_parameter`,
// `a_clause_at_one_parameter_backs_no_other`, `a_binder_whose_type_fixes_the_member_reads_it`
// (its `alias` writes the clause beside `x: Num`), and
// `a_clause_the_parameters_chain_holds_is_supplied_from_it` (this one measured on this file, added
// after the full runs).
//
// Pass under every part by design: `a_member_the_parameters_type_fixes_needs_no_clause`,
// `a_type_parameter_read_as_a_value_is_unchanged`, `over_additive_the_map_is_refused`.
