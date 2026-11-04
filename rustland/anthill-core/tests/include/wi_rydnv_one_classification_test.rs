//! WI-20261013-RYDNV — one classification per rule-body call (068 C1d). First part: a spec
//! operation's call whose instance the call does not fix, decided as an operation body decides
//! it (decided with the user 2026-10-31). The requested instance is held to the provisions
//! with each parameter nothing at the call fixes as a rigid variable: it is answered by a
//! provision only where it conforms to it for every type that parameter could be. A parameter
//! the carrier's provision determines is read off that provision, as `Iterable.find(xs)`
//! reads `Element` off `List`'s.
//!
//! ## Back-out
//!
//! Each measured alone over this file:
//!   * the spec's carrier parameter skipped again as one the signature never writes (the
//!     `is_carrier` leg of the abstract-dispatch arm in `check_apply_iter`) —
//!     `an_unfixed_carrier_is_refused_in_both_bodies` (both load);
//!   * the providers at the carrier not compared (`providers_apart_at_carrier`) —
//!     `providers_at_the_carrier_that_fix_the_open_parameter_apart_are_refused` (both load and
//!     answer `Meters`' 3);
//!   * the clause's `require[…]` not read at the carrier (`clause_required_view_at_carrier`) —
//!     `a_clause_require_names_the_instance_at_its_carrier` (`3`, `Meters`', for `Feet`'s 4),
//!     measured while the clause could write `require[…]`; proposal 060.1 §5 removed it, and the
//!     row writes the instance on the call's receiver, `Conv[A = Feet, B = String].tag(…)`.
//!
//!   * an operation's own `requires` left to the clause however the call's types fix it
//!     (`own_requirements_fixed_at` answering no) — both rows of the pinned class here, and the
//!     load halves of `wi_gfs6a`'s four KCNA0 rows (each loads);
//!   * a requirement the call fixes refused with the rule-body account that says nothing fixes
//!     it — `wi_gfs6a`'s q2 and fwd rows (their refusal does not say no impl provides it).
//!
//!   * the witness of a written `require[…]` read off the body's goals alone
//!     (`calls_run_with_their_goal`) — `a_requires_witness_in_a_value_slot_grounds_it`, while
//!     the clause could write one (removed by 060.1 §5; the row is the instance written at a
//!     call in a value slot now);
//!   * the provider question left out of `own_requirements_carried_by_arguments` —
//!     `a_requirement_at_a_spec_nothing_provides_is_refused_in_every_position`;
//!   * that function answering yes whatever the parameters write — P7VP4's
//!     `a_requirement_no_argument_names_is_refused_in_every_position`;
//!   * an `=` operand's call checked for its own `requires` as an operation body's again
//!     (`leaves_own_requirements_to_the_clause` the fragment's alone) — P7VP4's
//!     `an_operations_own_requires_is_its_clauses_condition_in_every_position`, `wi842`'s
//!     `a_rule_body_tie_is_decided_when_the_goal_runs_on_both_arms` and `wi_n31xx`'s
//!     `a_rule_body_forward_is_the_clauses_condition` (each refused at load).
//!
//! Outside this file, measured on the full gate: a parameter read through a projection off an
//! argument (`get(c: C) -> c.T`) counted as open — three `wi_0rp29` rows, whose witnesses are
//! held to agree on the member where the projection is read, get this file's refusal in place
//! of theirs.
//!
//! Pass either way, by design: the repairs of the unfixed carrier, the one provider at a
//! carrier, providers at two carriers, and the two rows written with the instance at the call
//! since 060.1 §5.

use anthill_core::eval::Value;

/// `Conv`'s carrier is `A`, the first parameter an operation receives on (`conv(a: A, b: B)`);
/// `tag(b: B)` writes none of it. Two providers, at `B = String` both.
const AT_A: &str = r#"
  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
    operation tag(b: B) -> Int64
  end
  sort Meters
    entity m(v: Int64)
    provides Conv[A = Meters, B = String]
    operation conv(a: Meters, b: String) -> Int64 = 7
    operation tag(b: String) -> Int64 = 3
  end
  sort Feet
    entity f(v: Int64)
    provides Conv[A = Feet, B = String]
    operation conv(a: Feet, b: String) -> Int64 = 8
    operation tag(b: String) -> Int64 = 4
  end
"#;

/// `Conv` declares only `tag(b: B)`, so its carrier is `B`, and `A` is read off the provision at
/// the call's `B`. `FEET` is a second provider at `B = String`, `FEET_INT` one at `B = Int64`.
const AT_B: &str = r#"
  sort Conv
    sort A = ?
    sort B = ?
    operation tag(b: B) -> Int64
  end
  sort Meters
    entity m(v: Int64)
    provides Conv[A = Meters, B = String]
    operation tag(b: String) -> Int64 = 3
  end
"#;

const FEET: &str = r#"
  sort Feet
    entity f(v: Int64)
    provides Conv[A = Feet, B = String]
    operation tag(b: String) -> Int64 = 4
  end
"#;

const FEET_INT: &str = r#"
  sort Feet
    entity f(v: Int64)
    provides Conv[A = Feet, B = Int64]
    operation tag(b: Int64) -> Int64 = 4
  end
"#;

fn program(ns: &str, decls: &[&str], body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String, Bool}}\n{}{body}\nend\n",
        decls.concat()
    )
}

/// The value of the nullary operation `qn`, run by the interpreter.
fn run(src: &str, qn: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(qn, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{qn}: expected an Int64, got {other:?}"),
    }
}

/// NOTHING AT THE CALL FIXES THE CARRIER: `Conv.tag("km")` requests `Conv[A = a, B = String]`
/// for every `a`, which no provision answers. Both bodies loaded, and the call answered
/// nothing when it ran — a residual from a rule body, a failed dispatch from an operation's.
/// FAILS with the carrier skipped again: both load.
#[test]
fn an_unfixed_carrier_is_refused_in_both_bodies() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "rydnv.unfixedrule",
            &[AT_A],
            "  rule t(?r) :- Conv.tag(\"km\", ?r)",
        )),
        &["rydnv.unfixedrule.Conv.tag", "the instance written at the call, `Conv[A = …].tag(…)`"],
        "a rule body names the instance at the call as the repair",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "rydnv.unfixedop",
            &[AT_A],
            "  sort U\n    operation use() -> Int64 = Conv.tag(\"km\")\n  end",
        )),
        &["rydnv.unfixedop.Conv.tag", "requires Conv[A = …]", "rydnv.unfixedop.U.use"],
        "an operation body names a `requires` on the operation",
    );
}

/// THE REPAIRS, each run: the instance written on the rule-body call's receiver, with its `B`
/// written and without; the operation-body call's bracket; an operation's `requires`. Each
/// names `Meters` and answers its 3, and an instance naming `Feet` answers `Feet`'s 4. Pass
/// either way. (The rule-body repair was the clause's `require[Conv[A = Meters, B = String]]`,
/// which proposal 060.1 §5 removed; the receiver's bracket answered the same on d39bd428.)
#[test]
fn the_repairs_of_an_unfixed_carrier_answer() {
    let ns = "rydnv.repairs";
    let src = program(
        ns,
        &[AT_A],
        "  sort U\n    \
         operation br() -> Int64 = Conv[A = Meters].tag(\"km\")\n    \
         operation viaReq[X](s: X) -> Int64 requires Conv[A = Meters, B = X] = Conv.tag(s)\n  \
         end\n  \
         rule full(?r) :- Conv[A = Meters, B = String].tag(\"km\", ?r)\n  \
         rule part(?r) :- Conv[A = Meters].tag(\"km\", ?r)\n  \
         rule feet(?r) :- Conv[A = Feet, B = String].tag(\"km\", ?r)\n  \
         rule through(?r) :- ?r <=> U.viaReq(\"km\")",
    );
    let mut kb = crate::common::load_kb_with(&src);
    for (rule, want) in [("full", 3), ("part", 3), ("feet", 4), ("through", 3)] {
        assert_eq!(
            crate::common::one_definite_int(&mut kb, &format!("{ns}.{rule}")),
            Some(want),
            "`{rule}`"
        );
    }
    assert_eq!(run(&src, &format!("{ns}.U.br")), 3, "the bracket");
}

/// TWO PROVIDERS AT THE CARRIER THAT FIX THE OPEN PARAMETER APART: at `B = String` both
/// `Meters` and `Feet` provide `Conv`, and `Conv.tag("km")` leaves `A` to them. The call took
/// the first provision's `A` and answered `Meters`' 3 in both bodies. Refused now, each body
/// naming the instance to write. FAILS with the providers not compared: both load and answer
/// 3.
#[test]
fn providers_at_the_carrier_that_fix_the_open_parameter_apart_are_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "rydnv.apartrule",
            &[AT_B, FEET],
            "  rule t(?r) :- Conv.tag(\"km\", ?r)",
        )),
        &[
            "names no instance of `rydnv.apartrule.Conv`: it leaves `A` open",
            "`rydnv.apartrule.Meters` and `rydnv.apartrule.Feet`",
            "Write the instance: `Conv[A = …, B = String].tag(…)`",
        ],
        "the rule body",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "rydnv.apartop",
            &[AT_B, FEET],
            "  sort U\n    operation use() -> Int64 = Conv.tag(\"km\")\n  end",
        )),
        &[
            "it leaves `A` open",
            "`rydnv.apartop.Conv.tag[A = …](…)`",
        ],
        "the operation body",
    );
}

/// THE INSTANCE WRITTEN AT THE CALL NAMES IT AT ITS CARRIER: over the same two providers,
/// `Conv[A = Feet, B = String].tag("km", ?r)` answers `Feet`'s 4 — the repair the refusal above
/// names. The clause wrote `require[Conv[A = Feet, B = String]]` before the call, which
/// proposal 060.1 §5 removed; then the typer read `A` off the first provision at `String` and
/// pinned `Meters`' member, so the clause answered 3 under a `require` naming `Feet`, and the
/// row FAILED with the clause's `require` not read at the carrier. The receiver's bracket
/// answered 4 on d39bd428 too, so the row passes either way now. The bracket in an operation
/// body, `Conv[A = Feet].tag("km")`, answers 4 either way.
#[test]
fn a_clause_require_names_the_instance_at_its_carrier() {
    let ns = "rydnv.declared";
    let src = program(
        ns,
        &[AT_B, FEET],
        "  sort U\n    operation br() -> Int64 = Conv[A = Feet].tag(\"km\")\n  end\n  \
         rule t(?r) :- Conv[A = Feet, B = String].tag(\"km\", ?r)",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(crate::common::one_definite_int(&mut kb, &format!("{ns}.t")), Some(4));
    assert_eq!(run(&src, &format!("{ns}.U.br")), 4, "the bracket");
}

/// CONTROLS, passing either way: one provider at the carrier, whose provision determines `A`
/// (3 in both bodies), and providers at two carriers, `String` and `Int64` (3).
#[test]
fn a_provision_at_the_carrier_determines_what_the_call_leaves_open() {
    for (ns, decls) in [("rydnv.one", vec![AT_B]), ("rydnv.twocarriers", vec![AT_B, FEET_INT])] {
        let src = program(
            ns,
            &decls,
            "  sort U\n    operation use() -> Int64 = Conv.tag(\"km\")\n  end\n  \
             rule t(?r) :- Conv.tag(\"km\", ?r)",
        );
        let mut kb = crate::common::load_kb_with(&src);
        assert_eq!(crate::common::one_definite_int(&mut kb, &format!("{ns}.t")), Some(3), "{ns}");
        assert_eq!(run(&src, &format!("{ns}.U.use")), 3, "{ns}");
    }
}

/// THE SAME CALL UNDER A RULE BODY'S COMPOUND EXPRESSION is refused as the bare one is: what
/// stands under a `let` is typed as an operation body's text, whose refusal is tagged for a
/// pass that reads no rule body, so it loaded, silently (found by `/code-review`). FAILS with
/// the refusal asked of the rule's own term alone.
#[test]
fn an_unfixed_carrier_under_a_let_is_refused_too() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "rydnv.unfixedlet",
            &[AT_A],
            "  rule t(?r) :- ?r <=> (let s = \"km\"  Conv.tag(s))",
        )),
        &["rydnv.unfixedlet.Conv.tag", "the instance written at the call, `Conv[A = …].tag(…)`"],
        "under a `let`",
    );
}

/// A REQUIREMENT IN SCOPE AT ANOTHER CARRIER COVERS NOTHING HERE: a sort that requires `Conv`
/// at `B = Int64` does not name the instance of a call at `B = String`, which the two
/// providers there still leave open (found by `/code-review`; it was read as covered by the
/// spec's symbol alone, and the first provision's `A` answered). FAILS with any same-spec
/// requirement read as covering.
#[test]
fn a_requirement_at_another_carrier_does_not_name_the_instance() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "rydnv.othercarrier",
            &[AT_B, FEET],
            "  sort U\n    requires Conv[A = Meters, B = Int64]\n    \
             operation use() -> Int64 = Conv.tag(\"km\")\n  end",
        )),
        &["it leaves `A` open", "rydnv.othercarrier.Conv.tag[A = …](…)"],
        "a requirement at `Int64` beside a call at `String`",
    );
}

// ── an operation's own `requires` its call fixes is decided at load ───────────────────────

/// `d`'s `Desc[T = T]` at its default `Int64` and `whichN`'s `TypeValue[T = T]` at a typed head:
/// the call's types fix each, and a second provider of the spec (`StrDesc`) leaves the
/// arguments nothing to derive it from.
const OWN: &str = r#"
  import anthill.prelude.{Option, Type}
  import anthill.reflect.{TypeValue}
  sort Desc
    sort T = ?
    operation describe() -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation describe() -> Int64 = 7
  end
  sort StrDesc
    provides Desc[T = String]
    operation describe() -> Int64 = 8
  end
  sort U
    operation d[T = Int64]() -> Int64 requires Desc[T = T] = Desc[T = T].describe()
    operation whichN[T](o: Option[T]) -> Type requires TypeValue[T = T] = TypeValue.type_value[T]()
  end
"#;

/// A REQUIREMENT THE CALL'S TYPES FIX IS DECIDED AT LOAD (068 C1d's pinned class): `U.d(?n)`
/// and `?n <=> U.d()` answer `IntDesc`'s 7, `U.whichN(?o, ?t)` under `?o: Option[T = Int64]`
/// answers `Int64` — each as its operation-body twin does. The clause was handed the
/// requirement as its condition, which read the argument values — none — and a debug build
/// aborted ("`__req_desc` not bound in caller frame", WI-20261023-GBH5F's row). FAILS with the
/// requirement left to the clause however the call's types fix it (`own_requirements_fixed_at`).
#[test]
fn an_operations_own_requirement_its_call_fixes_is_decided_at_load() {
    let ns = "rydnv.own";
    let src = program(
        ns,
        &[OWN],
        "  rule viaRule(?n) :- U.d(?n)\n  \
         rule viaVal(?n) :- ?n <=> U.d()\n  \
         rule r(?o: Option[T = Int64], ?t) :- U.whichN(?o, ?t)\n  \
         rule which(?t) :- r(Option.none(), ?t)",
    );
    let mut kb = crate::common::load_kb_with(&src);
    for rule in ["viaRule", "viaVal"] {
        assert_eq!(crate::common::one_definite_int(&mut kb, &format!("{ns}.{rule}")), Some(7), "`{rule}`");
    }
    let rows = crate::common::shown_rows(&mut kb, &format!("{ns}.which"));
    assert_eq!(rows, vec![("Int64".to_string(), true)], "`whichN` at the typed head");
}

/// … AND REFUSED AT LOAD WHERE NOTHING PROVIDES IT, with the refusal its operation-body twin
/// gets: `d[T = Bool]` with no provider at `Bool` answered `IntDesc`'s 7 — the bridge took the
/// one provider of `Desc` there was — and two providers at `Int64` aborted a debug build. FAILS
/// as the row above does: the first loads and answers 7.
#[test]
fn an_operations_own_requirement_its_call_fixes_with_no_provider_is_refused() {
    let errs = crate::common::load_errors_of(&program(
        "rydnv.ownnone",
        &[r#"
  sort Desc
    sort T = ?
    operation describe() -> Int64
  end
  sort IntDesc
    provides Desc[T = Int64]
    operation describe() -> Int64 = 7
  end
  sort U
    operation d[T = Bool]() -> Int64 requires Desc[T = T] = Desc[T = T].describe()
    operation twin() -> Int64 = d()
  end
"#],
        "  rule v(?n) :- U.d(?n)",
    ));
    let refused: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("`rydnv.ownnone.Desc[T = anthill.prelude.Bool]` cannot be supplied"))
        .collect();
    assert_eq!(refused.len(), 2, "the rule body and its operation-body twin: {errs:#?}");
    let text = |e: &str| e.split_once(": type mismatch").map(|(_, t)| t.to_string());
    assert_eq!(text(refused[0]), text(refused[1]), "one refusal, written twice");
}

/// A REQUIREMENT AT A PROJECTION IS FIXED ONLY WHERE THE ARGUMENT'S TYPE GROUNDS IT: over
/// `pick(x: Box) requires Desc[T = x.E]`, `pick(?b, ?r)` at a head variable the clause leaves
/// untyped is the clause's condition, and answers `Red`'s 7 through `r(box(v: red()), ?r)` —
/// in the goal spelling and in a value slot. `x.E` holds no variable, so read as ground it was
/// fixed, and the clause refused (found reviewing this part). FAILS with the projection not
/// read at the argument's type in `own_requirements_fixed_at`: both clauses refused.
#[test]
fn a_requirement_at_a_projection_the_clause_leaves_open_is_its_condition() {
    let ns = "rydnv.proj";
    let src = program(
        ns,
        &[r#"
  sort Desc
    sort T = ?
    operation tag() -> Int64
  end
  sort Red
    entity red
    provides Desc[T = Red]
    operation tag() -> Int64 = 7
  end
  sort Box
    sort E = ?
    entity box(v: E)
  end
  operation pick(x: Box) -> Int64 requires Desc[T = x.E] = Desc.tag[T = x.E]()
"#],
        "  rule r(?b, ?r) :- pick(?b, ?r)\n  \
         rule rv(?b, ?r) :- ?r <=> pick(?b)\n  \
         rule q(?r) :- r(box(v: red()), ?r)\n  \
         rule qv(?r) :- rv(box(v: red()), ?r)",
    );
    let mut kb = crate::common::load_kb_with(&src);
    for rule in ["q", "qv"] {
        assert_eq!(crate::common::one_definite_int(&mut kb, &format!("{ns}.{rule}")), Some(7), "`{rule}`");
    }
}

// ── the class read in every position ──────────────────────────────────────────────────────

/// AN INSTANCE WRITTEN AT A CALL IN A VALUE SLOT: `?r <=> Conv[A = Meters, B =
/// String].tag("km")` answers `Meters`' 3, as its goal spelling does. The row was the witness of
/// a `require[Conv[A = Meters, B = String]]` standing in the value slot, which the witness scan
/// read off the clause's top-level goals alone, refusing the clause "no body call … to ground
/// the requirement" (FAILED with that scan restored, `calls_run_with_their_goal`). Proposal
/// 060.1 §5 removed `require[…]`; the instance is written on the call now, and the row passes
/// either way.
#[test]
fn a_requires_witness_in_a_value_slot_grounds_it() {
    let ns = "rydnv.valuewitness";
    let src = program(
        ns,
        &[AT_A],
        "  rule t(?r) :- ?r <=> Conv[A = Meters, B = String].tag(\"km\")",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(crate::common::one_definite_int(&mut kb, &format!("{ns}.t")), Some(3));
}

/// A REQUIREMENT AT A SPEC NOTHING PROVIDES IS REFUSED IN EVERY POSITION: no value could
/// derive it, so it is no condition of the clause. `stampOf(?x, ?n)` over `stampOf[B](x: B)
/// requires Stamp[T = B]`, beside no provider of `Stamp`, loaded at goal position and was
/// declined by the inference, while `?n = stampOf(?x)` was refused. FAILS with the provider
/// question left out of `own_requirements_carried_by_arguments`: both load.
#[test]
fn a_requirement_at_a_spec_nothing_provides_is_refused_in_every_position() {
    let decl = r#"
  sort Stamp
    sort T = ?
    operation stamp() -> Int64
  end
  operation stampOf[B](x: B) -> Int64 requires Stamp[T = B] = Stamp.stamp[T = B]()
"#;
    for (spelling, clause) in [
        ("goal", "  rule names(?x, ?n) :- stampOf(?x, ?n)"),
        ("operand", "  rule names(?x, ?n) :- ?n = stampOf(?x)"),
        ("value", "  rule names(?x, ?n) :- ?n <=> stampOf(?x)"),
    ] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&program("rydnv.noprovider", &[decl], clause)),
            &["rydnv.noprovider.Stamp", "cannot be supplied for call to `rydnv.noprovider.stampOf`"],
            spelling,
        );
    }
}

// ── a call in a connective's goal slot ────────────────────────────────────────────────────

/// `Util.sign`, whose `WeakOrd[T = A]` is a condition of the clause, and the `Ascending` and
/// `Descending` orders over `Int64` a citation can select.
const ORDERS: &str = r#"
  import anthill.prelude.{Error, EmptyStream, WeakOrd, Ord}
  import anthill.prelude.Numeric.{sub}
  sort Ascending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end
  sort Descending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Util
    operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
  end
"#;

/// `rel` cited at `(1, 5)` under `Descending`, under `Ascending` and uncited: how many answers
/// each citation gets, and the first one's `c` where there is one.
fn cited_counts(ns: &str, rules: &str, rel: &str) -> [(i64, Option<i64>); 3] {
    let src = program(
        ns,
        &[ORDERS],
        &format!(
            "{rules}\n  sort Driver\n    \
             operation n[A](x: A, y: A) -> Int64 effects {{Error}} requires WeakOrd[T = A] = \
             {rel}(x, y).takeN(5).length()\n    \
             operation desc() -> Int64 effects {{Error}} = n[A = Int64, WeakOrd = Descending](1, 5)\n    \
             operation asc() -> Int64 effects {{Error}} = n[A = Int64, WeakOrd = Ascending](1, 5)\n    \
             operation plain() -> Int64 effects {{Error}} = {rel}(1, 5).takeN(5).length()\n    \
             operation first[A](x: A, y: A) -> Int64 effects {{Error, Error[EmptyStream]}} \
             requires WeakOrd[T = A] = {rel}(x, y).head.c\n    \
             operation descC() -> Int64 effects {{Error, Error[EmptyStream]}} = \
             first[A = Int64, WeakOrd = Descending](1, 5)\n    \
             operation ascC() -> Int64 effects {{Error, Error[EmptyStream]}} = \
             first[A = Int64, WeakOrd = Ascending](1, 5)\n    \
             operation plainC() -> Int64 effects {{Error, Error[EmptyStream]}} = {rel}(1, 5).head.c\n  \
             end"
        ),
    );
    let mut interp = crate::common::interp_for(&src);
    let mut at = |entry: &str| match interp.call(&format!("{ns}.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => Some(n),
        _ => None,
    };
    let row = |n: Option<i64>, c: Option<i64>| (n.expect("a count"), c);
    [
        row(at("desc"), at("descC")),
        row(at("asc"), at("ascC")),
        row(at("plain"), at("plainC")),
    ]
}

/// A CALL IN AN `|` BRANCH IS A CONDITION OF THE CLAUSE, its read standing beside it in the
/// branch (`or(and(find_dictionary(…), sign(…)), …)`), where a citation routes to it as to one
/// at the top of the body: each branch spelling answers `Descending`'s 4, `Ascending`'s -4 and
/// `Int64`'s own -1, as the goal spelling does, and so does a branch whose call's witness is
/// bound in the branch alone (`?x`) — for an operation's own `requires` (`Util.sign`) and for a
/// spec operation (`WeakOrd.compare`). It had no read, and answered `Int64`'s -1 under both
/// rivals. FAILS with the reads placed at the body's own goals alone (`nested_goals` pushing
/// nothing): `-1` under each citation, for every spelling but the goal ones, which pass either
/// way by design.
#[test]
fn a_call_in_a_branch_is_its_clauses_condition() {
    for (ns, rule) in [
        ("rydnv.branchl", "  rule r(?a, ?b, ?c) :- (Util.sign(?a, ?b, ?c) | 1 = 2)"),
        ("rydnv.branchr", "  rule r(?a, ?b, ?c) :- (1 = 2 | Util.sign(?a, ?b, ?c))"),
        (
            "rydnv.branchlocal",
            "  rule r(?a, ?b, ?c) :- (?x <=> ?a & Util.sign(?x, ?b, ?c)) | 1 = 2",
        ),
        ("rydnv.branchgoal", "  rule r(?a, ?b, ?c) :- Util.sign(?a, ?b, ?c)"),
        ("rydnv.dbranchl", "  rule r(?a, ?b, ?c) :- (WeakOrd.compare(?a, ?b, ?c) | 1 = 2)"),
        ("rydnv.dbranchr", "  rule r(?a, ?b, ?c) :- (1 = 2 | WeakOrd.compare(?a, ?b, ?c))"),
        (
            "rydnv.dbranchlocal",
            "  rule r(?a, ?b, ?c) :- (?x <=> ?a & WeakOrd.compare(?x, ?b, ?c)) | 1 = 2",
        ),
        ("rydnv.dbranchgoal", "  rule r(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)"),
    ] {
        assert_eq!(
            cited_counts(ns, rule, "r"),
            [(1, Some(4)), (1, Some(-4)), (1, Some(-1))],
            "{ns}"
        );
    }
}

/// A GOAL ON A DEFINED OPERATION BESIDE ITS CLAUSES IS THE RELATION'S, whatever the declaring
/// sort: with a clause at the operation's own arity, an arity + 1 goal is read against the
/// clauses and refused for its arity — for `sort Tool`'s bodied operation (no parameter, no
/// provider) in both its spellings, the positional result column and `result:`, for one of
/// `Prov` (which provides `Desc` and is provided by nothing), for a parametric data sort's
/// bodied operation and for the host operation `String.length`. The walk
/// gate reads no provider, so each is a spec operation's call to it; FAILS with that call taken
/// for the goal where clauses define the functor (rule_dispatch's rung 2 condition backed out):
/// each loads clean, the call answering where the relation was written. `Held.peek` loaded clean
/// before this ticket too, its sort being walked for its parameter. A goal at the parameter list
/// beside clauses stays the call (`gte` and its laws, `wi_9c2pz`, `wi_4nekz`).
#[test]
fn a_goal_on_a_defined_operation_beside_its_clauses_is_the_relations() {
    let tool = "  sort Tool\n    operation size(x: Int64) -> Int64 = x\n  end";
    let two = "got 2 positional";
    for (ns, decl, clause, goal, functor, got) in [
        ("rydnv.arity.tool", tool, "Tool.size(1)", "Tool.size(1, ?n)", "Tool.size", two),
        (
            "rydnv.arity.result",
            tool,
            "Tool.size(1)",
            "Tool.size(1, result: ?n)",
            "Tool.size",
            "got 1 positional + `result`",
        ),
        (
            "rydnv.arity.prov",
            "  sort Desc\n    sort T = ?\n    operation describe(x: T) -> Int64\n  end\n  \
             sort Prov\n    provides Desc[T = Int64]\n    \
             operation describe(x: Int64) -> Int64 = 9\n    \
             operation own(x: Int64) -> Int64 = x\n  end",
            "Prov.own(1)",
            "Prov.own(1, ?n)",
            "Prov.own",
            two,
        ),
        (
            "rydnv.arity.data",
            "  sort Held\n    sort V = ?\n    entity held(v: V)\n    \
             operation peek(h: Held[V]) -> V = h.v\n  end",
            "Held.peek(held(v: 1))",
            "Held.peek(held(v: 1), ?n)",
            "Held.peek",
            two,
        ),
        (
            "rydnv.arity.host",
            "  import anthill.prelude.{String}",
            "String.length(\"abc\")",
            "String.length(\"abc\", ?n)",
            "anthill.prelude.String.length",
            two,
        ),
    ] {
        let errs = crate::common::load_errors_of(&format!(
            "namespace test.{ns}\n  import anthill.prelude.{{Int64}}\n{decl}\n  \
             rule {clause} :- true\n  rule asked(?n) :- {goal}\nend\n"
        ));
        assert!(
            errs.len() == 1 && errs[0].contains(&format!("{functor}` can match (1 positional), {got}")),
            "{ns}: expected the one arity refusal of `{goal}`, got {errs:?}"
        );
    }
}

/// A LAW IN ITS SPEC'S OWN SORT IS ITS CLAUSE'S CONDITION, nothing providing the spec: a law
/// written in `Spec` is the law of every carrier, and its citation supplies the instance, so
/// `heavy`'s open `w(?a)` loads. Its namespace-level twin is in no sort that could supply it,
/// and is refused (requirement-channel.md §5.2, decided with the user). FAILS with the spec's
/// own sort not counted as supplying it (`dispatch_to_the_clause`): the law is refused too.
#[test]
fn a_law_in_its_specs_own_sort_is_its_clauses_condition() {
    let spec = "  import anthill.prelude.{Int64}\n  import anthill.prelude.PartialOrd.{gte}\n  \
                sort Spec\n    sort T = ?\n    operation w(a: T) -> Int64\n";
    crate::common::load_kb_with(&format!(
        "namespace test.rydnv.ownlaw\n{spec}    rule heavy(?a: T) :- gte(w(?a), 3)\n  end\nend\n"
    ));
    let errs = crate::common::load_errors_of(&format!(
        "namespace test.rydnv.nslaw\n{spec}  end\n  rule heavy(?a) :- gte(Spec.w(?a), 3)\nend\n"
    ));
    assert!(
        errs.len() == 1 && errs[0].contains("nothing provides `test.rydnv.nslaw.Spec`"),
        "the namespace-level twin is refused: {errs:?}"
    );
}

/// A CALL IN A PARENTHESIZED GOAL LIST is its clause's condition, as in the `&` the list is
/// (`goal_list_is_a_conjunction_test`): it answers 4 / -4 / -1. It was refused at load, the
/// list read as a tuple and the call in it as a value of two arguments given three. FAILS
/// with the list read as a tuple (`is_written_goal_list` answering `false`): the load refusal.
#[test]
fn a_call_in_a_goal_list_is_its_clauses_condition() {
    assert_eq!(
        cited_counts(
            "rydnv.goallist",
            "  rule r(?a, ?b, ?c) :- (Util.sign(?a, ?b, ?c), 1 = 1)",
            "r"
        ),
        [(1, Some(4)), (1, Some(-4)), (1, Some(-1))]
    );
}

/// A CALL IN A NEGAND, A QUANTIFIER'S BODY AND A DISCHARGE'S CONSEQUENT reads its condition
/// there: `not(Util.sign(?a, ?b, 4))` fails under `Descending` (4) and holds under `Ascending`
/// and uncited; `(forall ?z in [1]: Util.sign(?a, ?b, ?c))` and `(forall(?z), hyp(?z) -:
/// Util.sign(?a, ?b, ?c))`, with `?c` fixed at 4, hold under `Descending` alone — and so do
/// their twins over the spec operation `WeakOrd.compare`. They read `Int64`'s own -1 under every
/// citation: the negation held three times and the others never did. FAILS as the row above
/// does: `(1, 1, 1)`, `(0, 0, 0)` and `(0, 0, 0)`, for both calls.
#[test]
fn a_call_in_a_negand_a_quantifier_or_a_consequent_reads_its_condition_there() {
    for (tag, call) in [("s", "Util.sign"), ("d", "WeakOrd.compare")] {
        let negated = cited_counts(
            &format!("rydnv.{tag}negand"),
            &format!("  rule r(?a, ?b, ?c) :- not({call}(?a, ?b, 4)), ?c <=> 1"),
            "r",
        );
        assert_eq!(negated.map(|(n, _)| n), [0, 1, 1], "the negation of {call}");
        let quantified = cited_counts(
            &format!("rydnv.{tag}quantified"),
            &format!("  rule r(?a, ?b, ?c) :- ?c <=> 4, (forall ?z in [1]: {call}(?a, ?b, ?c))"),
            "r",
        );
        assert_eq!(quantified.map(|(n, _)| n), [1, 0, 0], "the quantifier over {call}");
        let discharged = cited_counts(
            &format!("rydnv.{tag}consequent"),
            &format!(
                "  rule hyp(?z) :- false
           rule r(?a, ?b, ?c) :- ?c <=> 4, (forall(?z), hyp(?z) -: {call}(?a, ?b, ?c))"
            ),
            "r",
        );
        assert_eq!(discharged.map(|(n, _)| n), [1, 0, 0], "the consequent {call}");
    }
}

/// What the rows on forms add to [`ORDERS`]: a value whose sort provides no `WeakOrd`,
/// operations to hand a `lambda` to, at `Int64` and at the type of their second argument, an
/// operation with an argument at no carrier, and an equation whose right-hand side is a form.
const FORM_DECLS: &str = "  import anthill.prelude.Option.{some, none}\n  \
                          entity box(v: Int64)\n  \
                          sort Apply\n    \
                          operation app(f: (u: Int64) -> Int64, v: Int64) -> Int64 = f(v)\n    \
                          operation appAt[X](f: (u: X) -> Int64, v: X) -> Int64 = f(v)\n    \
                          operation shift[A](x: A, n: Int64) -> Int64 requires WeakOrd[T = A] = \
                          Int64.add(WeakOrd.compare(x, x), n)\n  \
                          end\n  \
                          sort Tw\n    \
                          operation tw[A](a: A, b: A) -> Int64 requires WeakOrd[T = A]\n    \
                          rule tw(?a, ?b) <=> (let s = Util.sign(?a, ?b)\n      s) @[simp]\n  \
                          end\n";

/// A CALL UNDER A `let`, AN `if`, A `match` OR A `lambda`, ITS INSTANCE CARRIED BY A CLAUSE
/// VARIABLE, IS ITS CLAUSE'S CONDITION, as the same call written as a goal is: each spelling
/// answers `Descending`'s 4, `Ascending`'s -4 and `Int64`'s own -1, for an operation's own
/// `requires` (`Util.sign`) and for a spec operation (`WeakOrd.compare`). The read stands
/// before the goal that holds the form, and the form is run with its dictionary; the closure a
/// `lambda` builds carries it. So does a `@[simp]` equation whose right-hand side is the form,
/// rewritten into the clause. Each was refused at load ("nothing in the clause determines
/// which `anthill.prelude.WeakOrd` instance it means"). FAILS with the typer leaving a call to
/// the clause only outside a form (`clause_supplies_requirements` reading
/// `leaves_own_requirements_to_the_clause` alone): every form spelling is refused. The slot
/// spellings also FAIL with the evaluator running a slots-woven call as a deferred dispatch
/// (`start_apply_with_woven_slots` skipped): no answer under any citation. The goal spellings
/// pass either way, by design.
#[test]
fn a_call_under_a_form_is_its_clauses_condition() {
    for (ns, rule) in [
        ("rydnv.sgoal", "  rule r(?a, ?b, ?c) :- Util.sign(?a, ?b, ?c)"),
        ("rydnv.slet", "  rule r(?a, ?b, ?c) :- ?c <=> (let s = Util.sign(?a, ?b)\n    s)"),
        ("rydnv.sif", "  rule r(?a, ?b, ?c) :- ?c <=> (if true then Util.sign(?a, ?b) else 0)"),
        (
            "rydnv.scond",
            "  rule r(?a, ?b, ?c) :- ?c <=> (if Int64.lt(Util.sign(?a, ?b), 0) then -4 else 4)",
        ),
        (
            "rydnv.smatch",
            "  rule r(?a, ?b, ?c) :- ?c <=> (match true\n    case true -> Util.sign(?a, ?b)\n    case false -> 0)",
        ),
        (
            "rydnv.slambda",
            "  rule r(?a, ?b, ?c) :- ?c <=> Apply.app(lambda (u: Int64) -> Util.sign(?a, ?b), 0)",
        ),
        ("rydnv.ssimp", "  rule r(?a, ?b, ?c) :- ?c <=> Tw.tw(?a, ?b)"),
        ("rydnv.dgoal", "  rule r(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)"),
        ("rydnv.dlet", "  rule r(?a, ?b, ?c) :- ?c <=> (let s = WeakOrd.compare(?a, ?b)\n    s)"),
        (
            "rydnv.dif",
            "  rule r(?a, ?b, ?c) :- ?c <=> (if true then WeakOrd.compare(?a, ?b) else 0)",
        ),
        (
            "rydnv.dmatch",
            "  rule r(?a, ?b, ?c) :- ?c <=> (match true\n    case true -> WeakOrd.compare(?a, ?b)\n    case false -> 0)",
        ),
        (
            "rydnv.dlambda",
            "  rule r(?a, ?b, ?c) :- ?c <=> Apply.app(lambda (u: Int64) -> WeakOrd.compare(?a, ?b), 0)",
        ),
    ] {
        let want = if ns == "rydnv.scond" {
            // The condition reads the sign, and the branch says which way it went.
            [(1, Some(4)), (1, Some(-4)), (1, Some(-4))]
        } else {
            [(1, Some(4)), (1, Some(-4)), (1, Some(-1))]
        };
        assert_eq!(cited_counts(ns, &format!("{FORM_DECLS}{rule}"), "r"), want, "{ns}");
    }
}

/// A CALL IN A BRANCH THAT IS NOT TAKEN COSTS ITS CLAUSE NOTHING: at `box(v: 1)`, whose sort
/// provides no `WeakOrd`, the read before the goal binds the absence of a provider in place of
/// failing the clause, and only the branch that calls would read it. Untaken, the clause
/// answers the other branch's 1, definitely; taken, the call refuses the absence and the clause
/// has no answer, as a goal calling it at `box(v: 1)` has none; at `Int64` it answers `Int64`'s
/// own. For both classes, under an `if` and under a `match`, each queried uncited. FAILS with a
/// read under a form failing on a missing provider, as a goal's read does: every untaken row is
/// empty. The `Util.sign` rows also FAIL with the read of a slot under a form dropped from the
/// body the resolver runs (`is_routing_only_read` ignoring `in_form:`): uncited, the form waits
/// on a dictionary nothing binds; with the evaluator running a slots-woven call as a deferred
/// dispatch; and with the typer leaving a call to the clause only outside a form. The taken
/// rows pass either way, by design.
#[test]
fn a_call_in_a_branch_not_taken_costs_its_clause_nothing() {
    let src = program(
        "rydnv.untaken",
        &[ORDERS, FORM_DECLS],
        "  rule sIf(?f, ?a, ?b, ?e) :- ?e <=> (if ?f then Util.sign(?a, ?b) else 1)\n  \
         rule dMatch(?f, ?a, ?b, ?e) :- ?e <=> (match ?f\n    \
         case true -> WeakOrd.compare(?a, ?b)\n    \
         case false -> 1)\n  \
         rule sIfUntaken(?e) :- sIf(false, box(v: 1), box(v: 5), ?e)\n  \
         rule sIfTaken(?e) :- sIf(true, box(v: 1), box(v: 5), ?e)\n  \
         rule sIfInt(?e) :- sIf(true, 1, 5, ?e)\n  \
         rule dMatchUntaken(?e) :- dMatch(false, box(v: 1), box(v: 5), ?e)\n  \
         rule dMatchTaken(?e) :- dMatch(true, box(v: 1), box(v: 5), ?e)\n  \
         rule dMatchInt(?e) :- dMatch(true, 1, 5, ?e)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    for class in ["sIf", "dMatch"] {
        let rel = |case: &str| format!("rydnv.untaken.{class}{case}");
        assert_eq!(crate::common::one_definite_int(&mut kb, &rel("Untaken")), Some(1), "{class}: the other branch");
        let taken = crate::common::query_unary(&mut kb, &rel("Taken"));
        assert!(taken.is_empty(), "{class}: the call has no value at `box(v: 1)`: {taken:?}");
        assert_eq!(crate::common::one_definite_int(&mut kb, &rel("Int")), Some(-1), "{class}: `Int64`'s own");
    }
}

/// A CALL AN ARGUMENT OF WHICH NAMES A FORM'S OWN BINDER KEEPS ITS CLASS: the lambda's
/// parameter `u`, the `match` case's `x` and the `let`'s `s` are bound inside the form, where no
/// read before the goal sees them, and the read takes every argument as a witness — `u` in
/// `Apply.shift(?a, u)` too, where `?a` carries the instance. An operation's own `requires`
/// there is refused, as before; a spec operation on the lambda's parameter is dispatched by the
/// value, as before: `Int64`'s own -1 under every citation. FAILS with the binder test
/// (`names_a_binder`) answering no: the refused spellings load.
#[test]
fn a_call_naming_a_forms_own_binder_keeps_its_class() {
    for (what, rule) in [
        (
            "a lambda's parameter",
            "  rule r(?a, ?b, ?c) :- ?c <=> Apply.appAt(lambda (u) -> Util.sign(u, ?b), ?a)",
        ),
        (
            "a match case's binder",
            "  rule r(?a, ?b, ?c) :- ?c <=> (match some(?a)\n    case some(x) -> Util.sign(x, ?b)\n    case none -> 0)",
        ),
        ("a let's binder", "  rule r(?a, ?b, ?c) :- ?c <=> (let s = ?a\n    Util.sign(s, ?b))"),
        (
            "a lambda's parameter at no carrier",
            "  rule r(?a, ?c) :- ?c <=> Apply.app(lambda (u: Int64) -> Apply.shift(?a, u), 0)",
        ),
    ] {
        let src = program("rydnv.binder", &[ORDERS, FORM_DECLS], rule);
        let errs = crate::common::load_errors_of(&src);
        crate::common::assert_refused_naming(
            &errs,
            &["requirement `anthill.prelude.WeakOrd[T = ", "cannot be supplied for call to `rydnv.binder."],
            what,
        );
    }
    let by_value = cited_counts(
        "rydnv.binderspec",
        &format!(
            "{FORM_DECLS}  rule r(?a, ?b, ?c) :- ?c <=> Apply.appAt(lambda (u) -> WeakOrd.compare(u, ?b), ?a)"
        ),
        "r",
    );
    assert_eq!(by_value, [(1, Some(-1)), (1, Some(-1)), (1, Some(-1))], "by the value");
}
