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
//!     `a_clause_require_names_the_instance_at_its_carrier` (`3`, `Meters`', for `Feet`'s 4).
//!
//!   * an operation's own `requires` left to the clause however the call's types fix it
//!     (`own_requirements_fixed_at` answering no) — both rows of the pinned class here, and the
//!     load halves of `wi_gfs6a`'s four KCNA0 rows (each loads);
//!   * a requirement the call fixes refused with the rule-body account that says nothing fixes
//!     it — `wi_gfs6a`'s q2 and fwd rows (their refusal does not say no impl provides it).
//!
//!   * the witness of a written `require[…]` read off the body's goals alone
//!     (`calls_run_with_their_goal`) — `a_requires_witness_in_a_value_slot_grounds_it`;
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
//! carrier, and providers at two carriers.

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
        &["rydnv.unfixedrule.Conv.tag", "require[Conv[A = …]]"],
        "a rule body names the clause's `require` as the repair",
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

/// THE REPAIRS, each run: the clause's `require[…]`, with its `B` written and without; the
/// call's bracket; an operation's `requires`. Each names `Meters` and answers its 3, and a
/// `require` naming `Feet` answers `Feet`'s 4. Pass either way.
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
         rule full(?r) :- require[Conv[A = Meters, B = String]], Conv.tag(\"km\", ?r)\n  \
         rule part(?r) :- require[Conv[A = Meters]], Conv.tag(\"km\", ?r)\n  \
         rule feet(?r) :- require[Conv[A = Feet, B = String]], Conv.tag(\"km\", ?r)\n  \
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
            "declare `require[Conv[A = …, B = String]]` in the clause",
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

/// THE CLAUSE'S `require[…]` NAMES THE INSTANCE AT ITS CARRIER: over the same two providers,
/// `require[Conv[A = Feet, B = String]]` answers `Feet`'s 4. The typer read `A` off the first
/// provision at `String` and pinned `Meters`' member, so the clause answered 3 under a
/// `require` naming `Feet`. FAILS with the clause's `require` not read at the carrier: 3. The bracket in an operation body, `Conv[A = Feet].tag("km")`,
/// answers 4 either way.
#[test]
fn a_clause_require_names_the_instance_at_its_carrier() {
    let ns = "rydnv.declared";
    let src = program(
        ns,
        &[AT_B, FEET],
        "  sort U\n    operation br() -> Int64 = Conv[A = Feet].tag(\"km\")\n  end\n  \
         rule t(?r) :- require[Conv[A = Feet, B = String]], Conv.tag(\"km\", ?r)",
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
        &["rydnv.unfixedlet.Conv.tag", "require[Conv[A = …]]"],
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

/// A `require[…]`'S WITNESS MAY STAND IN A VALUE SLOT: `require[Conv[A = Meters, B = String]],
/// ?r <=> Conv.tag("km")` answers `Meters`' 3, as its goal spelling does. The witness scan
/// read the clause's top-level goals alone, so the clause was refused "no body call … to
/// ground the requirement". FAILS with that scan restored (`calls_run_with_their_goal` read
/// as the body's goals): refused.
#[test]
fn a_requires_witness_in_a_value_slot_grounds_it() {
    let ns = "rydnv.valuewitness";
    let src = program(
        ns,
        &[AT_A],
        "  rule t(?r) :- require[Conv[A = Meters, B = String]], ?r <=> Conv.tag(\"km\")",
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
/// bound in the branch alone (`?x`). It had no read, and answered `Int64`'s -1 under both
/// rivals. FAILS with the reads placed at the body's own goals alone (`nested_goals` pushing
/// nothing): `-1` under each citation, for every spelling but the goal one, which passes either
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
    ] {
        assert_eq!(
            cited_counts(ns, rule, "r"),
            [(1, Some(4)), (1, Some(-4)), (1, Some(-1))],
            "{ns}"
        );
    }
}

/// A CALL IN A NEGAND, A QUANTIFIER'S BODY AND A DISCHARGE'S CONSEQUENT reads its condition
/// there: `not(Util.sign(?a, ?b, 4))` fails under `Descending` (4) and holds under `Ascending`
/// and uncited; `(forall ?z in [1]: Util.sign(?a, ?b, ?c))` and `(forall(?z), hyp(?z) -:
/// Util.sign(?a, ?b, ?c))`, with `?c` fixed at 4, hold under `Descending` alone. They read
/// `Int64`'s own -1 under every citation: the negation held three times and the others never
/// did. FAILS as the row above does: `(1, 1, 1)`, `(0, 0, 0)` and `(0, 0, 0)`.
#[test]
fn a_call_in_a_negand_a_quantifier_or_a_consequent_reads_its_condition_there() {
    let negated = cited_counts(
        "rydnv.negand",
        "  rule r(?a, ?b, ?c) :- not(Util.sign(?a, ?b, 4)), ?c <=> 1",
        "r",
    );
    assert_eq!(negated.map(|(n, _)| n), [0, 1, 1], "the negation");
    let quantified = cited_counts(
        "rydnv.quantified",
        "  rule r(?a, ?b, ?c) :- ?c <=> 4, (forall ?z in [1]: Util.sign(?a, ?b, ?c))",
        "r",
    );
    assert_eq!(quantified.map(|(n, _)| n), [1, 0, 0], "the quantifier");
    let discharged = cited_counts(
        "rydnv.consequent",
        "  rule hyp(?z) :- false
           rule r(?a, ?b, ?c) :- ?c <=> 4, (forall(?z), hyp(?z) -: Util.sign(?a, ?b, ?c))",
        "r",
    );
    assert_eq!(discharged.map(|(n, _)| n), [1, 0, 0], "the consequent");
}
