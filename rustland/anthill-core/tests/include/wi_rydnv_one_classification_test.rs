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
        "namespace {ns}\n  import anthill.prelude.{{Int64, String}}\n{}{body}\nend\n",
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
