//! WI-20261020-NNQ1S / WI-20260930-FB53M — A CARRIER'S MEMBER SUPPLIES A SPEC OPERATION THAT HAS
//! AN IMPLEMENTATION OF ITS OWN ONLY WHERE IT FITS IT (decided with the user 2026-11-21, reading
//! (A) of FB53M; kernel-language.md *A member that does not fit is no supplier*).
//!
//! MEASURED FIRST on 7d609b66 with the debug CLI. A member beside a default body or a builtin is
//! not compared with the spec operation where it is declared (`check_member_signature`'s gate:
//! it is another operation of the same name), and dispatch took it by its short name all the same
//! (`carrier_own_op`):
//!
//! * `P.neq(a: Int64, b: Int64) = true`, no provision: `neq(p(x: 1), p(x: 1))` answered `true`,
//!   where the derived `neq` answers `false`; a written `provides PartialEq[T = P]` changed
//!   nothing; a one-parameter `Q.neq` died at the call, "expected 1 args, got 2".
//! * `Car.peek(s: Car)` beside `Sp.peek(s: Sp, k: Int64) = 0`: `Sp.peek(car(v: 1), 5)` died the
//!   same way; a member returning `String` died adding to it; a member taking `k: String` was
//!   handed the `Int64` and answered 9.
//!
//! Now `record_members_that_supply_nothing` (typing/signature.rs) decides at load, for every
//! carrier member whose short name a spec operation with an implementation of its own shares,
//! whether it fits — the provision's comparison, at each provision that dispatches to the
//! carrier or at the carrier itself — and `carrier_own_op`, which every reader of a carrier's own
//! member goes through, passes over one that does not. One row per reader below.
//!
//! THE GAP IT OPENED, CLOSED BESIDE IT: typed by the spec's own signature, a call over a receiver
//! whose effect row is the caller's own row parameter (`a: Car[V = Int64, EC = R]`) read the
//! spec's `s.E` as nothing, "type 'Car' has no member 'E'" — on main too, with no member at all.
//! The non-fitting override had been typing those calls in the spec's place (WI-606's fallback).
//! A provision's effect-row binding resting on a rigid now lends itself where no override is read
//! instead (`RowReading::RigidsFixed`).
//!
//! ONE MEMBER IS REFUSED INSTEAD: an `eq` that does not fit `PartialEq.eq` beside the carrier's
//! provision holds the name its derived `eq` is declared under, so the provision would have none
//! ([`an_eq_that_does_not_fit_is_refused`]).
//!
//! MEASURED 2026-11-21, a run-time switch each, over all of `anthill-core` (11 364 tests, one
//! optimized build): control 0 fail.
//!
//! 1. THE FILTER (`carrier_own_op`, and `resolve_op_target_at`'s inherited row) off — 14 FAIL:
//!    this file's three over a member that does not fit, and the eleven rows of
//!    `wi_0rp29_nested_projection_value_in_type_test` and `wi_jpsdh_call_site_bracket_test` that
//!    record the spec's call beside such a member.
//! 2. A WITNESS'S PROVISION NOT COMPARED AT (only the carrier's own) — 1 FAILS:
//!    `wi_y6zcd_call_at_several_carriers_test::a_carriers_own_member_answers_only_at_its_signatures_carriers`,
//!    whose `Leaf2.conv` answers through `W3`'s provision alone.
//! 3. THE RIGID ROW READ AS `Ground` — 15 FAIL: [`a_spec_projection_reads_a_row_resting_on_the_callers_row`]
//!    and fourteen rows of the two files above, whose spec calls the reading types.
//! 4. THE `eq` REFUSAL off — 1 FAILS: [`an_eq_that_does_not_fit_is_refused`].
//!
//! A CARRIER THAT HAS NO PROVISION is compared at itself. Read as supplying nothing there, 6 rows
//! fail (the eq-dispatch index takes a sort's own `eq` with no provision); read as fitting
//! without the comparison, none does — no program in the suite has a carrier with no provision
//! beside a member that does not fit and loads (proposal 059 R4 refuses most).
//!
//! PASS EITHER WAY, BY DESIGN: [`a_spec_projection_over_an_open_row_lends_nothing`].

use crate::common::{
    assert_refused_naming, load_errors_of as load_errors, load_kb_with, one_definite_int,
    query_pattern_term, run_int64,
};
use anthill_core::kb::resolve::ResolveConfig;

/// NNQ1S's carriers: `P` with a `neq` over two `Int64`s, `Q` with a one-parameter one, and — with
/// `written` — `P`'s `provides PartialEq` written out.
fn neq_program(ns: &str, written: bool) -> String {
    let provision = if written { "provides PartialEq[T = Self]" } else { "" };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort P
    entity p(x: Int64)
    {provision}
    operation neq(a: Int64, b: Int64) -> Bool = true
  end
  sort Q
    entity q(x: Int64)
    operation neq(n: Int64) -> Bool = true
  end
  operation b(t: Bool) -> Int64 = if t then 1 else 0
  operation same() -> Int64 = b(neq(p(x: 1), p(x: 1)))
  operation apart() -> Int64 = b(neq(p(x: 1), p(x: 2)))
  operation one() -> Int64 = b(neq(q(x: 1), q(x: 1)))
  operation own() -> Int64 = b(P.neq(3, 4))
  operation ownq() -> Int64 = b(Q.neq(3))
  rule same_r(?v) :- ?v <=> b(neq(p(x: 1), p(x: 1)))
end
"#
    )
}

/// THE TICKET'S PROGRAM: `neq` of two `P`s is the derived `neq` — `false` for equal values, `true`
/// for distinct ones — written provision or not, in an operation body (the typer's static
/// dispatch and the interpreter's) and in a rule body; the one-parameter `Q.neq` is passed over
/// rather than called with two arguments. The CONTROL: `P.neq(3, 4)` and `Q.neq(3)` name the
/// members and still run them. RED with the member-fit rule backed out: `same` answers 1, `one`
/// dies at the call, the rule body answers 1.
#[test]
fn neq_of_a_carrier_is_the_derived_one_beside_a_member_that_does_not_fit() {
    for written in [false, true] {
        let ns = if written { "winnq1s.neq_written" } else { "winnq1s.neq" };
        let src = neq_program(ns, written);
        for (op, want) in [("same", 0), ("apart", 1), ("one", 0), ("own", 1), ("ownq", 1)] {
            assert_eq!(
                run_int64(&src, &format!("{ns}.{op}")),
                Ok(want),
                "{op}, provision written: {written}"
            );
        }
        let mut kb = load_kb_with(&src);
        assert_eq!(
            one_definite_int(&mut kb, &format!("{ns}.same_r")),
            Some(0),
            "the rule body, provision written: {written}"
        );
    }
}

/// FB53M's carriers beside `Sp.peek(s: Sp, k: Int64) -> Int64 = 0`: `Car` taking one parameter,
/// `Car2` returning a `String`, `Car3` taking `k: String` — none fits — and `Car4`, which fits
/// and answers 44. Each provides `Sp`.
const FB53M_CARRIERS: &str = r#"
  sort Sp
    sort T = ?
    operation peek(s: Sp, k: Int64) -> Int64 = 0
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = Car]
    operation peek(s: Car) -> Int64 = 7
  end
  sort Car2
    sort V = ?
    entity car2(v: V)
    provides Sp[T = Car2]
    operation peek(s: Car2, k: Int64) -> String = "s"
  end
  sort Car3
    sort V = ?
    entity car3(v: V)
    provides Sp[T = Car3]
    operation peek(s: Car3, k: String) -> Int64 = 9
  end
  sort Car4
    sort V = ?
    entity car4(v: V)
    provides Sp[T = Car4]
    operation peek(s: Car4, k: Int64) -> Int64 = 44
  end
"#;

fn fb53m_program(ns: &str, rest: &str) -> String {
    format!(
        "\nnamespace {ns}\n  import anthill.prelude.{{Int64, String}}\n{FB53M_CARRIERS}{rest}end\n"
    )
}

/// FB53M'S THREE PROGRAMS RUN THE DEFAULT, and a member that fits still overrides it: in an
/// operation body, in a rule body, and through the dictionary of a value typed at the spec
/// (`via(x: Sp)`, proposal 073 §2 — `resolve_op_target`), the call naming the member running it. RED with the member-fit rule backed out: the first three
/// die at the call or answer the member's 9.
#[test]
fn a_spec_call_beside_a_member_that_does_not_fit_runs_the_default() {
    let ns = "winnq1s.fb";
    let src = fb53m_program(
        ns,
        "  operation f1() -> Int64 = Sp.peek(car(v: 1), 5)
  operation f2() -> Int64 = Sp.peek(car2(v: 1), 5) + 1
  operation f3() -> Int64 = Sp.peek(car3(v: 1), 5)
  operation f4() -> Int64 = Sp.peek(car4(v: 1), 5)
  operation own() -> Int64 = Car.peek(car(v: 1))
  operation via(x: Sp) -> Int64 = Sp.peek(x, 5)
  operation d1() -> Int64 = via(car(v: 1))
  operation d4() -> Int64 = via(car4(v: 1))
  rule r1(?v) :- ?v <=> Sp.peek(car(v: 1), 5)
  rule r4(?v) :- ?v <=> Sp.peek(car4(v: 1), 5)
",
    );
    for (op, want) in [("f1", 0), ("f2", 1), ("f3", 0), ("f4", 44), ("own", 7), ("d1", 0), ("d4", 44)] {
        assert_eq!(run_int64(&src, &format!("{ns}.{op}")), Ok(want), "{op}");
    }
    let mut kb = load_kb_with(&src);
    assert_eq!(one_definite_int(&mut kb, &format!("{ns}.r1")), Some(0), "the rule body");
    assert_eq!(one_definite_int(&mut kb, &format!("{ns}.r4")), Some(44), "CONTROL: the rule body");
}

/// … AND A QUERY: `Sp.peek(car(v: 1), 5, 0)` holds — the default's answer — and the fitting
/// member's 44 is what a query of `Car4` holds. RED with the member-fit rule backed out: the first
/// query has no answer (the call dies).
#[test]
fn a_query_of_a_spec_call_beside_a_member_that_does_not_fit_runs_the_default() {
    let ns = "winnq1s.fbq";
    let mut kb = load_kb_with(&fb53m_program(ns, ""));
    let mut holds = |pattern: &str| {
        let goal = query_pattern_term(&mut kb, pattern);
        let sols = kb.resolve(&[goal], &ResolveConfig::default());
        sols.iter().filter(|s| s.is_definite()).count()
    };
    assert_eq!(holds(&format!("{ns}.Sp.peek({ns}.Car.car(v: 1), 5, 0)")), 1, "the default's 0");
    assert_eq!(holds(&format!("{ns}.Sp.peek({ns}.Car.car(v: 1), 5, 7)")), 0, "not the member's 7");
    assert_eq!(
        holds(&format!("{ns}.Sp.peek({ns}.Car4.car4(v: 1), 5, 44)")),
        1,
        "CONTROL: the member that fits"
    );
}

/// THE BUILTIN `eq` IS THE ONE MEMBER REFUSED FOR NOT FITTING: `P2.eq(a: Int64, b: Int64)` beside
/// `provides PartialEq` supplies nothing, as every member that does not fit beside the spec's
/// implementation — and it holds the name the carrier's derived `eq` is declared under, so the
/// provision would have no member. It LOADED, and `eq(p2(x: 1), p2(x: 1))` died at the call,
/// "EqualityWithNoMember"; before the member-fit rule, the member was handed two `P2`s and
/// answered `false`. Now refused at load, in the comparison's words. The CONTROL: `P3.eq(a: P3,
/// b: P3) = false` fits, and decides — identical operands included, `P3` providing `PartialEq`
/// and no `Eq` (WI-20261025-TSYS6). Each writes its provision: a member named `eq` on a sort that
/// provides no `PartialEq` captures the name (proposal 059 R4). RED with the refusal backed out:
/// `P2` loads.
#[test]
fn an_eq_that_does_not_fit_is_refused() {
    let program = |ns: &str, member: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq}}
  sort P
    entity p(x: Int64)
    provides PartialEq[T = Self]
    {member}
  end
  operation b(t: Bool) -> Int64 = if t then 1 else 0
  operation e() -> Int64 = b(eq(p(x: 1), p(x: 1)))
end
"#
        )
    };
    assert_refused_naming(
        &load_errors(&program(
            "winnq1s.eq2",
            "operation eq(a: Int64, b: Int64) -> Bool = false",
        )),
        &[
            "'winnq1s.eq2.P' provides 'anthill.prelude.PartialEq' but its own member 'eq' does not \
             fit 'anthill.prelude.PartialEq.eq'",
            "parameter 1 is `Int64` where the spec's is `P`",
        ],
        "an `eq` over two `Int64`s",
    );
    let ns = "winnq1s.eq3";
    assert_eq!(
        run_int64(&program(ns, "operation eq(a: P, b: P) -> Bool = false"), &format!("{ns}.e")),
        Ok(0),
        "CONTROL: the fitting `eq` decides"
    );
}

/// THE GAP: a spec call typed by the spec's own signature, over a receiver whose row is the
/// caller's row parameter, reads the spec's `s.E` through the provision as `{R}`. It was refused
/// "type 'Car' has no member 'E'" — on main as well, with no member at all — where the same call
/// at `EC = {}` ran. The CONTROL is that call, which ran either way. RED with the rigid reading
/// backed out (`RowReading::RigidsFixed` read as `Ground`): refused.
#[test]
fn a_spec_projection_reads_a_row_resting_on_the_callers_row() {
    let ns = "winnq1s.rigid";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Sp
    sort T = ?
    effects E = ?
    operation get(x: T, s: Self) -> Int64 effects s.E = 3
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Self, E = {{EC}}]
  end
  operation use[R](a: Car[V = Int64, EC = R]) -> Int64 effects {{R}} = Sp.get(a, a)
  operation usec(a: Car[V = Int64, EC = {{}}]) -> Int64 = Sp.get(a, a)
  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 1)
    use(a) + usec(a)
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(6));
}

/// … AND IN A PARAMETER'S TYPE: `f: (n: Int64) -> Int64 @ {s.E}` over `a: Car[V = Int64, EC =
/// R]` reads the callback's row as `{R}`, where it was refused "type 'Car' has no member 'E'" —
/// a parameter is read off the spec's own signature whatever the call runs, so no override ever
/// read it instead. Found by `/code-review` beside the return's reading. RED with the parameter
/// site's reading backed out (MEASURED).
#[test]
fn a_spec_parameter_reads_a_row_resting_on_the_callers_row() {
    let ns = "winnq1s.param";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Sp
    sort T = ?
    effects E = ?
    operation each(x: T, s: Self, f: (n: Int64) -> Int64 @ {{s.E}}) -> Int64 effects s.E = f(1)
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Self, E = {{EC}}]
  end
  operation use[R](a: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    Sp.each(a, a, lambda (n: Int64) -> n + 1)
  operation usec(a: Car[V = Int64, EC = {{}}]) -> Int64 = Sp.each(a, a, lambda (n: Int64) -> n + 1)
  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 1)
    use(a) + usec(a)
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(4));
}

/// … AND A ROW RESTING ON A VARIABLE NOTHING FIXED STILL LENDS NOTHING (WI-396): over a bare
/// `Car`, whose `EC` the argument leaves open, the spec's `s.E` is no row, and the call is
/// refused naming it. Passes either way by design: the rigid reading is not a pure default.
#[test]
fn a_spec_projection_over_an_open_row_lends_nothing() {
    let ns = "winnq1s.open";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Sp
    sort T = ?
    effects E = ?
    operation get(x: T, s: Self) -> Int64 effects s.E = 3
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Self, E = {{EC}}]
  end
  operation use(a: Car[V = Int64, EC = ?]) -> Int64 = Sp.get(a, a)
end
"#
    );
    let errs = load_errors(&src);
    assert!(!errs.is_empty(), "an open row is not read as pure: {errs:#?}");
}
