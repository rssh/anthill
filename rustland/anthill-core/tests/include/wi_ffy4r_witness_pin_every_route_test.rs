//! WI-20261003-FFY4R — A CALL'S WITNESS PIN (`Spec.op[Spec = W](…)`) IS READ BY EVERY ROUTE THE
//! CALL IS DISPATCHED THROUGH, a defaulted spec operation's as a body-less one's.
//!
//! Over `sort Holder { sort C = ?; operation size(c: C) -> Int64; operation size2(c: C) -> Int64
//! = size(c) }`, `sort Box { sort V = ?; entity box(v: V) }` and two witnesses, `OptIntBoxH` at
//! `Box[V = Option[T = Int64]]` answering 42 and `OptStrBoxH` at `[… = String]` answering 7:
//!
//! (a) `Holder.size2[Holder = OptIntBoxH](box(v: none))`, the DEFAULTED operation, was refused at
//!     load, "unknown type-param 'Holder'": the bracket of a spec's default named only a
//!     requirement of the enclosing declaration (WI-20261013-50ZMN), so no pin could say where
//!     the default body's own calls dispatch. It is the default body run at the named witness's
//!     instance now, which its `size(c)` reads (proposal 073 §3): 42, and 7 at `OptStrBoxH`.
//! (b) `Holder.size[Holder = OptIntBoxH](box(v: none))`, the body-less one, ran to 42 since
//!     WI-20260929-0RP29's tenth pass, by a re-dispatch at the witness in ONE place
//!     (`narrowed_to_named_witness`, after its own dispatch answered `NoCandidates`). That is gone:
//!     the resolution itself reads the pin where the receiver matches no provision as it stands
//!     (`goal_at_named_witness`, at step 0 of `resolve_inner`), and a pinned goal is never
//!     `NoCandidates` (`resolve_at_goal`), so a pin no instance answers is refused at load —
//!     `Holder.size[Holder = IntH](box(v: none))`, over a witness at `Int64`, LOADED and left a
//!     residual goal at run time before (MEASURED on a5384da6 with the debug CLI).
//!
//! And a defaulted call that names its witness is answered by that witness's instance alone: the
//! suppliers found by the carrier — its own member, another witness's — and the provision at the
//! carrier are not asked (`names_its_witness` in `check_apply_iter`'s defaulted tree).
//! `Mk.viaRecv[Mk = W2](a(n: 9))` beside `A`'s own `viaRecv` answered `A`'s 7 with that step
//! backed out, the bracket read by nothing.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: a call runs to its value, a refusal is asserted by its words.
//! The bracket in a row's comment is the verdict on a5384da6.
//!
//! Found beside it and fixed here: where nothing else says the spec's carrier (a `match`
//! scrutinee), the witness's provision says it — the body-less `Mk.e[Mk = W2]()` was refused
//! "ambiguous dispatch … write `[Mk = W2]`" with that bracket written; a defaulted operation's
//! tie between two witnesses offers the bracket that now selects one; a witness's name,
//! `W2.viaDefault()`, is `Mk.viaDefault[Mk = W2]()` in an operation body (WI-20261102-YCZ0J's
//! refused row, turned into its answer as that ticket asked) and is refused, naming the bracket,
//! in a rule body, which reads none.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! EIGHT PARTS, each backed out alone by a temporary switch, over the whole `wi_tests` binary
//! (9673 rows, green with nothing backed out; optimized build; measured 2026-11-20). The part
//! [`a_witness_name_in_a_rule_body_is_refused_where_no_bracket_is_read`] holds — the name
//! refused outside an operation body — was measured with the debug CLI (its row says what).
//!
//! 1. THE GOAL READ AT THE NAMED WITNESS (`goal_at_named_witness` at step 0 of `resolve_inner`).
//!    6 FAIL: [`a_witness_pin_on_a_defaulted_operation_runs_its_body_at_the_witness`],
//!    [`a_witness_pin_on_a_body_less_operation_reaches_the_witness`],
//!    `wi_0rp29_review9_regressions_test::a_bracket_naming_a_witness_dispatches_to_it_over_an_undecided_slot`,
//!    `wi_sgxyh_unfixed_slot_test::a_selected_witness_answers_an_unfixed_slot` and two rows of
//!    `wi_f3fyj_value_in_type_binding_test` (a bracket selecting a provider at its value).
//! 2. A PINNED GOAL IS NEVER `NoCandidates` (`resolve_at_goal`). 11 FAIL — the six of part 1,
//!    this file's covers-no-receiver row, the 0RP29 control,
//!    `wi_50zmn`'s, `wi_c6gk8`'s and `wi_p0qgf`'s named-witness refusals — nine of them by the
//!    body-less route's assertion that no pinned goal reaches its `NoCandidates` arm, two by the
//!    defaulted route's `unreachable!`: the invariant is what holds the part in place.
//! 3. THE DEFAULTED OPERATION'S BRACKET TAKES A WITNESS (`seed_bracket_bindings`). 11 FAIL: every
//!    row of this file on a defaulted operation, the 50ZMN witness row and
//!    `wi_ycz0j_carrier_names_inherited_member_test::a_default_through_a_witness_runs_at_the_witness_instance`.
//! 4. THE DEFAULTED CALL'S ROUTE FOR A NAMED WITNESS (`check_apply_call`, ahead of the abstract
//!    receiver and the carrier). 7 FAIL: [`a_pin_on_a_defaulted_operation_outranks_the_carriers_own_member`],
//!    [`a_pin_on_a_dot_names_the_same_instance`], [`a_pin_says_the_carrier_nothing_else_says`],
//!    [`the_default_body_reads_the_pinned_instance`], [`a_defaulted_tie_offers_the_bracket_that_selects_a_witness`],
//!    the 50ZMN witness row (refused as missing the requirement its sort declares) and the YCZ0J
//!    row. Row (a) itself passes without it, through the instance route at the carrier.
//! 5. THE CARRIER THE WITNESS SAYS (`bind_carrier_the_witness_says`). 2 FAIL:
//!    [`a_pin_says_the_carrier_nothing_else_says`] and the YCZ0J row (`Mk.viaDefault[Mk = W2]()`
//!    under a `match`).
//! 6. A WITNESS'S NAME LOWERED TO THE BRACKET (`type_receiver.rs`). 1 FAILS: the YCZ0J row.
//! 7. THE TIE'S REPAIR ON A DEFAULTED OPERATION (`supplier_tie_repair`). 1 FAILS:
//!    [`a_defaulted_tie_offers_the_bracket_that_selects_a_witness`].
//! 8. THE NARROWED GOAL'S CARRIER CLEARED — measured inert (0 fail) once part 4 kept a named
//!    witness off the route that asks at the receiver's carrier, and REMOVED.
//!
//! PASS UNDER EVERY PART, by design: [`no_pin_over_two_covering_witnesses_is_refused_at_load`],
//! [`a_defaulted_call_at_a_known_type_takes_its_instance`] — the controls.

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, query_unary, run_int64};

const HOLDER: &str = "
  sort Holder
    sort C = ?
    operation size(c: C) -> Int64
    operation size2(c: C) -> Int64 = size(c)
  end

  sort Box
    sort V = ?
    entity box(v: V)
  end

  sort OptIntBoxH
    provides Holder[C = Box[V = Option[T = Int64]]]
    operation size(c: Box[V = Option[T = Int64]]) -> Int64 = 42
  end

  sort OptStrBoxH
    provides Holder[C = Box[V = Option[T = String]]]
    operation size(c: Box[V = Option[T = String]]) -> Int64 = 7
  end
";

/// A witness at a carrier `box(v: none)` is not.
const INT_H: &str = "
  sort IntH
    provides Holder[C = Int64]
    operation size(c: Int64) -> Int64 = 1
  end
";

/// A program whose `go()` is `body`, beside `HOLDER` and `decls`.
fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String, Option}}\n  import anthill.prelude.Option.{{some, none}}\n{HOLDER}\n{decls}\n  operation go() -> Int64 = {body}\nend\n"
    )
}

fn runs(ns: &str, decls: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, body), &format!("{ns}.go"))
}

fn errors(ns: &str, decls: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(ns, decls, body))
}

// ── The ticket's rows ───────────────────────────────────────────────────────

/// [refused, unknown type-param 'Holder'] (a): the defaulted operation's bracket names the
/// instance its body runs at, and the body's `size(c)` is that witness's.
#[test]
fn a_witness_pin_on_a_defaulted_operation_runs_its_body_at_the_witness() {
    let body = "Holder.size2[Holder = OptIntBoxH](box(v: none))";
    assert_eq!(runs("t.ffy4r.a1", "", body), Ok(42));
    let body = "Holder.size2[Holder = OptStrBoxH](box(v: none))";
    assert_eq!(runs("t.ffy4r.a2", "", body), Ok(7));
}

/// [42, 7] (b): the body-less operation's pin, read by the resolution now rather than by a
/// re-dispatch of its route.
#[test]
fn a_witness_pin_on_a_body_less_operation_reaches_the_witness() {
    let body = "Holder.size[Holder = OptIntBoxH](box(v: none))";
    assert_eq!(runs("t.ffy4r.b1", "", body), Ok(42));
    let body = "Holder.size[Holder = OptStrBoxH](box(v: none))";
    assert_eq!(runs("t.ffy4r.b2", "", body), Ok(7));
}

/// [the body-less call LOADED, a residual goal at run time; the defaulted one refused, unknown
/// type-param] A pin naming a witness that covers no receiver of the call is refused at load,
/// naming the witness.
#[test]
fn a_pin_naming_a_witness_that_covers_no_receiver_is_refused_at_load() {
    for (ns, op) in [("t.ffy4r.n1", "size"), ("t.ffy4r.n2", "size2")] {
        let body = format!("Holder.{op}[Holder = IntH](box(v: none))");
        assert_refused_naming(
            &errors(ns, INT_H, &body),
            &[
                &format!("{ns}.Holder.{op}.dispatch"),
                &format!("the call selected `{ns}.IntH` for {ns}.Holder, which provides no instance at these bindings"),
            ],
            "a witness at `Int64` is no instance at a `Box`",
        );
    }
}

/// [the body-less call refused by its selection check; the defaulted one, unknown type-param] A
/// witness providing the spec at other bindings than the receiver's is refused at load.
#[test]
fn a_pin_naming_a_witness_at_other_bindings_is_refused_at_load() {
    assert_refused_naming(
        &errors("t.ffy4r.o1", "", "Holder.size[Holder = OptStrBoxH](box(v: some(1)))"),
        &["but not at the bindings this call to t.ffy4r.o1.Holder.size needs"],
        "`OptStrBoxH` is at `String`, the receiver at `Int64`",
    );
    assert_refused_naming(
        &errors("t.ffy4r.o2", "", "Holder.size2[Holder = OptStrBoxH](box(v: some(1)))"),
        &["the call selected `t.ffy4r.o2.OptStrBoxH` for t.ffy4r.o2.Holder, which provides no instance at these bindings"],
        "`OptStrBoxH` is at `String`, the receiver at `Int64`",
    );
}

/// [refused, unknown type-param 'Holder'] A bracket on a defaulted operation that names no
/// provider of its spec is refused as one on a body-less operation is.
#[test]
fn a_pin_naming_no_provider_on_a_defaulted_operation_is_refused() {
    assert_refused_naming(
        &errors("t.ffy4r.np", "", "Holder.size2[Holder = Box](box(v: none))"),
        &["t.ffy4r.np.Box does not provide t.ffy4r.np.Holder"],
        "`Box` provides nothing",
    );
}

/// CONTROL, passes on the tree before: with no pin, two witnesses covering `box(v: none)` leave
/// the call undecided, and it is refused at load on both operations.
#[test]
fn no_pin_over_two_covering_witnesses_is_refused_at_load() {
    for (ns, op) in [("t.ffy4r.u1", "size"), ("t.ffy4r.u2", "size2")] {
        assert_refused_naming(
            &errors(ns, "", &format!("Holder.{op}(box(v: none))")),
            &[&format!("nothing here fixes `T` of `Option`, and `{ns}.OptIntBoxH` and `{ns}.OptStrBoxH` provide `{ns}.Holder` only at an instance of it")],
            "no pin, two witnesses",
        );
    }
}

/// CONTROL, passes on the tree before (WI-20261105-P0QGF's row): at a type the arguments fix, the
/// defaulted call takes the one instance there, unpinned.
#[test]
fn a_defaulted_call_at_a_known_type_takes_its_instance() {
    assert_eq!(runs("t.ffy4r.k1", "", "Holder.size2(box(v: some(1)))"), Ok(42));
    assert_eq!(runs("t.ffy4r.k2", "", "Holder.size2(box(v: some(\"x\")))"), Ok(7));
}

// ── A pin beside what the carrier finds ─────────────────────────────────────

/// `A` provides `Mk` at itself and `W2` is a witness at `A`; `a_decls` and `w_decls` go in their
/// bodies, and `go() -> ret` is `body`, beside `n() -> Int64`, the `n` of the `A` `go()` gives
/// where `ret` is `A`.
fn mk_program(ns: &str, a_decls: &str, w_decls: &str, ret: &str, body: &str) -> String {
    format!(
        "namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Mk
    sort C = ?
    operation e() -> C
    operation viaDefault() -> C = e()
    operation viaRecv(c: C) -> Int64 = 5
  end
  sort A
    entity a(n: Int64)
    provides Mk[C = A]
    operation e() -> A = a(n: 1)
{a_decls}
  end
  sort W2
    provides Mk[C = A]
    operation e() -> A = a(n: 3)
{w_decls}
  end
  operation go() -> {ret} = {body}
{n}
end
",
        n = if ret == "A" {
            "  operation n() -> Int64 =\n    match go()\n      case a(n) -> n"
        } else {
            ""
        },
    )
}

fn mk_runs(ns: &str, a_decls: &str, w_decls: &str, body: &str) -> Result<i64, String> {
    run_int64(&mk_program(ns, a_decls, w_decls, "Int64", body), &format!("{ns}.go"))
}

const A_OWN: &str = "    operation viaRecv(c: A) -> Int64 = 7";
const W2_OWN: &str = "    operation viaRecv(c: A) -> Int64 = 8";

/// [refused, unknown type-param 'Mk'] A defaulted call that names its witness runs that witness's
/// instance — its member where it writes one, the default where it does not — and not the member
/// the carrier `A` writes, which the unpinned call runs.
#[test]
fn a_pin_on_a_defaulted_operation_outranks_the_carriers_own_member() {
    let pinned = "Mk.viaRecv[Mk = W2](a(n: 9))";
    assert_eq!(mk_runs("t.ffy4r.m1", A_OWN, "", pinned), Ok(5));
    assert_eq!(mk_runs("t.ffy4r.m2", A_OWN, W2_OWN, pinned), Ok(8));
    assert_eq!(mk_runs("t.ffy4r.m3", "", "", pinned), Ok(5));
    // Controls: unpinned, the carrier's own member, and the default where it writes none.
    assert_eq!(mk_runs("t.ffy4r.m4", A_OWN, "", "Mk.viaRecv(a(n: 9))"), Ok(7));
    assert_eq!(mk_runs("t.ffy4r.m5", "", "", "Mk.viaRecv(a(n: 9))"), Ok(5));
}

/// [refused, unknown type-param 'Mk'] The default body's own calls read the pinned instance: `e()`
/// in `viaDefault` is `W2`'s, where the unpinned call reads `A`'s.
#[test]
fn the_default_body_reads_the_pinned_instance() {
    // `go() -> A` binds `C`.
    let n_of = |ns: &str, call: &str| {
        run_int64(&mk_program(ns, "", "", "A", call), &format!("{ns}.n"))
    };
    assert_eq!(n_of("t.ffy4r.d1", "Mk.viaDefault[Mk = W2]()"), Ok(3));
    assert_eq!(n_of("t.ffy4r.d2", "Mk.viaDefault()"), Ok(1));
}

/// [the defaulted call refused, unknown type-param 'Mk'; the body-less one refused "ambiguous
/// dispatch … the call selects none — write `[Mk = W2]`", with that bracket written] Where
/// nothing else says the spec's carrier — a `match` scrutinee, no argument, no expected type —
/// the witness's provision says it (`bind_carrier_the_witness_says`), on both operations. With
/// the bracket accepted and the carrier left open, the defaulted call loaded and died at run time
/// "operation has no body" (MEASURED).
#[test]
fn a_pin_says_the_carrier_nothing_else_says() {
    let n_of = |ns: &str, call: &str| {
        let body = format!("\n    match {call}\n      case a(n) -> n");
        run_int64(&mk_program(ns, "", "", "Int64", &body), &format!("{ns}.go"))
    };
    assert_eq!(n_of("t.ffy4r.c1", "Mk.e[Mk = W2]()"), Ok(3));
    assert_eq!(n_of("t.ffy4r.c2", "Mk.viaDefault[Mk = W2]()"), Ok(3));
}

/// [both refused, unknown type-param 'Mk'] The dot spelling is the applicative call (§8.7, *A dot
/// call carries the bracket of the call it resolves to*), and names the same instance.
#[test]
fn a_pin_on_a_dot_names_the_same_instance() {
    let pinned = "a(n: 9).viaRecv[Mk = W2]()";
    assert_eq!(mk_runs("t.ffy4r.dt1", A_OWN, "", pinned), Ok(5));
    assert_eq!(mk_runs("t.ffy4r.dt2", "", W2_OWN, pinned), Ok(8));
    assert_eq!(mk_runs("t.ffy4r.dt3", A_OWN, "", "a(n: 9).viaRecv()"), Ok(7));
}

/// Two witnesses at one carrier, each writing the defaulted member, and no default.
fn tied(ns: &str, body: &str) -> String {
    format!(
        "namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Holder
    sort C = ?
    operation size(c: C) -> Int64
    operation size2(c: C) -> Int64 = size(c)
  end
  sort Box
    entity box(n: Int64)
  end
  sort W1
    provides Holder[C = Box]
    operation size(c: Box) -> Int64 = 1
    operation size2(c: Box) -> Int64 = 11
  end
  sort W2
    provides Holder[C = Box]
    operation size(c: Box) -> Int64 = 2
    operation size2(c: Box) -> Int64 = 22
  end
  operation go() -> Int64 = {body}
end
"
    )
}

/// [the tie's repair said "No bracket names any of them … here there is no such slot"; the
/// pinned call refused, unknown type-param 'Holder'] A defaulted operation's tie between two
/// witnesses is still refused unselected, and its repair offers the bracket that now selects
/// one, as the body-less operation's does.
#[test]
fn a_defaulted_tie_offers_the_bracket_that_selects_a_witness() {
    assert_refused_naming(
        &load_errors_of(&tied("t.ffy4r.t1", "Holder.size2(box(n: 0))")),
        &[
            "ambiguous dispatch of `t.ffy4r.t1.Holder.size2` on carrier `t.ffy4r.t1.Box`",
            "or write `[Spec = Witness]` in the call's bracket list, naming a witness sort among them",
        ],
        "two witnesses, no default",
    );
    let errs = load_errors_of(&tied("t.ffy4r.t2", "Holder.size2(box(n: 0))")).join(" | ");
    assert!(!errs.contains("No bracket names any of them"), "the repair is the bracket: {errs}");
    let run = |ns: &str, body: &str| run_int64(&tied(ns, body), &format!("{ns}.go"));
    assert_eq!(run("t.ffy4r.t3", "Holder.size2[Holder = W2](box(n: 0))"), Ok(22));
    assert_eq!(run("t.ffy4r.t4", "Holder.size2[Holder = W1](box(n: 0))"), Ok(11));
    // The body-less twin, as before.
    assert_eq!(run("t.ffy4r.t5", "Holder.size[Holder = W2](box(n: 0))"), Ok(2));
}

/// [refused, "a call does not choose a witness's instance"] A witness's name lowers to the bracket
/// in an operation body only: a rule body's call is evaluated by the resolver's bridge, which
/// reads no call-site bracket, so there it is refused, naming the bracket and where it is read.
/// Lowered there too, `W2.viaRecv(a(n: 1))` beside `A`'s own `viaRecv` answered `A`'s 7 (MEASURED
/// with the debug CLI). The same call in an operation body a rule calls answers `W2`'s.
#[test]
fn a_witness_name_in_a_rule_body_is_refused_where_no_bracket_is_read() {
    let src = |ns: &str, rule: &str| {
        mk_program(ns, A_OWN, "", "Int64", "W2.viaRecv(a(n: 1))")
            .trim_end()
            .strip_suffix("end")
            .expect("a namespace")
            .to_string()
            + rule
            + "\nend\n"
    };
    assert_refused_naming(
        &load_errors_of(&src("t.ffy4r.r1", "  rule r(?x) :- ?x <=> W2.viaRecv(a(n: 1))")),
        &[
            "`viaRecv` is `t.ffy4r.r1.Mk.viaRecv`, which `W2` provides as a witness at `t.ffy4r.r1.A`",
            "the bracket `[Mk = W2]`, which an operation body reads and this one does not",
        ],
        "a rule body reads no bracket",
    );
    let mut kb = load_kb_with(&src("t.ffy4r.r2", "  rule r(?x) :- ?x <=> go()"));
    let answers: Vec<i64> = query_unary(&mut kb, "t.ffy4r.r2.r")
        .into_iter()
        .map(|(v, definite)| match v {
            anthill_core::eval::Value::Int(i) if definite => i,
            other => panic!("a definite Int64, got {other:?} (definite: {definite})"),
        })
        .collect();
    assert_eq!(answers, vec![5], "the operation body's call runs `W2`'s instance");
}

/// [refused, unknown type-param 'Mk'] A witness whose own member reads a requirement of the
/// witness's own sort is entered with that sort's dictionary: `W2 requires Show[T = Int64]` and
/// its `viaRecv` calls `Show.show(8)`, answered by `IntShow` (108), through the bracket and
/// through `W2`'s name.
#[test]
fn a_witness_member_reading_its_own_sorts_requirement_runs() {
    let decls = "
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort IntShow
    provides Show[T = Int64]
    operation show(x: Int64) -> Int64 = add(x, 100)
  end
";
    let program = |ns: &str, body: &str| {
        mk_program(ns, "", "    operation viaRecv(c: A) -> Int64 = Show.show(8)", "Int64", body)
            .replacen("  import anthill.prelude.{Int64}\n", &format!("  import anthill.prelude.{{Int64}}\n  import anthill.prelude.Int64.{{add}}\n{decls}"), 1)
            .replacen("  sort W2\n", "  sort W2\n    requires Show[T = Int64]\n", 1)
    };
    for (ns, body) in [("t.ffy4r.w1", "Mk.viaRecv[Mk = W2](a(n: 9))"), ("t.ffy4r.w2", "W2.viaRecv(a(n: 9))")] {
        assert_eq!(run_int64(&program(ns, body), &format!("{ns}.go")), Ok(108), "`{body}`");
    }
}
