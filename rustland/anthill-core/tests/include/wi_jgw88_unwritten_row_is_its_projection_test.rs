//! WI-20261103-JGW88 — A ROW A REQUIREMENT LEAVES UNWRITTEN IS THE ROW ITS PROJECTION NAMES.
//!
//! Over `sort Strm { sort C = ?  effects E = ?  operation step(s: C) -> Int64 effects {E} }`, a
//! body under `requires Strm[C = P]` that declares `effects {P.E}` and calls `Strm.step(x)` (`x:
//! P`) incurs the row of the instance at `P` — the member the clause leaves unwritten,
//! WI-20261006-GVGSQ's unknown — and `P.E` is that row. WI-20261020-DNX0E made such a member the
//! projection the signature writes for a TYPE (`-> P.Val = Storage.get(x, k)`), by
//! `MintedParam::Member`'s `at` and the ζ arm, and left a row out of it. Measured on the parent
//! (29c0191f, with the CLI, and as back-outs 1–3 below together), each spelling — on an
//! operation's clause and on a sort's — refused "expected declared: [P.E], got undeclared
//! effect: Strm[C = P].E".
//!
//! What it took, each read where it is compared:
//!
//! - **The body's coverage** (`undeclared_effects`): the row member minted with its `at`
//!   (`declared_carrier_param`), and the row check asking the ζ identity of an atom
//!   (`atom_is_projected_instance_member`).
//! - **A row against a row** (`relate_effect_rows`, `cancel_instance_member_tails`): an arrow's
//!   `@ {P.E}` in the body is the instance's row too.
//! - **A caller** reads the callee's `P.E` off the carrier it fills `P` with (`check_apply_iter`,
//!   `resolve_type_deep_value`, as the call's result is read): `Error` at `Mem`, nothing at
//!   `Pure`. Past the body, `g(mem)` under `effects {Error}` was refused "undeclared effect:
//!   P.E", the callee's own name. Where the carrier's provisions do not read it, the call is
//!   refused naming the requirement to write it in, as a parameter's projection is
//!   (`UnreadProjection`).
//! - **Only the spec `P.E` is read through** (`rigid_projection_lender`): another clause at `P`
//!   leaving a member of that name unwritten is another instance's. Found by /code-review for
//!   rows and for types alike — with `A` requiring `B[C = C]`, `effects {P.E} requires A[C = P]
//!   = B.op(x)` covered `B`'s `Error` while callers read `A`'s `{}`, and `-> P.Val requires A[C
//!   = P] = B.get(x)` returned `B`'s `Int64` as `A`'s `String` (MEASURED; the type half since
//!   DNX0E).
//!
//! ## Back-outs, one at a time
//!
//! Measured over this file and the 27 suites the change reads through — `wi_dnx0e`,
//! `wi_gvgsq`, `wi_xqgew`, `wi1059`, `wi_kssa4`, `wi_qgvb1`, `wi826`, `wi841`, `wi_a3nnd`,
//! `provision_written_through_alias`, `wi_0rp29_review9`, `wi_sg16k`, `wi383`, `wi428`,
//! `wi1012`, `wi1010`, `wi_wbhtm`, and the effect suites `wi475`, `wi365`, `wi604`, `wi609`,
//! `wi612`, `wi1049`, `wi594`, `wi_1tjqh`, `wi_450ka` (377 rows). Each fails the rows of this
//! file named, and no other:
//!
//! 1. **A row minted with no `at`** (`declared_carrier_param` withheld for an effect row): 6 —
//!    every row whose body is over `P.E` (`a_row_a_requirement_…`, `a_caller_…`, `two_carriers_…`,
//!    `an_arrows_row_…`, `a_row_the_carriers_provision_…`, and `another_requirements_member_…`'s
//!    control), each body refused "undeclared effect: Strm[C = P].E" (`A[C = P].E`).
//! 2. **No ζ identity in the coverage check** (`undeclared_effects` without
//!    `atom_is_projected_instance_member`): the same but `an_arrows_row_…`, whose body incurs
//!    the annotation's own `P.E` at `f()`.
//! 3. **The call's row read through pure σ** (`check_apply_iter`'s `walk_type_deep_value`): 5 —
//!    `a_row_a_requirement_…`, `a_caller_…`, `two_carriers_…`, `an_arrows_row_…` and
//!    `another_requirements_member_…`'s control, each caller refused "`P.E` does not read at this
//!    call" (the unread check below reads the ungrounded `P.E`; with it backed out too, the
//!    parent's "undeclared effect: P.E").
//! 4. **Any clause at `P` taken for the lender** (`declared_carrier_param` without
//!    `rigid_projection_lender`): `another_requirements_member_…` — its row, type and own-clause
//!    shapes each load clean.
//! 5. **No row cancelled against its projection** (`relate_effect_rows` without
//!    `cancel_instance_member_tails`): `an_arrows_row_…`, refused "got () -> Int64 @ {Strm[C =
//!    P].E}".
//! 6. **No unread projection reported at a call** (the `UnreadProjection` check in
//!    `check_apply_iter`'s effect loop): `a_row_the_carriers_provision_…`, refused "undeclared
//!    effect: P.E".
//!
//! Pass under every back-out, by design: `a_row_left_unwritten_is_still_owed` — a body declaring
//! `effects {}`, and one declaring `P.E` that raises `Q`'s row, refused as on the parent.
//!
//! Not here, and still refused on this tree (MEASURED with the CLI): a caller forwarding the row
//! through a type parameter of its own (`h[Q](y: Q) effects {Q.E} requires Strm[C = Q] = g(y)`
//! is refused "undeclared effect: P.E", as its type twin `-> Q.Val = g(y, k)` is refused
//! "expected Q.Val, got P.Val"); `g` as a function value (`app(g, mem)`, refused "undeclared
//! effect: P.E", as `app(g, memStore)` over `-> P.Val` is refused "got P.Val"); a parametric
//! provider writing the row to its own parameter (`provides Strm[C = Wrap, E = R]`, refused
//! naming `P.E`, as `Val = T` is refused naming `P.Val`); `P.E` under a requirement writing the
//! row to a sibling parameter (`requires Strm[C = P, E = R]`, kept neutral by
//! `resolve_rigid_projection` — `effects {R}` is the spelling that runs); and a spec operation's
//! `effects {P.E}` read at a provision (`Car provides Sp[P = Mem]` overriding `Sp.h` with
//! `effects {Error}` is refused "does not refine it", `check_override_refinement` reading no
//! `P.E` at `P = Mem` — a load-time check this change does not touch).

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `Strm` provided at `Mem`, raising `Error`, and at `Pure`, raising nothing — beside `decl` and
/// `mains`.
fn strm_program(ns: &str, decl: &str, mains: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Error}}
  sort Strm
    sort C = ?
    effects E = ?
    operation step(s: C) -> Int64 effects {{E}}
  end
  sort Mem
    entity mem
    provides Strm[C = Mem, E = {{Error}}]
    operation step(s: Mem) -> Int64 effects {{Error}} = 7
  end
  sort Pure
    entity pure
    provides Strm[C = Pure, E = {{}}]
    operation step(s: Pure) -> Int64 = 5
  end
{decl}
{mains}
end
"#
    )
}

/// How many carriers `g` takes: `x: P`, or `x: P, y: Q` with `Strm[C = Q]` required beside.
#[derive(Clone, Copy, PartialEq)]
enum Carriers {
    One,
    Two,
}

/// `g`, declaring `effects {row}` with body `body`, under `requires Strm[C = P]` (and `Strm[C =
/// Q]`) — written on a sort `Sp` and on the operation `g[P]` itself; each with the call that
/// names it (`Sp.g`, `g`).
fn both_clause_kinds(
    ns: &str,
    carriers: Carriers,
    row: &str,
    body: &str,
) -> [(String, String, &'static str); 2] {
    let (params, sort_q, sort_req_q, op_params, op_req_q) = match carriers {
        Carriers::One => ("", "", "", "P", ""),
        Carriers::Two => (
            ", y: Q",
            "\n    sort Q = ?",
            "\n    requires Strm[C = Q]",
            "P, Q",
            ", Strm[C = Q]",
        ),
    };
    [
        (
            format!("{ns}.sort"),
            format!(
                "  sort Sp\n    sort P = ?{sort_q}\n    requires Strm[C = P]{sort_req_q}\n    \
                 operation g(x: P{params}) -> Int64 effects {{{row}}} = {body}\n  end"
            ),
            "Sp.g",
        ),
        (
            format!("{ns}.op"),
            format!(
                "  operation g[{op_params}](x: P{params}) -> Int64 effects {{{row}}} requires \
                 Strm[C = P]{op_req_q} = {body}"
            ),
            "g",
        ),
    ]
}

/// `src` is refused once, naming each of `expected`.
#[track_caller]
fn assert_refused_once(src: &str, expected: &[&str], why: &str) {
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 1, "{why}: one refusal: {errs:#?}");
    assert_refused_naming(&errs, expected, why);
}

/// `effects {P.E}` covers what the instance's `E` raises, and is read off the carrier the call
/// fills `P` with: `g(mem)` runs to 7 under `effects {Error}`, `g(pure)` to 5 under no row — the
/// requirement on the sort and on the operation alike. The parent refused the body, "expected
/// declared: [P.E], got undeclared effect: Strm[C = P].E".
#[test]
fn a_row_a_requirement_leaves_unwritten_is_the_row_its_projection_names() {
    for (ns, decl, call) in both_clause_kinds("wi_jgw88.covers", Carriers::One, "P.E", "Strm.step(x)") {
        let mains = format!(
            "  operation main() -> Int64 effects {{Error}} = {call}(mem) * 6\n  \
             operation mainPure() -> Int64 = {call}(pure)"
        );
        let src = strm_program(&ns, &decl, &mains);
        assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(42), "{ns}: at Mem");
        assert_eq!(run_int64(&src, &format!("{ns}.mainPure")), Ok(5), "{ns}: at Pure");
    }
}

/// A caller is held to the row of the carrier it fills `P` with: `g(mem)` under no row is refused
/// once, naming `Error` — the row of `Mem`'s provision, not the callee's `P.E` (back-out 3).
#[test]
fn a_caller_incurs_the_row_of_the_carrier_it_fills_the_parameter_with() {
    for (ns, decl, call) in both_clause_kinds("wi_jgw88.caller", Carriers::One, "P.E", "Strm.step(x)") {
        let src = strm_program(&ns, &decl, &format!("  operation main() -> Int64 = {call}(mem)"));
        assert_refused_once(
            &src,
            &["main.effects", "expected declared: [], got undeclared effect: Error"],
            &ns,
        );
    }
}

/// Two carriers' rows are each their own projection: `effects {P.E, Q.E}` covers `Strm.step(x) +
/// Strm.step(y)`, and runs at `(mem, pure)` to 12 under `effects {Error}`; under no row it is
/// refused naming `Error` at `(mem, pure)` and at `(pure, mem)` alike — each projection read off
/// its own argument.
#[test]
fn two_carriers_rows_are_each_their_own_projection() {
    let body = "Strm.step(x) + Strm.step(y)";
    for (ns, decl, call) in both_clause_kinds("wi_jgw88.two", Carriers::Two, "P.E, Q.E", body) {
        let mains = format!("  operation main() -> Int64 effects {{Error}} = {call}(mem, pure)");
        let src = strm_program(&ns, &decl, &mains);
        assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(12), "{ns}");
        for args in ["mem, pure", "pure, mem"] {
            let src = strm_program(&ns, &decl, &format!("  operation main() -> Int64 = {call}({args})"));
            assert_refused_once(
                &src,
                &["expected declared: [], got undeclared effect: Error"],
                &format!("{ns} at ({args})"),
            );
        }
    }
}

/// An arrow's `@ {P.E}` in the body is the instance's row as the declaration's is: `let f: () ->
/// Int64 @ {P.E} = lambda () -> Strm.step(x)` runs to 7 at `Mem`, where it was refused
/// "expected () -> Int64 @ {P.E}, got () -> Int64 @ {Strm[C = P].E}" (/code-review). Over
/// `Strm.step(y)`, `Q`'s row, the annotation is refused.
#[test]
fn an_arrows_row_in_the_body_is_the_instances_row_too() {
    let body = |at: &str| format!("{{\n    let f: () -> Int64 @ {{P.E}} = lambda () -> Strm.step({at})\n    f()\n  }}");
    for (ns, decl, call) in both_clause_kinds("wi_jgw88.arrow", Carriers::One, "P.E", &body("x")) {
        let src = strm_program(&ns, &decl, &format!("  operation main() -> Int64 effects {{Error}} = {call}(mem)"));
        assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(7), "{ns}");
    }
    for (ns, decl, _) in both_clause_kinds("wi_jgw88.arrow_other", Carriers::Two, "P.E", &body("y")) {
        assert_refused_naming(
            &load_errors_of(&strm_program(&ns, &decl, "")),
            &["f.annotation", "@ {Strm[C = Q].E}"],
            &ns,
        );
    }
}

/// A carrier whose provision leaves the row unwritten does not read `P.E`: `g(open)` is refused
/// naming the requirement to write it in, as a parameter's projection is — where it was refused
/// "undeclared effect: P.E" in a caller that has no `P` (/code-review).
#[test]
fn a_row_the_carriers_provision_leaves_unwritten_is_refused_naming_the_requirement() {
    let open = "  sort Open\n    entity open\n    provides Strm[C = Open]\n    \
                operation step(s: Open) -> Int64 = 2\n  end";
    for (ns, decl, call) in both_clause_kinds("wi_jgw88.unread", Carriers::One, "P.E", "Strm.step(x)") {
        let src = strm_program(&ns, &format!("{decl}\n{open}"), &format!("  operation main() -> Int64 = {call}(open)"));
        assert_refused_once(&src, &["`P.E` does not read at this call", "leaves `E` unwritten"], &ns);
    }
}

/// `A`, provided at `Mem` with the row `{}`, and `B`, which `Mem` provides with `{Error}` —
/// `A` requiring `B` of its carrier where `a_requires_b` — beside `decl`.
fn lender_program(ns: &str, a_requires_b: bool, decl: &str) -> String {
    let requires_b = if a_requires_b { "\n    requires B[C = C]" } else { "" };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Error, String}}
  sort B
    sort C = ?
    sort Val = ?
    effects E = ?
    operation op(s: C) -> Int64 effects {{E}}
    operation get(s: C) -> Val
  end
  sort A
    sort C = ?
    sort Val = ?
    effects E = ?{requires_b}
    operation opa(s: C) -> Int64 effects {{E}}
  end
  sort Mem
    entity mem
    provides A[C = Mem, Val = String, E = {{}}]
    provides B[C = Mem, Val = Int64, E = {{Error}}]
    operation op(s: Mem) -> Int64 effects {{Error}} = 7
    operation get(s: Mem) -> Int64 = 7
    operation opa(s: Mem) -> Int64 = 5
  end
{decl}
end
"#
    )
}

/// `P.E` and `P.Val` name the instance of the requirement they are read through, and no other
/// at `P`: under `requires A[C = P]`, `B`'s members — reached through `A`'s own requirement, or
/// through the operation's own clause inside a sort whose requirement is `A` — are `B`'s, and a
/// body that returns or raises them is refused naming them. The parent of /code-review's fix
/// loaded each, and a caller declaring no row called the row's (MEASURED). CONTROL: `A`'s own
/// row through the same sort runs to 5 under no row. (On a sort whose `A` requires `B`, `P.E`
/// reads both, and is refused as an ambiguous projection.)
#[test]
fn another_requirements_member_at_the_parameter_is_its_own_instance() {
    let refused = [
        (
            "row",
            true,
            "  operation g[P](x: P) -> Int64 effects {P.E} requires A[C = P] = B.op(x)",
            "undeclared effect: B[C = P].E",
        ),
        (
            "type",
            true,
            "  operation g[P](x: P) -> P.Val requires A[C = P] = B.get(x)",
            "expected P.Val, got B[C = P].Val",
        ),
        (
            "own",
            false,
            "  sort Sp\n    sort P = ?\n    requires A[C = P]\n    operation g(x: P) -> Int64 \
             effects {P.E} requires B[C = P] = B.op(x)\n  end",
            "undeclared effect: B[C = P].E",
        ),
    ];
    // Every shape judged before any is asserted, so a back-out names each it lets through.
    let verdicts: Vec<(String, Vec<String>, &str)> = refused
        .iter()
        .map(|(tag, a_requires_b, decl, refusal)| {
            let ns = format!("wi_jgw88.lender.{tag}");
            let errs = load_errors_of(&lender_program(&ns, *a_requires_b, decl));
            (ns, errs, *refusal)
        })
        .collect();
    let wrong: Vec<&(String, Vec<String>, &str)> = verdicts
        .iter()
        .filter(|(_, errs, refusal)| errs.len() != 1 || !errs[0].contains(refusal))
        .collect();
    assert!(wrong.is_empty(), "each refused once, naming its member: {wrong:#?}");
    let decl = "  sort Sp\n    sort P = ?\n    requires A[C = P]\n    operation g(x: P) -> Int64 \
                effects {P.E} requires B[C = P] = A.opa(x)\n  end\n  \
                operation main() -> Int64 = Sp.g(mem)";
    let src = lender_program("wi_jgw88.lender.control", false, decl);
    assert_eq!(run_int64(&src, "wi_jgw88.lender.control.main"), Ok(5));
}

/// CONTROL, by design the same on the parent: the row is still owed. A body declaring `effects
/// {}` is refused naming the instance's row, and one declaring `P.E` that raises `Q`'s row is
/// refused naming that row — `P.E` is the instance at `P` and no other.
#[test]
fn a_row_left_unwritten_is_still_owed() {
    let refused = [
        (
            "empty",
            Carriers::One,
            "",
            "Strm.step(x)",
            "expected declared: [], got undeclared effect: Strm[C = P].E",
        ),
        (
            "other",
            Carriers::Two,
            "P.E",
            "Strm.step(y)",
            "expected declared: [P.E], got undeclared effect: Strm[C = Q].E",
        ),
    ];
    for (tag, carriers, row, body, refusal) in refused {
        for (ns, decl, _) in both_clause_kinds(&format!("wi_jgw88.owed.{tag}"), carriers, row, body) {
            assert_refused_once(&strm_program(&ns, &decl, ""), &["g.effects", refusal], &ns);
        }
    }
}
