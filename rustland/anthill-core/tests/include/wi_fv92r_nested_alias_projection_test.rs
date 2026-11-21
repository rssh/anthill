//! WI-20261103-FV92R — a projection off a `let`-aliased receiver is the projection off the path
//! the alias names WHEREVER the annotation writes it, not at its top alone. Over `let t = st`,
//! `let p: (k: t.provider.K, n: Int64) = (k: j, n: 1)` was refused "type mismatch in
//! p.annotation (let-binding): expected (k: t.provider.K, n: Int64), got (k: st.provider.K, n:
//! Int64)", `let o: Option[T = t.provider.K] = some(j)` likewise, and a lambda binder `p: (k:
//! t.provider.K, n: Int64)` at `check(st, p.k)`, "expected st.provider.K, got t.provider.K"
//! (MEASURED on 5175d999 with the debug CLI). The alias was read by a step BEFORE the elimination
//! walk (`canonicalize_projection_receivers`) that rewrote a top-level projection only; nested,
//! `t.provider` is abstract, `t.provider.K` stays a neutral, and it kept the alias's name.
//!
//! The walk reads the alias itself now, at the receiver and before the receiver's type
//! (`project_expr_carried`), so the step is gone. At the receiver and NOT on the neutral: read on
//! the neutral it came, an alias of a FIELD PATH (`let pr = st.provider`, `pr.K`) was refused
//! "cannot project 'K' off an abstract receiver with no concrete sort", at the top too, where the
//! step had read it — only the path `st.provider` finds the `requires` of `State` that declares
//! `K` (MEASURED on the first version of this change).
//!
//! BACK-OUT, MEASURED: the walk reading no alias and the step put back (a temporary switch, over
//! the whole `wi_tests`, 9687 tests) fails 4, all here — `the_tickets_three_programs_run`,
//! `every_nesting_of_the_projection_reads_the_alias`,
//! `a_nested_projection_handed_to_another_state_is_refused_at_the_call` (refused at the
//! annotation instead) and `the_alias_in_scope_is_the_one_read` (its re-bound row, likewise).
//! No other row of the suite writes a projection through an alias below the annotation's top.
//!
//! PASS EITHER WAY BY DESIGN: `a_top_level_projection_through_an_alias_still_reads_it`, the step's
//! own rows, which the walk now reads the same; and in `the_alias_in_scope_is_the_one_read` the
//! lambda parameter shadowing the alias, which no alias reading ever touched.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// The ticket's sorts: `State` holds a `provider` of an open `P` whose `K` the `requires` lends;
/// `MemStore` provides it at `Int64`; `check` takes a key of the `State` it is given.
const SORTS: &str = "  import anthill.prelude.{Int64, String, List, Option}
  import anthill.prelude.Option.{some, none}
  sort DataProvider
    sort P = ?
    sort K = ?
  end
  sort State
    sort P = ?
    requires DataProvider[P = P]
    entity state(provider: P)
  end
  sort MemStore
    entity mem(n: Int64)
    provides DataProvider[P = MemStore, K = Int64]
  end
  operation check(s: State, k: s.provider.K) -> Int64 = 42";

/// The ticket's program: `fwd(st, j)` whose body is `let t = st` and then `body`, run by `go` at a
/// `State[P = MemStore]`.
fn ticket_program(ns: &str, body: &str) -> String {
    format!(
        "namespace {ns}
{SORTS}
  operation fwd(st: State, j: st.provider.K) -> Int64 =
    let t = st
    {body}
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, 41)
end
"
    )
}

/// [`ticket_program`] with a second `State`, `u`, and a key `ju` of its own.
fn two_state_program(ns: &str, body: &str) -> String {
    format!(
        "namespace {ns}
{SORTS}
  operation fwd(st: State, u: State, j: st.provider.K, ju: u.provider.K) -> Int64 =
    let t = st
    {body}
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, st, 41, 41)
end
"
    )
}

/// Each `(tag, src)` runs `go` to 42.
#[track_caller]
fn assert_run(ns: &str, rows: &[(&str, String)]) {
    for (tag, src) in rows {
        assert_eq!(run_int64(src, &format!("{ns}.{tag}.go")), Ok(42), "{tag}");
    }
}

/// `src` is refused once, naming `refusal`.
#[track_caller]
fn assert_refused(src: &str, refusal: &str, why: &str) {
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 1, "{why}: one refusal: {errs:#?}");
    assert_refused_naming(&errs, &[refusal], why);
}

/// The ticket's acceptance: the three programs run to 42.
/// FAILS backed out (each refused as the module doc quotes).
#[test]
fn the_tickets_three_programs_run() {
    let ns = "wi_fv92r.ticket";
    let rows = [
        ("tuple", "let p: (k: t.provider.K, n: Int64) = (k: j, n: 1)\n    check(st, p.k)"),
        ("option", "let o: Option[T = t.provider.K] = some(j)\n    42"),
        (
            "lambda",
            "let h = lambda (p: (k: t.provider.K, n: Int64)) -> check(st, p.k)\n    h((k: j, n: 1))",
        ),
    ];
    let rows: Vec<_> = rows
        .iter()
        .map(|(tag, body)| (*tag, ticket_program(&format!("{ns}.{tag}"), body)))
        .collect();
    assert_run(ns, &rows);
}

/// The projection is read through the alias at any depth and in any form that writes it: an
/// option of a tuple, taken apart by a `match`; a list; an arrow's parameter; a tuple pattern's
/// binder; through two aliases; and off an alias of a FIELD PATH, whose projection only the path
/// can read (`pr.K` under `let pr = st.provider`, and `let pr = t.provider`, an alias's field).
/// FAILS backed out: each nested row refused at its annotation, the field-path rows "cannot
/// project 'K' off an abstract receiver with no concrete sort".
#[test]
fn every_nesting_of_the_projection_reads_the_alias() {
    let ns = "wi_fv92r.nested";
    let rows = [
        (
            "option_of_tuple",
            "let o: Option[T = (k: t.provider.K, n: Int64)] = some((k: j, n: 1))
    match o case some(p) -> check(st, p.k) case none() -> 0",
        ),
        ("list", "let xs: List[T = t.provider.K] = [j]\n    42"),
        (
            "arrow",
            "let f: (x: t.provider.K) -> Int64 = lambda (x: st.provider.K) -> check(st, x)\n    f(j)",
        ),
        (
            "pattern_binder",
            "let (a: (k: t.provider.K, n: Int64), b) = ((k: j, n: 1), 2)\n    check(st, a.k)",
        ),
        (
            "chain",
            "let t2 = t\n    let p: (k: t2.provider.K, n: Int64) = (k: j, n: 1)\n    check(st, p.k)",
        ),
        ("field_path", "let pr = st.provider\n    let o: Option[T = pr.K] = some(j)\n    42"),
        (
            "field_path_of_alias",
            "let pr = t.provider\n    let p: (k: pr.K, n: Int64) = (k: j, n: 1)\n    check(st, p.k)",
        ),
    ];
    let rows: Vec<_> = rows
        .iter()
        .map(|(tag, body)| (*tag, ticket_program(&format!("{ns}.{tag}"), body)))
        .collect();
    assert_run(ns, &rows);
}

/// The ticket's control: a nested `t.provider.K` is `st`'s key, so handed to `check(u, …)` for
/// another `u: State` it is refused there — the annotation reads and the call does not.
/// FAILS backed out: each refused at its annotation, before the call.
#[test]
fn a_nested_projection_handed_to_another_state_is_refused_at_the_call() {
    let other = "type mismatch in check.k (op-arg): expected u.provider.K, got st.provider.K";
    let rows = [
        ("tuple", "let p: (k: t.provider.K, n: Int64) = (k: j, n: 1)\n    check(u, p.k)"),
        (
            "option_of_tuple",
            "let o: Option[T = (k: t.provider.K, n: Int64)] = some((k: j, n: 1))
    match o case some(p) -> check(u, p.k) case none() -> 0",
        ),
        (
            "lambda",
            "let h = lambda (p: (k: t.provider.K, n: Int64)) -> check(u, p.k)\n    h((k: j, n: 1))",
        ),
        (
            "pattern_binder",
            "let (a: (k: t.provider.K, n: Int64), b) = ((k: j, n: 1), 2)\n    check(u, a.k)",
        ),
        (
            "field_path",
            "let pr = t.provider\n    let p: (k: pr.K, n: Int64) = (k: j, n: 1)\n    check(u, p.k)",
        ),
    ];
    for (tag, body) in rows {
        assert_refused(
            &two_state_program(&format!("wi_fv92r.other.{tag}"), body),
            other,
            tag,
        );
    }
}

/// The alias read is the one IN SCOPE. Re-bound (`let t = u`), `t.provider.K` nested is `u`'s
/// key: it takes `ju` and runs where `u`'s key is asked for, and is refused where `st`'s is.
/// A lambda parameter `t` is its own receiver, not the alias it shadows: `check(st, p.k)` over it
/// is refused.
///
/// And the alias names its target's BINDING, not its spelling: a binder symbol is fresh per
/// binding site, so a later binder spelled `st` — a `let st = u`, a lambda parameter, an arrow's
/// own parameter around the projection — is another value, and `t.provider.K` stays the outer
/// `st`'s key under each. `/code-review` read the rewrite as captured by such a binder (the
/// arrow's `st`, the lambda's); MEASURED, it is not: under the arrow `(st: State, k:
/// t.provider.K)`, `f(u, j)` runs and `f(u, ju)` is refused.
///
/// FAIL backed out, MEASURED row by row: every row but `lambda_param` — the runs refused, and
/// the refusals refused elsewhere, at the annotation or the lambda's binder (`t.provider.K` as
/// written), or, `target_lambda_param`, naming `t.provider.K` where the fix names the outer
/// `st`'s key. `lambda_param` passes either way by design: no alias is read under it.
#[test]
fn the_alias_in_scope_is_the_one_read() {
    let ns = "wi_fv92r.scope";
    let runs = [
        (
            "rebound",
            "let t = u\n    let p: (k: t.provider.K, n: Int64) = (k: ju, n: 1)\n    check(u, p.k)",
        ),
        (
            "target_rebound",
            "let st = u\n    let p: (k: t.provider.K, n: Int64) = (k: j, n: 1)\n    check(t, p.k)",
        ),
        (
            "target_arrow_binder",
            "let f: (st: State, k: t.provider.K) -> Int64 = lambda (s: State, k: t.provider.K) -> check(t, k)
    f(u, j)",
        ),
    ];
    let runs: Vec<_> = runs
        .iter()
        .map(|(tag, body)| (*tag, two_state_program(&format!("{ns}.{tag}"), body)))
        .collect();
    assert_run(ns, &runs);
    for (tag, body, refusal) in [
        (
            "target_rebound_st",
            "let st = u\n    let p: (k: t.provider.K, n: Int64) = (k: j, n: 1)\n    check(st, p.k)",
            "type mismatch in check.k (op-arg): expected u.provider.K, got st.provider.K",
        ),
        (
            "target_lambda_param",
            "let h = lambda (st: State) -> lambda (p: (k: t.provider.K, n: Int64)) -> check(st, p.k)\n    42",
            "expected st.provider.K, got st.provider.K (these render alike because `st` is two",
        ),
        (
            "target_arrow_binder_foreign",
            "let f: (st: State, k: t.provider.K) -> Int64 = lambda (s: State, k: t.provider.K) -> check(t, k)
    f(u, ju)",
            "type mismatch in f.k (op-arg): expected st.provider.K, got u.provider.K",
        ),
    ] {
        assert_refused(&two_state_program(&format!("{ns}.{tag}"), body), refusal, tag);
    }
    assert_refused(
        &two_state_program(
            &format!("{ns}.rebound_st"),
            "let t = u\n    let p: (k: t.provider.K, n: Int64) = (k: ju, n: 1)\n    check(st, p.k)",
        ),
        "type mismatch in check.k (op-arg): expected st.provider.K, got u.provider.K",
        "the re-bound alias's key handed to `st`'s",
    );
    assert_refused(
        &two_state_program(
            &format!("{ns}.lambda_param"),
            "let h = lambda (t: State) -> lambda (p: (k: t.provider.K, n: Int64)) -> check(st, p.k)\n    42",
        ),
        "type mismatch in check.k (op-arg): expected st.provider.K, got t.provider.K",
        "the lambda parameter `t` shadowing the alias",
    );
}

/// CONTROL — the rows the step before the walk read, at the top of the annotation: a `let`, a
/// tuple pattern's binder, a lambda's, an alias of a field path; each runs, and handed to
/// `check(u, …)` is refused. PASSES EITHER WAY BY DESIGN: the walk reads them as the step did.
#[test]
fn a_top_level_projection_through_an_alias_still_reads_it() {
    let ns = "wi_fv92r.top";
    let rows = [
        ("let", "let k: t.provider.K = j\n    check(ST, k)"),
        ("pattern_binder", "let (a: t.provider.K, b) = (j, 2)\n    check(ST, a)"),
        ("lambda", "let h = lambda (k: t.provider.K) -> check(ST, k)\n    h(j)"),
        ("field_path", "let pr = st.provider\n    let k: pr.K = j\n    check(ST, k)"),
    ];
    let runs: Vec<_> = rows
        .iter()
        .map(|(tag, body)| {
            (*tag, ticket_program(&format!("{ns}.{tag}"), &body.replace("ST", "st")))
        })
        .collect();
    assert_run(ns, &runs);
    for (tag, body) in rows {
        assert_refused(
            &two_state_program(&format!("{ns}.other.{tag}"), &body.replace("ST", "u")),
            "type mismatch in check.k (op-arg): expected u.provider.K, got st.provider.K",
            tag,
        );
    }
}
