//! WI-20261103-SG16K — a typed lambda binder whose annotation projects a parameter its
//! receiver fixes is the type the projection reads to. Under `x: Leaf[E = Int64]`,
//! `lambda (s: List[T = x.E]) -> true` was refused "type mismatch in <binder>.s
//! (binder-annotation): expected List[T = x.E], got List[T = Int64]", with no key involved: the
//! lambda arm read only the projections off a name that denotes a sort, so its parameter
//! type kept `x.E` as written, and the binder check, which reads the same annotation off the
//! receivers' types, compared `List[T = Int64]` with it. Over an open `E` the two readings are
//! one neutral, and it loaded.
//!
//! Now a body's annotation has one reader, `read_written_annotation`, and the `let` arm, the
//! lambda arm and the binder check all go through it: each projection is read off its receiver's
//! type in scope, a let-aliased compound receiver as the path it names (the `let` arm's step,
//! WI-400 increment C). A projection that does not read is refused wherever it is written; a
//! binder among several of a lambda's parameters kept it raw in silence.
//!
//! STILL REFUSED, as the `let` and the signature refuse them, though the lambda loaded them
//! unread: a projection off an un-annotated binder (`lambda x -> lambda (s: List[T = x.E])`), off
//! a type parameter whose only bound is a `requires` (`x.Key`, `x: P`, `requires Storage[C = P]`;
//! WI-20261103-G5FK3), and off a spec's own carrier in its default body (`c.Elem`, `c: C`;
//! WI-20261103-95S43 — reading it through `this_instance_member` was tried here and backed out:
//! with no gate for a projection an author writes, it loaded `let y: x.T = x` in a data sort).
//!
//! BACK-OUTS, MEASURED — each ONE part put back, over this file's 10 rows:
//!
//!  * The lambda arm reading the denoted names alone (as before) — 6, each a lambda whose one
//!    parameter's annotation the binder check reads otherwise, refused at the binder or where the
//!    unread type is used: `a_binder_projecting_a_fixed_member_is_the_member_it_reads_to`,
//!    `the_lambda_applied_to_another_element_type_is_refused`,
//!    `the_binder_reads_its_receiver_where_the_lambda_is_written`,
//!    `the_binder_is_read_inside_any_type_its_annotation_writes`,
//!    `a_compound_receiver_through_an_alias_is_the_path_it_names` and
//!    `a_call_result_through_an_alias_meets_the_binder_through_it` (their lone binders). And
//!    `wi_7ab56_projection_key_test`'s `a_projection_key_is_judged_at_its_receivers_declared_type`,
//!    which drives the lambda position at `Int64`.
//!  * The binder check keeping an unread projection raw, in silence (as before) — 1:
//!    `a_binder_among_several_is_read_and_refused_as_one_alone_is` (`x.Nope` beside `b` loads).
//!  * No alias step in `read_written_annotation` — 2:
//!    `a_compound_receiver_through_an_alias_is_the_path_it_names` and
//!    `a_call_result_through_an_alias_meets_the_binder_through_it`, refused at `check(st, k)`,
//!    "expected st.provider.K, got t.provider.K". And `wi_0rp29_review9_regressions_test`'s
//!    `a_let_annotation_through_an_alias_names_its_target`, the `let` spelling.
//!  * A call not reading its argument through the alias (no aliases given `call_arg_paths`, an
//!    older step this file measures for WI-20261103-F9ZR9) — 1: `a_call_result_through_an_alias_meets_the_binder_through_it`,
//!    refused at `get(t, j)`, "expected t.provider.K, got st.provider.K". And four rows of
//!    `wi_0rp29_review9_regressions_test`: `a_let_annotation_through_an_alias_names_its_target`,
//!    `a_lambda_hint_names_a_let_aliass_receiver_as_the_call_does`,
//!    `a_returned_projection_names_a_let_aliass_receiver_as_its_parameters_do` and
//!    `a_returned_projection_through_a_let_alias_meets_its_annotation`.
//!
//! PASS EITHER WAY BY DESIGN: `over_an_open_member_the_binder_stays_the_neutral_it_was`, the
//! control (an open member reads to the neutral `x.E` both ways). Under the first part the
//! unknown-member and refused rows pass too: the binder check reads the same annotation and
//! refuses it, so a lone binder's unread projection is refused by either site.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// A program declaring `decl` beside `Leaf`, whose member `E` an instance may fix, `W`, whose
/// field fixes it, and `Storage`, a spec with a carrier and a member `Key`.
fn program(ns: &str, decl: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Set, List, Option, String}}
  import anthill.prelude.Option.{{some, none}}
  sort Leaf
    sort E = ?
    entity leaf(e: E)
  end
  sort W
    entity w(l: Leaf[E = Int64])
  end
  sort Storage
    sort C = ?
    sort Key = ?
  end
  {decl}
end
"#
    )
}

/// `src` loads with no refusal.
#[track_caller]
fn assert_loads(src: &str, why: &str) {
    let errs = load_errors_of(src);
    assert!(errs.is_empty(), "{why} should load: {errs:#?}");
}

/// `src` is refused once, naming `expected` ([`assert_refused_naming`]).
#[track_caller]
fn assert_refused(src: &str, expected: &str, why: &str) {
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 1, "{why}: one refusal: {errs:#?}");
    assert_refused_naming(&errs, &[expected], why);
}

/// The ticket's program loads, at `List` and at `Set`, and the binder is `Int64`'s in the
/// body: `n + 1` types, and runs.
#[test]
fn a_binder_projecting_a_fixed_member_is_the_member_it_reads_to() {
    for container in ["List", "Set"] {
        let src = program(
            &format!("wi_sg16k.fixed.{}", container.to_lowercase()),
            &format!(
                "operation k(x: Leaf[E = Int64]) -> Bool =\n    let h = lambda (s: {container}[T = x.E]) -> true\n    true"
            ),
        );
        assert_loads(&src, &format!("`{container}[T = x.E]` over `x: Leaf[E = Int64]`"));
    }
    let src = program(
        "wi_sg16k.fixed.run",
        "operation k(x: Leaf[E = Int64]) -> Int64 =
    let h = lambda (s: Option[T = x.E]) -> (match s
        case some(n) -> n + 1
        case none -> 0)
    h(some(41))
  operation main() -> Int64 = k(leaf(e: 1))",
    );
    assert_eq!(run_int64(&src, "wi_sg16k.fixed.run.main"), Ok(42));
}

/// The ticket's acceptance: the lambda applied to a `List[T = String]` is refused at the
/// argument, against the type its binder reads to; applied to a `List[T = Int64]` it loads.
/// `Set` the same.
#[test]
fn the_lambda_applied_to_another_element_type_is_refused() {
    for container in ["List", "Set"] {
        let at = |arg: &str| {
            format!(
                "operation k(x: Leaf[E = Int64], ys: {container}[T = {arg}]) -> Bool =\n    let h = lambda (s: {container}[T = x.E]) -> true\n    h(ys)"
            )
        };
        let tag = container.to_lowercase();
        assert_refused(
            &program(&format!("wi_sg16k.apply.{tag}.string"), &at("String")),
            &format!(
                "type mismatch in h._1 (op-arg): expected {container}[T = Int64], got {container}[T = String]"
            ),
            &format!("`h` applied to a `{container}[T = String]`"),
        );
        assert_loads(
            &program(&format!("wi_sg16k.apply.{tag}.int"), &at("Int64")),
            &format!("`h` applied to a `{container}[T = Int64]`"),
        );
    }
}

/// The receiver is read where the lambda is written: a `let` alias of a parameter, nested and
/// as the whole annotation; a field path; an outer lambda's binder; a `match` binder. Each
/// loads applied at `Int64` and is refused applied at `String`.
#[test]
fn the_binder_reads_its_receiver_where_the_lambda_is_written() {
    let list = "expected List[T = Int64], got List[T = String]";
    let rows: [(&str, fn(&str) -> String, &str); 5] = [
        (
            "alias",
            |arg| format!("operation k(x: Leaf[E = Int64], ys: List[T = {arg}]) -> Bool =\n    let y = x\n    let h = lambda (s: List[T = y.E]) -> true\n    h(ys)"),
            list,
        ),
        (
            "alias_whole",
            |arg| format!("operation k(x: Leaf[E = Int64], y0: {arg}) -> Bool =\n    let y = x\n    let h = lambda (s: y.E) -> true\n    h(y0)"),
            "expected Int64, got String",
        ),
        (
            "field",
            |arg| format!("operation k(v: W, ys: List[T = {arg}]) -> Bool =\n    let h = lambda (s: List[T = v.l.E]) -> true\n    h(ys)"),
            list,
        ),
        (
            "outer_lambda",
            |arg| format!("operation k(ys: List[T = {arg}]) -> Bool =\n    let h = lambda (x: Leaf[E = Int64]) -> lambda (s: List[T = x.E]) -> true\n    let g = h(leaf(e: 1))\n    g(ys)"),
            list,
        ),
        (
            "match",
            |arg| format!("operation k(o: Option[T = Leaf[E = Int64]], ys: List[T = {arg}]) -> Bool =\n    match o\n      case some(x) -> (let h = lambda (s: List[T = x.E]) -> true\n        h(ys))\n      case none -> false"),
            list,
        ),
    ];
    for (tag, at, refusal) in rows {
        assert_loads(
            &program(&format!("wi_sg16k.recv.{tag}.int"), &at("Int64")),
            &format!("the receiver read through the {tag}, applied at `Int64`"),
        );
        assert_refused(
            &program(&format!("wi_sg16k.recv.{tag}.string"), &at("String")),
            refusal,
            &format!("the receiver read through the {tag}, applied at `String`"),
        );
    }
}

/// `fwd` whose body is `let t = st` and then `body`, its lines after the first indented as a body
/// line is. Beside it `check`, whose key is its `State`'s, `get`, which answers the key it is
/// given at its `State`'s, and a second `State`, `u`, with a key `ju` of its own; `go` runs `fwd`
/// at one `State` for both.
fn alias_program(ns: &str, body: &str) -> String {
    program(
        ns,
        &format!(
            "sort DataProvider
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
  operation check(s: State, k: s.provider.K) -> Int64 = 42
  operation get(s: State, k: s.provider.K) -> s.provider.K = k
  operation fwd(st: State, u: State, j: st.provider.K, ju: u.provider.K) -> Int64 =
    let t = st
    {body}
  operation go() -> Int64 =
    let st: State[P = MemStore] = state(provider: mem(n: 1))
    fwd(st, st, 41, 41)"
        ),
    )
}

/// Each `(tag, body)` of `runs` runs to 42; each `(tag, body, refusal)` of `refused` is refused
/// once, naming `refusal`.
#[track_caller]
fn assert_alias_rows(ns: &str, runs: &[(&str, &str)], refused: &[(&str, &str, &str)]) {
    for (tag, body) in runs {
        let ns = format!("{ns}.{tag}");
        assert_eq!(run_int64(&alias_program(&ns, body), &format!("{ns}.go")), Ok(42), "{tag}");
    }
    for (tag, body, refusal) in refused {
        assert_refused(&alias_program(&format!("{ns}.{tag}"), body), refusal, tag);
    }
}

/// A compound receiver through a `let` alias is the path the alias names, so `k: t.provider.K`
/// under `let t = st` is `st.provider.K` — whose member is abstract, `State`'s `requires` lending
/// it — and `check(st, k)` takes it, at a lambda's lone binder and at one of several; each runs.
/// Before SG16K the two were refused at `check(st, k)`, "expected st.provider.K, got
/// t.provider.K". `check(u, k)` for another `State` is refused. The `let` spelling is
/// `wi_0rp29_review9_regressions_test`'s `a_let_annotation_through_an_alias_names_its_target`.
/// NOT HERE: the projection nested in a type (`p: (k: t.provider.K, n: Int64)`) stays keyed to `t`
/// and is refused there, in a `let` as well, the alias step's own boundary (WI-20261103-FV92R).
#[test]
fn a_compound_receiver_through_an_alias_is_the_path_it_names() {
    assert_alias_rows(
        "wi_sg16k.alias",
        &[
            ("one", "let h = lambda (k: t.provider.K) -> check(st, k)\n    h(j)"),
            ("several", "let h = lambda (k: t.provider.K, n: Int64) -> check(st, k)\n    h(j, 1)"),
        ],
        &[(
            "other",
            "let h = lambda (k: t.provider.K) -> check(u, k)\n    h(j)",
            "type mismatch in check.k (op-arg): expected u.provider.K, got st.provider.K",
        )],
    );
}

/// A call's result meets the binder through the same alias: `get(t, j)` is `st.provider.K`, the
/// call reading its argument `t` as the path it names, as the binder `k: t.provider.K` is read,
/// so `h(get(t, j))` runs — at a lone binder, at one of several, at a binder written
/// `st.provider.K`, and through two aliases, `let t2 = t` (WI-20261103-F9ZR9; before SG16K each
/// but the third was refused at `check(st, k)`, "expected st.provider.K, got t.provider.K", the
/// two aliases' "got t2.provider.K").
/// Refused: the body handing `k` to `check(u, k)` for another `u`, through one alias and two, and
/// the lone binder given `get(u, ju)`, which is `u`'s key. NOT HERE: a binder among several given
/// `get(u, ju)` loads, the parameter list a fresh variable where no arrow is expected
/// (WI-20261103-2N4QH).
#[test]
fn a_call_result_through_an_alias_meets_the_binder_through_it() {
    let other = "type mismatch in check.k (op-arg): expected u.provider.K, got st.provider.K";
    assert_alias_rows(
        "wi_sg16k.alias.call",
        &[
            ("one", "let h = lambda (k: t.provider.K) -> check(st, k)\n    h(get(t, j))"),
            (
                "several",
                "let h = lambda (k: t.provider.K, n: Int64) -> check(st, k)\n    h(get(t, j), 1)",
            ),
            ("st_binder", "let h = lambda (k: st.provider.K) -> check(st, k)\n    h(get(t, j))"),
            (
                "chain",
                "let t2 = t\n    let h = lambda (k: t2.provider.K) -> check(st, k)\n    h(get(t2, j))",
            ),
        ],
        &[
            ("other", "let h = lambda (k: t.provider.K) -> check(u, k)\n    h(get(t, j))", other),
            (
                "chain_other",
                "let t2 = t\n    let h = lambda (k: t2.provider.K) -> check(u, k)\n    h(get(t2, j))",
                other,
            ),
            (
                "foreign",
                "let h = lambda (k: t.provider.K) -> check(st, k)\n    h(get(u, ju))",
                "type mismatch in h._1 (op-arg): expected st.provider.K, got u.provider.K",
            ),
        ],
    );
}

/// A projection is read wherever the annotation writes it: in a function type's parameter, in a
/// tuple type's components, off a rigid whose `requires` fixes the member, and off an open member
/// through an alias, where it is the neutral the aliased parameter's own type writes.
#[test]
fn the_binder_is_read_inside_any_type_its_annotation_writes() {
    assert_loads(
        &program(
            "wi_sg16k.inside.arrow",
            "operation k(x: Leaf[E = Int64]) -> Bool =\n    let h = lambda (f: (y: x.E) -> Bool) -> f(1)\n    true",
        ),
        "`f: (y: x.E) -> Bool` called at `1`",
    );
    assert_refused(
        &program(
            "wi_sg16k.inside.arrow.string",
            "operation k(x: Leaf[E = Int64]) -> Bool =\n    let h = lambda (f: (y: x.E) -> Bool) -> f(\"a\")\n    true",
        ),
        "type mismatch in f._1 (op-arg): expected Int64, got String",
        "`f: (y: x.E) -> Bool` called at `\"a\"`",
    );
    let src = program(
        "wi_sg16k.inside.tuple",
        "operation k(x: Leaf[E = Int64]) -> Int64 =\n    let h = lambda (p: (a: x.E, b: x.E)) -> p.a + p.b\n    h((a: 1, b: 2))\n  operation main() -> Int64 = k(leaf(e: 1))",
    );
    assert_eq!(run_int64(&src, "wi_sg16k.inside.tuple.main"), Ok(3));
    assert_refused(
        &program(
            "wi_sg16k.inside.tuple.string",
            "operation k(x: Leaf[E = Int64]) -> Bool =\n    let h = lambda (p: (a: x.E, b: x.E)) -> true\n    h((a: 1, b: \"y\"))",
        ),
        // One tuple is the argument list (kernel-language §4.4), so each component is an
        // argument of its own and the one at `b` is refused.
        "type mismatch in h.b (op-arg): expected Int64, got String",
        "`p: (a: x.E, b: x.E)` applied at `(a: 1, b: \"y\")`",
    );
    let rigid = |key: &str| {
        format!("operation k[P]() -> Bool requires Storage[C = P, Key = {key}] =\n    let h = lambda (s: P.Key) -> s + 1\n    true")
    };
    assert_loads(
        &program("wi_sg16k.inside.rigid", &rigid("Int64")),
        "`s: P.Key` with `Key = Int64`, `s + 1`",
    );
    assert_refused(
        &program("wi_sg16k.inside.rigid.string", &rigid("String")),
        "type mismatch in add.b (op-arg): expected String, got Int64",
        "`s: P.Key` with `Key = String`, `s + 1`",
    );
    let open_alias = |arg: &str| {
        format!("operation k(x: Leaf, ys: List[T = {arg}]) -> Bool =\n    let y = x\n    let h = lambda (s: List[T = y.E]) -> true\n    h(ys)")
    };
    assert_loads(
        &program("wi_sg16k.inside.open_alias", &open_alias("x.E")),
        "`List[T = y.E]` under `let y = x`, applied at `List[T = x.E]`",
    );
    assert_refused(
        &program("wi_sg16k.inside.open_alias.int", &open_alias("Int64")),
        "type mismatch in h._1 (op-arg): expected List[T = x.E], got List[T = Int64]",
        "`List[T = y.E]` under `let y = x`, applied at `List[T = Int64]`",
    );
}

/// One of several binders of a lambda's parameter list is read as a lone one: a fixed member is
/// its type in the body, an unknown member is refused at the binder. It was kept raw in silence.
#[test]
fn a_binder_among_several_is_read_and_refused_as_one_alone_is() {
    let src = program(
        "wi_sg16k.several.run",
        "operation k(x: Leaf[E = Int64]) -> Int64 =\n    let h = lambda (s: x.E, b: Int64) -> s + b\n    h(1, 2)\n  operation main() -> Int64 = k(leaf(e: 1))",
    );
    assert_eq!(run_int64(&src, "wi_sg16k.several.run.main"), Ok(3));
    assert_refused(
        &program(
            "wi_sg16k.several.nope",
            "operation k(x: Leaf[E = Int64]) -> Bool =\n    let h = lambda (s: List[T = x.Nope], b: Int64) -> true\n    true",
        ),
        "type mismatch in <binder>.s (binder-annotation): expected a well-formed type projection, got type 'wi_sg16k.several.nope.Leaf' has no member 'Nope'",
        "`s: List[T = x.Nope]` beside `b: Int64`",
    );
}

/// A member the receiver does not declare is refused at the binder, where the projection is
/// formed.
#[test]
fn a_member_the_receiver_does_not_declare_is_refused_at_the_binder() {
    assert_refused(
        &program(
            "wi_sg16k.nope",
            "operation k(x: Leaf[E = Int64]) -> Bool =\n    let h = lambda (s: List[T = x.Nope]) -> true\n    true",
        ),
        "type mismatch in <binder>.s (binder-annotation): expected a well-formed type projection, got type 'wi_sg16k.nope.Leaf' has no member 'Nope'",
        "`List[T = x.Nope]`",
    );
}

/// A projection the `let` and the signature refuse is refused at a lambda's binder too, where it
/// loaded unread: off an un-annotated binder, off a type parameter whose only bound is a
/// `requires` (WI-20261103-G5FK3), and off a spec's own carrier in its default body — `c.Elem`,
/// `c: C`, refused as `-> c.Elem` is (WI-20261103-95S43). Each beside its `let`
/// spelling, refused for the same reason.
#[test]
fn projections_the_let_and_the_signature_refuse_are_refused_at_the_binder() {
    let unannotated = |inner: &str| format!("operation k() -> Bool =\n    let f = lambda x -> {inner}\n    true");
    let required = |inner: &str| {
        format!("operation k[P](x: P) -> Bool requires Storage[C = P] =\n    {inner}\n    true")
    };
    let own_carrier = |inner: &str| {
        format!("sort Coll\n    sort C = ?\n    sort Elem = ?\n    operation first(c: C) -> Elem\n    operation pick(c: C) -> Bool =\n      {inner}\n      true\n  end")
    };
    let rows = [
        (
            "unannotated.lambda",
            unannotated("lambda (s: List[T = x.E]) -> true"),
            "(binder-annotation): expected a well-formed type projection, got cannot project 'E' off an abstract receiver",
        ),
        (
            "unannotated.let",
            unannotated("(let z: List[T = x.E] = []\n      true)"),
            "(let-binding): expected a well-formed type projection, got cannot project 'E' off an abstract receiver",
        ),
        (
            "required.lambda",
            required("let h = lambda (s: x.Key) -> true"),
            "(binder-annotation): expected a well-formed type projection, got cannot project 'Key' off an abstract receiver",
        ),
        (
            "required.let",
            required("let z: Option[T = x.Key] = none"),
            "(let-binding): expected a well-formed type projection, got cannot project 'Key' off an abstract receiver",
        ),
        (
            "own_carrier.lambda",
            own_carrier("let h = lambda (e: c.Elem) -> true"),
            "(binder-annotation): expected a well-formed type projection, got cannot project 'Elem' off an abstract receiver",
        ),
        (
            "own_carrier.let",
            own_carrier("let e: c.Elem = first(c)"),
            "(let-binding): expected a well-formed type projection, got cannot project 'Elem' off an abstract receiver",
        ),
    ];
    for (tag, decl, refusal) in rows {
        assert_refused(&program(&format!("wi_sg16k.refused.{tag}"), &decl), refusal, tag);
    }
}

/// CONTROL — passes either way: over an open `E` the binder is the neutral `x.E`, so the program
/// loads, and the body's `n + 1` and the lambda applied to a `List[T = Int64]` are refused
/// against it.
#[test]
fn over_an_open_member_the_binder_stays_the_neutral_it_was() {
    assert_loads(
        &program(
            "wi_sg16k.open",
            "operation k(x: Leaf) -> Bool =\n    let h = lambda (s: List[T = x.E]) -> true\n    true",
        ),
        "`List[T = x.E]` over `x: Leaf`",
    );
    assert_refused(
        &program(
            "wi_sg16k.open.body",
            "operation k(x: Leaf) -> Int64 =
    let h = lambda (s: Option[T = x.E]) -> (match s
        case some(n) -> n + 1
        case none -> 0)
    0",
        ),
        "type mismatch in add.b (op-arg): expected x.E, got Int64",
        "`n + 1` with `n: x.E`",
    );
    assert_refused(
        &program(
            "wi_sg16k.open.apply",
            "operation k(x: Leaf, ys: List[T = Int64]) -> Bool =\n    let h = lambda (s: List[T = x.E]) -> true\n    h(ys)",
        ),
        "type mismatch in h._1 (op-arg): expected List[T = x.E], got List[T = Int64]",
        "`h` applied to a `List[T = Int64]` over an open `E`",
    );
}
