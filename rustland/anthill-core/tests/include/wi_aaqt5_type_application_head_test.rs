//! WI-20260929-AAQT5 — a type application's arguments are read whatever its head is.
//!
//! `check_sort_type_args` returns `Ok` for any head that does not play `Sort`, and both
//! type lowerings — a type position, and a clause's binding value — stopped there. So an
//! application whose head is not a sort was never checked. MEASURED before the fix, each
//! loading clean:
//!
//!     operation h(s: foo[3]) -> Int64 = s.v            `foo` a constructor: `3` dropped
//!     operation h(s: g[3]) -> Int64 = 1                `g` an operation:   `3` dropped
//!     operation f(x: anthill.prelude[Int64]) -> …      a namespace:        `Int64` dropped
//!     operation t(o: Option.some[Int64]) -> …          took a `some("x")`
//!     operation t(o: Option.some[Zork = Int64]) -> …   a type of its own, which no value has
//!
//! and `operation f(x: anthill.prelude.TypeExtractor.TypeVar[name = Int64])` PANICKED in
//! `make_parameterized_type`. The binding position carried the stray positional in a
//! `reflect.SortView` wrapper instead of dropping it, which refused `provides Store[State =
//! foo[3]]` only by accident ("the spec's is `SortView(foo, 3)`") and added a second error
//! about the first to loads that had already failed.
//!
//! THE RULE NOW (kernel-language §5.1, §8.2). The arguments of a type application bind the
//! type parameters of a SORT — the sort applied, or the sort whose CONSTRUCTOR is applied
//! (`Option.some[T = Int64]`, §8.2's parametric variant; positionally `Option.some[Int64]`,
//! in the order the sort declares its parameters). Any other head takes none. An argument
//! with no parameter to bind is refused where it is written, and is not built into the
//! type. What the sort requires of a parameter it requires of its constructor's argument.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! EIGHT PARTS, each backed out PRESENT-BUT-WRONG, APPLIED AND RUN over this file's 24 rows:
//!
//! 1. THE HEAD — `Loader::type_application_keys` stops at a head that does not play `Sort`,
//!    as the gate did (a name kept as written, a positional dropped). 15 FAIL:
//!    [`a_head_that_is_no_sort_takes_no_type_arguments`],
//!    [`a_constructor_of_a_sort_without_parameters_takes_none`],
//!    [`a_constructors_positional_binds_its_sorts_parameter`],
//!    [`a_constructors_positionals_bind_in_declaration_order`],
//!    [`a_constructors_argument_must_name_its_sorts_parameter`],
//!    [`a_constructors_parameter_is_bound_once`],
//!    [`a_constructor_is_over_applied_past_its_sorts_parameters`],
//!    [`a_constructors_sort_is_found_whatever_the_order`],
//!    [`an_alias_of_a_constructor_application_keeps_what_it_fixes`],
//!    [`a_sorts_requirement_reaches_its_constructors_argument`],
//!    [`a_binding_with_a_head_that_takes_none_is_refused_where_written`],
//!    [`a_binding_and_a_signature_read_a_constructors_positional_alike`],
//!    [`an_alias_of_an_application_that_takes_none_is_refused`] — and, BY PANIC in
//!    `make_parameterized_type`, [`a_meta_constructor_application_is_refused_not_a_crash`]
//!    and [`a_meta_constructor_binding_is_refused_not_a_crash`].
//! 2. THE CONSTRUCTOR — `KnowledgeBase::type_arg_owner` answers `None` for a constructor,
//!    so one is a head that takes no argument. 16 FAIL: the fourteen of part 1 that apply a
//!    constructor (all but [`a_head_that_is_no_sort_takes_no_type_arguments`]) — refused,
//!    by the wrong rule — with [`the_named_constructor_argument_is_the_baseline`], §8.2's
//!    own spelling refused, and
//!    [`a_constructors_declaring_scope_is_the_sort_it_is_filed_under`].
//! 3. THE ORDER-FREE OWNER — `type_arg_owner` reads `strict_parent_sort`, the index a sort's
//!    BODY fills as it loads. 4 FAIL: [`a_constructors_sort_is_found_whatever_the_order`]
//!    (a type written above its sort), and three whose sort is written FIRST —
//!    [`a_constructor_of_a_sort_without_parameters_takes_none`] at its entity-field row,
//!    [`an_alias_of_an_application_that_takes_none_is_refused`] and
//!    [`an_alias_of_a_constructor_application_keeps_what_it_fixes`] — because an entity's
//!    field types and an alias's reading are lowered before ANY sort body loads. Each is
//!    told its constructor "takes no type arguments".
//! 4. NOT BUILT — a refused NAME stays in the type, as it did. 5 FAIL:
//!    [`a_refused_name_on_a_sort_adds_no_second_error`],
//!    [`a_constructors_argument_must_name_its_sorts_parameter`] and
//!    [`a_constructors_sort_is_found_whatever_the_order`] (the second error, at the call, is
//!    back), and BY PANIC the two `a_meta_constructor…` rows.
//! 5. THE BARE HEAD — an application none of whose arguments bound goes to the builder
//!    anyway (`parameterized_child`, `assemble_binding_value`). 2 FAIL, BY PANIC: the two
//!    `a_meta_constructor…` rows.
//! 6. THE WRAPPER — a binding's overflow positional rides a `reflect.SortView` again. 3 FAIL:
//!    [`an_over_applied_binding_is_reported_once`],
//!    [`an_over_applied_alias_target_adds_no_error_of_its_own`] and
//!    [`a_binding_with_a_head_that_takes_none_is_refused_where_written`] — each a second
//!    error about the first, printing the wrapper.
//! 7. WHOSE PARAMETERS — `TypeArgProblem::describe` reads a constructor's own (empty)
//!    parameter list instead of its sort's. 8 FAIL, each at its message ("its sort `…`
//!    declares …"): [`a_constructor_of_a_sort_without_parameters_takes_none`],
//!    [`a_constructors_argument_must_name_its_sorts_parameter`],
//!    [`a_constructor_is_over_applied_past_its_sorts_parameters`],
//!    [`a_constructors_sort_is_found_whatever_the_order`],
//!    [`an_alias_of_a_constructor_application_keeps_what_it_fixes`],
//!    [`a_binding_with_a_head_that_takes_none_is_refused_where_written`] and the two
//!    `a_meta_constructor…` rows.
//! 8. THE SITE'S SORT — `Loader::record_type_application_site` records a constructor-headed
//!    application under the constructor, as both lowerings did. 1 FAILS:
//!    [`a_sorts_requirement_reaches_its_constructors_argument`] (`Dict.dict[K = Float]`,
//!    `Dict.dict[Float]` and the binding load clean; the sort-head control still refuses).
//!
//! PASS UNDER EVERY BACK-OUT, by design: [`an_unresolved_head_is_reported_once`],
//! [`a_sort_head_reads_as_it_did`], [`a_free_standing_entity_is_its_own_sort`] — what the
//! check already did, pinned so the rows above are read against it — and
//! [`the_fit_is_answered_per_argument`], which drives `fit_type_args` itself and which no
//! part above touches. [`the_named_constructor_argument_is_the_baseline`] and
//! [`a_constructors_declaring_scope_is_the_sort_it_is_filed_under`] pass under every part
//! but 2: the first is `wi_jsfhg_variant_type_is_inhabited_test`'s row, and the second
//! compares two relations that part 3 makes one.
//!
//! NOT A PART, because no row can tell: `typing::sort_application` lost its `SortView` arm
//! (nothing lowers a binding to that wrapper any more, so the arm had no input), and the
//! type position's carrier split became `typing::parameterized_value` (the same split —
//! the existing suite is its guard).
//!
//! NOT COVERED HERE, and why. The SPEC of a clause is a third lowering (`sort_inst_to_value`)
//! with its own argument grammar — operation bindings, the WI-407 carrier slot — and
//! `provides g` loads clean for an operation `g` with or without a bracket, where `requires
//! g` is refused (WI-993): a provision naming no sort, which is not an argument question
//! (WI-20261005-GD7HQ). A bracket in a TERM position (`convert_term`, the rule-body walk,
//! the typer's value arm) still gates on a `Sort` head, where a bracket on another head is
//! a call's or a predicate's. A rule head's sigil-free bound takes that path too, at the
//! one depth it does not check: `rule p(x: Buf[W = Int64]) :- true` loads — and its clause
//! matches nothing — where `?x: Buf[W = Int64]` is refused (WI-20261005-BHCVT).

use crate::common::{assert_refused_naming, load_errors_of, run_int64, try_load_kb_with_files};
use anthill_core::kb::{KnowledgeBase, TypeArgProblem};

/// `Buf[T, N]` with its constructor `buf`, `Foo` (no parameters) with `foo`, the spec
/// `Store` whose `State` the provisions bind, and an operation `g`. `body` follows.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, Option}}
  import anthill.prelude.Option.{{some}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Foo
    entity foo(v: Int64)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end

  entity Rec(v: Int64)

  operation g(x: Int64) -> Int64 = x
{body}
end
"#
    )
}

/// The refusals of `program(ns, body)`.
fn errors(ns: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(ns, body))
}

/// `errors`, which must be exactly ONE, naming every token: the refusal where the
/// application is written and nothing after it.
fn the_one_refusal(ns: &str, body: &str, tokens: &[&str]) {
    let errs = errors(ns, body);
    assert_refused_naming(&errs, tokens, body);
    assert_eq!(errs.len(), 1, "{body}: one refusal, where it is written; got {errs:#?}");
}

/// `takeSome(o: {ty})` called with `arg`, as `ns.go()`.
fn take_some(ns: &str, ty: &str, arg: &str) -> Result<i64, String> {
    let body = format!(
        "  operation takeSome(o: {ty}) -> Int64 = 21\n  operation go() -> Int64 = takeSome({arg})"
    );
    run_int64(&program(ns, &body), &format!("{ns}.go"))
}

// ── a head that is neither a sort nor a constructor ───────────────────────────────────

/// AN OPERATION, A NAMESPACE, A PARAMETER, A CONSTANT: none has a type parameter, so a type
/// argument applied to one is refused, naming what the head is. Each loaded clean with the
/// argument dropped.
#[test]
fn a_head_that_is_no_sort_takes_no_type_arguments() {
    for (case, body, head, kind) in [
        ("op", "  operation h(s: g[3]) -> Int64 = 1", "wiaaqt5.none.op.g", "Operation"),
        (
            "ns",
            "  operation h(x: anthill.prelude[Int64]) -> Int64 = 1",
            "anthill.prelude",
            "Namespace",
        ),
        (
            "param",
            "  operation h(a: Int64, s: a[Int64]) -> Int64 = 1",
            "wiaaqt5.none.param.h.a",
            "Param",
        ),
        (
            "konst",
            "  const K: Int64 = 3\n  operation h(s: K[Int64]) -> Int64 = 1",
            "wiaaqt5.none.konst.K",
            "Const",
        ),
    ] {
        the_one_refusal(
            &format!("wiaaqt5.none.{case}"),
            body,
            &[
                "invalid type argument",
                &format!("`{head}` takes no type arguments"),
                &format!("a declaration of kind {kind}"),
            ],
        );
    }
}

// ── a constructor: its arguments bind its sort's parameters ──────────────────────────

/// THE TICKET'S FIRST PROGRAM. `foo` is a constructor of `Foo`, which declares no
/// parameters, so `foo[3]` is over-applied — said of the constructor, naming its sort — in
/// every position a type is written: a parameter, a return, an entity field, and nested in
/// another application.
#[test]
fn a_constructor_of_a_sort_without_parameters_takes_none() {
    for (case, body) in [
        ("param", "  operation h(s: foo[3]) -> Int64 = s.v"),
        ("ret", "  operation h(n: Int64) -> foo[3] = foo(v: n)"),
        ("field", "  entity Holder(f: foo[3])"),
        ("nested", "  operation h(s: Buf[T = foo[3]]) -> Int64 = 1"),
    ] {
        let ns = format!("wiaaqt5.plain.{case}");
        the_one_refusal(
            &ns,
            body,
            &[
                &format!("`{ns}.Foo.foo` is over-applied: 1 positional type argument(s)"),
                &format!("its sort `{ns}.Foo` declares no type parameters"),
            ],
        );
    }
}

/// THE BASELINE, §8.2's own spelling: `Option.some[T = Int64]` takes a `some(1)` and refuses
/// a `some("x")`. It is `wi_jsfhg_variant_type_is_inhabited_test`'s; here so the positional
/// row below is read against it.
#[test]
fn the_named_constructor_argument_is_the_baseline() {
    let ty = "Option.some[T = Int64]";
    assert_eq!(take_some("wiaaqt5.named.ok", ty, "some(1)"), Ok(21));
    let refused = take_some("wiaaqt5.named.bad", ty, "some(\"x\")").unwrap_err();
    assert!(
        refused.contains("expected some[T = Int64], got some[T = String]"),
        "{refused}"
    );
}

/// THE POSITIONAL SPELLING IS THE SAME TYPE. `Option.some[Int64]` binds `Option`'s `T`, so
/// the call that fits runs and the one that does not is refused with the named spelling's
/// own message. Was: `Int64` dropped, the parameter typed at the bare `some`, and
/// `takeSome(some("x"))` answered 21.
#[test]
fn a_constructors_positional_binds_its_sorts_parameter() {
    let ty = "Option.some[Int64]";
    assert_eq!(take_some("wiaaqt5.pos.ok", ty, "some(1)"), Ok(21));
    let refused = take_some("wiaaqt5.pos.bad", ty, "some(\"x\")").unwrap_err();
    assert!(
        refused.contains("expected some[T = Int64], got some[T = String]"),
        "`Option.some[Int64]` is `Option.some[T = Int64]`: {refused}"
    );
}

/// IN THE ORDER THE SORT DECLARES THEM (§5.1), and a positional skips what a name took.
/// `Buf` declares `T` then `N`: `Buf.buf[Int64]` binds `T`; `Buf.buf[N = 3, Int64]` still
/// binds `T`, the name having taken `N`. Each takes a `buf` of `Int64` and reads its field,
/// and refuses a `buf` of `String` naming `T`. `Buf.buf[Int64]` is the ticket's third
/// program.
#[test]
fn a_constructors_positionals_bind_in_declaration_order() {
    for (case, ty) in [("first", "Buf.buf[Int64]"), ("skip", "Buf.buf[N = 3, Int64]")] {
        let ns = format!("wiaaqt5.order.{case}");
        let body = |arg: &str| {
            format!(
                "  operation h(s: {ty}) -> Int64 = s.v\n  operation go() -> Int64 = h(buf(v: {arg}))"
            )
        };
        assert_eq!(
            run_int64(&program(&ns, &body("7")), &format!("{ns}.go")),
            Ok(7),
            "{ty}"
        );
        let refused = run_int64(&program(&ns, &body("\"x\"")), &format!("{ns}.go")).unwrap_err();
        assert!(
            refused.contains("T = Int64") && refused.contains("got buf[T = String"),
            "{ty} binds `T`: {refused}"
        );
    }
}

/// A NAME THE SORT DOES NOT DECLARE is refused, naming the sort whose parameters they are.
/// Was: `Option.some[Zork = Int64]` was a type of its own, refused only at a call and only
/// as a mismatch (`expected some[Zork = Int64], got some[T = String]`). The call is here to
/// show nothing follows the refusal.
#[test]
fn a_constructors_argument_must_name_its_sorts_parameter() {
    the_one_refusal(
        "wiaaqt5.zork",
        "  operation takeSome(o: Option.some[Zork = Int64]) -> Int64 = 21\n  \
         operation go() -> Int64 = takeSome(some(\"x\"))",
        &[
            "`anthill.prelude.Option.some` has no type parameter named 'Zork'",
            "its sort `anthill.prelude.Option` declares type parameter(s) T",
        ],
    );
}

/// A PARAMETER BOUND TWICE is refused, and the type keeps the FIRST binding: a `some(1)`
/// then fits it. Was: no refusal, and the type read its first binding twice (`some[T =
/// Int64, T = Int64]`).
#[test]
fn a_constructors_parameter_is_bound_once() {
    the_one_refusal(
        "wiaaqt5.twice",
        "  operation takeSome(o: Option.some[T = Int64, T = String]) -> Int64 = 21\n  \
         operation go() -> Int64 = takeSome(some(1))",
        &["`anthill.prelude.Option.some` binds the type parameter 'T' more than once"],
    );
}

/// A POSITIONAL PAST THE SORT'S PARAMETERS is an over-application. Was: both dropped.
#[test]
fn a_constructor_is_over_applied_past_its_sorts_parameters() {
    the_one_refusal(
        "wiaaqt5.over",
        "  operation takeSome(o: Option.some[Int64, String]) -> Int64 = 21",
        &[
            "`anthill.prelude.Option.some` is over-applied: 2 positional type argument(s) but \
             only 1 declared type parameter(s) left to bind",
            "its sort `anthill.prelude.Option` declares type parameter(s) T",
        ],
    );
}

/// THE CONSTRUCTOR'S SORT IS KNOWN BEFORE ITS BODY LOADS. A type written ABOVE the sort it
/// names — and one in a file loaded BEFORE the sort's — reads the constructor's parameters
/// as one written below does: the positional binds, the stray name is refused naming the
/// sort. The parent index `strict_parent_sort` reads is filled as each sort's body loads,
/// so asking it here answers "no sort" for exactly these.
#[test]
fn a_constructors_sort_is_found_whatever_the_order() {
    let late = "  sort Late\n    sort T = ?\n    entity late(v: T)\n  end\n";
    let one_file = |ns: &str, ty: &str| {
        format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64}}\n  \
             operation h(s: Late.late[{ty}]) -> Int64 = s.v\n{late}  \
             operation go() -> Int64 = h(late(v: 7))\nend\n"
        )
    };
    assert_eq!(
        run_int64(&one_file("wiaaqt5.above.ok", "Int64"), "wiaaqt5.above.ok.go"),
        Ok(7),
        "a constructor applied above its sort"
    );
    let errs = load_errors_of(&one_file("wiaaqt5.above.bad", "Zork = Int64"));
    assert_refused_naming(
        &errs,
        &[
            "`wiaaqt5.above.bad.Late.late` has no type parameter named 'Zork'",
            "its sort `wiaaqt5.above.bad.Late` declares type parameter(s) T",
        ],
        "a stray name on a constructor applied above its sort",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");

    // Two files, the one that USES the constructor loaded first.
    let user = "namespace wiaaqt5.above.files.user\n  import anthill.prelude.{Int64}\n  \
                import wiaaqt5.above.files.decl.{Late}\n  \
                operation h(s: Late.late[Zork = Int64]) -> Int64 = 1\nend\n";
    let decl = format!("namespace wiaaqt5.above.files.decl\n{late}end\n");
    let errs = try_load_kb_with_files(&[user, decl.as_str()])
        .err()
        .unwrap_or_default();
    assert_refused_naming(
        &errs,
        &[
            "`wiaaqt5.above.files.decl.Late.late` has no type parameter named 'Zork'",
            "its sort `wiaaqt5.above.files.decl.Late` declares type parameter(s) T",
        ],
        "a stray name on a constructor applied in a file loaded before its sort's",
    );
    assert_eq!(errs.len(), 1, "{errs:#?}");
}

/// AN ALIAS OF A CONSTRUCTOR APPLICATION, APPLIED FURTHER (WI-20260924-SNJPR's rule, on a
/// constructor). What the alias fixes is GIVEN: `IntBuf[3]` over `sort IntBuf = Buf.buf[T =
/// Int64]` binds the sort's NEXT parameter, `N`, and keeps `T` — a `buf` of `Int64` fits
/// and one of `String` does not; a second positional has no parameter left; and a name may
/// not bind `T` again.
#[test]
fn an_alias_of_a_constructor_application_keeps_what_it_fixes() {
    let body = |ty: &str, arg: &str| {
        format!(
            "  sort IntBuf = Buf.buf[T = Int64]\n  operation h(s: {ty}) -> Int64 = s.v\n  \
             operation go() -> Int64 = h(buf(v: {arg}))"
        )
    };
    let run = |ns: &str, ty: &str, arg: &str| {
        run_int64(&program(ns, &body(ty, arg)), &format!("{ns}.go"))
    };
    assert_eq!(run("wiaaqt5.given.ok", "IntBuf[3]", "7"), Ok(7));
    let refused = run("wiaaqt5.given.bad", "IntBuf[3]", "\"x\"").unwrap_err();
    assert!(
        refused.contains("T = Int64") && refused.contains("got buf[T = String"),
        "the alias's `T` stands: {refused}"
    );
    the_one_refusal(
        "wiaaqt5.given.over",
        &body("IntBuf[3, Bool]", "7"),
        &[
            "`wiaaqt5.given.over.Buf.buf` is over-applied: 2 positional type argument(s) but \
             only 1 declared type parameter(s) left to bind",
            "its sort `wiaaqt5.given.over.Buf` declares type parameter(s) T, N",
        ],
    );
    assert_refused_naming(
        &errors("wiaaqt5.given.again", &body("IntBuf[T = Bool]", "7")),
        &["already binds `T` to `Int64`, which the application binds again"],
        "IntBuf[T = Bool]",
    );
}

/// `Dict[K]`, which requires `Eq` of its key, with its constructor `dict`; `body` follows.
fn keyed(ns: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Float, Eq}}\n  \
         sort Dict\n    sort K = ?\n    requires Eq[T = K]\n    entity dict(k: K)\n  end\n  \
         sort Store\n    sort State = ?\n  end\n{body}\nend\n"
    )
}

/// WHAT THE SORT REQUIRES OF A PARAMETER, IT REQUIRES OF ITS CONSTRUCTOR'S ARGUMENT. `Dict`
/// requires `Eq` at `K`, and `Float` is no lawful key: `Dict[K = Float]` is refused
/// (WI-835), and so is the constructor applied at it, by name or by position, in a type
/// and in a clause's binding. The use-site check reads the application the lowering
/// RECORDS, and a constructor-headed one was recorded under the constructor — which
/// requires nothing — so `Dict.dict[K = Float]` loaded clean. A lawful key still loads,
/// and the constructor's value flows through the type.
#[test]
fn a_sorts_requirement_reaches_its_constructors_argument() {
    let unlawful = |ns: &str| {
        vec![
            format!("'{ns}.Dict' requires `anthill.prelude.Eq` at its parameter `K`"),
            "`K = anthill.prelude.Float`".to_string(),
        ]
    };
    for (case, body) in [
        // THE CONTROL — the sort itself, WI-835's own row: refused before and after.
        ("sort", "  operation m(d: Dict[K = Float]) -> Int64 = 1"),
        ("named", "  operation m(d: Dict.dict[K = Float]) -> Int64 = 1"),
        ("positional", "  operation m(d: Dict.dict[Float]) -> Int64 = 1"),
        (
            "binding",
            "  sort Carrier\n    provides Store[State = Dict.dict[Float]]\n  end",
        ),
    ] {
        let ns = format!("wiaaqt5.keyed.{case}");
        let errs = load_errors_of(&keyed(&ns, body));
        let tokens = unlawful(&ns);
        let tokens: Vec<&str> = tokens.iter().map(String::as_str).collect();
        assert_refused_naming(&errs, &tokens, body);
        assert_eq!(errs.len(), 1, "{body}: {errs:#?}");
    }
    let lawful = "  operation m(d: Dict.dict[Int64]) -> Int64 = d.k\n  \
                  operation go() -> Int64 = m(dict(k: 7))";
    assert_eq!(
        run_int64(&keyed("wiaaqt5.keyed.ok", lawful), "wiaaqt5.keyed.ok.go"),
        Ok(7),
        "a lawful key"
    );
}

/// THE TWO READINGS OF "WHICH SORT IS THIS A CONSTRUCTOR OF" AGREE. `type_arg_owner` reads
/// the scope a constructor was DECLARED in, because the index `strict_parent_sort` reads is
/// filled only as each sort's body loads; once everything has loaded they are one relation,
/// for every constructor of the standard library and this file's fixture. A constructor
/// filed under one sort and declared in another would bind one sort's parameters here
/// while the typer classified its values at the other's.
#[test]
fn a_constructors_declaring_scope_is_the_sort_it_is_filed_under() {
    let kb = crate::common::load_kb_with(&program("wiaaqt5.filed", ""));
    let constructors: Vec<_> = kb.entity_field_type_functors().copied().collect();
    let mut checked = 0;
    for ctor in constructors {
        let Some(sort) = kb.strict_parent_sort(ctor) else {
            continue;
        };
        assert_eq!(
            kb.type_arg_owner(ctor).map(|s| kb.qualified_name_of(s).to_owned()),
            Some(kb.qualified_name_of(sort).to_owned()),
            "the sort whose parameters `{}` takes",
            kb.qualified_name_of(ctor)
        );
        checked += 1;
    }
    assert!(
        checked > 100,
        "the standard library declares well over a hundred constructors; only {checked} were \
         compared — the walk is not reaching them"
    );
}

// ── an argument that binds nothing is not built ───────────────────────────────────────

/// A REFUSED NAME DOES NOT STAY IN THE TYPE. `Buf[W = Int64]` is refused, and the parameter
/// is typed at `Buf`: the call beside it is not a second error. Was two — `expected Buf[W =
/// Int64], got Buf[T = Int64, N = ??_]` at the call, about a type the first error had
/// already refused.
#[test]
fn a_refused_name_on_a_sort_adds_no_second_error() {
    the_one_refusal(
        "wiaaqt5.stray",
        "  operation h(s: Buf[W = Int64]) -> Int64 = 1\n  operation go() -> Int64 = h(buf(v: 1))",
        &["`wiaaqt5.stray.Buf` has no type parameter named 'W'", "it declares type parameter(s) T, N"],
    );
}

/// THE TICKET'S ADDENDUM. `TypeExtractor.TypeVar` is a constructor of the type
/// meta-language's sort, which declares no parameters — so `name = Int64` names none and a
/// positional has none to take. Refused where written. Was a PANIC in
/// `make_parameterized_type` (and, for one build of WI-20260924-F3FYJ, a clean load typing
/// the parameter as a forged type variable named `Int64`).
#[test]
fn a_meta_constructor_application_is_refused_not_a_crash() {
    let ty = "anthill.prelude.TypeExtractor.TypeVar";
    let sort = "its sort `anthill.prelude.TypeExtractor` declares no type parameters";
    the_one_refusal(
        "wiaaqt5.meta.named",
        &format!("  operation f(x: {ty}[name = Int64]) -> Int64 = 1"),
        &[&format!("`{ty}` has no type parameter named 'name'"), sort],
    );
    the_one_refusal(
        "wiaaqt5.meta.pos",
        &format!("  operation f(x: {ty}[Int64]) -> Int64 = 1"),
        &[&format!("`{ty}` is over-applied"), sort],
    );
}

// ── a clause's binding value reads the same ───────────────────────────────────────────

/// A carrier providing `Store` at `State = {state}`, its member `peek` taking `peek_ty`.
fn carrier(state: &str, peek_ty: &str) -> String {
    format!(
        "  sort Carrier\n    provides Store[State = {state}]\n    \
         operation peek(s: {peek_ty}) -> Int64 = 1\n  end"
    )
}

/// THE BINDING POSITION REFUSES WHERE IT IS WRITTEN. `Store[State = foo[3]]` was refused
/// only by accident — the stray `3` rode a `reflect.SortView` wrapper into the member-fit
/// check, which printed it ("parameter 1 is `Foo` where the spec's is `SortView(foo, 3)`").
/// It is the over-application it is in a signature, and the member that fits `foo` is no
/// second error. An operation head takes no argument here either.
#[test]
fn a_binding_with_a_head_that_takes_none_is_refused_where_written() {
    the_one_refusal(
        "wiaaqt5.bind.ctor",
        &carrier("foo[3]", "Foo"),
        &[
            "`wiaaqt5.bind.ctor.Foo.foo` is over-applied",
            "its sort `wiaaqt5.bind.ctor.Foo` declares no type parameters",
        ],
    );
    let errs = errors("wiaaqt5.bind.op", &carrier("g[3]", "Int64"));
    assert_refused_naming(
        &errs,
        &["`wiaaqt5.bind.op.g` takes no type arguments", "a declaration of kind Operation"],
        "State = g[3]",
    );
    assert!(
        !errs.iter().any(|e| e.contains("SortView")),
        "no refusal prints the wrapper: {errs:#?}"
    );
}

/// A SORT-HEAD OVER-APPLICATION IS REPORTED ONCE. The member takes exactly the `Buf[Int64,
/// 3]` the binding is once its third argument is refused. Was two: the over-application,
/// then "its own member 'peek' does not fit … where the spec's is `SortView(Buf, Bool)[T =
/// Int64, N = 3]`".
#[test]
fn an_over_applied_binding_is_reported_once() {
    the_one_refusal(
        "wiaaqt5.bind.over",
        &carrier("Buf[Int64, 3, Bool]", "Buf[Int64, 3]"),
        &[
            "`wiaaqt5.bind.over.Buf` is over-applied: 3 positional type argument(s) but only 2",
            "it declares type parameter(s) T, N",
        ],
    );
}

/// A spec `One[A]`, an alias `X` of it at `target`, and a carrier providing `X`.
fn aliased(target: &str) -> String {
    format!(
        "  sort Wis\n    entity wis(n: Int64)\n  end\n  \
         sort One\n    sort A = ?\n    operation one(a: A) -> Int64\n  end\n  \
         sort X = {target}\n  \
         sort Carrier\n    provides X\n    operation one(a: Wis) -> Int64 = 4\n  end\n  \
         operation go() -> Int64 = One.one(wis(n: 1))"
    )
}

/// AN OVER-APPLIED ALIAS TARGET IS ONE ERROR, at the alias. The alias's recorded reading is
/// lowered the way a binding is, so it took the wrapper too, and `provides X` then reported
/// that `X` "stands for `SortView(One, Bool)[A = Wis]`, which is not a sort". The control
/// is the alias that fits: it loads, and the spec operation dispatches through it.
#[test]
fn an_over_applied_alias_target_adds_no_error_of_its_own() {
    assert_eq!(
        run_int64(&program("wiaaqt5.alias.ok", &aliased("One[Wis]")), "wiaaqt5.alias.ok.go"),
        Ok(4),
        "the alias that fits"
    );
    the_one_refusal(
        "wiaaqt5.alias.over",
        &aliased("One[Wis, Bool]"),
        &["`wiaaqt5.alias.over.One` is over-applied: 2 positional type argument(s) but only 1"],
    );
}

/// A BINDING AND A SIGNATURE READ A CONSTRUCTOR'S POSITIONAL ALIKE. The binding `State =
/// Option.some[Int64]` is the type a member writes `Option.some[T = Int64]`: that member
/// fits, and one at `String` is refused naming both types. Was: the positional rode the
/// wrapper, so the member that fits was refused ("where the spec's is `SortView(some,
/// Int64)`") and so was every other.
#[test]
fn a_binding_and_a_signature_read_a_constructors_positional_alike() {
    let state = "Option.some[Int64]";
    let fits = errors("wiaaqt5.bind.some.ok", &carrier(state, "Option.some[T = Int64]"));
    assert!(fits.is_empty(), "the member at the binding's own type fits: {fits:#?}");
    assert_refused_naming(
        &errors("wiaaqt5.bind.some.bad", &carrier(state, "Option.some[T = String]")),
        &[
            "its own member 'peek' does not fit",
            "parameter 1 is `some[T = String]` where the spec's is `some[T = Int64]`",
        ],
        "a member at another argument of the constructor",
    );
}

/// THE ADDENDUM, in a binding: refused where written, not a crash, and no wrapper.
#[test]
fn a_meta_constructor_binding_is_refused_not_a_crash() {
    let errs = errors(
        "wiaaqt5.bind.meta",
        "  sort Carrier\n    \
         provides Store[State = anthill.prelude.TypeExtractor.TypeVar[name = Int64]]\n  end",
    );
    assert_refused_naming(
        &errs,
        &[
            "`anthill.prelude.TypeExtractor.TypeVar` has no type parameter named 'name'",
            "its sort `anthill.prelude.TypeExtractor` declares no type parameters",
        ],
        "State = TypeExtractor.TypeVar[name = Int64]",
    );
    assert!(
        !errs.iter().any(|e| e.contains("SortView")),
        "no refusal prints the wrapper: {errs:#?}"
    );
}

/// AN ALIAS OF SUCH AN APPLICATION is refused at its declaration — once, though a
/// declaration is lowered twice (as a type, and again as the reading a spec clause takes).
/// Was a clean load.
#[test]
fn an_alias_of_an_application_that_takes_none_is_refused() {
    the_one_refusal(
        "wiaaqt5.alias.ctor",
        "  sort X = foo[3]",
        &["`wiaaqt5.alias.ctor.Foo.foo` is over-applied"],
    );
}

// ── controls: what the check already did ──────────────────────────────────────────────

/// AN UNRESOLVED HEAD is reported by the resolver and by nothing else: nothing is known of
/// its parameters, so its arguments are not judged.
#[test]
fn an_unresolved_head_is_reported_once() {
    the_one_refusal(
        "wiaaqt5.unresolved",
        "  operation f(x: Zork[Int64, K = Bool]) -> Int64 = 1",
        &["unresolved name 'Zork'"],
    );
}

/// A SORT HEAD reads as it did, in the words it did: "it declares", not "its sort".
#[test]
fn a_sort_head_reads_as_it_did() {
    the_one_refusal(
        "wiaaqt5.sort",
        "  operation f(x: Buf[Int64, 3, Bool]) -> Int64 = 1",
        &[
            "`wiaaqt5.sort.Buf` is over-applied: 3 positional type argument(s) but only 2 \
             declared type parameter(s) left to bind — it declares type parameter(s) T, N",
        ],
    );
}

/// A FREE-STANDING ENTITY is its own sort (§6.3), not a constructor of another: it answers
/// for itself.
#[test]
fn a_free_standing_entity_is_its_own_sort() {
    the_one_refusal(
        "wiaaqt5.rec",
        "  operation f(x: Rec[3]) -> Int64 = 1",
        &["`wiaaqt5.rec.Rec` is over-applied", "— it declares no type parameters"],
    );
}

// ── the rule itself ───────────────────────────────────────────────────────────────────

/// `fit_type_args` answers PER ARGUMENT, in source order: which declared parameter each
/// written argument binds, `None` for one that binds nothing, and the first that does not
/// fit. A positional takes the next parameter no NAME took, wherever among the names it is
/// written; a parameter an alias has `given` is bound already.
#[test]
fn the_fit_is_answered_per_argument() {
    let mut kb = KnowledgeBase::new();
    let declared = vec!["K".to_string(), "V".to_string()];
    let k = kb.intern("K");
    let v = kb.intern("V");
    let w = kb.intern("W");
    let fit = |given: &[_], written: &[_]| {
        let fit = kb.fit_type_args(&declared, given, written);
        (fit.slots.to_vec(), fit.problem)
    };

    // `[String, Int64]` — in declaration order.
    assert_eq!(fit(&[], &[None, None]), (vec![Some(0), Some(1)], None));
    // `[Int64, K = String]` — the positional skips the `K` a LATER name takes.
    assert_eq!(fit(&[], &[None, Some(k)]), (vec![Some(1), Some(0)], None));
    // `[W = …, V = …]` — the undeclared name binds nothing, the declared one binds.
    assert_eq!(
        fit(&[], &[Some(w), Some(v)]),
        (
            vec![None, Some(1)],
            Some(TypeArgProblem::UndeclaredParam { param: "W".into() })
        )
    );
    // `[K = …, K = …, …, …]` — the first `K` binds, the second does not; the first
    // positional takes `V`, the second has no parameter left. The FIRST problem is reported.
    assert_eq!(
        fit(&[], &[Some(k), Some(k), None, None]),
        (
            vec![Some(0), None, Some(1), None],
            Some(TypeArgProblem::DuplicateParam { param: "K".into() })
        )
    );
    // `[…, …, …]` — an over-application alone.
    assert_eq!(
        fit(&[], &[None, None, None]),
        (
            vec![Some(0), Some(1), None],
            Some(TypeArgProblem::ExcessPositional { given: 3, free: 2 })
        )
    );
    // An alias has given `K`: a positional takes `V`, and a name may not bind `K` again.
    assert_eq!(fit(&[k], &[None]), (vec![Some(1)], None));
    assert_eq!(
        fit(&[k], &[Some(k)]),
        (vec![None], Some(TypeArgProblem::DuplicateParam { param: "K".into() }))
    );
}
