//! WI-20260824-PAPX0 — a dot on a receiver that denotes a sort (proposal 055 umbrella A
//! step 4, `docs/design/055-implementation.md` §4).
//!
//! THE RULE. A receiver that denotes a sort — a written type, or a name a `let` bound to
//! one — takes `.m(…)` as the call the written `Sort[…].m(…)` makes: `m` is looked up
//! among that sort's operations and constructors, the arguments are the call's as
//! written, and the bracket binds the sort's parameters. The members of `Type` itself are
//! not reached through such a receiver. So one type value gives one answer in every
//! spelling:
//!
//!   Box[V = Int64].tag()      (Box[V = Int64]).tag()      let t = Box[V = Int64]; t.tag()
//!
//! A `Type` that denotes nothing known at the dot — a parameter, a call's result — is a
//! value, and its dot is `Type`'s.
//!
//! EVERY ROW HAS ITS OWN SOURCE. A row that shares a fixture with a row that stops
//! loading measures the fixture: the whole KB fails and the surviving row cannot be
//! called either.
//!
//! CONTROLS — measured, each piece of the change backed out on its own:
//!
//!   the rung (`denoted_sort_dot` answering `NotDenoting` always) — FAIL:
//!     a_let_bound_type_receiver_resolves_in_the_denoted_sort
//!     the_denoted_sorts_type_arguments_ride_the_call
//!     a_missing_member_is_refused_about_the_denoted_sort
//!     an_alias_hop_keeps_the_denotation
//!     a_member_of_type_is_not_reached_through_a_denoting_receiver
//!     eq_is_refused_on_a_denoting_receiver_and_the_named_call_answers
//!     a_member_on_both_the_sort_and_type_is_the_sorts
//!     a_receiver_denoting_type_itself_is_types_own_call
//!     a_member_taking_values_of_the_sort_is_called_as_written
//!     a_positional_bracket_binds_the_next_parameter
//!     a_nested_positional_bracket_is_named_too
//!     a_constructor_is_reached_through_a_let_bound_type
//!     a_bracket_on_a_constructor_binds_in_both_spellings
//!     a_type_parameter_in_the_bracket_is_that_parameter
//!     a_parenthesized_type_is_a_receiver
//!     an_alias_denotes_what_it_stands_for
//!     a_declaration_that_is_no_call_is_refused_truthfully
//!     an_internal_member_is_hidden_as_its_written_name_is
//!     a_constant_in_the_bracket_is_part_of_the_denoted_type
//!     a_spec_is_denoted_as_any_sort_is
//!     a_lambda_under_the_binding_sees_the_denotation
//!   naming the bracket's arguments (`type_value_denoted_type` replaced by the node's
//!   term twin) — FAIL:
//!     a_positional_bracket_binds_the_next_parameter
//!     a_nested_positional_bracket_is_named_too
//!     a_type_parameter_in_the_bracket_is_that_parameter
//!   its arm for an argument that is not a nominal type (answering `None`) — FAIL:
//!     a_constant_in_the_bracket_is_part_of_the_denoted_type
//!   the constructor arm — FAIL:
//!     a_constructor_is_reached_through_a_let_bound_type
//!     a_bracket_on_a_constructor_binds_in_both_spellings
//!     an_alias_denotes_what_it_stands_for (its constructor case)
//!   the alias read, and separately its "owns no members" clause — FAIL:
//!     an_alias_denotes_what_it_stands_for
//!   the visibility check — FAIL:
//!     an_internal_member_is_hidden_as_its_written_name_is
//!   the converter's parenthesized receiver — FAIL:
//!     a_parenthesized_type_is_a_receiver
//!     a_parenthesized_value_is_a_receiver
//!
//!   PASS UNDER EVERY BACK-OUT, by design — they are the fences:
//!     the_written_spellings_are_unchanged — neither reaches the typer's dot frame.
//!     a_shadowing_rebind_drops_the_denotation — without the rung nothing resolves in
//!       `Box` anyway. It does not drive `clear_type_denotation` either: `let t = 1`
//!       mints a fresh binder symbol, so the map, keyed by symbol, never collides.
//!     a_type_that_denotes_nothing_here_is_a_value — the boundary: a parameter and a
//!       call's result keep `Type`'s own dot.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The sort every row is about, indented for a namespace body.
const BOX: &str = r#"
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
    operation wrap(x: V) -> V = x
    operation combine(a: Box[V], b: Box[V]) -> Int64 = 1
    operation count(b: Box) -> Int64 = 3
    operation unbox(b: Box[V]) -> V = match b
      case mk(v) -> v
  end
"#;

/// A namespace `test.<ns>` holding [`BOX`] and `body`, preceded by `prefix` (a reopening
/// of `anthill.prelude.Type`, for the rows that give `Type` a member).
fn source(ns: &str, prefix: &str, body: &str) -> String {
    format!(
        "{prefix}\nnamespace test.{ns}\n  import anthill.prelude.{{Type, Bool}}\n{BOX}\n{body}\nend\n"
    )
}

/// Load, call `test.<ns>.go()`, and hand back its value.
fn run(ns: &str, prefix: &str, body: &str) -> Value {
    let mut interp = interp_for(&source(ns, prefix, body));
    interp
        .call(&format!("test.{ns}.go"), &[])
        .unwrap_or_else(|e| panic!("{ns}: {e:?}"))
}

fn run_int(ns: &str, prefix: &str, body: &str) -> i64 {
    match run(ns, prefix, body) {
        Value::Int(n) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, prefix: &str, body: &str) -> String {
    let errs = try_load_kb_with(&source(ns, prefix, body))
        .err()
        .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
    format!("{errs:?}")
}

/// `Type` reopened with a member that takes the type value.
const TYPE_TAG: &str = r#"
namespace anthill.prelude
  sort Type
    operation tag(t: Type) -> Int64 = 99
  end
end
"#;

// ── the rule ────────────────────────────────────────────────────────────────

/// The row the ticket was opened for. Before the rung this did not load.
#[test]
fn a_let_bound_type_receiver_resolves_in_the_denoted_sort() {
    let got = run_int(
        "papx0",
        "",
        "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.tag()",
    );
    assert_eq!(got, 7, "`t.tag()` with `t` denoting Box is Box's `tag`");
}

/// The denotation is the instantiation, not the head alone: the member's signature is
/// read at the receiver's bindings. Driven both ways — the value comes back, and a
/// wrong-typed argument is refused at `Int64` rather than unifying with a free `V`.
#[test]
fn the_denoted_sorts_type_arguments_ride_the_call() {
    assert_eq!(
        run_int(
            "papx0args",
            "",
            "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.wrap(5)",
        ),
        5
    );
    let rendered = refusal(
        "papx0argsbad",
        "",
        "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.wrap(\"s\")",
    );
    // The site, not just the two type names: with the bindings dropped the refusal is
    // `go.return (op-return): expected Int64, got String`, which holds both names too.
    assert!(
        rendered.contains("wrap.x") && rendered.contains("op-arg"),
        "the refusal must land on the argument, not the return: {rendered}"
    );
    assert!(
        rendered.contains("expected Int64") && rendered.contains("got String"),
        "the receiver's V = Int64 must reach the argument check: {rendered}"
    );
}

/// A member the denoted sort does not declare is refused about THAT sort.
#[test]
fn a_missing_member_is_refused_about_the_denoted_sort() {
    let rendered = refusal(
        "papx0miss",
        "",
        "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.nosuch()",
    );
    assert!(
        rendered.contains("papx0miss.Box.nosuch") && rendered.contains("no such member"),
        "the refusal must name the denoted sort: {rendered}"
    );
    assert!(
        !rendered.contains("prelude.Type"),
        "and not the `Type` handle: {rendered}"
    );
}

/// `let u = t` keeps what `t` denotes.
#[test]
fn an_alias_hop_keeps_the_denotation() {
    let got = run_int(
        "papx0hop",
        "",
        "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    let u = t\n    u.tag()",
    );
    assert_eq!(got, 7);
}

// ── `Type`'s own members ────────────────────────────────────────────────────

/// A member declared on `Type` and not on the denoted sort is not an answer. The refusal
/// names both, and the spelling it advises is run.
#[test]
fn a_member_of_type_is_not_reached_through_a_denoting_receiver() {
    const ONLY_ON_TYPE: &str = r#"
namespace anthill.prelude
  sort Type
    operation only_on_type(t: Type) -> Int64 = 99
  end
end
"#;
    let rendered = refusal(
        "papx0onlytype",
        ONLY_ON_TYPE,
        "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.only_on_type()",
    );
    assert!(
        rendered.contains("`Box` declares no `only_on_type`"),
        "the denoted sort is the one searched: {rendered}"
    );
    assert!(
        rendered.contains("anthill.prelude.Type.only_on_type(…)"),
        "the member of `Type` is named with its spelling: {rendered}"
    );
    // The advised spelling.
    assert_eq!(
        run_int(
            "papx0onlytypenamed",
            ONLY_ON_TYPE,
            "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    anthill.prelude.Type.only_on_type(t)",
        ),
        99
    );
}

/// The stdlib's own case: `Type` provides `Eq`, `Box` declares no `eq`. `t.eq(u)` is
/// refused, as the written `Box[V = Int64].eq(u)` is, and the named call compares the
/// two type values.
#[test]
fn eq_is_refused_on_a_denoting_receiver_and_the_named_call_answers() {
    let rendered = refusal(
        "papx0eq",
        "",
        "  operation go() -> Bool =\n    let t = Box[V = Int64]\n    let u = Box[V = Int64]\n    t.eq(u)",
    );
    assert!(
        rendered.contains("`Box` declares no `eq`")
            && rendered.contains("anthill.prelude.PartialEq.eq(…)"),
        "{rendered}"
    );
    // The written spelling refuses the same program.
    let written = refusal(
        "papx0eqwritten",
        "",
        "  operation go() -> Bool = Box[V = Int64].eq(Box[V = Int64])",
    );
    assert!(written.contains("Box.eq"), "{written}");
    // The advised spelling.
    let got = run(
        "papx0eqnamed",
        "",
        "  operation go() -> Bool =\n    let t = Box[V = Int64]\n    let u = Box[V = Int64]\n    anthill.prelude.PartialEq.eq(t, u)",
    );
    assert!(matches!(got, Value::Bool(true)), "got {got:?}");
}

/// A name both the sort and `Type` declare: the receiver denotes the sort, so it is the
/// sort's — in all three spellings — and the member of `Type` is the named call.
#[test]
fn a_member_on_both_the_sort_and_type_is_the_sorts() {
    for (ns, body) in [
        ("papx0bothbare", "  operation go() -> Int64 = Box.tag()"),
        ("papx0bothwritten", "  operation go() -> Int64 = Box[V = Int64].tag()"),
        (
            "papx0bothbound",
            "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.tag()",
        ),
    ] {
        assert_eq!(run_int(ns, TYPE_TAG, body), 7, "{ns}");
    }
    assert_eq!(
        run_int(
            "papx0bothnamed",
            TYPE_TAG,
            "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    Type.tag(t)",
        ),
        99
    );
}

/// The boundary of the rule. A `Type` that denotes nothing known at the dot is a value:
/// a call's result reaches `Type`'s `eq` and a member declared on `Type`, and a parameter
/// is refused about `Type`.
#[test]
fn a_type_that_denotes_nothing_here_is_a_value() {
    let got = run(
        "papx0lost",
        "",
        "  operation id_ty(x: Type) -> Type = x\n  operation go() -> Bool =\n    let t = id_ty(Box[V = Int64])\n    t.eq(Box[V = Int64])",
    );
    assert!(matches!(got, Value::Bool(true)), "got {got:?}");
    assert_eq!(
        run_int(
            "papx0lostmember",
            TYPE_TAG,
            "  operation id_ty(x: Type) -> Type = x\n  operation go() -> Int64 =\n    let t = id_ty(Box[V = Int64])\n    t.tag()",
        ),
        99
    );
    for (ns, body) in [
        (
            "papx0param",
            "  operation f(t: Type) -> Int64 = t.tag()\n  operation go() -> Int64 = f(Box)",
        ),
        (
            "papx0lostmiss",
            "  operation id_ty(x: Type) -> Type = x\n  operation go() -> Int64 =\n    let t = id_ty(Box[V = Int64])\n    t.tag()",
        ),
    ] {
        let rendered = refusal(ns, "", body);
        assert!(
            rendered.contains("anthill.prelude.Type.tag") && rendered.contains("no such member"),
            "{ns}: {rendered}"
        );
    }
}

/// The sort denoted is `Type`: its member is called as the written `Type.tag()` calls it,
/// with no argument for the parameter, and refused in the same words.
#[test]
fn a_receiver_denoting_type_itself_is_types_own_call() {
    let bound = refusal(
        "papx0self",
        TYPE_TAG,
        "  operation go() -> Int64 =\n    let t = Type\n    t.tag()",
    );
    let written = refusal("papx0selfwritten", TYPE_TAG, "  operation go() -> Int64 = Type.tag()");
    for rendered in [&bound, &written] {
        assert!(
            rendered.contains("tag.arity") && rendered.contains("no argument fills parameter `t`"),
            "{rendered}"
        );
    }
}

// ── the call is the written one ─────────────────────────────────────────────

/// A member whose parameters are values of the sort is called with the arguments as
/// written — the receiver is a type and fills none of them — as `Box[V = Int64].combine(…)`
/// is. The bracket reaches the argument check here too.
#[test]
fn a_member_taking_values_of_the_sort_is_called_as_written() {
    for (ns, body) in [
        (
            "papx0instwritten",
            "  operation go() -> Int64 = Box[V = Int64].combine(mk(v: 1), mk(v: 2))",
        ),
        (
            "papx0instbound",
            "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.combine(mk(v: 1), mk(v: 2))",
        ),
    ] {
        assert_eq!(run_int(ns, "", body), 1, "{ns}");
    }
    for (ns, body) in [
        (
            "papx0instwrittenbad",
            "  operation go() -> Int64 = Box[V = Int64].combine(mk(v: \"a\"), mk(v: 2))",
        ),
        (
            "papx0instboundbad",
            "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.combine(mk(v: \"a\"), mk(v: 2))",
        ),
    ] {
        let rendered = refusal(ns, "", body);
        assert!(
            rendered.contains("combine.a") && rendered.contains("expected Box[V = Int64]"),
            "{ns}: {rendered}"
        );
    }
}

/// `Box[Int64]` is `Box[V = Int64]`: the positional argument binds the next parameter.
/// It was refused, and before that admitted with `V` left free.
#[test]
fn a_positional_bracket_binds_the_next_parameter() {
    assert_eq!(
        run_int(
            "papx0pos",
            "",
            "  operation go() -> Int64 =\n    let t = Box[Int64]\n    t.wrap(5)",
        ),
        5
    );
    for (ns, body) in [
        ("papx0poswritten", "  operation go() -> Int64 = Box[Int64].wrap(\"s\")"),
        (
            "papx0posbound",
            "  operation go() -> Int64 =\n    let t = Box[Int64]\n    t.wrap(\"s\")",
        ),
    ] {
        let rendered = refusal(ns, "", body);
        assert!(
            rendered.contains("wrap.x") && rendered.contains("expected Int64"),
            "{ns}: {rendered}"
        );
    }
    // Named and positional mixed: the positional skips the parameter a name took.
    const PAIR: &str = "  sort Pair2[L, R]\n    entity pr(l: L, r: R)\n    operation second(x: R) -> R = x\n  end\n";
    assert_eq!(
        run_int(
            "papx0mixed",
            "",
            &format!("{PAIR}  operation go() -> Int64 =\n    let t = Pair2[R = Int64, String]\n    t.second(5)"),
        ),
        5
    );
    let rendered = refusal(
        "papx0mixedbad",
        "",
        &format!("{PAIR}  operation go() -> Int64 =\n    let t = Pair2[Int64, String]\n    t.second(5)"),
    );
    assert!(
        rendered.contains("second.x") && rendered.contains("expected String"),
        "{rendered}"
    );
}

/// A positional bracket inside the bracket is named as the outer one is.
#[test]
fn a_nested_positional_bracket_is_named_too() {
    for (ns, body) in [
        (
            "papx0nestwritten",
            "  operation go() -> Int64 = Box.unbox(Box[V = Box[Int64]].wrap(mk(v: 3)))",
        ),
        (
            "papx0nestbound",
            "  operation go() -> Int64 =\n    let t = Box[V = Box[Int64]]\n    Box.unbox(t.wrap(mk(v: 3)))",
        ),
    ] {
        assert_eq!(run_int(ns, "", body), 3, "{ns}");
    }
}

/// `let t = Box; t.mk(5)` constructs, as `Box.mk(5)` does.
#[test]
fn a_constructor_is_reached_through_a_let_bound_type() {
    for (ns, body) in [
        ("papx0ctorwritten", "  operation go() -> Int64 = Box.unbox(Box.mk(5))"),
        (
            "papx0ctorbound",
            "  operation go() -> Int64 =\n    let t = Box\n    Box.unbox(t.mk(5))",
        ),
    ] {
        assert_eq!(run_int(ns, "", body), 5, "{ns}");
    }
}

/// A bracket on a constructor's receiver binds the sort's parameters, in both spellings:
/// the field is checked at them (`wi_hzvqa_alias_receiver_test` has the rule's own rows).
#[test]
fn a_bracket_on_a_constructor_binds_in_both_spellings() {
    for (ns, bind, recv) in [
        ("papx0ctorbrwritten", "", "Box[V = Int64]"),
        ("papx0ctorbrbound", "    let t = Box[V = Int64]\n", "t"),
    ] {
        let body = format!("  operation go() -> Int64 =\n{bind}    Box.unbox({recv}.mk(5))");
        assert_eq!(run_int(ns, "", &body), 5, "{ns}");
        let bad = format!("{ns}bad");
        let body = format!("  operation go() -> Int64 =\n{bind}    Box.count({recv}.mk(\"s\"))");
        let rendered = refusal(&bad, "", &body);
        assert!(
            rendered.contains("mk.v (entity-field): expected Int64, got String"),
            "{bad}: {rendered}"
        );
    }
}

/// A type parameter in the bracket is that parameter, read as the written
/// `Box[V = T].wrap(y)` reads it. The value read of `T` needs its `TypeValue` clause.
#[test]
fn a_type_parameter_in_the_bracket_is_that_parameter() {
    assert_eq!(
        run_int(
            "papx0rigidwritten",
            "",
            "  operation written[T](y: T) -> T = Box[V = T].wrap(y)\n  operation go() -> Int64 = written(5)",
        ),
        5
    );
    assert_eq!(
        run_int(
            "papx0rigid",
            "",
            "  operation bound[T](y: T) -> T\n    requires anthill.reflect.TypeValue[T = T]\n  =\n    let t = Box[V = T]\n    t.wrap(y)\n  operation go() -> Int64 = bound(5)",
        ),
        5
    );
}

/// Parentheses make an expression: `(Box[V = Int64]).tag()` is a dot on the type value,
/// and the bracket rides it.
#[test]
fn a_parenthesized_type_is_a_receiver() {
    assert_eq!(
        run_int("papx0paren", "", "  operation go() -> Int64 = (Box[V = Int64]).tag()"),
        7
    );
    assert_eq!(
        run_int("papx0parenbare", "", "  operation go() -> Int64 = (Box).tag()"),
        7
    );
    let rendered = refusal(
        "papx0parenbad",
        "",
        "  operation go() -> Int64 = (Box[V = Int64]).wrap(\"s\")",
    );
    assert!(
        rendered.contains("wrap.x") && rendered.contains("expected Int64"),
        "{rendered}"
    );
}

/// The same for a value: `(b).unbox()` is `b.unbox()`. A parenthesized receiver of a
/// CALL was dropped, leaving `unbox()` standing alone. (The member read `(b).v` already
/// kept its receiver; it is here as the fence.)
#[test]
fn a_parenthesized_value_is_a_receiver() {
    assert_eq!(
        run_int(
            "papx0parencall",
            "",
            "  operation go() -> Int64 =\n    let b = mk(v: 4)\n    (b).unbox()",
        ),
        4
    );
    assert_eq!(
        run_int(
            "papx0parenfield",
            "",
            "  operation go() -> Int64 =\n    let b = mk(v: 4)\n    (b).v",
        ),
        4
    );
}

/// An alias is read as a name path reads it: a pure alias is the sort it stands for,
/// through a chain of aliases too, and one that owns members of its own is read as
/// written. The parameters an alias fixes ride a call through it in both spellings
/// (`wi_hzvqa_alias_receiver_test` has the rule's own rows).
#[test]
fn an_alias_denotes_what_it_stands_for() {
    const ALIASES: &str = "  sort CA = Box[V = Int64]\n  sort CB = Box\n  sort CC = CA\n";
    for (ns, alias, call, want) in [
        ("papx0aliastag", "CA", "t.tag()", 7),
        ("papx0aliaswrap", "CA", "t.wrap(5)", 5),
        ("papx0aliasbare", "CB", "t.wrap(5)", 5),
        ("papx0aliaschain", "CC", "t.wrap(5)", 5),
        ("papx0aliasctor", "CA", "Box.unbox(t.mk(5))", 5),
    ] {
        let body = format!("{ALIASES}  operation go() -> Int64 =\n    let t = {alias}\n    {call}");
        assert_eq!(run_int(ns, "", &body), want, "{ns}");
    }
    let written = refusal(
        "papx0aliasbadwritten",
        "",
        &format!("{ALIASES}  operation go() -> Int64 = CA.wrap(\"s\")"),
    );
    let bound = refusal(
        "papx0aliasbadbound",
        "",
        &format!("{ALIASES}  operation go() -> Int64 =\n    let t = CA\n    t.wrap(\"s\")"),
    );
    for rendered in [&written, &bound] {
        assert!(
            rendered.contains("wrap.x (op-arg): expected Int64, got String"),
            "one refusal site for both spellings:\n{written}\n{bound}"
        );
    }

    // An alias with members of its own: `extra` is the alias's, and `tag` — the target's —
    // is not reached through it, as the written `CA.tag()` is not.
    const OWNING: &str =
        "  sort CA = Box[V = Int64]\n  namespace CA\n    operation extra() -> Int64 = 11\n  end\n";
    for (ns, body) in [
        ("papx0ownwritten", "  operation go() -> Int64 = CA.extra()"),
        ("papx0ownbound", "  operation go() -> Int64 =\n    let t = CA\n    t.extra()"),
    ] {
        assert_eq!(run_int(ns, "", &format!("{OWNING}{body}")), 11, "{ns}");
    }
    for (ns, body) in [
        ("papx0owntagwritten", "  operation go() -> Int64 = CA.tag()"),
        ("papx0owntagbound", "  operation go() -> Int64 =\n    let t = CA\n    t.tag()"),
    ] {
        let rendered = refusal(ns, "", &format!("{OWNING}{body}"));
        assert!(rendered.contains("CA.tag"), "{ns}: {rendered}");
    }
}

/// A constant in the bracket is part of the type: `Vec[Int64, 3]` is not a
/// `Vec[Int64, 4]`, through the bound name as written.
#[test]
fn a_constant_in_the_bracket_is_part_of_the_denoted_type() {
    const VEC: &str = "  sort Vec[E, N]\n    entity vec(e: E)\n    operation same(x: Vec[E, N]) -> Vec[E, N] = x\n  end\n";
    for (ns, body) in [
        (
            "papx0constwritten",
            "  operation go() -> Int64 =\n    let v: Vec[Int64, 4] = Vec[Int64, 3].same(vec(e: 1))\n    2",
        ),
        (
            "papx0constbound",
            "  operation go() -> Int64 =\n    let t = Vec[Int64, 3]\n    let v: Vec[Int64, 4] = t.same(vec(e: 1))\n    2",
        ),
    ] {
        let rendered = refusal(ns, "", &format!("{VEC}{body}"));
        assert!(
            rendered.contains("expected Vec[E = Int64, N = 4], got Vec[E = Int64, N = 3]"),
            "{ns}: {rendered}"
        );
    }
}

/// The receiver denotes a spec: the member is the spec's operation at the bracket's
/// carrier, as `Desc[T = Leaf].label()` is.
#[test]
fn a_spec_is_denoted_as_any_sort_is() {
    const SPEC: &str = "  sort Desc\n    sort T = ?\n    operation label() -> Int64\n  end\n  sort Leaf\n    entity leaf\n    provides Desc[T = Leaf]\n    operation label() -> Int64 = 7\n  end\n";
    for (ns, body) in [
        ("papx0specwritten", "  operation go() -> Int64 = Desc[T = Leaf].label()"),
        (
            "papx0specbound",
            "  operation go() -> Int64 =\n    let t = Desc[T = Leaf]\n    t.label()",
        ),
    ] {
        assert_eq!(run_int(ns, "", &format!("{SPEC}{body}")), 7, "{ns}");
    }
}

/// A lambda written under the `let` sees what the name denotes.
#[test]
fn a_lambda_under_the_binding_sees_the_denotation() {
    let got = run_int(
        "papx0lambda",
        "",
        "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    let f = lambda (x: Int64) -> t.wrap(x)\n    f(3)",
    );
    assert_eq!(got, 3);
}

/// A nested sort is declared in `Box` and is not a call. The refusal says that, and does
/// not say `Box` has no such member.
#[test]
fn a_declaration_that_is_no_call_is_refused_truthfully() {
    let rendered = refusal(
        "papx0nested",
        "",
        "  namespace Box\n    sort Inner\n      entity inn\n    end\n  end\n  operation go() -> Type =\n    let t = Box\n    t.Inner",
    );
    assert!(
        rendered.contains("`Inner` is declared in `Box` and is neither"),
        "{rendered}"
    );
    assert!(!rendered.contains("no such member"), "{rendered}");
}

/// An `internal` member is hidden from a dot written outside its sort, as the written
/// `Vault.secret()` is, and reached from inside it.
#[test]
fn an_internal_member_is_hidden_as_its_written_name_is() {
    let lib = |ns: &str, body: &str| {
        format!(
            "namespace lib.{ns}\n  sort Vault\n    entity open\n    internal entity sealed(k: Int64)\n    internal operation secret() -> Int64 = 13\n    operation inside() -> Int64 =\n      let t = Vault\n      t.secret()\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.Vault\n{body}\nend\n"
        )
    };
    for (ns, body, hidden) in [
        ("papx0hidwritten", "  operation go() -> Int64 = Vault.secret()", "secret"),
        (
            "papx0hidbound",
            "  operation go() -> Int64 =\n    let t = Vault\n    t.secret()",
            "secret",
        ),
        (
            "papx0hidctor",
            "  operation go() -> Vault =\n    let t = Vault\n    t.sealed(1)",
            "sealed",
        ),
    ] {
        let errs = try_load_kb_with(&lib(ns, body))
            .err()
            .unwrap_or_else(|| panic!("{ns}: an internal member must be refused from outside"));
        let rendered = format!("{errs:?}");
        assert!(
            rendered.contains(&format!("{hidden}' is internal to 'lib.{ns}.Vault'"))
                && rendered.contains(&format!("from scope 'test.{ns}.go'")),
            "{ns}: {rendered}"
        );
    }
    let mut interp = interp_for(&lib("papx0hidinside", "  operation go() -> Int64 = Vault.inside()"));
    let got = interp
        .call("test.papx0hidinside.go", &[])
        .unwrap_or_else(|e| panic!("inside: {e:?}"));
    assert!(matches!(got, Value::Int(13)), "got {got:?}");
}

// ── fences ──────────────────────────────────────────────────────────────────

/// Neither written spelling reaches the typer's dot frame; both answer as before.
#[test]
fn the_written_spellings_are_unchanged() {
    for (ns, body) in [
        ("papx0bare", "  operation go() -> Int64 = Box.tag()"),
        ("papx0written", "  operation go() -> Int64 = Box[V = Int64].tag()"),
    ] {
        assert_eq!(run_int(ns, "", body), 7, "{ns}");
    }
}

/// A shadowing `let` is a new name: the inner `t` is an `Int64` and the dot is its.
#[test]
fn a_shadowing_rebind_drops_the_denotation() {
    let rendered = refusal(
        "papx0shadow",
        "",
        "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    let t = 1\n    t.tag()",
    );
    assert!(rendered.contains("Int64"), "the inner binding decides: {rendered}");
    assert!(
        !rendered.contains("papx0shadow.Box"),
        "the outer denotation must not survive the rebind: {rendered}"
    );
}
