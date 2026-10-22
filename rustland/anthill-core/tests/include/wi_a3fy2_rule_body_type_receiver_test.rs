//! WI-20261008-A3FY2 — a parenthesized type receiver in a rule body (proposal 055 umbrella
//! A step 4; the rule is WI-20260824-PAPX0's, `docs/kernel-language.md` §5.4).
//!
//! THE RULE. A receiver that denotes a sort takes a dot as the written companion call, and
//! a rule body reads it so as an operation body does:
//!
//!   rule r(?x) :- ?x <=> (Box).tag()                 as  ?x <=> Box.tag()
//!   rule r(?x) :- ?x <=> (Box[V = Int64]).wrap(5)    as  ?x <=> Box[V = Int64].wrap(5)
//!
//! Before, the rule-body walk built the receiver as a data term — a reference to the sort,
//! an application of it — and the typer refused the sort's name, or an entry of its
//! bracket, as an unresolved name.
//!
//! ONE BOUNDARY. A constructor reached through such a receiver is refused in a rule body's
//! own term, with the spelling that works. A constructor there is the term the clause
//! matches, and the loader builds it from the written name: it names the positional
//! arguments by their fields and leaves an omitted field open. The construction the dot
//! makes is a call; stored in a rule body it matched as a different term —
//! `holds((Sh).pt(1))` answered nothing where `holds(Sh.pt(1))` answers.
//!
//! ONE NODE. The dot is replaced by the written call before anything reads the rule body
//! (`typing::written_type_dots_as_calls`), so the two spellings are one call to every
//! reader. Left a dot it was typed as a dot is: its arguments were checked at load where
//! the written call's are not, an equation was applied to it at load where the written
//! call keeps a residual, and the variable an argument names was not typed by the call's
//! parameter, so a later `?c.bump()` was left unevaluated.
//!
//! EVERY ROW HAS ITS OWN SOURCE, as in `wi_papx0_dot_receiver_split_test`.
//!
//! CONTROLS — measured against this module alone, each piece backed out on its own:
//!
//!   the loader's receiver (`Loader::written_type_receiver_occurrence` answering `None`
//!   always) — FAIL, each on the unresolved-name refusal:
//!     a_parenthesized_type_receiver_answers_as_the_written_one
//!     the_bracket_binds_the_sorts_parameters
//!     an_alias_receiver_binds_what_the_alias_fixes
//!     the_dot_is_a_call_wherever_a_rule_body_writes_it
//!     a_requirement_of_the_sort_is_supplied_as_for_the_written_call
//!     an_equation_carries_the_receiver_into_an_operation_body
//!     a_constructor_in_a_rule_body_is_written_by_its_name
//!     a_member_the_sort_does_not_declare_is_refused_about_the_sort
//!     an_internal_member_is_hidden_as_its_written_name_is
//!     both_spellings_are_one_call_to_every_reader
//!     a_dotted_sort_name_is_a_written_type_in_both_bodies (its rule-body rows)
//!   the replacement before the rule body is read (`body_with_written_type_calls` handing
//!   the body back as it came, so the dispatch walk types the dot) — FAIL:
//!     both_spellings_are_one_call_to_every_reader
//!   the typer's constructor refusal (`denoted_sort_dot`'s rule-body clause) — FAIL:
//!     a_constructor_in_a_rule_body_is_written_by_its_name
//!   that refusal asked of every rule-body text (`in_rule_body` for
//!   `written_as_an_operation_body`) — FAIL:
//!     a_constructor_under_a_compound_expression_is_the_operation_bodys
//!
//!   PASS UNDER EVERY BACK-OUT, by design — they are the fences:
//!     the_written_spellings_are_unchanged — neither reaches a dot.
//!     a_parenthesized_value_keeps_the_value_dot — the receiver is no written type.
//!     a_constructor_under_a_compound_expression_is_the_operation_bodys — passes with the
//!       loader's receiver and with the constructor refusal backed out; it is the fence of
//!       the last back-out only.

use anthill_core::eval::Value;

use crate::common::{load_errors_of, load_kb_with, query_unary};

/// The sort every row is about, indented for a namespace body.
const BOX: &str = r#"
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
    operation flag() -> Bool = true
    operation wrap(x: V) -> V = x
    rule rows(1) :- true
  end
"#;

/// A namespace `test.<ns>` holding [`BOX`] and `body`, preceded by `prefix` (another
/// namespace, for the row that reads a sort from outside it).
fn source(ns: &str, prefix: &str, body: &str) -> String {
    format!(
        "{prefix}\nnamespace test.{ns}\n  import anthill.prelude.{{Type, Bool, Option}}\n  import anthill.prelude.Option.{{some, none}}\n{BOX}\n{body}\nend\n"
    )
}

/// Load, resolve `test.<ns>.r(?x)`, and hand back the integers `?x` is bound to. Every
/// answer must be definite.
fn ints(ns: &str, prefix: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&source(ns, prefix, body));
    query_unary(&mut kb, &format!("test.{ns}.r"))
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "{ns}: a conditional answer, {v:?}");
            match v {
                Value::Int(n) => n,
                other => panic!("{ns}: expected an Int64, got {other:?}"),
            }
        })
        .collect()
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, prefix: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, prefix, body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    format!("{errs:?}")
}

/// The message the receiver drew before: the sort, or an entry of its bracket, read as a
/// value no name denotes. No refusal below may be that one.
const UNRESOLVED: &str = "expected resolved name";

// ── the rule ────────────────────────────────────────────────────────────────

/// The rows the ticket was opened for, and the positional bracket.
#[test]
fn a_parenthesized_type_receiver_answers_as_the_written_one() {
    for (ns, body) in [
        ("a3fy2bare", "  rule r(?x) :- ?x <=> (Box).tag()"),
        ("a3fy2named", "  rule r(?x) :- ?x <=> (Box[V = Int64]).tag()"),
        ("a3fy2pos", "  rule r(?x) :- ?x <=> (Box[Int64]).tag()"),
        ("a3fy2nested", "  rule r(?x) :- ?x <=> (Box[V = Box[V = Int64]]).tag()"),
        ("a3fy2var", "  rule r(?x) :- ?x <=> (Box[V = ?t]).tag()"),
    ] {
        assert_eq!(ints(ns, "", body), [7], "{ns}");
    }
}

/// The bracket is the call's: an argument is checked at the parameter it binds, in the
/// written call's own words.
#[test]
fn the_bracket_binds_the_sorts_parameters() {
    assert_eq!(
        ints("a3fy2wrap", "", "  rule r(?x) :- ?x <=> (Box[V = Int64]).wrap(5)"),
        [5]
    );
    for (ns, body) in [
        ("a3fy2badwritten", "  rule r(?x) :- ?x <=> Box[V = Int64].wrap(\"s\")"),
        ("a3fy2bad", "  rule r(?x) :- ?x <=> (Box[V = Int64]).wrap(\"s\")"),
    ] {
        let rendered = refusal(ns, "", body);
        assert!(
            rendered.contains("wrap.x") && rendered.contains("expected Int64, got String"),
            "{ns}: {rendered}"
        );
        assert!(!rendered.contains(UNRESOLVED), "{ns}: {rendered}");
    }
    // A bracket the sort does not take is refused once, about the bracket.
    let rendered = refusal("a3fy2nokey", "", "  rule r(?x) :- ?x <=> (Box[W = Int64]).tag()");
    assert!(rendered.contains("has no type parameter named 'W'"), "{rendered}");
    assert!(!rendered.contains(UNRESOLVED), "{rendered}");
}

/// A receiver that is an alias binds the parameters the alias fixes.
#[test]
fn an_alias_receiver_binds_what_the_alias_fixes() {
    const ALIAS: &str = "  sort CA = Box[V = Int64]\n";
    assert_eq!(
        ints("a3fy2alias", "", &format!("{ALIAS}  rule r(?x) :- ?x <=> (CA).wrap(5)")),
        [5]
    );
    let rendered = refusal(
        "a3fy2aliasbad",
        "",
        &format!("{ALIAS}  rule r(?x) :- ?x <=> (CA).wrap(\"s\")"),
    );
    assert!(
        rendered.contains("wrap.x") && rendered.contains("expected Int64, got String"),
        "{rendered}"
    );
}

/// The dot is evaluated where the written call is: as an operand of `<=>` on either side
/// and of `=`, under `not`, as a goal, as a goal's argument, as an argument of a call and
/// of another such dot, and paren-less.
#[test]
fn the_dot_is_a_call_wherever_a_rule_body_writes_it() {
    for (ns, body, expected) in [
        ("a3fy2left", "  rule r(?x) :- (Box).tag() <=> ?x", vec![7]),
        ("a3fy2eq", "  rule r(1) :- (Box).tag() = 7", vec![1]),
        ("a3fy2noteq", "  rule r(1) :- not((Box).tag() = 8)", vec![1]),
        ("a3fy2notheld", "  rule r(1) :- not((Box).tag() = 7)", vec![]),
        ("a3fy2goal", "  rule r(1) :- (Box).flag()", vec![1]),
        ("a3fy2notgoal", "  rule r(1) :- not((Box).flag())", vec![]),
        (
            "a3fy2goalarg",
            "  fact p(7)\n  rule r(1) :- p((Box).tag())",
            vec![1],
        ),
        (
            "a3fy2callarg",
            "  operation inc(n: Int64) -> Int64 = n + 1\n  rule r(?x) :- ?x <=> inc((Box).tag())",
            vec![8],
        ),
        (
            "a3fy2dotarg",
            "  rule r(?x) :- ?x <=> (Box[V = Int64]).wrap((Box).tag())",
            vec![7],
        ),
        (
            "a3fy2later",
            "  rule r(?x) :- ?x <=> (Box[V = Int64]).wrap(?y), ?y <=> 4",
            vec![4],
        ),
        ("a3fy2parenless", "  rule r(?x) :- ?x <=> (Box).tag", vec![7]),
        ("a3fy2chain", "  rule r(?x) :- ?x <=> (Box).tag().abs()", vec![7]),
    ] {
        assert_eq!(ints(ns, "", body), expected, "{ns}");
    }
}

/// A requirement of the denoted sort is supplied for the call as for the written one, and
/// refused in the same sentence where the clause cannot supply it.
#[test]
fn a_requirement_of_the_sort_is_supplied_as_for_the_written_call() {
    const HOLDER: &str = "  sort Desc\n    sort T = ?\n    operation label(x: T) -> Int64\n  end\n  sort Leaf\n    entity leaf\n    provides Desc[T = Leaf]\n    operation label(x: Leaf) -> Int64 = 7\n  end\n  sort Twig\n    entity twig\n  end\n  sort Holder[T]\n    requires Desc[T = T]\n    operation show(x: T) -> Int64 = Desc.label(x)\n  end\n";
    for (ns, call) in [
        ("a3fy2reqwritten", "Holder[T = Leaf].show(leaf())"),
        ("a3fy2req", "(Holder[T = Leaf]).show(leaf())"),
        ("a3fy2reqbare", "(Holder).show(leaf())"),
    ] {
        assert_eq!(
            ints(ns, "", &format!("{HOLDER}  rule r(?x) :- ?x <=> {call}")),
            [7],
            "{ns}"
        );
    }
    for (ns, call) in [
        ("a3fy2noreqwritten", "Holder[T = Twig].show(twig())"),
        ("a3fy2noreq", "(Holder[T = Twig]).show(twig())"),
    ] {
        let rendered = refusal(ns, "", &format!("{HOLDER}  rule r(?x) :- ?x <=> {call}"));
        assert!(
            rendered.contains("Holder.show.requires") && rendered.contains("cannot be supplied"),
            "{ns}: {rendered}"
        );
        assert!(!rendered.contains(UNRESOLVED), "{ns}: {rendered}");
    }
}

/// An equation's right-hand side is built by the rule-body walk and typed where it is
/// spliced. Fired in an operation body, the dot is the operation body's: a call, and for a
/// constructor a construction.
#[test]
fn an_equation_carries_the_receiver_into_an_operation_body() {
    assert_eq!(
        ints(
            "a3fy2simp",
            "",
            "  rule f(?n) <=> (Box[V = Int64]).wrap(?n) @[simp]\n  operation g() -> Int64 = f(3)\n  rule r(?x) :- ?x <=> g()",
        ),
        [3]
    );
    assert_eq!(
        ints(
            "a3fy2simpctor",
            "",
            "  rule f(?n) <=> (Box).mk(?n) @[simp]\n  operation g() -> Box[V = Int64] = f(3)\n  rule r(?x) :- mk(v: ?x) <=> g()",
        ),
        [3]
    );
}

/// The two spellings are one call to every reader of the rule body. Each row is a place
/// where the rule-body walk reads a dot and a written call differently, so a dot left a
/// dot answered differently from its written spelling.
#[test]
fn both_spellings_are_one_call_to_every_reader() {
    const HOLD: &str = "  sort Cnt\n    entity cnt(n: Int64)\n    operation bump(c: Cnt) -> Int64 = match c\n      case cnt(n) -> n + 1\n  end\n  sort Hold\n    operation keep(c: Cnt) -> Int64 = 0\n    operation take(n: Int64) -> Int64 = n\n    operation open(n: Int64) -> Int64\n    operation seven(x: Cnt) -> Int64 = 7\n    rule open(?n) <=> take(?n) @[simp]\n  end\n";
    let both = |body: &str| [body.replace("RECV", "Hold"), body.replace("RECV", "(Hold)")];

    // The call's parameter types the variable its argument names, which is what lets the
    // dot after it be dispatched. Left a dot, `?c` was untyped and `?c.bump()` unevaluated.
    for (ns, body) in ["a3fy2typesw", "a3fy2types"].into_iter().zip(both(
        "  rule inner(?c, ?x) :- ?z <=> RECV.keep(?c), ?x <=> ?c.bump()\n  rule r(?x) :- inner(cnt(n: 4), ?x)",
    )) {
        assert_eq!(ints(ns, "", &format!("{HOLD}{body}")), [5], "{ns}");
    }

    // An argument the typer cannot type — a field of an untyped variable — leaves the
    // call to be evaluated by its value, as the written call is. Left a dot, the whole
    // dot was bound unevaluated.
    for (ns, body) in ["a3fy2untypedw", "a3fy2untyped"].into_iter().zip(both(
        "  rule inner(?p, ?x) :- ?x <=> RECV.seven(?p.it)\n  rule r(?x) :- inner(wrapper(it: cnt(n: 4)), ?x)\n  entity wrapper(it: Cnt)",
    )) {
        assert_eq!(ints(ns, "", &format!("{HOLD}{body}")), [7], "{ns}");
    }

    // What the walk does with the written call is its own, and is one verdict for both
    // spellings: an ordinary operation's call in a value slot is not checked against its
    // parameters at load, and an equation is not applied to it there. A dot is checked,
    // and an equation applied — so each row had two verdicts.
    for (what, body) in [
        ("an argument of another type", "  rule r(?x) :- ?x <=> RECV.take(\"s\")"),
        ("a call an equation defines", "  rule r(?x) :- ?x <=> RECV.open(4)"),
    ] {
        let [written, dotted] = both(body);
        let verdict = |ns: &str, body: &str| -> Result<Vec<bool>, Vec<String>> {
            let source = source(ns, "", &format!("{HOLD}{body}"));
            let errs = load_errors_of(&source);
            if !errs.is_empty() {
                return Err(errs);
            }
            let mut kb = load_kb_with(&source);
            Ok(query_unary(&mut kb, &format!("test.{ns}.r"))
                .into_iter()
                .map(|(_, definite)| definite)
                .collect())
        };
        let written = verdict("a3fy2verdict", &written);
        let dotted = verdict("a3fy2verdict", &dotted);
        assert_eq!(
            written.as_ref().map_err(|_| "refused"),
            dotted.as_ref().map_err(|_| "refused"),
            "{what}: written {written:?}, dotted {dotted:?}"
        );
    }
}

// ── the boundary ────────────────────────────────────────────────────────────

/// A constructor reached through the receiver is refused in a rule body's own term, and
/// the spelling the refusal gives answers — for a bare receiver, a bracketed one, an
/// alias, a sort named by a path, and a receiver that is itself dotted on. The spelling is
/// the constructor's qualified name, which the sort's short name is not for a path.
#[test]
fn a_constructor_in_a_rule_body_is_written_by_its_name() {
    const DECLS: &str = "  fact holds(mk(v: 5))\n  sort CA = Box[V = Int64]\n  sort Outer\n    sort Inner[W]\n      entity inn(k: Int64)\n    end\n  end\n  fact holds(Outer.Inner.inn(k: 5))\n";
    for (ns, dotted, constructor) in [
        ("a3fy2ctor", "(Box).mk(5)", "Box.mk"),
        ("a3fy2ctorbr", "(Box[V = Int64]).mk(5)", "Box.mk"),
        ("a3fy2ctoralias", "(CA).mk(5)", "Box.mk"),
        ("a3fy2ctorpath", "(Outer.Inner[W = Int64]).inn(5)", "Outer.Inner.inn"),
    ] {
        let rendered = refusal(ns, "", &format!("{DECLS}  rule r(1) :- holds({dotted})"));
        assert!(
            rendered.contains("the constructor written by its name")
                && rendered.contains(&format!("`test.{ns}.{constructor}(…)`"))
                && rendered.contains("a receiver that denotes a sort"),
            "{ns}: {rendered}"
        );
        assert!(!rendered.contains(UNRESOLVED), "{ns}: {rendered}");
        let advised = format!("{ns}advised");
        assert_eq!(
            ints(
                &advised,
                "",
                &format!("{DECLS}  rule r(1) :- holds(test.{advised}.{constructor}(5))"),
            ),
            [1],
            "{ns}: the advised spelling"
        );
    }
    let rendered = refusal("a3fy2ctorchain", "", "  rule r(?x) :- ?x <=> (Box).mk(5).v");
    assert!(rendered.contains("`test.a3fy2ctorchain.Box.mk(…)`"), "{rendered}");
    assert_eq!(
        ints(
            "a3fy2ctorchainadvised",
            "",
            "  rule r(?x) :- ?x <=> test.a3fy2ctorchainadvised.Box.mk(5).v",
        ),
        [5]
    );

    // Why it is a refusal: the written name leaves an omitted field open, so the term
    // matches a fact that fills it. The call the dot makes does not build that term.
    const SHAPE: &str = "  sort Sh\n    entity pt(x: Int64, y: Option[T = Int64])\n  end\n  fact held(pt(x: 1, y: some(2)))\n";
    assert_eq!(
        ints("a3fy2open", "", &format!("{SHAPE}  rule r(1) :- held(Sh.pt(1))")),
        [1]
    );
    let rendered = refusal(
        "a3fy2opendot",
        "",
        &format!("{SHAPE}  rule r(1) :- held((Sh).pt(1))"),
    );
    assert!(rendered.contains("`test.a3fy2opendot.Sh.pt(…)`"), "{rendered}");
}

/// Under a compound expression a rule body's text is written as an operation body is, and
/// the constructor is that body's: it loads, as it did.
#[test]
fn a_constructor_under_a_compound_expression_is_the_operation_bodys() {
    let errs = load_errors_of(&source(
        "a3fy2compound",
        "",
        "  rule r(?x) :- ?x <=> (if true then (Box).mk(5) else Box.mk(6))",
    ));
    assert!(errs.is_empty(), "{errs:?}");
}

/// A member the denoted sort does not declare is refused about that sort, and a member of
/// `Type` with its spelling — neither as an unresolved name. A rule of the sort is the goal
/// its written spelling is (`wi_r653s_paren_less_dot_test`); it was refused here as no
/// call until WI-20261008-R653S.
#[test]
fn a_member_the_sort_does_not_declare_is_refused_about_the_sort() {
    for (ns, body, said) in [
        (
            "a3fy2nosuch",
            "  rule r(?x) :- ?x <=> (Box).nosuch()",
            vec!["Box.nosuch", "no such member"],
        ),
        (
            "a3fy2eqmember",
            "  rule r(1) :- (Box).eq(Box)",
            vec!["`Box` declares no `eq`", "anthill.prelude.PartialEq.eq(…)"],
        ),
    ] {
        let rendered = refusal(ns, "", body);
        for words in said {
            assert!(rendered.contains(words), "{ns}: `{words}` not in {rendered}");
        }
        assert!(!rendered.contains(UNRESOLVED), "{ns}: {rendered}");
    }
}

/// An `internal` member is hidden from a dot written outside its sort, as the written
/// `Vault.secret()` is, and a public one is reached.
#[test]
fn an_internal_member_is_hidden_as_its_written_name_is() {
    let lib = |ns: &str| {
        format!(
            "namespace lib.{ns}\n  sort Vault\n    entity open\n    internal operation secret() -> Int64 = 13\n    operation inside() -> Int64 = 5\n  end\nend\n"
        )
    };
    for (ns, call) in [
        ("a3fy2hidwritten", "Vault.secret()"),
        ("a3fy2hid", "(Vault).secret()"),
    ] {
        let rendered = refusal(
            ns,
            &lib(ns),
            &format!("  import lib.{ns}.Vault\n  rule r(?x) :- ?x <=> {call}"),
        );
        assert!(
            rendered.contains(&format!("is internal to 'lib.{ns}.Vault'")),
            "{ns}: {rendered}"
        );
    }
    assert_eq!(
        ints(
            "a3fy2pub",
            &lib("a3fy2pub"),
            "  import lib.a3fy2pub.Vault\n  rule r(?x) :- ?x <=> (Vault).inside()",
        ),
        [5]
    );
}

// ── fences ──────────────────────────────────────────────────────────────────

/// The written spellings never reach a dot; both answer as before.
#[test]
fn the_written_spellings_are_unchanged() {
    for (ns, body, expected) in [
        ("a3fy2wbare", "  rule r(?x) :- ?x <=> Box.tag()", 7),
        ("a3fy2wnamed", "  rule r(?x) :- ?x <=> Box[V = Int64].tag()", 7),
        ("a3fy2wwrap", "  rule r(?x) :- ?x <=> Box[V = Int64].wrap(5)", 5),
    ] {
        assert_eq!(ints(ns, "", body), [expected], "{ns}");
    }
}

/// A sort named by a dotted path is a written type as its bare name is, with a bracket
/// and without, and the rule body follows the operation body. The path's own rows are
/// `wi_rxt6s_dotted_sort_type_value_test`; until it, both bodies refused the bare path
/// with the unresolved-name message.
#[test]
fn a_dotted_sort_name_is_a_written_type_in_both_bodies() {
    const NESTED: &str = "  sort Outer\n    sort Inner[W]\n      entity inn\n      operation deep() -> Int64 = 21\n    end\n  end\n";
    for (ns, body) in [
        ("a3fy2dottedrule", "  rule r(?x) :- ?x <=> (Outer.Inner).deep()"),
        (
            "a3fy2dottedop",
            "  operation go() -> Int64 = (Outer.Inner).deep()\n  rule r(?x) :- ?x <=> go()",
        ),
        ("a3fy2dottedwritten", "  rule r(?x) :- ?x <=> Outer.Inner.deep()"),
        (
            "a3fy2dottedbracket",
            "  rule r(?x) :- ?x <=> (Outer.Inner[W = Int64]).deep()",
        ),
        (
            "a3fy2dottedbracketop",
            "  operation go() -> Int64 = (Outer.Inner[W = Int64]).deep()\n  rule r(?x) :- ?x <=> go()",
        ),
    ] {
        assert_eq!(ints(ns, "", &format!("{NESTED}{body}")), [21], "{ns}");
    }
}

/// Parentheses around a value are a value receiver: the dot is the value's, and the
/// receiver fills the member's first parameter.
#[test]
fn a_parenthesized_value_keeps_the_value_dot() {
    assert_eq!(
        ints(
            "a3fy2value",
            "",
            "  sort Cnt\n    entity cnt(n: Int64)\n    operation bump(c: Cnt) -> Int64 = match c\n      case cnt(n) -> n + 1\n  end\n  rule r(?x) :- ?x <=> (cnt(n: 4)).bump()",
        ),
        [5]
    );
}
