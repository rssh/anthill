//! WI-20260902-40KSW — a dotted name written where a value is, and given no value by any
//! reading, is refused ONCE, saying what the name is: a namespace has no value, a segment
//! names nothing, or a segment is `internal` to a scope the text is not written in. It was
//! refused once per SEGMENT, each segment told "expected resolved name, got unresolved" —
//! a namespace, a sort and a constructor among them that resolved.
//!
//! Measured on a3082618 (`zz.inner` a namespace, `zz.Q` a sort holding `internal sort Sec`
//! and `internal const hidden`), the same in both bodies:
//!
//! | written | before | after |
//! |---|---|---|
//! | `zz.inner = 7` | 2 × "unresolved" | 1, `zz.inner` is a namespace |
//! | `zz = 7` | 1 × "unresolved" | 1, `zz` is a namespace |
//! | `zz.nosuch.x = 7` | 3 × "unresolved" | 1, `zz.nosuch` names nothing: `zz` declares no `nosuch` |
//! | `nosuch.x = 7` | 2 × "unresolved" | 1, no `nosuch` is visible |
//! | `zz.Q.Sec`, `zz.Q.hidden.x` | 1 / 2 × "unresolved" | 1, internal to `zz.Q` |
//! | `zz.Color.nosuch` | 1 × "unresolved" | 1, the sort `zz.Color` declares no `nosuch` |
//! | rule body: `7 = zz.S.seven`, `3 = zz.S.mk.x` | "unresolved" | hold, as their one-segment twins |
//!
//! The rows that already answered once — a rule, a constructor, a sort by a path — keep
//! their errors ([`the_names_with_a_reading_keep_it`]), and so does a name no scope has,
//! written alone ([`a_name_alone_that_names_nothing_keeps_its_refusal`]).
//!
//! WHICH ROWS FAIL WITH A PART BACKED OUT, each alone, measured with temporary switches:
//!   * the typer's rung over the chain (`dotted_name_without_value` answering `None`):
//!     [`a_namespace_by_a_path_is_refused_once_as_a_namespace`],
//!     [`a_path_that_names_nothing_is_refused_once`],
//!     [`a_first_segment_that_names_nothing_is_refused_once`],
//!     [`an_internal_name_by_a_path_is_refused_as_internal`] — both bodies of each —
//!     [`a_written_field_access_call_keeps_its_argument`], whose first argument is a
//!     dotted name, and [`every_value_position_reads_the_name_whole`].
//!   * the namespace arm of `check_bare_ref`: [`a_namespace_alone_is_refused_as_a_namespace`].
//!   * the operation-body walk's dot stamp on the chain it did not read: the
//!     operation-body half of the five rows of the rung.
//!   * a sort prefix read as the chain's first segment:
//!     [`an_internal_name_by_a_path_is_refused_as_internal`].
//!
//!
//! The follow-up's parts, each backed out alone over the rows below them:
//!   * a sort a path names, recorded as its type value, read as the chain's first segment
//!     by the relation and operation readings: [`a_member_by_a_path_to_its_sort_is_read_in_a_rule_body`],
//!     [`a_path_with_a_value_prefix_is_read_off_the_value`];
//!   * an alias's bracket handed to the operation as its receiver's type: the first of those;
//!   * a sort prefix that declares no next segment: [`a_member_a_sort_does_not_declare_is_refused_once`];
//!   * the rest of a path read off a value prefix, a value place passed over by the walk, and
//!     a constructor or an operation as the first segment: [`a_path_with_a_value_prefix_is_read_off_the_value`];
//!   * the `internal` check before the relation and operation readings:
//!     [`an_internal_operation_by_a_path_is_refused_in_a_rule_body`];
//!   * an equation whose replacement the loader refused left unfired, and the loader's
//!     outer node leaving a hidden prefix to the inner one: [`a_refused_replacement_is_reported_once`];
//!   * a hidden path named by its qualified name, as the loader names it:
//!     [`an_internal_name_by_a_path_is_refused_as_internal`],
//!     [`an_internal_operation_by_a_path_is_refused_in_a_rule_body`],
//!     [`a_refused_replacement_is_reported_once`].
//!
//!
//! A rule body's data slots, each part backed out alone:
//!   * the dotted name judged in a data slot (`data_dotted_name_error`):
//!     [`a_dotted_name_in_a_rule_body_data_slot_is_judged_as_in_a_head`];
//!   * a type parameter's member left to what it is bound to:
//!     [`data_slot_readings_with_an_answer_keep_it`];
//!   * a refusal named through the failing segment, which makes the value reading and the
//!     data reading of one name one diagnostic: [`a_path_that_names_nothing_is_refused_once`],
//!     [`a_dotted_name_in_a_rule_body_data_slot_is_judged_as_in_a_head`].
//!
//! [`the_names_with_a_reading_keep_it`], [`a_name_alone_that_names_nothing_keeps_its_refusal`]
//! and [`a_value_prefix_is_read_as_before`] pass either way, by design: they are the bound.

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

const DECL: &str = "\
namespace zz
  import anthill.prelude.Int64
  sort Color
    entity red
  end
  sort P
    entity pt(x: Int64, y: Int64)
  end
  sort Q
    const origin: P = P.pt(3, 4)
    internal const hidden: P = P.pt(3, 4)
    internal sort Sec
      entity sx
    end
  end
end
namespace zz.inner
  fact b(1)
  rule rel(1) :- b(1)
end
";

/// `body` compared with `7`, in a rule body and in an operation body.
fn both_bodies(ns: &str, body: &str) -> [(&'static str, Vec<String>); 2] {
    let rule = load_errors_of(&format!(
        "{DECL}namespace {ns}r\n  import anthill.prelude.Int64\n  rule r(1) :- {body} = 7\nend\n"
    ));
    let op = load_errors_of(&format!(
        "{DECL}namespace {ns}o\n  import anthill.prelude.{{Int64, Bool}}\n  \
         operation viaOp() -> Bool = {body} = 7\nend\n"
    ));
    [("rule body", rule), ("operation body", op)]
}

/// One error, naming each of `tokens`, and none calling a name unresolved.
#[track_caller]
fn refused_once(errs: &[String], tokens: &[&str], why: &str) {
    assert_eq!(errs.len(), 1, "{why}: one error for the one written name, got {errs:#?}");
    assert_refused_naming(errs, tokens, why);
    assert!(
        !errs[0].contains("unresolved"),
        "{why}: a name that resolved is not called unresolved: {errs:#?}"
    );
}

#[test]
fn a_namespace_by_a_path_is_refused_once_as_a_namespace() {
    for (at, errs) in both_bodies("k40a", "zz.inner") {
        refused_once(&errs, &["`zz.inner` is a namespace", "has no value"], at);
    }
}

#[test]
fn a_namespace_alone_is_refused_as_a_namespace() {
    for (at, errs) in both_bodies("k40b", "zz") {
        refused_once(&errs, &["`zz` is a namespace", "has no value"], at);
    }
}

#[test]
fn a_path_that_names_nothing_is_refused_once() {
    for (at, errs) in both_bodies("k40c", "zz.nosuch.x") {
        refused_once(
            &errs,
            &["`zz.nosuch` names nothing", "the namespace `zz` declares no `nosuch`"],
            at,
        );
    }
    // Deeper, it is named where resolution fails, as a clause head names it.
    for (at, errs) in both_bodies("k40d", "zz.inner.nosuch.y") {
        refused_once(
            &errs,
            &["`zz.inner.nosuch` names nothing", "the namespace `zz.inner` declares no `nosuch`"],
            at,
        );
    }
}

#[test]
fn a_first_segment_that_names_nothing_is_refused_once() {
    for (at, errs) in both_bodies("k40e", "nosuch.x") {
        refused_once(
            &errs,
            &["`nosuch.x` names nothing", "no `nosuch` is visible in scope", "import"],
            at,
        );
    }
}

/// The addendum's program: `probe.Hid.Sec` from another namespace is refused as its import
/// is, and so is a hidden const read by a path.
#[test]
fn an_internal_name_by_a_path_is_refused_as_internal() {
    for (body, name) in [("zz.Q.Sec", "'zz.Q.Sec'"), ("zz.Q.hidden.x", "'zz.Q.hidden'")] {
        for (at, errs) in both_bodies("k40f", body) {
            refused_once(&errs, &[name, "is internal to 'zz.Q'"], &format!("{at}: {body}"));
        }
    }
    let probe = "\
namespace probe
  import anthill.prelude.Int64
  sort Hid
    internal sort Sec
      entity sx
    end
  end
end
";
    let errs = load_errors_of(&format!(
        "{probe}namespace user\n  import anthill.prelude.{{Int64, Type}}\n  \
         operation nm(t: Type) -> Int64 = 1\n  operation useIt() -> Int64 = nm(probe.Hid.Sec)\nend\n"
    ));
    refused_once(&errs, &["'probe.Hid.Sec' is internal to 'probe.Hid'", "scope 'user"], "nm(probe.Hid.Sec)");
    let import = load_errors_of(&format!(
        "{probe}namespace user\n  import anthill.prelude.Int64\n  import probe.Hid.Sec\nend\n"
    ));
    assert_refused_naming(&import, &["is internal to 'probe.Hid'"], "the import's twin");
}

/// The bound: a name with a reading is typed as that reading, once, as before.
#[test]
fn the_names_with_a_reading_keep_it() {
    for (body, expected) in [
        ("zz.inner.rel", "expected Relation["),
        ("zz.Color.red", "expected Color, got Int64"),
        ("zz.Color", "expected Type, got Int64"),
    ] {
        for (at, errs) in both_bodies("k40g", body) {
            assert_eq!(errs.len(), 1, "{at}: {body}: {errs:#?}");
            assert!(errs[0].contains("eq.b (op-arg)") && errs[0].contains(expected), "{at}: {body}: {errs:#?}");
        }
    }
}

/// The bound: a name no scope has, written alone, keeps the refusal it had.
#[test]
fn a_name_alone_that_names_nothing_keeps_its_refusal() {
    for (at, errs) in both_bodies("k40h", "nosuch") {
        assert_eq!(errs.len(), 1, "{at}: {errs:#?}");
        assert!(errs[0].contains("nosuch.name") && errs[0].contains("unresolved"), "{at}: {errs:#?}");
    }
}

/// The bound: a written `anthill.reflect.field_access(…)` is a call, so its second argument
/// is an argument, typed as a value; its first, a dotted name, is that name.
#[test]
fn a_written_field_access_call_keeps_its_argument() {
    let errs = load_errors_of(&format!(
        "{DECL}namespace k40i\n  import anthill.prelude.Int64\n  \
         operation g() -> Int64 = anthill.reflect.field_access(zz.inner, nosuch)\nend\n"
    ));
    assert_eq!(errs.len(), 2, "{errs:#?}");
    assert!(errs[0].contains("`zz.inner` is a namespace"), "{errs:#?}");
    assert!(errs[1].contains("nosuch.name") && errs[1].contains("unresolved"), "{errs:#?}");
}

/// The bound: a path whose prefix is a value reads a field of it, as before.
#[test]
fn a_value_prefix_is_read_as_before() {
    let mut interp = interp_for(&format!(
        "{DECL}namespace k40j\n  import anthill.prelude.Int64\n  \
         operation go() -> Int64 = zz.Q.origin.x\nend\n"
    ));
    match interp.call("k40j.go", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 3),
        other => panic!("expected 3, got {other:?}"),
    }
}

/// Every place a value is written meets the one refusal: a const's value, a constraint
/// body, a lambda in either body, a call's argument, and a `@[simp]` right-hand side where
/// a call fires it — the text typed as the rule's, from the rule's scope.
#[test]
fn every_value_position_reads_the_name_whole() {
    for (at, decls) in [
        ("const", "  const c: Int64 = zz.inner"),
        ("constraint", "  fact val(1)\n  constraint k1: val(?v) :- val(?v), ?v = zz.inner"),
        ("rule lambda", "  rule r(?f) :- ?f = lambda (x: Int64) -> zz.inner"),
        (
            "operation lambda",
            "  operation h() -> Function[A = Int64, B = Int64] = lambda (x: Int64) -> zz.inner",
        ),
        ("argument", "  operation id(x: Int64) -> Int64 = x\n  operation g() -> Int64 = id(zz.inner)"),
        (
            "simp right-hand side",
            "  operation f() -> Int64\n  rule f() <=> zz.inner @[simp]\n  operation g() -> Int64 = f()",
        ),
    ] {
        let errs = load_errors_of(&format!(
            "{DECL}namespace k40k\n  import anthill.prelude.{{Int64, Function}}\n{decls}\nend\n"
        ));
        refused_once(&errs, &["`zz.inner` is a namespace"], at);
    }
}

// ── the follow-up: members of a sort or a value by a path, and refused replacements ──

const MEMBERS: &str = "\
namespace zm
  import anthill.prelude.Int64
  sort Color
    entity red
    entity blue(n: Int64)
  end
  sort P
    entity pt(x: Int64, y: Int64)
  end
  sort S
    operation mk() -> P = P.pt(3, 4)
    operation seven() -> Int64 = 7
    internal operation sec() -> Int64 = 1
  end
  sort Box[V]
    entity bx(v: V)
    entity nul
    operation zero() -> Int64 = 0
    operation empty() -> Box[V = V] = nul
    operation wrapIt(x: V) -> Box[V = V] = bx(x)
  end
  sort CA = Box[V = Int64]
end
";

/// `test.<ns>.r(1)`'s answers over `MEMBERS` and a rule `r(1) :- <body>` written in `ns`.
fn holds(ns: &str, body: &str) -> usize {
    let mut kb = crate::common::load_kb_with(&format!(
        "{MEMBERS}namespace {ns}\n  import anthill.prelude.{{Int64, String}}\n  rule r(1) :- {body}\nend\n"
    ));
    crate::common::query_unary(&mut kb, &format!("{ns}.r")).len()
}

/// `body` compared with `7` in a rule body and in an operation body, over `MEMBERS`.
fn both_bodies_over_members(ns: &str, body: &str) -> [(&'static str, Vec<String>); 2] {
    let rule = load_errors_of(&format!(
        "{MEMBERS}namespace {ns}r\n  import anthill.prelude.Int64\n  rule r(1) :- {body} = 7\nend\n"
    ));
    let op = load_errors_of(&format!(
        "{MEMBERS}namespace {ns}o\n  import anthill.prelude.{{Int64, Bool}}\n  \
         operation viaOp() -> Bool = {body} = 7\nend\n"
    ));
    [("rule body", rule), ("operation body", op)]
}

/// A member named through a path to its sort is read in a rule body as the one-segment
/// spelling is: `7 = zm.S.seven` holds as `7 = S.seven` does. It was refused, "seven …
/// unresolved", because the walk records the sort a path names as its type value. An
/// alias's path gives the alias's bracket as the receiver's type, as `CA.empty` does.
#[test]
fn a_member_by_a_path_to_its_sort_is_read_in_a_rule_body() {
    assert_eq!(holds("k40m", "7 = zm.S.seven"), 1);
    assert_eq!(holds("k40n", "8 = zm.S.seven"), 0);
    assert_eq!(holds("k40o", "7 = ..zm.S.seven"), 1);
    assert_eq!(holds("k40p", "0 = zm.CA.zero"), 1);
    let bracket = load_errors_of(&format!(
        "{MEMBERS}namespace k40q\n  import anthill.prelude.{{Int64, String}}\n  \
         rule r(?v) :- ?v = zm.CA.empty, ?v = zm.Box.bx(\"s\")\nend\n"
    ));
    assert_refused_naming(&bracket, &["expected Box[V = String], got Box[V = Int64]"], "the alias's bracket");
    let open = load_errors_of(&format!(
        "{MEMBERS}namespace k40r\n  import anthill.prelude.{{Int64, String}}\n  \
         rule r(?v) :- ?v = zm.Box.empty, ?v = zm.Box.bx(\"s\")\nend\n"
    ));
    assert!(open.is_empty(), "no bracket, no binding: {open:#?}");
}

/// A member a sort does not declare is refused about that sort, once, in both bodies. A
/// member reached past the qualified names — through a sort the sort provides, through an
/// alias — is no such member, and the rest of the path is read off it.
#[test]
fn a_member_a_sort_does_not_declare_is_refused_once() {
    for (body, sort, missing) in [("zm.Color.nosuch", "zm.Color", "nosuch"), ("zm.P.x", "zm.P", "x")] {
        for (at, errs) in both_bodies_over_members("k40s", body) {
            refused_once(
                &errs,
                &[&format!("`{body}` names nothing: the sort `{sort}` declares no `{missing}`")],
                &format!("{at}: {body}"),
            );
        }
    }
    for (at, errs) in both_bodies_over_members("k40t", "Int64.compare") {
        assert!(errs.iter().all(|e| !e.contains("names nothing")), "{at}: provided: {errs:#?}");
    }
    // Past the provided member, the rest is read off it.
    for (at, errs) in both_bodies_over_members("k40t2", "Int64.compare.x") {
        refused_once(&errs, &["compare"], at);
    }
}

/// A path whose prefix names a value reads the rest off that value, as the operation body
/// does: `3 = zm.S.mk.x` holds in a rule body and `4 = zm.S.mk.x` does not; a field the
/// value's sort lacks is refused about the sort; a constructor's field by a path is read
/// off its bare instance, refused once in an operation body, where that instance is an
/// incomplete construction; an operation's parameter by a path is no member.
#[test]
fn a_path_with_a_value_prefix_is_read_off_the_value() {
    assert_eq!(holds("k40u", "3 = zm.S.mk.x"), 1);
    assert_eq!(holds("k40v", "4 = zm.S.mk.x"), 0);
    for (at, errs) in both_bodies_over_members("k40w", "zm.S.mk.z") {
        refused_once(&errs, &["zm.P.z", "no such member"], at);
    }
    let [(_, rule), (_, op)] = both_bodies_over_members("k40x", "zm.Color.blue.n");
    assert!(rule.is_empty(), "the bare instance's field in a rule body: {rule:#?}");
    refused_once(&op, &["`blue` is constructed without its field `n`"], "operation body");
    for (at, errs) in both_bodies_over_members("k40y", "zm.Box.wrapIt.x") {
        refused_once(&errs, &["wrapIt"], at);
    }
}

/// An `internal` operation by a path is refused in a rule body as in an operation body.
/// Read whole, as the relation and operation readings look a name up, it loaded.
#[test]
fn an_internal_operation_by_a_path_is_refused_in_a_rule_body() {
    for (at, errs) in both_bodies_over_members("k40z", "zm.S.sec") {
        refused_once(&errs, &["'zm.S.sec' is internal to 'zm.S'"], at);
    }
}

/// An equation whose replacement the loader refused is not fired into the typer, which
/// reported the same text again at its call; a path through a hidden prefix is refused
/// once, as the access to that prefix, in a replacement and in a fact's argument.
#[test]
fn a_refused_replacement_is_reported_once() {
    for (at, rule, tokens) in [
        ("a compound", "rule f(?x) <=> nosuchfn(?x) @[simp]", &["`nosuchfn` names nothing"][..]),
        ("a path", "rule f(?x) <=> zz.inner.nosuch @[simp]", &["`zz.inner.nosuch` names nothing"][..]),
        ("a hidden path", "rule f(?x) <=> zz.Q.Sec @[simp]", &["'zz.Q.Sec' is internal to 'zz.Q'"][..]),
        ("a hidden prefix", "rule f(?x) <=> zz.Q.hidden.x @[simp]", &["'zz.Q.hidden' is internal to 'zz.Q'"][..]),
    ] {
        for caller in ["", "\n  operation g() -> Int64 = f(1)"] {
            let errs = load_errors_of(&format!(
                "{DECL}namespace k40fire\n  import anthill.prelude.Int64\n  \
                 operation f(x: Int64) -> Int64\n  {rule}{caller}\nend\n"
            ));
            assert_eq!(errs.len(), 1, "{at}, caller {:?}: {errs:#?}", !caller.is_empty());
            assert_refused_naming(&errs, tokens, at);
        }
    }
    let fact = load_errors_of(&format!(
        "{DECL}namespace k40fact\n  import anthill.prelude.Int64\n  fact holds(zz.Q.hidden.x)\nend\n"
    ));
    refused_once(&fact, &["'zz.Q.hidden' is internal to 'zz.Q'"], "a fact's argument");
}

// ── a rule body's data slots: a `<=>` operand, a `let`, an argument of a goal or a term ──

/// A dotted name in a rule body's data slot is judged as a clause head judges one. An
/// `internal` name by a path is refused — `?v <=> zz.Q.sec` ran the hidden operation from
/// outside its sort and answered 1 — and a name a namespace or a sort declares nowhere
/// names nothing, once, where resolution fails (`zz.inner.nosuch.y` as `zz.inner.nosuch`).
/// A namespace is data a term may hold, as in a head.
#[test]
fn a_dotted_name_in_a_rule_body_data_slot_is_judged_as_in_a_head() {
    let hidden_op = "namespace zh\n  import anthill.prelude.Int64\n  sort Q\n    \
                     internal operation sec() -> Int64 = 1\n    rule inside(?v) :- ?v <=> Q.sec\n  end\nend\n";
    for slot in ["?v <=> {p}", "let ?v = {p}", "?v <=> box(v: {p})", "foo({p}), ?v <=> 0"] {
        let rule = |p: &str| {
            format!(
                "{DECL}{hidden_op}namespace k40d{}\n  import anthill.prelude.Int64\n  fact foo(1)\n  \
                 entity box(v: Int64)\n  rule r(?v) :- {}\nend\n",
                slot.len(),
                slot.replace("{p}", p)
            )
        };
        for (path, tokens) in [
            ("zh.Q.sec", &["'zh.Q.sec' is internal to 'zh.Q'"][..]),
            ("zz.Q.hidden.x", &["'zz.Q.hidden' is internal to 'zz.Q'"][..]),
            ("zz.inner.nosuch.y", &["`zz.inner.nosuch` names nothing", "the namespace `zz.inner`"][..]),
            ("zz.Color.nosuch", &["the sort `zz.Color` declares no `nosuch`"][..]),
            ("nosuch.x", &["no `nosuch` is visible"][..]),
        ] {
            refused_once(&load_errors_of(&rule(path)), tokens, &format!("{slot} at {path}"));
        }
        let namespace = load_errors_of(&rule("zz.inner"));
        assert!(namespace.is_empty(), "{slot}: a namespace is data: {namespace:#?}");
    }
    // Inside its sort, the hidden operation is its own and answers.
    let mut kb = crate::common::load_kb_with(&format!("{DECL}{hidden_op}"));
    assert_eq!(crate::common::query_unary(&mut kb, "zh.Q.inside").len(), 1);
}

/// The bound: a member read through a requirement's name is no undeclared member — the
/// name is a type parameter, read through what it requires — and the readings with an
/// answer keep it: a nullary operation by a path is its value, a relation by a path its
/// name, a dotted name in a goal's argument still matches the fact that holds it.
#[test]
fn data_slot_readings_with_an_answer_keep_it() {
    let errs = load_errors_of(
        "namespace k40req\n  import anthill.prelude.{Int64, Additive, Multiplicative}\n  \
         import anthill.prelude.algebra.{Ring}\n  sort G\n    sort F = ?\n    requires R: Ring[F]\n    \
         fact holdsF(R.one)\n    rule b1(?v) :- ?v <=> R.zero\n    rule b2(1) :- holdsF(R.one)\n  end\nend\n",
    );
    assert!(errs.is_empty(), "read through the requirement: {errs:#?}");
    let mut kb = crate::common::load_kb_with(&format!(
        "{MEMBERS}namespace k40keep\n  import anthill.prelude.Int64\n  fact holds(zm.S.seven)\n  \
         rule seven(?v) :- ?v <=> zm.S.seven\n  rule matched(1) :- holds(zm.S.seven)\nend\n"
    ));
    let seven = crate::common::query_unary(&mut kb, "k40keep.seven");
    assert_eq!(seven.len(), 1);
    assert!(matches!(seven[0].0, Value::Int(7)), "{seven:?}");
    assert_eq!(crate::common::query_unary(&mut kb, "k40keep.matched").len(), 1);
}
