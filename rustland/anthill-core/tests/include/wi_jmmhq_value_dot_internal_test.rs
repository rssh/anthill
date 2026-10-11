//! WI-20261008-JMMHQ — a dot on a value reaches an `internal` operation only from where
//! its name is visible (kernel-language.md §8.6).
//!
//! THE RULE. `b.peek()` is the call `peek(b)` of the operation the dot resolves to, and
//! an `internal` operation is hidden from it where its written name would be: refused
//! outside the declaring scope, reached inside it. The question is asked of the operation
//! the dot settled on, so it holds on every rung that finds one — the receiver's own
//! member, a spec's operation reached through `provides`, through `requires` or through a
//! clause on a type parameter, and the parent sort's — and of the receiver's own member
//! before a dispatch decision can hand the call on from it. A hidden member is refused,
//! and is not passed over for a visible one of its name.
//!
//! It is asked from the scope the dot's TEXT is written in. For the text of a rewrite
//! that is the rule's scope, wherever the rule fires: a dot there is resolved at the
//! call it rewrites, once its receiver has a type, and is still the rule's text.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with a refused row measures
//! the fixture.
//!
//! CONTROLS — measured, each piece backed out on its own.
//!
//!   both checks (`hidden_dot_member` answering nothing) — FAIL, each loading clean:
//!     the_receivers_own_internal_member_is_hidden_outside_its_sort
//!     the_parent_sorts_internal_member_is_hidden_from_a_variant_receiver
//!     a_provided_specs_internal_operation_is_hidden
//!     a_constraining_specs_internal_operation_is_hidden
//!     a_required_specs_internal_operation_is_reported_as_hidden (refused either way; the
//!       refusal is the argument's without the check — see the row)
//!     a_lambda_is_written_in_its_operations_scope
//!     top_level_code_is_outside_the_sort
//!     a_rule_outside_the_sort_is_refused_naming_its_scope
//!     a_receiver_typed_by_an_alias_is_asked_the_same
//!     a_same_named_member_of_the_callers_sort_does_not_lend_its_visibility
//!     a_hidden_operation_is_not_passed_over_for_a_field_of_its_name
//!     a_hidden_member_is_not_passed_over_for_the_spec_operation_it_backs
//!     a_hidden_member_of_a_spec_typed_receiver_is_not_passed_over_either
//!     a_rewrite_written_outside_the_sort_is_refused_naming_the_rules_scope
//!     an_argument_of_a_rewritten_call_is_the_callers_text
//!     what_a_macro_hands_back_is_not_the_rules_text
//!   the check on the operation the ladder settled on, alone — FAIL: the parent-sort row
//!   and the three spec rows. The rows on the receiver's own member pass: the check
//!   beside it answers them.
//!   the check on the receiver's own member, alone — FAIL:
//!     a_hidden_member_of_a_spec_typed_receiver_is_not_passed_over_either
//!   The other own-member rows pass: there the member is the operation settled on.
//!
//!   the rule's scope on the text a rewrite splices (`reparent_spliced` stamping none),
//!   and separately its carry through a rebuild of the node (`rebuilt_expr`), and
//!   separately the dot frame reading the checked code's scope instead — FAIL:
//!     a_rewrite_written_in_the_sort_reaches_its_internal_members
//!     a_rewrite_written_outside_the_sort_is_refused_naming_the_rules_scope
//!     a_dot_rule_carries_its_sorts_scope
//!     an_argument_of_a_rewritten_call_is_the_callers_text (the rule's own dot is
//!       refused first)
//!     a_rewrite_of_a_rewrites_text_is_its_own_rules
//!     a_stored_rewrite_is_still_its_rules_when_typed_again
//!   the `FieldOf` reduction's site reading the checked code's scope, and separately the
//!   walk from a node a pass built to the text it was built from
//!   (`NodeOccurrence::text_scope`) — FAIL:
//!     a_rewrite_written_in_the_sort_reaches_its_internal_members (its field case)
//!     a_stored_rewrite_is_still_its_rules_when_typed_again
//!   the scope left out of a deep copy of the node — FAIL:
//!     a_stored_rewrite_is_still_its_rules_when_typed_again
//!
//!   NOT DRIVEN: the dot on a receiver that denotes a sort asks through the same reader
//!   (`written_scope`), and no row fails with the checked code's scope put back there. A
//!   rule's text cannot write a type as a receiver — `(Box).m()` names nothing in it —
//!   so that dot is never a rewrite's text today.
//!
//!   PASS under every back-out, by design — what the checks must not refuse:
//!     the_receivers_own_internal_member_is_reached_inside_its_sort
//!     the_parent_sorts_internal_member_is_reached_inside_it
//!     a_specs_internal_operation_is_reached_inside_the_spec
//!     a_nested_sort_and_a_second_entry_are_inside
//!     a_rule_inside_the_sort_reaches_it
//!     a_visible_member_backing_a_hidden_spec_operation_is_the_one_asked_about

use anthill_core::eval::Value;
use anthill_core::kb::typing::{type_check_sorts, Loaded};

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, load_stdlib_kb_with_source, query_unary,
    rendered_load_errors, run_int64,
};

/// `lib.<ns>.Box[V]` with an `internal` operation, `inside` written in the sort beside
/// it and `outside` in another namespace.
fn boxed(ns: &str, inside: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n    internal operation peek(b: Box[V]) -> V = b.v\n{inside}\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.Box\n{outside}\nend\n"
    )
}

/// `lib.<ns>.Desc`, a spec whose `label` is `internal` and defaulted, `Twig` providing
/// it with no member of its own, `inside` written in the spec and `outside` elsewhere.
fn spec(ns: &str, inside: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  sort Desc\n    sort T = ?\n    internal operation label(x: T) -> Int64 = 5\n{inside}\n  end\n  sort Twig\n    entity twig\n    provides Desc[T = Twig]\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.{{Desc, Twig}}\n{outside}\nend\n"
    )
}

/// The load of `src` is refused because `member`, internal to `owner`, is reached from
/// `scope`.
#[track_caller]
fn assert_hidden(src: &str, member: &str, owner: &str, scope: &str) {
    assert_refused_naming(
        &load_errors_of(src),
        &[&format!(
            "'{member}' is internal to '{owner}' and cannot be referenced from scope '{scope}'"
        )],
        scope,
    );
}

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

// ── the rungs ───────────────────────────────────────────────────────────────

#[test]
fn the_receivers_own_internal_member_is_hidden_outside_its_sort() {
    assert_hidden(
        &boxed(
            "jmmhqown",
            "",
            "  operation go() -> Int64 =\n    let b = Box.mk(4)\n    b.peek()",
        ),
        "peek",
        "lib.jmmhqown.Box",
        "test.jmmhqown.go",
    );
}

#[test]
fn the_receivers_own_internal_member_is_reached_inside_its_sort() {
    assert_runs(
        &boxed(
            "jmmhqin",
            "    operation inside(b: Box[V]) -> V = b.peek()",
            "  operation go() -> Int64 =\n    let b = Box.mk(4)\n    b.inside()",
        ),
        "test.jmmhqin.go",
        4,
    );
}

/// A variant-typed receiver reaches its sort's members through the parent-sort rung.
fn colour(ns: &str, inside: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  sort Colour\n    entity red\n    entity green\n    internal operation shout(c: Colour) -> Int64 = 9\n{inside}\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.Colour\n{outside}\nend\n"
    )
}

#[test]
fn the_parent_sorts_internal_member_is_hidden_from_a_variant_receiver() {
    assert_hidden(
        &colour(
            "jmmhqparent",
            "",
            "  operation go(r: Colour.red) -> Int64 = r.shout()",
        ),
        "shout",
        "lib.jmmhqparent.Colour",
        "test.jmmhqparent.go",
    );
}

#[test]
fn the_parent_sorts_internal_member_is_reached_inside_it() {
    assert_runs(
        &colour(
            "jmmhqparentin",
            "    operation loud(r: Colour.red) -> Int64 = r.shout()\n    operation both() -> Int64 = loud(red)",
            "  operation go() -> Int64 = Colour.both()",
        ),
        "test.jmmhqparentin.go",
        9,
    );
}

#[test]
fn a_provided_specs_internal_operation_is_hidden() {
    assert_hidden(
        &spec(
            "jmmhqprov",
            "",
            "  operation go(t: Twig) -> Int64 = t.label()",
        ),
        "label",
        "lib.jmmhqprov.Desc",
        "test.jmmhqprov.go",
    );
}

#[test]
fn a_constraining_specs_internal_operation_is_hidden() {
    assert_hidden(
        &spec(
            "jmmhqparam",
            "",
            "  operation go[X](x: X) -> Int64 requires Desc[T = X] = x.label()",
        ),
        "label",
        "lib.jmmhqparam.Desc",
        "test.jmmhqparam.go",
    );
}

/// Both spec rungs, written in the spec: a concrete receiver, and a type parameter the
/// operation's own clause constrains.
#[test]
fn a_specs_internal_operation_is_reached_inside_the_spec() {
    assert_runs(
        &spec(
            "jmmhqspecin",
            "    operation viaTwig(t: Twig) -> Int64 = t.label()\n    operation viaParam[X](x: X) -> Int64 requires Desc[T = X] = x.label()",
            "  operation go() -> Int64 = Desc.viaTwig(Twig.twig()) + Desc.viaParam(Twig.twig())",
        ),
        "test.jmmhqspecin.go",
        10,
    );
}

/// The rung a spec-typed receiver reaches a required spec's operation through. This
/// program is refused without the check too — the receiver is typed at the spec and the
/// operation takes the spec's carrier — so what the check changes is which refusal the
/// author reads: the member they may not name, and not an argument of a call they may
/// not make.
#[test]
fn a_required_specs_internal_operation_is_reported_as_hidden() {
    assert_hidden(
        "namespace lib.jmmhqreq\n  sort Walk\n    sort C = ?\n    internal operation step(c: C) -> Int64 = 1\n  end\n  sort Coll\n    sort C = ?\n    requires Walk[C = C]\n    operation size(c: C) -> Int64\n  end\n  sort Bag\n    entity bag\n    provides Walk[C = Bag]\n    provides Coll[C = Bag]\n    operation size(c: Bag) -> Int64 = 0\n  end\nend\nnamespace test.jmmhqreq\n  import lib.jmmhqreq.{Walk, Coll, Bag}\n  operation go(c: Coll[C = Bag]) -> Int64 = c.step()\nend\n",
        "step",
        "lib.jmmhqreq.Walk",
        "test.jmmhqreq.go",
    );
}

// ── where the dot is written ────────────────────────────────────────────────

#[test]
fn a_lambda_is_written_in_its_operations_scope() {
    assert_hidden(
        &boxed(
            "jmmhqlam",
            "",
            "  operation go() -> Int64 =\n    let b = Box.mk(4)\n    let f = lambda (x: Box[Int64]) -> x.peek()\n    f(b)",
        ),
        "peek",
        "lib.jmmhqlam.Box",
        "test.jmmhqlam.go",
    );
}

#[test]
fn top_level_code_is_outside_the_sort() {
    assert_hidden(
        "namespace lib.jmmhqtop\n  sort Box\n    entity mk(v: Int64)\n    internal operation peek(b: Box) -> Int64 = b.v\n  end\nend\nimport lib.jmmhqtop.Box\noperation jmmhqTopPeek(b: Box) -> Int64 = b.peek()\n",
        "peek",
        "lib.jmmhqtop.Box",
        "jmmhqTopPeek",
    );
}

/// A sort nested in `Box` and a second entry of `Box` are both inside its scope.
#[test]
fn a_nested_sort_and_a_second_entry_are_inside() {
    assert_runs(
        &boxed(
            "jmmhqnest",
            "    sort Inner\n      entity inn\n      operation viaInner(b: Box[Int64]) -> Int64 = b.peek()\n    end",
            "  operation go() -> Int64 = Box.Inner.viaInner(Box.mk(4))",
        ),
        "test.jmmhqnest.go",
        4,
    );
    let second_entry = format!(
        "{}namespace lib.jmmhqentry.Box\n  operation viaEntry(b: Box[Int64]) -> Int64 = b.peek()\nend\n",
        boxed(
            "jmmhqentry",
            "",
            "  operation go() -> Int64 = Box.viaEntry(Box.mk(4))",
        )
    );
    assert_runs(&second_entry, "test.jmmhqentry.go", 4);
}

/// `Box` for a rule body: the receiver is typed by the field it is read from.
fn held(ns: &str, inside: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  sort Box\n    import anthill.prelude.PartialEq.{{eq}}\n    entity mk(v: Int64)\n    entity holder(b: Box, w: Int64)\n    internal operation peek(b: Box) -> Int64 = 5\n{inside}\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.Box\n  import anthill.prelude.PartialEq.{{eq}}\n{outside}\nend\n"
    )
}

#[test]
fn a_rule_outside_the_sort_is_refused_naming_its_scope() {
    assert_hidden(
        &held(
            "jmmhqrout",
            "",
            "  rule peeked(?w) :- Box.holder(b: ?b, w: ?w), eq(?w, ?b.peek())",
        ),
        "peek",
        "lib.jmmhqrout.Box",
        "test.jmmhqrout",
    );
}

#[test]
fn a_rule_inside_the_sort_reaches_it() {
    let mut kb = load_kb_with(&held(
        "jmmhqrin",
        "    fact holder(b: mk(v: 1), w: 5)\n    fact holder(b: mk(v: 2), w: 6)\n    rule peeked(?w) :- holder(b: ?b, w: ?w), eq(?w, ?b.peek())",
        "",
    ));
    let answers = query_unary(&mut kb, "lib.jmmhqrin.Box.peeked");
    assert!(
        matches!(answers.as_slice(), [(Value::Int(5), _)]),
        "the holder whose `w` is what `peek` answers, and no other: {answers:?}"
    );
}

#[test]
fn a_receiver_typed_by_an_alias_is_asked_the_same() {
    assert_hidden(
        &boxed(
            "jmmhqalias",
            "",
            "  sort CA = Box[V = Int64]\n  operation go(c: CA) -> Int64 = c.peek()",
        ),
        "peek",
        "lib.jmmhqalias.Box",
        "test.jmmhqalias.go",
    );
}

/// The member is found by the receiver's sort, and visibility is asked of that member:
/// the caller's own `internal peek` is reached on its own value and lends nothing to a
/// `Box`.
#[test]
fn a_same_named_member_of_the_callers_sort_does_not_lend_its_visibility() {
    let mine = |ns: &str, go: &str| {
        boxed(
            ns,
            "",
            &format!(
                "  sort Mine\n    entity mine\n    internal operation peek(m: Mine) -> Int64 = 3\n    operation go() -> Int64 = {go}\n  end"
            ),
        )
    };
    assert_runs(&mine("jmmhqmine", "mine().peek()"), "test.jmmhqmine.Mine.go", 3);
    assert_hidden(
        &mine("jmmhqtheirs", "Box.mk(4).peek()"),
        "peek",
        "lib.jmmhqtheirs.Box",
        "test.jmmhqtheirs.Mine.go",
    );
}

// ── one name, two members ───────────────────────────────────────────────────

/// An operation is found before a field of its name. Hidden, it is not passed over for
/// the field: the dot is refused, as the frame's field read refuses a field an `internal`
/// constructor declares beside a public one.
#[test]
fn a_hidden_operation_is_not_passed_over_for_a_field_of_its_name() {
    let src = |ns: &str, outside: &str| {
        format!(
            "namespace lib.{ns}\n  sort Box\n    entity mk(v: Int64)\n    internal operation v(b: Box) -> Int64 = 100\n    operation inside(b: Box) -> Int64 = b.v\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.Box\n{outside}\nend\n"
        )
    };
    assert_hidden(
        &src("jmmhqfield", "  operation go(b: Box) -> Int64 = b.v"),
        "v",
        "lib.jmmhqfield.Box",
        "test.jmmhqfield.go",
    );
    assert_runs(
        &src(
            "jmmhqfieldin",
            "  operation go() -> Int64 = Box.inside(Box.mk(4))",
        ),
        "test.jmmhqfieldin.go",
        100,
    );
}

/// `Leaf`'s own `label` is `internal` and backs the public `Desc.label`. The dot takes
/// the receiver's own member, which is hidden; the spec's operation is the name an
/// outside caller may write, and it reaches the same implementation.
#[test]
fn a_hidden_member_is_not_passed_over_for_the_spec_operation_it_backs() {
    let src = |ns: &str, go: &str| {
        format!(
            "namespace lib.{ns}\n  sort Desc\n    sort T = ?\n    operation label(x: T) -> Int64\n  end\n  sort Leaf\n    entity leaf\n    provides Desc[T = Leaf]\n    internal operation label(x: Leaf) -> Int64 = 7\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.{{Desc, Leaf}}\n  operation go() -> Int64 = {go}\nend\n"
        )
    };
    assert_hidden(
        &src("jmmhqbacks", "Leaf.leaf().label()"),
        "label",
        "lib.jmmhqbacks.Leaf",
        "test.jmmhqbacks.go",
    );
    assert_runs(&src("jmmhqbacksnamed", "Desc.label(Leaf.leaf())"), "test.jmmhqbacksnamed.go", 7);
}

/// The same on a receiver typed at a spec that carries its own members: there the dot
/// hands the call to the spec operation the member backs, for the value to decide, and
/// that hand-over is not a way past a hidden member either. The named call answers.
#[test]
fn a_hidden_member_of_a_spec_typed_receiver_is_not_passed_over_either() {
    let src = |ns: &str, call: &str| {
        format!(
            "namespace lib.{ns}\n  sort Desc\n    sort T = ?\n    operation describe(x: T) -> Int64 = 1\n  end\n  sort Coll\n    sort E = ?\n    provides Desc[T = Self]\n    internal operation describe(x: Self) -> Int64 = 7\n  end\n  sort Leaf\n    entity leaf\n    provides Coll[E = Int64]\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.{{Desc, Coll, Leaf}}\n  operation via(c: Coll) -> Int64 = {call}\n  operation go() -> Int64 = via(Leaf.leaf())\nend\n"
        )
    };
    assert_hidden(
        &src("jmmhqabstract", "c.describe()"),
        "describe",
        "lib.jmmhqabstract.Coll",
        "test.jmmhqabstract.via",
    );
    assert_runs(
        &src("jmmhqabstractnamed", "Desc.describe(c)"),
        "test.jmmhqabstractnamed.go",
        7,
    );
}

/// The other way round: the member the dot takes is public and the spec operation it
/// backs is `internal`. Nothing hidden is named, and the dot answers.
#[test]
fn a_visible_member_backing_a_hidden_spec_operation_is_the_one_asked_about() {
    assert_runs(
        "namespace lib.jmmhqpub\n  sort Desc\n    sort T = ?\n    internal operation label(x: T) -> Int64 = 5\n  end\n  sort Leaf\n    entity leaf\n    provides Desc[T = Leaf]\n    operation label(x: Leaf) -> Int64 = 7\n  end\nend\nnamespace test.jmmhqpub\n  import lib.jmmhqpub.{Desc, Leaf}\n  operation go() -> Int64 = Leaf.leaf().label()\nend\n",
        "test.jmmhqpub.go",
        7,
    );
}

// ── the text of a rewrite ───────────────────────────────────────────────────
//
// A rewrite's right-hand side is typed where it fires, and a dot in it is resolved
// there, once its receiver has a type. Its text is still the rule's: visibility is
// asked from the scope the rule is written in, as it is for a name the rule writes.

/// `lib.<ns>.Box` with an `internal` operation and an `internal` constructor's field,
/// `inside` written in the sort and `outside` in another namespace.
fn rewritten(ns: &str, inside: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  sort Box\n    internal entity mk(v: Int64)\n    operation make(v: Int64) -> Box = mk(v)\n    internal operation peek(b: Box) -> Int64 = 4\n    internal operation plus(b: Box, x: Int64) -> Int64 = x + 4\n{inside}\n  end\nend\nnamespace test.{ns}\n  import lib.{ns}.Box\n{outside}\nend\n"
    )
}

const CALLS_OPEN: &str = "  operation go() -> Int64 = Box.open(Box.make(1))";

/// A rule written in the sort reaches the sort's `internal` members with a dot from
/// every call it rewrites: an operation, and a field of an `internal` constructor.
#[test]
fn a_rewrite_written_in_the_sort_reaches_its_internal_members() {
    for (ns, rhs, expected) in [("jmmhqrwop", "?b.peek()", 4), ("jmmhqrwfield", "?b.v", 1)] {
        let inside =
            format!("    operation open(b: Box) -> Int64\n    rule open(?b) <=> {rhs} @[simp]");
        assert_runs(
            &rewritten(ns, &inside, CALLS_OPEN),
            &format!("test.{ns}.go"),
            expected,
        );
    }
}

/// The same rules written in another namespace are refused, and the refusal names the
/// scope the rule is written in — not the operation whose call it rewrote.
#[test]
fn a_rewrite_written_outside_the_sort_is_refused_naming_the_rules_scope() {
    for (ns, rhs, member) in [("jmmhqrwoutop", "?b.peek()", "peek"), ("jmmhqrwoutfield", "?b.v", "v")] {
        let outside = format!(
            "  operation open(b: Box) -> Int64\n  rule open(?b) <=> {rhs} @[simp]\n  operation go() -> Int64 = open(Box.make(1))"
        );
        assert_hidden(
            &rewritten(ns, "", &outside),
            member,
            &format!("lib.{ns}.Box"),
            &format!("test.{ns}"),
        );
    }
}

/// A dot rule declared in the receiver's sort is the third place a rewrite fires, and
/// the one that types the call's arguments under the rewritten text.
#[test]
fn a_dot_rule_carries_its_sorts_scope() {
    const DOT_RULE: &str = "    rule dr: dot_apply(?e, special, ?x) <=> ?e.plus(?x) @[simp]";
    assert_runs(
        &rewritten(
            "jmmhqdotrule",
            DOT_RULE,
            "  operation go() -> Int64 = Box.make(1).special(3)",
        ),
        "test.jmmhqdotrule.go",
        7,
    );
}

/// The arguments of the rewritten call are the caller's text, typed under the rule's:
/// a hidden member the caller writes there is still asked from the caller's scope.
#[test]
fn an_argument_of_a_rewritten_call_is_the_callers_text() {
    assert_hidden(
        &rewritten(
            "jmmhqdotarg",
            "    rule dr: dot_apply(?e, special, ?x) <=> ?e.plus(?x) @[simp]",
            "  operation go() -> Int64 =\n    let b = Box.make(1)\n    b.special(b.peek())",
        ),
        "peek",
        "lib.jmmhqdotarg.Box",
        "test.jmmhqdotarg.go",
    );
}

/// A rewrite fired on the text of another: the innermost rule's scope is the one asked.
/// `openOut` is rewritten in `test` to the public `Box.open`, which `Box` rewrites to a
/// dot on its own `internal` operation.
#[test]
fn a_rewrite_of_a_rewrites_text_is_its_own_rules() {
    assert_runs(
        &rewritten(
            "jmmhqnested",
            "    operation open(b: Box) -> Int64\n    rule open(?b) <=> ?b.peek() @[simp]",
            "  operation openOut(b: Box) -> Int64\n  rule openOut(?b) <=> Box.open(?b) @[simp]\n  operation go() -> Int64 = openOut(Box.make(1))",
        ),
        "test.jmmhqnested.go",
        4,
    );
}

/// The typed body is stored with the rewrite's text in it, and is typed again from
/// there: by a later load's sweep, and on a copy of the knowledge base. The field read
/// is then a call of `field_access` with no dot left to ask, and the text it was
/// lowered from is still its rule's.
///
/// NOT THE RECIPE, BY NAME: the file is typed again by hand, from its own `LoadResult`.
#[test]
fn a_stored_rewrite_is_still_its_rules_when_typed_again() {
    let inside = "    operation open(b: Box) -> Int64\n    rule open(?b) <=> ?b.v @[simp]";
    let (mut kb, result) =
        load_stdlib_kb_with_source(&rewritten("jmmhqretype", inside, CALLS_OPEN));
    let mut copy = kb.deep_clone().expect("a KB with a user file copies");
    for (which, kb) in [("the KB", &mut kb), ("its copy", &mut copy)] {
        let mut again = type_check_sorts(kb, result.loaded());
        again.extend(type_check_sorts(kb, Loaded::nothing()));
        let again = rendered_load_errors(again);
        assert!(again.is_empty(), "{which}, typed again: {again:?}");
    }
}

/// A macro hands back what it was handed. Where that is the caller's own occurrence,
/// it is the caller's text still, though it now stands where the rule's macro call
/// stood: a hidden member the caller reaches in it is asked from the caller's scope.
/// (Only a node the macro built is re-parented onto the rule's text; this row is what
/// turns if one handed back ever is.)
#[test]
fn what_a_macro_hands_back_is_not_the_rules_text() {
    assert_hidden(
        "namespace lib.jmmhqmacro\n  import anthill.reflect.{NodeOccurrence}\n  sort Box\n    entity mk(v: Int64)\n    internal operation peek(b: Box) -> Int64 = 4\n    operation pass(r: NodeOccurrence, x: NodeOccurrence) -> NodeOccurrence = x\n    rule dr: dot_apply(?e, relay, ?x) <=> pass(?e, ?x) @[simp]\n  end\nend\nnamespace test.jmmhqmacro\n  import lib.jmmhqmacro.Box\n  operation go() -> Int64 =\n    let b = Box.mk(1)\n    b.relay(b.peek())\nend\n",
        "peek",
        "lib.jmmhqmacro.Box",
        "test.jmmhqmacro.go",
    );
}
