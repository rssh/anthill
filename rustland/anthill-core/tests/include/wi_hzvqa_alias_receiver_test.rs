//! WI-20261008-HZVQA — a member reached through a type alias is reached at the parameters
//! the alias fixes.
//!
//! THE RULE. Over `sort CA = Box[V = Int64]`, `CA.wrap(…)` is the call
//! `Box[V = Int64].wrap(…)` makes — written, or through a name a `let` bound to the alias
//! — a construction `CA.mk(…)` is `Box[V = Int64].mk(…)`, and a rule cited `CA.rel` is
//! cited as `Box[V = Int64].rel` is. A parameter the alias leaves open is left to the
//! call, as a written bracket leaves it, and an alias that fixes nothing says nothing.
//! A receiver names the instance the call is at and says nothing more of the result.
//!
//! BEFORE. The member path was read through the alias to the sort and the bindings were
//! dropped: `operation go() -> String = CA.wrap("s")` loaded and answered `"s"`.
//!
//! EVERY ROW HAS ITS OWN SOURCE, as in `wi_papx0_dot_receiver_split_test`.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the loader's alias receiver (`Loader::alias_recv_type_of` answering `None`) — FAIL:
//!     a_written_call_through_an_alias_is_at_its_parameters
//!     a_chain_of_aliases_fixes_what_each_link_fixes
//!     a_partial_alias_leaves_its_open_parameter_to_the_call
//!     an_alias_written_positionally_or_fixing_a_constant_is_at_it
//!     a_callee_bracket_must_agree_with_the_alias
//!     the_alias_types_the_result_of_a_call_without_arguments
//!     a_qualified_path_through_an_alias_carries_it
//!     an_alias_that_names_the_enclosing_parameter_is_at_that_parameter
//!     a_spec_called_through_an_alias_is_at_its_members
//!     an_alias_that_fixes_a_requirement_slot_selects_its_provider
//!     a_rule_body_call_through_an_alias_is_at_its_parameters
//!     a_rule_body_goal_through_an_alias_is_checked_and_answers
//!     a_paren_less_goal_through_an_alias_is_the_applied_goal
//!     a_rule_cited_through_an_alias_is_cited_at_its_parameters
//!     a_name_another_rung_answered_takes_no_receiver (its visible half)
//!     wi_papx0_dot_receiver_split_test::an_alias_denotes_what_it_stands_for
//!   the typer's (`denoted_sort_dot` taking no receiver from the alias) — FAIL, the
//!   let-bound halves of:
//!     a_let_bound_call_through_an_alias_is_at_its_parameters
//!     a_chain_of_aliases_fixes_what_each_link_fixes
//!     a_partial_alias_leaves_its_open_parameter_to_the_call
//!     an_alias_written_positionally_or_fixing_a_constant_is_at_it
//!     the_alias_types_the_result_of_a_call_without_arguments
//!     an_alias_that_names_the_enclosing_parameter_is_at_that_parameter
//!     a_spec_called_through_an_alias_is_at_its_members
//!     an_alias_that_fixes_a_requirement_slot_selects_its_provider
//!     wi_papx0_dot_receiver_split_test::an_alias_denotes_what_it_stands_for
//!   the bare citation's arm (`try_qualified_rule_ref` building the leaf always) — FAIL:
//!     a_rule_cited_through_an_alias_is_cited_at_its_parameters
//!   the chain reading of a paren-less callee (`alias_recv_type`'s first arm) — FAIL:
//!     a_paren_less_goal_through_an_alias_is_the_applied_goal
//!   the last-container reset in `read_path_through_aliases` — FAIL:
//!     an_alias_above_the_members_sort_is_not_its_receiver
//!   the callee test in `dotted_alias_receiver` — FAIL:
//!     a_name_another_rung_answered_takes_no_receiver
//!   the receiver riding a capture rule's reshaped redex (`fold_capture_redex` declining
//!   a redex that has one) — FAIL:
//!     a_capture_rule_fires_on_a_call_that_has_a_receiver
//!   the receiver left out of the result where it has bound the call (`check_apply_iter`
//!   comparing it with the declared return always) — FAIL:
//!     a_receiver_names_the_instance_and_not_the_result
//!   a constructor's receiver:
//!     not built by the loader (the `ApplyOrConstructor` frame reading none for an
//!     entity) — FAIL: a_constructor_called_with_a_receiver_is_at_its_parameters,
//!       a_constructor_with_a_receiver_types_its_arguments_as_any_other (its bracket
//!       halves: the bracket is then unread, and refused),
//!       wi_papx0_dot_receiver_split_test::a_bracket_on_a_constructor_binds_in_both_spellings,
//!       wi_w6jh0_companion_receiver_bracket_test::a_constructor_reads_its_receiver_bracket
//!     not built for a denoting receiver (`denoted_sort_dot`'s constructor arm) — FAIL:
//!       the let-bound and parenthesized halves of the first and third of those rows
//!     not read by the typer (`check_constructor_iter` without `seed_receiver_type_args`)
//!       — FAIL: the first, third and fourth of those rows
//!     read in a rule's compound expression (the frame's `lowering_rule_compound_expr`
//!       gate) — FAIL: a_constructor_in_a_rule_body_takes_no_receiver
//!
//!   PASS UNDER EVERY BACK-OUT, by design — the fence:
//!     an_alias_that_fixes_nothing_says_nothing — a bare alias had no bindings to drop.
//!
//!   `a_constructor_with_a_receiver_types_its_arguments_as_any_other` also guards the
//!   node's shape: the receiver is a slot of the constructor node, so the node's argument
//!   typing is untouched. MEASURED with a construction that has a receiver built as an
//!   application instead: its alias halves were refused too.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The sorts and aliases the rows are about, indented for a namespace body.
const DECLS: &str = r#"
  sort Box[V]
    entity mk(v: V)
    operation wrap(x: V) -> V = x
    operation same(x: V) -> Bool = true
    rule holds(?x: Int64) :- ?x <=> 1
  end
  sort Pair[L, R]
    entity pair(l: L, r: R)
    operation fst(a: L, b: R) -> L = a
    operation snd(a: L, b: R) -> R = b
  end
  sort CA = Box[V = Int64]
  sort CB = Box
  sort CC = CA
  sort IB = Box[Int64]
  sort PA = Pair[L = Int64]
  sort PB = PA[R = String]
"#;

fn source(ns: &str, body: &str) -> String {
    format!("namespace test.{ns}\n  import anthill.prelude.{{Type, Bool, Error}}\n{DECLS}\n{body}\nend\n")
}

/// Load, call `test.<ns>.go()`, and hand back its value as [`shown`].
fn run(ns: &str, body: &str) -> String {
    run_source(ns, &source(ns, body))
}

fn run_source(ns: &str, source: &str) -> String {
    let mut interp = interp_for(source);
    let value = interp
        .call(&format!("test.{ns}.go"), &[])
        .unwrap_or_else(|e| panic!("{ns}: {e:?}"));
    shown(value)
}

/// A value as the text the rows compare: an integer's digits, a string's contents.
fn shown(value: Value) -> String {
    match value {
        Value::Int(n) => n.to_string(),
        Value::Str(s) => s.to_string(),
        other => panic!("expected an Int64 or a String, got {other:?}"),
    }
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, body: &str) -> String {
    refusal_of(ns, &source(ns, body))
}

fn refusal_of(ns: &str, source: &str) -> String {
    let errs = try_load_kb_with(source)
        .err()
        .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
    format!("{errs:?}")
}

/// `go() -> <ret>` whose body is `call` on the receiver written out.
fn written(ret: &str, recv: &str, call: &str) -> String {
    format!("  operation go() -> {ret} = {recv}.{call}")
}

/// The same call through a name a `let` bound to the receiver.
fn bound(ret: &str, recv: &str, call: &str) -> String {
    format!("  operation go() -> {ret} =\n    let t = {recv}\n    t.{call}")
}

// ── the rule ────────────────────────────────────────────────────────────────

/// The ticket's program. Before, it loaded and answered `"s"`.
#[test]
fn a_written_call_through_an_alias_is_at_its_parameters() {
    let rendered = refusal("hzvqawritten", &written("String", "CA", "wrap(\"s\")"));
    assert!(
        rendered.contains("wrap.x (op-arg): expected Int64, got String"),
        "{rendered}"
    );
    // The twin with the type written out, which is what the alias stands for.
    let twin = refusal("hzvqatwin", &written("String", "Box[V = Int64]", "wrap(\"s\")"));
    assert!(twin.contains("wrap.x (op-arg): expected Int64, got String"), "{twin}");
    assert_eq!(
        run("hzvqagood", &written("Int64", "CA", "wrap(5)")),
        "5",
        "the argument the alias admits is taken"
    );
}

#[test]
fn a_let_bound_call_through_an_alias_is_at_its_parameters() {
    let rendered = refusal("hzvqabound", &bound("String", "CA", "wrap(\"s\")"));
    assert!(
        rendered.contains("wrap.x (op-arg): expected Int64, got String"),
        "{rendered}"
    );
    assert_eq!(run("hzvqaboundgood", &bound("Int64", "CA", "wrap(5)")), "5");
}

/// `sort CB = Box` fixes nothing, and a call through it is the call `Box.wrap` makes.
#[test]
fn an_alias_that_fixes_nothing_says_nothing() {
    for (ns, body) in [
        ("hzvqabarewritten", written("String", "CB", "wrap(\"s\")")),
        ("hzvqabarebound", bound("String", "CB", "wrap(\"s\")")),
    ] {
        assert_eq!(run(ns, &body), "s", "{ns}");
    }
}

/// `sort CC = CA` fixes what `CA` fixes; `sort PB = PA[R = String]` over
/// `sort PA = Pair[L = Int64]` fixes both.
#[test]
fn a_chain_of_aliases_fixes_what_each_link_fixes() {
    type Spelling = fn(&str, &str, &str) -> String;
    for (tag, spell) in [("w", written as Spelling), ("b", bound as Spelling)] {
        for (ns, ret, recv, call, site) in [
            ("chain", "String", "CC", "wrap(\"s\")", "wrap.x (op-arg): expected Int64, got String"),
            ("inner", "String", "PB", "fst(\"s\", \"t\")", "fst.a (op-arg): expected Int64, got String"),
            ("outer", "Int64", "PB", "snd(1, 2)", "snd.b (op-arg): expected String, got Int64"),
        ] {
            let ns = format!("hzvqa{ns}{tag}");
            let rendered = refusal(&ns, &spell(ret, recv, call));
            assert!(rendered.contains(site), "{ns}: {rendered}");
        }
        let ns = format!("hzvqachainok{tag}");
        assert_eq!(
            run(&ns, &spell("String", "PB", "snd(1, \"t\")")),
            "t",
            "{ns}"
        );
    }
}

/// `sort PA = Pair[L = Int64]` fixes `L` and leaves `R` to the call.
#[test]
fn a_partial_alias_leaves_its_open_parameter_to_the_call() {
    type Spelling = fn(&str, &str, &str) -> String;
    for (tag, spell) in [("w", written as Spelling), ("b", bound as Spelling)] {
        let ns = format!("hzvqapartbad{tag}");
        let rendered = refusal(&ns, &spell("String", "PA", "fst(\"s\", \"t\")"));
        assert!(
            rendered.contains("fst.a (op-arg): expected Int64, got String"),
            "{ns}: {rendered}"
        );
        let ns = format!("hzvqapartopen{tag}");
        assert_eq!(
            run(&ns, &spell("String", "PA", "snd(1, \"t\")")),
            "t",
            "{ns}: `R` is the argument's"
        );
    }
}

/// `sort IB = Box[Int64]` fixes `V` as `Box[V = Int64]` does, and a constant an alias
/// fixes is part of the receiver as a type is.
#[test]
fn an_alias_written_positionally_or_fixing_a_constant_is_at_it() {
    type Spelling = fn(&str, &str, &str) -> String;
    for (tag, spell) in [("w", written as Spelling), ("b", bound as Spelling)] {
        let ns = format!("hzvqapos{tag}");
        let rendered = refusal(&ns, &spell("String", "IB", "wrap(\"s\")"));
        assert!(
            rendered.contains("wrap.x (op-arg): expected Int64, got String"),
            "{ns}: {rendered}"
        );
    }
    const VEC: &str = "  sort Vec[E, N]\n    entity vec(e: E)\n    operation same(x: Vec[E, N]) -> Vec[E, N] = x\n  end\n  sort V3 = Vec[N = 3]\n";
    for (ns, bind, call) in [
        ("hzvqaconstw", "", "V3.same(vec(e: 1))"),
        ("hzvqaconstb", "    let t = V3\n", "t.same(vec(e: 1))"),
    ] {
        let go = |n: u8| {
            format!("{VEC}  operation go() -> Int64 =\n{bind}    let v: Vec[Int64, {n}] = {call}\n    2")
        };
        let rendered = refusal(ns, &go(4));
        assert!(rendered.contains("got Vec[N = 3, E = Int64]"), "{ns}: {rendered}");
        let ok = format!("{ns}ok");
        assert_eq!(run(&ok, &go(3)), "2", "{ok}");
    }
}

/// The alias is the call's receiver, so the callee's own bracket must agree with it, as
/// it must with a receiver written out.
#[test]
fn a_callee_bracket_must_agree_with_the_alias() {
    let rendered = refusal(
        "hzvqaconflict",
        "  operation go() -> String = CA.wrap[V = String](\"s\")",
    );
    assert!(
        rendered.contains("expected the receiver's V = Int64")
            && rendered.contains("got the callee bracket's V = String"),
        "{rendered}"
    );
    assert_eq!(
        run("hzvqaagree", "  operation go() -> Int64 = CA.wrap[V = Int64](5)"),
        "5"
    );
}

/// A call with no argument to say the parameter is typed by its receiver, and the alias
/// is the receiver.
#[test]
fn the_alias_types_the_result_of_a_call_without_arguments() {
    const CELL: &str = "  sort Cell[V]\n    entity cell(v: V)\n    entity nil\n    operation empty() -> Self = nil\n  end\n  sort IC = Cell[V = Int64]\n";
    for (ns, bind, call) in [
        ("hzvqaresultw", "", "IC.empty()"),
        ("hzvqaresultb", "    let t = IC\n", "t.empty()"),
    ] {
        let go = |annotation: &str| {
            format!(
                "{CELL}  operation go() -> Int64 =\n{bind}    let c: {annotation} = {call}\n    1"
            )
        };
        let rendered = refusal(ns, &go("Cell[V = String]"));
        assert!(
            rendered.contains("expected Cell[V = String], got Cell[V = Int64]"),
            "{ns}: {rendered}"
        );
        let ok = format!("{ns}ok");
        assert_eq!(run(&ok, &go("Cell[V = Int64]")), "1", "{ok}");
    }
}

/// The alias is read where the path crosses it, however the path starts.
#[test]
fn a_qualified_path_through_an_alias_carries_it() {
    for (ns, path) in [
        ("hzvqaqual", "test.hzvqaqual.CA"),
        ("hzvqaroot", "..test.hzvqaroot.CA"),
    ] {
        let rendered = refusal(ns, &written("String", path, "wrap(\"s\")"));
        assert!(
            rendered.contains("wrap.x (op-arg): expected Int64, got String"),
            "{ns}: {rendered}"
        );
    }
}

/// `sort BS = Box[V = S]` written inside `sort Outer[S]` fixes `V` to that parameter.
#[test]
fn an_alias_that_names_the_enclosing_parameter_is_at_that_parameter() {
    let outer = |body: &str| {
        format!("  sort Outer[S]\n    entity o(s: S)\n    sort BS = Box[V = S]\n{body}\n  end\n")
    };
    for (ns, good, bad) in [
        (
            "hzvqaouterw",
            "    operation use(x: S) -> S = BS.wrap(x)",
            "    operation use(x: S) -> String = BS.wrap(\"s\")",
        ),
        (
            "hzvqaouterb",
            "    operation use(x: S) -> S =\n      let t = BS\n      t.wrap(x)",
            "    operation use(x: S) -> String =\n      let t = BS\n      t.wrap(\"s\")",
        ),
    ] {
        assert_eq!(
            run(ns, &format!("{}  operation go() -> Int64 = Outer.use(4)", outer(good))),
            "4",
            "{ns}"
        );
        let bad_ns = format!("{ns}bad");
        let rendered = refusal(&bad_ns, &format!("{}  operation go() -> Int64 = 1", outer(bad)));
        assert!(rendered.contains("wrap.x (op-arg)"), "{bad_ns}: {rendered}");
    }
}

/// A spec's operation called through an alias of the spec is called at the members the
/// alias fixes: with `Out` fixed to `String` the result is a `String`, as it is with the
/// spec written out.
#[test]
fn a_spec_called_through_an_alias_is_at_its_members() {
    const SPEC: &str = "  sort Desc\n    sort T = ?\n    sort Out = ?\n    operation label(x: T) -> Out\n  end\n  sort Leaf\n    entity leaf\n    provides Desc[T = Leaf, Out = Int64]\n    operation label(x: Leaf) -> Int64 = 7\n  end\n  sort DA = Desc[Out = Int64]\n  sort DS = Desc[Out = String]\n";
    for (ns, body) in [
        ("hzvqaspecw", written("Int64", "DA", "label(leaf)")),
        ("hzvqaspecb", bound("Int64", "DA", "label(leaf)")),
    ] {
        assert_eq!(run(ns, &format!("{SPEC}{body}")), "7", "{ns}");
    }
    let twin = refusal(
        "hzvqaspectwin",
        &format!("{SPEC}{}", written("Int64", "Desc[Out = String]", "label(leaf)")),
    );
    assert!(twin.contains("go.return (op-return): expected Int64, got String"), "{twin}");
    for (ns, body) in [
        ("hzvqaspecbadw", written("Int64", "DS", "label(leaf)")),
        ("hzvqaspecbadb", bound("Int64", "DS", "label(leaf)")),
    ] {
        let rendered = refusal(ns, &format!("{SPEC}{body}"));
        assert!(
            rendered.contains("go.return (op-return): expected Int64, got String"),
            "{ns}: {rendered}"
        );
    }
}

/// A call in a rule body is the same call.
#[test]
fn a_rule_body_call_through_an_alias_is_at_its_parameters() {
    let rendered = refusal(
        "hzvqarule",
        "  rule r(?v) :- ?v <=> CA.wrap(\"s\")\n  operation go() -> Int64 = 1",
    );
    assert!(
        rendered.contains("wrap.x (op-arg): expected Int64, got String"),
        "{rendered}"
    );
    assert_eq!(
        run(
            "hzvqaruleok",
            "  rule r(?v) :- ?v <=> CA.wrap(5)\n  operation go() -> Int64 = 1"
        ),
        "1"
    );
}

/// A named requirement slot the alias fixes selects the provider for a call through it,
/// as the same slot written in a receiver bracket does: by length, `"aa"` and `"bb"` are
/// one element. Before, the call was refused — its requirement had no provider.
#[test]
fn an_alias_that_fixes_a_requirement_slot_selects_its_provider() {
    let slots = |ns: &str, body: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{Int64, String, WeakOrd, SortedSet, Type}}\n\
             \x20 import anthill.prelude.String.{{length}}\n\
             \x20 import anthill.prelude.Numeric.{{sub}}\n\
             \x20 sort ByLength\n\
             \x20   provides WeakOrd[T = String]\n\
             \x20   operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))\n\
             \x20 end\n\
             \x20 sort ConcOrd\n\
             \x20   entity conc\n\
             \x20   provides WeakOrd[T = String]\n\
             \x20   operation compare(a: String, b: String) -> Int64 = 0\n\
             \x20 end\n\
             \x20 sort BL = SortedSet[T = String, O = ByLength]\n\
             \x20 sort CS = SortedSet[T = String, O = ConcOrd]\n\
             {body}\n\
             end\n"
        )
    };
    let sized = |bind: &str, recv: &str, second: &str| {
        format!(
            "  operation go() -> Int64 =\n{bind}    SortedSet.size({recv}.insert({recv}.insert({recv}.empty(), \"aa\"), \"{second}\"))"
        )
    };
    for (tag, bind, recv) in [
        ("twin", "", "SortedSet[T = String, O = ByLength]"),
        ("w", "", "BL"),
        ("b", "    let t = BL\n", "t"),
    ] {
        for (second, want) in [("bb", "1"), ("b", "2")] {
            let ns = format!("hzvqaslot{tag}{second}");
            assert_eq!(run_source(&ns, &slots(&ns, &sized(bind, recv, second))), want, "{ns}");
        }
    }
    // A concrete provider is one a call may not select, written out or through the alias.
    for (ns, recv) in [
        ("hzvqaslotconctwin", "SortedSet[T = String, O = ConcOrd]"),
        ("hzvqaslotconc", "CS"),
    ] {
        let body = format!("  operation go() -> Int64 =\n    let s = {recv}.empty()\n    1");
        let rendered = refusal_of(ns, &slots(ns, &body));
        assert!(rendered.contains("SortedSet.empty.selection"), "{ns}: {rendered}");
    }
}

/// A goal in a rule body is the same call: its argument is checked at the alias's
/// parameters. The goals that answer are the fence here — they pass under every back-out,
/// and say that a goal which carries a receiver is still resolved, and still negated.
#[test]
fn a_rule_body_goal_through_an_alias_is_checked_and_answers() {
    let rendered = refusal(
        "hzvqagoalbad",
        "  rule r(?x: Int64) :- ?x <=> 7, CA.same(\"s\")\n  operation go() -> Int64 = 1",
    );
    assert!(
        rendered.contains("same.x (op-arg): expected Int64, got String"),
        "{rendered}"
    );
    for (ns, goals, want) in [
        ("hzvqagoal", "CA.holds(?x)", "1"),
        ("hzvqagoalnot", "?x <=> 7, not(CA.holds(?x))", "1"),
        ("hzvqagoalnotone", "?x <=> 1, not(CA.holds(?x))", "0"),
    ] {
        let body = format!(
            "  rule r(?x: Int64) :- {goals}\n  operation go() -> Int64 effects {{Error}} = r.takeN(5).length()"
        );
        assert_eq!(run(ns, &body), want, "{ns}");
    }
}

/// A paren-less goal is the applied goal, through an alias too: `:- CR.ok` carries the
/// receiver `:- CR.ok()` carries. Shown where the receiver is refused — the alias fixes a
/// requirement slot to a concrete provider — since a goal with no argument gives a
/// receiver nothing else to say.
#[test]
fn a_paren_less_goal_through_an_alias_is_the_applied_goal() {
    let reg = |ns: &str, goal: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{Int64, String, Bool, Error, WeakOrd}}\n\
             \x20 sort ConcOrd\n\
             \x20   entity conc\n\
             \x20   provides WeakOrd[T = String]\n\
             \x20   operation compare(a: String, b: String) -> Int64 = 0\n\
             \x20 end\n\
             \x20 sort Reg[T]\n\
             \x20   requires O: WeakOrd[T]\n\
             \x20   entity reg(v: T)\n\
             \x20   operation ok() -> Bool = true\n\
             \x20 end\n\
             \x20 sort CR = Reg[T = String, O = ConcOrd]\n\
             \x20 sort IR = Reg[T = Int64]\n\
             \x20 rule r(?x: Int64) :- ?x <=> 7, {goal}\n\
             \x20 operation go() -> Int64 effects {{Error}} = r.takeN(5).length()\n\
             end\n"
        )
    };
    for (ns, goal) in [("hzvqaparenapplied", "CR.ok()"), ("hzvqaparenless", "CR.ok")] {
        let rendered = refusal_of(ns, &reg(ns, goal));
        assert!(rendered.contains("Reg.ok.selection"), "{ns}: {rendered}");
    }
    for (ns, goal) in [("hzvqaparenokapplied", "IR.ok()"), ("hzvqaparenokless", "IR.ok")] {
        assert_eq!(run_source(ns, &reg(ns, goal)), "1", "{ns}");
    }
}

/// A variadic-capture rule fires on its head however the call names the sort: bare,
/// with a receiver bracket, or through an alias that fixes the parameter. Before, a call
/// with a receiver was left to the operation's own body, which answers 5.
#[test]
fn a_capture_rule_fires_on_a_call_that_has_a_receiver() {
    let capture = |ns: &str, call: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{Int64}}\n\
             \x20 import anthill.prelude.List.{{cons}}\n\
             \x20 import anthill.prelude.Numeric.{{add}}\n\
             \x20 import anthill.reflect.{{NodeOccurrence, make_apply, sub_occurrences}}\n\
             \x20 operation kept(v: Int64, w: Int64) -> Int64 = add(add(v, w), 100)\n\
             \x20 operation pick(x: NodeOccurrence, args: NodeOccurrence) -> NodeOccurrence =\n\
             \x20   make_apply(\"test.{ns}.kept\", cons(x, sub_occurrences(args)), x)\n\
             \x20 sort CBox[V]\n\
             \x20   entity cb(v: V)\n\
             \x20   operation trigger[R](x: Int64, ...args: R) -> Int64 = x\n\
             \x20   rule trigger(?x, ...?args) <=> test.{ns}.pick(?x, ?args) @[simp]\n\
             \x20 end\n\
             \x20 sort IC = CBox[V = Int64]\n\
             \x20 operation go() -> Int64 = {call}\n\
             end\n"
        )
    };
    for (ns, recv) in [
        ("hzvqacapsort", "CBox"),
        ("hzvqacapwritten", "CBox[V = Int64]"),
        ("hzvqacapalias", "IC"),
    ] {
        let call = format!("{recv}.trigger(5, a: 7)");
        assert_eq!(run_source(ns, &capture(ns, &call)), "112", "{ns}");
    }
}

/// A receiver names the instance a call is at, and says nothing more of the result. The
/// result is what the operation declares, read at that instance, and every spelling of the
/// call gives it: bare, the callee's bracket, the receiver's — named or positional — and an
/// alias. Before, a receiver was also compared with the declared return, and a call whose
/// return was anything but the receiver's own instance was refused at that return,
/// whatever used the result.
#[test]
fn a_receiver_names_the_instance_and_not_the_result() {
    let sorts = |ns: &str, body: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.Type\n\
             \x20 sort Cell[V]\n\
             \x20   entity nil\n\
             \x20   entity cell(v: V)\n\
             \x20   operation empty() -> Cell = nil\n\
             \x20   operation some() -> Cell[V = ?] = nil\n\
             \x20   operation ints() -> Cell[V = Int64] = cell(v: 1)\n\
             \x20   operation count(c: Cell) -> Int64 = 3\n\
             \x20   operation unbox(c: Self) -> V = match c\n\
             \x20     case cell(v) -> v\n\
             \x20 end\n\
             \x20 sort Pair[L, R]\n\
             \x20   entity pair(l: L, r: R)\n\
             \x20   entity lone(l: L)\n\
             \x20   operation half(x: L) -> Pair[L = L] = lone(l: x)\n\
             \x20   operation swap(p: Self) -> Pair[L = R, R = L] = match p\n\
             \x20     case pair(l, r) -> pair(l: r, r: l)\n\
             \x20   operation size(p: Pair) -> Int64 = 2\n\
             \x20 end\n\
             \x20 sort Opt[T]\n\
             \x20   entity none\n\
             \x20   operation make[A]() -> Opt[T = A] = none\n\
             \x20   operation count(o: Opt) -> Int64 = 3\n\
             \x20 end\n\
             \x20 sort IC = Cell[V = Int64]\n\
             \x20 sort SC = Cell[V = String]\n\
             \x20 sort PIS = Pair[L = Int64, R = String]\n\
             \x20 sort IO = Opt[T = Int64]\n\
             {body}\n\
             end\n"
        )
    };
    let go = |bind: &str, expr: &str| format!("  operation go() -> Int64 =\n{bind}    {expr}");
    let annotated = |bind: &str, ty: &str, call: &str| {
        format!("  operation go() -> Int64 =\n{bind}    let c: {ty} = {call}\n    1")
    };

    // The return leaves its slot open — the bare sort, or `?` — and is some cell, the
    // operation's to choose: taken where any cell is, refused where one instance is asked.
    for (tag, bind, call) in [
        ("sort", "", "Cell.empty()"),
        ("callee", "", "Cell.empty[V = Int64]()"),
        ("recv", "", "Cell[V = Int64].empty()"),
        ("recvpos", "", "Cell[Int64].empty()"),
        ("alias", "", "IC.empty()"),
        ("bound", "    let t = IC\n", "t.empty()"),
        ("recvq", "", "Cell[V = Int64].some()"),
        ("aliasq", "", "IC.some()"),
    ] {
        let ns = format!("hzvqaopenany{tag}");
        let body = go(bind, &format!("Cell.count({call})"));
        assert_eq!(run_source(&ns, &sorts(&ns, &body)), "3", "{ns}");
        let ns = format!("hzvqaopenat{tag}");
        let rendered = refusal_of(&ns, &sorts(&ns, &annotated(bind, "Cell[V = Int64]", call)));
        assert!(
            rendered.contains("c.annotation (let-binding): expected Cell[V = Int64], got Cell[V = ?V]"),
            "{ns}: {rendered}"
        );
    }

    // The return is written at one instance, whatever instance the call is at: `ints` is a
    // cell of `Int64` called at `String` too, and the value in it is the `Int64`.
    for (tag, bind, call) in [
        ("sort", "", "Cell.ints()"),
        ("callee", "", "Cell.ints[V = String]()"),
        ("recv", "", "Cell[V = String].ints()"),
        ("recvpos", "", "Cell[String].ints()"),
        ("alias", "", "SC.ints()"),
        ("bound", "    let t = SC\n", "t.ints()"),
    ] {
        let ns = format!("hzvqafixedany{tag}");
        let body = go(bind, &format!("Cell.count({call})"));
        assert_eq!(run_source(&ns, &sorts(&ns, &body)), "3", "{ns}");
        let ns = format!("hzvqafixedvalue{tag}");
        let body = go(bind, &format!("Cell.unbox({call})"));
        assert_eq!(run_source(&ns, &sorts(&ns, &body)), "1", "{ns}");
        let ns = format!("hzvqafixedat{tag}");
        let rendered = refusal_of(&ns, &sorts(&ns, &annotated(bind, "Cell[V = String]", call)));
        assert!(
            rendered.contains("c.annotation (let-binding): expected Cell[V = String], got Cell[V = Int64]"),
            "{ns}: {rendered}"
        );
    }

    // The return names the parameters, in its own order: at `(Int64, String)` a swapped
    // pair is a `Pair[L = String, R = Int64]`.
    for (tag, call) in [
        ("sort", "Pair.swap(pair(l: 1, r: \"s\"))"),
        ("recv", "Pair[L = Int64, R = String].swap(pair(l: 1, r: \"s\"))"),
        ("alias", "PIS.swap(pair(l: 1, r: \"s\"))"),
    ] {
        let ns = format!("hzvqaswap{tag}");
        let body = annotated("", "Pair[L = String, R = Int64]", call);
        assert_eq!(run_source(&ns, &sorts(&ns, &body)), "1", "{ns}");
        let ns = format!("hzvqaswapat{tag}");
        let rendered = refusal_of(&ns, &sorts(&ns, &annotated("", "Pair[L = Int64, R = String]", call)));
        assert!(
            rendered.contains("c.annotation (let-binding): expected Pair[L = Int64, R = String], got Pair[L = String, R = Int64]"),
            "{ns}: {rendered}"
        );
    }

    // The return writes one slot and leaves the other.
    for (tag, call) in [
        ("sort", "Pair.half(1)"),
        ("callee", "Pair.half[L = Int64, R = String](1)"),
        ("recv", "Pair[L = Int64, R = String].half(1)"),
        ("alias", "PIS.half(1)"),
    ] {
        let ns = format!("hzvqaparthalf{tag}");
        assert_eq!(run_source(&ns, &sorts(&ns, &go("", &format!("Pair.size({call})")))), "2", "{ns}");
    }

    // The return is written with the operation's OWN parameter, which is not the sort's:
    // the receiver does not fix it, in any spelling, and what fixes it is what fixes an
    // operation's parameter at any call — here the callee's bracket, or the expected type.
    for (tag, call) in [
        ("sort", "Opt.make()"),
        ("callee", "Opt.make[T = Int64]()"),
        ("recv", "Opt[T = Int64].make()"),
        ("alias", "IO.make()"),
    ] {
        let ns = format!("hzvqaownparam{tag}");
        let rendered = refusal_of(&ns, &sorts(&ns, &go("", &format!("Opt.count({call})"))));
        assert!(
            rendered.contains("Opt.make.type_arg: expected a type for 'A', got unconstrained"),
            "{ns}: {rendered}"
        );
        let ns = format!("hzvqaownparamat{tag}");
        let body = format!("  operation go() -> Int64 =\n    let o: Opt[T = String] = {call}\n    Opt.count(o)");
        assert_eq!(run_source(&ns, &sorts(&ns, &body)), "3", "{ns}");
    }
    let ns = "hzvqaownparambracket";
    let body = go("", "Opt.count(Opt[T = Int64].make[A = Int64]())");
    assert_eq!(run_source(ns, &sorts(ns, &body)), "3");

    // What the receiver does say stands: an argument is checked at its instance.
    for (ns, call, site) in [
        ("hzvqarecvarghalf", "Pair.size(PIS.half(\"s\"))", "half.x (op-arg): expected Int64, got String"),
        (
            "hzvqarecvargswap",
            "Pair.size(Pair[L = String, R = String].swap(pair(l: 1, r: \"s\")))",
            "swap.p (op-arg): expected Pair[L = String, R = String], got Pair[L = Int64, R = String]",
        ),
    ] {
        let rendered = refusal_of(ns, &sorts(ns, &go("", call)));
        assert!(rendered.contains(site), "{ns}: {rendered}");
    }
}

// ── constructors ────────────────────────────────────────────────────────────

/// A namespace `test.<ns>` holding a sort with constructors, aliases of it, and `body`.
fn constructors(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n\
         \x20 import anthill.prelude.{{Type, Error}}\n\
         \x20 sort Box[V]\n\
         \x20   entity mk(v: V)\n\
         \x20   entity nil\n\
         \x20   operation unbox(b: Self) -> V = match b\n\
         \x20     case mk(v) -> v\n\
         \x20   operation count(b: Box) -> Int64 = 3\n\
         \x20 end\n\
         \x20 sort Pair[L, R]\n\
         \x20   entity pair(l: L, r: R)\n\
         \x20   operation fst(p: Self) -> L = match p\n\
         \x20     case pair(l, r) -> l\n\
         \x20 end\n\
         \x20 sort CA = Box[V = Int64]\n\
         \x20 sort PA = Pair[L = Int64]\n\
         {body}\n\
         end\n"
    )
}

/// A constructor is a call, and its receiver binds the sort's parameters for it as an
/// operation's does — a written bracket, an alias, a name a `let` bound to either. The
/// fields are checked at them and the value is the sort at them. Before, a bracket on a
/// constructor was refused outright, and what an alias fixed was dropped: `CA.mk("s")`
/// built a `Box[V = String]`.
#[test]
fn a_constructor_called_with_a_receiver_is_at_its_parameters() {
    let go = |bind: &str, expr: &str| format!("  operation go() -> Int64 =\n{bind}    {expr}");
    for (tag, bind, recv) in [
        ("recv", "", "Box[V = Int64]"),
        ("recvpos", "", "Box[Int64]"),
        ("paren", "", "(Box[V = Int64])"),
        ("alias", "", "CA"),
        ("bound", "    let t = CA\n", "t"),
        ("boundrecv", "    let t = Box[V = Int64]\n", "t"),
    ] {
        let ns = format!("hzvqactor{tag}");
        let body = go(bind, &format!("Box.unbox({recv}.mk(5))"));
        assert_eq!(run_source(&ns, &constructors(&ns, &body)), "5", "{ns}");

        let ns = format!("hzvqactorfield{tag}");
        let body = go(bind, &format!("Box.count({recv}.mk(\"s\"))"));
        let rendered = refusal_of(&ns, &constructors(&ns, &body));
        assert!(
            rendered.contains("mk.v (entity-field): expected Int64, got String"),
            "{ns}: {rendered}"
        );

        // The value is the sort at the receiver's parameters, with a field or without one.
        for (kind, ctor) in [("mk", "mk(5)"), ("nil", "nil()")] {
            let ns = format!("hzvqactorat{kind}{tag}");
            let body = go(
                bind,
                &format!("let c: Box[V = String] = {recv}.{ctor}\n    1"),
            );
            let rendered = refusal_of(&ns, &constructors(&ns, &body));
            assert!(
                rendered.contains(
                    "c.annotation (let-binding): expected Box[V = String], got Box[V = Int64]"
                ),
                "{ns}: {rendered}"
            );
        }
        let ns = format!("hzvqactornil{tag}");
        let body = format!(
            "  operation go() -> Int64 =\n{bind}    let c: Box[V = Int64] = {recv}.nil()\n    Box.count(c)"
        );
        assert_eq!(run_source(&ns, &constructors(&ns, &body)), "3", "{ns}");
    }

    // With no receiver the parameter is the field's, as it was.
    let ns = "hzvqactorplain";
    let body = "  operation go() -> String = Box.unbox(Box.mk(\"s\"))";
    assert_eq!(run_source(ns, &constructors(ns, body)), "s");

    // An alias fixes what it fixes and leaves the rest to the fields.
    let ns = "hzvqactorpart";
    let body = "  operation go() -> Int64 = Pair.fst(PA.pair(1, \"s\"))";
    assert_eq!(run_source(ns, &constructors(ns, body)), "1");
    let ns = "hzvqactorpartbad";
    let body = "  operation go() -> String = Pair.fst(PA.pair(\"x\", \"s\"))";
    let rendered = refusal_of(ns, &constructors(ns, body));
    assert!(
        rendered.contains("pair.l (entity-field): expected Int64, got String"),
        "{rendered}"
    );
}

/// A constructor's arguments are typed from its declared fields — an arrow-typed field
/// lets a bare operation name stand for the function, a ground field type fixes a call's
/// own parameter — and they are with a receiver as without one.
#[test]
fn a_constructor_with_a_receiver_types_its_arguments_as_any_other() {
    let hints = |ns: &str, expr: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{List, Type}}\n\
             \x20 import anthill.prelude.List.{{nil}}\n\
             \x20 import anthill.prelude.Numeric.{{add}}\n\
             \x20 sort Fb[V]\n\
             \x20   entity fb(f: (x: V) -> V)\n\
             \x20   operation run(b: Self, x: V) -> V = match b\n\
             \x20     case fb(f) -> f(x)\n\
             \x20 end\n\
             \x20 sort Holder[V]\n\
             \x20   entity hold(c: List[T = Int64], v: V)\n\
             \x20   operation size(h: Holder) -> Int64 = 4\n\
             \x20 end\n\
             \x20 operation inc(x: Int64) -> Int64 = add(x, 1)\n\
             \x20 operation poly[A]() -> List[T = A] = nil\n\
             \x20 sort IF = Fb[V = Int64]\n\
             \x20 sort IH = Holder[V = Int64]\n\
             \x20 operation go() -> Int64 = {expr}\n\
             end\n"
        )
    };
    for (tag, fb, holder) in [
        ("sort", "Fb", "Holder"),
        ("recv", "Fb[V = Int64]", "Holder[V = Int64]"),
        ("alias", "IF", "IH"),
    ] {
        let ns = format!("hzvqactorarrow{tag}");
        assert_eq!(run_source(&ns, &hints(&ns, &format!("Fb.run({fb}.fb(inc), 1)"))), "2", "{ns}");
        let ns = format!("hzvqactorcall{tag}");
        assert_eq!(
            run_source(&ns, &hints(&ns, &format!("Holder.size({holder}.hold(poly(), 1))"))),
            "4",
            "{ns}"
        );
    }
}

/// In a rule body a constructor is a term the clause matches, not a call, and takes no
/// receiver: a written bracket is refused, standing alone or under an `if`, and a
/// constructor named through an alias is the sort's constructor.
#[test]
fn a_constructor_in_a_rule_body_takes_no_receiver() {
    for (ns, term) in [
        ("hzvqactorrule", "Box[V = Int64].mk(5)"),
        ("hzvqactorruleif", "(if true then Box[V = Int64].mk(5) else Box[V = Int64].mk(6))"),
    ] {
        let body = format!("  rule r(?v) :- ?v <=> {term}\n  operation go() -> Int64 = 1");
        let rendered = refusal_of(ns, &constructors(ns, &body));
        assert!(rendered.contains("is not read here — `Box.mk`"), "{ns}: {rendered}");
    }
    let ns = "hzvqactorrulealias";
    let body = "  fact Box.mk(7)\n  rule r(?x: Int64) :- CA.mk(?x)\n  operation go() -> Int64 effects {Error} = r.takeN(5).length()";
    assert_eq!(run_source(ns, &constructors(ns, body)), "1");
}

// ── citations ───────────────────────────────────────────────────────────────

/// A namespace `test.<ns>` holding a parametric sort with relations, an alias that fixes
/// its parameter, one that does not, and `body`.
fn relations(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n\
         \x20 import anthill.prelude.{{Int64, Error, EmptyStream, Relation}}\n\
         \x20 sort Colour\n\
         \x20   entity red\n\
         \x20   entity green\n\
         \x20 end\n\
         \x20 sort Wrap[T]\n\
         \x20   entity wrap(v: T)\n\
         \x20   rule dom(?x: Wrap[T = T]) :- true\n\
         \x20   rule one(?n: Int64) :- ?n <=> 1\n\
         \x20 end\n\
         \x20 sort WC = Wrap[T = Colour]\n\
         \x20 sort WB = Wrap\n\
         {body}\n\
         end\n"
    )
}

/// `WC.dom` is `Wrap[T = Colour].dom`: bare, applied, and under a member.
#[test]
fn a_rule_cited_through_an_alias_is_cited_at_its_parameters() {
    const EFF: &str = "effects {Error, Error[EmptyStream]}";
    let go = "  operation go() -> Int64 = 1";

    // Under a member: the column is typed at the alias's instance.
    let ns = "hzvqacitecol";
    let body = format!("  operation a() -> Wrap[T = Colour] {EFF} =\n    WC.dom.head.x\n{go}");
    assert_eq!(run_source(ns, &relations(ns, &body)), "1");
    let ns = "hzvqacitecolbad";
    let body = format!("  operation a() -> Wrap[T = Int64] {EFF} =\n    WC.dom.head.x\n{go}");
    let rendered = refusal_of(ns, &relations(ns, &body));
    assert!(
        rendered.contains("expected Wrap[T = Int64], got Wrap[T = Colour]"),
        "{rendered}"
    );

    // Bare: the alias fixes the parameter, where a bare alias leaves it undetermined.
    let ns = "hzvqacitebare";
    let body = format!("  operation a() -> Int64 =\n    let r = WC.dom\n    1\n{go}");
    assert_eq!(run_source(ns, &relations(ns, &body)), "1");
    let ns = "hzvqaciteopen";
    let body = format!("  operation a() -> Int64 =\n    let r = WB.dom\n    1\n{go}");
    let rendered = refusal_of(ns, &relations(ns, &body));
    assert!(rendered.contains("is not determined at this citation"), "{rendered}");
    let ns = "hzvqaciteexpect";
    let body = format!(
        "  operation a() -> Relation[T = (x: Wrap[T = Int64]), E = {{Error}}] = WC.dom\n{go}"
    );
    let rendered = refusal_of(ns, &relations(ns, &body));
    assert!(
        rendered.contains("got Relation[T = (x: Wrap[T = Colour]), E = {Error}]"),
        "{rendered}"
    );

    // Applied: the argument is checked against the alias's instance.
    let ns = "hzvqaciteapplied";
    let body = format!(
        "  operation a() -> Int64 effects {{Error}} = WC.dom(wrap(1)).takeN(5).length()\n{go}"
    );
    let rendered = refusal_of(ns, &relations(ns, &body));
    assert!(
        rendered.contains("argument binding column `x` has an incompatible type"),
        "{rendered}"
    );
    let ns = "hzvqaciteappliedok";
    let body = format!(
        "  operation a() -> Int64 effects {{Error}} = WC.dom(wrap(red())).takeN(5).length()\n{go}"
    );
    assert_eq!(run_source(ns, &relations(ns, &body)), "1");

    // And the relation cited through the alias answers what the relation answers.
    for (ns, recv) in [
        ("hzvqaciterunsort", "Wrap"),
        ("hzvqaciterunwritten", "Wrap[T = Colour]"),
        ("hzvqaciterunalias", "WC"),
    ] {
        let body = format!(
            "  operation go() -> Int64 effects {{Error}} = {recv}.one.takeN(5).length()"
        );
        assert_eq!(run_source(ns, &relations(ns, &body)), "1", "{ns}");
    }
}

/// An alias is the receiver of its own members only. `OA.Inner.dom` reaches a relation of
/// the nested `Inner` through an alias of the sort above it, and the alias's bracket on
/// `Outer` is no receiver of `Inner`'s member.
#[test]
fn an_alias_above_the_members_sort_is_not_its_receiver() {
    let nested = |ns: &str, recv: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{Int64, Error, Relation}}\n\
             \x20 sort Outer[S]\n\
             \x20   entity o(s: S)\n\
             \x20   sort Inner[V]\n\
             \x20     entity inner(v: V)\n\
             \x20     rule dom(?x: Inner[V = V]) :- true\n\
             \x20   end\n\
             \x20 end\n\
             \x20 sort OA = Outer[S = Int64]\n\
             \x20 operation a() -> Int64 effects {{Error}} =\n\
             \x20   {recv}.Inner.dom(Outer.Inner.inner(1)).takeN(5).length()\n\
             \x20 operation go() -> Int64 = 1\n\
             end\n"
        )
    };
    for (ns, recv) in [("hzvqanestedsort", "Outer"), ("hzvqanestedalias", "OA")] {
        assert_eq!(run_source(ns, &nested(ns, recv)), "1", "{ns}");
    }
}

/// The receiver is the alias's only where the path was read through the alias. Here the
/// member the alias reaches is hidden, so the name is answered by the root namespace of
/// the same spelling, and that callee takes no receiver from the alias.
#[test]
fn a_name_another_rung_answered_takes_no_receiver() {
    let source = |ns: &str, visibility: &str| {
        format!(
            "namespace HzvqaAlias\n\
             \x20 operation wrap(x: String) -> hzvqalib.Box[V = String] = hzvqalib.Box.mk(x)\n\
             end\n\
             namespace hzvqalib\n\
             \x20 sort Box[V]\n\
             \x20   entity mk(v: V)\n\
             \x20   {visibility}operation wrap(x: V) -> V = x\n\
             \x20   operation count(b: Box) -> Int64 = 3\n\
             \x20 end\n\
             \x20 sort HzvqaAlias = Box[V = Int64]\n\
             end\n\
             namespace test.{ns}\n\
             \x20 import hzvqalib.HzvqaAlias\n\
             \x20 import hzvqalib.Box\n\
             \x20 operation go() -> Int64 = Box.count(HzvqaAlias.wrap(\"s\"))\n\
             end\n"
        )
    };
    let ns = "hzvqatiehidden";
    assert_eq!(run_source(ns, &source(ns, "internal ")), "3");
    // The control: visible, the member is the alias's and the call is at `V = Int64`.
    let ns = "hzvqatievisible";
    let rendered = refusal_of(ns, &source(ns, ""));
    assert!(
        rendered.contains("wrap.x (op-arg): expected Int64, got String"),
        "{rendered}"
    );
}
