//! WI-20261013-WF14Z (068 C1b) — A CLAUSE IS TYPED AS A WHOLE (068-implementation §6.2,
//! decision 1): one substitution over its variables, from every position that declares a
//! type. Before, only a constructor's application and an operation's or an entity's declared
//! parameters typed a rule variable; the head's written bound, an operation call's result —
//! in a value slot and as the result column of `f(args, ?r)` —, a rule goal's columns and a
//! field read typed nothing, so a dot on the variable they make was data: `rule h1(?a: Int64,
//! ?x) :- ?x <=> ?a.abs()` bound `?x` to the term `-3.abs`.
//!
//! What types a variable, each read after the walk on a copy of the clause's typing and kept
//! only where it fits (`LatePosition`, `settle_late_positions`):
//!
//!   * the head's written bound, the enclosing sort's parameters in it rigid
//!     (`settle_head_bounds`);
//!   * an operation call's result in a slot that declares a type (`CallResult`), a projection
//!     on a parameter read off the argument's type and a type constructor reduced
//!     (`computed_result_type`), the call's written type arguments read (`constrain_application`);
//!   * the result column of `f(args, ?r)` at goal position (`ResultColumn`);
//!   * a rule goal's columns: the callee's, generalized across its clauses and opened fresh
//!     (`rule_goal_columns`), its own head's for a goal on its own relation, nothing for one on
//!     another relation of its cycle (`same_rule_goal_cycle`);
//!   * a dot's value, once its receiver is typed (`DotResult`).
//!
//! Found on the way, and fixed: a typed head's domain check refused a value whose part the
//! bound fixes and the value does not carry (`read_unknowns_from_bound`); a dotted chain on a
//! sigil-free clause parameter was a name, not a field read (`clause_param_field_read`,
//! `clause_param_method_call` in the loader).
//!
//! ## Back-out
//!
//! Each part mutated to a no-op in place under a switch of its own, one build, and this file
//! run under each switch with the modules the change moved (`wi_0rrqp`, `wi_9wvt7`,
//! `wi_p7vp4`, `wi742`, `wi_c7anm`, `wi_9c2pz`, `wi818`, `wi_5g28a`, `wi_x9pb4`, `wi_shed7`,
//! `wi_a3fy2`, `wi_rxt6s`; measured 2026-10-22, the last four rows with this file, `wi_0rrqp`
//! and `wi_9c2pz` only):
//!
//! | backed out | fails |
//! |---|---|
//! | the head's bound (`settle_head_bounds`) | `a_heads_bound_types_its_variable`, `a_field_of_a_head_parameter_is_a_receiver`, `a_field_read_types_the_slot_it_fills`, `a_projection_in_a_result_is_read_off_the_argument`, `a_rule_goal_reads_the_callees_columns`, `wi_0rrqp…::an_inferred_column_is_checked_as_a_written_one`, `wi_p7vp4…::a_member_of_a_sort_that_requires_is_refused_at_rule_variables` |
//! | the enclosing sort's parameter rigid in a bound (`rigidify`) | `wi_0rrqp…::an_inferred_column_is_checked_as_a_written_one` |
//! | a call's result in a value slot (`LatePosition::CallResult`) | `a_calls_result_types_the_slot_it_fills`, `a_projection_in_a_result_is_read_off_the_argument`, `a_rule_goal_reads_the_callees_columns` |
//! | the result column (`LatePosition::ResultColumn`) | `a_calls_result_types_the_slot_it_fills`, four `wi_9wvt7` rows (`a_scoped_kb_does_not_outlive_a_rule_body_call`, `a_clock_read_in_a_rule_body_is_not_performed`, `an_effectful_thunk_leaves_the_goal_undecided`, `the_advised_repairs_answer`) |
//! | a rule goal (`LatePosition::RuleGoal`) | `a_rule_goal_reads_the_callees_columns`, `a_relation_that_calls_itself_reads_its_own_columns`, `a_goal_on_a_relation_of_its_cycle_reads_nothing`, `wi_0rrqp…::a_column_a_rule_goal_types_is_read_at_its_type`, `wi_0rrqp…::a_rule_goal_fixes_what_the_citation_leaves_unfixed`, `wi742…::an_unannotated_column_types_as_its_goal_reads_it`, `wi_c7anm…::the_declared_column_schema_follows_the_written_order` |
//! | a dot's value (`LatePosition::DotResult`) | `a_field_read_types_the_slot_it_fills`, `a_field_of_a_head_parameter_is_a_receiver` |
//! | a call's written type arguments (`constrain_application`) | `a_rule_goal_reads_the_callees_columns`, by `useFr` (`field_access`'s `Name`) |
//! | a projection read off the argument (`computed_result_type`) | `a_projection_in_a_result_is_read_off_the_argument`, `wi818…::sld_head_law_still_proves_once` (the result read as `s.T`, an `eq` refused) |
//! | a type constructor reduced (the same function) | `a_rule_goal_reads_the_callees_columns`, by `useFr` |
//! | a conforming type taking over a call's placeholder (`constrain_var_at`) | `a_projection_in_a_result_is_read_off_the_argument` |
//! | a goal on another relation of the cycle reading nothing (`same_rule_goal_cycle`) | `a_goal_on_a_relation_of_its_cycle_reads_nothing` |
//! | a column that says nothing taking the other clauses' type (`generalize_columns`) | `a_relation_that_calls_itself_reads_its_own_columns`, `a_goal_on_a_relation_of_its_cycle_reads_nothing` |
//! | generalized, the citation's join instead | `two_clauses_that_tie_their_columns_differently_are_generalized` (and github-todo's `open_item`, measured on the first cut) |
//! | a stamp's sort parameter opened per citation (`ClauseTypes::at_citation`) | `wi_0rrqp…::a_head_bound_beside_the_constructor_reads_the_same` |
//! | a value's unknown part read from its bound (`read_unknowns_from_bound`) | `a_typed_head_admits_a_value_whose_part_its_bound_fixes`, `wi_9wvt7_error_reify…::a_generic_boundary_answers_through_a_rule_body`, `wi_9wvt7_reify_rule_body…::a_generic_catcher_cited_from_a_rule_faults` |
//! | the parameter form's field read and method call (`clause_param_field_read`, `clause_param_method_call`), each alone | `a_field_of_a_head_parameter_is_a_receiver` |
//! | the parameter form's bracket refused (`clause_param_method_call`) | `a_bracket_on_a_parameter_forms_method_call_is_refused` |
//! | only a committed goal typing (`collect_occurrence_type_constraints`'s `committed`) | `a_branch_or_a_negation_types_nothing_outside_it` |
//! | a variable a clause types nowhere a fresh column (`clause_goal_columns`) | `a_clause_that_types_a_column_nowhere_says_nothing_of_it` |
//! | a relation being read answering nothing (`rule_goal_columns_in_flight`) | every row: the load overflows the stack |
//! | that set kept apart from the memo, which a stored clause clears | none: no load of `anthill-core`'s suite stores a clause while a relation's columns are read (a panic there under a switch, every row green) |
//!
//! The second part, measured 2026-10-22 with this file, `wi_0rrqp`, `wi_9c2pz`, `wi_s8cbv`,
//! `wi_prva2`, `wi_shed7`, `wi742`, `wi_k4jgc` and `wi_pw9a0` — what a clause's typing records,
//! each part backed out alone:
//!
//! | backed out | fails |
//! |---|---|
//! | a column only an unread goal names, told from one nothing names (`GoalColumn::unread`): the old reading, "named by no other column" | `a_column_nothing_in_its_clause_names_is_open` |
//! | the record of a goal that read nothing (`note_unread_goal`) | `a_relation_that_calls_itself_reads_its_own_columns`, `a_goal_on_a_relation_of_its_cycle_reads_nothing`, `a_clause_that_types_a_column_nowhere_says_nothing_of_it` |
//! | a `Term` position typing nothing (`says_nothing_of_a_value`) | `a_term_slot_types_nothing` |
//! | an `Option` parameter the call's placeholder (`constrain_application`) | `an_option_parameter_is_the_calls_placeholder` |
//! | the some-coercion at a placeholder's takeover (`constrain_var_at`'s `WrapSome`) | `an_option_parameter_is_the_calls_placeholder` |
//! | a type written as a term typing nothing (`type_written_as_term`) | `a_bracket_entry_types_nothing` |
//! | a bound naming an unresolved sort read as unwritten; one at a spec (`settle_head_bounds`), each alone | `a_refused_bound_is_read_as_unwritten` |
//! | a position that fits once the sort's parameters vary counted as fixing one (`fits_once_parameters_vary`) | `a_goal_that_fixes_the_sorts_parameter_is_that_class` |
//! | the element a bare value meets an `Option` placeholder as bound to the value's type (`constrain_var_at`) | `what_the_some_coercion_binds_is_the_calls` |
//! | a column of occurrences quoting its argument (`constrain_goal_at_columns`) | `a_column_of_occurrences_quotes_its_argument` |
//! | a collection literal read as its collection, not as the reflect entity it is stored as (`collection_literal_type`) | `a_collection_literal_is_its_collection`: refused at load, `TupleLiteral.x` no such member |
//!
//! A goal on its own relation reading the clause's own head was a part too, and no row failed
//! with it backed out: the memo answers nothing for a relation while its clauses are being
//! read, and the relation's columns after, which is the one type the decision asks for. It
//! was removed.
//!
//! PASS EITHER WAY, BY DESIGN: `a_constructor_types_its_variable_in_either_goal_order` and
//! `a_dot_on_a_typed_variable_answers_as_its_written_call` (both since WI-20260925-0RRQP), and
//! the stated limits at the end of two rows.

const CNT: &str = r#"
  import anthill.prelude.{Int64, Bool, String, List, Option, Result, Error, EmptyStream}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Result.{ok, err}
  import anthill.prelude.Stream.{head}
  sort Cnt
    entity cnt(n: Int64)
    operation bump(c: Cnt) -> Int64 = Int64.add(c.n, 1)
    operation isPos(c: Cnt) -> Bool = true
  end
  import NS.Cnt.{cnt}
  sort Mk
    operation mk4() -> Cnt = cnt(n: 4)
  end
  entity P(t: Int64)
  fact pf(5)
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{CNT}{body}end\n").replace("NS", ns)
}

/// The one definite `Int64` of each unary relation `rules` of `body`'s program.
#[track_caller]
fn ints(ns: &str, body: &str, rules: &[&str]) -> Vec<Option<i64>> {
    let mut kb = crate::common::load_kb_with(&program(ns, body));
    rules
        .iter()
        .map(|r| crate::common::one_definite_int(&mut kb, &format!("{ns}.{r}")))
        .collect()
}

/// CONTROL, PASSES EITHER WAY: a constructor's application typed `?c` before this ticket
/// (WI-20260925-0RRQP), in either goal order.
#[test]
fn a_constructor_types_its_variable_in_either_goal_order() {
    assert_eq!(
        ints(
            "wiwf14z.ctor",
            "  rule a1(?x) :- ?c <=> cnt(n: 4), ?x <=> ?c.bump()\n  \
             rule a2(?x) :- ?x <=> ?c.bump(), ?c <=> cnt(n: 4)\n",
            &["a1", "a2"],
        ),
        [Some(5), Some(5)]
    );
}

/// THE HEAD'S BOUND TYPES ITS VARIABLE: `?a: Int64` makes `?a.abs()` `Int64.abs`, `?c: Cnt`
/// makes `?c.bump()` `Cnt.bump`. Read without the bound, each dot was data: the terms
/// `-3.abs` and `cnt(n: 4).bump`.
#[test]
fn a_heads_bound_types_its_variable() {
    assert_eq!(
        ints(
            "wiwf14z.bound",
            "  rule h1(?a: Int64, ?x) :- ?x <=> ?a.abs()\n  \
             rule q1(?x) :- h1(-3, ?x)\n  \
             rule inner(?c: Cnt, ?x) :- ?x <=> ?c.bump()\n  \
             rule q2(?x) :- inner(cnt(n: 4), ?x)\n",
            &["q1", "q2"],
        ),
        [Some(3), Some(5)]
    );
}

/// A CALL'S RESULT TYPES THE SLOT IT FILLS, in a value slot (`?c <=> Mk.mk4()`: the `T` of
/// `<=>` is `mk4`'s `Cnt`) and as the result column of the goal `Mk.mk4(?c)`. Read without it,
/// `?c.bump()` was the term `cnt(n: 4).bump`.
#[test]
fn a_calls_result_types_the_slot_it_fills() {
    assert_eq!(
        ints(
            "wiwf14z.result",
            "  rule m1(?x) :- ?c <=> Mk.mk4(), ?x <=> ?c.bump()\n  \
             rule m2(?x) :- Mk.mk4(?c), ?x <=> ?c.bump()\n",
            &["m1", "m2"],
        ),
        [Some(5), Some(5)]
    );
}

/// A RULE GOAL READS THE CALLEE'S COLUMNS, typed as its clauses type them — `gen`'s by a
/// constructor, `fr`'s by a field read in a body the dispatch walk has rewritten to
/// `field_access`, whose `FieldOf` result is reduced at the receiver's type. Read without the
/// callee's columns, both dots were data.
#[test]
fn a_rule_goal_reads_the_callees_columns() {
    assert_eq!(
        ints(
            "wiwf14z.goal",
            "  rule gen(?c) :- ?c <=> cnt(n: 4)\n  \
             rule g1(?x) :- gen(?c), ?x <=> ?c.bump()\n  \
             rule fr(?p: P, ?y) :- ?y <=> ?p.t\n  \
             rule useFr(?z) :- fr(P(t: -3), ?y), ?z <=> ?y.abs()\n",
            &["g1", "useFr"],
        ),
        [Some(5), Some(3)]
    );
}

/// A FIELD READ TYPES THE SLOT IT FILLS: `?y <=> ?p.t` makes `?y` the field's `Int64`, in
/// either goal order. Read without it, `?y.abs()` was the term `P(t: -3).t.abs`.
#[test]
fn a_field_read_types_the_slot_it_fills() {
    assert_eq!(
        ints(
            "wiwf14z.field",
            "  rule r1(?p: P, ?x) :- ?y <=> ?p.t, ?x <=> ?y.abs()\n  \
             rule q1(?x) :- r1(P(t: -3), ?x)\n  \
             rule r2(?p: P, ?x) :- ?x <=> ?y.abs(), ?y <=> ?p.t\n  \
             rule q2(?x) :- r2(P(t: -3), ?x)\n",
            &["q1", "q2"],
        ),
        [Some(3), Some(3)]
    );
}

/// A FIELD OF A TYPED HEAD PARAMETER IS A RECEIVER (WI-20261012-RXT6S's note on 7D48J), in
/// the sigil spelling and in the parameter form (kernel-language §5.3, "The parameter form"),
/// where `p.t` reads the field of the variable `p` binds. The sigil-free `(p.t).abs()` was
/// refused, "t.name: expected resolved name", and `p.t.abs()` "names nothing"; the sigil
/// spelling bound the term `P(t: -3).t.abs`.
#[test]
fn a_field_of_a_head_parameter_is_a_receiver() {
    assert_eq!(
        ints(
            "wiwf14z.recv",
            "  rule s1(?p: P, ?x) :- ?x <=> (?p.t).abs()\n  \
             rule s2(p: P, ?x) :- ?x <=> (p.t).abs()\n  \
             rule s3(p: P, ?x) :- ?x <=> p.t.abs()\n  \
             rule s4(p: P, ?x) :- ?y <=> p.t, ?x <=> ?y.abs()\n  \
             rule q1(?x) :- s1(P(t: -3), ?x)\n  \
             rule q2(?x) :- s2(P(t: -3), ?x)\n  \
             rule q3(?x) :- s3(P(t: -3), ?x)\n  \
             rule q4(?x) :- s4(P(t: -3), ?x)\n",
            &["q1", "q2", "q3", "q4"],
        ),
        [Some(3), Some(3), Some(3), Some(3)]
    );
}

/// CONTROL, PASSES EITHER WAY: a dot on a variable a constructor types answers as its
/// written-call twin in a comparison, a goal's argument and as a goal (WI-20261008-A3FY2's
/// note on 7D48J), since WI-20260925-0RRQP.
#[test]
fn a_dot_on_a_typed_variable_answers_as_its_written_call() {
    let ns = "wiwf14z.dot";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule e1() :- ?c <=> cnt(n: 4), ?c.bump() = 5\n  \
         rule e2() :- ?c <=> cnt(n: 4), pf(?c.bump())\n  \
         rule e3() :- ?c <=> cnt(n: 4), ?c.isPos()\n",
    ));
    for rule in ["e1", "e2", "e3"] {
        let goal = crate::common::query_pattern_term(&mut kb, &format!("{ns}.{rule}()"));
        let sols = kb.resolve(&[goal], &Default::default());
        assert!(
            sols.len() == 1 && sols[0].is_definite(),
            "{rule}: holds, got {} solutions",
            sols.len()
        );
    }
}

/// A RELATION THAT CALLS ITSELF READS ITS OWN COLUMNS AS ONE TYPE: `reach`'s second clause
/// holds its column at what its own goal reads, so the relation's column is the first
/// clause's `Cnt`. Generalized as a clause that holds at every type, the column typed
/// nothing and `?c.bump()` was data.
#[test]
fn a_relation_that_calls_itself_reads_its_own_columns() {
    assert_eq!(
        ints(
            "wiwf14z.rec",
            "  rule reach(?c) :- ?c <=> cnt(n: 4)\n  \
             rule reach(?c) :- reach(?d), ?c <=> ?d\n  \
             rule useReach(?x) :- reach(?c), ?x <=> ?c.bump()\n",
            &["useReach"],
        ),
        [Some(5)]
    );
}

/// A GOAL ON ANOTHER RELATION OF ITS OWN CYCLE READS NOTHING, so the columns of `ev` and
/// `od` are each read without the other's, whichever is asked first: outside the cycle `ev`'s
/// column is its base clause's `Cnt`, and `od`'s, which only a goal on `ev` fills, is no type.
/// STATED LIMIT: `useOd`'s dot is data. Read through the memo alone, which answers nothing for
/// a relation being typed, each column would depend on which of the two was asked first.
#[test]
fn a_goal_on_a_relation_of_its_cycle_reads_nothing() {
    let ns = "wiwf14z.cycle";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule ev(?c) :- ?c <=> cnt(n: 0)\n  \
         rule ev(?c) :- od(?d), ?c <=> ?d\n  \
         rule od(?c) :- ev(?d), ?c <=> ?d\n  \
         rule useEv(?x) :- ev(?c), ?x <=> ?c.bump()\n  \
         rule useOd(?x) :- od(?c), ?x <=> ?c.bump()\n",
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.useEv")),
        Some(1)
    );
    let shown = crate::common::shown_rows(&mut kb, &format!("{ns}.useOd"));
    assert_eq!(
        shown,
        [("cnt(n: 0).bump".to_string(), true)],
        "the dot stays data"
    );
}

/// TWO CLAUSES THAT TIE THEIR COLUMNS DIFFERENTLY ARE GENERALIZED, not joined:
/// `view(some(?d), ?d)` beside `view(none, none)` holds its second column at the first's
/// element in one clause and at an `Option` in the other, so the column is no type, and `desc`
/// answers both of `ob`'s values. Joined as a citation's columns are, the second column was an
/// `Option`, `desc`'s `?d` got that bound, and the `String` was refused — github-todo's
/// `open_item` answered nothing (measured on this ticket's first cut).
#[test]
fn two_clauses_that_tie_their_columns_differently_are_generalized() {
    let ns = "wiwf14z.gen";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  entity ob(v: Option[T = String])\n  \
         fact ob(v: some(\"s\"))\n  \
         fact ob(v: none)\n  \
         rule view(some(?d), ?d) :- true\n  \
         rule view(none, none) :- true\n  \
         rule desc(?d) :- ob(v: ?o), view(?o, ?d)\n",
    ));
    let mut rows: Vec<String> = crate::common::shown_rows(&mut kb, &format!("{ns}.desc"))
        .into_iter()
        .map(|(shown, definite)| {
            assert!(definite, "{shown}: definite");
            shown
        })
        .collect();
    rows.sort();
    assert_eq!(rows, ["\"s\"", "none"]);
}

/// A PROJECTION ON A PARAMETER IN A CALL'S RESULT IS READ OFF THE ARGUMENT'S TYPE: `head(s:
/// Self) -> s.T` at `?l: List[T = Int64]` is an `Int64`. Read as a type of its own the result
/// made `?r` an `s.T`, and an `eq` beside it was refused (`wi818_executable_backing_test`).
///
/// STATED LIMIT, PASSES EITHER WAY: a construction passed where the spec's carrier is
/// declared (`head(cons(7, nil))`) is read at the spec's own parameter, which a `List` does
/// not unify with — so `hd`'s `?r` stays untyped and its dot is data.
#[test]
fn a_projection_in_a_result_is_read_off_the_argument() {
    let ns = "wiwf14z.proj";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule hd2(?l: List[T = Int64], ?x) :- ?r <=> head(?l), ?x <=> ?r.abs()\n  \
         rule q(?x) :- hd2(cons(-7, nil), ?x)\n  \
         rule hd(?x) :- ?r <=> head(cons(-7, nil)), ?x <=> ?r.abs()\n",
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.q")),
        Some(7)
    );
    let shown = crate::common::shown_rows(&mut kb, &format!("{ns}.hd"));
    assert_eq!(shown, [("-7.abs".to_string(), true)], "the dot stays data");
}

/// A TYPED HEAD ADMITS A VALUE WHOSE PART ITS BOUND FIXES AND THE VALUE DOES NOT CARRY. Found
/// here: once a call's result column types a column, the column's bound is checked as a
/// written one is, and `Result[T = Int64, E = ?e]` refused `err(error: 5)` — the value says
/// nothing of `T`, and its open type's unknown `T` met `Int64` as a type of its own. The written
/// twins answered nothing before this ticket. CONTROLS: a value its bound does not admit is
/// still refused.
#[test]
fn a_typed_head_admits_a_value_whose_part_its_bound_fixes() {
    let ns = "wiwf14z.dom";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule w1(?r: Result[T = Int64, E = ?e]) :- ?r <=> err(error: 5)\n  \
         rule w2(?r: Result[T = ?a, E = Int64]) :- ?r <=> ok(value: 5)\n  \
         rule n1(?r: Result[T = Int64, E = Bool]) :- ?r <=> err(error: 5)\n  \
         rule n2(?r: Result[T = Int64, E = ?e]) :- ?r <=> ok(value: \"s\")\n",
    ));
    for rule in ["w1", "w2"] {
        let rows = crate::common::query_unary(&mut kb, &format!("{ns}.{rule}"));
        assert!(
            rows.len() == 1 && rows[0].1,
            "{rule}: the value, got {rows:?}"
        );
    }
    for rule in ["n1", "n2"] {
        let rows = crate::common::query_unary(&mut kb, &format!("{ns}.{rule}"));
        assert!(rows.is_empty(), "{rule}: refused, got {rows:?}");
    }
}

/// A BRACKET ON A METHOD CALL OF THE PARAMETER FORM IS REFUSED, as on any dot call, which has
/// no channel for one — the refusal the `?p.t.m[…]()` spelling gets. Lowered with its bracket
/// read as an argument, the call could not be built.
#[test]
fn a_bracket_on_a_parameter_forms_method_call_is_refused() {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(
            "wiwf14z.bracket",
            "  rule s(p: P, ?x) :- ?x <=> p.t.abs[T = Int64]()\n",
        )),
        &["call-site type arguments are not supported on a dot call"],
        "a bracket on a dot call",
    );
}

/// A BRANCH OR A NEGATION TYPES NOTHING OUTSIDE IT: `pi`'s `Int64` column, read in a `|`
/// branch or under `not`, does not make `?x` an `Int64` for the conjunct beside it, which reads
/// `pc`'s `Cnt`. Read as a conjunct, it typed `?x` first, `pc`'s column disagreed, and the dot
/// was refused as a member `Int64` does not have.
#[test]
fn a_branch_or_a_negation_types_nothing_outside_it() {
    assert_eq!(
        ints(
            "wiwf14z.branch",
            "  fact pi(1)\n  fact pc(cnt(n: 4))\n  \
             rule viaOr(?y) :- (pi(?x) | pc(?x)), pc(?x), ?y <=> ?x.bump()\n  \
             rule viaNot(?y) :- not(pi(?x)), pc(?x), ?y <=> ?x.bump()\n",
            &["viaOr", "viaNot"],
        ),
        [Some(5), Some(5)]
    );
}

/// A CLAUSE THAT TYPES A COLUMN NOWHERE SAYS NOTHING OF IT: `anc`'s second clause names `?e`
/// only in its head and in its goal on `anc`, which reads nothing while `anc` is being read, so
/// the relation's column is the first clause's `Cnt`. Left out of that clause's columns, the
/// slot was dropped from the relation, and `?e.bump()` was data.
#[test]
fn a_clause_that_types_a_column_nowhere_says_nothing_of_it() {
    assert_eq!(
        ints(
            "wiwf14z.ancestry",
            "  entity par(of: Cnt, is: Cnt)\n  \
             fact par(of: cnt(n: 1), is: cnt(n: 2))\n  \
             rule anc(?c, ?e) :- par(of: ?c, is: ?e)\n  \
             rule anc(?c, ?e) :- par(of: ?c, is: ?m), anc(?m, ?e)\n  \
             rule useAnc(?x) :- anc(?a, ?e), ?x <=> ?e.bump()\n",
            &["useAnc"],
        ),
        [Some(3)]
    );
}

/// STATED LIMIT, PASSES EITHER WAY: a column whose whole type is a variable — here the join of
/// an `Int64` and a `String`, which is no type — is read at the type its use asks for:
/// `anyHolds.head.x` loads returned as an `Int64` and answers one of the two values.
#[test]
fn a_column_whose_whole_type_is_a_variable_is_read_at_any_type() {
    let ns = "wiwf14z.whole";
    let mut interp = crate::common::interp_for(&program(
        ns,
        "  fact holds(1)\n  fact holds(\"a\")\n  \
         rule anyHolds(?x) :- holds(?x)\n  \
         operation f() -> Int64 effects {Error, Error[EmptyStream]} = anyHolds.head.x\n",
    ));
    assert!(interp.call(&format!("{ns}.f"), &[]).is_ok(), "loads, and answers a value");
}

// ── What a clause's typing records, which decision 3's refusals are counted on ──────────
//
// Nothing below refuses: a late position that does not fit is recorded with its class
// (`clause_disagreements_by_this_thread`), and 068-implementation §6.2's decision 3 refuses
// the classes once they are counted. A position the operation-body typer accepts records
// nothing; one it refuses records its class.

/// What loading with `load` records of its clauses' disagreements, by class.
fn recorded<T>(load: impl FnOnce() -> T) -> (T, Vec<(&'static str, usize)>) {
    use anthill_core::kb::typing::clause_disagreements_by_this_thread;
    // The shared standard library is loaded once per binary, on the thread that asks first;
    // asked here, what it records is not counted against `load`.
    let _base = crate::common::load_stdlib_kb();
    let before: std::collections::HashMap<_, _> =
        clause_disagreements_by_this_thread().into_iter().collect();
    let out = load();
    let added = clause_disagreements_by_this_thread()
        .into_iter()
        .filter_map(|(class, n)| {
            let d = n - before.get(class).copied().unwrap_or(0);
            (d > 0).then_some((class, d))
        })
        .collect();
    (out, added)
}

/// A COLUMN WHOSE VARIABLE NOTHING IN ITS CLAUSE NAMES IS OPEN: `classify`'s second clause
/// takes every `?x`, so `classify(5, ?r)` answers through it and records nothing. Read as the
/// other clause's `Colour` — what a goal on the relation itself leaves unsaid — it recorded a
/// rule-goal disagreement.
#[test]
fn a_column_nothing_in_its_clause_names_is_open() {
    let ns = "wiwf14z.open";
    let (answers, said) = recorded(|| {
        ints(
            ns,
            "  sort Colour\n    entity red\n  end\n  \
             rule classify(?x: Colour, ?c) :- ?c <=> 1\n  \
             rule classify(?x, ?c) :- ?c <=> 2\n  \
             rule g(?r) :- classify(5, ?r)\n",
            &["g"],
        )
    });
    assert_eq!((answers, said), (vec![Some(2)], vec![]));
}

/// A `Term` SLOT TYPES NOTHING, as an operation's argument converts any value to the `Term`
/// it declares: `takes`'s column is `nonvar`'s parameter, and `5` and an `Int64` variable meet
/// it with nothing recorded. Typed `Term`, the variable disagreed with every other position.
#[test]
fn a_term_slot_types_nothing() {
    let ns = "wiwf14z.term";
    let (answers, said) = recorded(|| {
        ints(
            ns,
            "  rule takes(?g) :- anthill.reflect.nonvar(?g)\n  \
             rule viaLit(?r) :- takes(5), ?r <=> 1\n  \
             rule viaVar(?r) :- takes(?x), ?x <=> -5, ?r <=> Int64.abs(?x)\n",
            &["viaLit", "viaVar"],
        )
    });
    assert_eq!((answers, said), (vec![Some(1), Some(5)], vec![]));
}

/// AN `Option` PARAMETER IS THE CALL'S PLACEHOLDER: a bare `Int64` meets it as an operation's
/// argument does, by the some-coercion, and the variable stays the head's `Int64`. Read as
/// the variable's type, the head's bound disagreed with it. The call runs on the bare value —
/// a rule-body call does not wrap it, which is WI-20261013-R1W5A's (C1c types the call as an
/// operation body is); `len` here does not read its argument.
#[test]
fn an_option_parameter_is_the_calls_placeholder() {
    let ns = "wiwf14z.option";
    let (answers, said) = recorded(|| {
        ints(
            ns,
            "  sort Opt\n    operation len(o: Option[T = Int64]) -> Int64 = 1\n  end\n  \
             rule viaHead(?a: Int64, ?r) :- ?r <=> Opt.len(?a)\n  \
             rule g(?r) :- viaHead(3, ?r)\n",
            &["g"],
        )
    });
    assert_eq!((answers, said), (vec![Some(1)], vec![]));
}

/// A BRACKET ENTRY IS NO DATA: `p.E` in `require[Desc[T = p.E]]` is a projection written as a
/// term, and the head parameter in it is not typed at its `value` field (`NodeOccurrence`).
/// Typed there, the head's bound `Box` disagreed with it.
#[test]
fn a_bracket_entry_types_nothing() {
    let ns = "wiwf14z.bracketentry";
    let (answers, said) = recorded(|| {
        ints(
            ns,
            "  sort Desc\n    sort T = ?\n    operation tag() -> Int64\n  end\n  \
             sort Red\n    import anthill.prelude.Int64\n    entity red\n    \
             provides Desc[T = Red]\n    operation tag() -> Int64 = 7\n  end\n  \
             sort Box\n    sort E = ?\n    entity box(v: E)\n  end\n  \
             rule anchored(p: Box, ?r) :- ?d = require[Desc[T = p.E]], Desc.tag(?r)\n  \
             rule g(?r) :- anchored(box(v: red()), ?r)\n",
            &["g"],
        )
    });
    assert_eq!((answers, said), (vec![Some(7)], vec![]));
}

/// A BOUND THE LOADER REFUSES IS READ AS UNWRITTEN: one naming a sort that does not resolve,
/// and one at a spec over its parameter, are each refused once where they are written, and
/// the clause typing reads neither. Read, each disagreed with the column `item` gives the
/// variable.
#[test]
fn a_refused_bound_is_read_as_unwritten() {
    let ns = "wiwf14z.refusedbound";
    for (bound, refusal) in [
        ("NoSuchSortAnywhere", "unresolved name 'NoSuchSortAnywhere'"),
        ("Sizer", "a rule variable is typed `wiwf14z.refusedbound.Sizer`"),
    ] {
        let (errors, said) = recorded(|| {
            crate::common::load_errors_of(&program(
                ns,
                &format!(
                    "  sort Sizer\n    sort T = ?\n    operation size(a: T) -> Int64\n  end\n  \
                     fact item(1)\n  rule f(?x: {bound}) :- item(?x)\n"
                ),
            ))
        });
        assert!(
            errors.len() == 1 && errors[0].contains(refusal) && said.is_empty(),
            "{bound}: {errors:#?} {said:?}"
        );
    }
}

/// A BODY THAT FIXES THE SORT'S PARAMETER THROUGH A GOAL is that class, as through a
/// construction: `bx` answers only `Box2[T = Int64]` values, where `pr` holds at every `T`.
/// Recorded as a rule-goal disagreement before it was told apart.
#[test]
fn a_goal_that_fixes_the_sorts_parameter_is_that_class() {
    let ns = "wiwf14z.fixedbygoal";
    let (_, said) = recorded(|| {
        crate::common::load_kb_with(&program(
            ns,
            "  rule bx(?x) :- ?x <=> NS.Box2.b2(v: 5)\n  \
             sort Box2[T]\n    entity b2(v: T)\n    rule pr(?x: Box2[T = T]) :- bx(?x)\n  end\n",
        ))
    });
    assert_eq!(said, [("sort parameter fixed", 1)]);
}

/// A COLLECTION LITERAL IS ITS COLLECTION: `item`'s facts hold the tuples `(x: 1)` and `(x:
/// true)`, and `f`'s bound `(x: Int64)` reads the one that fits with nothing recorded; `viaBody`
/// builds `(x: 1)` and `viaHead` reads one out of `mk`'s head, each handed to `pair`'s column
/// `(x: Int64)`; `one`'s column is the tuple `(x: Int64)`, so the field read on the value
/// `viaDot` reads out of it is an `Int64`'s, and `abs` answers. Read as the reflect
/// `TupleLiteral` entity a tuple is stored as, the fact's column and `mk`'s each disagreed
/// with the bound, and the field read was refused, a member `TupleLiteral` does not have.
#[test]
fn a_collection_literal_is_its_collection() {
    let ns = "wiwf14z.literal";
    let (answers, said) = recorded(|| {
        let mut kb = crate::common::load_kb_with(&program(
            ns,
            "  fact item((x: 1))\n  fact item((x: true))\n  \
             rule f(?x: (x: Int64)) :- item(?x)\n  \
             rule pair(?p: (x: Int64)) :- true\n  \
             rule viaBody(?r) :- ?t <=> (x: 1), pair(?t), ?r <=> 1\n  \
             rule mk((x: ?a)) :- ?a <=> 1\n  \
             rule viaHead(?r) :- mk(?t), pair(?t), ?r <=> 1\n  \
             fact one((x: -3))\n  \
             rule viaDot(?r) :- one(?t), ?r <=> ?t.x.abs()\n",
        ));
        (
            crate::common::query_unary(&mut kb, &format!("{ns}.f")).len(),
            crate::common::one_definite_int(&mut kb, &format!("{ns}.viaBody")),
            crate::common::one_definite_int(&mut kb, &format!("{ns}.viaHead")),
            crate::common::one_definite_int(&mut kb, &format!("{ns}.viaDot")),
        )
    });
    assert_eq!((answers, said), ((1, Some(1), Some(1), Some(3)), vec![]));
}

/// WHAT THE SOME-COERCION BINDS IS THE CALL'S: `?a: Int64` meets `pick`'s `Option[T = A]`
/// as its element, so `A` is `Int64`, and `?b`, at `A`, is an `Int64` — the dot on it is
/// `Int64.abs`. Kept only as the check's verdict, `A` stayed open and the dot was data.
#[test]
fn what_the_some_coercion_binds_is_the_calls() {
    let ns = "wiwf14z.coercionbinds";
    let (answers, said) = recorded(|| {
        ints(
            ns,
            "  sort Opt2\n    operation pick[A](x: Option[T = A], y: A) -> A = y\n  end\n  \
             rule viaPick(?a: Int64, ?b, ?r) :- ?c <=> Opt2.pick(?a, ?b), ?r <=> ?b.abs()\n  \
             rule g(?r) :- viaPick(3, -4, ?r)\n",
            &["g"],
        )
    });
    assert_eq!((answers, said), (vec![Some(4)], vec![]));
}

/// A COLUMN OF OCCURRENCES QUOTES ITS ARGUMENT (user, 2026-10-22): `synth_int`'s column is
/// `occurrence_term`'s `NodeOccurrence`, and `synth_int(42, ?n)` reads `42`'s occurrence,
/// with nothing recorded. Met as a type, `42`'s `Int64` disagreed with the column. The
/// operation-body twin, `q(42)` at `e: NodeOccurrence`, stays refused.
#[test]
fn a_column_of_occurrences_quotes_its_argument() {
    let ns = "wiwf14z.occurrence";
    let (answers, said) = recorded(|| {
        ints(
            ns,
            "  import anthill.reflect.{occurrence_term}\n  \
             import anthill.reflect.Expr.{int_lit}\n  \
             rule synth_int(?e, 1) :- occurrence_term(?e, int_lit(value: ?))\n  \
             rule g(?n) :- synth_int(42, ?n)\n",
            &["g"],
        )
    });
    assert_eq!((answers, said), (vec![Some(1)], vec![]));
}
