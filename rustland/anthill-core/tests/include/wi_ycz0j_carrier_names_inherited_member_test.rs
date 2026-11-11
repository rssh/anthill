//! WI-20261102-YCZ0J — A SORT'S NAME REACHES THE MEMBERS ITS PROVISIONS LEND. `Carrier.op(…)`,
//! for an `op` the carrier does not declare and a spec it provides does, is that spec's
//! operation called at the carrier's instance: the member a dot on a value of the carrier
//! reaches, chosen by the same order (kernel-language §8.7). Decided with the user, 2026-11-11.
//!
//! Over `sort Mk { sort C = ?; operation e() -> C; operation viaDefault() -> C = e();
//! operation viaRecv(c: C) -> Int64 = 5 }` and `sort A { entity a(n: Int64); provides Mk[C =
//! A]; operation e() -> A = a(n: 1) }`, `A.viaDefault()` is `Mk[C = A].viaDefault()`, and
//! `List.isEmpty(xs)` is `Stream.isEmpty(xs)` held to a list. Before, each was refused at load,
//! "unknown functor … Fix the spelling, or import the namespace that declares `A.viaDefault`",
//! while `a(n: 9).viaRecv()` and `[1, 2].isEmpty()` ran.
//!
//! The loader reads such a name as the dot on the sort's type value, where a `provides` the
//! sort writes names a sort declaring the member (`written_provisions_lend`); the typer answers
//! that dot with the member the sort's own provisions lend (`spec_op_lent_by_own_provisions`),
//! the receiver binds the spec's parameters as the sort's provision binds them
//! (`seed_provider_receiver`), and where the sort IS a value of the spec (`List provides
//! Stream`) each argument the spec types by itself is held to the sort
//! (`pin_provider_receiver_arguments`). A witness's provision (`sort W2 provides Mk[C = A]`)
//! has its own members at `A`, and a call at `A` would run `A`'s: the default reached through
//! `W2`'s name is refused, naming the witness.
//!
//! Found beside it: a receiver naming a sort that is not the callee's own bound nothing, so
//! `Numeric[T = String].add(1, 2)` loaded and answered 3. The receiver reads the provision now.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: a call runs to its value, a refusal is asserted by its
//! words. The bracket in a row's comment is the verdict on 9d9570ae, measured 2026-11-11 with
//! the debug CLI.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! FOURTEEN PARTS, each backed out alone by a temporary switch over a binary of this file and the
//! 34 suites nearest the change — the provision rung (`wi_x9rrn`), the companion receiver
//! (`wi_w6jh0`, `wi_rs2g4`), the dot on a type value (`wi_papx0` ×2, `wi_qk77s`, `wi_a3fy2`,
//! `wi_1y96b`, `wi_rxt6s`), dot dispatch through provisions (`wi281`, `wi450`, `wi492`,
//! `wi614`, `wi1035` and the four suites it borrows from), aliases and paths (`wi_hzvqa`,
//! `wi_n2865`, `wi_xftc7`, `wi752`, `wi_4bxdw`), paren-less citations (`wi_5g28a`,
//! `wi_r653s`), brackets (`wi_bad3v`, `wi_8k7w0`, `wi_tx0g6`, `wi1119`, `wi_6b67s`), and
//! `wi_c6gk8`, `wi_shed7`, `x13yv`: 420 rows, green with nothing backed out. Measured
//! 2026-11-11.
//!
//! 1. THE TYPER'S RUNG (`written_sort_dot` reading `spec_op_lent_by_own_provisions`). 15 FAIL:
//!    every row the file then had (18) but the three controls named below.
//! 2. THE RECEIVER BINDING THE SPEC'S PARAMETERS (`seed_provider_receiver`). 8 FAIL:
//!    [`a_default_the_carrier_inherits_is_called_through_its_name`] and every row that calls
//!    `viaDefault` (`C` left open) — the paren-less, path and alias, `let`, eponymous and rule
//!    body rows — [`the_carriers_instance_takes_no_other_carrier`] (a `B` accepted), and
//!    [`a_conversions_receiver_binds_the_spec_it_converts_to`] (`Numeric[T = String]` loads).
//! 3. THE HOLD ON A SELF-TYPED ARGUMENT (`pin_provider_receiver_arguments`). 2 FAIL:
//!    [`a_spec_its_providers_are_holds_its_receiver_to_the_named_sort`] and
//!    [`a_bracket_on_the_receiver_names_the_instance`], whose `List[T = String]` is refused
//!    by the hold.
//! 4. THE WITNESS REFUSAL (`witness_route_only`). 1 FAILS:
//!    [`a_default_through_a_witness_is_refused_naming_the_witness`].
//! 5. A CARRIER THAT IS A PARAMETER OF THE PROVIDER IS NO WITNESS (`witness_route_only`'s
//!    `type_param_global_var` test). 1 FAILS: [`a_conversions_receiver_binds_the_spec_it_converts_to`],
//!    `let t = Numeric` then `t.add(1, 2)` refused as a witness at `Numeric.T`.
//! 6. THE LOADER'S CALL RUNG (`dot_call_receiver_chain`'s rung 4). 10 FAIL: every applied
//!    `Sort.member(…)` in an operation body.
//! 7. THE LOADER'S PAREN-LESS RUNG (`try_lending_sort_dot`). 1 FAILS:
//!    [`the_name_without_parentheses_is_the_call`].
//! 8. THE LOADER'S BRACKETED RECEIVER (`lent_through_written_receiver`). 1 FAILS:
//!    [`a_bracket_on_the_receiver_names_the_instance`].
//! 9. THE RULE BODY'S READING (`lending_sort_method_call`, both spellings). 2 FAIL:
//!    [`a_rule_body_reads_the_name_as_an_operation_body_does`] and
//!    `wi_x9rrn_provided_member_address_test::the_qualified_population_is_contained_in_the_member_imports`,
//!    whose `TotalFloat.neq(?a, ?a)` is a rule-body goal.
//! 10. THE SORT'S TYPE VALUE AS THE RECEIVER (`push_sort_receiver`, in place of the bare
//!    name's reading). 1 FAILS: [`an_eponymous_sort_names_the_member`].
//! 11. THE CLAUSE TERM'S READING (`lent_member_dot_term`, measured over this file alone).
//!    1 FAILS: [`an_equation_side_reads_the_name_as_its_twins`], refused "equation
//!    replacement term `A.viaRecv` names nothing".
//! 12. THE CALL'S OWN BRACKET ON A WRITTEN RECEIVER (`written_sort_dot`'s `lent_with_bracket`,
//!    over this file alone). 1 FAILS: [`the_calls_own_bracket_is_read`].
//! 13. A RECEIVER TYPE HOLDING A VALUE LOWERED TO ITS TERM (`lent_through_written_receiver`,
//!    over this file alone). 1 FAILS: [`a_receiver_holding_a_value_names_its_instance`].
//! 14. AN EFFECT GUARD LEFT OUT OF THE CLAUSE TERM'S READING (`in_effect_guard`, measured with
//!    the debug CLI and by the full gate before it was added). FAILS:
//!    [`an_effect_guard_keeps_the_name_it_spells`] and
//!    `wi_x5sb4_guard_refutation_test::a_guard_goal_that_names_nothing_is_refused_where_it_is_written`:
//!    the guard loaded and `dz([])` ran to 1 without its `Error[DivisionByZero]`.
//!
//! PASSES UNDER EVERY PART, by design: [`the_working_spellings_are_unchanged`],
//! [`a_member_the_sort_declares_wins`] and [`a_misspelled_member_is_still_an_unknown_functor`].

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, query_unary, run_int64,
};

const MK: &str = "
  sort Mk
    sort C = ?
    operation e() -> C
    operation viaDefault() -> C = e()
    operation viaRecv(c: C) -> Int64 = 5
  end

  sort A
    entity a(n: Int64)
    provides Mk[C = A]
    operation e() -> A = a(n: 1)
  end
";

/// A program whose `go()` is `body`, beside `Mk`, `A` and `decls`.
fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String, List, Stream, Bool, Option, Numeric}}\n  import anthill.prelude.Option.{{some, none}}\n{MK}\n{decls}\n  operation go() -> Int64 =\n{body}\nend\n"
    )
}

fn runs(ns: &str, decls: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, body), &format!("{ns}.go"))
}

fn errors(ns: &str, decls: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(ns, decls, body))
}

/// `n` of the `A` an expression of type `A` gives.
fn n_of(expr: &str) -> String {
    format!("    match {expr}\n      case a(n) -> n")
}

// ── The ticket's programs ───────────────────────────────────────────────────

/// [refused, unknown functor] The default `A` inherits, run at `A`'s instance: `e()` is `A`'s.
#[test]
fn a_default_the_carrier_inherits_is_called_through_its_name() {
    assert_eq!(runs("t.ycz0j.dflt", "", &n_of("A.viaDefault()")), Ok(1));
}

/// [refused, unknown functor] A default taking the carrier.
#[test]
fn a_default_taking_the_carrier_is_called_through_its_name() {
    assert_eq!(runs("t.ycz0j.recv", "", "    A.viaRecv(a(n: 9))"), Ok(5));
}

/// [refused, unknown functor] `List.isEmpty` is `Stream`'s member at a list, as
/// `[1, 2].isEmpty()` is.
#[test]
fn a_stdlib_carrier_names_the_member_its_provision_lends() {
    let body = "    if List.isEmpty([1, 2]) then 1 else 0";
    assert_eq!(runs("t.ycz0j.lst", "", body), Ok(0));
    let body = "    let e: List[T = Int64] = []\n    if List.isEmpty(e) then 1 else 0";
    assert_eq!(runs("t.ycz0j.lste", "", body), Ok(1));
    let body = "    List.size([1, 2, 3])";
    assert_eq!(runs("t.ycz0j.lsz", "", body), Ok(3));
}

/// Controls: the spellings that ran before run alike.
#[test]
fn the_working_spellings_are_unchanged() {
    assert_eq!(runs("t.ycz0j.c1", "", "    a(n: 9).viaRecv()"), Ok(5));
    assert_eq!(runs("t.ycz0j.c2", "", &n_of("Mk[C = A].viaDefault()")), Ok(1));
    assert_eq!(runs("t.ycz0j.c3", "", &n_of("A.e()")), Ok(1));
    let body = "    if [1, 2].isEmpty() then 1 else 0";
    assert_eq!(runs("t.ycz0j.c4", "", body), Ok(0));
    let body = "    if Stream.isEmpty([1, 2]) then 1 else 0";
    assert_eq!(runs("t.ycz0j.c5", "", body), Ok(0));
}

// ── Every spelling of the name ──────────────────────────────────────────────

/// [refused, unknown functor] Without parentheses the name is the call, as `A.e` is.
#[test]
fn the_name_without_parentheses_is_the_call() {
    assert_eq!(runs("t.ycz0j.pl", "", &n_of("A.viaDefault")), Ok(1));
}

/// [refused, unknown functor] Through the namespace's path, and through an alias.
#[test]
fn a_path_and_an_alias_name_the_same_member() {
    assert_eq!(runs("t.ycz0j.path", "", &n_of("t.ycz0j.path.A.viaDefault()")), Ok(1));
    assert_eq!(runs("t.ycz0j.al", "  sort AA = A\n", &n_of("AA.viaDefault()")), Ok(1));
}

/// [refused, no such member (dot dispatch)] A `let` holding the sort reaches it too.
#[test]
fn a_let_holding_the_sort_reaches_the_member() {
    let body = "    let t = A\n".to_string() + &n_of("t.viaDefault()");
    assert_eq!(runs("t.ycz0j.let", "", &body), Ok(1));
    let body = "    let l = List\n    if l.isEmpty([1, 2]) then 1 else 0";
    assert_eq!(runs("t.ycz0j.letl", "", body), Ok(0));
}

/// [refused, unknown functor] A bracket on the receiver binds the sort's parameters, as on an
/// operation the sort declares: at `T = String` a list of integers is no argument.
#[test]
fn a_bracket_on_the_receiver_names_the_instance() {
    let body = "    if List[T = Int64].isEmpty([1, 2]) then 1 else 0";
    assert_eq!(runs("t.ycz0j.br", "", body), Ok(0));
    let body = "    if List[T = String].isEmpty([1, 2]) then 1 else 0";
    assert_refused_naming(
        &errors("t.ycz0j.brs", "", body),
        &["isEmpty.s", "expected List[T = String], got List[T = Int64]"],
        "the bracket's instance is the argument's type",
    );
}

/// [refused, unknown functor] The call's own bracket is read as on a member the sort
/// declares, with or without a bracket on the receiver; on a `let` holding the sort it is
/// refused, as on any member, with the advice to write the call on the sort.
#[test]
fn the_calls_own_bracket_is_read() {
    let found = |call: &str| format!("    match {call}\n      case some(v) -> v\n      case none() -> 0");
    let bare = found("List.find[EffP = {}]([1, 2, 3], lambda x -> x > 1)");
    assert_eq!(runs("t.ycz0j.cb", "", &bare), Ok(2));
    let both = found("List[T = Int64].find[EffP = {}]([1, 2, 3], lambda x -> x > 1)");
    assert_eq!(runs("t.ycz0j.cbb", "", &both), Ok(2));
    let held = "    let t = List\n".to_string() + &found("t.find[EffP = {}]([1, 2, 3], lambda x -> x > 1)");
    assert_refused_naming(
        &errors("t.ycz0j.cbl", "", &held),
        &["not read on a receiver that denotes a sort", "`Sort.find[…](…)`"],
        "a `let` holding the sort reads no bracket",
    );
}

/// [refused, unknown functor] A receiver whose bracket holds a value names its instance too.
#[test]
fn a_receiver_holding_a_value_names_its_instance() {
    let decls = "  sort Sq2\n    operation size(s: Self) -> Int64\n    operation twice(s: Self) -> Int64 = size(s) * 2\n  end\n  sort Buf\n    sort T = ?\n    sort N = ?\n    entity buf(v: T)\n    provides Sq2\n    operation size(s: Self) -> Int64 = 3\n  end\n";
    assert_eq!(runs("t.ycz0j.val", decls, "    Buf[T = Int64, N = 3].twice(buf(v: 1))"), Ok(6));
}

/// [refused, `P` constructed without its field] An eponymous sort's bare name is its
/// construction (§4.4); as the receiver of a member its provisions lend it is the sort.
#[test]
fn an_eponymous_sort_names_the_member() {
    let decls = "  sort P\n    entity P(n: Int64)\n    provides Mk[C = P]\n    operation e() -> P = P(n: 4)\n  end\n";
    let body = "    match P.viaDefault()\n      case P(n) -> n";
    assert_eq!(runs("t.ycz0j.ep", decls, body), Ok(4));
}

/// [refused, unknown functor] In a generic body and in the carrier's own body.
#[test]
fn the_name_is_read_in_a_generic_body_and_the_carriers_own() {
    let decls = "  operation emp[T](xs: List[T = T]) -> Bool = List.isEmpty(xs)\n";
    let body = "    if emp([\"a\"]) then 1 else 0";
    assert_eq!(runs("t.ycz0j.gen", decls, body), Ok(0));
    let decls = "  sort B\n    entity b(n: Int64)\n    provides Mk[C = B]\n    operation e() -> B = b(n: 2)\n    operation own() -> Int64 = B.viaRecv(b(n: 3)) + 1\n  end\n";
    assert_eq!(runs("t.ycz0j.own", decls, "    B.own()"), Ok(6));
}

/// The member chosen is the one the dot chooses: `List.map` is `FiniteCollection`'s, nearer
/// than `Iterable`'s, so the two spellings give one result type, refused at a `List` alike.
#[test]
fn the_member_chosen_is_the_dots() {
    let refusal = |ns: &str, call: &str| {
        let body = format!("    let ys: List[T = Int64] = {call}\n    1");
        errors(ns, "", &body)
            .into_iter()
            .find(|e| e.contains("ys.annotation"))
            .map(|e| e.split_once("got ").map(|(_, got)| got.to_string()).unwrap_or(e))
    };
    let named = refusal("t.ycz0j.mapn", "List.map([1, 2], lambda x -> x + 1)");
    let dotted = refusal("t.ycz0j.mapd", "[1, 2].map(lambda x -> x + 1)");
    assert!(
        named.as_deref().is_some_and(|t| t.starts_with("MappedStream[")),
        "`List.map` is `FiniteCollection.map`, got {named:?}"
    );
    assert_eq!(named, dotted, "one member, one result type");
}

// ── The instance ────────────────────────────────────────────────────────────

/// [refused, unknown functor] The call is at `A`'s instance: a `B` is no argument.
#[test]
fn the_carriers_instance_takes_no_other_carrier() {
    let decls = "  sort B\n    entity b(n: Int64)\n    provides Mk[C = B]\n    operation e() -> B = b(n: 2)\n  end\n";
    assert_refused_naming(
        &errors("t.ycz0j.ab", decls, "    A.viaRecv(b(n: 9))"),
        &["viaRecv.c", "expected A, got B"],
        "`A.viaRecv` takes an `A`",
    );
}

const SQ: &str = "
  sort Sq
    operation size(s: Self) -> Int64
    operation twice(s: Self) -> Int64 = size(s) * 2
  end
  sort Bag
    entity bag(n: Int64)
    provides Sq
    operation size(s: Bag) -> Int64 = match s
      case bag(n) -> n
  end
  sort Pile
    entity pile(n: Int64)
    provides Sq
    operation size(s: Pile) -> Int64 = 100
  end
";

/// [refused, unknown functor] A spec its providers ARE (`Sq` receives on itself): the
/// argument the spec types by itself is held to the named sort, and the call runs its
/// instance. Without the hold `Bag.twice(pile(n: 4))` would run `Pile`'s, 200.
#[test]
fn a_spec_its_providers_are_holds_its_receiver_to_the_named_sort() {
    assert_eq!(runs("t.ycz0j.sq", SQ, "    Bag.twice(bag(n: 4))"), Ok(8));
    assert_refused_naming(
        &errors("t.ycz0j.sqp", SQ, "    Bag.twice(pile(n: 4))"),
        &["twice.s", "expected Bag, got Pile"],
        "`Bag.twice` takes a `Bag`",
    );
    assert_refused_naming(
        &errors("t.ycz0j.lso", "", "    if List.isEmpty(some(1)) then 1 else 0"),
        &["isEmpty.s", "expected List[T = ?T], got Option[T = Int64]"],
        "`List.isEmpty` takes a list",
    );
}

/// A member the sort declares is its own, whatever its provisions lend under the name.
#[test]
fn a_member_the_sort_declares_wins() {
    let decls = "  sort A2\n    entity a2(n: Int64)\n    provides Mk[C = A2]\n    operation e() -> A2 = a2(n: 1)\n    operation viaRecv(c: A2) -> Int64 = 7\n  end\n";
    assert_eq!(runs("t.ycz0j.own2", decls, "    A2.viaRecv(a2(n: 9))"), Ok(7));
}

const W2: &str = "
  sort W2
    provides Mk[C = A]
    operation e() -> A = a(n: 3)
  end
";

/// [refused, unknown functor] A witness's provision has its members at `A`; a call at `A`
/// runs `A`'s instance (`Mk[C = A].viaDefault()` answers 1 beside `W2`), so the default
/// reached through `W2`'s name is refused rather than run at the wrong instance.
#[test]
fn a_default_through_a_witness_is_refused_naming_the_witness() {
    assert_refused_naming(
        &errors("t.ycz0j.w", W2, &n_of("W2.viaDefault()")),
        &["`viaDefault` is `t.ycz0j.w.Mk.viaDefault`", "provides as a witness at `t.ycz0j.w.A`"],
        "a witness's instance is not the carrier's",
    );
    assert_eq!(runs("t.ycz0j.wc", W2, &n_of("Mk[C = A].viaDefault()")), Ok(1));
    assert_eq!(runs("t.ycz0j.we", W2, &n_of("W2.e()")), Ok(3));
}

/// A name no provision lends keeps its refusal.
#[test]
fn a_misspelled_member_is_still_an_unknown_functor() {
    assert_refused_naming(
        &errors("t.ycz0j.typo", "", "    A.vaDefault()"),
        &["unknown functor", "Fix the spelling", "`A.vaDefault`"],
        "a typo is a typo",
    );
}

// ── A receiver naming a provider of the callee's spec ───────────────────────

/// [loads, 3] `Numeric[T = String].add(1, 2)`: the receiver names `Numeric`, which provides
/// `Additive[T = T]`, and its bracket was dropped. It binds `Additive`'s `T` now.
#[test]
fn a_conversions_receiver_binds_the_spec_it_converts_to() {
    assert_refused_naming(
        &errors("t.ycz0j.nums", "", "    Numeric[T = String].add(1, 2)"),
        &["add.a", "expected String, got Int64"],
        "the receiver's `T` is the spec's",
    );
    assert_eq!(runs("t.ycz0j.numi", "", "    Numeric[T = Int64].add(1, 2)"), Ok(3));
    assert_eq!(runs("t.ycz0j.numb", "", "    Numeric.add(1, 2)"), Ok(3));
    // [refused, no such member (dot dispatch)]
    assert_eq!(runs("t.ycz0j.numl", "", "    let t = Numeric\n    t.add(1, 2)"), Ok(3));
}

// ── In a clause's own text ──────────────────────────────────────────────────

/// [refused, equation replacement term names nothing] An equation's right-hand side reads the
/// name as its twins `(A).viaRecv(?x)` and `Mk.viaRecv(?x)` are read: the rewrite runs.
#[test]
fn an_equation_side_reads_the_name_as_its_twins() {
    let decls = "  operation twice(x: A) -> Int64
  rule twice(?x) <=> A.viaRecv(?x) * 2 @[simp]
";
    assert_eq!(runs("t.ycz0j.simp", decls, "    twice(a(n: 1))"), Ok(10));
    let decls = "  operation twice(x: A) -> Int64
  rule twice(?x) <=> (A).viaRecv(?x) * 2 @[simp]
";
    assert_eq!(runs("t.ycz0j.simpt", decls, "    twice(a(n: 1))"), Ok(10));
}

/// An effect guard does not dispatch a dot (§5.5), so the name stays the one it spells
/// there and is refused as naming nothing. Read as the dot on `List`, the goal matched no
/// clause, its negation held, and `dz([])` loaded without the effect it performs.
#[test]
fn an_effect_guard_keeps_the_name_it_spells() {
    let guarded = |ns: &str, guard: &str, imports: &str| {
        format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64, List, Error, DivisionByZero}}\n{imports}  operation dz(xs: List[T = Int64]) -> Int64 effects {{Error[DivisionByZero] :- {guard}}} = 1\n  operation go() -> Int64 = dz([])\nend\n"
        )
    };
    assert_refused_naming(
        &load_errors_of(&guarded("t.ycz0j.guard", "List.isEmpty(xs)", "")),
        &["effect guard goal `List.isEmpty` names nothing"],
        "a guard reads no dot on a sort",
    );
    // The application decides the call, and the effect is charged.
    let applied = guarded("t.ycz0j.guarda", "isEmpty(xs)", "  import anthill.prelude.Iterable.{isEmpty}\n");
    assert_refused_naming(
        &load_errors_of(&applied),
        &["go.effects", "Error[T = DivisionByZero]"],
        "the guard's application charges the effect",
    );
}

// ── In a rule body ──────────────────────────────────────────────────────────

/// [refused, rule-body term names nothing] A rule body reads the name as an operation body
/// does, applied and without parentheses.
#[test]
fn a_rule_body_reads_the_name_as_an_operation_body_does() {
    let src = format!(
        "namespace t.ycz0j.rb\n  import anthill.prelude.{{Int64, List}}\n{MK}\n  rule r1(?x) :- ?x <=> A.viaRecv(a(n: 1))\n  rule r2(?x) :- ?x <=> List.size([1, 2, 3])\n  rule r3(?x) :- A.viaRecv(a(n: 1)) = 6, ?x <=> 1\n  rule r4(?n) :- ?x <=> A.viaDefault, ?x <=> a(n: ?n)\nend\n"
    );
    let mut kb = load_kb_with(&src);
    let int = |answers: Vec<(anthill_core::eval::Value, bool)>| -> Vec<i64> {
        answers
            .into_iter()
            .map(|(v, definite)| match v {
                anthill_core::eval::Value::Int(i) if definite => i,
                other => panic!("a definite Int64, got {other:?} (definite: {definite})"),
            })
            .collect()
    };
    assert_eq!(int(query_unary(&mut kb, "t.ycz0j.rb.r1")), vec![5]);
    assert_eq!(int(query_unary(&mut kb, "t.ycz0j.rb.r2")), vec![3]);
    assert!(query_unary(&mut kb, "t.ycz0j.rb.r3").is_empty(), "`viaRecv` answers 5, not 6");
    assert_eq!(int(query_unary(&mut kb, "t.ycz0j.rb.r4")), vec![1], "`A.viaDefault` is `a(n: 1)`");
}
