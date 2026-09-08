//! WI-742 (proposal 060 §2, §2.1) — a `?x: T` annotation on a RELATIONAL rule head
//! compiles to a generated `domain(?x, T)` body goal.
//!
//! The annotation used to be legal only on a `[simp]`/`[unfold]` EQUATION (WI-582),
//! because the resolver's rewrite path was the only site that enforced it. Proposal
//! 060's rule gives it a second reader that is an ORDINARY GOAL: the loader installs
//! the bound as before, and the typer prepends `domain(?x, T)` to the clause body
//! (`typing::install_typed_head_domain_goals`). At run time that goal only READS the
//! value's carried type (`value_type_term`, WI-578) — no typing operation.
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT, stated per group:
//!
//!  * `lifting the loader refusal` (`load.rs`'s `NotARewrite` arm, restored for a
//!    relational head) — EVERY test here fails at load.
//!  * `install_typed_head_domain_goals` (the typer sweep deleted) — the FILTER rows
//!    fail: `filters_a_non_conforming_binding`, `mode_in_selects_per_carrier`,
//!    `a_bodyless_typed_head_still_guards`, `refutes_after_a_later_goal_binds`,
//!    `an_undischarged_guard_residualizes`, and the C666A dispatch row. The load-only
//!    rows and the column-type rows keep passing, which is exactly why they are not
//!    the evidence that anything RUNS.
//!  * `BuiltinTag::TypeDomain`'s three-valued arm (Suspend → Failure) —
//!    `delays_then_holds_when_a_later_goal_binds` and
//!    `an_undischarged_guard_residualizes` fail; the mode-(in) rows pass either way.
//!  * `typed_head_guards_its_own_carrier` (the C666A admission) — the two C666A
//!    admission rows fail at load; the three refusal rows pass either way BY DESIGN,
//!    which is what makes them controls rather than duplicates.
//!  * `convert_rule_head_with_params` (§2.1) — the four `parameter_form_*` rows fail;
//!    every other row passes either way.
//!  * `load_rule`'s parameter-map clear wrapper —
//!    `parameter_names_do_not_leak_past_their_rule` fails; every other row passes either
//!    way, which is what makes it its own axis.
//!  * `parse_arg_type_name_of`'s dotted and applied arms —
//!    `a_parameter_type_may_be_written_qualified_or_applied` fails on the dotted and
//!    applied rows; its `pick_bare` and `pick_sigil` rows pass either way BY DESIGN and
//!    are the yardsticks the other two must meet.
//!  * `head_type_annotation_names`' named-arg leg —
//!    `the_parameter_spelling_earns_the_same_c666a_admission` fails at load; the sigil
//!    spelling's admission row passes either way.
//!
//! NO ROW PINS AN "UNRESOLVED BARE NAME IN A HEAD" REFUSAL, deliberately — see
//! [`an_unresolved_bare_head_name_stays_a_symbolic_constant`], which is what such a
//! refusal would break.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// Solutions whose residual set is EMPTY — a definite row, as opposed to a
/// conditional answer carrying an undischarged goal. The distinction is the whole
/// point of the flounder rows: a typed head must never present an unchecked binding
/// as a definite answer.
fn definite_answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// Two carriers under one relation: `Colour` values and a `Thing` value, all rows of
/// the same `item` fact table. The typed clause must keep only the `Colour` rows; the
/// untyped twin beside it is the control that the FACTS admit both.
const FILTER_SRC: &str = r#"
namespace test.wi742.filter
  import anthill.prelude.{Int64}

  sort Colour
    entity red
    entity green
  end
  sort Thing
    entity thing(n: Int64)
  end

  fact item(red())
  fact item(green())
  fact item(thing(n: 1))

  rule colours(?x: Colour) :- item(?x)
  rule anything(?x) :- item(?x)
end
"#;

#[test]
fn a_relational_typed_head_loads() {
    // The WI-582 refusal is gone for this shape. Loud-error-only: the rows below are
    // what show it RUNS.
    let kb = crate::common::load_kb_with(FILTER_SRC);
    assert!(kb.try_resolve_symbol("test.wi742.filter.colours").is_some());
}

#[test]
fn filters_a_non_conforming_binding() {
    let mut kb = crate::common::load_kb_with(FILTER_SRC);
    // 2 of the 3 rows: `thing(n: 1)` is refuted by the generated guard.
    assert_eq!(answers(&mut kb, "test.wi742.filter.colours(?x)"), 2);
    // THE CONTROL, and it shares no fixture accident with the arm above: the same
    // three facts, the same clause shape, only the annotation removed.
    assert_eq!(answers(&mut kb, "test.wi742.filter.anything(?x)"), 3);
}

#[test]
fn an_untagged_equation_keeps_its_refusal() {
    // Proposal 060 §2's one explicit carve-out: an untagged equational head has
    // neither reader — no rewrite fires it, and it is not a relational clause.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace test.wi742.eqn
  import anthill.prelude.{Int64}
  sort Colour
    entity red
  end
  sort Lib
    sort A = ?
    operation keep(x: A, y: A) -> A
    -- `<=>`, not `=`: `=` at a bodyless head is refused for its OWN reason (WI-888),
    -- which would make this row measure that refusal instead of this one.
    rule keep(?x: Colour, ?y) <=> ?x
  end
end
"#,
        ),
        &["enforced only where the resolver fires a directional rewrite"],
    );
}

/// A `<=>` goal BINDS (proposal 049), which is what lets the generated guard delay and
/// then be re-asked. `eq` would not: it is a semantic equality TEST that never binds,
/// so `rule f(?x: String) :- eq(?x, "abe")` residualizes with OR WITHOUT the
/// annotation — MEASURED, and the reason this fixture is spelled with `<=>`.
const DELAY_SRC: &str = r#"
namespace test.wi742.delay
  import anthill.prelude.{Int64, String}

  rule named(?x: String) :- ?x <=> "abe"
  rule named_bad(?x: String) :- ?x <=> 5
  rule named_untyped(?x) :- ?x <=> "abe"
end
"#;

#[test]
fn delays_then_holds_when_a_later_goal_binds() {
    let mut kb = crate::common::load_kb_with(DELAY_SRC);
    // `?x` is UNBOUND when `domain` is asked. The goal suspends, rotation lets `<=>`
    // bind it, and the re-asked goal HOLDS — one definite row, not a residual.
    assert_eq!(definite_answers(&mut kb, "test.wi742.delay.named(?x)"), 1);
    assert_eq!(
        definite_answers(&mut kb, "test.wi742.delay.named_untyped(?x)"),
        1
    );
}

#[test]
fn refutes_after_a_later_goal_binds() {
    let mut kb = crate::common::load_kb_with(DELAY_SRC);
    // Same shape, non-conforming binding: the re-asked guard REFUTES.
    assert_eq!(answers(&mut kb, "test.wi742.delay.named_bad(?x)"), 0);
}

#[test]
fn an_undischarged_guard_residualizes() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.undischarged
  import anthill.prelude.{Int64, String}
  fact anchor(1)
  rule loose(?x: String, ?y) :- anchor(?y)
  rule loose_untyped(?x, ?y) :- anchor(?y)
end
"#,
    );
    // NOTHING binds `?x`. The guard must stay undischarged — an answer, but a
    // CONDITIONAL one — never a definite row presenting an unchecked binding.
    assert_eq!(answers(&mut kb, "test.wi742.undischarged.loose(?x, ?y)"), 1);
    assert_eq!(
        definite_answers(&mut kb, "test.wi742.undischarged.loose(?x, ?y)"),
        0
    );
    // CONTROL: the untyped twin has nothing to discharge, so its row is definite.
    assert_eq!(
        definite_answers(&mut kb, "test.wi742.undischarged.loose_untyped(?x, ?y)"),
        1
    );
}

#[test]
fn a_bodyless_typed_head_still_guards() {
    // `:- true` folds to an EMPTY body (§6.1), and the clause is still a clause —
    // MEASURED: it answers where a bare declaration (`rule p(?x)`) does not. So the
    // generated guard becomes the whole body, and `prepend_generated_body_goals`
    // maintains the WI-812 bodied-rule gate across that flip.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.bodyless
  import anthill.prelude.{Int64}
  sort Colour
    entity red
  end
  sort Thing
    entity thing(n: Int64)
  end
  fact src(red())
  fact src(thing(n: 1))

  rule ok(?x: Colour) :- true
  rule ok_untyped(?x) :- true

  rule typed_hits(?v) :- src(?v), ok(?v)
  rule untyped_hits(?v) :- src(?v), ok_untyped(?v)
end
"#,
    );
    // MODE (in): the caller binds first, so the guard decides on a value it can read.
    assert_eq!(answers(&mut kb, "test.wi742.bodyless.typed_hits(?v)"), 1);
    assert_eq!(answers(&mut kb, "test.wi742.bodyless.untyped_hits(?v)"), 2);
}

#[test]
fn an_undischarged_guard_raises_when_the_relation_is_drained() {
    // The other half of the row above, at the other face. The RESOLVER keeps the
    // guard as a residual; the typed `Relation` face has no room for a third outcome,
    // so DRAINING one raises `Error[RelationFloundered]` (WI-737's existing route,
    // reached because the generated goal is ORDINARY). "Flounders loudly, never a
    // silent non-check" is this row, not the residual count above.
    const DRAIN_SRC: &str = r#"
namespace test.wi742.drain
  import anthill.prelude.{Int64, String, List}
  fact anchor(1)
  rule loose(?x: String, ?y) :- anchor(?y)
  rule settled(?x: String, ?y) :- anchor(?y), ?x <=> "abe"

  operation drainLoose() -> List[(x: String, y: Int64)] effects Error =
    let r = loose
    r.takeN(5)

  operation drainSettled() -> List[(x: String, y: Int64)] effects Error =
    let r = settled
    r.takeN(5)
end
"#;
    let mut interp = crate::common::interp_for(DRAIN_SRC);
    let err = interp
        .call("test.wi742.drain.drainLoose", &[])
        .expect_err("a never-discharged typed guard must RAISE, not materialize a row");
    assert!(
        matches!(err, anthill_core::eval::EvalError::Raised { .. }),
        "the raise goes on the Error channel (WI-737), got {err:?}"
    );
    // CONTROL, and it is what says the raise is about the UNDISCHARGED guard and not
    // about typed heads: the same clause with a binder discharges and drains.
    // A FRESH INTERPRETER — a raised call leaves the frame stack mid-unwind, and
    // reusing it reports `deliver: parent frame had no awaiting state` for the next
    // call whatever that call does (measured).
    let mut fresh = crate::common::interp_for(DRAIN_SRC);
    fresh
        .call("test.wi742.drain.drainSettled", &[])
        .expect("a discharged guard drains normally");
}

#[test]
fn a_nonexistent_sort_in_the_annotation_stays_loud() {
    // Unchanged by this work and asserted so it stays that way: lifting the WI-582
    // refusal must not turn an unresolved bound into a silently-never-firing clause.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace test.wi742.nosort
  import anthill.prelude.{Int64}
  fact item(1)
  rule f(?x: NoSuchSortAnywhere) :- item(?x)
end
"#,
        ),
        &["unresolved name 'NoSuchSortAnywhere'"],
    );
}

// ── 052's column type (proposal 060 §2's "column type, true by construction") ──

/// The column-type claim is only measurable in the NEGATIVE direction: an
/// UNCONSTRAINED column is a fresh type variable, which unifies with whatever the
/// consumer declares. So a clean load of the matching declaration is NOT evidence —
/// the four-cell matrix below is, and its two `_accepts_` rows exist to say so.
fn column_src(annotation: &str, declared: &str) -> String {
    format!(
        r#"
namespace test.wi742.col
  import anthill.prelude.{{Int64, List}}
  sort Colour
    entity red
    entity green
  end
  fact item(red())
  fact item(green())

  rule colours({annotation}) :- item(?x)

  operation all() -> List[(x: {declared})] effects Error =
    let r = colours
    r.takeN(5)
end
"#
    )
}

#[test]
fn a_typed_column_types_as_its_bound() {
    crate::common::load_kb_with(&column_src("?x: Colour", "Colour"));
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&column_src("?x: Colour", "Int64")),
        &["expected List[T = (x: Int64)], got List[T = (x: Colour)]"],
    );
}

#[test]
fn an_untyped_column_accepts_either_declaration() {
    // THE CONTROL for the row above, and the reason its second half is the evidence:
    // with no annotation the column is a fresh variable, so BOTH declarations load.
    crate::common::load_kb_with(&column_src("?x", "Colour"));
    crate::common::load_kb_with(&column_src("?x", "Int64"));
}

// ── proposal 060 §2.1 — the sigil-free parameter form ─────────────────────────

const PARAM_SRC: &str = r#"
namespace test.wi742.param
  import anthill.prelude.{Int64, String, List}
  import anthill.prelude.PartialOrd.{gte}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 12)

  rule adult(name: String, age: Int64) :- person(name: name, age: age), gte(age, 18)
end
"#;

#[test]
fn parameter_form_introduces_typed_clause_variables() {
    let mut kb = crate::common::load_kb_with(PARAM_SRC);
    // The head parameters are read BARE in the body and bind like `?name` / `?age`;
    // `bob` is filtered by the ordinary guard, so the rule really RAN.
    assert_eq!(answers(&mut kb, "test.wi742.param.adult(?n, ?a)"), 1);
}

fn param_column_src(declared: &str) -> String {
    PARAM_SRC.trim_end().trim_end_matches("end").to_owned()
        + &format!(
            r#"
  operation rows() -> List[{declared}] effects Error =
    let r = adult
    r.takeN(5)
end
"#
        )
}

#[test]
fn parameter_form_names_and_types_the_columns() {
    crate::common::load_kb_with(&param_column_src("(name: String, age: Int64)"));
    // The TYPE comes from the parameter list…
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&param_column_src("(name: String, age: String)")),
        &["expected List[T = (name: String, age: String)]"],
    );
    // …and so does the NAME.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&param_column_src("(nm: String, age: Int64)")),
        &["expected List[T = (nm: String, age: Int64)]"],
    );
}

#[test]
fn a_head_carrying_a_type_var_introducer_is_left_to_the_ordinary_path() {
    // A `ParseAux` child — the rule-level `[A]` introducer rides as one — is a
    // parse-only payload the generic head conversion reads at its own build site and
    // filters out of the argument walk. The reclassifier has neither the read nor the
    // filter, so it DECLINES such a head rather than filtering (which would silently
    // drop the bracket the author wrote).
    //
    // MEASURED BEFORE THE DECLINE: `rule g[A](a: List[T = A], …)` PANICKED on
    // `convert_term`'s `unreachable!` — a panic, not a refusal. Now both spellings give
    // the SAME loud error, which is the point: combining the `[T]` introducer with a
    // parameterized bound is unsupported in the SIGIL spelling too (the control below),
    // so it is not §2.1's question — it is WI-20260908-PW9A0, which owns both lifting
    // this decline and the misdirecting `unresolved name` reported meanwhile.
    const PROG: &str = r#"
namespace test.wi742.introducer
  import anthill.prelude.{Int64, List}
  sort Summable
    sort T = ?
  end
  fact Summable[T = Int64]
  fact src([1, 2], 7)
  rule g[A](@a: List[T = A], @b: Int64) :- src(@a, @b), Summable[A]
end
"#;
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&PROG.replace('@', "")),
        &["unresolved name 'A'"],
    );
    // THE CONTROL, and it is what makes the row above a decline rather than a
    // regression: the SIGIL spelling of the identical program answers the same way.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&PROG.replace('@', "?")),
        &["unresolved name 'A'"],
    );
}

#[test]
fn parameter_form_leaves_entity_constructor_heads_alone() {
    // THE DISCRIMINATOR IS THE RESOLVED CATEGORY, NEVER THE CASE: `palette` is
    // lowercase and an entity constructor, so its named argument stays a named
    // argument. This is the row the whole shipped corpus consists of.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.entity
  sort Colour
    entity red
    entity green
  end
  sort Palette
    entity palette(c: Colour)
  end
  fact palette(c: red())
  fact palette(c: green())
  rule any_colour(?c) :- palette(c: ?c)
end
"#,
    );
    assert_eq!(answers(&mut kb, "test.wi742.entity.any_colour(?c)"), 2);
}

#[test]
fn parameter_form_leaves_a_variable_valued_named_arg_alone() {
    // The SECOND half of the discriminator: `from: ?a` is not `name: Type` at all, so
    // it stays a named argument. Reclassifying it would silently replace a written
    // argument with a variable named after its own label.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.namedarg
  import anthill.prelude.{Int64}
  sort Flow
    entity flow(from: Int64, to: Int64)
  end
  fact flow(from: 1, to: 2)
  rule reaches(from: ?a, to: ?b) :- flow(from: ?a, to: ?b)
end
"#,
    );
    assert_eq!(
        answers(&mut kb, "test.wi742.namedarg.reaches(from: ?a, to: ?b)"),
        1
    );
}

#[test]
fn parameter_names_do_not_leak_past_their_rule() {
    // The parameter map SHADOWS resolved symbols — that is what makes a parameter a
    // parameter — so a name left in it turns a LATER item's identically-spelled datum
    // into this rule's variable. MEASURED before `load_rule`'s clear wrapper: `fact
    // seen(name)` below asserted a FREE VARIABLE and `later("zzz")` answered 1.
    // Found by `/code-review`.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.leak
  import anthill.prelude.{Int64, String}
  import anthill.prelude.PartialOrd.{gte}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule adult(name: String, age: Int64) :- person(name: name, age: age), gte(age, 18)
  fact seen("bob")
  rule later(?z) :- seen(?z)
end
"#,
    );
    assert_eq!(answers(&mut kb, "test.wi742.leak.later(\"zzz\")"), 0);
    // CONTROL: the fact itself still answers for what it holds, and the rule that
    // introduced the parameter still works — so the clear is scoped, not a deletion.
    assert_eq!(answers(&mut kb, "test.wi742.leak.later(\"bob\")"), 1);
    assert_eq!(answers(&mut kb, "test.wi742.leak.adult(?n, ?a)"), 1);
}

#[test]
fn a_parameter_type_may_be_written_qualified_or_applied() {
    // Three spellings of ONE `name: Type`. The dotted and applied ones were NOT
    // reclassified at first: no clause variable was introduced, the body's bare name
    // rode as an `Ident` that unifies with nothing, and the clause LOADED CLEAN and
    // answered NOTHING — the silent dead clause this feature's refusal exists to
    // prevent, reached through the spellings that refusal cannot see. Found by
    // `/code-review`. The applied row is also what keeps the two spellings one form:
    // the SIGIL `?l: List[T = Int64]` always accepted a parameterized bound.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.spell
  import anthill.prelude.{Int64, List}
  sort Colour
    entity red
    entity green
  end
  fact item(red())
  fact item(green())
  fact xs([1, 2])

  rule pick_bare(c: Colour) :- item(c)
  rule pick_dotted(c: test.wi742.spell.Colour) :- item(c)
  rule pick_applied(l: List[T = Int64]) :- xs(l)
  rule pick_sigil(?l: List[T = Int64]) :- xs(?l)
end
"#,
    );
    assert_eq!(answers(&mut kb, "test.wi742.spell.pick_bare(?c)"), 2);
    assert_eq!(answers(&mut kb, "test.wi742.spell.pick_dotted(?c)"), 2);
    assert_eq!(answers(&mut kb, "test.wi742.spell.pick_applied(?l)"), 1);
    // The sigil twin, which worked all along — the yardstick the other three must meet.
    assert_eq!(answers(&mut kb, "test.wi742.spell.pick_sigil(?l)"), 1);
}

#[test]
fn an_unresolved_bare_head_name_stays_a_symbolic_constant() {
    // WI-742's acceptance says an untyped bare head name "remains a loud unresolved-name
    // error". IT NEVER WAS ONE, and the premise is wrong rather than the code: such a
    // name is a SYMBOLIC CONSTANT, and both spellings of it intern to one unresolved
    // `Ident` and UNIFY. This row is what a refusal would have to break, so it is the
    // reason there is none.
    //
    // The refusal WAS built and measured breaking it: three `parse_test` rows fell on
    // `fact WorkItem(…, status: Open)`, where `Open` is a `WorkStatus` variant the
    // standalone fixture never declares and the matching query spells identically.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.symconst
  fact q(alpha, beta)
  rule p(alpha, ?y) :- q(alpha, ?y)
end
"#,
    );
    // The constant matches ITSELF — which is what makes the clause live, not dead.
    assert_eq!(answers(&mut kb, "test.wi742.symconst.p(?a, ?b)"), 1);
    // …and it is a constant, not a variable: it does not match something else.
    assert_eq!(answers(&mut kb, "test.wi742.symconst.p(?a, gamma)"), 0);
}

// ── C666A — the guarded non-enclosing join (the ticket's acceptance addition) ──

#[test]
fn a_typed_head_may_join_the_predicate_its_carrier_exposes() {
    // Two independent implementors extend one declared predicate through their own
    // `requires` edge. C666A refuses that UNGUARDED; the generated `domain(?x, A)`
    // guard is what makes it safe, and each clause then answers only for its own
    // carrier — which is the acceptance, driven rather than asserted at load.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.c666a
  import anthill.prelude.{Int64, String}

  sort Spec
    rule p(?x, ?tag)
  end

  sort A
    requires test.wi742.c666a.Spec
    entity a(n: Int64)
    rule p(?x: A, "from A") :- true
  end

  sort B
    requires test.wi742.c666a.Spec
    entity b(n: Int64)
    rule p(?x: B, "from B") :- true
  end

  fact seed(a(n: 1))
  fact seed(b(n: 2))
  rule which(?v, ?tag) :- seed(?v), test.wi742.c666a.Spec.p(?v, ?tag)

  -- The per-carrier selection is driven from INSIDE the program: a query pattern
  -- cannot spell an entity constructor, so a `which(a(n: 1), …)` pattern would
  -- measure the query converter rather than the clause selection.
  rule tag_of_a(?tag) :- test.wi742.c666a.Spec.p(a(n: 1), ?tag)
  rule tag_of_b(?tag) :- test.wi742.c666a.Spec.p(b(n: 2), ?tag)
end
"#,
    );
    // Both clauses landed on the ONE predicate, and each answered for its own row.
    assert_eq!(answers(&mut kb, "test.wi742.c666a.which(?v, ?tag)"), 2);
    // An A-carried input fires ONLY the A clause, and a B-carried input only the B
    // clause — exactly one tag each, which is the dispatch the guard performs.
    assert_eq!(answers(&mut kb, "test.wi742.c666a.tag_of_a(?t)"), 1);
    assert_eq!(answers(&mut kb, "test.wi742.c666a.tag_of_b(?t)"), 1);
    assert_eq!(answers(&mut kb, "test.wi742.c666a.tag_of_a(\"from A\")"), 1);
    assert_eq!(answers(&mut kb, "test.wi742.c666a.tag_of_a(\"from B\")"), 0);
    assert_eq!(answers(&mut kb, "test.wi742.c666a.tag_of_b(\"from B\")"), 1);
    assert_eq!(answers(&mut kb, "test.wi742.c666a.tag_of_b(\"from A\")"), 0);
}

#[test]
fn the_parameter_spelling_earns_the_same_c666a_admission() {
    // ONE INTERNAL FORM, ONE VERDICT. The admission reads the head's annotations at the
    // SCAN, before any bound is installed, and §2.1's parameter form carries no
    // `typed_var` marker — so reading only the marker made the two spellings diverge
    // here: `rule p(?x: A)` loaded and `rule p(x: A)` was refused, in otherwise
    // identical programs. Found by `/code-review`.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi742.c666a_param
  import anthill.prelude.{Int64}
  sort Spec
    rule p(?x)
  end
  sort A
    requires test.wi742.c666a_param.Spec
    entity a(n: Int64)
    rule p(x: A) :- true
  end
  fact seed(a(n: 1))
  rule hits(?v) :- seed(?v), test.wi742.c666a_param.Spec.p(?v)
end
"#,
    );
    assert_eq!(answers(&mut kb, "test.wi742.c666a_param.hits(?v)"), 1);
}

#[test]
fn an_unguarded_join_is_still_refused() {
    // CONTROL 1 — the identical program with the annotations removed. This row passes
    // either way BY DESIGN: it is what shows the admission is about the GUARD.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace test.wi742.c666a_un
  import anthill.prelude.{Int64}
  sort Spec
    rule p(?x)
  end
  sort A
    requires test.wi742.c666a_un.Spec
    entity a(n: Int64)
    rule p(?x) :- true
  end
end
"#,
        ),
        &["the unguarded rule head `p` in 'test.wi742.c666a_un.A'"],
    );
}

#[test]
fn a_guard_naming_another_sort_is_not_an_admission() {
    // CONTROL 2 — the head IS typed, but on a sort that says nothing about `A`. The
    // admission is a PREDICATE ("selects the contributing carrier"), not "has an
    // annotation"; without this row, `?x: Int64` would buy the join.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace test.wi742.c666a_wrong
  import anthill.prelude.{Int64}
  sort Spec
    rule p(?x)
  end
  sort A
    requires test.wi742.c666a_wrong.Spec
    entity a(n: Int64)
    rule p(?x: Int64) :- true
  end
end
"#,
        ),
        &["the unguarded rule head `p` in 'test.wi742.c666a_wrong.A'"],
    );
}

#[test]
fn a_wildcard_import_join_stays_refused_even_when_typed() {
    // CONTROL 3 — a NAMESPACE is not a carrier, so there is nothing for a guard to
    // select and the implicit whole-scope extension C666A exists to stop is exactly
    // what would be admitted. This is the row that keeps the admission from being
    // "any typed head anywhere".
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace test.wi742.wild.lib
  rule p(?x)
  rule p(0) :- true
end
namespace test.wi742.wild.user
  import test.wi742.wild.lib.*
  import anthill.prelude.{Int64}
  rule p(?x: Int64) :- true
end
"#,
        ),
        &["the unguarded rule head `p` in 'test.wi742.wild.user'"],
    );
}
