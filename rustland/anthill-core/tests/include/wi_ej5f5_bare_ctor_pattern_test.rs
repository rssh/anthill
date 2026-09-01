//! WI-20260827-EJ5F5 — A BARE NULLARY-CONSTRUCTOR NAME IN A `case` PATTERN NOW MATCHES
//! THE CONSTRUCTOR. It used to bind as a variable, so the arm matched EVERYTHING, every
//! later arm was dead, and the operation returned a WRONG value with no diagnostic.
//!
//! ```text
//!   operation pick(c: C) -> Int64 =        operation pickp(c: C) -> Int64 =
//!     match c                                match c
//!       case red -> 1                          case red() -> 1
//!       case green -> 2                        case green() -> 2
//!
//!   C.pick(green())  answered 1  WRONG     C.pickp(green())  answers 2
//! ```
//!
//! THE MECHANISM WAS A HALF-APPLIED SPEC RULE, not a missing one. kernel-language.md
//! §8.6 already said a `case` name resolves type-directedly against the scrutinee's own
//! constructors, and the typer already implemented that resolution
//! (`pattern_var_ctor_sym`) — but only two readers ever asked: the EXHAUSTIVENESS check
//! and the arm's Γ fact. Everything that RUNS reads the stored `Pattern`, where the
//! loader had left a fresh binder symbol: `eval::pattern` bound it, `folded_call_match`
//! bound it, and cpp-gen (the third reader, and the one that disagreed in the OTHER
//! direction) emitted a nullary tag check for it. The fix rewrites the resolved ones in
//! `bind_and_label_pattern`, which is inside the typer's tree-producing path, so the
//! rewritten arm reaches the stored body through `MatchFinal` + `set_op_body_node` and
//! every reader sees ONE answer.
//!
//! WHY THE TYPER AND NOT THE LOADER: which constructors are in view is a property of the
//! scrutinee's TYPE. The grammar cannot tell the two apart at all — `pattern_var` is a
//! bare identifier and `pattern_constructor` requires the parens — and no load pass holds
//! a type. This is what the spec paragraph means by "this resolution happens during
//! type-checking, not at load".
//!
//! THE AXES AND THEIR BACK-OUTS — every one was RUN, and the table is the measurement,
//! not a prediction:
//!
//! ```text
//!   back out …                                        red tests
//!   the rewrite (`role == MatchArm` ⇒ false)          headline, nested, relational
//!   DEPTH (sub-patterns recursed as `Binder`)         nested ONLY
//!   the ARITY gate (`takes_no_fields`)                arity ONLY
//!   the `: T` opt-out (`var_pattern_ctor`)            annotated/let AND exhaustiveness
//!   body/guard re-pointing (`repoint_arm_binders`)    ALL but one — SRC stops LOADING
//!   the ROLE gate (`let` site ⇒ `MatchArm`)           ALL — SRC stops LOADING
//!   ─ and one that NOTHING here separates ───────────────────────────────────────────
//!   feeding Γ the WRITTEN patterns again              nothing; see
//!                                                     `the_stored_arm_pattern_is_ground_at_depth`
//! ```
//!
//! Two of those take the whole file down rather than inverting a row, and that is what
//! they measure: the fixture stops LOADING, because removing a binding nothing else
//! supplies orphans every reference to it.
//!
//! * DEPTH — a nested `case some(red)` asks the FIELD's type, not the scrutinee's, so the
//!   rewrite recurses with the type actually threaded to each position.
//! * ARITY — `case suc` names a constructor that takes a field, so it is NOT a value and
//!   must stay a binder; rewriting it would build a 0-argument constructor pattern, which
//!   `match_constructor_pattern` refuses arity-strictly, turning a working catch-all into
//!   a DEAD arm. The gate is PERMISSIVE about a name the KB declares nothing for
//!   (`takes_no_fields`) and the REWRITE alone adds the declaration
//!   (`declares_a_nullary_entity`) — a split the suite forced, not a preference: spelling
//!   the shared one strictly fails `wi537_local_interpretation_test::
//!   match_nullary_ctor_arms_accumulate_negations`, whose hand-built KB interns its
//!   constructor names instead of declaring them.
//! * ROLE — a `let` / `lambda` binder is irrefutable and never rewritten. Backing this
//!   one out does not invert a value, it removes a binding nothing else supplies: the
//!   load reports `42:17: type mismatch in red.name: expected resolved name, got
//!   unresolved`.
//! * RE-POINTING — the rewrite removes the arm's binder, but the LOADER already pointed
//!   the arm's body and guard at it (`local_names_stack`, built before any type exists),
//!   so those references must follow the rewrite to the constructor. Without it
//!   `case red -> red` stops loading with the same message — while `case red() -> red`
//!   keeps working, which would put a difference back between two spellings this ticket
//!   exists to make identical.
//!
//! WHAT PASSES EITHER WAY, AND WHY IT IS HERE: every `*_paren_*` row. They never reach
//! the rewrite (the parenthesized spelling already loads as `Pattern::Constructor`), and
//! they are asserted beside each bare row to show the bare row's expected value is the
//! one the language already had — not a new one invented by this test.
//!
//! THE CORPUS'S OWN TWO BARE-NAME ARMS are `case other -> mirror_refusal(…)` in
//! `rustland/anthill-todo/anthill/main.anthill`, where `other` names no `MirrorTarget`
//! constructor. They stay binders, and they are driven — not merely loaded — by
//! `wi1117_mirror_export_import_test::export_without_a_mirror_fact_is_refused`, which
//! runs `export` on a project with no `fact Mirror` (so `mirror_target` answers the
//! nullary `mirror_absent`) and asserts the refusal text. `a_binder_arm_still_catches_
//! every_constructor` below is the in-crate twin of that row.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// `(total, definite)` — a SUSPENSION is `(1, 0)` and a decided answer is `(1, 1)`, and
/// the WI-580 row below turns on telling them apart.
fn counts(kb: &mut KnowledgeBase, rule: &str) -> (usize, usize) {
    let goal = crate::common::query_pattern_term(kb, rule);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let def = sols.iter().filter(|s| s.is_definite()).count();
    (sols.len(), def)
}

/// `C` is the ticket's own sort, with a THIRD variant so an arm behind the catch-all can
/// be shown reached. `Nat` exists for the ARITY axis: `suc` takes a field, so a bare
/// `case suc` names a constructor that is not, by itself, a value.
///
/// `other` names no constructor of anything, which is the corpus's own shape.
const SRC: &str = r#"
namespace ej5f5
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{some, none}
  sort C
    entity red
    entity green
    entity blue
  end
  sort Nat
    entity zed
    entity suc(prev: Nat)
  end
  sort Ops
    -- THE HEADLINE PAIR
    operation pick(c: C) -> Int64 =
      match c
        case red -> 1
        case green -> 2
        case blue -> 3
    operation pickp(c: C) -> Int64 =
      match c
        case red() -> 1
        case green() -> 2
        case blue() -> 3
    -- DEPTH: the bare name sits in CONSTRUCTOR-ARGUMENT position, where the candidate
    -- set is the FIELD's constructors, not the scrutinee's.
    operation nest(o: Option[T = C]) -> Int64 =
      match o
        case some(red) -> 1
        case some(green) -> 2
        case none() -> 3
    operation nestp(o: Option[T = C]) -> Int64 =
      match o
        case some(red()) -> 1
        case some(green()) -> 2
        case none() -> 3
    -- ROLE: a `let` binder is irrefutable. `red` here binds the VALUE, so the body's
    -- `red` is that value and not the constructor.
    operation letbind(c: C) -> Int64 =
      let red = c
      Ops.pickp(red)
    -- ARITY: `suc` takes a field, so a bare `case suc` is a BINDER (a catch-all), and
    -- the `zed` arm after it is dead. Rewriting it would make a 0-arg constructor
    -- pattern that matches NEITHER `suc(...)` nor `zed`.
    operation arity(n: Nat) -> Int64 =
      match n
        case suc -> 1
        case zed() -> 2
    -- A GENUINE BINDER catch-all — the corpus's `case other` shape.
    operation binder(c: C) -> Int64 =
      match c
        case red() -> 1
        case other -> 9
    -- The rewrite REMOVES a binding, so an arm body that names the bare name must still
    -- resolve — through the ordinary scope ladder, to the entity. See
    -- `an_arm_body_naming_the_bare_name_still_resolves`.
    operation echo(c: C) -> C =
      match c
        case red -> red
        case green -> green
        case blue -> blue
    -- THE OPT-OUT: a written annotation says "binder", so this is a catch-all.
    operation annot(c: C) -> Int64 =
      match c
        case (red: C) -> 7
        case green() -> 2
    -- The Γ / coverage rows. `gamma` is DELIBERATELY total by its two `some` arms plus
    -- `none()`, so the arm-2 negation below is the only thing that separates the readings.
    operation gamma(o: Option[T = C]) -> Int64 =
      match o
        case some(red) -> 1
        case some(green) -> 2
        case none() -> 3
  end
  rule bare_red()     :- Ops.pick(red())    = 1
  rule bare_green1()  :- Ops.pick(green())  = 1
  rule bare_green2()  :- Ops.pick(green())  = 2
  rule bare_blue3()   :- Ops.pick(blue())   = 3
  rule paren_green2() :- Ops.pickp(green()) = 2
  rule paren_green1() :- Ops.pickp(green()) = 1

  rule nest_green1()  :- Ops.nest(some(green()))  = 1
  rule nest_green2()  :- Ops.nest(some(green()))  = 2
  rule nest_none3()   :- Ops.nest(none())         = 3
  rule nestp_green2() :- Ops.nestp(some(green())) = 2

  rule let_green2()   :- Ops.letbind(green()) = 2
  rule let_green1()   :- Ops.letbind(green()) = 1

  rule arity_suc1()   :- Ops.arity(suc(prev: zed())) = 1
  rule arity_zed1()   :- Ops.arity(zed())            = 1
  rule arity_zed2()   :- Ops.arity(zed())            = 2

  rule binder_red1()  :- Ops.binder(red())   = 1
  rule binder_grn9()  :- Ops.binder(green()) = 9

  rule echo_green()   :- Ops.echo(green()) = green()
  rule echo_notred()  :- Ops.echo(green()) = red()

  rule annot_red7()   :- Ops.annot(red())   = 7
  rule annot_grn7()   :- Ops.annot(green()) = 7
  rule annot_grn2()   :- Ops.annot(green()) = 2

  -- WI-580: the relational direction. A bare-name arm makes every arm's
  -- `unify(scrutinee, patternᵢ)` a FRESH VAR, so no arm narrows anything and the
  -- case split decides nothing.
  rule bare_gen(?c)   :- Ops.pick(?c)  = 2
  rule paren_gen(?c)  :- Ops.pickp(?c) = 2
end
"#;

/// The names of a unary predicate's DEFINITE answers — so the WI-580 row can name the
/// value it decides on, not only count it.
fn definite_names(kb: &mut KnowledgeBase, qn: &str) -> Vec<String> {
    crate::common::query_unary(kb, qn)
        .into_iter()
        .filter(|(_, d)| *d)
        .map(|(v, _)| match kb.value_head_symbol(&v) {
            Some(s) => kb.local_name_of(s).to_string(),
            None => format!("{v:?}"),
        })
        .collect()
}

/// THE HEADLINE. `case red` is the constructor `C.red`, so `pick(green())` is 2.
///
/// BACK OUT the `PatternRole::MatchArm` rewrite and every `bare_*` assertion here
/// inverts: `bare_green1` becomes (1, 1) and `bare_green2` (0, 0). The two `paren_*`
/// rows pass either way, by design — they are what the answer is being compared TO.
#[test]
fn a_bare_nullary_constructor_name_matches_the_constructor() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "ej5f5.paren_green2()"),
        (1, 1),
        "CONTROL, unmoved by this change: the parenthesized spelling always matched"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.paren_green1()"),
        (0, 0),
        "CONTROL: and it never matched the FIRST arm"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.bare_green2()"),
        (1, 1),
        "the bare spelling now answers what the parenthesized one answers. (0, 0) with \
         the rewrite backed out — the `red` arm was a catch-all"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.bare_green1()"),
        (0, 0),
        "and it no longer answers the FIRST arm's value. (1, 1) with the rewrite backed \
         out, which is the wrong answer the ticket measured"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.bare_red()"),
        (1, 1),
        "the arm that WAS being matched by accident still matches on purpose"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.bare_blue3()"),
        (1, 1),
        "the THIRD arm — dead behind a catch-all before this change, so it is the row \
         that shows the whole ladder is reached, not only the second arm"
    );
}

/// DEPTH. The candidate set is the type threaded to THIS position: inside `some(_)` it is
/// the field's constructors. Nothing about the outer scrutinee (an `Option`) names `red`.
///
/// BACK OUT the rewrite and `nest_green1` is (1, 1) / `nest_green2` (0, 0). Restrict the
/// rewrite to the arm's OUTERMOST pattern (the smaller fix the ticket's headline asks
/// for) and these two rows alone go red while every row above stays green.
#[test]
fn the_resolution_reaches_a_nested_position() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "ej5f5.nestp_green2()"),
        (1, 1),
        "CONTROL: the parenthesized nested spelling"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.nest_green2()"),
        (1, 1),
        "the bare twin"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.nest_green1()"),
        (0, 0),
        "and `some(red)` is no longer a catch-all over every `some`"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.nest_none3()"),
        (1, 1),
        "the arm past the two `some` arms is reached"
    );
}

/// ARITY. `suc` takes a field, so the bare name is not a value and stays a BINDER — which
/// makes the arm a catch-all and the `zed()` arm after it dead.
///
/// THIS IS THE GATE'S OWN ROW. Remove `is_nullary_constructor` from
/// `pattern_var_ctor_sym` and `case suc` is rewritten to a 0-argument constructor
/// pattern; `match_constructor_pattern` is arity-strict, so it matches neither `suc(…)`
/// (1 field, 0 sub-patterns) nor `zed`, and BOTH `arity_suc1` and `arity_zed1` go to
/// (0, 0) — a catch-all turned into a dead arm.
#[test]
fn a_bare_name_naming_a_constructor_with_fields_is_still_a_binder() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "ej5f5.arity_suc1()"),
        (1, 1),
        "the catch-all catches `suc`. (0, 0) without the arity gate"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.arity_zed1()"),
        (1, 1),
        "and it catches `zed` too — the `zed()` arm behind it is DEAD, which is what a \
         catch-all means. (0, 0) without the arity gate"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.arity_zed2()"),
        (0, 0),
        "the dead arm stays dead — asserted so the row above cannot be read as `zed` \
         reaching its own arm"
    );
}

/// A NAME THAT NAMES NO CONSTRUCTOR OF THE SCRUTINEE is a binder, and the corpus's two
/// `case other ->` arms are exactly this shape. Unmoved by the change; here because the
/// ticket's acceptance asks for it ASSERTED rather than assumed.
#[test]
fn a_binder_arm_still_catches_every_constructor() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "ej5f5.binder_red1()"),
        (1, 1),
        "its own arm"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.binder_grn9()"),
        (1, 1),
        "everything else falls to the binder"
    );
}

/// THE OPT-OUT and the ROLE gate — the two ways a name that DOES name a constructor still
/// binds.
///
/// `case (red: C)` carries a written annotation, which is only ever written on a binder,
/// so it is the repair for a binder whose name collides with a constructor. A `let red =`
/// is irrefutable, so it binds whatever the scope calls its constructors.
///
/// BACK OUT the `type_ann.is_none()` guard and this test alone goes red: `annot_grn7`
/// becomes (0, 0) and `annot_grn2` (1, 1). BACK OUT the `PatternRole::Binder` at the
/// `let` call site and the fixture stops LOADING — measured, `42:17: type mismatch in
/// red.name: expected resolved name, got unresolved`, because `let red = c` rewrites to a
/// constructor pattern, binds nothing, and the body's `Ops.pickp(red)` then names a
/// binder that no longer exists. Every test in this file fails on that one, which is why
/// the row that PINS the role gate is a load, not a value.
#[test]
fn an_annotated_binder_and_a_let_binder_are_never_rewritten() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "ej5f5.annot_red7()"),
        (1, 1),
        "the annotated arm takes its own constructor"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.annot_grn7()"),
        (1, 1),
        "AND everything else — it is a catch-all, so the `green()` arm behind it is dead"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.annot_grn2()"),
        (0, 0),
        "the dead arm stays dead"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.let_green2()"),
        (1, 1),
        "`let red = c` binds the VALUE, so `pickp(red)` is `pickp(green())`"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.let_green1()"),
        (0, 0),
        "not the constructor `red`"
    );
}

/// THE REWRITE REMOVES A BINDING, and the arm body has to survive that. `case red -> red`
/// used to bind `red` to the scrutinee and read the binder; now the arm binds nothing and
/// the body's `red` resolves through the ordinary scope ladder to the entity.
///
/// PASSES EITHER WAY, and that is the point rather than a weakness: a catch-all echoing
/// its binder and a constructor arm returning its own constructor agree on every input, so
/// no VALUE separates them. What this pins is that the program still LOADS — which is not
/// automatic, and is exactly what back-out D above breaks for a `let`: remove the binding
/// where nothing else supplies the name and the body reports `expected resolved name, got
/// unresolved`.
#[test]
fn an_arm_body_naming_the_bare_name_still_resolves() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        counts(&mut kb, "ej5f5.echo_green()"),
        (1, 1),
        "the arm returns its own constructor"
    );
    assert_eq!(
        counts(&mut kb, "ej5f5.echo_notred()"),
        (0, 0),
        "and not another one — asserted so the row above cannot be read as `echo`          answering anything at all"
    );
}

/// THE `: T` OPT-OUT IS ONE ANSWER FOR ALL THREE READERS, not just for the matcher.
///
/// `case (red: C) -> 7` is a catch-all (the row above drives that), so the `blue`
/// constructor is NOT covered and the match is non-exhaustive. While the annotation gate
/// sat at the rewrite alone, `collect_covered_entities` still resolved the annotated name
/// and recorded `red` as covered — so this diagnostic was SILENT, and the arm's Γ
/// carried the ground `eq(c, Ref(red))` for an arm that in fact runs for `green` and
/// `blue` too.
///
/// BACK OUT the `pattern.pattern_type_ann().is_some()` gate in `var_pattern_ctor` and
/// this test alone goes red: the diagnostic disappears. Found by `/code-review`.
#[test]
fn the_annotation_opt_out_reaches_the_exhaustiveness_check_too() {
    let missing = |source: &str| -> Vec<String> {
        // WI-20260901-Q68AK — STOPS BEFORE THE TYPER, because this test drives
        // `type_check_sorts` itself over a fixture the pipeline refuses on purpose.
        // The verdict is bound, not discarded (WI-966).
        let (mut kb, result) = crate::common::load_stdlib_kb_untyped(source);
        anthill_core::kb::typing::type_check_sorts(&mut kb, &result.defined_sorts)
            .iter()
            .map(|e| format!("{e}"))
            .filter(|s| s.contains("missing"))
            .collect()
    };
    let annotated = r#"
namespace ej5f5ann
  import anthill.prelude.{Int64}
  -- `enum`, not `sort`: the exhaustiveness check only runs for `SortKind::Enum`, so a
  -- plain `sort` would make BOTH rows silent and the pair would measure nothing.
  enum C
    entity red
    entity green
  end
  sort Ops
    operation pick(c: C) -> Int64 =
      match c
        case (red: C) -> 7
  end
end
"#;
    let bare = missing(&annotated.replace("case (red: C)", "case red"));
    assert!(
        bare.iter().any(|m| m.contains("green")),
        "CONTROL — the same file one annotation apart: bare, the name IS the constructor \
         `red`, so the match covers `red` alone and `green` is genuinely missing. This \
         row is what shows the check is LIVE in this shape, so the silence below is the \
         annotation being honoured and not the check being off: {bare:?}"
    );
    let annotated_reports = missing(annotated);
    assert!(
        annotated_reports.is_empty(),
        "and annotated, the arm binds — a CATCH-ALL, so the match is total and nothing \
         is missing. Back the `pattern_type_ann` gate out of `var_pattern_ctor` and this \
         reports `missing green` about a match that answers for every constructor: \
         {annotated_reports:?}"
    );
}

/// THE STORED ARM PATTERN IS GROUND AT DEPTH, and what that buys the Γ producer.
///
/// Every reader of an arm pattern has to read the one the rewrite produced, not the one
/// the author wrote. This asserts the first half directly — `case some(red)` is STORED as
/// `some(red())`, a constructor with no binder hole — and then shows what the second half
/// is worth by running the Γ producer over the stored arms: because arm 1 is ground, arm 2
/// carries the earlier-arm negation `neq(o, some(red))` beside its own `eq`. Reading the
/// WRITTEN pattern instead produced `some(var_ref(red))` — a `var_ref` at a binder the
/// rewrite had removed — which is not ground, so no negation was emitted at all.
///
/// WHAT THIS SEPARATES: back out the rewrite (or its DEPTH leg) and the stored pattern is
/// a `Pattern::Var`, so both halves fail.
///
/// WHAT IT DOES NOT SEPARATE, MEASURED, so the next reader does not take it for more than
/// it is: feeding `match_arm_gamma_facts` the WRITTEN patterns again — the pre-review
/// wiring, and the actual defect `/code-review` found — leaves every row in this FILE
/// green, this one included. The reason is that this test builds the producer call
/// itself; the typer's own call is made inside one `build_type` frame and the resulting
/// `FlowEnv` is consumed there, so no test can read it. The reachable consumer is
/// `guarded_atom_refuted` — a guarded effect atom whose guard Γ refutes is DROPPED from
/// the operation's row — and a fixture that puts an arm negation in front of one would
/// pin the wiring. Nothing covers it today.
#[test]
fn the_stored_arm_pattern_is_ground_at_depth() {
    use anthill_core::eval::value::Value;
    use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence, Pattern};
    use std::rc::Rc;
    let mut kb = crate::common::load_kb_with(SRC);
    let op = kb
        .try_resolve_symbol("ej5f5.Ops.gamma")
        .expect("Ops.gamma is declared");
    let body = kb.op_body_node(op).expect("a typed body").clone();
    let (scrutinee, branches) = match body.as_expr() {
        Some(Expr::Match {
            scrutinee,
            branches,
        }) => (Rc::clone(scrutinee), branches.clone()),
        other => panic!("expected a match body, got {other:?}"),
    };
    // Arm 1 is `case some(red)`: a `some` constructor whose ONE sub-pattern must itself
    // be a constructor, not a binder. This is the DEPTH claim, read off the stored tree.
    let sub = match branches[0].pattern.as_pattern() {
        Some(Pattern::Constructor { pos_args, .. }) if pos_args.len() == 1 => {
            Rc::clone(&pos_args[0])
        }
        other => panic!("arm 1 should be stored as a 1-argument constructor, got {other:?}"),
    };
    assert!(
        matches!(sub.as_pattern(), Some(Pattern::Constructor { pos_args, named_args, .. })
                 if pos_args.is_empty() && named_args.is_empty()),
        "the NESTED `red` is stored as a nullary constructor, not a binder: {:?}",
        sub.as_pattern()
    );

    let arms: Vec<(Rc<NodeOccurrence>, bool)> = branches
        .iter()
        .map(|b| (Rc::clone(&b.pattern), b.guard.is_some()))
        .collect();
    let facts = anthill_core::kb::typing::match_arm_gamma_facts(
        &mut kb,
        &Value::Node(scrutinee),
        &arms,
        &[],
    );
    assert_eq!(
        facts[0].len(),
        1,
        "arm 1 carries its own `eq` and nothing earlier"
    );
    assert_eq!(
        facts[1].len(),
        2,
        "arm 2 carries the earlier `neq(o, some(red))` BESIDE its own `eq` — the negation \
         exists only because arm 1 is GROUND, which it is only because the nested `red` \
         was rewritten"
    );
    assert_eq!(facts[2].len(), 3, "and `none()` knows both earlier values");
}

/// THE SECOND, QUIETER SYMPTOM the ticket named: the WI-580 unfold case-splits a
/// suspended `eq` over one continuation per arm, each asserting
/// `unify(scrutinee, patternᵢ)`. A `Pattern::Var` arm becomes a FRESH VAR there
/// (`fresh_pattern_occ`), which unifies with everything — so no arm narrows the
/// scrutinee and the relational query cannot decide.
#[test]
fn the_relational_direction_now_decides_on_the_bare_spelling() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        definite_names(&mut kb, "ej5f5.paren_gen"),
        vec!["green".to_string()],
        "CONTROL: the parenthesized spelling always case-split"
    );
    assert_eq!(
        definite_names(&mut kb, "ej5f5.bare_gen"),
        vec!["green".to_string()],
        "the bare spelling now case-splits the same way"
    );
}
