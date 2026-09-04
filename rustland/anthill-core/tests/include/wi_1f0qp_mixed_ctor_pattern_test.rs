//! WI-20260827-1F0QP — a MIXED constructor PATTERN means what a MIXED constructor
//! APPLICATION means.
//!
//! ## The reading this ticket picks, and why
//!
//! `docs/kernel-language.md` states the RANK-AMONG-NOT-NAMED rule for sort bindings
//! (§5.2) and for operation calls (§2.2.10) — `two(2, a: 1)` puts 2 in `b`, the field
//! not already given by name — and said nothing at all about constructor PATTERNS. Of
//! the two admissible readings the ticket names, this suite asserts (a): a mixed
//! pattern reads the spelling its mixed application writes. A pattern is how a value
//! is taken apart and an application is how it is put together; making `case two(y, a: 1)`
//! reject the value `two(2, a: 1)` builds would be a rule with no reading behind it.
//! Reading (b) — a load error — was rejected because it would refuse in PATTERN
//! position the one spelling that is legal in every other position, and the spec has
//! no other such asymmetry.
//!
//! What was NOT admissible is what the tree did: the positional sub-pattern took the
//! LEADING field, collided with the named one, and the arm SILENTLY did not match, so
//! a later arm answered — `punmix(two(a: 1, b: 7))` returned 0 where the program says 7.
//!
//! ## FIVE PRODUCERS, FIVE ROWS
//!
//! The rank rule had SIX open-coded leading-index copies. `positional_to_named_plan`
//! (the shared owner, WI-500) owned the APPLICATION side only; each reader of the
//! PATTERN side had written its own. They are separate code paths reached by separate
//! programs, so each gets its own row here — a fix to one is invisible to the others:
//!
//!  1. `eval::pattern::match_constructor_pattern` — the RUNTIME matcher, reached with a
//!     GROUND scrutinee (`ground_*` below).
//!  2. `kb::resolve::fresh_pattern_occ` — the WI-580 unfold's pattern side, reached only
//!     when the scrutinee is UNGROUND and the SLD case-split runs (`unfold_*`). It
//!     carried a SECOND defect on the same line: `sort_by_key(s.index())` is INTERNING
//!     order where the canonical entity form is DECLARATION order.
//!  3. `kb::body_specialize::match_ctor_fields` — the SPECIALIZER's compile-time matcher
//!     (`specializer_*`). Worst of the three: its wrong answer is `PatOutcome::No`, a
//!     DEFINITE non-match that prunes the arm statically.
//!  4. `kb::body_specialize::ctor_field_occs` — the SCRUTINEE side of the same matcher,
//!     which read a mixed constructor OCCURRENCE (`specializer_reads_a_mixed_scrutinee`).
//!  5. `kb::typing`'s pattern binder typing — WHICH declared type a positional binder
//!     gets (`typer_*`). Invisible while an entity's fields share a type; a WRONG
//!     BINDER TYPE the moment they don't.
//!
//! The sixth, `kb::load`'s query-path `pos_field_type`, is the expected-type HINT for a
//! mixed QUERY's positional argument; `mixed_query_*` drives it. The seventh,
//! `eval::pattern::constructor_sub_values`, is the eval SCRUTINEE side — its doc
//! ASSERTED sub-values come back in declaration order, which concatenating
//! `positional ++ named` makes false for a mixed carrier; it now establishes that
//! rather than assuming it.
//!
//! ## THE OPERATION CALL, folded in
//!
//! A mixed OPERATION call (`add2(2, a: 1)`) was a LOAD ERROR — `named argument 'a' binds
//! a parameter already given` — where the constructor spelling of the same shape was
//! legal: one shape, two answers, two models for an author to learn. Filed as a separate
//! ticket at first and then folded in, so the rule is now ONE rule (kernel §6.3). Three
//! more sites, and `positional_param_indices` is their shared owner:
//!
//!  8. `bind_call_arguments` — the coverage check that refused it.
//!  9. the ARGUMENT TYPE CHECK and the inference loop beside it, plus the function-value
//!     path's `slots`. Not optional extras: with the rank rule live and these three left
//!     indexing by slot, a mixed call is CHECKED against one parameter and BOUND to
//!     another — `takeB(1, a: 1)` on `(a: Int64, b: String)` loaded clean and delivered
//!     an `Int64` to a `String` parameter. Review-found, after exactly that shipped in a
//!     first draft; `a_mixed_operation_call_*` uses a HETEROGENEOUS carrier so the row
//!     can see it.
//! 10. `reorder_named_args_in_apply` — THE SECOND PRODUCER, and the reason a typer-only
//!     fix would be worse than the bug: the runtime binds argument `i` to parameter `i`
//!     (`start_apply` streams `pos_args ++ named_args`, `enter_operation` zips that
//!     against `params`), so merely admitting the call would bind it BACKWARDS. A mixed
//!     call is rewritten ALL-POSITIONAL in parameter order.
//! 11. `kb::body_specialize::bind_params` — the specializer's own copy.
//!
//! `relational_result_column` is the same change's other half: §5.3 restricts the
//! functional-relation view to the all-positional spelling, which was IMPLIED before
//! only because a labelled call could not reach it. With the rank rule live
//! `Desc.describe(x: leaf(), ?r)` reaches it with `unfilled` empty and one surplus
//! positional — the relational signature — and the caller indexed `pos_results` out of
//! bounds. It now asks §5.3's question directly.
//!
//! ## THE CENSUS, AND WHAT IS EXEMPT
//!
//! `grep -n 'fields.get(i)\|covered\[i\]\|pos_args.get(i)'` over `anthill-core/src`
//! finds four more hits. Each is left as it is, and for a stated reason rather than
//! because it was not reached:
//!
//!  * `kb::typing`'s TUPLE pattern alignment (`bind_and_label_pattern`'s
//!    `Pattern::Tuple` arm) reads component `i` by SLOT, and must: §4.5 makes a
//!    tuple's component order its IDENTITY, which is why
//!    `canonicalize_record_named_args` is a deliberate no-op for an ordered product.
//!    The rank rule is a rule about FIELDS, which have no order of their own beyond
//!    declaration.
//!  * `kb::typing`'s named-argument subtyping (`b_covered`) matches ACTUALS to
//!    ACTUALS, not positions to fields; there is nothing to rank.
//!  * `kb::mod`'s spec-op carrier classification indexes `arg_places` by PLACE and
//!    falls back to `pos_args.get(i)`. Exempt for the reason already written at the
//!    site: it reads a GOAL at arity + 1, one positional longer than the call, so
//!    ranking a positional here would take the RESULT COLUMN for an argument — and
//!    a named-arg goal never becomes a call at all (WI-938 requires
//!    `named_arity: 0`), so its all-or-nothing decline costs no answer.
//!
//! ## WHAT REDDENS WHEN THE CHANGE IS BACKED OUT
//!
//! MEASURED, site by site (revert one file, run this suite):
//!
//! ```text
//!   backed out                          rows that redden
//!   eval/pattern.rs                     ground_*, typer_*
//!   kb/resolve.rs `fresh_pattern_occ`   unfold_*
//!   kb/body_specialize.rs               specializer_selects_*, specializer_reads_*
//!   kb/typing.rs                        typer_*, a_mixed_operation_call_*,
//!                                       unmixed_operation_calls_*
//!   kb/load.rs                          mixed_query_*
//!   everything                          all eight non-control rows
//! ```
//!
//! `typer_*` appears twice on purpose and the two failures are DIFFERENT: with the
//! typer site out it fails to LOAD (the binder types as `Int64` and is returned from an
//! op declared `-> String`), and with the eval site out it loads and answers from the
//! wrong arm. It is the only row that cannot be made site-pure — proving a binder's TYPE
//! requires running the operation, and running it goes through the matcher.
//!
//! `unmixed_operation_calls_*` is a CONTROL — it passes with and without this change —
//! but only while its fixture loads, and with `kb/typing.rs` out `OPSRC` does not load
//! at all (its mixed calls are refused). So it reddens there for a reason that is not
//! its subject. That is why `OPSRC` is a separate program from `SRC`: sharing one
//! fixture would have put every constructor row in the same position.
//!
//! Reverting `kb/resolve.rs` WHOLESALE does not compile: it owns
//! `rank_positional_among_unnamed`, which the other three sites call. The row above is
//! the `fresh_pattern_occ` hunk alone.
//!
//! `all_positional_and_all_named_patterns_are_unmoved` and
//! `the_mixed_application_is_unmoved` pass EITHER WAY, by design: they are the controls
//! that say the change is confined to the mixed PATTERN spelling. `typer_*` additionally
//! fails to LOAD with the typer site backed out, which is why it asserts the load and
//! then drives the operation.

use anthill_core::intern::Symbol;
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// `(total, definite)` for a nullary-headed rule. Both halves: a mixed pattern's
/// failure mode is a DECIDED answer from the WRONG arm (`total 1, definite 1` on a
/// goal that should have none), which a bare `len()` cannot tell from a suspension.
fn counts(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let def = sols.iter().filter(|s| s.is_definite()).count();
    (sols.len(), def)
}

/// `Two` is the two-field homogeneous carrier — the rank rule has something to get
/// wrong and the TYPES cannot tell the two fields apart, so every row below is about
/// the VALUE that arrives, never about a type error masking it. `Het` is its
/// heterogeneous twin, reserved for the typer row.
const SRC: &str = r#"
namespace test.wi1f0qp
  import anthill.prelude.{Int64, String}
  sort Two
    entity two(a: Int64, b: Int64)
  end
  -- The unfold's own carrier. The SLD case-split (`folded_call_match`) admits only
  -- a DISJOINT match — one arm per constructor head — so the unfold rows cannot
  -- reuse `Two`'s two-same-head arms; they would decline the unfold and suspend,
  -- measuring nothing. `one` is here to make the match disjoint, nothing else.
  sort Sh
    entity two2(a: Int64, b: Int64)
    entity one(c: Int64)
  end
  sort C
    -- THE SUBJECT: one positional sub-pattern and one named, in one pattern.
    -- `y` must be field `b` — the field NOT given by name — exactly as the
    -- APPLICATION `two(2, a: 1)` puts 2 in `b`.
    operation mixed(t: Two) -> Int64 =
      match t
        case two(y, a: 1) -> y
        case two(p, q) -> 0

    -- THE CONTROLS. Neither spelling is mixed, so neither moves.
    operation allPos(t: Two) -> Int64 =
      match t
        case two(p, q) -> q
    operation allNamed(t: Two) -> Int64 =
      match t
        case two(a: 1, b: w) -> w
        case two(p, q) -> 0

    -- The UNFOLD row's operation: same mixed pattern, over a DISJOINT match. Only
    -- the `two2` arm can answer 7, so a `= 7` goal isolates that arm.
    operation umixed(t: Sh) -> Int64 =
      match t
        case two2(y, a: 1) -> y
        case one(z) -> 0

    -- The mixed APPLICATION, the side WI-20260827-T2470 already fixed: 2 fills `b`.
    operation mixApp() -> Two = two(2, a: 1)


    -- The SPECIALIZER rows. `specMix` has BINDERS on both sides of the mixed
    -- pattern, because a literal sub-pattern against a skeleton leaf is
    -- undecidable and would never reach the ranking. `specScrut` matches on a
    -- constructor the OP BODY builds mixed, which is what `ctor_field_occs` reads.
    operation specMix(t: Two) -> Int64 =
      match t
        case two(y, a: z) -> y
        case two(p, q) -> 0
    operation specScrut() -> Int64 =
      match two(2, a: 1)
        case two(y, a: 1) -> y
        case two(p, q) -> 0
  end

  -- GROUND scrutinee: the eval matcher.
  rule ground7(1)  :- C.mixed(two(a: 1, b: 7)) = 7
  rule ground0(1)  :- C.mixed(two(a: 1, b: 7)) = 0
  -- the guard really is read: a scrutinee whose `a` is not 1 falls through
  rule groundFall(1) :- C.mixed(two(a: 9, b: 7)) = 0

  -- UNGROUND scrutinee: the WI-580 unfold's case-split (`fresh_pattern_occ`).
  rule unfold7(?t)  :- C.umixed(?t) = 7
  rule unfold0(?t)  :- C.umixed(?t) = 0

  -- CONTROLS, both spellings, ground.
  rule ctlPos(1)   :- C.allPos(two(a: 1, b: 7)) = 7
  rule ctlNamed(1) :- C.allNamed(two(a: 1, b: 7)) = 7
  rule ctlApp(1)   :- C.mixApp() = two(a: 1, b: 2)

  -- the specializer's own call site (its args stay unbound; the row inspects the
  -- SYNTHESIZED rule, not an answer)
  rule obSpecMix(?w) :- C.specMix(two(a: ?u, b: ?v), ?r), ?w = ?r
end
"#;

/// The OPERATION-CALL fixture, deliberately its OWN program rather than part of `SRC`.
/// With the call-binding change backed out this does not load — a mixed call is refused
/// — so folding it into the shared fixture would redden every constructor row in this
/// file for a reason that has nothing to do with constructors, and the per-site matrix
/// above would measure nothing.
///
/// `takeA` returns `a` and `takeB` returns `b` off the SAME call spelling, so the pair
/// pins the binding from both ends rather than asserting one value a wrong binding could
/// also produce.
///
/// ITS PARAMETERS ARE HETEROGENEOUS (`a: Int64, b: String`) and that is load-bearing,
/// not decoration. A first draft used two `Int64` parameters, and a review found what it
/// could not see: the typer's ARGUMENT TYPE CHECK still indexed by slot, so
/// `takeA("two", a: 1)` was refused naming `takeA.a` and `takeB(1, a: 1)` loaded clean
/// and delivered an `Int64` to a `String` parameter. With both fields one type, every
/// such row passes. Any carrier here must keep the two parameter types DISTINCT.
const OPSRC: &str = r#"
namespace test.wi1f0qp.ops
  import anthill.prelude.{Int64, String}
  sort C
    operation takeA(a: Int64, b: String) -> Int64  = a
    operation takeB(a: Int64, b: String) -> String = b
    operation callMixA() -> Int64  = takeA("two", a: 1)
    operation callMixB() -> String = takeB("two", a: 1)
    -- CONTROLS: the two unmixed spellings of the same call.
    operation callPosA()   -> Int64 = takeA(1, "two")
    operation callNamedA() -> Int64 = takeA(a: 1, b: "two")
    -- A mixed application of a FUNCTION VALUE, whose parameter list is an arrow's
    -- `slots` rather than an operation's `params` — a separate reader of the rule.
    operation applyIt(f: (acc: Int64, x: String) -> Int64) -> Int64 = f("hi", acc: 3)
    operation takeAcc(acc: Int64, x: String) -> Int64 = acc
    operation callFn() -> Int64 = applyIt(takeAcc)
  end
  rule opA(1)    :- C.callMixA() = 1
  rule opB(1)    :- C.callMixB() = "two"
  rule opAbad(1) :- C.callMixA() = 2
  rule opCtlPos(1)   :- C.callPosA()   = 1
  rule opCtlNamed(1) :- C.callNamedA() = 1
  rule opFn(1)   :- C.callFn() = 3
end
"#;

fn kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

fn ops_kb() -> KnowledgeBase {
    crate::common::load_kb_with(OPSRC)
}

// ── 1. the eval matcher ──────────────────────────────────────────────────────

/// SITE 1, `eval::pattern::match_constructor_pattern`. THE TICKET'S THREE ROWS, on a
/// GROUND scrutinee.
///
/// Backed out, `ground7` is (0, 0) and `ground0` is (1, 1) — the exact silent loss the
/// ticket measured: not "no answer", but a CONFIDENT WRONG one from the fallthrough arm.
#[test]
fn ground_a_mixed_pattern_binds_the_field_not_given_by_name() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ground7(1)"),
        (1, 1),
        "`case two(y, a: 1)` over `two(a: 1, b: 7)` binds `y` to field `b` = 7"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ground0(1)"),
        (0, 0),
        "and the fallthrough arm must NOT answer — the silent loss this ticket is about"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.groundFall(1)"),
        (1, 1),
        "CONTROL for the row above: the named `a: 1` is really tested, so a scrutinee \
         whose `a` is 9 genuinely does fall through to 0"
    );
}

// ── 2. the unfold's pattern side ─────────────────────────────────────────────

/// SITE 2, `kb::resolve::fresh_pattern_occ` — a SEPARATE PRODUCER from site 1, reached
/// only when the scrutinee is UNGROUND, so site 1's fix is invisible here.
///
/// Backed out, `unfold7` is (0, 0): the arm's pattern occurrence was built as
/// `two(a: 1, a: ?y)` — two args for one field — which unifies with no `Two` at all, so
/// the case-split's first arm could never fire and only the fallthrough survived.
#[test]
fn unfold_a_mixed_pattern_case_splits_to_the_field_not_given_by_name() {
    let mut kb = kb();
    let answers = crate::common::query_unary(&mut kb, "test.wi1f0qp.unfold7");
    let definite: Vec<_> = answers.iter().filter(|(_, d)| *d).collect();
    assert_eq!(
        definite.len(),
        1,
        "exactly one arm can yield 7 — the mixed `case two2(y, a: 1)` one — and the \
         case-split must COMMIT to it, not suspend. Got {answers:?}"
    );
    assert_eq!(
        entity_shape(&kb, &definite[0].0),
        "two2(a: 1, b: 7)",
        "the case-split bound `?t` to the shape the MIXED pattern names: `y` is field \
         `b`, so 7 lands in `b` and the named `a: 1` in `a`. Backed out, the arm's \
         pattern occurrence was `two2(a: 1, a: ?y)` and unified with nothing"
    );
    // Both arms can yield 0 once the mixed one works (`two2(a: 1, b: 0)` and any
    // `one`), so this counts DERIVATIONS, not a shape — deliberately a `>=`, because
    // its job is to pass EITHER WAY. Pinned at an exact 2 it would just be a second
    // copy of the row above; as a `>=` it says the unfold RAN, so the row above is
    // measuring the mixed arm's pattern and not a declined case-split.
    assert!(
        counts(&mut kb, "test.wi1f0qp.unfold0(?t)").1 >= 1,
        "CONTROL: the `one` arm case-splits and decides 0 with or without this change"
    );
}

// ── 3./4. the specializer ────────────────────────────────────────────────────

/// An entity-shaped answer as `two2(a: 1, b: 7)` — read CARRIER-NEUTRALLY through
/// [`TermView`], since a case-split answer rides on whatever carrier the search proved
/// it on (a `Value::Node` here, a `Value::Entity` or interned `Term` elsewhere) and the
/// row is about the FIELDS, not the carrier.
fn entity_shape(kb: &KnowledgeBase, v: &anthill_core::eval::Value) -> String {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let functor = match v.head(kb) {
        ViewHead::Functor {
            functor: Some(s), ..
        } => s,
        other => return format!("<not an entity: {other:?}>"),
    };
    let short = |s: Symbol| kb.local_name_of(s).rsplit('.').next().unwrap_or("").to_string();
    let fields: Vec<Symbol> = kb
        .entity_field_names(functor)
        .map(|f| f.to_vec())
        .unwrap_or_default();
    let args: Vec<String> = fields
        .iter()
        .map(|f| match v.named_arg(kb, *f) {
            Some(item) => match crate::common::scalar_int(kb, &item.to_value()) {
                Some(n) => format!("{}: {n}", short(*f)),
                None => format!("{}: <non-int>", short(*f)),
            },
            None => format!("{}: <missing>", short(*f)),
        })
        .collect();
    format!("{}({})", short(functor), args.join(", "))
}

/// The operation symbol with this short name.
fn op_sym(kb: &KnowledgeBase, short: &str) -> Symbol {
    all_operation_params(kb)
        .into_iter()
        .map(|(s, _)| s)
        .find(|s| kb.local_name_of(*s).rsplit('.').next() == Some(short))
        .unwrap_or_else(|| panic!("operation `{short}` not found"))
}

/// The single defining rule synthesized for `op`, rendered as its body RHS shape.
fn synth_rhs(kb: &mut KnowledgeBase, rule_qn: &str, op_short: &str) -> String {
    kb.synthesize_body_derived_defrules(rule_qn);
    let op = op_sym(kb, op_short);
    let rid = kb
        .rules_by_functor(op)
        .into_iter()
        .find(|r| !kb.is_fact(*r))
        .unwrap_or_else(|| panic!("no defining rule synthesized for `{op_short}`"));
    let body = kb.rule_body_nodes(rid);
    assert_eq!(body.len(), 1, "defining rule has one `?result = <rhs>` goal");
    let rhs = match body[0].as_expr() {
        Some(Expr::Apply { pos_args, .. }) if pos_args.len() == 2 => {
            std::rc::Rc::clone(&pos_args[1])
        }
        other => panic!("body goal must be `eq(?result, rhs)`, got {other:?}"),
    };
    format!("{:?}", rhs.as_expr())
}

/// SITE 3, `kb::body_specialize::match_ctor_fields`. A THIRD producer: the compile-time
/// matcher that picks an arm while SYNTHESIZING a defining rule, over a fresh-leaf
/// SKELETON rather than a value.
///
/// Its wrong answer was the worst of the three — `PatOutcome::No` is a DEFINITE
/// non-match, so the mixed arm was pruned STATICALLY and the synthesized rule was the
/// fallthrough's constant. Backed out, the RHS is `Const(Int(0))` instead of the binder.
#[test]
fn specializer_selects_the_mixed_arm() {
    let mut kb = kb();
    let rhs = synth_rhs(&mut kb, "test.wi1f0qp.obSpecMix", "specMix");
    assert!(
        rhs.contains("Var("),
        "the mixed arm must survive specialization and return its BINDER `y`; \
         got `{rhs}` — `Const(Int(0))` there means the arm was pruned statically"
    );
    assert!(
        !rhs.contains("Int(0)"),
        "and specifically NOT the fallthrough constant: {rhs}"
    );
}

/// SITE 4, `kb::body_specialize::ctor_field_occs` — the SCRUTINEE half of the same
/// matcher, and a genuinely different input: a constructor the OPERATION BODY builds
/// MIXED (`match two(2, a: 1)`), which the loader never desugars (that is what
/// WI-20260827-T2470 established).
///
/// Backed out, the reader put 2 in `a`, found `a: 1` wanting a slot already taken, and
/// answered `None` — so the specializer called an ordinary constant value UNDECIDABLE
/// and left a residual `match` where a value was staring at it.
#[test]
fn specializer_reads_a_mixed_scrutinee() {
    let mut kb = kb();
    let op = op_sym(&kb, "specScrut");
    // `op_defining_equations` is a LOUD decline: it returns `None` when the reduced
    // body still contains a `match`. Backed out, that is exactly what happens — the
    // reader could not decide the mixed scrutinee, so the match residualized and this
    // `expect` fires. Post-fix it reduces to a single unguarded equation.
    let eqs = kb
        .op_defining_equations(op)
        .expect("`match` over a constructor the body BUILDS must reduce, not residualize");
    assert_eq!(eqs.len(), 1, "one arm survives, with no `if` guards");
    assert!(eqs[0].guards.is_empty(), "the arm is unguarded");
    let rendered = format!("{:?}", eqs[0].result.as_expr());
    assert!(
        rendered.contains("Int(2)"),
        "`match two(2, a: 1)` selects `case two(y, a: 1)` and reduces to 2 — the \
         mixed scrutinee means `two(a: 1, b: 2)`, so `y` is 2. Got: {rendered}"
    );
}

// ── 5. the typer ─────────────────────────────────────────────────────────────

/// SITE 5, `kb::typing`'s pattern binder typing — WHICH declared type a positional
/// binder is given.
///
/// This is the row `Two` cannot carry: with both fields `Int64`, ranking to the wrong
/// field is invisible to the typer. `Het` declares `a: Int64, b: String`, so in
/// `case het(y, a: 1)` the binder `y` is field `b` and must type as `String`.
///
/// Backed out, `y` types as `Int64`, and returning it from an operation declared
/// `-> String` is a TYPE ERROR — the fixture does not load at all. So this row asserts
/// the load first and then DRIVES the operation, because "it loads" alone would keep
/// passing if `hpick` resolved to nothing.
#[test]
fn typer_a_mixed_pattern_binder_is_typed_from_the_field_it_takes() {
    const HET: &str = r#"
namespace test.wi1f0qp.hetero
  import anthill.prelude.{Int64, String}
  sort Het
    entity het(a: Int64, b: String)
  end
  sort D
    operation hpick(h: Het) -> String =
      match h
        case het(y, a: 1) -> y
        case het(p, q) -> "fallthrough"
  end
  rule hp(1)   :- D.hpick(het(a: 1, b: "seven")) = "seven"
  rule hpBad(1) :- D.hpick(het(a: 1, b: "seven")) = "fallthrough"
end
"#;
    let mut kb = crate::common::load_kb_with(HET);
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.hetero.hp(1)"),
        (1, 1),
        "`y` is field `b`, so it types as `String` AND carries b's value"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.hetero.hpBad(1)"),
        (0, 0),
        "CONTROL: the fallthrough arm did not answer — without it the row above \
         would pass on a String that merely happens to be there"
    );
}

// ── 6. the query loader's expected-type hint ─────────────────────────────────

/// SITE 6, `kb::load`'s query-path `pos_field_type`. A mixed QUERY's positional
/// argument is desugared into the field it ranks to (WI-433, already through the shared
/// owner); the expected TYPE it is converted under was computed by a SECOND, leading-index
/// rule. So a mixed query converted its positional argument under a field's declared type
/// and then stored it in a DIFFERENT field.
///
/// Driven where that hint is observable at all: `expected` reaches exactly one decision
/// on this path, `list_literal_lowering` (WI-1096), which lowers a `[…]` surface literal
/// to a `cons`/`nil` chain only when the expected type IS a list. So a `[…]` in a MIXED
/// query's positional slot is the row. Backed out, the hint is `tag`'s `Int64`,
/// `find_list_element_type` answers `None`, the bracket stays an unlowered
/// `anthill.reflect.ListLiteral` term, and the query cannot match the `cons` chain the
/// loader stored — even though the desugar put it in the right field.
#[test]
fn mixed_query_types_its_positional_argument_from_the_field_it_ranks_to() {
    const BAG: &str = r#"
namespace test.wi1f0qp.bagns
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{cons}
  sort Bag
    entity bag(tag: Int64, xs: List[T = Int64])
  end
  fact bag(tag: 1, xs: [1, 2])
end
"#;
    let mut kb = crate::common::load_kb_with(BAG);
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.bagns.Bag.bag([1, 2], tag: 1)"),
        (1, 1),
        "the MIXED query `bag([1, 2], tag: 1)` ranks `[1, 2]` into `xs` AND types it \
         from `xs`, so the bracket lowers to the same `cons` chain the fact stored"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.bagns.Bag.bag(tag: 1, xs: [1, 2])"),
        (1, 1),
        "CONTROL, passing either way: the ALL-NAMED spelling of the same query already \
         took its hint by field name, so it was never affected"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.bagns.Bag.bag([1, 3], tag: 1)"),
        (0, 0),
        "CONTROL for the row above: the elements are really compared, so the row is \
         not passing on a list that matches anything"
    );
}

// ── 7. the operation call ────────────────────────────────────────────────────

/// SITE 7, `kb::typing`'s `bind_call_arguments` + `reorder_named_args_in_apply` +
/// `kb::body_specialize`'s `bind_params` — the OPERATION CALL, folded in because the
/// asymmetry was the whole complaint: `two(2, a: 1)` was legal and `add2(2, a: 1)` was
/// a load error, so one shape had two answers and an author two models to learn.
///
/// Backed out, the fixture does NOT LOAD — `named argument 'a' binds a parameter
/// already given` — so this row asserts the load and then DRIVES the call, because a
/// clean load says nothing about which parameter each argument reached.
///
/// `takeA` returns `a` and `takeB` returns `b` off the SAME call spelling, so the pair
/// pins the binding in both directions rather than asserting one number that a wrong
/// binding could also produce. `opAbad` is the refutation: 1 is the answer AND 2 is not.
///
/// THE SECOND PRODUCER, which is why the typer alone is not the fix: the runtime binds
/// argument `i` to parameter `i` (`start_apply` streams `pos_args ++ named_args`,
/// `enter_operation` zips that against `params`), so a typer that merely stopped
/// refusing would have loaded a call the runtime then bound backwards — `takeA` would
/// answer 2. `reorder_named_args_in_apply` emitting the arguments in PARAMETER order is
/// what makes `opA` and `opB` disagree correctly.
#[test]
fn a_mixed_operation_call_binds_like_a_mixed_constructor() {
    let mut kb = ops_kb();
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ops.opA(1)"),
        (1, 1),
        "`takeA(2, a: 1)` gives parameter `a` the NAMED 1 — so `takeA`, which returns \
         `a`, answers 1"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ops.opB(1)"),
        (1, 1),
        "and parameter `b` the POSITIONAL 2 — the same call, read from the other end. \
         Without the runtime reorder this is where a typer-only fix answers 1"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ops.opAbad(1)"),
        (0, 0),
        "and `takeA` does NOT answer 2 — the row above is a binding, not a coincidence"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ops.opFn(1)"),
        (1, 1),
        "and a mixed application of a FUNCTION VALUE — `f(\"hi\", acc: 3)` against \
         `(acc: Int64, x: String)` — ranks the same way. A separate reader (an arrow's \
         `slots`, not an operation's `params`), so a separate row: with it left \
         indexing by slot this call is refused naming `acc`"
    );
}

/// §5.3's functional-relation view is the ALL-POSITIONAL spelling, and admitting the
/// mixed call is what made that condition load-bearing rather than implied.
///
/// `Desc.describe(x: leaf(), ?r)` fills every parameter BY NAME and leaves one positional
/// over — `unfilled` empty, `surplus_positional == 1`, which is the relational spelling's
/// own signature. It could not reach `relational_result_column` before, because a label
/// over a positionally-filled parameter was a coverage error; with the rank rule live it
/// can, and the column index it returned (`params.len()`) indexed `pos_results` OUT OF
/// BOUNDS — a loader PANIC on an ordinary program, review-found.
///
/// So the view now asks §5.3's question directly ("named arguments are not this shape:
/// the result column is positional and last"), and the goal is the ordinary over-arity
/// call it is. Backed out — remove the `!binding.has_named_args` clause — this test
/// PANICS rather than failing, which is the whole point of driving it.
#[test]
fn a_named_arg_goal_is_not_the_relational_result_column() {
    const REL: &str = r#"
namespace test.wi1f0qp.rel
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    operation describe(x: Leaf) -> Int64 = 7
    provides Desc[T = Leaf]
  end
  rule answer(?r) :- Desc.describe(x: leaf(), ?r)
end
"#;
    let errs = match crate::common::try_load_kb_with(REL) {
        Ok(_) => panic!("a goal with a label AND a surplus positional is not the \
                         relational view (§5.3) — it must be refused as over-arity"),
        Err(e) => e,
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("expected 1 argument") && joined.contains("got 2 arguments"),
        "and refused by WI-1100's ordinary arity diagnostic, naming the declared arity \
         and the count given; got: {joined}"
    );
}

/// THE OPERATION-CALL CONTROLS: neither unmixed spelling has a ranking decision to
/// make, so `takeA(1, 2)` and `takeA(a: 1, b: 2)` mean what they always meant. They are
/// what says the argument REORDER above is confined to the mixed call rather than a
/// change to how every call binds — the risk that made a second producer worth naming.
///
/// They pass with and without this change, but only while `OPSRC` LOADS, and with the
/// typer site backed out it does not (its mixed calls are refused). So they redden in
/// that one column of the matrix for a reason that is not their subject — see the
/// header. Splitting them into a third fixture with no mixed call in it would make the
/// column clean and the control weaker: what must be shown unmoved is an unmixed call
/// sitting in the same program as a mixed one, since that is the program this change
/// newly admits.
#[test]
fn unmixed_operation_calls_are_unmoved() {
    let mut kb = ops_kb();
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ops.opCtlPos(1)"),
        (1, 1),
        "all-positional `takeA(1, 2)` still answers 1"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ops.opCtlNamed(1)"),
        (1, 1),
        "all-named `takeA(a: 1, b: 2)` still answers 1"
    );
}

/// THE ADJACENT DEFECT THIS DOES NOT FIX, pinned at its CURRENT (wrong) value so
/// WI-20260829-QBNKY has a row to flip and so the measurement behind a code comment
/// cannot rot.
///
/// An OVER-ARITY constructor pattern — `case two(p, q, r)` on `entity two(a, b)` — LOADS
/// CLEAN, where the over-arity TERM spelling of the same shape is a located load error.
/// It is then refused by whichever consumer notices first, and no two agree: the eval
/// matcher's arity-strict test silently does not match, `fresh_pattern_occ` declines the
/// whole unfold so the goal RESIDUALIZES, `match_ctor_fields` answers a definite
/// non-match, and the typer types the surplus binder from nothing.
///
/// This is measured HERE because WI-20260827-1F0QP tripped on it: routing
/// `fresh_pattern_occ` through the shared owner, its `OverArity` arm took
/// `anf_flatten`'s `debug_assert!(false, …)` precedent — and the assert FIRED on this
/// fixture, an ordinary source program. The arm is a plain decline instead, and the
/// comment there says why. When QBNKY makes the shape a load error, this test becomes
/// an `expect_load_errors` and that arm can take the assert its sibling has.
///
/// Asserted as CURRENT BEHAVIOUR, not as correct behaviour.
#[test]
fn an_over_arity_constructor_pattern_still_loads_and_residualizes() {
    const OA: &str = r#"
namespace test.wi1f0qp.oa
  import anthill.prelude.Int64
  sort Sh
    entity two(a: Int64, b: Int64)
    entity one(c: Int64)
  end
  sort C
    operation pick(t: Sh) -> Int64 =
      match t
        case two(p, q, r) -> p
        case one(z) -> 0
  end
  rule g(?t) :- C.pick(?t) = 0
end
"#;
    // It LOADS — this is the whole finding, and WI-20260829-QBNKY must make it a
    // located load error naming `two`, the sub-pattern count and the declared fields.
    let mut kb = crate::common::load_kb_with(OA);
    let answers = crate::common::query_unary(&mut kb, "test.wi1f0qp.oa.g");
    assert_eq!(
        answers.iter().filter(|(_, d)| *d).count(),
        0,
        "and it DECIDES NOTHING: `fresh_pattern_occ` declines the unfold over the \
         malformed arm, so the whole case-split — the well-formed `one` arm included — \
         is left as a residual. WI-20260829-QBNKY must refuse the pattern at LOAD, at \
         which point this fixture stops loading and this row becomes an \
         `expect_load_errors`"
    );
}

// ── the controls ─────────────────────────────────────────────────────────────

/// THE CONTROLS, and they pass BOTH WITH AND WITHOUT this change, by design: the rank
/// rule only has a choice to make when a pattern is MIXED. An all-positional pattern
/// ranks over every field and an all-named one has no positional to rank, so both
/// spellings mean today what they meant before — which is what makes this change a
/// repair of one spelling rather than a redefinition of pattern matching.
#[test]
fn all_positional_and_all_named_patterns_are_unmoved() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ctlPos(1)"),
        (1, 1),
        "`case two(p, q)` still binds `q` to `b`"
    );
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ctlNamed(1)"),
        (1, 1),
        "`case two(a: 1, b: w)` still binds `w` to `b`"
    );
}

/// THE OTHER CONTROL: the APPLICATION side, which WI-20260827-T2470 fixed and this
/// ticket must not disturb. It is the row that says the two sides now AGREE rather than
/// that the pattern side moved somewhere new — `two(2, a: 1)` and `case two(y, a: 1)`
/// read one spelling one way.
#[test]
fn the_mixed_application_is_unmoved() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.wi1f0qp.ctlApp(1)"),
        (1, 1),
        "`two(2, a: 1)` still means `two(a: 1, b: 2)`"
    );
}
