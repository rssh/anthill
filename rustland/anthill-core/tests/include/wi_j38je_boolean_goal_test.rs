//! WI-20260822-J38JE — WHAT A TERM IN GOAL POSITION MEANS.
//!
//! Two halves, delivered in two passes and pinned together here because they are one
//! rule read from both ends:
//!
//!   * **A BOOLEAN CONSTANT IS A SEARCH** — `true` succeeds, `false` fails, at every
//!     goal position (user decision 2026-08-22). `false` is legal-and-DEAD rather than
//!     refused, which is what §6.6 already requires of the boolean OPERATORS ("at every
//!     GOAL position: the body's atoms, and the goal slots of the connectives above
//!     them").
//!   * **EVERY OTHER CONSTANT IS A LOAD ERROR** (item 4) — `:- 42`, `:- "hello"`,
//!     `:- 1.5` denote no truth, so the clause can never fire. The complement of the
//!     constant reading.
//!   * **AND THE READING IS TYPE-DIRECTED, NOT A LIST OF SHAPES** (item 1, USER DECISION
//!     2026-08-22: "of course any bool expression. How can be other?"). A `Bool`-valued
//!     expression in goal position is a CONDITION — it evaluates, and the goal succeeds
//!     iff the value is `true`. An earlier pass of this ticket shipped an ENUMERATED
//!     reading instead and defended it with §6.6; that was wrong, and §6.6 was never
//!     evidence for it. §6.6 redirects three NAMES (`not` / `or` / `and`) to the
//!     resolver primitives before anything is typed, so those names never reach the
//!     question — a rule about names, not about terms.
//!
//! ── WHAT WAS WRONG, MEASURED ─────────────────────────────────────────────────
//!
//! Nothing gave a constant a reading, so a constant in goal position became NO GOAL AT
//! ALL: it resolved to no clause and no builtin, and WI-1034's "rule-body goal names
//! nothing" refusal cannot reach it because a CONSTANT NAMES NO NAME. `false` therefore
//! gave the right answer for the wrong reason, `true` gave the wrong one, and `42` gave
//! none at all:
//!
//! | body | logic | before | now |
//! |---|---|---|---|
//! | `:- true` | 1 | 1 (the loader strip) | 1 |
//! | `:- false` | 0 | 0 — BY ACCIDENT | 0 |
//! | `:- not(true)` | 0 | **1** | 0 |
//! | `:- not(false)` | 1 | 1 | 1 |
//! | `:- base(9) \| true` | 1 | **0** | 1 |
//! | `:- 42` | — | loads, answers 0, **no diagnostic** | **load error** |
//! | `:- not(42)` | — | loads, answers **1** | **load error** |
//! | `:- b.flag` (`flag: true`) | 1 | 1 | 1 |
//! | `:- b.flag` (`flag: **false**`) | 0 | **1** | 0 |
//!
//! The dot row is the type-directed reading arriving. `b.flag` lowers to
//! `field_access(b, flag)` at arity 2, whose BUILTIN goal reading was "the projection
//! landed" — so it answered 1 for a `false` field, and 1 for an `Int64` field too. It is
//! now routed to `eq(field_access(…), true)`, the SAME rewrite WI-580 applies to a
//! `Bool` operation's bare goal: one answer to "is this expression true", however the
//! expression is spelled.
//!
//! The two wrong boolean rows share one cause, and 061 is half of it: `:- true` got its
//! meaning from a strip over the body's TOP-LEVEL goal list, which by construction
//! cannot reach a goal nested under `not` or `|`. Before 061 both positions answered the
//! same (wrongly); after it, one spelling had two readings decided by DEPTH. The reading
//! now lives in `SearchStream::step_init`, where every goal passes.
//!
//! ── THE BACK-OUTS ────────────────────────────────────────────────────────────
//!
//! * **THE GOAL READING** — gate off the `ViewHead::Const(Literal::Bool(b))` arm in
//!   `step_init` (kb/resolve.rs). RUN over the whole `wi_tests` binary (3283 rows),
//!   **exactly 2 fail**: [`the_reading_holds_at_every_goal_position`] and
//!   [`the_boolean_constants_keep_their_reading`], each on the same two goals —
//!   `not(<false-ish>)` and a disjunction whose live branch is `true`. It felled ONE
//!   row when it shipped, and the second is the control this pass added; the count
//!   moved because the file grew, not because the reading did.
//!   [`a_false_goal_fails_by_the_rule_not_by_accident`] still passes either way, and
//!   that is the point of its own comment: `false` answers 0 under BOTH readings, by
//!   the rule now and by resolving-to-nothing before, so no count of its own can
//!   separate them. `not(true)` is what separates them. The top-level rows pass either
//!   way too (the loader strip answers `true`) — which is why the nested ones are here.
//! * **THE LOADER STRIP** — gate off `is_empty_conjunction_goal` in `load_rule`'s body
//!   loop (kb/load.rs, 061). RUN over the same 3283 rows, **exactly 1 fails**:
//!   [`a_top_level_true_is_still_erased_at_load`]. Everything else passes, INCLUDING all
//!   of `wi_fqc85`, because the resolver arm now answers the goal the strip would have
//!   removed. That is a guard absorbing a neighbour's domain: when 061 shipped, this
//!   same back-out felled 24 rows. It is the reason this row asserts the BODY and not an
//!   answer count, and `wi_fqc85`'s own back-out list has been corrected to say so.
//! * **THE CONSTANT REFUSAL** (item 4) — neutralize the `Expr::Const(lit)` arm in
//!   `check_goal_atom_reading` (kb/typing.rs) so a constant falls through to `continue`.
//!   RUN over the whole `wi_tests` binary (3283 rows), **exactly 3 fail**:
//!   [`a_non_boolean_constant_goal_is_a_load_error`],
//!   [`the_refusal_holds_at_every_goal_position`] and
//!   [`the_refusal_names_the_position_not_just_the_rule`]. Every reading row and both
//!   controls pass either way, by design — a control measures what must not move.
//! * **THE DESCENT** (a SECOND axis of the same fix, so it gets its own back-out) —
//!   make `proved_goal_children` return empty for `forall_in` / `some_in` /
//!   `forall_impl`, which is the hole the retired three-symbol allowlist had. RUN over
//!   the same 3283 rows, **exactly 1 fails**:
//!   [`the_refusal_holds_at_every_goal_position`], on its last two sub-rows.
//!   [`the_boolean_constants_keep_their_reading`] passes either way and that is the
//!   point — the RESOLVER answers a boolean constant inside a quantifier whatever the
//!   loader checks, which is exactly how the two readings came apart.
//! * **THE CONDITION READING FOR A DOT PROJECTION** — neutralize the
//!   `BuiltinTag::FieldAccess` arm in `step_init` (kb/resolve.rs), so the builtin's own
//!   arity-2 goal reading wins again. RUN over the whole `wi_tests` binary, **exactly 2
//!   fail**: [`a_bool_expression_in_goal_position_is_a_condition`], on the `false` field
//!   ANSWERING 1 (the `true` field passes either way, which is why the row drives both
//!   polarities), and [`what_the_condition_reading_cannot_yet_reduce`], whose `pdotn`
//!   row goes 0 → 1. That second one is the reason the non-`Bool` residue is pinned
//!   rather than described: the same arm decides both, so a back-out that fell only the
//!   `Bool` row would have left the other half unmeasured.
//! * **THE LOCALIZATION** — replace the `Some(o.span.source)` tag with `None` at both
//!   pushes in `check_goal_atom_reading`. RUN over the same 3283 rows, **exactly 1
//!   fails**: [`the_refusal_names_the_position_not_just_the_rule`]. The message
//!   survives and still names the constant, so no other row can see the difference —
//!   it renders `… at 61..63`, a byte offset naming no file, no line and no column.
//!   That is why the row asserts the PREFIX and not the text.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// Load `src` and return its rendered load errors, failing if it LOADS — for the
/// refusal rows, whose whole content is that the program no longer loads.
fn refusal(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a load error, but this loaded clean:\n{src}"))
}

/// One namespace carrying every shape, so the rows below differ only in the goal they
/// drive. `base` has the single clause `base(7)`, so `base(9)` is a goal that FAILS —
/// which is what makes the disjunction rows measure the other branch.
const SRC: &str = r#"
namespace j38je
  import anthill.prelude.{Int64, Bool}
  rule base(7) :- true

  rule ptrue(1)    :- true
  rule pfalse(1)   :- false
  rule nottrue(1)  :- not(true)
  rule notfalse(1) :- not(false)
  rule andtrue(1)  :- base(7), true
  rule andfalse(1) :- base(7), false
  rule ortrue(1)   :- base(9) | true
  rule orfalse(1)  :- base(9) | false
  rule orlive(1)   :- base(7) | false

  rule gtlive(1)   :- Int64.gt(2, 1)
  rule gtdead(1)   :- Int64.gt(1, 2)
end
"#;

#[test]
fn a_boolean_constant_goal_is_a_search_that_succeeds_or_fails() {
    // THE DECISION ITSELF, at the top level. PASSES EITHER WAY under the goal-reading
    // back-out (061's loader strip answers `true` there, and `false` fails by accident),
    // which is why it is not the row that measures the fix — it is the row that says
    // what the fix must not change.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "j38je.ptrue(1)"), 1, "`:- true` is a successful search");
    assert_eq!(answers(&mut kb, "j38je.pfalse(1)"), 0, "`:- false` is an unsuccessful one");
}

#[test]
fn the_reading_holds_at_every_goal_position() {
    // THE ROW THAT MEASURES THE FIX, and the one no top-level test can stand in for. A
    // goal nested under `not` or `|` never reaches the loader's top-level strip, so
    // before this it kept the old non-reading: `not(true)` SUCCEEDED and a disjunction
    // whose live branch was `true` FAILED.
    //
    // BACKED OUT (delete the `ViewHead::Const(Literal::Bool(b))` arm from `step_init`):
    // this row FAILS on `nottrue` (1, not 0) and on `ortrue` (0, not 1).
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "j38je.nottrue(1)"), 0, "not(true) FAILS");
    assert_eq!(answers(&mut kb, "j38je.notfalse(1)"), 1, "not(false) succeeds");
    assert_eq!(answers(&mut kb, "j38je.ortrue(1)"), 1, "a dead branch beside `true`");
    assert_eq!(answers(&mut kb, "j38je.orfalse(1)"), 0, "two dead branches");
    assert_eq!(
        answers(&mut kb, "j38je.orlive(1)"),
        1,
        "CONTROL: a live branch beside `false` — `false` must not poison the disjunction"
    );
}

#[test]
fn a_false_goal_fails_by_the_rule_not_by_accident() {
    // `false` ANSWERED 0 BEFORE THIS TOO, and that is the trap the row exists for: it
    // failed because a `Term::Const` resolves to no clause and no builtin, the same way
    // a TYPO fails — WI-1034's "names nothing" refusal cannot reach a constant, which
    // names no name. The answer count alone cannot tell the two apart, so the row drives
    // the composition: under the accident `not(false)` also succeeds (a dead goal
    // negated), while `false` at the tail of a conjunction is indistinguishable either
    // way. What separates them is `not(true)` — measured in the row above — and the
    // conjunction rows here, which pin that a `false` reached mid-body kills the clause
    // rather than being skipped like `true`.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(answers(&mut kb, "j38je.andtrue(1)"), 1, "`true` mid-body skips");
    assert_eq!(answers(&mut kb, "j38je.andfalse(1)"), 0, "`false` mid-body kills");
}

#[test]
fn a_top_level_true_is_still_erased_at_load() {
    // THE TWO READINGS DO NOT OVERLAP, and this row is the seam. §6.1 reads `fact H` as
    // `H :- true`, and only an EMPTY body makes that the same clause `fact` stores —
    // `is_equation` and WI-624's ground-fact fast path both read body-emptiness, so a
    // clause carrying one always-succeeding goal is a DIFFERENT clause with the same
    // answers. The resolver arm cannot supply that; the loader strip must stay.
    //
    // Asserts the BODY, not an answer count, because the answers agree under both
    // readings — which is precisely why this is the only row the loader-strip back-out
    // fells.
    let kb = crate::common::load_kb_with(
        "namespace j38jeb\n  rule viatrue(1) :- true\n  fact viafact(1)\nend\n",
    );
    let sym = kb
        .try_resolve_symbol("j38jeb.viatrue")
        .expect("the rule head is scoped where it is written");
    let rules = kb.rules_by_functor(sym);
    assert_eq!(rules.len(), 1, "one clause");
    assert!(
        kb.rule_body_nodes(rules[0]).is_empty(),
        "`:- true` IS the empty body — the `true` contributed no goal"
    );
}

#[test]
fn a_bool_expression_in_goal_position_is_a_condition() {
    // ITEM 1, AS DECIDED: a `Bool`-valued expression in goal position evaluates, and the
    // goal succeeds iff it is `true`. Every spelling below is one expression kind, and
    // they must all agree — that agreement IS the reading, and a per-shape list is what
    // it replaced.
    //
    // THE DOT ROWS ARE THE ONES THAT MOVED. `b.flag` lowered to `field_access(b, flag)`
    // at arity 2, and the builtin's goal reading was "the projection landed" — so it
    // answered 1 for `flag: false`, a WRONG answer rather than a missing one. Both
    // polarities are here because the `true` row passes under the back-out too: only the
    // `false` one separates "is it true" from "does it exist".
    //
    // BACKED OUT (delete the `BuiltinTag::FieldAccess` arm from `step_init`): this row
    // fails on `dotfalse` (1, not 0) and on `dotneg` (0, not 1).
    let mut kb = crate::common::load_kb_with(
        "namespace j38jej\n  import anthill.prelude.{Int64, Bool}\n  \
         sort Box\n    entity box(n: Int64, flag: Bool)\n    \
         operation isbig(b: Box) -> Bool = Int64.gt(1, 0)\n    \
         operation issmall(b: Box) -> Bool = Int64.gt(0, 1)\n  end\n  \
         rule dottrue(1)  :- box(n: 1, flag: true).flag\n  \
         rule dotfalse(1) :- box(n: 1, flag: false).flag\n  \
         rule dotneg(1)   :- not(box(n: 1, flag: false).flag)\n  \
         rule optrue(1)   :- Box.isbig(box(n: 1, flag: true))\n  \
         rule opfalse(1)  :- Box.issmall(box(n: 1, flag: true))\n  \
         rule littrue(1)  :- true\n  \
         rule litfalse(1) :- false\n  \
         rule bitrue(1)   :- Int64.gt(2, 1)\n  \
         rule bifalse(1)  :- Int64.gt(1, 2)\nend\n",
    );
    for (pred, want) in [
        ("dottrue", 1),   // a Bool DOT PROJECTION
        ("dotfalse", 0),
        ("dotneg", 1),    // …and it composes under `not`, which is where a wrong
        ("optrue", 1),    // a Bool OPERATION call at declared arity (WI-583)
        ("opfalse", 0),
        ("littrue", 1),   // a Bool CONSTANT (the decided half)
        ("litfalse", 0),
        ("bitrue", 1),    // a resolver BUILTIN returning Bool
        ("bifalse", 0),
    ] {
        assert_eq!(
            answers(&mut kb, &format!("j38jej.{pred}(1)")),
            want,
            "`{pred}`: every Bool-valued expression in goal position is the same condition"
        );
    }
}

// ── ITEM 4 — every other constant is a load error ────────────────────────────
//
// Each refusal fixture is its OWN namespace and its own load. Sharing one would make
// the rows unmeasurable in both directions: a single load error fails the whole file,
// so a fixture holding all four would pass while only one of them fired, and — worse —
// the controls below would die of a neighbour's error rather than of their own reading.

#[test]
fn a_non_boolean_constant_goal_is_a_load_error() {
    // THE HEADLINE GAP: three constant sorts, three separate loads. Before this each
    // one loaded clean and answered nothing — indistinguishable from a deliberate
    // `:- false`, which is the whole reason it needed a word said about it.
    //
    // BACKED OUT (delete the `Expr::Const(lit)` arm from `check_goal_atom_reading`):
    // every assertion here fails — the loads succeed.
    for (literal, body) in [("42", "42"), (r#""hello""#, r#""hello""#), ("1.5", "1.5")] {
        let src = format!("namespace j38jec{}\n  rule p(1) :- {body}\nend\n", literal.len());
        let errs = refusal(&src);
        assert!(
            errs.iter().any(|e| e.contains(literal) && e.contains("GOAL position")),
            "the refusal must quote the constant AS WRITTEN ({literal}) and name the \
             position; got: {errs:?}"
        );
    }
}

#[test]
fn the_refusal_holds_at_every_goal_position() {
    // THE ROW THAT MAKES ITEM 4 AGREE WITH THE READING IT COMPLEMENTS. `true`/`false`
    // are answered at every goal position, so their complement must be REFUSED at every
    // goal position, or the two halves disagree by depth — the exact defect 061 left
    // behind for `true`. `not(42)` is the sharpest: before this it answered ONE, a
    // negation succeeding over a goal with no meaning at all.
    //
    // The `|` row is where this pass's descent is WIDER than `undefined_rule_body_goals`'
    // (WI-863/WI-1034 tolerate a name that means nothing in a bare `or` branch, because
    // it may mean something in another program). A constant has no such defence, and
    // that difference is stated at `check_goal_atom_reading`.
    //
    // BACKED OUT (same arm): all five fail — the loads succeed, and `not(42)` answers 1.
    //
    // THE LAST TWO ARE THE REVIEW'S FINDING. The pass used to descend through a
    // hand-written allowlist of three symbols, so a bounded quantifier's body and a
    // discharge's consequent — both goal positions the resolver runs — were never
    // entered, while `SearchStream`'s boolean arm answered `true`/`false` inside them
    // perfectly well. That is the same "one spelling, two readings, decided by depth"
    // shape this ticket exists to remove, one connective further out. The descent now
    // reads the ONE slot table (`proved_goal_children`).
    for (label, body) in [
        ("under not", "not(42)"),
        ("in a bare or branch", "base(9) | 42"),
        ("mid-conjunction", "base(7), 42"),
        ("in a bounded quantifier's body", "(forall ?x in [1]: 42)"),
        ("in a discharge's consequent", "(forall(?x), base(?x) -: base(?x), 42)"),
    ] {
        let src = format!(
            "namespace j38jed{}\n  import anthill.prelude.List\n  rule base(7) :- true\n  \
             rule p(1) :- {body}\nend\n",
            body.len()
        );
        let errs = refusal(&src);
        assert!(
            errs.iter().any(|e| e.contains("42") && e.contains("GOAL position")),
            "a constant {label} must be refused too; got: {errs:?}"
        );
    }
}

#[test]
fn the_refusal_names_the_position_not_just_the_rule() {
    // A CONSTANT NAMES NOTHING TO CITE A RULE BY, so the SPAN is the whole diagnostic —
    // and the pass this refusal lives in is one of the late whole-KB passes, whose
    // errors are pushed UNTAGGED and render a bare byte offset. Two constants on the
    // same line, at different columns, in ONE file: if the location were not carried
    // through, both would render the same prefix (or none).
    //
    // BACKED OUT (drop the `Some(o.span.source)` tag at the call site): the messages
    // still name `42` and `99`, but render `… at 61..63` — no file, no line, no column.
    let errs = refusal(
        "namespace j38jee\n  rule base(7) :- true\n  rule p(1) :- 42\n  rule q(1) :- 99\nend\n",
    );
    let cols: Vec<&String> = errs.iter().filter(|e| e.contains("GOAL position")).collect();
    assert_eq!(cols.len(), 2, "one error per constant goal; got: {errs:?}");
    assert!(
        cols[0].starts_with("3:") && cols[1].starts_with("4:"),
        "each error must render `line:col` for ITS OWN constant, not a shared byte \
         offset; got: {cols:?}"
    );
}

#[test]
fn a_constant_in_a_value_position_is_untouched() {
    // THE CONTROL, and the one that decides whether the refusal is a POSITION rule or a
    // blanket ban on literals. Every row here puts a constant where a constant belongs —
    // a goal's ARGUMENT, an `eq` operand, a list element, an entity field — and all of
    // them must keep loading AND keep answering.
    //
    // Its own namespace, away from the refusal fixtures: a control that shared a file
    // with an arm would die of the arm's load error and prove nothing (the arms above
    // are each their own load for the same reason).
    //
    // PASSES EITHER WAY under the item-4 back-out, by design — a control measures what
    // the change must not touch.
    let mut kb = crate::common::load_kb_with(
        "namespace j38jef\n  import anthill.prelude.{Int64, List, String}\n  \
         sort Box\n    entity box(n: Int64)\n  end\n  \
         fact base(42)\n  \
         rule arg(1)  :- base(42)\n  \
         rule cmp(?x) :- ?x = 42\n  \
         rule lst(?l) :- ?l = [1, 2]\n  \
         rule fld(1)  :- base(?n), box(n: ?n) = box(n: 42)\nend\n",
    );
    assert_eq!(answers(&mut kb, "j38jef.arg(1)"), 1, "a constant ARGUMENT is data");
    assert_eq!(answers(&mut kb, "j38jef.cmp(?r)"), 1, "a constant `eq` operand is a value");
    assert_eq!(answers(&mut kb, "j38jef.lst(?r)"), 1, "a constant list element is a value");
    assert_eq!(answers(&mut kb, "j38jef.fld(1)"), 1, "a constant entity field is a value");
}

#[test]
fn the_boolean_constants_keep_their_reading() {
    // THE OTHER CONTROL, and the one that pins item 4's BOUNDARY: the refusal is over
    // "every constant EXCEPT the two booleans", so a `Bool` literal in each of the four
    // positions the row above refuses must still LOAD and still answer by the search
    // reading. Without this, narrowing the refusal's exemption to, say, top-level
    // `true` alone would go unmeasured.
    //
    // A CONTROL FOR ITEM 4 AND A DRIVER FOR THE READING — it passes either way under
    // the constant-refusal back-out, and FAILS under the goal-reading one (on `pneg`,
    // where `not(false)` answers 0 once `false` stops being a goal that fails). One row
    // can be both; what it must not be is silent about which change it measures.
    let mut kb = crate::common::load_kb_with(
        "namespace j38jeg\n  import anthill.prelude.{Bool, List}\n  rule base(7) :- true\n  \
         rule ptop(1)  :- true\n  \
         rule pneg(1)  :- not(false)\n  \
         rule pdis(1)  :- base(9) | true\n  \
         rule pcon(1)  :- base(7), true\n  \
         rule pqua(1)  :- (forall ?x in [1]: true)\n  \
         rule pqub(1)  :- (forall ?x in [1]: false)\nend\n",
    );
    // `p`-prefixed on purpose: a bare `neg` head collides with `Numeric.neg` (§6.6's
    // prefix operator) and the rule then answers NOTHING — measured, and it is what the
    // first draft of this row tripped over. The refusal under test has nothing to do
    // with it, which is exactly why the name must not be able to fake a failure.
    for (pred, want) in [("ptop", 1), ("pneg", 1), ("pdis", 1), ("pcon", 1), ("pqua", 1), ("pqub", 0)] {
        assert_eq!(
            answers(&mut kb, &format!("j38jeg.{pred}(1)")),
            want,
            "`{pred}`: a boolean constant at every position keeps the SEARCH reading, \
             not the refusal"
        );
    }
}

#[test]
fn what_the_condition_reading_cannot_yet_reduce() {
    // THE BOUND ON ITEM 1, pinned so that widening it is visible. Spec §5.3 says goal
    // position is CLOSED — a term with no reading is a load error — and two shapes are
    // deliberately still outside the refusal:
    //
    //  * A `const` REFERENCE (`:- flag`) loads and silently never matches. Withheld on
    //    purpose: there is no repair to point at, because a `const` does not fold
    //    ANYWHERE in a rule body — the second row here is the measurement, and it is the
    //    defect to fix before this one — WI-20260822-NDG34 owns it, and the same
    //    reference inside an OPERATION body folds correctly, so the split is eval-vs-SLD
    //    rather than value-vs-goal. Refusing the goal while the repair is also broken
    //    would only move the author's dead end.
    //  * A BOOL-RETURNING OPERATION CALL in goal position already evaluates, through
    //    WI-938's derived relational view at the operation's own arity — the reading
    //    item 1 settled, arriving by a mechanism this ticket did not write.
    //  * A HOST-BACKED OPERATION does not reduce here either — `Bool.and` / `or` / `not`
    //    are declared body-less in `prelude/bool.anthill` and their `<=>` laws are
    //    untagged, so they are inert in SLD. Same root as the `const` row: a rule body
    //    reduces a BODIED operation and a resolver BUILTIN, and nothing else
    //    (WI-20260822-ZJZS7). That is why `a & b` in a goal is still refused rather than
    //    admitted — a located error is the honest state of a reading the evaluator
    //    cannot deliver, and it is checked by `wi1046`'s own suite, not here.
    //  * A NON-BOOL DOT PROJECTION (`:- b.n`) now answers 0 rather than 1: it routes to
    //    `eq(b.n, true)`, and an `Int64` is not `true`. Correct as logic — a non-Bool
    //    expression denotes no truth — but SILENT, where its siblings (a non-Bool
    //    operation, a non-boolean constant) are located load errors. The refusal wants
    //    the field's declared type, which the typer stamps on the goal; not done here.
    //  * A DISCHARGE'S ANTECEDENT slot takes no constant reading either way. It is a
    //    hypothesis, not a goal the resolver proves — `SlotReading::Assumed`, which
    //    `proved_goal_children` deliberately filters out — so a constant written there
    //    is neither refused nor answered. Left alone rather than widened: an antecedent
    //    DECLARES the predicate its consequent proves against, which is why every walk
    //    that refuses a dead goal leaves the slot alone, and widening it would silently
    //    move WI-583's op check into a position nobody has legislated.
    //
    // Written to FAIL when any of them lands, which is the intent.
    let mut kb = crate::common::load_kb_with(
        "namespace j38jeh\n  import anthill.prelude.{Int64, Bool}\n  \
         const flag: Bool = true\n  const nn: Int64 = 5\n  \
         rule pconst(1) :- flag\n  \
         rule pfold(1)  :- Int64.gt(nn, 3)\n  \
         rule plit(1)   :- Int64.gt(5, 3)\n  \
         sort Box\n    entity box(n: Int64)\n    \
         operation isbig(b: Box) -> Bool = Int64.gt(1, 0)\n    \
         operation issmall(b: Box) -> Bool = Int64.gt(0, 1)\n    \
         operation bothbig(b: Box) -> Bool = Bool.and(Int64.gt(1, 0), Int64.gt(2, 1))\n  end\n  \
         rule pop(1)  :- Box.isbig(box(n: 5))\n  \
         rule pop2(1) :- Box.issmall(box(n: 5))\n  \
         rule pand(1) :- Bool.and(true, true) = true\n  \
         rule pandop(1) :- Box.bothbig(box(n: 5))\n  \
         rule pdotn(1)  :- box(n: 5).n\nend\n",
    );
    assert_eq!(answers(&mut kb, "j38jeh.pconst(1)"), 0, "a `const` goal: still silent");
    assert_eq!(answers(&mut kb, "j38jeh.pfold(1)"), 0, "…because a const folds NOWHERE here");
    assert_eq!(answers(&mut kb, "j38jeh.plit(1)"), 1, "CONTROL: the same call with the literal");
    assert_eq!(answers(&mut kb, "j38jeh.pop(1)"), 1, "a Bool operation call ALREADY evaluates");
    assert_eq!(answers(&mut kb, "j38jeh.pop2(1)"), 0, "…and is not vacuous");
    assert_eq!(
        answers(&mut kb, "j38jeh.pand(1)"),
        0,
        "a HOST-BACKED op does not reduce in a rule body: WI-20260822-ZJZS7"
    );
    assert_eq!(
        answers(&mut kb, "j38jeh.pandop(1)"),
        1,
        "CONTROL: the same conjunction through a BODIED operation, which does reduce"
    );
    assert_eq!(
        answers(&mut kb, "j38jeh.pdotn(1)"),
        0,
        "a NON-Bool dot projection: silently false where its siblings are load errors"
    );

    // The antecedent slot, in its own load — the refusal fires per FILE, so a fixture
    // that also carried a refused shape would report that instead and say nothing about
    // this one.
    let mut kb = crate::common::load_kb_with(
        "namespace j38jei\n  rule base(7) :- true\n  \
         rule pant(1) :- (forall(?x), 42 -: base(?x))\n  \
         rule plive(1) :- (forall(?x), base(?x) -: base(?x))\nend\n",
    );
    assert_eq!(answers(&mut kb, "j38jei.pant(1)"), 0, "a constant ANTECEDENT: still silent");
    assert_eq!(answers(&mut kb, "j38jei.plive(1)"), 1, "CONTROL: the discharge itself works");
}
