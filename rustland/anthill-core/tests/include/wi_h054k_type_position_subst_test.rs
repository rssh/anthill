//! WI-20260903-H054K — A RULE VARIABLE IN A TYPE POSITION OF A `[simp]` RHS IS
//! INSTANTIATED.
//!
//! ── THE DROP, AND WHY IT READ AS SILENCE ────────────────────────────────────
//!
//! A `[simp]` fire substitutes into the rule's RHS occurrence, and the TYPE positions of
//! that occurrence — `Expr::Apply`'s form-(3) `recv_type` (`Map[K = …].empty()`,
//! WI-20260829-W6JH0) and its `type_args` bracket — went through
//! `KnowledgeBase::apply_subst`, which is term-world and documents the drop at its own
//! site: "a non-`Term` carrier (a `Value::Node`) can't be a `Term` child, so a var bound
//! to one stays the var". The typer's fire binds EVERY rule variable to a `Value::Node`
//! (a redex's children ARE occurrences, WI-246), so the type position kept the throwaway
//! `fresh` global the equation had been opened against — and A FREE VARIABLE UNIFIES WITH
//! ANYTHING, so the check the author's bracket stands for could not fail. Not a
//! conservative no-op: a WRONG program loaded clean.
//!
//! WI-20260903-FCZ3N is what made it visible, by fixing its neighbour: keeping the
//! author's RHS occurrence took the GROUND spelling from 0 errors to 1, while the
//! VARIABLE spelling beside it stayed at 0.
//!
//! ── THE REPAIR, AND THE TWO QUESTIONS IT KEEPS APART ───────────────────────
//!
//! `SubstTypeRewrite::term` is now `node_occurrence::subst_type_term`: `apply_subst`'s OWN
//! `Fn` walk (`map_fn_children` — same structural sharing, same child order, same
//! hash-consing) with ONE arm changed. At a variable it reads σ through
//! `Substitution::resolve_as_value`, which sees EVERY carrier, and asks `type_denoted_by`
//! what TYPE the binding denotes; a binding that denotes none becomes `⊥`.
//!
//! **THE OBVIOUS COMPOSITION IS WRONG TWICE**, and both halves are measured rather than
//! argued — the KB already has a carrier-neutral σ (`KnowledgeBase::reify`) and an
//! occurrence→term boundary (`try_occurrence_to_term`), and routing the leaf through the
//! two of them is the natural repair:
//!
//!   1. `reify`'s answer for `Map[V = Int64, K = ?k]` with `?k ↦ Node(TypeValue{Bool})` is a
//!      `Value::Entity` — `fn_value` promotes any application with a non-leaf child — and a
//!      `Value::Entity` in a TYPE position is a carrier the type layer does not read:
//!      `resolved_type_is_ground_g`'s `_ => false` calls it non-ground, so
//!      `validate_arg_against_param` SKIPS the check. THE HEADLINE ROW STAYS AT ZERO.
//!      Delivering the binding on a carrier every reader skips only MOVES the drop.
//!   2. `try_occurrence_to_term` answers "does this have a GOAL-TERM shape", which is
//!      strictly WIDER than "does this denote a TYPE" — so four of row E's five bindings
//!      arrived as ground PSEUDO-TYPES and were checked and named. See that row.
//!
//! ── WHAT THE HEADLINE DOES NOT CLAIM ───────────────────────────────────────
//!
//! An UNBOUND type-position variable still keeps its variable, and that is not the same
//! defect wearing a hat. In a VALUE position an unbound rule variable leaves the RHS with
//! nothing to splice, which is why `simp_rewrite::bottom_out_unbound` writes `⊥` there; in a
//! TYPE position it is the spelling for an UNCONSTRAINED slot, and §"Expansion during
//! unification" makes `Map[K = ?]`, `Map[K = ?k]` with `?k` used once, and omitting the
//! binding altogether "all mean the same thing and … checked alike". MEASURED, all three
//! GROUND spellings loading clean — so the rule spelling loading clean is AGREEMENT with its
//! ground twin. Raised by `/code-review` as a gap and declined on that measurement; the
//! reason is recorded at the arm so it is not re-raised from the symmetry alone.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ───────────────────────────
//!
//! **AXIS 1 — READING σ CARRIER-NEUTRALLY.** `subst_type_term`'s variable arm narrowed back
//! to `Some(Value::Term { id, .. }) => id, _ => t`, which is `apply_subst` verbatim.
//! **EXACTLY 4 ROWS FAIL of 4 084** over the whole `wi_tests` binary, all four in this file:
//! [`a_type_position_variable_is_instantiated_from_the_match`] (both its spellings),
//! [`a_value_in_type_binding_is_the_value_it_denotes`],
//! [`a_binding_that_denotes_no_type_is_bottom_and_says_so`], and
//! [`every_writable_type_agrees_with_its_ground_twin`].
//!
//! **AXIS 2 — ASKING THE TYPE QUESTION AND NOT THE GOAL QUESTION.**
//! `type_denoted_by_occurrence`'s body replaced by a bare `try_occurrence_to_term`. **2 ROWS
//! FAIL** — the `⊥` row on four of its five shapes, and the agreement row on its tuples,
//! whose reflect `TupleLiteral` twin is a different term from the type the loader builds. The
//! two axes are separate and neither subsumes the other: axis 1 is about SEEING the binding
//! at all, axis 2 about what question to ask of it once seen, and the four rows that survive
//! axis 2 are what says so.
//!
//! GREEN under both back-outs, each by design and each for its own reason:
//! [`the_yardsticks_are_unmoved`] (the ground and direct spellings the headline is read
//! against, plus the un-fired rule — none has a type-position variable);
//! [`the_matching_key_is_accepted_and_computes`] (0 errors either way, because loading clean
//! was the defect); and [`the_type_args_bracket_channel_is_refused_at_load`], which pins a
//! NEIGHBOUR and is about the LOADER.
//!
//! **THE WRONG FIX**, measured rather than argued. The ticket's other candidate answer was
//! to REFUSE at the fire when the binding "is not representable" in a type position, read as
//! "is not already a `Value::Term`". Implemented — `type_denoted_by_occurrence` answering
//! `None` for every `Value::Node` — **5 ROWS FAIL**, and which they are is the whole point:
//!
//!   * [`the_matching_key_is_accepted_and_computes`] goes 0 → **1**, a FALSE refusal
//!     (`expected bottom, got String`) of a program whose key type is exactly right, and
//!     [`every_writable_type_agrees_with_its_ground_twin`] the same for every shape at once.
//!     Those are the rows whose VERDICT — accept versus refuse — separates the two answers.
//!   * the headline row and [`a_value_in_type_binding_is_the_value_it_denotes`] fail on their
//!     SENTENCE, not their count: a `⊥` key rejects a `String` too, so both still answer 1,
//!     and only `expected Bool` / `expected 7` against `expected bottom` tells the two apart.
//!     That is why those rows assert the message and not just the number.
//!   * [`a_binding_that_denotes_no_type_is_bottom_and_says_so`] fails on its CONTROL alone —
//!     its five `⊥` shapes are `⊥` under the wrong fix too, but the type PARAMETER beside
//!     them stops being deferred and is refused.
//!
//! ── THE CHANNELS, CENSUSED ──────────────────────────────────────────────────
//!
//! A type position reaches the fixed leaf ([`SubstTypeRewrite`]) down THREE channels, and
//! only one of them is drivable from a `[simp]` RHS today:
//!
//!   * `Expr::Apply.recv_type` — the form-(3) companion receiver. DRIVEN, by every row
//!     below.
//!   * `Expr::Apply.type_args` — the call-site bracket. NOT DRIVEN, and not for want of
//!     trying: a `[simp]` RHS cannot carry one at all (refused at load, MEASURED — the
//!     bracket is read only on an applicative call in an OPERATION BODY, WI-20260829-BAD3V).
//!     [`the_type_args_bracket_channel_is_refused_at_load`] pins that refusal, so the day
//!     the bracket gains a channel here this file goes red and asks for a row.
//!   * the `TypeNode` / `EffectExpr` spine (`map_type_child`). NOT DRIVEN — WI-378's own
//!     note says no producer mints a σ-substitutable var on that spine today ("denoteds
//!     are `Ref`/`Const`, type-vars stay ground `TypeChild::Ground`"), and this ticket did
//!     not find one either. It shares the leaf, so it moves with the other two.

use anthill_core::eval::Value;

/// The shared skeleton. `Map` is the carrier because its `K` is what a form-(3) receiver
/// can pin and what `put`'s `key` parameter is then checked against — the shortest program
/// in which a type-position binding decides an ARGUMENT.
///
/// ONE skeleton for every row on purpose (WI-20260902-4NEKZ's lesson): the rows quote each
/// other's messages, so a forked copy would let an edit move a message under an assertion
/// taken on a different program.
fn program(extra: &str) -> String {
    format!(
        "namespace zzh\n  import anthill.prelude.Int64\n  import anthill.prelude.Bool\n  \
         import anthill.prelude.String\n  import anthill.prelude.List\n  \
         import anthill.prelude.Map\n  \
         import anthill.prelude.Map.{{empty, put, size}}\n\
{extra}end\n"
    )
}

fn errs(extra: &str) -> Vec<String> {
    crate::common::try_load_kb_with(&program(extra))
        .err()
        .unwrap_or_default()
}

/// A load error with its `line:col` prefix stripped, so two spellings of ONE mistake can be
/// compared by what they SAY without asserting that they are written in the same place.
fn sentence(msg: &str) -> &str {
    msg.split_once(": ").map_or(msg, |(_, rest)| rest)
}

/// The receiver whose `K` disagrees with the `"a"` the driver passes, written as a rule
/// VARIABLE the fire has to instantiate. `mkv(Bool)` supplies the type at the redex.
const VARIABLE_WRONG: &str = "  rule mkv(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
                              operation dv() -> Int64 = size(put(mkv(Bool), \"a\", 1))\n";

/// The same receiver written GROUND — WI-20260903-FCZ3N's own gain, and the yardstick the
/// headline row is read against.
const GROUND_WRONG: &str = "  rule mkg(?x) <=> Map[K = Bool, V = Int64].empty() [simp]\n  \
                            operation dg() -> Int64 = size(put(mkg(1), \"a\", 1))\n";

/// And the same call written directly in an operation body, with no rule in it at all.
const DIRECT_WRONG: &str =
    "  operation dd() -> Int64 = size(put(Map[K = Bool, V = Int64].empty(), \"a\", 1))\n";

/// **A — THE HEADLINE.** The variable spelling reports the mismatch, and reports it in the
/// SAME SENTENCE the two spellings that always worked report it in.
///
/// Both halves are asserted because a repair could deliver either alone: a count of 1 with
/// a different sentence would mean the type came out as something else that also rejects a
/// `String` (which is exactly what the wrong fix does — `expected bottom`), and the
/// sentence alone says nothing about whether a second diagnosis was invented.
///
/// The SECOND spelling fires one `[simp]` rule out of another, so the instantiated type has
/// to survive a rewrite of a rewrite; it answers identically.
///
/// RED under either back-out: 0 errors, on both spellings — a wrong program loading clean.
#[test]
fn a_type_position_variable_is_instantiated_from_the_match() {
    let expected = {
        let d = errs(DIRECT_WRONG);
        assert_eq!(d.len(), 1, "the direct spelling is the yardstick: {d:#?}");
        sentence(&d[0]).to_owned()
    };
    assert_eq!(
        expected, "type mismatch in put.key (op-arg): expected Bool, got String",
        "the yardstick's own wording, spelled out so a change to it is visible here"
    );

    for (label, extra) in [
        ("one fire", VARIABLE_WRONG),
        (
            "a fire whose RHS is itself a redex",
            "  rule mka(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
             rule mkb(?j) <=> mka(?j) [simp]\n  \
             operation dc() -> Int64 = size(put(mkb(Bool), \"a\", 1))\n",
        ),
    ] {
        let e = errs(extra);
        assert_eq!(
            e.len(),
            1,
            "{label}: `?k` is bound to `Bool` by the match, so the receiver claims a \
             `Bool` key and `\"a\"` is not one — it was ZERO, the variable having stayed \
             the equation's own `fresh` global, which unifies with anything: {e:#?}"
        );
        assert_eq!(
            sentence(&e[0]),
            expected,
            "{label}: …and it is the SAME diagnosis the direct spelling gives, not merely \
             some diagnosis: {:?}",
            e[0]
        );
    }
}

/// **B — THE YARDSTICKS, UNMOVED.** Each is a way row A could have been green for the
/// wrong reason.
///
/// GREEN UNDER BOTH BACK-OUTS, all three, BY DESIGN — that is what makes them yardsticks.
/// The ground receiver and the direct call have no type-position VARIABLE, so this
/// ticket's leaf has nothing to instantiate in either; the un-fired rule says the
/// diagnosis comes from the FIRE and not from loading the rule.
#[test]
fn the_yardsticks_are_unmoved() {
    for (label, extra, expected) in [
        (
            "the GROUND receiver in a fired `[simp]` RHS",
            GROUND_WRONG,
            1,
        ),
        (
            "the same call written directly in an operation body",
            DIRECT_WRONG,
            1,
        ),
        (
            "the variable rule with NO consumer never fires",
            "  rule mkn(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n",
            0,
        ),
    ] {
        let e = errs(extra);
        assert_eq!(e.len(), expected, "{label}: {e:#?}");
    }
}

/// **C — THE MATCHING KEY IS ACCEPTED, AND THE PROGRAM COMPUTES.** The row that says this
/// ticket INSTANTIATES a type-position variable rather than merely poisoning it, and the
/// only row that separates the answer taken from the one refused.
///
/// GREEN UNDER BOTH BACK-OUTS (0 errors before this ticket too — everything loaded clean,
/// which was the defect) and RED UNDER THE WRONG FIX: lowering every `Value::Node` binding
/// to `⊥` instead of to the type it denotes makes this answer **1**, `expected bottom, got
/// String`, on a program whose key type is exactly what the author asked for. MEASURED.
/// Row A cannot make that distinction — a `⊥` key rejects a `String` too, so it answers 1
/// under both.
///
/// AND IT IS DRIVEN, not merely accepted: `dr()` evaluates to `Int(1)`, so the
/// instantiated receiver reaches a running `put`/`size` rather than only a typer that
/// stopped objecting.
#[test]
fn the_matching_key_is_accepted_and_computes() {
    const RIGHT: &str = "  rule mkr(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
                         operation dr() -> Int64 = size(put(mkr(String), \"a\", 1))\n";
    assert!(
        errs(RIGHT).is_empty(),
        "`?k` is bound to `String`, which is what `\"a\"` is — a CORRECT program must not \
         be refused: {:#?}",
        errs(RIGHT)
    );

    // THE CONTROL BESIDE IT: the same rule with the key written GROUND. Without it, "0
    // errors" here could mean the whole check stopped firing rather than passing.
    assert!(
        errs(
            "  rule mkgr(?x) <=> Map[K = String, V = Int64].empty() [simp]\n  \
              operation dgr() -> Int64 = size(put(mkgr(1), \"a\", 1))\n"
        )
        .is_empty(),
        "the ground twin of the accepted program must also load clean"
    );

    let mut interp = crate::common::interp_for(&program(RIGHT));
    let got = interp
        .call("zzh.dr", &[])
        .unwrap_or_else(|e| panic!("dr() must evaluate: {e:?}"));
    assert!(
        matches!(got, Value::Int(1)),
        "one `put` into an `empty()` whose receiver type came from a fired `[simp]` rule \
         has size 1 — got {got:?}"
    );
}

/// **D — A VALUE-IN-TYPE BINDING IS THE VALUE IT DENOTES, NOT `⊥`.** A literal reaches
/// type position as a `denoted` (§4.5 — `Vector[Int64, 3]`; there are no singleton types),
/// so a redex supplying `7` where the rule writes `Map[K = ?k]` asks for the key type `7`,
/// and the lowering must SAY SO rather than collapse it.
///
/// The row exists because `⊥` is the easy answer for every carrier that is not already a
/// term, and it would be wrong for this one: the whole point of reading σ carrier-neutrally
/// is that the binding is KNOWN at the fire, so what is known must be reported.
///
/// RED under either back-out (0 errors — the nonsense key silently unified with `String`)
/// and RED under the wrong fix, which reports `expected bottom` here instead of `expected
/// 7`, which is why the message and not only the count is asserted.
#[test]
fn a_value_in_type_binding_is_the_value_it_denotes() {
    const EXTRA: &str = "  rule mkb(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
                         operation db() -> Int64 = size(put(mkb(7), \"a\", 1))\n";
    let e = errs(EXTRA);
    assert_eq!(
        e.len(),
        1,
        "`Map[K = 7]` is not a map a `String` keys: {e:#?}"
    );
    assert_eq!(
        sentence(&e[0]),
        "type mismatch in put.key (op-arg): expected 7, got String",
        "…and the key it names is the LITERAL the redex supplied, not a `⊥` standing in \
         for one: {:?}",
        e[0]
    );
}

/// **E — AND A BINDING THAT DENOTES NO TYPE IS `⊥`, LOUDLY, WHATEVER SHAPE IT HAS.**
/// `Map[K = <a value-world expression>]` cannot be expressed in the carrier a type position
/// is read on, so the leaf writes `⊥` there — the same word
/// `simp_rewrite::bottom_out_unbound` writes one call out for the neighbouring "this
/// instantiation has no value to put here" — which is GROUND (`type_value_is_ground_g`), so
/// it is CHECKED and reported.
///
/// KEEPING THE CARRIER INSTEAD WOULD BE A SILENT SKIP, which is this ticket's own defect
/// wearing a different carrier: the type layer's groundness gate answers "cannot read" for
/// anything but a term or a `Node` type, and there that answer means SKIP THE CHECK.
///
/// **FIVE SHAPES, NOT ONE, AND THAT IS THE ROW'S POINT.** The first cut of this ticket
/// lowered a `Value::Node` binding through `try_occurrence_to_term` — the occurrence→GOAL
/// TERM boundary — which answers a strictly WIDER question than "does this denote a type".
/// A lambda has no goal shape and came out `⊥` correctly; the other four have perfectly
/// good goal terms and came out as ground PSEUDO-TYPES that were then checked and NAMED
/// (`expected idk`, `expected var_ref[name = s]`, `expected ListLiteral`, `expected
/// empty`), two of them leaking the internal reflect encoding into a user-facing message
/// and all four naming a type the author never wrote. All five load clean BEFORE this
/// ticket, so a fixture written from the lambda alone would have shipped the other four.
/// Found by `/code-review`, which built three of them; `node_occurrence::type_denoted_by`
/// is the gate that asks the type question instead.
///
/// RED under axis 1 (0 errors, every shape) and under axis 2 (four of the five report the
/// pseudo-type instead). The `bottom` in the message is this ticket's too:
/// `type_display_name` had no `Term::Bottom` arm and rendered it `TermId(3485)`.
///
/// THESE FIVE ARE THE ONLY `⊥`s THE WORKSPACE PRODUCES — censused at the arm itself, through
/// a file the test harness cannot capture. An `eprintln!` there reads ZERO, because libtest
/// swallows a test's stderr, and the first cut of this census did exactly that and believed
/// it; the file probe reads **5 hits across 36 binaries and 6 376 tests**, and all five are
/// this row's. That is also the population argument for axis 2: no row anywhere else can
/// move under it.
#[test]
fn a_binding_that_denotes_no_type_is_bottom_and_says_so() {
    for (label, redex_arg, decl) in [
        (
            "a LAMBDA — no goal-term shape either",
            "lambda (x) -> x",
            "",
        ),
        (
            "an operation CALL — a goal term, and not a type",
            "idk(\"z\")",
            "  operation idk(x: String) -> String = x\n",
        ),
        ("a LIST LITERAL", "[1, 2]", ""),
        (
            "a form-(3) CALL, whose goal term drops the receiver as well",
            "Map[K = Bool, V = Int64].empty()",
            "",
        ),
    ] {
        let extra = format!(
            "{decl}  rule mkl(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
             operation dl() -> Int64 = size(put(mkl({redex_arg}), \"a\", 1))\n"
        );
        let e = errs(&extra);
        assert_eq!(
            e.len(),
            1,
            "{label}: it denotes no type, so the key type is `⊥` and `\"a\"` is not one — \
             it must not load clean: {e:#?}"
        );
        assert_eq!(
            sentence(&e[0]),
            "type mismatch in put.key (op-arg): expected bottom, got String",
            "{label}: …and the answer is `⊥`, NOT the term the goal-lowering happens to \
             have for it — the `Map[K = …]` a diagnostic names must be a type the author \
             could have written: {:?}",
            e[0]
        );
    }

    // A VALUE PARAMETER, which needs the driver to take one — the shape whose
    // goal-lowering leaked `var_ref[name = s]`, the reflect encoding, into the message.
    let e = errs(
        "  rule mkp(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
                  operation dp(s: String) -> Int64 = size(put(mkp(s), \"a\", 1))\n",
    );
    assert_eq!(e.len(), 1, "a value parameter denotes no type: {e:#?}");
    assert_eq!(
        sentence(&e[0]),
        "type mismatch in put.key (op-arg): expected bottom, got String",
        "…and says so without naming `var_ref`: {:?}",
        e[0]
    );

    // THE CONTROL that stops this row from reading as "every binding is `⊥` now": a TYPE
    // PARAMETER is a type, and one still leaves the call UNDECIDED rather than refused —
    // `Ref(K)` is a sort-param symbol, so the gate reads it as non-ground and defers, which
    // is what a polymorphic position must do. GREEN under both back-outs and under the
    // first cut too; it is here because `⊥` is the aggressive answer and this bounds it.
    assert!(
        errs(
            "  rule mkq(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
              operation dq[K]() -> Int64 = size(put(mkq(K), \"a\", 1))\n"
        )
        .is_empty(),
        "a type PARAMETER in the type position is a type, and an undetermined one — the \
         call must be left to dispatch, not refused"
    );
}

/// **G — EVERY TYPE AN AUTHOR CAN WRITE AGREES WITH ITS GROUND TWIN.** The rows above all
/// send a NOMINAL sort through the variable, and a gate that reads only nominal types would
/// pass every one of them while falsely refusing everything else. This is the row that
/// censuses the shapes instead of trusting the fixture: for each type, the SAME correct
/// program is written twice — once with the receiver ground, once through the rule variable
/// — and the two must answer alike.
///
/// **IT FOUND A FALSE REFUSAL, which is why it is a row and not a remark.** A tuple type
/// reached through the variable answered `expected bottom, got (_1: Int64, _2: Bool)` on a
/// program whose key type is exactly right, while its ground twin loaded clean — the very
/// failure this file calls THE WRONG FIX, introduced by the first cut of the fix itself. The
/// cause is that a STRUCTURAL type has no nominal name to be classified by, so it does not
/// arrive as proposal 055's `Expr::TypeValue`; it arrives as the tuple it is spelled as, and
/// `node_occurrence::tuple_type_denoted` is the arm that reads it. `/code-review` found the
/// positional tuple; this census found the named and the nested one beside it.
///
/// **THE ARROW IS THE ONE DISAGREEMENT LEFT, and it is not this leaf's.** `(Int64) -> Bool`
/// written at the redex's VALUE position is refused by the PARSER — "`->` in expression
/// position builds an arrow-type term, not a function value" — so it never reaches σ at all.
/// Asserted here rather than narrated, so that if a value-position arrow ever becomes
/// writable this row asks for the measurement instead of silently starting to pass.
///
/// RED under axis 1 and axis 2 on the tuple entries (they were `⊥` under both, and 0 errors
/// before this ticket); the nominal entries are green throughout, which is what makes them
/// the controls for the tuple ones.
#[test]
fn every_writable_type_agrees_with_its_ground_twin() {
    for (label, ty, key_value) in [
        ("a nominal sort", "Bool", "true"),
        ("a PARAMETERIZED sort", "List[T = Int64]", "[1]"),
        ("a POSITIONAL tuple type", "(Int64, Bool)", "(1, true)"),
        (
            "a NAMED tuple type",
            "(a: Int64, b: Bool)",
            "(a: 1, b: true)",
        ),
        (
            "a NESTED tuple type",
            "((Int64, Bool), String)",
            "((1, true), \"s\")",
        ),
    ] {
        let ground = errs(&format!(
            "  rule mkg(?x) <=> Map[K = {ty}, V = Int64].empty() [simp]\n  \
             operation dg() -> Int64 = size(put(mkg(1), {key_value}, 1))\n"
        ));
        let variable = errs(&format!(
            "  rule mkv(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
             operation dv() -> Int64 = size(put(mkv({ty}), {key_value}, 1))\n"
        ));
        assert!(
            ground.is_empty(),
            "{label}: the fixture must be a CORRECT program — its GROUND spelling is the \
             yardstick and it must load clean, else this row measures nothing: {ground:#?}"
        );
        assert!(
            variable.is_empty(),
            "{label}: …and reaching the same type through a rule variable must not refuse \
             it. A type the gate cannot read becomes `⊥`, which is GROUND and so is CHECKED \
             — a FALSE REFUSAL of a right program, the thing this file calls the wrong \
             fix: {variable:#?}"
        );
    }

    // AND THE MISMATCH IS STILL REPORTED THROUGH A STRUCTURAL TYPE — otherwise "agrees with
    // its ground twin" could be bought by making the whole check stop firing.
    let e = errs(
        "  rule mkt(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
                  operation dt() -> Int64 = size(put(mkt((Int64, Bool)), \"a\", 1))\n",
    );
    assert_eq!(e.len(), 1, "a String is not a `(Int64, Bool)` key: {e:#?}");
    assert_eq!(
        sentence(&e[0]),
        "type mismatch in put.key (op-arg): expected (_1: Int64, _2: Bool), got String",
        "…and the tuple type is NAMED, not `bottom`: {:?}",
        e[0]
    );

    // THE ARROW, whose disagreement is the PARSER's. Pinned so the day it becomes writable
    // this row asks for a measurement rather than quietly starting to pass.
    let arrow = errs(
        "  rule mka(?k) <=> Map[K = ?k, V = Int64].empty() [simp]\n  \
                      operation da() -> Int64 = \
                      size(put(mka((Int64) -> Bool), lambda (x) -> true, 1))\n",
    );
    assert!(
        arrow
            .iter()
            .any(|m| m.contains("in expression position builds an arrow-type term")),
        "an arrow written at the redex's VALUE position is refused by the parser, so no \
         binding reaches σ — if that changes, this leaf needs an arrow measurement: {arrow:#?}"
    );
}

/// **F — THE SECOND CHANNEL IS REFUSED BEFORE IT REACHES THE LEAF.** `Expr::Apply` carries
/// TWO type positions through the same [`SubstTypeRewrite`] leaf — `recv_type`, which every
/// row above drives, and the call-site `type_args` bracket, which no row drives.
///
/// NOT AN OVERSIGHT, and this row is what says so instead of a sentence claiming it: a
/// `[simp]` RHS cannot carry a bracket at all. The refusal is asserted rather than
/// narrated, so the day that bracket gains a channel here this row goes red and asks
/// whoever opens it to add the missing measurement.
///
/// GREEN UNDER BOTH BACK-OUTS and under the wrong fix — it is about the LOADER, not about
/// σ. That is the point: it bounds this file's claim rather than supporting it.
#[test]
fn the_type_args_bracket_channel_is_refused_at_load() {
    let e = errs(
        "  operation idt[T](v: T) -> T = v\n  \
                  rule mkt(?k) <=> idt[T = ?k](1) [simp]\n  \
                  operation dt() -> Int64 = mkt(Bool)\n",
    );
    assert_eq!(
        e.len(),
        1,
        "a call-site type-argument bracket in a `[simp]` RHS is refused at load: {e:#?}"
    );
    assert!(
        e[0].contains("call-site type arguments") && e[0].contains("are not supported here"),
        "…by WI-20260829-BAD3V's own message, which is why `subst_type_args` has no row \
         in this file: {:?}",
        e[0]
    );
}
