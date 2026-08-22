//! WI-1046 — the boolean operators are position-directed IN FACT, not just in the spec.
//!
//! `docs/kernel-language.md` §6.6 (WI-529) states the design verbatim: *"`not`, `or`,
//! and `and` each name a dispatched value operation on `Bool` … inside an operation
//! body (evaluated), but a goal form in a rule body (resolved) … **Resolution is by
//! syntactic position**, not by a distinct glyph or operand type."*
//!
//! It was not. WI-529 routed ONE direction with a redirect (`kernel.not` → `Bool.not`
//! inside an op body) and left the rule-body direction to the implicit-prelude
//! FALLBACK — which sits BELOW scope resolution, so any name in scope shadows it. An
//! ordinary `import anthill.prelude.Bool` therefore repointed `not` and `|` in every
//! rule body of that namespace at the VALUE operations, which have no resolver
//! behaviour at all.
//!
//! ## MEASURED before the fix — one import, five rows
//!
//! | rule body | expected | no import | with `import anthill.prelude.Bool` |
//! |---|---|---|---|
//! | `l(?x) \| r(?x)` | 2 | 2 | **0** |
//! | `l(?x), r(?x)` (control) | 1 | 1 | 1 |
//! | `l(?x), not(empty(?x))` | 1 | 1 | **0** |
//! | `l(?x), not(r(?x))` | 0 | 0 | 0 |
//! | `l(?x) & r(?x)` | — | **0** | **0** |
//!
//! The `not` row is a WRONG ANSWER, not a missing one: negation-as-failure over a goal
//! that fails must SUCCEED. The fourth row is why the third is the one to drive — it
//! reads 0 under the defect and 0 when correct, so a suite that only checked it would
//! have measured nothing.
//!
//! The comma control is what proves the import is not simply breaking the fixture.
//!
//! ## Two halves, two remedies
//!
//! **`not` / `or` are ROUTED.** `Loader::route_body_goal_boolean` is the mirror of
//! WI-529's `redirect_op_body_boolean`, applied at GOAL POSITIONS — the flag
//! `in_body_goal` rides from each top-level body atom down through the goal slots of
//! whatever connectives sit above, and turns off at every data slot. Which slots those
//! are comes from the one shared table, `KnowledgeBase::goal_arg_slots`, that the two
//! KB goal walks read (WI-863 / WI-1034); the loader needs the answer while it is still
//! BUILDING the body, so it cannot ask either walk, and a third hand-written copy is
//! how the WI-1034 review found `and` listed as a conjunction in two of them.
//!
//! **`and` IS ROUTED TOO — since WI-20260822-J38JE.** It was REFUSED here, on the
//! ground that "there is nothing to route it to: §6.6 says goal conjunction is the
//! comma (there is no `kernel.and`)". That sentence described a MISSING PRIMITIVE as a
//! rule about the language — `not` and `or` each had one and `and` did not.
//! `anthill.kernel.and`, over the `push_and` conjunction primitive, supplies it. The
//! two rows below that asserted the refusal now assert ANSWERS, and the program this
//! file measured answering 0 answers what the comma answers.
//!
//! ## Blast radius: ZERO, measured over the corpus
//!
//! `Bool.and` / `Bool.or` / `Bool.not` appear in **no** rule-body goal position across
//! stdlib + rust bindings, + anthill-testcases, + examples and + anthill-todo. The
//! probe's CONTROL is that in the same walk `anthill.kernel.not` appears 3–4 times and
//! `anthill.kernel.push_choice` once — so it was looking in the right places and the
//! zero is a real zero. Nothing in the tree was relying on either behaviour.
//!
//! ## What fails per half — MEASURED by backing each one out
//!
//! Three pieces ship here, so three columns. "position-blind" is the flag threading
//! defeated — every rule-body node treated as a goal, which is the obvious shortcut.
//!
//! | test | routing | `and` refusal | position-blind |
//! |---|---|---|---|
//! | `an_imported_bool_no_longer_captures_negation` | **FAILS** | ok | ok |
//! | `an_imported_bool_no_longer_captures_disjunction` | **FAILS** | ok | ok |
//! | `the_routing_reaches_a_nested_connective` | **FAILS** | ok | ok |
//! | `a_goal_position_and_is_the_conjunction` | ok | — | ok |
//! | `the_equals_versus_ampersand_precedence_trap_is_a_silent_zero` | ok | — | ok |
//! | `a_data_slot_keeps_the_value_operators` | ok | ok | **FAILS** |
//! | `an_operation_body_still_evaluates_the_value_operators` | ok | ok | ok |
//!
//! The `and` refusal COLUMN IS RETIRED (the two rows that carried it now assert
//! answers); its back-out today is "make `push_and` unreachable", under which both of
//! them fail. Only the last row passes on all three, and it earns its place by guarding
//! the other direction entirely (WI-529's half, which this must not disturb). Note especially
//! that `a_data_slot_keeps_the_value_operators` is green under both real back-outs and
//! red only under the shortcut — a suite without it would report "all green" for a fix
//! that refuses every `and` a rule body mentions, data slots included.
//!
//! Outside this file, `wi1034_…::a_boolean_and_in_a_goal_position_is_refused_by_wi1046`
//! is the row WI-1034 pinned and handed here (it fails on the `and` column), and
//! `wi529_boolean_operator_split_test` owns the op-body direction this one mirrors.
//!
//! ## Three more the `/code-review` pass found, each DRIVEN before it was believed
//!
//! The last three tests in this file are theirs, and none had coverage before:
//!
//!   * the wrapper bit was keyed on `local_name == "tuple"` at any goal node, so a
//!     USER predicate named `tuple` had its DATA arguments walked as goals — refused
//!     where the identically-shaped `ordinary1046(?a & ?b)` loaded. It now rides a
//!     second flag set only by arriving through a `tuple_wrapped` SLOT.
//!   * folding `forall_impl` into the shared table silently changed the QUERY walk,
//!     which had never entered a discharge. A nested implication IS a query surface
//!     form (WI-863's doc said otherwise, and that doc is corrected), so
//!     `not((forall(?h), hyp(?h) -: hyp(?h)))` began refusing a name the pattern
//!     declares. The table stays honest; the DESCENT POLICY went back to the caller.
//!   * the redirect keyed on symbol identity alone, so it captured the arity-2
//!     RELATIONAL form `Bool.not(?a, ?r)` (WI-938) and rewrote it to the arity-1 NAF
//!     builtin, which then succeeded VACUOUSLY — 1 solution, `?r` unbound, reported
//!     DEFINITE. It is gated on arity now.
//!
//! A FOURTH finding was REFUTED by driving, and the measurement is worth keeping: in a
//! prelude-less KB (the embedder configuration) the `and` refusal cannot fire, because
//! `Bool.and` is not there to key on — but the construct is NOT silently dead, it is
//! refused by WI-1034's check instead ("rule-body goal `and` names nothing"), since the
//! operator bare-interns. Two checks, one loud outcome either way.
//!
//! The third is the one to note for how it was assessed: the pre-change answer was 0
//! solutions and the post-change answer was 1, so a count-only reading said the change
//! HELPED. Rendering the binding is what showed the 1 was fabricated.
//!
//! REFERENCE: WI-529 (the op-body half and the mechanism); WI-1034 (which found this);
//! `docs/kernel-language.md` §6.6; `stdlib/anthill/kernel/kernel.anthill:48`.

/// The five-row fixture, parameterized on whether `anthill.prelude.Bool` is imported.
/// One builder so the two arms cannot drift into two programs.
///
/// `right1046` CARRIES A ROW `left1046` DOES NOT (WI-FFPGD). The `pipe` row's job is to
/// show the disjunction enumerating BOTH arms, and it used to do that with a count of 2
/// over two arms that both answered `?x = 1` — one answer, reached twice. Answer dedup
/// now collapses that pair, so the row would have read 1 whether the right arm ran or
/// not. The extra `right1046(2)` restores the discrimination in the form that survives
/// dedup: the answer `2` can ONLY come from the right arm. The other three rows are
/// unmoved — `comma`/`nafTrue`/`nafFalse` all pivot on `?x = 1`, which both relations
/// still hold — so the whole table stays `[2, 1, 1, 0]`.
fn program(ns: &str, import_bool: bool) -> String {
    let imp = if import_bool {
        "  import anthill.prelude.Bool\n"
    } else {
        ""
    };
    format!(
        "namespace {ns}\n{imp}\
         \x20 fact left1046(1)\n\
         \x20 fact right1046(1)\n\
         \x20 fact right1046(2)\n\
         \x20 fact empty1046(99)\n\
         \x20 rule pipe1046(?x) :- left1046(?x) | right1046(?x)\n\
         \x20 rule comma1046(?x) :- left1046(?x), right1046(?x)\n\
         \x20 rule nafTrue1046(?x) :- left1046(?x), not(empty1046(?x))\n\
         \x20 rule nafFalse1046(?x) :- left1046(?x), not(right1046(?x))\n\
         end\n"
    )
}

/// Solution counts for the fixture's four rules, in table order.
fn counts(ns: &str, import_bool: bool) -> Vec<usize> {
    let mut kb = crate::common::load_kb_with(&program(ns, import_bool));
    ["pipe1046", "comma1046", "nafTrue1046", "nafFalse1046"]
        .iter()
        .map(|h| crate::common::query_unary(&mut kb, &format!("{ns}.{h}")).len())
        .collect()
}

/// THE HEADLINE, negation half. `not(g)` in a rule body is negation-as-failure whatever
/// is imported. Driven on the row that DISCRIMINATES: the negand FAILS, so NAF must
/// succeed and the rule must answer — the defect turned that 1 into 0, a wrong answer.
///
/// The `nafFalse` row is asserted beside it deliberately: it reads 0 both when NAF works
/// and when `not` has been captured, so it is the row that would have made a
/// too-narrow suite green through the whole defect.
#[test]
fn an_imported_bool_no_longer_captures_negation() {
    let with_import = counts("test.wi1046.naf.imported", true);
    assert_eq!(
        with_import[2], 1,
        "NAF over a failing goal must SUCCEED: {with_import:?}"
    );
    assert_eq!(
        with_import[3], 0,
        "NAF over a holding goal must FAIL: {with_import:?}"
    );
}

/// THE HEADLINE, disjunction half — and the strongest form of the claim: the two arms
/// must be EQUAL, so an import cannot change what a rule body means at all.
///
/// Compared as whole rows rather than per-row constants: what WI-1046 restores is the
/// spec's "resolution is by syntactic position", and a position-directed reading is
/// exactly one that does not vary with the import list. The comma row rides along as
/// the control — it never routed, so a difference there would mean the fixture, not the
/// routing, is what moved.
#[test]
fn an_imported_bool_no_longer_captures_disjunction() {
    let without = counts("test.wi1046.disj.plain", false);
    let with = counts("test.wi1046.disj.imported", true);
    assert_eq!(
        without,
        vec![2, 1, 1, 0],
        "the un-imported baseline: {without:?}"
    );
    assert_eq!(
        without, with,
        "an import must not change what a rule body MEANS — that is what \
         `position-directed` says (§6.6): {without:?} vs {with:?}",
    );
}

/// The routing reaches a connective NESTED under another, which is what makes it a
/// walk rather than a top-level special case. `not(a | b)` needs BOTH: the `not` routed
/// so the negation is entered at all, and the `or` inside it routed so the disjunction
/// resolves — under the defect the inner `|` was `Bool.or` even when `not` was fine.
///
/// Driven with an empty disjunction so the expected answer (1) is the NAF-succeeds one:
/// a row that expected 0 would pass with the whole body inert.
#[test]
fn the_routing_reaches_a_nested_connective() {
    let ns = "test.wi1046.nested";
    let src = format!(
        "namespace {ns}\n\
         \x20 import anthill.prelude.Bool\n\
         \x20 fact left1046(1)\n\
         \x20 fact empty1046(99)\n\
         \x20 rule nested1046(?x) :- left1046(?x), not(empty1046(?x) | empty1046(?x))\n\
         end\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        crate::common::query_unary(&mut kb, &format!("{ns}.nested1046")).len(),
        1,
        "a disjunction nested under a negation must resolve, not evaluate",
    );
}

/// `&` IN A GOAL POSITION IS REFUSED, naming the comma. There is no `kernel.and` to
/// route it to (§6.6), so the choice was between leaving it silently inert — MEASURED,
/// `l(?x) & r(?x)` answers 0 with BOTH facts present — and refusing it.
///
/// WI-20260822-J38JE — THIS ROW USED TO ASSERT A REFUSAL, and asserts an ANSWER now.
///
/// `a & b` in a goal position was refused because there was nothing to route it to
/// ("goal conjunction is the comma — there is no `kernel.and`"). That was a missing
/// primitive stated as a rule about the language: `not` and `or` each had a resolver
/// primitive and `and` had none. `anthill.kernel.and` over `push_and` supplies it, so
/// THIS EXACT PROGRAM — the one WI-1046 measured answering 0 — now answers what the
/// comma answers, and the comma is driven beside it because agreeing with it is the
/// whole claim.
#[test]
fn a_goal_position_and_is_the_conjunction() {
    let mk = |op: &str| {
        format!(
            "namespace test.wi1046.andgoal{}\n\
             \x20 fact left1046(1)\n\
             \x20 fact right1046(1)\n\
             \x20 fact left1046(2)\n\
             \x20 rule both1046(?x) :- left1046(?x) {op} right1046(?x)\n\
             end\n",
            op.len()
        )
    };
    let count = |op: &str| {
        let ns = format!("test.wi1046.andgoal{}.both1046(?x)", op.len());
        let mut kb = crate::common::load_kb_with(&mk(op));
        let goal = crate::common::query_pattern_term(&mut kb, &ns);
        kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default()).len()
    };
    assert_eq!(count("&"), 1, "`l(?x) & r(?x)` answers the one shared binding");
    assert_eq!(count(","), 1, "…and the COMMA answers the same — that is the claim");
}

/// THE CONTROL THE REFUSAL MUST NOT CONSUME: an OPERATION body still evaluates `&` /
/// `|` / `!` as the dispatched Bool VALUE operators. That is the other half of
/// position-directedness and the half WI-529 already delivered; this fixture is here so
/// that a future widening of the goal-position rule has to come past it.
///
/// Passes with both halves backed out, by design.
#[test]
fn an_operation_body_still_evaluates_the_value_operators() {
    let src = "namespace test.wi1046.opbody\n\
               \x20 import anthill.prelude.Bool\n\
               \x20 operation both1046(a: Bool, b: Bool) -> Bool = a & b\n\
               \x20 operation either1046(a: Bool, b: Bool) -> Bool = a | b\n\
               \x20 operation neither1046(a: Bool, b: Bool) -> Bool = !(a | b)\n\
               end\n";
    crate::common::load_kb_with(src);
}

/// …AND THE OTHER POSITION THE ROUTING MUST NOT TOUCH: a DATA slot inside a rule body.
/// `and` in a goal's ARGUMENT is a value expression, so it stays the Bool operation and
/// is neither routed nor refused.
///
/// This is the boundary the `in_body_goal` flag exists to draw — it turns off at every
/// slot the shared `goal_arg_slots` table does not list. Without that, this program
/// would be refused, and the refusal would be wrong. Passes either way by design (the
/// flag is off here before and after), which is exactly why it is worth pinning: it is
/// what a "just refuse `and` anywhere in a rule body" shortcut would break, and the
/// shortcut is the obvious way to write this fix.
///
/// Spelled as an explicit `and(…)` call rather than the infix `?r = ?a & ?b`, because
/// that spelling is NOT this case — see the test below.
#[test]
fn a_data_slot_keeps_the_value_operators() {
    let src = "namespace test.wi1046.dataslot\n\
               \x20 import anthill.prelude.Bool\n\
               \x20 fact flag1046(true)\n\
               \x20 rule anded1046(?r) :- flag1046(?a), flag1046(?b), eq(?r, and(?a, ?b))\n\
               end\n";
    crate::common::load_kb_with(src);
}

/// A PRECEDENCE TRAP THE REFUSAL MAKES LOUD, found by the control above failing on a
/// fixture that looked like a data slot and was not.
///
/// `&` is priority 2 and `=` is priority 3 (§6.6), and higher binds tighter — so
/// `?r = ?a & ?b` is `and(eq(?r, ?a), ?b)`, NOT `eq(?r, and(?a, ?b))`. The `and` is the
/// TOP-LEVEL GOAL. Before WI-1046 that rule loaded clean and silently never fired,
/// which is the worst possible outcome for a precedence surprise: the author's mental
/// parse and the engine's differ and nothing says so. It is now refused at the `and`.
///
/// Pinned because the refusal's VALUE here is larger than for a hand-written `a & b` —
/// nobody writes `a & b` as a goal on purpose, but `?r = ?a & ?b` is a natural thing to
/// write and means something else.
///
/// THE SIBLING `|` IS DELIBERATELY NOT REFUSED, and the asymmetry is the point rather
/// than an oversight. `|` is priority 1, so `?r = ?a | ?b` is `or(eq(?r, ?a), ?b)` — the
/// same trap — and it now answers `?r = ?_` with `residual: eq(?_, true)`, i.e. ONE
/// CONDITIONAL solution where it used to answer none. That is not the fabricated
/// DEFINITE answer `the_routing_does_not_capture_the_relational_call_form` guards
/// against: the resolver reports the residual, so nothing is passed off as decided.
/// And the two cases are not alike — `&` has NO goal reading at all (§6.6), so refusing
/// it costs nothing, whereas `or(eq(…), ?b)` is a well-formed disjunction whose second
/// branch happens to be a bare VARIABLE. Refusing that shape would refuse legitimate
/// `or`s; what is actually wrong there is a variable in a goal branch, which is a
/// different question (the `ho_apply` / unbound-predicate family) and not WI-1046's.
/// THE PRECEDENCE TRAP IS QUIET AGAIN, AND THIS ROW IS WHERE THAT IS RECORDED.
///
/// `&` has priority 2 and `=` priority 3, and HIGHER BINDS TIGHTER — so `?r = ?a & ?b`
/// parses as `and(eq(?r, ?a), ?b)`: the `&` is the GOAL conjunction and `?b` is its
/// second CONJUNCT, not an operand of the value `and` the author meant. While `and` in
/// a goal position was REFUSED that misreading was a load error; now it is a legal
/// conjunction that computes something else.
///
/// DRIVEN THROUGH THE PARSE, not through a binding, and that is deliberate: `=` is
/// `PartialEq.eq`, a semantic equality TEST that NEVER BINDS (§8.3), so the obvious
/// fixture — `?r = ?a & ?b` with `?r` free — SUSPENDS, and counting `.len()` on it
/// reports 1 for a residual that decided nothing. (Measured: `?r = (?a & ?b)` is
/// `total = 1, definite = 0`. An earlier draft of this row asserted that 1.) So both
/// operands are ground and the rows differ only in whether `?b` became a goal:
///
/// | body (`?a = true`, `?b = false`) | definite | why |
/// |---|---|---|
/// | `?a = true` | 1 | the `eq` test alone, and it decides |
/// | `?a = true & ?b` | **0** | …and `?b` is now a CONJUNCT — the goal `false` fails |
///
/// IT IS NOT REFUSABLE BY SHAPE, which is why it is pinned rather than fixed: the
/// trap's shape is `and(eq(…), g)`, an ordinary conjunction to write once `and` has a
/// goal reading (`(?x = 1) & p(?x)`). Refusing it would refuse a legitimate program, so
/// the lost loudness is a real cost of giving `and` its reading — recorded here instead
/// of left to be rediscovered. §6.6 keeps the precedence warning in prose.
#[test]
fn the_equals_versus_ampersand_precedence_trap_is_a_silent_zero() {
    let src = "namespace test.wi1046.precedence\n\
               \x20 import anthill.prelude.Bool\n\
               \x20 fact ft1046(true)\n\
               \x20 fact ff1046(false)\n\
               \x20 rule trap1046(1) :- ft1046(?a), ff1046(?b), ?a = true & ?b\n\
               \x20 rule ctrl1046(1) :- ft1046(?a), ff1046(?b), ?a = true\n\
               end\n";
    let mut kb = crate::common::load_kb_with(src);
    let definite = |kb: &mut anthill_core::kb::KnowledgeBase, pred: &str| {
        let goal =
            crate::common::query_pattern_term(kb, &format!("test.wi1046.precedence.{pred}(1)"));
        kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default())
            .iter()
            .filter(|s| s.is_definite())
            .count()
    };
    assert_eq!(
        definite(&mut kb, "ctrl1046"),
        1,
        "CONTROL: the `eq` test alone decides — without it the row below measures nothing"
    );
    assert_eq!(
        definite(&mut kb, "trap1046"),
        0,
        "`?a = true & ?b` is `and(eq(?a, true), ?b)`, so `?b` is a CONJUNCT and the \
         goal `false` fails — the same program was a LOAD ERROR before `and` had a \
         goal reading"
    );
}

// ── The three the /code-review pass found, each driven ────────────────────────

/// REVIEW FINDING 1 — a node is a conjunction WRAPPER because of WHERE IT SITS, never
/// because of what it is NAMED.
///
/// The first cut keyed the wrapper on `local_name == "tuple"` at any goal node, so a
/// USER predicate locally named `tuple` leaked goal-ness into its DATA arguments: this
/// program was REFUSED while the identical one with the predicate renamed loaded. Both
/// arms are driven together, because a test on the `tuple` arm alone would pass equally
/// if the walk had simply stopped refusing everything.
///
/// The wrapper bit now rides a second flag, set only when the walk arrives through a
/// slot the shared table marks `tuple_wrapped` — the same distinction
/// `KnowledgeBase::tuple_goal_children` draws by only ever being called from the
/// quantifier arm (WI-1034's own review finding, one layer down).
#[test]
fn a_user_predicate_named_tuple_keeps_its_arguments_as_data() {
    let named_tuple = "namespace test.wi1046.usertuple\n\
                       \x20 import anthill.prelude.Bool\n\
                       \x20 fact tuple(true)\n\
                       \x20 fact bit1046(true)\n\
                       \x20 rule r(?x) :- bit1046(?a), bit1046(?b), tuple(?a & ?b), ?x = 1\n\
                       end\n";
    let renamed = named_tuple
        .replace("test.wi1046.usertuple", "test.wi1046.usertuple2")
        .replace("tuple(", "ordinary1046(");
    crate::common::load_kb_with(&renamed); // the CONTROL, first: the shape is loadable
    crate::common::load_kb_with(named_tuple);
}

/// REVIEW FINDING 2 — the shared table says which slots are goals; the DESCENT POLICY
/// stays with each caller, and the query-pattern walk's policy is not to enter a
/// discharge.
///
/// Folding `forall_impl` into `goal_arg_slots` silently changed the QUERY walk, which
/// had listed only the bounded quantifiers. A nested implication IS a query surface
/// form (`grammar.js`'s `_non_name_atom_term` — WI-863's doc claimed otherwise), and
/// the query walk has no rule to collect hypotheses from, so entering it refused a name
/// the pattern itself declares.
///
/// Driven through the PATTERN reader rather than a load, because that is the only place
/// this fires; asserted under a `not`, since a bare connective is not entered either way
/// and would measure nothing.
#[test]
fn a_query_pattern_discharge_does_not_refuse_its_own_hypothesis() {
    let mut kb = crate::common::load_kb_with(
        "namespace test.wi1046.q\n  fact seed1046(1)\n  rule ok1046(?x) :- seed1046(?x)\nend\n",
    );
    let qt =
        crate::common::query_pattern_term(&mut kb, "not((forall(?h), hyp1046(?h) -: hyp1046(?h)))");
    let undefined: Vec<String> = kb
        .undefined_query_goal_functors(qt)
        .iter()
        .map(|s| kb.qualified_name_of(*s).to_string())
        .collect();
    assert!(
        undefined.is_empty(),
        "a discharge DECLARES its antecedents; the query walk must not refuse them: {undefined:?}",
    );
}

/// REVIEW FINDING 3 — the routing is gated on ARITY, so it cannot capture the
/// RELATIONAL call form of the same spec op.
///
/// `Bool.not(?a, ?r)` is the WI-938 functional-relation spelling — the result rides the
/// last argument — and it is a different call from the unary `not(goal)`. An
/// identity-only redirect rewrote it to `anthill.kernel.not`, the arity-1 NAF builtin,
/// which then SUCCEEDED VACUOUSLY: 1 solution with `?r` unbound (`?_`) and reported
/// DEFINITE. That is a wrong answer, and worse than the 0 solutions it replaced.
///
/// The assertion is on the BINDING, not the count: a count-only test would have read
/// "1 solution" as an improvement over the pre-change 0, which is exactly the reading
/// that made this look like a fix. 0 solutions here is the pre-existing behaviour of
/// the relational form on `Bool` (unrelated to WI-1046); what this pins is that the
/// routing does not turn it into a fabricated answer.
#[test]
fn the_routing_does_not_capture_the_relational_call_form() {
    let ns = "test.wi1046.relational";
    let src = format!(
        "namespace {ns}\n  import anthill.prelude.Bool\n\
         \x20 fact bit1046(true)\n\
         \x20 rule notrel1046(?r) :- bit1046(?a), Bool.not(?a, ?r)\n\
         end\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    let sols = crate::common::query_unary(&mut kb, &format!("{ns}.notrel1046"));
    for (v, definite) in &sols {
        let rendered = match v {
            anthill_core::eval::Value::Term { id, .. } => {
                anthill_core::persistence::print::TermPrinter::over(&kb).print_term(*id)
            }
            other => format!("{other:?}"),
        };
        assert!(
            !(*definite && rendered.starts_with("?")),
            "a DEFINITE answer must bind its result; got `{rendered}` — the arity-blind \
             redirect made NAF succeed vacuously here",
        );
    }
}

/// REVIEW ROUND 2, FINDING 1 — a connective is recognised by its SHAPE, never by its
/// spelling alone. Every arm of `goal_arg_slots` is gated on positional arity.
///
/// The table recognises `or` (a kernel RULE) and the markers by NAME, since they head no
/// builtin — and the loader now READS that table to decide which arguments are goals, so
/// a mis-classification became a load-blocking refusal. MEASURED: a user `fact or(true)`
/// with `or(?a & ?b)` in a rule body was REFUSED, because `or` was registered at slots 0
/// and 1 whatever the node's arity, so an `or/1` atom had its VALUE argument walked as a
/// goal. The identical program with the predicate renamed loaded clean.
///
/// Both arms again, and for the reason the `tuple` twin gives: an arm alone would pass
/// equally if the walk had simply stopped classifying anything.
///
/// This is the third time the same defect has been found one layer over — `tuple` (round
/// 1), `and` (WI-1034's review), now `or` and the markers. The gate is now uniform, and
/// the arities are the connectives' own rather than a second opinion about them.
#[test]
fn a_user_predicate_named_or_keeps_its_arguments_as_data() {
    let named_or = "namespace test.wi1046.useror\n\
                    \x20 import anthill.prelude.Bool\n\
                    \x20 fact or(true)\n\
                    \x20 fact bit1046o(true)\n\
                    \x20 rule r(?x) :- bit1046o(?a), bit1046o(?b), or(?a & ?b), ?x = 1\n\
                    end\n";
    let renamed = named_or
        .replace("test.wi1046.useror", "test.wi1046.useror2")
        .replace("or(", "ordinary1046o(");
    crate::common::load_kb_with(&renamed); // CONTROL first: the shape is loadable
    crate::common::load_kb_with(named_or);

    // …and the real `or/2` still IS a connective, so the gate did not retire the arm.
    let ns = "test.wi1046.realor";
    let src = format!(
        "namespace {ns}\n\
         \x20 fact leftor1046(1)\n\
         \x20 fact rightor1046(2)\n\
         \x20 rule pipe(?x) :- leftor1046(?x) | rightor1046(?x)\n\
         end\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        crate::common::query_unary(&mut kb, &format!("{ns}.pipe")).len(),
        2,
        "gating on arity must not stop `or/2` being the kernel disjunction",
    );
}
