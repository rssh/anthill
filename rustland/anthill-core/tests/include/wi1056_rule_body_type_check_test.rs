//! WI-1056 — a RULE BODY is type-checked, at the shape WI-1043 admitted: a body-less
//! spec-op atom reports every failure its type-check finds, not only the two 058 ties of
//! its own call.
//!
//! WI-1043 made a rule-body call on a body-less spec op a call site, for a DISPATCH
//! verdict. An `=` goal loads as a call on `PartialEq.eq` and arithmetic loads as calls on
//! `Numeric`, so that shape is most of what a rule body is made of — and a rule body had
//! never been type-checked at all (`type_rule_bodies` decides dispatch; it does not check
//! types). WI-1043 therefore reported only the ties, holding the status quo for the rest,
//! and left the rest here: **133** newly decided call sites on a whole-corpus load, whose
//! failures were 19 leaf errors rendering as **7 load errors in 4 files**, every one a
//! program that loaded and ran.
//!
//! ## The 7, decided — three ways, and only the last is an exemption
//!
//! | site | verdict |
//! |---|---|
//! | `webots/lf1/safety_common.anthill:236` (`Vec3(x: …)` in an `=` goal) | TYPER GAP, fixed |
//! | `webots/lf1/safety_gps.anthill:154` (`Pose(position: …)`) | TYPER GAP, fixed (same fix) |
//! | `stdlib/prelude/logical_stream.anthill:73` (`splitFirst(?a) = some(pair(…))`) | TYPER GAP, fixed (+ source clarified) |
//! | `stdlib/prelude/bigint.anthill:39` (`sub(?n, 1)`) | SOURCE error, fixed at source |
//! | `webots/lf1/safety_common.anthill:277,278,279` (`?p1.position`) | the standing WI-282 EXEMPTION |
//!
//! * **The constructor gap.** `check_apply_iter`'s materializer-fallback gate asked
//!   `is_constructor_symbol` — "is a constructor OF some enclosing sort" — where the
//!   question is `is_entity_constructor`, "does an APPLICATION of this functor construct
//!   an entity value". WI-926 made the first FALSE for an eponymous `sort E { entity E(…)
//!   }` (it is not a constructor of anything; it IS the sort) and it was never true for a
//!   free-standing `entity E(…)`. An operation body never notices, because the LOADER's
//!   `ApplyOrConstructor` drain already asks the right one; a rule body does not take that
//!   drain.
//! * **The partial-application gap.** `parameterized_compatible_view` refused a same-base
//!   actual that omits a declared parameter — the ONLY one of four spellings of that type
//!   to be refused: the bare form, the explicit `U = ?`, and an operation type parameter
//!   all conformed already. See `all_four_spellings_of_one_type_conform_alike`, and its
//!   doc for the false control that briefly reverted this fix. Whether the permissive
//!   reading is right AT ALL is pre-existing and belongs to all four spellings —
//!   **WI-1059**.
//! * **The source error.** `bigint`'s induction schema wrote bare `0` / `1` where
//!   `BigInt` is declared — a small integer literal is an `Int64` (only an i64 OVERFLOW
//!   parses as `BigInt`) and there is no implicit widening.
//!
//! `logical_stream`'s `interleave` is corrected too, though the typer fix alone would have
//! made it load: written `LogicalStream[?A]` it bound T and left the WI-714 effect row to
//! the sort's default, and it now shares one row variable across both inputs and the
//! result — which is what fair disjunction does. That is a clarification, not the fix.
//! * **The exemption** is not new and is not a blanket skip: an UNRESOLVED dot receiver
//!   (`undecidable_by_this_typer`) has been tolerated since WI-282, because a rule head
//!   declares no types. A dot on a KNOWN receiver still refuses — see
//!   `an_unresolved_receiver_is_exempt_and_a_known_one_is_not`, whose two halves are the
//!   pairing that makes the exemption a rule rather than a hole.
//!
//! A SECOND exemption joined it, from the same walk and for the same reason — the typer
//! has no reading, not that it declines to report one. An EQUATION-INTRODUCED functor
//! applied in a rule body (`ite`) has no signature to check against: `bool.anthill` argues
//! it CANNOT be an operation, because an operation evaluates both branches. WI-898 had
//! already gated its diagnostic `!in_rule_body` and then let the node fall through to a
//! worse one, so this half was only ever half written. Its boundary is the IMPORT, and
//! that is what keeps it from being a hole
//! (`an_imported_equation_functor_is_exempt_and_an_unresolved_one_is_not`).
//!
//! ## What is NOT in this ticket, MEASURED rather than deferred on a hunch
//!
//! The general `Expr::Apply` — a rule-body call that is neither a dot nor a spec op — is
//! still not typed. With this walk's gate widened to every `Expr::Apply`, a stdlib +
//! host-bindings load alone reports **468** errors (173 distinct) against **2** for the
//! body-less shape. They are not a backlog of small mistakes but two readings the typer
//! does not have: a rule NAME applied to arguments is a relational SUBGOAL (the WI-714 arm
//! is gated `!in_rule_body` for exactly that reason, so every subgoal falls through to
//! `UnknownApplyFunctor`), and `?P(…)` / reflect arguments land in `List[T = Term]`
//! positions. **WI-1058** owns it.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each
//!
//! | test | policy | ctor gate | partial-app | dedup | exemption |
//! |---|---|---|---|---|---|
//! | `a_genuine_type_error_in_a_rule_body_is_refused_at_load` | **FAILS** | ok | ok | ok | ok |
//! | `the_rule_body_and_the_operation_body_report_the_same_error` | **FAILS** | ok | ok | ok | †  |
//! | `an_eponymous_constructor_constructs_in_a_rule_body` | **FAILS** | **FAILS** | ok | ok | †  |
//! | `a_free_standing_entity_constructs_in_a_rule_body` | **FAILS** | **FAILS** | ok | ok | †  |
//! | `a_sort_nested_constructor_still_constructs` | **FAILS** | ok | ok | ok | †  |
//! | `one_leaf_inside_nested_body_less_atoms_is_reported_once` | **FAILS** | ok | ok | **FAILS** | †  |
//! | `an_unresolved_receiver_is_exempt_and_a_known_one_is_not` | ok | ok | ok | ok | **FAILS** |
//! | `an_imported_equation_functor_is_exempt_and_an_unresolved_one_is_not` | **FAILS** | ok | ok | ok | **FAILS** |
//! | `all_four_spellings_of_one_type_conform_alike` | ok | ok | **FAILS** | ok | †  |
//! | `the_bigint_induction_schema_is_typed_at_bigint` | ok | ok | ok | ok | †  |
//! | `the_corpus_still_loads` | ok | ok | ok | ok | **FAILS** |
//!
//! **†  is COLLATERAL, not coverage**, and it is the most informative cell in the table:
//! backing out the exemptions stops the STDLIB ITSELF from loading, so every test here
//! that needs a clean load breaks at the harness. That is precisely what
//! `the_corpus_still_loads` reports, and it is why that row — which reads like a
//! formality — is a real subject in that column rather than the pure non-regression this
//! file's first draft claimed. Read a † as "this row says nothing about that column".
//!
//! THE PREDICTED TABLE WAS WRONG IN NINE CELLS and the measurement is what fixed it; it is
//! recorded because two of the corrections are structural, not clerical:
//!
//!   * The three constructor rows FAIL under **policy** as well as under the ctor gate, and
//!     that is correct rather than a leak: `constructor_is_checked` drives the gate through
//!     a REFUSAL (a wrong field type), and with the tie-only policy back nothing reports
//!     it. A test that proves its subject by a refusal necessarily depends on the frame
//!     that reports refusals.
//!   * `a_sort_nested_constructor_still_constructs` is ok under **ctor gate** — its claim —
//!     but the first draft had it ok in EVERY column, which was false for a second reason:
//!     `carrier`'s sort spelled its constructor eponymously (`sort W { entity W(…) }`), so
//!     four rows that say nothing about constructors moved when the gate was reverted. The
//!     fixture now spells it `Wv`; see `carrier`.
//!
//! REFERENCE: WI-1043 (the shape and its narrowing); WI-1026; WI-282 (the exemption);
//! WI-926 (the eponymous constructor); WI-1058 (the general `Expr::Apply`);
//! `docs/kernel-language.md` §"Expansion during unification";
//! `docs/design/058-implementation.md` §23.

use crate::wi1012_static_supplier_tie_test::refusal;

/// A carrier with a member that takes a second `Int64` argument — the smallest program
/// with a call that can be WRONG in an ordinary way (a `String` where `Int64` is
/// declared), reachable from a rule body and from an operation body alike.
///
/// The constructor is `Wv`, NOT an eponymous `W`, and that is deliberate: an eponymous one
/// would make every test built on this fixture depend on the CONSTRUCTOR GATE as well as
/// on whatever it means to measure, and the back-out matrix below would then show those
/// rows failing in a column they say nothing about. MEASURED — the first version did spell
/// it `W` and four unrelated rows moved when the gate was reverted.
fn carrier(tail: &str) -> String {
    format!(
        "namespace test.wi1056\n\
         \x20 import anthill.prelude.{{Int64, String, Bool}}\n\
         \n\
         \x20 sort W\n\
         \x20   entity Wv(n: Int64)\n\
         \x20   operation bump(w: W, by: Int64) -> Int64\n\
         \x20 end\n\
         \n{tail}end\n",
    )
}

/// THE HEADLINE. A rule body with a genuine type error is REFUSED at load, naming the
/// parameter it is wrong about.
///
/// The error sits INSIDE an `=` goal, which is what makes it reachable at all: the atom
/// loads as a call on the body-less `PartialEq.eq`, so WI-1043's gate decides it and this
/// ticket's policy reports what deciding it found. CONTROL: with the policy back at
/// WI-1043's tie-only filter this program loads CLEAN and the rule silently never answers.
#[test]
fn a_genuine_type_error_in_a_rule_body_is_refused_at_load() {
    let msg = refusal(&carrier(
        "  rule bad(?r) :- ?r = W.bump(Wv(n: 1), \"not an int\")\n",
    ));
    assert!(
        msg.contains("bump.by") && msg.contains("expected Int64") && msg.contains("got String"),
        "the refusal must name the parameter and both types: {msg}",
    );
}

/// The POINT of the widening, stated as an equality rather than as two separate
/// assertions: one wrong call reports the same thing wherever it is written. Before this
/// ticket the operation body refused and the rule body loaded clean — one program, two
/// verdicts, decided by which side of `:-` the call sat on.
///
/// Compares the message BODY, not the location: the two calls are on different lines by
/// construction.
#[test]
fn the_rule_body_and_the_operation_body_report_the_same_error() {
    let bad_arg = "W.bump(Wv(n: 1), \"not an int\")";
    let from_rule = refusal(&carrier(&format!("  rule bad(?r) :- ?r = {bad_arg}\n")));
    let from_op = refusal(&carrier(&format!(
        "  operation probe() -> Int64 = {bad_arg}\n"
    )));
    let body = |m: &str| m.split_once(": ").expect("a `line:col: message` rendering").1.to_string();
    assert_eq!(
        body(&from_rule),
        body(&from_op),
        "a rule body and an operation body must report ONE call's error identically\n\
         rule: {from_rule}\nop:   {from_op}",
    );
}

/// An EPONYMOUS constructor applied in a rule body is a CONSTRUCTION, and this DRIVES the
/// constructor checker rather than asserting the program loads: the good program loads AND
/// a wrong FIELD TYPE is refused naming the field and both types. Only a node that reached
/// `check_constructor_iter` can produce that message — a gate that merely stopped erroring
/// could not.
///
/// CONTROL: with the gate back at `is_constructor_symbol` the good half is
/// `unknown apply functor: P` and the bad half reports the SAME vague thing instead of the
/// field — WI-926 deliberately does not mark an eponymous constructor, since it is not a
/// constructor OF anything.
#[test]
fn an_eponymous_constructor_constructs_in_a_rule_body() {
    constructor_is_checked("test.wi1056.epo", "sort P\n    entity P(a: Int64)\n  end", "P");
}

/// A FREE-STANDING `entity E(…)` — the `Pose` shape from
/// `examples/webots-modelling/lf1/leader.anthill`, declared at namespace level with no
/// enclosing sort. Same gate, second population: `is_constructor_symbol` was never true
/// for one of these either.
#[test]
fn a_free_standing_entity_constructs_in_a_rule_body() {
    constructor_is_checked("test.wi1056.free", "entity F(a: Int64)", "F");
}

/// THE NEGATIVE CONTROL for the constructor gate: a sort-nested, differently-named
/// constructor is the case `is_constructor_symbol` already answered. It must keep working,
/// and — said explicitly, because a both-ways-green test is not evidence on its own — it
/// passes with the gate reverted too. That is what makes the pair above a WIDENING rather
/// than a rewrite.
#[test]
fn a_sort_nested_constructor_still_constructs() {
    constructor_is_checked("test.wi1056.nested", "sort S\n    entity Q(a: Int64)\n  end", "Q");
}

/// Build `<decl>` and drive its constructor from a rule body, both ways: `?r = <ctor>(a:
/// 7)` must LOAD, and `?r = <ctor>(a: "seven")` must be REFUSED naming the field. Shared by
/// the three constructor tests so the only difference between them is the DECLARATION.
///
/// THE REFUSAL IS THE DRIVE. "It loads" would pass under any gate that stopped erroring;
/// only a node routed to `check_constructor_iter` reads the entity's declared field schema,
/// so `P.a (entity-field): expected Int64, got String` is evidence the construction was
/// really classified as one. It is also the exact check the corpus needed — `Vec3(x: ?nx,
/// y: ?ny, z: ?nz)` inside an `=` goal at `safety_common.anthill:236`.
///
/// NOT ASSERTED BY READING THE CONSTRUCTED VALUE BACK, which was the first draft and
/// measures something else: `=` never binds a logical variable (WI-519), so `rule mk(?p) :-
/// ?p = <ctor>(a: 7)` answers an undischarged residual, and the projecting form `?x =
/// <ctor>(a: 7).a` answers one too. Routing around that (a relational goal on a bodied
/// operation) leaves the constructor OUTSIDE any decided atom, so the test would pass with
/// the gate reverted — a both-ways-green subject.
fn constructor_is_checked(ns: &str, decl: &str, ctor: &str) {
    let src = |field: &str| {
        format!(
            "namespace {ns}\n\
             \x20 import anthill.prelude.{{Int64, String}}\n\
             \n\
             \x20 {decl}\n\
             \n\
             \x20 rule mk(?r) :- ?r = {ctor}(a: {field})\n\
             end\n",
        )
    };
    crate::common::load_kb_with(&src("7"));
    let msg = refusal(&src("\"seven\""));
    assert!(
        msg.contains(&format!("{ctor}.a")) && msg.contains("entity-field"),
        "a wrong FIELD TYPE must be refused as one — which only a node that reached the \
         constructor checker can report: {msg}",
    );
}

/// ONE type, FOUR spellings, ONE verdict — and the fourth is the only one this ticket
/// had to change.
///
/// `Box[T = Int64]` omits a declared parameter; `Box[T = Int64, U = ?]` writes the same
/// wildcard out; `Box` omits both; `feed[U](b: Box[T = Int64, U = U])` names it as an
/// operation type parameter. They denote the same thing, and kernel-language
/// §"Expansion during unification" says so. THREE of them already conformed to
/// `Box[T = Int64, U = Bool]`; only the partial one was refused, because a bare `Ref`
/// never reaches `parameterized_compatible_view` and an explicit `?` is a value in the
/// bindings list, while an OMITTED slot hit the `None` arm that rejected.
///
/// THE EFFECT-ROW HALF IS THE SAME TEST, and it is here because a first cut REVERTED this
/// fix over it. `feed(s: Stream[T = Int64])` against `takes_pure(s: Stream[T = Int64,
/// E = {}])` does flip from refused to accepted when the arm lands, which read as a
/// soundness regression — an effectful stream reaching a slot declared pure. It is not one:
/// the identical acceptance is reachable without the fix by writing `E = ?` or the bare
/// `Stream`, as the row below asserts. The control had measured "did this change THIS
/// program's verdict" instead of "was that verdict already obtainable another way".
///
/// Whether the permissive reading is right AT ALL is a separate, pre-existing question
/// belonging to all four spellings — **WI-1059**, where the restrictive answer's cost is
/// measured. This test pins only that they AGREE.
///
/// CONTROL: back out the arm and the two `partial` rows fail while the other six pass —
/// which is exactly the asymmetry, and exactly why the other six are here.
#[test]
fn all_four_spellings_of_one_type_conform_alike() {
    let boxed = |param: &str, op: &str| {
        format!(
            "namespace test.wi1056.partial\n\
             \x20 import anthill.prelude.{{Int64, Bool}}\n\
             \n\
             \x20 sort Box\n\
             \x20   sort T = ?\n\
             \x20   sort U = ?\n\
             \x20   entity Box(t: T, u: U)\n\
             \x20   operation get(b: Box) -> Int64\n\
             \x20 end\n\
             \n\
             \x20 operation takes_full(b: Box[T = Int64, U = Bool]) -> Int64 = Box.get(b)\n\
             \x20 operation {op}(b: {param}) -> Int64 = takes_full(b)\n\
             end\n",
        )
    };
    let streamed = |param: &str, op: &str| {
        format!(
            "namespace test.wi1056.erow\n\
             \x20 import anthill.prelude.{{Int64, Bool, Stream, List}}\n\
             \x20 operation takes_pure(s: Stream[T = Int64, E = {{}}]) -> Int64\n\
             \x20 operation {op}(s: {param}) -> Int64 = takes_pure(s)\n\
             end\n",
        )
    };
    // (spelling, operation header) — the op-type-param row needs its own `[U]` / `[E]`.
    for (param, op) in [
        ("Box[T = Int64, U = U]", "feed[U]"),   // explicit operation type parameter
        ("Box", "feed"),                         // bare: all parameters unwritten
        ("Box[T = Int64, U = ?]", "feed"),      // wildcard written out
        ("Box[T = Int64]", "feed"),             // PARTIAL — the spelling this ticket fixed
    ] {
        crate::common::load_kb_with(&boxed(param, op));
    }
    for (param, op) in [
        ("Stream[T = Int64, E = E]", "feed[E]"),
        ("Stream", "feed"),
        ("Stream[T = Int64, E = ?]", "feed"),
        ("Stream[T = Int64]", "feed"),
    ] {
        crate::common::load_kb_with(&streamed(param, op));
    }
}

/// ONE leaf error inside NESTED body-less atoms is reported ONCE.
///
/// A REGRESSION GUARD, and the case that found it is in the corpus: this walk RECURSES
/// into a body-less atom and then type-checks the whole atom, so every failure inside one
/// is derived by the descendant that owns it and again by each body-less ancestor. Here
/// the bad argument sits inside `sub` (a `Numeric` call) inside `=` (a `PartialEq.eq`
/// call) — two ancestors, and without `already_reported` the same line prints twice.
/// MEASURED first on `safety_common.anthill:277` (`?dx = ?p1.position.x - ?p2.position.x`),
/// which reported its dot twice for exactly this reason.
#[test]
fn one_leaf_inside_nested_body_less_atoms_is_reported_once() {
    let msg = refusal(&carrier(
        "  rule bad(?r) :- ?r = W.bump(Wv(n: 1), \"not an int\") - 1\n",
    ));
    assert!(msg.contains("bump.by"), "the nested failure must still be reported: {msg}");
    assert_eq!(
        msg.lines().count(),
        1,
        "one wrong argument inside two nested body-less atoms is ONE report: {msg}",
    );
}

/// THE EXEMPTION AND ITS BOUNDARY, in one test because either half alone reads as the
/// other's absence.
///
/// A rule head declares no types, so a dot on a head variable has NO receiver sort at load
/// — `tolerated_unresolved_receiver`, the WI-282 status quo, and the whole of what this
/// ticket does not newly refuse in the corpus (7 reports at 4 sites in
/// `examples/webots-modelling/lf1/safety_common.anthill`). The exemption is on the
/// UNRESOLVED receiver only: a dot on a receiver the typer DOES know still refuses, from
/// inside the same `=` goal.
///
/// CONTROL: drop the predicate from the leaf filter and the first arm refuses. The second
/// arm is WI-282's own diagnostic and passes either way — it is here to show the first arm
/// is a rule about unresolved receivers, not a skip of dot errors.
#[test]
fn an_unresolved_receiver_is_exempt_and_a_known_one_is_not() {
    // Untyped head vars: `?p1`/`?p2` have no sort, so `.position` cannot be resolved.
    crate::common::load_kb_with(
        "namespace test.wi1056.unresolved\n\
         \x20 import anthill.prelude.Float\n\
         \x20 rule dist(?dx, ?p1, ?p2) :- ?dx = ?p1.position.x - ?p2.position.x\n\
         end\n",
    );
    // A KNOWN receiver with no such member, inside the same `=` goal shape.
    let msg = refusal(&carrier("  rule bad(?r) :- ?r = Wv(n: 1).nosuch\n"));
    assert!(
        msg.contains("nosuch"),
        "a dot on a KNOWN receiver must still be refused: {msg}",
    );
}

/// THE SECOND EXEMPTION AND ITS BOUNDARY: an EQUATION-INTRODUCED functor applied in a
/// rule body is not a call this typer can check, and the boundary is the IMPORT.
///
/// `bool.anthill` argues that `ite` cannot be an operation at all — an operation would
/// evaluate both branches — so its two `[simp]` equations are its whole definition and
/// there is no signature to check a call against. `ordered.anthill` writes the same bare
/// call in a rule HEAD, which this walk never visits; refusing it in a BODY would make one
/// expression legal on one side of `:-` and not the other, and would refuse a program
/// smt-gen lowers to `(ite …)` today (`wi680_ite_lowering_test`).
///
/// The exemption is on the RESOLVED functor, which is what keeps it from being a hole:
/// without `import anthill.prelude.Bool.{ite}` the name interns bare, carries no kind, and
/// is still refused — correctly, since without the import it reaches none of the `[simp]`
/// rules either. Both arms are MEASURED here, and the pair is the test: the first alone
/// would pass under a blanket skip of unknown functors.
///
/// CONTROL: drop `UnreducedEquationFunctor` from `undecidable_by_this_typer` and the first
/// arm is refused — as `ambiguous dispatch of PartialEq.eq` if the raise is softened to an
/// `Ok`, which is why it is an `Err`. The second arm passes either way, by design.
#[test]
fn an_imported_equation_functor_is_exempt_and_an_unresolved_one_is_not() {
    let with_import = "namespace test.wi1056.ite\n\
                       \x20 import anthill.prelude.{Int64, Bool}\n\
                       \x20 import anthill.prelude.Ord.{gte}\n\
                       \x20 import anthill.prelude.Bool.{ite}\n\
                       \x20 rule clamp(?x, ?r) :- ?r = ite(gte(?x, 0), ?x, 0)\n\
                       end\n";
    crate::common::load_kb_with(with_import);

    let no_import = with_import.replace("  import anthill.prelude.Bool.{ite}\n", "");
    let msg = refusal(&no_import);
    assert!(
        msg.contains("ite") && msg.contains("Bool"),
        "an UNIMPORTED bare `ite` reaches none of the `[simp]` rules and must still be \
         refused, naming its owning sort: {msg}",
    );
}

/// The `bigint` SOURCE fix, pinned where it can be read: `BigInt.induction`'s step names
/// `to_bigint`, because `sub(?n, 1)` passed an `Int64` where `BigInt` is declared.
///
/// A STRUCTURAL ASSERTION, AND IT DOES NOT DRIVE THE SCHEMA — said here rather than left
/// to be assumed, because this file's other tests do drive. Nothing in the workspace
/// resolves `BigInt.induction`: it is a user-visible rule that the prove pipeline's phase γ
/// resolves citations against (`register_induction_axiom_witnesses`'s doc says the
/// hand-written primitives are deliberately not re-registered), and reaching it needs z3.
/// Its only other coverage, `numeric_induction_test::bigint_induction_loads_with_base_and_step`,
/// counts body goals.
///
/// THE RISK THAT LEAVES, raised in this ticket's /code-review and not refuted: `?P(0)` →
/// `?P(to_bigint(0))` puts an unreduced operation application where a literal was, in an
/// ARGUMENT position rather than a goal, so it is not folded by the resolver and would not
/// unify structurally with a base-case fact written at a bare `BigInt`. What keeps it from
/// being a regression is that the ORIGINAL was not usable either — `?P(0)` carried an
/// `Int64` literal, which no BigInt-typed predicate matches — and the step's `sub(?n, …)`
/// was already an unreduced application before this change. Making the schema
/// end-to-end drivable is a separate piece of work and is not claimed here.
///
/// Passes with the POLICY, the CTOR GATE and the DEDUP reverted — it pins a SOURCE edit,
/// which no code revert can undo. It fails under the other two only because the stdlib
/// stops loading at all there (the † cascade in this file's matrix), which is
/// `the_corpus_still_loads`'s claim, not this one's. Read the two together: this says the
/// schema is coherent, that one says nothing in the corpus is refused.
#[test]
fn the_bigint_induction_schema_is_typed_at_bigint() {
    let kb = crate::common::load_kb_with("namespace test.wi1056.bigint\n  fact present1056(1)\nend\n");
    let printer = anthill_core::persistence::print::TermPrinter::new(&kb);
    let sym = kb
        .try_resolve_symbol("anthill.prelude.BigInt.induction")
        .expect("BigInt.induction must be defined");
    let rid = kb
        .rules_by_functor(sym)
        .first()
        .copied()
        .expect("BigInt.induction must have a rule");
    let printed: String = kb
        .rule_body_nodes(rid)
        .iter()
        .map(|g| printer.print_occurrence(g))
        .collect::<Vec<_>>()
        .join(" ");
    assert!(
        printed.contains("to_bigint"),
        "the induction bounds must be BigInts, not Int64 literals: {printed}",
    );
    assert!(printed.contains("sub"), "the strong-induction step still uses sub: {printed}");
}

/// THE BLAST RADIUS, asserted rather than promised: the stdlib + Rust host bindings load
/// clean with the widened policy on. Every fixture above is small enough to be wrong in
/// the same way the policy is; this is the one measurement that catches an over-firing
/// report.
///
/// NOT a formality, and the back-out matrix is what says so: it FAILS when the exemptions
/// are backed out, because the STDLIB itself then no longer loads — exactly the failure
/// mode a suite of small fixtures cannot see. It passes under the other four reverts,
/// where it is the non-regression it looks like. (The `examples/` and `anthill-todo` tiers were measured the same way through
/// `anthill load`; they are not loadable as one batch here — two `classic-mini` files
/// collide on a bare `List` — so the tier this file asserts is the one the harness owns.)
#[test]
fn the_corpus_still_loads() {
    crate::common::load_kb_with("namespace test.wi1056.corpus\n  fact present1056c(1)\nend\n");
}
