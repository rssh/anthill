//! WI-20260925-PRVA2 — defects found while reviewing WI-20260925-P7VP4 / WI-20260925-SHED7,
//! present before those tickets. (a) was delivered by WI-20260925-YNCY3 (its row is
//! `wi1040_require_clause_dictionary_test::a_covered_call_nested_in_another_covered_call_is_-
//! woven_with_it`); (d) moved to proposal 068 (WI-20260926-ACG10), which decides it. The rows
//! here drive the rest, and a defect the ticket did not list: the SLD→eval bridge could not run
//! an operation that queries a rule with its own parameter.
//!
//! ## Back-out
//!
//! Each back-out below was MEASURED alone, over this file and P7VP4's; it fails the rows named
//! and nothing else there.
//!   * (b) skip a functional-relation goal in `body_refuted_by_ground_conjunct` without asking
//!     `functional_relation_refuted` — `a_ground_functional_relation_conjunct_is_evaluated_at_-
//!     opening` (a phantom conditional row); refute it on its zero candidates again, as before
//!     this ticket — that row and `a_functional_relation_goal_is_no_refutation_at_opening`.
//!   * (c), the provision question (`simp_guard_decision` / `provision_admits_carriers`):
//!     - every call on the per-carrier question — the eleven rows that need the provision: every
//!       (c) row below but `a_structural_binding_admits_no_carrier` and
//!       `the_per_carrier_question_refuses_in_either_order`, and P7VP4's
//!       `a_call_with_a_concrete_carrier_among_its_arguments_keeps_value_dispatch` and
//!       `a_witness_carrier_beside_a_second_carrier_loads` (their loads are refused);
//!     - suspend while ANY carrier is unknown, refusing only when all are known —
//!       `known_carriers_no_provision_binds_are_refused_at_load` (it loads clean);
//!     - render a combination's refusal with the per-carrier sentence — the four rows that read
//!       it: `a_refusal_names_the_carriers_no_provision_binds`, `known_carriers_…`,
//!       `a_conversion_row_is_no_instance`, `a_witness_carrier_is_known_at_load`;
//!     - drop `is_conversion_row` from the question — `a_conversion_row_is_no_instance`;
//!     - admit a STRUCTURAL binding — `a_structural_binding_admits_no_carrier`;
//!     - judge a provider variable per parameter — `a_variable_binds_its_parameters_alike`;
//!     - route on "carriers at two distinct parameters" instead of on the spec's carrier
//!       parameter — `a_carrier_at_a_non_carrier_parameter_asks_the_provision` (`t` empty);
//!     - file a witness-provided carrier as unknown at load again —
//!       `a_witness_carrier_is_known_at_load` (it loads, and answers `9`);
//!     - suspend when the first carrier read is unknown —
//!       `the_per_carrier_question_refuses_in_either_order` (one refusal, not two).
//!   * (e) HEAD's check (a failed unification tested against the WRITTEN parameter, no
//!     conformance pass) — `a_slot_route_follows_the_typers_instantiation` (`1` for `2`) and
//!     `a_converted_argument_routes_as_the_typer_instantiates`; a bare `types_compatible` over
//!     the walked pair in place of `validate_arg_against_param` — the conversion row alone; the
//!     argument's type left UNWALKED — P7VP4's `a_slot_routes_whichever_parameter_pins_it` and
//!     `a_woven_slot_call_that_waits_keeps_its_slots`.
//!   * the bridge:
//!     - `lower_leaf` back on `alloc_from_value` — `an_operation_run_by_the_bridge_queries_a_-
//!       rule_with_its_parameter` and `a_bridged_parameter_aligns_in_a_union` (a conditional
//!       row, `malformed_query`);
//!     - `goal_value_to_term` back on `alloc_from_value` — `a_bridged_parameter_lowers_inside_-
//!       a_negation`;
//!     - `rename_query_vars` refusing a ground `Node` — `a_bridged_parameter_aligns_in_a_union`
//!       (a debug-build panic);
//!     - `value_to_term`'s `Node` arm on the asserting `occurrence_to_term` —
//!       `a_bridged_control_form_operand_is_refused_loudly` (a debug-build panic).
//!
//! The CONTROL rows pass either way, by design, and each says why at its site.

use anthill_core::eval::Value;

/// `src` — one namespace — with `rules` added before its closing `end`: a row whose extra
/// declarations would refuse the shared fixture's load keeps them out of the other rows.
fn extended(src: &str, rules: &str) -> String {
    let body = src.trim_end().strip_suffix("end").expect("the fixture ends its namespace");
    format!("{body}{rules}end\n")
}

// ── (b) WI-670's open-time refutation and the functional-relation view ─────────────────────

/// A non-reorderable builtin (`ground`) on a caller variable, beside an UNWOVEN
/// functional-relation goal: `Util.sign(?x, 5, ?c)` is `sign`'s arity+1 view, which no clause
/// is written for and `step_init` answers off the discrimination tree.
const OPENING: &str = r#"
namespace wiprva2.opening
  import anthill.prelude.Int64

  sort Util
    operation sign(x: Int64, y: Int64) -> Int64 = Int64.sub(x, y)
  end

  entity num(n: Int64)
  fact num(n: 1)

  rule r(?x, ?c) :- anthill.reflect.ground(?x), Util.sign(?x, 5, ?c)
  -- the clause is OPENED before its caller variable is bound
  rule q(?c) :- r(?x, ?c), num(n: ?x)
  -- the same conjunction the other way round
  rule q2(?c) :- num(n: ?x), r(?x, ?c)
  -- nothing ever binds `?x`
  rule alone(?c) :- r(?x, ?c)

  -- a GROUND conjunct at opening: false (`sign(1, 5)` is -4) and true
  rule falseAt(?x, ?y) :- anthill.reflect.ground(?x), Util.sign(?y, 5, 0)
  rule trueAt(?x, ?y) :- anthill.reflect.ground(?x), Util.sign(?y, 5, -4)
  rule falseOne(?r) :- falseAt(?x, 1), ?r <=> 1
  rule trueOne(?r) :- trueAt(?x, 1), ?r <=> 1
  rule someFalse() :- falseAt(?z, 1)
  rule noneFalse(?r) :- not someFalse(), ?r <=> 1
end
"#;

/// (b) THE CASE. `r` opens with `?x` unbound, and WI-670's pre-check delays the whole clause on
/// its `ground(?x)` — after asking whether another conjunct REFUTES the clause regardless. The
/// functional-relation goal has zero discrim candidates, and that was read as the refutation:
/// `q` answered nothing where `q2`, the swapped conjunction, answers `-4`. The goal is answered
/// by the WI-938 hook, off the tree, so zero candidates refute nothing: the clause delays,
/// `num` binds `?x`, and `q` answers `-4` too. Where nothing binds `?x` the delayed clause is an
/// honest CONDITIONAL row, not a refutation. FAILS with the goal refuted on its zero
/// candidates: `q` and `alone` are both empty.
#[test]
fn a_functional_relation_goal_is_no_refutation_at_opening() {
    let mut kb = crate::common::load_kb_with(OPENING);
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "wiprva2.opening.q"),
        Some(-4),
        "`sign(1, 5)`, once `num` bound the caller variable the clause delayed on",
    );
    let rows = crate::common::query_unary(&mut kb, "wiprva2.opening.alone");
    assert!(
        rows.len() == 1 && !rows[0].1,
        "`?x` is never bound: one conditional row, not a refutation; got {rows:?}",
    );
}

/// (b) CONTROL — passes either way, BY DESIGN: the generator runs first, so `r` opens with
/// `?x` bound and no pre-check is asked.
#[test]
fn the_conjunction_the_other_way_round_answers_as_before() {
    let mut kb = crate::common::load_kb_with(OPENING);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.opening.q2"), Some(-4));
}

/// (b) — and a GROUND functional-relation conjunct is still judged: it is EVALUATED, as the
/// hook would evaluate it, and refutes the clause when its value is not the result column.
/// `falseAt(?x, 1)` holds `sign(1, 5, 0)`, false — refuted at opening, so `falseOne` is empty
/// and `noneFalse` holds definitely; `trueAt(?x, 1)` holds `sign(1, 5, -4)`, true — the clause
/// delays on `?x`, which nothing binds, and `trueOne` is one CONDITIONAL row. FAILS with the
/// goal skipped unevaluated: `falseOne` is a phantom conditional row and `noneFalse` is
/// undecided. (Before this ticket the zero candidates refuted BOTH clauses — right for the
/// false one by accident, and wrong for the true one.)
#[test]
fn a_ground_functional_relation_conjunct_is_evaluated_at_opening() {
    let mut kb = crate::common::load_kb_with(OPENING);
    let rows = crate::common::query_unary(&mut kb, "wiprva2.opening.falseOne");
    assert!(rows.is_empty(), "`sign(1, 5)` is -4, not 0: refuted at opening; got {rows:?}");
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.opening.noneFalse"), Some(1));
    let rows = crate::common::query_unary(&mut kb, "wiprva2.opening.trueOne");
    assert!(
        rows.len() == 1 && !rows[0].1,
        "`sign(1, 5)` is -4: the clause delays on `?x`, one conditional row; got {rows:?}",
    );
}

// ── (c) the requirement guard asks the provision ───────────────────────────────────────────

/// `Conv[A, B]` has a carrier at each of its two parameters, and its only provision is filed
/// under `Meters`, binding `B = String`.
const MULTI: &str = r#"
namespace wiprva2.multi
  import anthill.prelude.{Int64, String}

  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
  end

  sort Meters
    entity m(v: Int64)
    provides Conv[A = Meters, B = String]
    operation conv(a: Meters, b: String) -> Int64 = 7
  end

  -- every carrier unknown at load: the call is woven, and its read guards at run time
  rule toN(?x, ?u, ?r) :- Conv.conv(?x, ?u, ?r)
  rule go(?r) :- toN(m(v: 3), "km", ?r)
  -- no provision binds `B = Int64`
  rule noRow(?r) :- toN(m(v: 3), 5, ?r)
end
"#;

/// (c) THE CASE. `toN`'s call is woven, so its inferred read guards the call at run time — and
/// the guard asked EACH carrier to provide `Conv`: `Meters` does, `String` never will (it is the
/// provision's second binding, not a provider), so the read DontFired and `go` answered
/// nothing where value dispatch answers `7`. The guard now asks whether a provision binds
/// `A = Meters, B = String`, and one does. FAILS with the per-carrier question restored for
/// several parameters: `go` is empty.
#[test]
fn a_provision_at_several_parameters_answers_a_woven_call() {
    let mut kb = crate::common::load_kb_with(MULTI);
    assert_eq!(
        crate::common::body_calls(&kb, "wiprva2.multi.toN"),
        vec![
            ("conv".to_string(), true, Vec::new()),
            ("find_dictionary".to_string(), false, Vec::new()),
        ],
        "`toN`'s call is woven behind an inferred read — the read is what guards it",
    );
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.multi.go"), Some(7), "`Meters.conv`");
}

/// (c) CONTROL — passes either way, BY DESIGN, and guards the other direction: the question is
/// the PROVISION at the carriers, not "some carrier provides". No provision binds `B = Int64`,
/// so the read is refused and `noRow` is empty, definitely. A guard that asked only the first
/// carrier (`Meters` provides `Conv`) would fire, and the fetch at `(Meters, Int64)` would come
/// back undecided — one CONDITIONAL row where there is no answer (measured).
#[test]
fn a_call_no_provision_binds_is_refused() {
    let mut kb = crate::common::load_kb_with(MULTI);
    let rows = crate::common::query_unary(&mut kb, "wiprva2.multi.noRow");
    assert!(rows.is_empty(), "no provision of `Conv` at `(Meters, Int64)`; got {rows:?}");
}

/// (c) THE LOAD-TIME FACE. With both carriers concrete at load, WI-642's check asked each to
/// provide `Conv` and REFUSED the program: "`String` provides no `Conv`, and this clause
/// declares no `requires(Conv[…])`". The provision at `(Meters, String)` is the instance the
/// call dispatches to, so the program loads and `both` answers `7`. FAILS with the per-carrier
/// question restored: the load is refused.
#[test]
fn a_call_whose_carriers_are_known_at_load_is_not_refused() {
    let src = extended(MULTI, "  rule both(?r) :- Conv.conv(m(v: 3), \"km\", ?r)\n");
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.multi.both"), Some(7), "`Meters.conv`");
}

/// (c) — a refusal the per-carrier question made is KEPT, on the KNOWN carriers: `early` puts
/// `String` at `A`, which no provision binds, so its call is refused at load though its carrier
/// at `B` is unknown there — a carrier not read yet cannot create a provision. (Before this
/// ticket the per-carrier question refused it too, as "`String` provides no `Conv`".) FAILS
/// with the question suspending while ANY carrier is unknown: it loads clean.
#[test]
fn known_carriers_no_provision_binds_are_refused_at_load() {
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&extended(
            MULTI,
            "  rule early(?x, ?r) :- ?u <=> \"km\", Conv.conv(?u, ?x, ?r)\n",
        )),
        &["no provision of `wiprva2.multi.Conv` binds `A = anthill.prelude.String`"],
    );
}

/// (c) — a refusal about a COMBINATION says so. `Conv.conv(5, "km")` is refused because no
/// provision binds `A = Int64, B = String` — `String` at `B` is exactly what `Meters`' row
/// binds. The per-carrier sentence named whichever carrier was read last: "`String` provides no
/// `Conv` … Add a `provides Conv[…]` for `String`", a repair that is not one. FAILS with a
/// several-parameter refusal rendered as the per-carrier sentence.
#[test]
fn a_refusal_names_the_carriers_no_provision_binds() {
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&extended(
            MULTI,
            "  rule bad(?r) :- Conv.conv(5, \"km\", ?r)\n",
        )),
        &["no provision of `wiprva2.multi.Conv` binds `A = anthill.prelude.Int64, B = \
           anthill.prelude.String`"],
    );
}

/// A CONVERSION row — `Conv2`'s parameters forwarded, no operation supplied, the stdlib idiom
/// `Ord provides WeakOrd[T = T]` one parameter wider.
const CONV2: &str = "  sort Conv2\n    sort A = ?\n    sort B = ?\n    provides Conv[A = A, B = B]\n  end\n";

/// (c) — a CONVERSION is no instance. `Conv2 provides Conv[A = A, B = B]` says "hold a `Conv2`
/// and you can obtain a `Conv`"; nothing is a `Conv2`, and the provider search skips the row.
/// Read as a provision with only variables in it, it admitted EVERY carrier pair: `noRow`
/// became one conditional row (the guard fired, the fetch found no candidate), and
/// `Conv.conv(5, 6)` loaded where it is refused (and a `@[simp]` law rewrote it — measured).
/// FAILS with `is_conversion_row` dropped from the provision question: `noRow` is a
/// conditional row, and `bad` loads clean.
#[test]
fn a_conversion_row_is_no_instance() {
    let mut kb = crate::common::load_kb_with(&extended(MULTI, CONV2));
    let rows = crate::common::query_unary(&mut kb, "wiprva2.multi.noRow");
    assert!(rows.is_empty(), "no provision of `Conv` at `(Meters, Int64)`; got {rows:?}");
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&extended(
            MULTI,
            &format!("{CONV2}  rule bad(?r) :- Conv.conv(5, 6, ?r)\n"),
        )),
        &["no provision of `wiprva2.multi.Conv` binds `A = anthill.prelude.Int64, B = \
           anthill.prelude.Int64`"],
    );
}

/// `Conv[A, B]` and a caller of its `conv` whose carriers are unknown at load, with `rows`
/// supplying the provisions and `rules` the queries.
fn conv_program(ns: &str, rows: &str, rules: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String}}\n  \
         sort Conv\n    sort A = ?\n    sort B = ?\n    operation conv(a: A, b: B) -> Int64\n  end\n\
         {rows}  rule toN(?x, ?u, ?r) :- Conv.conv(?x, ?u, ?r)\n{rules}end\n"
    )
}

/// (c) — a STRUCTURAL binding admits no carrier: a carrier is a sort, never an arrow. With
/// `Meters provides Conv[A = Meters, B = (Int64) -> Int64]`, `toN(m(v: 3), "km")` has no
/// instance, and `go` is empty. FAILS with such a binding admitting any carrier: the guard
/// fires, the fetch finds nothing, and `go` is one conditional row.
#[test]
fn a_structural_binding_admits_no_carrier() {
    let src = conv_program(
        "wiprva2.arrow",
        "  sort Meters\n    entity m(v: Int64)\n    provides Conv[A = Meters, B = (Int64) -> Int64]\n    \
         operation conv(a: Meters, b: (Int64) -> Int64) -> Int64 = 7\n  end\n",
        "  rule go(?r) :- toN(m(v: 3), \"km\", ?r)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    let rows = crate::common::query_unary(&mut kb, "wiprva2.arrow.go");
    assert!(rows.is_empty(), "`String` is no `(Int64) -> Int64`; got {rows:?}");
}

/// (c) — one provider variable binds its parameters ALIKE. `Same provides Conv[A = X, B = X]`
/// serves `(Int64, Int64)` — `goSame` answers `1` — and not `(Int64, String)`, so `goMixed` is
/// empty. FAILS with each parameter judged alone: `goMixed` is one conditional row.
#[test]
fn a_variable_binds_its_parameters_alike() {
    let src = conv_program(
        "wiprva2.same",
        "  sort Same\n    sort X = ?\n    provides Conv[A = X, B = X]\n    \
         operation conv(a: X, b: X) -> Int64 = 1\n  end\n",
        "  rule goMixed(?r) :- toN(3, \"km\", ?r)\n  rule goSame(?r) :- toN(3, 4, ?r)\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.same.goSame"), Some(1));
    let rows = crate::common::query_unary(&mut kb, "wiprva2.same.goMixed");
    assert!(rows.is_empty(), "`X` is not both `Int64` and `String`; got {rows:?}");
}

/// (c) — a carrier at a parameter that is not the spec's CARRIER parameter asks the provision
/// too, though it is the call's only one. `Conv.tag(b: B)` stands at `B`: the clause names the
/// instance, `require[Conv[A = Meters, B = String]]`, and the read's guard asked `String` to
/// provide `Conv`, refused, and failed the clause where the operation-body twin answers `3`.
/// FAILS with the question routed on "carriers at two distinct parameters": `t` is empty.
#[test]
fn a_carrier_at_a_non_carrier_parameter_asks_the_provision() {
    const TAG: &str = r#"
namespace wiprva2.tag
  import anthill.prelude.{Int64, String}

  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
    operation tag(b: B) -> Int64
  end

  sort Meters
    entity m(v: Int64)
    provides Conv[A = Meters, B = String]
    operation conv(a: Meters, b: String) -> Int64 = 7
    operation tag(b: String) -> Int64 = 3
  end

  rule t(?r) :- require[Conv[A = Meters, B = String]], Conv.tag("km", ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(TAG);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.tag.t"), Some(3), "`Meters.tag`");
}

/// (c) — a WITNESS-provided carrier is KNOWN at load. `W provides Conv[A = Leaf, B = Int64]`
/// beside `Meters`' row, and `bad` calls `Conv.conv(leaf(), "s")`: no provision binds `(Leaf,
/// String)`. The load reader filed `Leaf` as unknown (P7VP4's third review round), `B = String`
/// alone matched `Meters`' row, and the call LOADED — and answered `9`, `W.conv` run at
/// `(Leaf, String)`. FAILS with the witness filter restored: it loads and answers `9`.
#[test]
fn a_witness_carrier_is_known_at_load() {
    let src = extended(
        MULTI,
        "  sort Leaf\n    entity leaf\n  end\n  \
         sort W\n    provides Conv[A = Leaf, B = Int64]\n    operation conv(a: Leaf, b: Int64) -> Int64 = 9\n  end\n  \
         rule bad(?r) :- ?u <=> \"s\", Conv.conv(leaf(), ?u, ?r)\n",
    );
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&src),
        &["no provision of `wiprva2.multi.Conv` binds `A = wiprva2.multi.Leaf, B = \
           anthill.prelude.String`"],
    );
}

/// (c) — the per-carrier question refuses a known carrier that provides nothing WHATEVER THE
/// ORDER: a carrier not read yet cannot rescue it. `Plain` provides no `Desc`; `first` puts it
/// before the unknown `?x`, `second` after. It returned at the first carrier it read, so
/// `second` waited (`Suspend`, no refusal) where `first` was refused. FAILS with the question
/// returning at the first carrier it reads: only `first` is refused.
#[test]
fn the_per_carrier_question_refuses_in_either_order() {
    const DESC: &str = r#"
namespace wiprva2.order
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation same(a: T, b: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation same(a: Leaf, b: Leaf) -> Int64 = 1
  end

  sort Plain
    entity plain
  end

  rule first(?x, ?r) :- Desc.same(plain(), ?x, ?r)
  rule second(?x, ?r) :- Desc.same(?x, plain(), ?r)
end
"#;
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(DESC),
        &[
            "`wiprva2.order.Plain` provides no `wiprva2.order.Desc`",
            "`wiprva2.order.Plain` provides no `wiprva2.order.Desc`",
        ],
    );
}

/// (c) — a stdlib spec whose operation has carriers at two parameters:
/// `PersistentCollection.insert(c: C, elem: Element)`. `List`'s provision binds `C = List` and
/// leaves `Element` to its own type variable, so `insert([1, 2], 3)` has an instance; asking
/// `Int64` to provide `PersistentCollection` refused the program at load. FAILS with the
/// per-carrier question restored for several parameters: the load is refused.
#[test]
fn a_stdlib_spec_with_carriers_at_two_parameters_answers() {
    const PC: &str = r#"
namespace wiprva2.pc
  import anthill.prelude.{Int64, List, PersistentCollection}

  rule r(?r) :- PersistentCollection.insert([1, 2], 3, ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(PC);
    let rows = crate::common::shown_rows(&mut kb, "wiprva2.pc.r");
    assert_eq!(rows.len(), 1, "one answer: {rows:?}");
    assert!(rows[0].1 && rows[0].0.contains('3'), "`3` prepended onto `[1, 2]`: {rows:?}");
}

// ── (e) the slot route follows the typer's instantiation ───────────────────────────────────

/// (e) — `cmp2[A](x: A, y: A)` requires `Cmp[T = A]`, `Circle provides Shape`, and each of
/// `Circle` and `Shape` has its own `Cmp`: `Circle`'s answers `1`, `ShapeCmp`'s `2`.
const ROUTE: &str = r#"
namespace wiprva2.route
  import anthill.prelude.{Int64, Error, EmptyStream, Relation, Option}

  sort Cmp
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end

  sort Shape
  end

  sort Circle
    provides Shape
    entity circle
    provides Cmp[T = Circle]
    operation cmp(a: Circle, b: Circle) -> Int64 = 1
  end

  sort ShapeCmp
    provides Cmp[T = Shape]
    operation cmp(a: Shape, b: Shape) -> Int64 = 2
  end

  sort Util
    operation cmp2[A](x: A, y: A) -> Int64 requires Cmp[T = A] = Cmp.cmp(x, y)
  end

  rule via(?a, ?b, ?c) :- Util.cmp2(?a, ?b, ?c)

  sort Driver
    -- a citation at `(Shape, Circle)`, from a caller holding `Cmp[T = Shape]`
    operation cite(c: Circle, s: Shape) -> Int64 effects {Error, Error[EmptyStream]}
      requires Cmp[T = Shape] = via(s, c).head.c
    -- the same call in an operation body: the typer instantiates it
    operation body(c: Circle, s: Shape) -> Int64 = Util.cmp2(s, c)
    operation goCite() -> Int64 effects {Error, Error[EmptyStream]} = cite(circle(), circle())
    operation goBody() -> Int64 = body(circle(), circle())
  end
end
"#;

fn drive_int(src: &str, entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// (e) THE CASE, in the order the typer accepts. The operation body types `cmp2(s, c)` at
/// `A = Shape` and answers `2`, `ShapeCmp`'s. The citation's slot route pinned `A = Shape` off
/// `x`, then tested `y`'s `Circle` against the WRITTEN parameter `A` rather than the pinned
/// `Shape`, refused, and routed nothing — so the slot was derived from the values, both
/// circles, and the rule answered `1`, `Circle`'s. Each argument is now tested against its
/// parameter as pinned, and the route is the caller's `Cmp[T = Shape]`. FAILS with HEAD's check
/// restored (a failed unification tested against the written parameter): `1`.
#[test]
fn a_slot_route_follows_the_typers_instantiation() {
    assert_eq!(
        (
            drive_int(ROUTE, "wiprva2.route.Driver.goCite"),
            drive_int(ROUTE, "wiprva2.route.Driver.goBody"),
        ),
        (2, 2),
        "the citation routes the dictionary the typer instantiates for the same call",
    );
}

/// (e) CONTROL — passes either way, BY DESIGN: it pins why the order the ticket named is not
/// reachable. At `(Circle, Shape)` the typer itself refuses — the citation's column typing and
/// the operation-body call both take `A` from the FIRST argument, and `Shape` is no `Circle` —
/// so no slot route is ever asked at that order. Instantiating a repeated type parameter at the
/// JOIN of its arguments, which would admit both orders, is the typer's question and
/// WI-20260926-NEKR0's; that change flips this row.
#[test]
fn the_other_order_is_refused_by_the_typer() {
    let src = extended(
        ROUTE,
        "  sort Driver2\n    \
         operation citeCS(c: Circle, s: Shape) -> Int64 effects {Error, Error[EmptyStream]}\n      \
         requires Cmp[T = Shape] = via(c, s).head.c\n    \
         operation bodyCS(c: Circle, s: Shape) -> Int64 = Util.cmp2(c, s)\n  \
         end\n",
    );
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&src),
        &["column `b` has an incompatible type", "expected Circle, got Shape"],
    );
}

/// (e) — the route asks the typer's own conformance question, so an argument the typer accepts
/// through a CONVERSION routes as the typer instantiates it. `f[A, B](x: Option[T = A], y: A,
/// …)` given a bare `Shape` for `x` through a typed column: the operation body wraps it
/// (WI-408's some-coercion) and answers `2`; the route's bare subtype test refused `Shape`
/// against `Option[T = Shape]`, routed nothing, and the citation answered `1`, the value's
/// own. FAILS with a bare `types_compatible` in the route: `1`.
#[test]
fn a_converted_argument_routes_as_the_typer_instantiates() {
    let src = extended(
        ROUTE,
        "  sort Util2\n    \
         operation f[A, B](x: Option[T = A], y: A, z: B) -> Int64 requires Cmp[T = A] = Cmp.cmp(y, y)\n  \
         end\n  \
         rule viaOpt(?a: Shape, ?b, ?z, ?c) :- Util2.f(?a, ?b, ?z, ?c)\n  \
         sort Driver3\n    \
         operation cite(s: Shape, t: Shape) -> Int64 effects {Error, Error[EmptyStream]}\n      \
         requires Cmp[T = Shape] = viaOpt(s, t, 0).head.c\n    \
         operation body(s: Shape, t: Shape) -> Int64 = Util2.f(s, t, 0)\n    \
         operation goCite() -> Int64 effects {Error, Error[EmptyStream]} = cite(circle(), circle())\n    \
         operation goBody() -> Int64 = body(circle(), circle())\n  \
         end\n",
    );
    assert_eq!(
        (
            drive_int(&src, "wiprva2.route.Driver3.goCite"),
            drive_int(&src, "wiprva2.route.Driver3.goBody"),
        ),
        (2, 2),
        "the citation routes `ShapeCmp`, as the typer instantiates `A = Shape`",
    );
}

// ── the SLD→eval bridge: an operation run from a rule body ─────────────────────────────────

/// An operation evaluated FROM A RULE BODY whose body queries a rule with its own parameter.
const BRIDGE: &str = r#"
namespace wiprva2.bridge
  import anthill.prelude.{Int64, Error, EmptyStream, Relation}
  import anthill.prelude.Relation.{union}

  sort Circle
    entity circle
  end

  rule same(?a, ?c) :- ?c <=> ?a
  rule one(?a, ?c) :- ?c <=> 1
  rule seven(?c) :- ?c <=> 7
  rule keep(?f, ?c) :- ?c <=> 1

  sort Driver
    operation fInt(x: Int64) -> Int64 effects {Error, Error[EmptyStream]} = same(x).head.c
    operation fCircle(x: Circle) -> Int64 effects {Error, Error[EmptyStream]} = one(x).head.c
    operation uniR(x: Int64) -> Int64 effects {Error, Error[EmptyStream]} =
      seven.union(same(x)).head.c
    operation g(f: (x: Int64) -> Int64) -> Int64 effects {Error, Error[EmptyStream]} =
      keep(f).head.c
  end

  rule rInt(?r) :- ?r <=> Driver.fInt(3)
  rule rCircle(?r) :- ?r <=> Driver.fCircle(circle())
  rule rUniR(?r) :- ?r <=> Driver.uniR(4)
  rule rLambda(?r) :- ?r <=> Driver.g(lambda (x: Int64) -> Int64.add(x, 1))
end
"#;

/// THE BRIDGE CASE. The SLD→eval bridge hands an operation each operand on the carrier the
/// resolver proved it on — a rule-body `3` or `circle()` is an occurrence (WI-20260827-3ZNBC) —
/// so `same(x)` built the query `same(<occurrence>, ?c)`, and lowering it refused the nested
/// occurrence: "cannot lower Value::Node into a KB term". The call raised, and each rule was
/// one conditional row with the call unevaluated. The query leaf now lowers through the
/// occurrence-aware converter. FAILS with `lower_leaf` back on `alloc_from_value`.
#[test]
fn an_operation_run_by_the_bridge_queries_a_rule_with_its_parameter() {
    let mut kb = crate::common::load_kb_with(BRIDGE);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.bridge.rInt"), Some(3), "`same(3)`");
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.bridge.rCircle"), Some(1), "`one(circle())`");
}

/// CONTROL — passes either way, BY DESIGN: called from the interpreter, the operand is a native
/// value and the query always lowered.
#[test]
fn the_same_operation_called_from_the_interpreter_answers_as_before() {
    let mut interp = crate::common::interp_for(BRIDGE);
    match interp.call("wiprva2.bridge.Driver.fInt", &[Value::Int(3)]) {
        Ok(Value::Int(n)) => assert_eq!(n, 3),
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// The bridge, at the query lowerer's OTHER term boundary: a bridged parameter used as a
/// NEGATED goal inside a disjunction and inside a multi-goal negation, which synthesize a
/// conjunction rule (`goal_value_to_term`). Each raised "cannot lower Value::Node" and was a
/// conditional row, where the eval-called twin answers `1`. FAILS with `goal_value_to_term`
/// back on `alloc_from_value`.
#[test]
fn a_bridged_parameter_lowers_inside_a_negation() {
    const NEG: &str = r#"
namespace wiprva2.neg
  import anthill.prelude.{Stream, Option, Error, Int64}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{as_term, ResolveStreamFailure}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query, negation, disjunction, conjunction}

  sort Nums
    entity num(n: Int64)
  end
  fact num(n: 1)
  fact num(n: 2)

  sort Driver
    -- or(not(g), num(2))
    operation orNot(g: Nums) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), disjunction(left: negation(query: pattern_query(term: as_term(g))),
                                                  right: pattern_query(term: as_term(num(n: 2))))))
        case none() -> 0
        case some(_) -> 1
    -- not(not(g), num(2))
    operation notConj(g: Nums) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), negation(query: conjunction(left: negation(query: pattern_query(term: as_term(g))),
                                                                  right: pattern_query(term: as_term(num(n: 2)))))))
        case none() -> 0
        case some(_) -> 1
  end

  rule rOrNot(?r) :- ?r <=> Driver.orNot(num(n: 1))
  rule rNotConj(?r) :- ?r <=> Driver.notConj(num(n: 1))
end
"#;
    let mut kb = crate::common::load_kb_with(NEG);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.neg.rOrNot"), Some(1));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.neg.rNotConj"), Some(1));
}

/// The bridge, at `Relation.union`'s column alignment: `seven.union(same(x))` renames the right
/// operand's query, which holds the bridged parameter — and `rename_query_vars` refused the
/// occurrence as Internal, a debug-build PANIC, where the eval-called twin answers `7`. A
/// GROUND occurrence names no column variable; it passes through. FAILS with a ground `Node`
/// refused there: the test panics.
#[test]
fn a_bridged_parameter_aligns_in_a_union() {
    let mut kb = crate::common::load_kb_with(BRIDGE);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wiprva2.bridge.rUniR"), Some(7));
}

/// The bridge with an operand that has NO term form — a lambda — is refused LOUDLY: the query
/// raises (`malformed_query`), and the rule is one conditional row, the call unevaluated. The
/// lowering reached `occurrence_to_term`'s `debug_assert!` — a debug-build PANIC, and a `⊥`
/// query in release. FAILS with `value_to_term`'s `Node` arm on the asserting converter: the
/// test panics.
#[test]
fn a_bridged_control_form_operand_is_refused_loudly() {
    let mut kb = crate::common::load_kb_with(BRIDGE);
    let rows = crate::common::query_unary(&mut kb, "wiprva2.bridge.rLambda");
    assert!(
        rows.len() == 1 && !rows[0].1,
        "the call raised: one conditional row, never a definite answer; got {rows:?}",
    );
}
