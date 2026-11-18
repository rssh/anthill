//! WI-20261115-YR3N7 — A TYPED COLUMN CHECKS A BOUND VALUE; IT DOES NOT GENERATE ONE.
//!
//! A sort's derived domain was ONE clause whose body proposed each constructor to the value in
//! turn — `List.domain(?x) :- …, push_choice(unify(?x, nil), (unify(?x, cons(…)), …),
//! __refined_domain(?x, …))` — so checking a ground value ran the generator over every piece of
//! it: `nil` refuted, `cons` matched, the refining case left on the search, untried, at every
//! cell. It is now derived ONE CLAUSE PER CONSTRUCTOR, the constructor in the head (proposal 060
//! §2.3, "The head decides the mode"): a bound value selects the one clause its constructor
//! heads, and an unbound one matches every head in clause order. Every field is filled through
//! the dispatching `apply_domain`, which costs neither depth nor fuel, and a value of a sort that
//! REFINES the asked one is the case the call applies (`KnowledgeBase::lower_apply_domain`),
//! filled at its own sort with a dictionary put together from the handed one's slots.
//!
//! MEASURED on the CLI (the fewest `--max-steps` that answer, by bisection; first answer / the
//! search exhausted), the ticket's fixture: a typed `List[T = Product]` of n elements cost
//! 13 + 27n / 25 + 38n before, and costs 8 + 10n / 11 + 14n now — the clauses written by hand
//! one per constructor (`ldom` below) cost 5 + 10n / 7 + 14n. The ticket's two-product,
//! two-order state: 177 / 281 before, 73 / 105 now.
//!
//! BACK-OUT, measured 2026-11-18 one axis at a time over this file, `wi_sxz3g`, `wi_j9ssg`,
//! `wi743`, `wi_shed7`, `wi_wt8wg`, `wi_5g28a_sort_domain` and `wi_atvc1` (97 rows), each a
//! temporary mutation in one build, removed:
//!  * [W] the tree before (HEAD's sources, these tests) — `a_checked_list_costs…`,
//!    `a_ground_check_leaves_no_case_untried`, and SXZ3G's two order rows. Row 1 of the ticket
//!    (`a_small_state_is_checked_at_the_default_limits`) passes there BY DESIGN since
//!    WI-20261115-0WT09: the default depth counts nesting, and the check is as deep as the value
//!    is nested in either shape;
//!  * [F] the dispatch charged a step of fuel — `a_checked_list_costs…` alone;
//!  * [R] a fill read a marker bound run instead of dropped — `a_checked_list_costs…` alone;
//!  * [C] the refining case off at the call — `a_refining_value_is_filled_at_its_own_sort`,
//!    `a_refinements_instance_is_checked_whole`, `wi_j9ssg`'s two holding rows and `wi_atvc1`'s
//!    `a_callers_wider_pattern_reaches_a_reify_through_a_rule`;
//!  * [T] a parameter's later slot left uncompared — `a_refinements_instance_is_checked_whole`
//!    alone;
//!  * [H] a refining sort with no domain admitted without its conformance check — NO ROW, by
//!    design: a value a constructor heads always conforms to its own sort's top type, so the
//!    two answer alike today; the check keeps the path before this ticket's reading, under
//!    which a value whose type is not decided yet waits;
//!  * [N] a typed head's ground bound filled by name where it has no conditions —
//!    `wi_j9ssg::a_refining_value_is_in_the_refined_domain` (the call's case never runs);
//!  * [S] the clause-order sort off (facts first, the index's map order inside) — 12 in each of
//!    two runs, the set moving with the map's seed: `an_unbound_column_generates_in_declaration_
//!    order`, four of `wi743` (declaration order, fairness, a base constructor declared last, an
//!    indeterminate bound), four or five of `wi_shed7`, `wi_wt8wg`'s column row in one run, and
//!    SXZ3G's two;
//!  * [O] a derived fill's candidates in facts-first order — `an_unbound_column_generates_in_
//!    declaration_order` alone.
//!
//! The controls (`the_controls_refuse_and_bind_as_before`, `a_bound_value_at_a_rigid_type_is_
//! checked`) pass under every axis: they are what the change must not move.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::{ResolveConfig, ResolveStats};
use anthill_core::kb::KnowledgeBase;

use crate::common::{definite_unary, load_kb_with, query_pattern_term};

const SHOP: &str = r#"
namespace yr3n7
  import anthill.prelude.{List, Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.kernel.{domain}
  enum OrderStatus
    entity CREATED
    entity PAID
  end
  entity Product(id: Int64, price: Int64)
  entity Order(id: Int64, status: OrderStatus, total: Int64)
  entity S(products: List[T = Product], orders: List[T = Order])
  fact member(?x, cons(head: ?x, tail: ?))
  rule member(?x, cons(head: ?, tail: ?t)) :- member(?x, ?t)
  rule has_order(?s: S, ?o: Order) :- ?s <=> S(orders: ?os), member(?o, ?os)
  operation st() -> S = S(products: [Product(1, 10), Product(1, 20)],
                          orders: [Order(1, PAID, 5), Order(2, CREATED, 0)])
  operation big() -> S = S(
    products: [Product(1, 10), Product(2, 10), Product(3, 10), Product(4, 10), Product(5, 10),
               Product(6, 10), Product(7, 10), Product(8, 10), Product(9, 10), Product(10, 10),
               Product(11, 10), Product(12, 10), Product(13, 10), Product(14, 10), Product(15, 10),
               Product(16, 10), Product(17, 10), Product(18, 10), Product(19, 10), Product(20, 10)],
    orders: [Order(1, PAID, 5), Order(2, PAID, 5), Order(3, PAID, 5), Order(4, PAID, 5),
             Order(5, PAID, 5), Order(6, PAID, 5), Order(7, PAID, 5), Order(8, PAID, 5),
             Order(9, PAID, 5), Order(10, PAID, 5), Order(11, PAID, 5), Order(12, PAID, 5),
             Order(13, PAID, 5), Order(14, PAID, 5), Order(15, PAID, 5), Order(16, PAID, 5),
             Order(17, PAID, 5), Order(18, PAID, 5), Order(19, PAID, 5), Order(20, CREATED, 0)])
  rule q_full :- ?s <=> st(), has_order(?s, Order(2, CREATED, 0))
  rule q_big :- ?s <=> big(), has_order(?s, Order(20, CREATED, 0))
  rule q_part(?id) :- ?s <=> st(), has_order(?s, Order(id: ?id, status: CREATED))

  -- the same domain written by hand, ONE CLAUSE PER CONSTRUCTOR, the constructor in the head
  rule intdom(?x) :- domain(?x, Int64)
  rule pdom(Product(id: ?i, price: ?p)) :- intdom(?i), intdom(?p)
  fact ldom(nil)
  rule ldom(cons(head: ?h, tail: ?t)) :- ldom(?t), pdom(?h)
  rule only_lp(?l: List[T = Product]) :- true
  rule i1 :- ldom([Product(1, 2)])
  rule i2 :- ldom([Product(1, 2), Product(3, 4)])
  rule i4 :- ldom([Product(1, 2), Product(3, 4), Product(5, 6), Product(7, 8)])
  rule t1 :- only_lp([Product(1, 2)])
  rule t2 :- only_lp([Product(1, 2), Product(3, 4)])
  rule t4 :- only_lp([Product(1, 2), Product(3, 4), Product(5, 6), Product(7, 8)])

  enum Sw
    entity ON
    entity OFF
  end
  entity C(n: Int64, s: Sw)
  entity A(n: Int64)
  rule tc(?v: C) :- true

  -- a base constructor with a field declared before a nullary one
  sort Mix
    entity tagged(s: Sw)
    entity plain
  end
  rule mixes(?m: Mix) :- true
end
"#;

/// The ticket's row 7: a value built from a column of mixed types, which the guard in front of
/// the body accepts (it reads the top type alone) and the fill refuses.
const MIXED: &str = r#"
namespace yr3n7m
  import anthill.prelude.{List, Int64}
  entity Product(id: Int64, price: Int64)
  entity S(products: List[T = Product])
  fact h3(1)
  fact h3(Product(1, 2))
  rule mk3(?s) :- h3(?e), ?s <=> S(products: [?e])
  rule typed(?s: S) :- mk3(?s)
end
"#;

/// Refining values reached past the guard in front of the body, which reads a non-parametric
/// sort's top type alone: through a list element, from a column of mixed types (the ticket's
/// row 7 device). `Twin[Q]` refines `Pair` at ONE type for both of its parameters; `Other2`
/// refines `Base` with a field no domain fills (a tuple), so it has no domain of its own.
const REFINE: &str = r#"
namespace yr3n7f
  import anthill.prelude.{List, Int64}
  sort Colour
    entity red
    entity green
  end
  sort Letter
    entity a
    entity b
  end
  sort Pair
    sort A = ?
    sort B = ?
    entity pair(a: A, b: B)
  end
  sort Twin
    sort Q = ?
    requires Pair[A = Q, B = Q]
    entity twin(q: Q)
  end
  entity HL(ps: List[T = Pair[A = Colour, B = Letter]])
  entity HC(ps: List[T = Pair[A = Colour, B = Colour]])
  fact hp(twin(q: red))
  fact hp(pair(a: red, b: a))
  fact hp(pair(a: red, b: green))
  rule mkL(?h) :- hp(?e), ?h <=> HL(ps: [?e])
  rule mkC(?h) :- hp(?e), ?h <=> HC(ps: [?e])
  rule atL(?h: HL) :- mkL(?h)
  rule atC(?h: HC) :- mkC(?h)

  sort Base
    entity base
  end
  sort Other2
    requires Base
    entity o2(p: (Int64, Int64))
  end
  entity HB(bs: List[T = Base])
  fact hv(2)
  fact hv("s")
  rule mkB(?h) :- hv(?e), ?h <=> HB(bs: [o2(p: (1, ?e))])
  rule atB(?h: HB) :- mkB(?h)
end
"#;

/// 060 §2.3's rigid fixture, and the bound reading it states: `hasAt[X](v)` hands the caller's
/// dictionary to `el` with `?x` bound.
const RIGID: &str = r#"
namespace yr3n7r
  import anthill.prelude.{Int64, Error}
  import anthill.reflect.SortDomain
  sort Colour
    entity red
    entity green
    entity blue
  end
  sort Wrap[T]
    entity wrap(v: T)
    rule el(?x: T) :- true
  end
  sort Base
    entity base
  end
  sort Other
    requires Base
    entity other(n: Int64)
  end
  sort Wide
    sort W = ?
    entity wide(w: W)
  end
  sort Narrow2
    sort Q = ?
    requires Wide[W = Q]
    entity narrow2(q: Q)
  end
  sort Driver
    operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] =
      Wrap[T = X].el.takeN(9).length()
    operation hasAt[X](v: X) -> Int64 effects {Error} requires SortDomain[T = X] =
      Wrap[T = X].el(v).takeN(9).length()
    operation wrappedRed() -> Int64 effects {Error} = hasAt[X = Wrap[T = Colour]](wrap(v: red))
    operation wrappedBlue() -> Int64 effects {Error} = hasAt[X = Wrap[T = Colour]](wrap(v: blue))
    operation otherAtBase() -> Int64 effects {Error} = hasAt[X = Base](other(7))
    operation baseAtBase() -> Int64 effects {Error} = hasAt[X = Base](base)
    operation narrowAtWide() -> Int64 effects {Error} =
      hasAt[X = Wide[W = Colour]](narrow2(q: green))
    operation bases() -> Int64 effects {Error} = countAt[X = Base]()
    operation wraps() -> Int64 effects {Error} = countAt[X = Wrap[T = Colour]]()
  end
end
"#;

fn drive(entry: &str) -> Result<i64, String> {
    let mut interp = crate::common::interp_for(RIGID);
    match interp.call(&format!("yr3n7r.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => Ok(n),
        other => Err(format!("{other:?}")),
    }
}

/// The search of `pattern`, drained up to `max_solutions` (0: all), and its telemetry.
fn search(kb: &mut KnowledgeBase, pattern: &str, max_solutions: usize) -> (usize, ResolveStats) {
    let goal = query_pattern_term(kb, pattern);
    let config = ResolveConfig {
        max_solutions,
        ..ResolveConfig::default()
    };
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config);
    assert!(!stats.truncated, "`{pattern}` was truncated: {stats:?}");
    (solutions.iter().filter(|s| s.is_definite()).count(), stats)
}

/// Does `pattern` hold, definitely, at the default limits?
fn holds(kb: &mut KnowledgeBase, pattern: &str) -> bool {
    search(kb, pattern, 0).0 > 0
}

/// The ticket's row 1, and a state ten times larger, each answered at the DEFAULT depth and fuel.
/// Passes under [W] by design since WI-20261115-0WT09 (the module doc).
#[test]
fn a_small_state_is_checked_at_the_default_limits() {
    let mut kb = load_kb_with(SHOP);
    assert!(holds(&mut kb, "yr3n7.q_full"), "the two-product, two-order state holds the order");
    assert!(holds(&mut kb, "yr3n7.q_big"), "the twenty-product, twenty-order state holds it");
}

/// THE CASE: a typed `List[T = Product]` column costs, per element, exactly the steps the same
/// domain written by hand one clause per constructor does — a cell selects `cons`'s one clause,
/// a `Product` its one clause, the dispatch costs nothing and the dictionary the call hands in is
/// not read again. The constant differs (the column's guard and clause). FAILS under [W] (27 per
/// element), [F] (14) and [R] (11).
#[test]
fn a_checked_list_costs_what_a_clause_per_constructor_costs() {
    let mut kb = load_kb_with(SHOP);
    let mut steps = |q: &str| search(&mut kb, &format!("yr3n7.{q}"), 1).1.steps;
    let (i1, i2, i4) = (steps("i1"), steps("i2"), steps("i4"));
    let (t1, t2, t4) = (steps("t1"), steps("t2"), steps("t4"));
    let hand = (i4 - i2) / 2;
    assert_eq!(i2 - i1, hand, "the hand-written clauses cost the same per element: {i1} {i2} {i4}");
    assert_eq!(t2 - t1, hand, "typed {t1} {t2} {t4} against written {i1} {i2} {i4}");
    assert_eq!((t4 - t2) / 2, hand, "typed {t1} {t2} {t4} against written {i1} {i2} {i4}");
}

/// A GROUND CHECK LEAVES NO CASE UNTRIED: after its one answer the search asks no goal again —
/// every cell selected its one clause, and no alternative is left behind it. FAILS under [W]:
/// each piece's refining case is asked after the answer.
#[test]
fn a_ground_check_leaves_no_case_untried() {
    let mut kb = load_kb_with(SHOP);
    for q in ["t1", "t4", "i4"] {
        let pattern = format!("yr3n7.{q}");
        let (one, first) = search(&mut kb, &pattern, 1);
        let (all, drained) = search(&mut kb, &pattern, 0);
        assert_eq!((one, all), (1, 1), "{q}");
        assert_eq!(
            first.goals_asked, drained.goals_asked,
            "{q}: goals asked after the answer ({first:?} / {drained:?})"
        );
    }
}

/// THE CONTROLS, passing under every axis (the ticket's rows 4 and 7, and the partly bound
/// query): a wrong-type value is refused, a value built from a mixed column is refused by the
/// fill though the guard accepts it, and a partly bound order still binds its id.
#[test]
fn the_controls_refuse_and_bind_as_before() {
    let mut kb = load_kb_with(SHOP);
    assert!(holds(&mut kb, "yr3n7.tc(yr3n7.C(1, yr3n7.Sw.ON))"));
    assert!(!holds(&mut kb, "yr3n7.tc(yr3n7.A(1))"), "a value of another sort");
    let ids = definite_unary(&mut kb, "yr3n7.q_part");
    assert_eq!(ids.len(), 1, "{ids:?}");
    assert!(matches!(ids[0], Value::Int(2)), "{ids:?}");

    let mut kb = load_kb_with(MIXED);
    assert_eq!(definite_unary(&mut kb, "yr3n7m.mk3").len(), 2, "untyped: both values");
    assert_eq!(definite_unary(&mut kb, "yr3n7m.typed").len(), 1, "typed: `S(products: [1])` refused");
}

/// GENERATION IN THE DERIVATION'S ORDER: an unbound column matches every head of the fill, in
/// clause order — base constructors first, each group in declaration order — so `tagged`, declared
/// first, comes before `plain`, though `plain`'s clause is a fact and facts are otherwise tried
/// before rules (kernel-language §8.3). FAILS with the fill's candidates in facts-first order [O],
/// and in an order the index's map decides [S].
#[test]
fn an_unbound_column_generates_in_declaration_order() {
    let mut kb = load_kb_with(SHOP);
    let rows = crate::common::shown_rows(&mut kb, "yr3n7.mixes");
    assert!(rows.iter().all(|(_, definite)| *definite), "{rows:?}");
    let shown: Vec<&str> = rows.iter().map(|(r, _)| r.as_str()).collect();
    assert_eq!(shown.len(), 3, "{shown:?}");
    assert!(
        shown[0].contains("tagged") && shown[0].contains("ON")
            && shown[1].contains("tagged") && shown[1].contains("OFF")
            && shown[2].contains("plain"),
        "tagged(ON), tagged(OFF), plain: {shown:?}"
    );
}

/// A REFINEMENT'S INSTANCE IS CHECKED WHOLE (`/code-review`): `Twin[Q] requires Pair[A = Q, B =
/// Q]` names `Q` twice, so a `twin` is no `Pair[A = Colour, B = Letter]` — `Q` meets `Colour`
/// at `A` and `Letter` at `B` — and is one at `Pair[A = Colour, B = Colour]`. FAILS with a
/// parameter's later slot left uncompared (`atL` answers the `twin` too).
///
/// CONTROL, and a LIMIT stated: a refining sort with NO DOMAIN of its own (`Other2`, whose tuple
/// field no domain fills) has its value checked as a type with no domain is, by CONFORMANCE —
/// the check the path before this ticket ran (`DomainEvidence::NoDomainType`), which reads the
/// top type: `o2(p: (1, "s"))` is admitted beside `o2(p: (1, 2))`, as it was there.
#[test]
fn a_refinements_instance_is_checked_whole() {
    let mut kb = load_kb_with(REFINE);
    assert_eq!(definite_unary(&mut kb, "yr3n7f.mkL").len(), 3, "untyped: every value");
    let at_l = crate::common::shown_rows(&mut kb, "yr3n7f.atL");
    assert_eq!(at_l.len(), 1, "the `pair(red, a)` alone: {at_l:?}");
    assert!(at_l[0].0.contains("pair"), "{at_l:?}");
    let at_c = crate::common::shown_rows(&mut kb, "yr3n7f.atC");
    assert_eq!(at_c.len(), 2, "the `twin` and `pair(red, green)`: {at_c:?}");
    assert!(at_c.iter().any(|(r, _)| r.contains("twin")), "{at_c:?}");
    assert_eq!(definite_unary(&mut kb, "yr3n7f.mkB").len(), 2, "untyped: both values");
    let at_b = crate::common::shown_rows(&mut kb, "yr3n7f.atB");
    assert_eq!(at_b.len(), 2, "conformance reads the top type: {at_b:?}");
    assert!(at_b.iter().all(|(_, definite)| *definite), "{at_b:?}");
}

/// 060 §2.3's BOUND READING at a rigid type: `hasAt[X = Wrap[T = Colour]](wrap(v: red))` goes
/// through `Wrap`'s one clause and `Colour`'s clause for `red` alone — one row, as for `blue`.
/// And the generation rows beside it unchanged: `countAt` lists `Wrap`'s three and `Base`'s one,
/// never a refining sort's value. Pass under every axis.
#[test]
fn a_bound_value_at_a_rigid_type_is_checked() {
    assert_eq!(drive("wrappedRed"), Ok(1));
    assert_eq!(drive("wrappedBlue"), Ok(1));
    assert_eq!(drive("baseAtBase"), Ok(1));
    assert_eq!(drive("wraps"), Ok(3));
    assert_eq!(drive("bases"), Ok(1), "a domain lists its own sort's constructors");
}

/// A VALUE OF A REFINING SORT at a rigid type, filled at its own sort by the call: `other(7)`
/// under `sort Other requires Base` at `Base`'s dictionary, and `narrow2(q: green)` under
/// `requires Wide[W = Q]` at `Wide[W = Colour]`'s — `Narrow2`'s condition is the `Colour`
/// dictionary the caller handed, the slot `Q` meets, not one its own type names. FAILS under
/// [C]. Observably the same as a dictionary built from the value's type today — every
/// dictionary the language builds names its type's own sort — and different once a provision can
/// hand a sub-domain of another provider (WT8WG's item 2).
#[test]
fn a_refining_value_is_filled_at_its_own_sort() {
    assert_eq!(drive("otherAtBase"), Ok(1));
    assert_eq!(drive("narrowAtWide"), Ok(1));
}
