//! WI-20261003-QV5W5 — proposal 069 stage 1: a sort's type and effect-row parameters may
//! declare a DEFAULT (`sort Box[T = Int64]`, `sort T = ? default Int64`, `effects E = ?
//! default {}`), and a written type that leaves the parameter out takes it, in every
//! position. `Function` declares `effects E = ? default {}`, so `Function[A, B]` is the pure
//! function and `Function[A, B, ?]` the open one (kernel-language.md §4.4, §8.1).
//!
//! CONTROLS. The rows were run with each of three back-outs, and each says at its site what
//! that did:
//! - FILL: no default is filled anywhere (`parameter_default_fills` answers nothing) — a
//!   left-out slot is open again, as before the proposal;
//! - CARRIER: the carrier rule reads a slot holding its default as written, not as left out;
//! - HK: a bare sort written into a higher-kinded slot has its own defaults filled.

use anthill_core::eval::Value;

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, run_int64};

const BOX: &str = "\
namespace qv5w5.boxes
  import anthill.prelude.{Int64, String}
  sort Box[T = Int64]
    entity box(v: T)
  end
  operation unbox(b: Box) -> Int64 = match b case box(v) -> v
  operation anyv(b: Box[?]) -> Int64 = 1
  operation strs(b: Box[String]) -> Int64 = match b case box(v) -> v.length()
{extra}end
";

fn boxes(extra: &str) -> String {
    BOX.replace("{extra}", extra)
}

/// `b: Box` under `sort Box[T = Int64]` is `Box[T = Int64]`: an `Int64` box is taken and runs,
/// a `String` box is refused naming the defaulted type. FILL: the refusal is gone, `b` being
/// any box again.
#[test]
fn a_left_out_parameter_takes_its_default() {
    assert_eq!(
        run_int64(&boxes("  operation go() -> Int64 = unbox(box(v: 7))\n"), "qv5w5.boxes.go"),
        Ok(7)
    );
    assert_refused_naming(
        &load_errors_of(&boxes("  operation bad() -> Int64 = unbox(box(v: \"s\"))\n")),
        &["unbox.b (op-arg): expected Box[T = Int64], got Box[T = String]"],
        "a String box where `Box` is declared",
    );
}

/// `Box[?]` is the explicit opt-out — any box — and a written argument overrides the default.
/// Passes with and without FILL by design: neither spelling leaves the slot out (its fixture
/// has no `unbox`, whose body reads the default).
#[test]
fn an_explicit_hole_is_open_and_a_written_argument_wins() {
    let src = |extra: &str| {
        boxes(extra).replace(
            "  operation unbox(b: Box) -> Int64 = match b case box(v) -> v\n",
            "",
        )
    };
    assert_eq!(
        run_int64(
            &src("  operation go() -> Int64 = anyv(box(v: \"s\")) + strs(box(v: \"abc\"))\n"),
            "qv5w5.boxes.go"
        ),
        Ok(4)
    );
    assert_refused_naming(
        &load_errors_of(&src("  operation bad() -> Int64 = strs(box(v: 1))\n")),
        &["strs.b (op-arg): expected Box[T = String], got Box[T = Int64]"],
        "an Int64 box where `Box[String]` is declared",
    );
}

/// The statement form `sort T = ? default Int64` is the bracket form's. FILL: loads.
#[test]
fn the_statement_form_declares_the_same_default() {
    let src = "\
namespace qv5w5.stmt
  import anthill.prelude.{Int64, String}
  sort Box
    sort T = ? default Int64
    entity box(v: T)
  end
  operation unbox(b: Box) -> Int64 = match b case box(v) -> v
  operation bad() -> Int64 = unbox(box(v: \"s\"))
end
";
    assert_refused_naming(
        &load_errors_of(src),
        &["unbox.b (op-arg): expected Box[T = Int64], got Box[T = String]"],
        "the statement form's default",
    );
}

const PAIR: &str = "\
namespace qv5w5.pairs
  import anthill.prelude.{Int64, String, Bool}
  sort AsymmetricPair[T1, T2 = T1]
    entity apair(first: T1, second: T2)
    operation secondOf(p: Self) -> T2 = match p case apair(f, s) -> s
    operation inside(p: AsymmetricPair) -> Int64 = 1
  end
  operation sym(p: AsymmetricPair) -> Int64 = match p case apair(f, s) -> 1
  operation ints(p: AsymmetricPair[Int64]) -> Int64 = match p case apair(f, s) -> f + s
  operation mixed(p: AsymmetricPair[Int64, String]) -> Int64 = match p case apair(f, s) -> f + s.length()
{extra}end
";

fn pairs(extra: &str) -> String {
    PAIR.replace("{extra}", extra)
}

/// `T2 = T1` ties the slot it fills to the one it names: a bare `p: AsymmetricPair` takes
/// `apair(1, 2)` and refuses `apair(1, "s")`, a bare return refuses a body returning one, and
/// `AsymmetricPair[Int64]` is an `Int64` pair. Written in full, the second slot is the
/// author's. FILL: every refusal is gone.
#[test]
fn a_dependent_default_ties_the_slot_it_names() {
    assert_eq!(
        run_int64(
            &pairs(
                "  operation go() -> Int64 = sym(apair(first: 1, second: 2)) + \
                 ints(apair(first: 3, second: 4)) + mixed(apair(first: 1, second: \"ab\"))\n"
            ),
            "qv5w5.pairs.go"
        ),
        Ok(11)
    );
    for (extra, token) in [
        (
            "  operation bad() -> Int64 = sym(apair(first: 1, second: \"s\"))\n",
            "sym.p (op-arg): expected AsymmetricPair[T1 = Int64, T2 = Int64], got AsymmetricPair[T1 = Int64, T2 = String]",
        ),
        (
            "  operation bad() -> AsymmetricPair = apair(first: 1, second: \"s\")\n",
            "bad.return (op-return)",
        ),
        (
            "  operation bad() -> Int64 = ints(apair(first: 1, second: \"s\"))\n",
            "ints.p (op-arg): expected AsymmetricPair[T1 = Int64, T2 = Int64]",
        ),
    ] {
        assert_refused_naming(&load_errors_of(&pairs(extra)), &[token], extra);
    }
}

/// Inside the sort a reference to it is read as anywhere (proposal 070 §1.3): a member about
/// this instance writes `Self`, and returns an asymmetric pair's `T2`; one taking a bare
/// `AsymmetricPair` takes a symmetric pair there too. FILL: the inside refusal is gone.
#[test]
fn inside_the_sort_a_bare_reference_takes_the_default_too() {
    let src = pairs(
        "  operation go() -> Int64 = AsymmetricPair.secondOf(apair(first: 1, second: \"abc\")).length()\n",
    );
    assert_eq!(run_int64(&src, "qv5w5.pairs.go"), Ok(3));
    assert_refused_naming(
        &load_errors_of(&pairs(
            "  operation bad() -> Int64 = AsymmetricPair.inside(apair(first: 1, second: \"s\"))\n",
        )),
        &["inside.p (op-arg): expected AsymmetricPair[T1 = Int64, T2 = Int64]"],
        "a bare in-sort reference is the symmetric pair",
    );
}

/// A default that is a VARIABLE stays the variable: `AP[T1 = X]` under `sort AP[T1, T2 = T1]`
/// is `AP[T1 = X, T2 = X]`, and a body returning the second component as an `X` loads and runs.
/// FAILS with the default-filled slot wrapped whatever it holds — refused "expected ?X, got ?X",
/// the readers that ask whether a type is a variable matching it by carrier. FILL: refused, `T2`
/// being open.
#[test]
fn a_default_that_is_a_variable_is_that_variable() {
    let src = "\
namespace qv5w5.var
  import anthill.prelude.{Int64}
  sort AP[T1, T2 = T1]
    entity ap(first: T1, second: T2)
  end
  operation pick[X](p: AP[T1 = X]) -> X = match p case ap(f, s) -> s
  operation useX[X](p: AP[T1 = X], x: X) -> X = x
  operation go() -> Int64 = pick(ap(first: 1, second: 2)) + useX(ap(first: 3, second: 4), 5)
end
";
    assert_eq!(run_int64(src, "qv5w5.var.go"), Ok(7));
}

/// A default naming a slot left out ties the two in a clause too, through a variable of the
/// clause's own: `holds(AP[], ?n)` matches the symmetric pairs only, a fresh variable at each
/// firing — so a body naming `AP[]` twice takes two pairs of different element types — and a
/// fact `hasSym(AP[])` holds of every symmetric pair. FILL: `sym` answers the asymmetric pair
/// too.
#[test]
fn a_dependent_default_in_a_clause_is_a_variable_of_its_own() {
    let src = "\
namespace qv5w5.clause
  import anthill.prelude.{Int64, String}
  sort AP[T1, T2 = T1]
    entity ap(first: T1, second: T2)
  end
  fact holds(AP[T1 = Int64, T2 = Int64], 1)
  fact holds(AP[T1 = String, T2 = String], 2)
  fact holds(AP[T1 = Int64, T2 = String], 3)
  rule sym(?n) :- holds(AP[], ?n)
  rule twice(?p) :- holds(AP[], ?a), holds(AP[], ?b), ?p <=> ?a * 10 + ?b
  fact hasSym(AP[])
end
";
    let mut kb = load_kb_with(src);
    let mut ints = |kb: &mut anthill_core::kb::KnowledgeBase, qn: &str| {
        let mut v: Vec<i64> = crate::common::query_unary(kb, qn)
            .into_iter()
            .map(|(v, _)| match v {
                Value::Int(n) => n,
                other => panic!("{qn}: {other:?}"),
            })
            .collect();
        v.sort();
        v
    };
    assert_eq!(ints(&mut kb, "qv5w5.clause.sym"), vec![1, 2]);
    assert_eq!(ints(&mut kb, "qv5w5.clause.twice"), vec![11, 12, 21, 22]);
    let mut holds = |kb: &mut anthill_core::kb::KnowledgeBase, q: &str| {
        let goal = crate::common::query_pattern_term(kb, q);
        kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default()).len()
    };
    let at = |a: &str, b: &str| {
        format!(
            "qv5w5.clause.hasSym(qv5w5.clause.AP[T1 = anthill.prelude.{a}, T2 = anthill.prelude.{b}])"
        )
    };
    assert_eq!(holds(&mut kb, &at("Int64", "Int64")), 1);
    assert_eq!(holds(&mut kb, &at("String", "String")), 1);
    assert_eq!(holds(&mut kb, &at("Int64", "String")), 0);
}

/// The carrier rule (070 §1.4) reads a slot its author left out as LEFT OUT, whatever default
/// then fills it: `get(c: Cell, x: V) -> V` uses `Cell`'s `V` beside a `c` that is not its
/// carrier, and is refused naming `Self` — the default is no carrier. CARRIER: it loads, `V`
/// read as the operation's own type parameter. FILL: refused as before the proposal, `c` being
/// any `Cell` (the wording this row names is the default's).
#[test]
fn a_slot_holding_its_default_is_no_carrier() {
    let src = "\
namespace qv5w5.carrier
  import anthill.prelude.{Int64}
  sort Cell[V = Int64]
    entity cell(v: V)
    operation get(c: Cell, x: V) -> V = x
  end
end
";
    assert_refused_naming(
        &load_errors_of(src),
        &[
            "expected a carrier for `V`",
            "`c` is a `Cell` at `V`'s default — its `V` is left out",
            "Type `c` as `Self`",
        ],
        "a defaulted slot is not the carrier",
    );
    // The repair the refusal names loads.
    let fixed = src.replace("get(c: Cell, x: V)", "get(c: Self, x: V)");
    assert!(load_errors_of(&fixed).is_empty(), "{:?}", load_errors_of(&fixed));
}

/// A default may name an earlier parameter inside a type: `Values = List[T = K]` makes an
/// `Index[Int64]` hold a list of `Int64`s, which a body reads back as one. FILL: refused,
/// `Values` being open where a `List[T = Int64]` is returned.
#[test]
fn a_default_names_an_earlier_parameter_inside_a_type() {
    let src = "\
namespace qv5w5.index
  import anthill.prelude.{Int64, List}
  sort Index[K, Values = List[T = K]]
    entity ix(k: K, vs: Values)
  end
  operation f(i: Index[Int64]) -> List[T = Int64] = match i case ix(k, vs) -> vs
  operation go() -> Int64 = f(ix(k: 1, vs: [2, 3, 4])).length()
end
";
    assert_eq!(run_int64(src, "qv5w5.index.go"), Ok(3));
}

/// The declaration's own refusals, each at the default: a later parameter, itself, a row for
/// a type parameter and a type for a row one — an enclosing sort's row parameter included —, a
/// default reaching its own sort, a higher-kinded default of another arity or naming a later
/// parameter, and a default on a higher-kinded parameter's own member — and, at the parse, a
/// `default` on an alias. Pass with and without FILL: they are the declaration's.
#[test]
fn a_default_is_checked_at_its_declaration() {
    for (decl, token) in [
        (
            "sort Bad[A = List[T = B], B]  entity bad(a: A) end",
            "the default of `A` names `B`, which is declared after it",
        ),
        ("sort Me[A = A]  entity me(a: A) end", "the default of `A` names `A` itself"),
        (
            "sort K[A = {}]  entity k(a: A) end",
            "the default of `A` is of the wrong kind: `A` is a type parameter",
        ),
        (
            "sort R  effects E = ? default Int64  entity r(x: Int64) end",
            "the default of `E` is of the wrong kind: `E` is an effect-row parameter",
        ),
        (
            "sort R2  effects E = ? default {}  sort T = ? default E  entity r2(x: Int64) end",
            "the default of `T` is of the wrong kind: `T` is a type parameter",
        ),
        (
            "sort Tree[T = Tree]  entity leaf(x: Int64) end",
            "a parameter default of `qv5w5.decl.Tree` reaches the sort again",
        ),
        (
            "sort H[F[T] = Int64, A]  entity h(a: A) end",
            "`F` is a higher-kinded parameter of `qv5w5.decl.H` declaring 1 parameter(s)",
        ),
        (
            "sort H5[F[T] = G, G[T]]  entity h5(x: Int64) end",
            "the default of `F` names `G`, which is declared after it",
        ),
        (
            "sort HM[F[T = Int64]]  entity hm(x: Int64) end",
            "`T` is a parameter of the higher-kinded parameter `F`",
        ),
        (
            "sort Outer  effects R = ?  sort Inner[T = R]  entity inn(x: T) end  entity o(x: Int64) end",
            "the default of `T` is of the wrong kind: `T` is a type parameter of `qv5w5.decl.Outer.Inner`",
        ),
    ] {
        let src = format!(
            "namespace qv5w5.decl\n  import anthill.prelude.{{Int64, String, List}}\n  {decl}\nend\n"
        );
        assert_refused_naming(&load_errors_of(&src), &[token], decl);
    }
    let errs = crate::common::parse_errs("namespace qv5w5.decl\n  sort Al = Int64 default String\nend\n");
    assert_refused_naming(
        &errs,
        &["`sort Al = …` is not a parameter declaration, so it takes no `default`"],
        "a default on an alias",
    );
}

/// A higher-kinded default is a bare sort of the parameter's arity: `Holder[A = Int64]` is
/// `Holder[F = List, A = Int64]`, which a list holder is and an `Option` holder is not. FILL:
/// the `Option` holder is taken.
#[test]
fn a_higher_kinded_default_is_a_bare_sort() {
    let src = "\
namespace qv5w5.hk
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.Option.some
  sort Holder[F[T] = List, A]
    entity holder(xs: F[T = A])
  end
  operation n(h: Holder[A = Int64]) -> Int64 = 5
  operation openF(h: Holder[F = Option, A = Int64]) -> Int64 = 1
  operation go() -> Int64 = n(holder(xs: [1, 2, 3])) + openF(holder(xs: some(1)))
{extra}end
";
    assert_eq!(run_int64(&src.replace("{extra}", ""), "qv5w5.hk.go"), Ok(6));
    assert_refused_naming(
        &load_errors_of(
            &src.replace("{extra}", "  operation bad() -> Int64 = n(holder(xs: some(1)))\n"),
        ),
        &["n.h (op-arg): expected Holder[F = List, A = Int64], got Holder[F = Option, A = Int64]"],
        "an Option holder where the default says List",
    );
}

/// A bare sort written into a higher-kinded slot is the unapplied constructor, so its own
/// defaults are not filled: `Holder[F = Seq, …]` under `sort Seq[T = Int64]` holds a `Seq` of
/// the holder's `A`, a `String` one here, and the parameter's declared type is the type
/// `Holder[F = Seq, A = String]` a body writes as a value. HK: the run is unchanged — the
/// typer applies `F[T = A]` by `F`'s head — and the declared type is another one, `F` holding
/// `Seq[T = Int64]`, a type where a constructor of one parameter is declared.
#[test]
fn a_sort_in_a_higher_kinded_slot_is_not_applied() {
    let src = "\
namespace qv5w5.hkslot
  import anthill.prelude.{Int64, String, Type}
  sort Seq[T = Int64]
    entity sq(x: T)
  end
  sort Holder[F[T], A]
    entity holder(xs: F[T = A])
  end
  operation n(h: Holder[F = Seq, A = String]) -> Int64 = 2
  operation go() -> Int64 = n(holder(xs: sq(x: \"s\")))
  operation idt(t: Type) -> Type = t
  operation written() -> Type = idt(Holder[F = Seq, A = String])
  rule asValue(?t) :- ?t <=> written()
end
";
    assert_eq!(run_int64(src, "qv5w5.hkslot.go"), Ok(2));
    let mut kb = load_kb_with(src);
    let got = crate::common::query_unary(&mut kb, "qv5w5.hkslot.asValue");
    let op = kb.resolve_symbol("qv5w5.hkslot.n");
    let declared = anthill_core::kb::op_info::lookup_operation_info(&kb, op)
        .expect("`n` has a signature")
        .params[0]
        .1
        .clone();
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        anthill_core::kb::term_view::views_structurally_equal(&kb, &got[0].0, &declared),
        "the written value is {:?}, the declared parameter {declared:?}",
        got[0].0
    );
}

const FUNCTIONS: &str = "\
namespace qv5w5.fn
  import anthill.prelude.{Int64, Function, Error}
  operation boom(x: Int64) -> Int64 effects {Error} = x
  operation inc(x: Int64) -> Int64 = x + 1
  operation use(f: Function[A = Int64, B = Int64]) -> Int64 = f(5)
  operation useOpen(f: Function[A = Int64, B = Int64, E = ?]) -> Int64 = 0
  operation mkOpen() -> Function[A = Int64, B = Int64, E = ?] = boom
  operation viaArrow(g: (x: Int64) -> Int64) -> Function[A = Int64, B = Int64] = g
  operation toArrow(g: Function[A = Int64, B = Int64]) -> (x: Int64) -> Int64 = g
  operation go() -> Int64 = use(inc) + useOpen(boom) + use(toArrow(viaArrow(inc)))
{extra}end
";

fn functions(extra: &str) -> String {
    FUNCTIONS.replace("{extra}", extra)
}

/// `Function` declares `effects E = ? default {}`: a written `Function[A, B]` is the pure
/// function in a parameter, a return and an annotation, and is the arrow `(A) -> B` both ways;
/// `E = ?` is the open spelling. FILL: every refusal is gone, and `toArrow` is refused
/// (`expected Int64 -> Int64, got Function[…, E = g.E]`).
#[test]
fn function_without_its_row_is_the_pure_function() {
    assert_eq!(run_int64(&functions(""), "qv5w5.fn.go"), Ok(12));
    for (extra, token) in [
        (
            "  operation bad() -> Int64 = use(boom)\n",
            "use.f (op-arg): expected callback effects admitted by parameter `f`",
        ),
        (
            "  operation bad() -> Function[A = Int64, B = Int64] = boom\n",
            "bad.return (op-return): expected Function[A = Int64, B = Int64, E = {}]",
        ),
        (
            "  operation bad() -> Int64 =\n    let w: Function[A = Int64, B = Int64] = lambda (z: Int64) -> boom(z)\n    0\n",
            "w.annotation (let-binding): expected Function[A = Int64, B = Int64, E = {}]",
        ),
    ] {
        assert_refused_naming(&load_errors_of(&functions(extra)), &[token], extra);
    }
}

/// The program the e-applied-arrow family named this ticket for (user, 2026-10-14): a lambda
/// that writes the cell it is given, held at `Function[A = Cell[V = Int64], B = Int64]`, was
/// admitted — an unwritten `E` took any row — and applying it in an operation that declares no
/// effects wrote `q` (552). It is refused at the annotation. FILL: it loads again.
#[test]
fn a_writing_lambda_is_refused_where_function_is_written_without_its_row() {
    let src = "\
namespace qv5w5.cellfn
  import anthill.prelude.{Int64, Function, Cell, Modify}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation use(q: Cell[V = Int64]) -> Int64 =
    let w: Function[A = Cell[V = Int64], B = Int64] = lambda (z: Cell[V = Int64]) -> put(z, 5)
    w(q)
end
";
    assert_refused_naming(
        &load_errors_of(src),
        &["w.annotation (let-binding): expected Function[A = Cell[V = Int64], B = Int64, E = {}]"],
        "a lambda writing its parameter where the pure function is written",
    );
}

const RULES: &str = "\
namespace qv5w5.rules
  import anthill.prelude.{Int64, String, Type}
  sort Box[T = Int64]
    entity box(a: T, b: T)
    rule same(?p) :- ?p <=> box(a: ?x, b: ?x)
  end
  entity Held(b: Box[?])
  fact Held(b: box(a: 1, b: 1))
  fact Held(b: box(a: \"s\", b: \"s\"))
  rule ints(?p: Box) :- Held(b: ?p)
  rule anys(?p: Box[?]) :- Held(b: ?p)
  sort Def[T = Int64]
    operation tag() -> Int64 = 8
  end
  fact holds(Def[])
  operation idt(t: Type) -> Type = t
  operation decl(x: Def) -> Int64 = 0
  operation viaBody() -> Type = idt(Def[])
  rule bodyType(?t) :- ?t <=> viaBody()
end
";

/// A rule's written bound reads the default as an operation's parameter does: `?p: Box`
/// matches the `Int64` box only, and `Box[?]` both. FILL: `ints` answers both.
#[test]
fn a_written_bound_takes_the_default() {
    let mut kb = load_kb_with(RULES);
    assert_eq!(crate::common::query_unary(&mut kb, "qv5w5.rules.ints").len(), 1);
    assert_eq!(crate::common::query_unary(&mut kb, "qv5w5.rules.anys").len(), 2);
}

/// A bracket written as a VALUE is the type it writes, with its defaults: the fact
/// `holds(Def[])` holds `Def[T = Int64]` and not `Def[T = String]`, and an operation body's
/// `idt(Def[])` is the type a parameter declared `Def` has. FILL: the fact holds the open
/// `Def[]`, and the body's type differs from the declared one.
#[test]
fn a_bracket_written_as_a_value_takes_the_default() {
    let mut kb = load_kb_with(RULES);
    let answers = |kb: &mut anthill_core::kb::KnowledgeBase, q: &str| {
        let goal = crate::common::query_pattern_term(kb, q);
        kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default())
            .len()
    };
    assert_eq!(answers(&mut kb, "qv5w5.rules.holds(qv5w5.rules.Def[T = anthill.prelude.Int64])"), 1);
    assert_eq!(answers(&mut kb, "qv5w5.rules.holds(qv5w5.rules.Def[T = anthill.prelude.String])"), 0);
    let got: Vec<Value> = crate::common::query_unary(&mut kb, "qv5w5.rules.bodyType")
        .into_iter()
        .map(|(v, _)| v)
        .collect();
    let op = kb.resolve_symbol("qv5w5.rules.decl");
    let declared = anthill_core::kb::op_info::lookup_operation_info(&kb, op)
        .expect("`decl` has a signature")
        .params[0]
        .1
        .clone();
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        anthill_core::kb::term_view::views_structurally_equal(&kb, &got[0], &declared),
        "`idt(Def[])` is {:?}, `x: Def` is {declared:?}",
        got[0]
    );
}

/// A constructor in a rule's PATTERN position leaves its sort's parameter the clause's
/// variable for a query to bind (user, 2026-10-23, reading (b)): `same` answers a `String`
/// box under `sort Box[T = Int64]`. Passes with and without FILL by design — no default is
/// filled into a pattern; the reading it pins is the decision, under which reading (a) would
/// answer nothing.
#[test]
fn a_constructor_pattern_keeps_its_parameter_open() {
    let mut kb = load_kb_with(RULES);
    let goal = crate::common::query_pattern_term(
        &mut kb,
        "qv5w5.rules.Box.same(qv5w5.rules.Box.box(a: \"s\", b: \"s\"))",
    );
    let answers = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
    assert_eq!(answers.len(), 1);
}

/// A rule reads a declared default through `anthill.reflect.SortParamDefault`, an earlier
/// parameter named by reference: `AsymmetricPair`'s `T2` is `T1`, and `Function`'s `E` is `{}`.
/// Passes with and without FILL — the row is the declaration's; FAILS with the row not filed
/// (`Loader::file_parameter_default`'s assertion taken out): the rule answers nothing.
#[test]
fn a_default_is_reflected() {
    let src = "\
namespace qv5w5.reflect
  import anthill.reflect.SortParamDefault
  sort AsymmetricPair[T1, T2 = T1]
    entity apair(first: T1, second: T2)
  end
  rule defaultOf(?d) :- SortParamDefault(param: ?, default: ?d)
end
";
    let mut kb = load_kb_with(src);
    let rows: Vec<String> = crate::common::shown_rows(&mut kb, "qv5w5.reflect.defaultOf")
        .into_iter()
        .map(|(r, _)| r)
        .collect();
    assert!(rows.iter().any(|r| r.ends_with("T1")), "{rows:?}");
    assert!(rows.iter().any(|r| r == "{}"), "{rows:?}");
}
