//! WI-20261003-KPBVX — a transparent type alias carries a parameter's declared default exactly
//! as the application it names does (proposal 069 §2, *a type default is context-free*): `sort
//! F = Function[A, B]` is the pure function wherever it is written, `sort B = Box` under `sort
//! Box[T = Int64]` is the `Int64` box, and an alias that WRITES the slot (`?`, `{Error}`) keeps
//! what it writes. Each row drives the alias beside the direct spelling.
//!
//! CONTROLS. The rows were run with each of three back-outs, and each says at its site what
//! that did:
//! - ALIAS-FILL: an alias's definition is lowered without its defaults, as a value as well as
//!   a type — the alias losing the default;
//! - MARK: the alias's recorded type is its term, which cannot say a slot was left out
//!   (`KnowledgeBase::alias_types` as it was);
//! - OPEN: an alias's `?` at a defaulted slot is left unwritten in a value position, as at a
//!   slot with no default.

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, run_int64};

const FUNCTIONS: &str = "\
namespace kpbvx.fn
  import anthill.prelude.{Int64, Function, Error}
  sort F = Function[A = Int64, B = Int64]
  sort G = Function[A = Int64, B = Int64, E = ?]
  sort H = Function[A = Int64, B = Int64, E = {Error}]
  operation boom(x: Int64) -> Int64 effects {Error} = x
  operation inc(x: Int64) -> Int64 = x + 1
  operation useF(f: F) -> Int64 = f(5)
  operation useDirect(f: Function[A = Int64, B = Int64]) -> Int64 = f(5)
  operation useG(f: G) -> Int64 = 0
  operation useH(f: H) -> Int64 effects {Error} = f(1)
  operation mkF() -> F = inc
  operation mkG() -> G = boom
  operation mkH() -> H = boom
  operation mkE() -> Function[A = Int64, B = Int64, E = {Error}] = boom
  operation go() -> Int64 effects {Error} =
    useF(inc) + useF(mkF()) + useG(boom) + useG(mkG()) + useH(boom) + useH(mkH()) + useH(inc)
{extra}end
";

fn functions(extra: &str) -> String {
    FUNCTIONS.replace("{extra}", extra)
}

/// Row (1), a PARAMETER: `f: F` takes a pure function and refuses an effectful one, in the
/// words `f: Function[A, B]` is refused in; `G`, writing `?`, takes it; `H`, writing `{Error}`,
/// is a function that may raise `Error`. ALIAS-FILL: `useF(boom)` loads.
#[test]
fn a_parameter_typed_by_the_alias_is_the_pure_function() {
    assert_eq!(run_int64(&functions(""), "kpbvx.fn.go"), Ok(16));
    for (call, op) in [("useF(boom)", "useF"), ("useDirect(boom)", "useDirect")] {
        let errs = load_errors_of(&functions(&format!("  operation bad() -> Int64 = {call}\n")));
        assert_eq!(errs.len(), 1, "{errs:#?}");
        assert_refused_naming(
            &errs,
            &[
                &format!("{op}.f (op-arg): expected callback effects admitted by parameter `f`"),
                "declares `Error`, which the closed row does not admit",
            ],
            call,
        );
    }
}

/// Row (2), a RETURN, and an annotation: `-> F` and `let w: F` are pure, so a body or a lambda
/// that raises is refused there; `-> G` and `-> H` hold the effectful function (in the fixture:
/// `mkG`, `mkH`). ALIAS-FILL: both load.
#[test]
fn a_return_typed_by_the_alias_is_the_pure_function() {
    for (extra, token) in [
        (
            "  operation bad() -> F = boom\n",
            "bad.return (op-return): expected F (Function[A = Int64, B = Int64, E = {}])",
        ),
        (
            "  operation bad() -> Int64 =\n    let w: F = lambda (z: Int64) -> boom(z)\n    0\n",
            "w.annotation (let-binding): expected F (Function[A = Int64, B = Int64, E = {}])",
        ),
    ] {
        let errs = load_errors_of(&functions(extra));
        assert_eq!(errs.len(), 1, "{errs:#?}");
        assert_refused_naming(&errs, &[token], extra);
    }
}

/// Row (4), a WRITTEN BOUND on a rule column: `?p: F` is pure, so a body binding it to a
/// function that may raise is refused as under `?p: Function[A, B]`; `G` and `H` take it.
/// ALIAS-FILL: the `F` clause loads.
#[test]
fn a_rule_bound_typed_by_the_alias_is_the_pure_function() {
    for (bound, shown) in [
        ("F", "F (Function[A = Int64, B = Int64, E = {}])"),
        ("Function[A = Int64, B = Int64]", "Function[A = Int64, B = Int64, E = {}]"),
    ] {
        let errs = load_errors_of(&functions(&format!(
            "  rule bs(?p: {bound}) :- ?p <=> mkE()\n"
        )));
        assert_eq!(errs.len(), 1, "{errs:#?}");
        assert_refused_naming(
            &errs,
            &[&format!(
                "expected Function[A = Int64, B = Int64, E = {{Error}}], got {shown}"
            )],
            bound,
        );
    }
    for bound in ["G", "H"] {
        let errs = load_errors_of(&functions(&format!(
            "  rule bs(?p: {bound}) :- ?p <=> mkE()\n"
        )));
        assert!(errs.is_empty(), "{bound}: {errs:#?}");
    }
}

const BOXES: &str = "\
namespace kpbvx.boxes
  import anthill.prelude.{Int64, String, Type}
  sort Box[T = Int64]
    entity box(a: T, b: T)
  end
  sort B = Box
  sort BA = Box[?]
  entity Held(b: Box[?])
  fact Held(b: box(a: 1, b: 1))
  fact Held(b: box(a: \"s\", b: \"s\"))
  rule ints(?p: Box) :- Held(b: ?p)
  rule aints(?p: B) :- Held(b: ?p)
  rule anys(?p: Box[?]) :- Held(b: ?p)
  rule aanys(?p: BA) :- Held(b: ?p)
{extra}end
";

fn boxes(extra: &str) -> String {
    BOXES.replace("{extra}", extra)
}

/// Row (3), a RULE's logical position: a column bound `?p: B` is the `Int64` box, answering
/// what `?p: Box` answers, and `BA`, an alias of `Box[?]`, ranges over every element type as
/// `Box[?]` does. A body binding `?p: B` to a `String` box is refused. ALIAS-FILL: `aints`
/// answers both boxes, and the clause loads.
#[test]
fn a_rule_column_bound_by_the_alias_takes_the_default() {
    let mut kb = load_kb_with(&boxes(""));
    for (direct, alias, n) in [("ints", "aints", 1), ("anys", "aanys", 2)] {
        assert_eq!(crate::common::query_unary(&mut kb, &format!("kpbvx.boxes.{direct}")).len(), n);
        assert_eq!(crate::common::query_unary(&mut kb, &format!("kpbvx.boxes.{alias}")).len(), n);
    }
    let errs = load_errors_of(&boxes("  rule bs(?p: B) :- ?p <=> box(a: \"s\", b: \"s\")\n"));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert_refused_naming(
        &errs,
        &["bs.p (rule-bound): expected B (Box[T = Int64]), got Box[T = String]"],
        "a String box bound where `B` is the column's type",
    );
}

const VALUES: &str = "\
namespace kpbvx.values
  import anthill.prelude.{Int64, String, Type}
  sort Two[L, R = Int64]
    operation tag() -> Int64 = 9
  end
  sort TS = Two[L = String]
  sort TE = Two[]
  sort TQ = Two[R = ?]
  sort TB = Two
  sort TC = TS
  fact holds(TS)
  fact holdsE(TE)
  fact holdsC(TC)
  fact holdsQ(TQ[L = String])
  fact holdsBare(TB)
  fact written(Two[L = String])
  operation idt(t: Type) -> Type = t
  operation viaAlias() -> Type = idt(TS)
  operation viaApplied() -> Type = idt(TQ[L = String])
  operation decl(x: Two[L = String]) -> Int64 = 0
  rule aliasType(?t) :- ?t <=> viaAlias()
  rule appliedType(?t) :- ?t <=> viaApplied()
end
";

fn answers(kb: &mut anthill_core::kb::KnowledgeBase, q: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, q);
    kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default())
        .len()
}

/// Row (3) again, an alias written as a VALUE — a fact's data slot, a query's, an operation
/// body's argument: it is the value the bracket of its definition is, so `TS` over `sort TS =
/// Two[L = String]` is `Two[L = String, R = Int64]`, the type `x: Two[L = String]` declares,
/// and so is a chain to it (`TC`) and `TE` over `Two[]`. A bare link (`TB` over `Two`) is the
/// sort's name, as `Two` is. ALIAS-FILL: `holds`, `holdsE` and `holdsC` hold no `R`, so the
/// first four counts are 0, a query writing `TS` misses the written fact, and the body's type
/// is not the declared one.
#[test]
fn an_alias_written_as_a_value_takes_the_default() {
    let mut kb = load_kb_with(VALUES);
    let int_pair = "kpbvx.values.Two[L = anthill.prelude.String, R = anthill.prelude.Int64]";
    for fact in ["holds", "holdsE", "holdsC"] {
        let at = if fact == "holdsE" {
            "kpbvx.values.Two[R = anthill.prelude.Int64]"
        } else {
            int_pair
        };
        assert_eq!(answers(&mut kb, &format!("kpbvx.values.{fact}({at})")), 1, "{fact}");
    }
    assert_eq!(answers(&mut kb, &format!("kpbvx.values.written({int_pair})")), 1);
    assert_eq!(answers(&mut kb, "kpbvx.values.written(kpbvx.values.TS)"), 1);
    assert_eq!(answers(&mut kb, "kpbvx.values.holdsBare(kpbvx.values.Two)"), 1);
    assert_eq!(answers(&mut kb, &format!("kpbvx.values.holdsBare({int_pair})")), 0);
    let declared = {
        let op = kb.resolve_symbol("kpbvx.values.decl");
        anthill_core::kb::op_info::lookup_operation_info(&kb, op)
            .expect("`decl` has a signature")
            .params[0]
            .1
            .clone()
    };
    let got = crate::common::query_unary(&mut kb, "kpbvx.values.aliasType");
    assert_eq!(got.len(), 1, "{got:?}");
    assert!(
        anthill_core::kb::term_view::views_structurally_equal(&kb, &got[0].0, &declared),
        "`idt(TS)` is {:?}, `x: Two[L = String]` is {declared:?}",
        got[0].0
    );
}

/// An alias that writes `?` at a defaulted slot keeps it open in a value position, as the
/// bracket written out does: `TQ[L = String]` over `sort TQ = Two[R = ?]` holds any `R`, and
/// an operation body's `idt(TQ[L = String])` is `Two[L = String]`, as `idt(Two[L = String, R
/// = ?])` is. Binding that slot again is two values for one parameter, as in a type position.
/// OPEN: the fact holds `R = Int64` only (and, measured on the parent with the CLI, the body's
/// value is `Two[L = String, R = Int64]` and the rebinding loads). Passes under ALIAS-FILL by
/// design: nothing is filled into a written `?`.
#[test]
fn an_alias_writing_the_slot_open_keeps_it_open_as_a_value() {
    let mut kb = load_kb_with(VALUES);
    for r in ["anthill.prelude.String", "anthill.prelude.Int64"] {
        let q = format!("kpbvx.values.holdsQ(kpbvx.values.Two[L = anthill.prelude.String, R = {r}])");
        assert_eq!(answers(&mut kb, &q), 1, "{q}");
    }
    let shown = crate::common::shown_rows(&mut kb, "kpbvx.values.appliedType");
    assert_eq!(shown.len(), 1, "{shown:?}");
    assert_eq!(shown[0].0, "Two[L = String]");
    let errs = load_errors_of(&VALUES.replace(
        "  rule aliasType",
        "  operation rebind() -> Type = idt(TQ[R = String])\n  rule aliasType",
    ));
    assert_refused_naming(
        &errs,
        &["'kpbvx.values.TQ' is a type alias", "already binds `R`"],
        "a slot the alias writes `?` bound again",
    );
}

const PAIRS: &str = "\
namespace kpbvx.pairs
  import anthill.prelude.{Int64, String}
  sort AsymmetricPair[T1, T2 = T1]
    entity apair(first: T1, second: T2)
  end
  sort P = AsymmetricPair[Int64]
  operation pp(p: P) -> Int64 = match p case apair(f, s) -> f + s
{extra}end
";

/// Row (5), a DEPENDENT default through an alias: `P` over `AsymmetricPair[Int64]` has `T2 =
/// Int64`, so it takes `apair(3, 4)`, its body reads the second as an `Int64`, and it refuses
/// `apair(1, "s")`. ALIAS-FILL: `pp`'s body is refused, `s` being any `T2` ("add.b (op-arg):
/// expected Int64, got p.T2").
#[test]
fn a_dependent_default_through_an_alias() {
    let pairs = |extra: &str| PAIRS.replace("{extra}", extra);
    assert_eq!(
        run_int64(&pairs("  operation go() -> Int64 = pp(apair(first: 3, second: 4))\n"), "kpbvx.pairs.go"),
        Ok(7)
    );
    let errs = load_errors_of(&pairs(
        "  operation bad() -> Int64 = pp(apair(first: 1, second: \"s\"))\n",
    ));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert_refused_naming(
        &errs,
        &["pp.p (op-arg): expected P (AsymmetricPair[T1 = Int64, T2 = Int64]), got AsymmetricPair[T1 = Int64, T2 = String]"],
        "a String second where `P` is declared",
    );
}

const CARRIER: &str = "\
namespace kpbvx.carrier
  import anthill.prelude.{Int64, List}
  sort Box[T = Int64]
    entity box(v: T)
{extra}  end
  sort MyBox = Box
  sort MyBox2 = MyBox
  sort Boxes = List[T = MyBox]
end
";

/// The carrier rule (proposal 070 §1.4) through an alias: `b: MyBox` over `sort MyBox = Box`
/// leaves `T` out as `b: Box` does, so `get(b: MyBox, x: T) -> T` uses `Box`'s `T` with no
/// carrier and is refused naming the alias and the default; so are a chain of aliases and a
/// list holding one. Typed `Self`, it loads. MARK: all three load, the alias's type saying `T` was written.
/// ALIAS-FILL: refused, `b` being any `Box` (the wording this row names is the default's).
#[test]
fn an_alias_leaving_the_slot_out_is_no_carrier() {
    for (ty, said) in [
        ("MyBox", "`b` is a `MyBox`, a `Box` at `T`'s default — its `T` is left out"),
        ("MyBox2", "`b` is a `MyBox2`, a `Box` at `T`'s default — its `T` is left out"),
        ("Boxes", "`b` holds a `MyBox`, a `Box` at `T`'s default — its `T` is left out"),
    ] {
        let src = CARRIER.replace(
            "{extra}",
            &format!("    operation get(b: {ty}, x: T) -> T = x\n"),
        );
        let errs = load_errors_of(&src);
        assert_eq!(errs.len(), 1, "{ty}: {errs:#?}");
        assert_refused_naming(&errs, &["expected a carrier for `T`", said], ty);
    }
    let fixed = CARRIER.replace(
        "{extra}",
        "    operation get(b: MyBox, c: Self, x: T) -> T = x\n",
    );
    assert!(load_errors_of(&fixed).is_empty(), "{:?}", load_errors_of(&fixed));
}

const REQUIRES: &str = "\
namespace kpbvx.req
  import anthill.prelude.{Int64, String}
  sort Box[T = Int64]
    entity box(v: T)
  end
  sort MyBox = Box
  sort Show[T]
    operation show(x: T) -> Int64
  end
  sort BoxShow
    entity bs
    provides Show[T = {at}]
    operation show(x: Box[{el}]) -> Int64 = 7
  end
  operation ask(x: MyBox) -> Int64 requires Show[T = MyBox] = Show.show(x)
  operation go() -> Int64 = ask(box(v: 1))
end
";

/// A binding of a `requires` or `provides` clause written through the alias is the `Int64`
/// box: `requires Show[T = MyBox]` is supplied by a provision at `MyBox` or at `Box[Int64]`,
/// and not by one at `Box[String]`. ALIAS-FILL: the provision at `MyBox` is refused, its
/// member's `x: Box[T = Int64]` taking less than any `Box` the spec's `T` then is.
#[test]
fn a_clause_binding_written_through_the_alias_takes_the_default() {
    let program = |at: &str, el: &str| REQUIRES.replace("{at}", at).replace("{el}", el);
    for at in ["MyBox", "Box[Int64]"] {
        assert_eq!(run_int64(&program(at, "Int64"), "kpbvx.req.go"), Ok(7), "{at}");
    }
    let errs = load_errors_of(&program("Box[String]", "String"));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert_refused_naming(
        &errs,
        &["`kpbvx.req.Show[T = kpbvx.req.MyBox (kpbvx.req.Box[T = anthill.prelude.Int64])]` cannot be supplied"],
        "a provision at another element type",
    );
}
