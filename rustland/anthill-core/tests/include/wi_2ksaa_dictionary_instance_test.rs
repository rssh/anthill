//! WI-20261113-2KSAA — proposal 074 stage 1: A TYPECLASS INSTANCE IS A DICTIONARY, AND IS
//! WRITTEN AS ONE (`docs/proposals/074-typeclass-instance-is-a-dictionary.md` §2).
//!
//! A dictionary is written `Dictionary.instance[Additive[T = Int64]]()`, a built-in typed `S`
//! (`Additive[T = Int64]`), and a parameter that takes one is typed at the spec, `x: Additive`.
//! A spec application is a type wherever it is written (§1.1): 073 part 2 read
//! `add2(Additive[T = Int64], 2, 3)` as the instance, which is refused now, naming the
//! dictionary's spelling. The classes of "Which sorts have a dictionary" are read off the
//! declaration alone, over the whole chain: who provides a sort no longer decides whether a
//! value typed at it is a dictionary.
//!
//! The target programs T1 to T9 are driven to their answers in §2's spelling, with the
//! refusals the proposal keeps beside them; stages 2 and 4 add T12 and T11 here.
//!
//! CONTROLS, measured with a temporary switch per part in one build, then removed — see the
//! ledger at the end of this file.

use anthill_core::eval::{Interpreter, Value};

use crate::common::{interp_for, load_errors_of, show_value};

fn call(interp: &mut Interpreter, op: &str) -> Value {
    match interp.call(op, &[]) {
        Ok(v) => v,
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

fn shown(interp: &mut Interpreter, op: &str) -> String {
    let v = call(interp, op);
    show_value(interp.kb(), &v)
}

/// A program of `body` in namespace `p074.{ns}`, with the imports the rows share.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace p074.{ns}
  import anthill.prelude.{{Int64, Float, Additive, Type, List, Stream, Bool, String}}
  import anthill.realization.runtime.Dictionary
{body}
end
"#
    )
}

fn answers(ns: &str, body: &str, op: &str) -> String {
    let mut interp = interp_for(&program(ns, body));
    shown(&mut interp, &format!("p074.{ns}.{op}"))
}

fn refused(body: &str) -> Vec<String> {
    let errors = load_errors_of(&program("refused", body));
    assert!(!errors.is_empty(), "expected a refusal of:\n{body}");
    errors
}

fn says(errors: &[String], text: &str) -> bool {
    errors.iter().any(|e| e.contains(text))
}

const ADD2: &str = "  operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b\n";

// ── The target programs (§ "Target programs") ──────────────────────────────────────────

/// T1: the member spelling, one instance per signature, fixed by the call (§1.3). Runs as
/// before; no dictionary is written.
#[test]
fn t1_the_member_spelling_is_fixed_by_the_call() {
    let body = "  operation add3(x: Additive.T, y: Additive.T) -> Additive.T = x + y
  operation go() -> (Int64, Float) = (add3(1, 2), add3(3.0, 4.3))";
    assert_eq!(answers("t1", body, "go"), "(3, 7.3)");
}

/// T2: a function value applied at two instances takes each as a dictionary parameter (§4),
/// handed as §2 writes it. Ran before only through 073 part 2's spelling.
#[test]
fn t2_a_function_value_applied_at_two_instances() {
    let body = "  operation applyBoth(f: (d: Additive, x: d.T, y: d.T) -> d.T) -> (Int64, Float) =
    let ints = f(Dictionary.instance[Additive[T = Int64]](), 1, 2)
    let floats = f(Dictionary.instance[Additive[T = Float]](), 3.0, 4.3)
    (ints, floats)
  operation both() -> (Int64, Float) = applyBoth(lambda (d: Additive, x: d.T, y: d.T) -> x + y)";
    assert_eq!(answers("t2", body, "both"), "(3, 7.3)");
}

/// T3: one `let`-bound closure handed to an operation at two types needs no dictionary
/// parameter: each reference takes the dictionary at the type it is used at (§4.4).
#[test]
fn t3_a_generalized_closure_at_two_types() {
    let body = "  operation sumWith[X](f: (x: X, y: X) -> X, a: X, b: X) -> X = f(a, b)
  operation go() -> (Int64, Float) =
    let f = lambda (x, y) -> x + y
    let ints = sumWith(f, 2, 3)
    let floats = sumWith(f, 1.5, 2.5)
    (ints, floats)";
    assert_eq!(answers("t3", body, "go"), "(5, 4.0)");
}

/// T4: two independent dictionaries in one function type, the second's member the result.
#[test]
fn t4_two_independent_dictionaries_in_one_arrow() {
    let body = "  operation applyMap(f: (p: Additive, q: Additive, x: p.T) -> q.T) -> Float =
    f(Dictionary.instance[Additive[T = Int64]](), Dictionary.instance[Additive[T = Float]](), 2)
  operation go() -> Float =
    applyMap(lambda (p: Additive, q: Additive, x: p.T) -> Additive.zero[T = q.T]())
  operation applyTwo(f: (p: Additive, q: Additive, a: p.T, b: q.T) -> q.T) -> Float =
    f(Dictionary.instance[Additive[T = Int64]](), Dictionary.instance[Additive[T = Float]](), 1, 2.5)
  operation two() -> Float = applyTwo(lambda (p: Additive, q: Additive, a: p.T, b: q.T) -> b + b)";
    let mut interp = interp_for(&program("t4", body));
    assert_eq!(shown(&mut interp, "p074.t4.go"), "0.0");
    assert_eq!(shown(&mut interp, "p074.t4.two"), "5.0");
}

/// T5: where the function is at one type of each, the instances are the operation's type
/// parameters, and its clauses their dictionaries.
#[test]
fn t5_instances_as_type_parameters_under_clauses() {
    let body = "  operation applyMap[T, S](f: (v: T) -> S, x: T) -> S requires Additive[T = T], Additive[T = S] = f(x + x)
  operation go() -> Float = applyMap(lambda (v: Int64) -> if v > 3 then 1.5 else 0.5, 2)";
    assert_eq!(answers("t5", body, "go"), "1.5");
}

const CONVERT: &str = "  sort Convert
    sort X = ?
    sort Y = ?
    operation conv(a: X) -> Y
  end
  sort IntToFloat
    provides Convert[X = Int64, Y = Float]
    operation conv(a: Int64) -> Float = 1.5
  end
";

/// T6: a spec of two parameters: by its members, and by its dictionary, which covers both.
/// `useWith` ran before only through 073 part 2's spelling.
#[test]
fn t6_a_spec_of_two_parameters_by_members_and_by_dictionary() {
    let body = format!(
        "{CONVERT}  operation use(a: Convert.X) -> Convert.Y = Convert.conv(a)
  operation useWith(c: Convert, a: c.X) -> c.Y = Convert.conv(a)
  operation go() -> (Float, Float) =
    (use(2), useWith(Dictionary.instance[Convert[X = Int64, Y = Float]](), 2))"
    );
    assert_eq!(answers("t6", &body, "go"), "(1.5, 1.5)");
}

/// T7: `add2` at `Int64`'s dictionary, built at load (group one); at a clause's, under
/// `requires Additive[T = X]` (group two); and `S` fixed by the type expected, a `let`'s.
#[test]
fn t7_add2_at_a_dictionary() {
    let body = format!(
        "{ADD2}  operation ints() -> Int64 = add2(Dictionary.instance[Additive[T = Int64]](), 2, 3)
  operation sum2[X](a: X, b: X) -> X requires Additive[T = X] =
    add2(Dictionary.instance[Additive[T = X]](), a, b)
  operation viaClause() -> (Int64, Float) = (sum2(2, 3), sum2(1.5, 2.5))
  operation viaLet() -> Int64 =
    let k: Additive[T = Int64] = Dictionary.instance()
    add2(k, 2, 3)"
    );
    let mut interp = interp_for(&program("t7", &body));
    assert_eq!(shown(&mut interp, "p074.t7.ints"), "5");
    assert_eq!(shown(&mut interp, "p074.t7.viaClause"), "(5, 4.0)");
    assert_eq!(shown(&mut interp, "p074.t7.viaLet"), "5");
}

/// T8: polymorphic recursion through a conditional provision, one leg through a lambda: each
/// step calls at `Wrap` of the previous type, so the dictionary is passed at run time
/// (WI-817's witness, `wi817_polyrec_requirement_test`), entered here with a dictionary
/// written at the outermost call.
#[test]
fn t8_polymorphic_recursion_passes_its_dictionary_at_run_time() {
    let src = format!(
        r#"
namespace p074.t8
  import anthill.prelude.{{Int64, Function}}
  import anthill.prelude.Additive.{{sub}}
  import anthill.prelude.PartialEq.{{eq}}
  import anthill.realization.runtime.Dictionary
{}
  sort Poly
    operation apply_fn[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)
    operation f[FT](n: Int64, x: FT) -> Int64 requires Desc[FT] =
      if eq(n, 0) then Desc.describe(x) else g[FT](n, x)
    operation g[GT](n: Int64, x: GT) -> Int64 requires Desc[GT] =
      apply_fn[Wrap[A = GT]](lambda w -> f[Wrap[A = GT]](sub(n, 1), w), wrap(x))
    operation viaDict(d: Desc, n: Int64, x: d.T) -> Int64 = f(n, x)
    operation drive(n: Int64) -> Int64 = viaDict(Dictionary.instance[Desc[T = Leaf]](), n, leaf())
  end
end
"#,
        crate::common::DESC_INSTANCES
    );
    let mut interp = interp_for(&src);
    for (n, want) in [(0, 1), (1, 12), (2, 122)] {
        match interp.call("p074.t8.Poly.drive", &[Value::Int(n)]) {
            Ok(Value::Int(v)) => assert_eq!(v, want, "drive({n})"),
            other => panic!("drive({n}): expected {want}, got {other:?}"),
        }
    }
}

/// T9: a data structure of instances holds one per element (073 §2, group three).
#[test]
fn t9_a_list_of_streams_holds_one_instance_per_element() {
    let body = "  import anthill.prelude.Stream.{takeN}
  operation twice(x: Int64) -> Int64 = x * 2
  operation streams(xs: List[T = Int64]) -> List[T = Stream[T = Int64, E = {}]] =
    [xs, xs.map(twice)]
  operation firsts(ss: List[T = Stream[T = Int64, E = {}]]) -> List[T = List[T = Int64]] =
    ss.map(lambda s -> takeN(s, 1)).collect()
  operation go() -> List[T = List[T = Int64]] = firsts(streams([1, 2, 3]))";
    assert_eq!(answers("t9", body, "go"), "[[1], [2]]");
}

// ── Kept refusals (§ "Target programs", below the table) ───────────────────────────────

/// KSSA4's rule stands (§1.2): a value typed at a spec is the dictionary, no value of a
/// carrier. `Tagger.probe(w)` over `w: Tagger`, and `x + a` over `x: Additive`.
#[test]
fn a_dictionary_is_no_value_of_a_carrier() {
    let errors = refused(
        "  sort Tagger
    sort C = ?
    operation probe(x: C) -> Int64
  end
  operation direct(w: Tagger) -> Int64 = Tagger.probe(w)",
    );
    assert!(says(&errors, "Tagger"), "{errors:?}");
    let errors = refused("  operation bad(x: Additive, a: x.T) -> x.T = x + a");
    assert!(says(&errors, "got Additive[T = x.T]"), "{errors:?}");
}

/// One instance per signature (§1.3): `add3(1, 2.5)` is refused.
#[test]
fn the_member_spelling_is_one_instance() {
    let errors = refused(
        "  operation add3(x: Additive.T, y: Additive.T) -> Additive.T = x + y
  operation bad() -> Float = add3(1, 2.5)",
    );
    assert!(says(&errors, "add3"), "{errors:?}");
}

/// §4: the member spelling in an arrow is the operation's type parameter, so `f(1, 2)` inside
/// is refused; and one `X` per call of `applyBoth`, so `f` is not applied at two types.
#[test]
fn an_arrow_names_no_instance_of_its_own() {
    let errors = refused(
        "  operation applyBoth(f: (x: Additive.T, y: Additive.T) -> Additive.T) -> Int64 = f(1, 2)",
    );
    assert!(says(&errors, "expected Additive.T, got Int64"), "{errors:?}");
    let errors = refused(
        "  operation applyBoth[X](f: (x: X, y: X) -> X) -> (Int64, Float) = (f(1, 2), f(3.0, 4.3))",
    );
    assert!(says(&errors, "type mismatch in f.x (op-arg): expected ?X, got Int64"), "{errors:?}");
}

// ── A spec application is a type (§1.1) ───────────────────────────────────────────────

/// Where a dictionary is expected the spec application is refused, the message naming the
/// spelling that writes one. FAILS with the refusal backed out, where the application is typed
/// as the `Type` it spells and refused as no `Additive` (073 part 2, which answered 5 here,
/// built the dictionary instead).
#[test]
fn a_spec_application_where_a_dictionary_is_expected_is_refused() {
    let errors = refused(&format!(
        "{ADD2}  operation ints() -> Int64 = add2(Additive[T = Int64], 2, 3)"
    ));
    assert!(
        says(&errors, "written `Dictionary.instance[Additive[T = Int64]]()`"),
        "{errors:?}"
    );
}

/// Where a `Type` is expected it is the type, as before. Passes either way, by design.
#[test]
fn a_spec_application_where_a_type_is_expected_is_the_type() {
    let body = "  operation asType() -> Type = Additive[T = Int64]";
    assert_eq!(answers("ty", body, "asType"), "Additive[T = Int64]");
}

// ── Dictionary.instance: what it is, and what it refuses (§2, "The value") ────────────

/// A dictionary prints as the value it is (§3): `Dictionary(impl: Int64)`, its
/// sub-dictionaries positional before `impl`. It printed `Dictionary[impl = Int64]`, the bracket
/// of a type applied.
#[test]
fn a_dictionary_prints_as_a_value() {
    let src = format!(
        r#"
namespace p074.print
  import anthill.prelude.{{Int64, Additive}}
  import anthill.realization.runtime.Dictionary
{}
  operation ints() -> Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]]()
  operation wrapped() -> Desc[T = Wrap[A = Leaf]] = Dictionary.instance[Desc[T = Wrap[A = Leaf]]]()
end
"#,
        crate::common::DESC_INSTANCES
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p074.print.ints"), "Dictionary(impl: Int64)");
    assert_eq!(
        shown(&mut interp, "p074.print.wrapped"),
        "Dictionary(Dictionary(impl: Leaf), impl: WrapDesc)"
    );
}

/// A key of the bracket names a provider by the spec's short name; without it §8.7's order
/// selects. `Leaf`'s own provision answers 1, a second provider `Alt` 2.
#[test]
fn a_key_names_the_provider() {
    let body = "  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Leaf
    entity leaf(k: Int64)
    provides Tag[T = Leaf]
    operation tag(x: Leaf) -> Int64 = 1
  end
  sort Alt
    provides Tag[T = Leaf]
    operation tag(x: Leaf) -> Int64 = 2
  end
  operation viaOpen(t: Tag, x: t.T) -> Int64 = Tag.tag(x)
  operation go() -> (Int64, Int64) =
    (viaOpen(Dictionary.instance[Tag[T = Leaf]](), leaf(k: 0)),
     viaOpen(Dictionary.instance[Tag[T = Leaf], Tag = Alt](), leaf(k: 0)))";
    assert_eq!(answers("key", body, "go"), "(1, 2)");
}

/// `S` is fixed as a type parameter is: nothing fixes it in `add2(Dictionary.instance(), 2,
/// 3)`, where the dictionary is expected at `Additive` with `T` open.
#[test]
fn an_unconstrained_dictionary_is_refused() {
    let errors = refused(&format!(
        "{ADD2}  operation bad() -> Int64 = add2(Dictionary.instance(), 2, 3)"
    ));
    assert!(says(&errors, "nothing fixes it here"), "{errors:?}");
}

const SORTS: &str = "  sort Box
    sort V = ?
    entity box(v: V)
  end
  enum E
    entity e1(k: Int64)
    operation flip(e: E) -> E = e
  end
  sort Marker
    sort T = ?
  end
  sort Ticker
    operation now() -> String
  end
";

/// One row per sort `Dictionary.instance` builds no dictionary of — a data sort, an abstract
/// sort with values of its own, one whose chain declares no operation (whose values are its
/// providers'), one with no parameter — and the two applications it cannot build one at.
#[test]
fn dictionary_instance_refuses_what_has_no_dictionary() {
    let rows: &[(&str, &str, &str)] = &[
        ("Box[V = Int64]", "Box[V = Int64]", "`Box` is a data sort"),
        ("E", "E", "`E` is a data sort"),
        (
            "Stream[T = Int64, E = {}]",
            "Stream[T = Int64, E = {}]",
            "`Stream` is an abstract sort with values of its own",
        ),
        ("Additive", "Additive", "leaves `T` unwritten"),
        (
            "Additive[T = Bool]",
            "Additive[T = Bool]",
            "expected the dictionary of `Additive[T = Bool]`",
        ),
        ("anthill.cli.Main", "anthill.cli.Main", "declares an operation, so it has no dictionary"),
        ("Marker[T = Int64]", "Marker[T = Int64]", "declares an operation, so it has no dictionary"),
        (
            "anthill.logic.Constructive.Constructive",
            "anthill.logic.Constructive.Constructive",
            "declares an operation, so it has no dictionary",
        ),
        (
            "anthill.logic.Classical.Classical",
            "anthill.logic.Classical.Classical",
            "declares an operation, so it has no dictionary",
        ),
        ("Ticker", "Ticker", "has operations and no parameter"),
        ("anthill.prelude.Time", "anthill.prelude.Time", "has operations and no parameter"),
    ];
    for (ty, s, text) in rows {
        let errors = refused(&format!(
            "{SORTS}  operation f() -> {ty} = Dictionary.instance[{s}]()"
        ));
        assert!(says(&errors, text), "`Dictionary.instance[{s}]()`: {errors:?}");
    }
}

/// A key naming a sort that does not provide the spec, a key that is not the spec's short
/// name, and an argument.
#[test]
fn dictionary_instance_refuses_a_bracket_it_cannot_read() {
    let errors = refused(&format!(
        "{SORTS}  operation f() -> Additive[T = Int64] = Dictionary.instance[Additive[T = Int64], Additive = Box]()"
    ));
    assert!(says(&errors, "`Box`, which provides no `Additive`"), "{errors:?}");
    let errors = refused(
        "  operation f() -> Additive[T = Int64] = Dictionary.instance[Additive[T = Int64], Foo = Int64]()",
    );
    assert!(says(&errors, "the key `Foo`"), "{errors:?}");
    let errors =
        refused("  operation f() -> Additive[T = Int64] = Dictionary.instance[Additive[T = Int64]](3)");
    assert!(says(&errors, "1 argument(s)"), "{errors:?}");
}

// ── The classes, read off the declaration over the whole chain (§2) ───────────────────

const DFLT: &str = "  sort Dflt
    sort T = ?
    operation dflt() -> T
  end
";

/// `Dflt` declares an operation that mentions `T` and none receiving on `Dflt`: a spec over
/// `T` whoever provides it. Provided by a sort with values of its own (`Seven`, a witness at
/// `Int64`), `d: Dflt` takes a dictionary, `Seven`'s value is refused there, and `Dflt[T =
/// Int64]` is a `Type`. FAILS with the provision rung restored, where `d: Dflt` took a
/// `Seven` and `Dflt[T = Int64]` was refused as a `Type`.
#[test]
fn a_spec_whose_provider_has_values_of_its_own_still_has_a_dictionary() {
    let body = format!(
        "{DFLT}  sort Seven
    entity seven(k: Int64)
    provides Dflt[T = Int64]
    operation dflt() -> Int64 = 7
  end
  operation pick(d: Dflt) -> d.T = Dflt.dflt[T = d.T]()
  operation go() -> Int64 = pick(Dictionary.instance[Dflt[T = Int64]]())
  operation asType() -> Type = Dflt[T = Int64]"
    );
    let mut interp = interp_for(&program("dflt", &body));
    assert_eq!(shown(&mut interp, "p074.dflt.go"), "7");
    assert_eq!(shown(&mut interp, "p074.dflt.asType"), "Dflt[T = Int64]");
    let errors = refused(&format!(
        "{body}\n  operation bad() -> Int64 = pick(seven(k: 0))"
    ));
    assert!(says(&errors, "expected Dflt, got Seven"), "{errors:?}");
}

/// `Dflt` provided at `Int64`: 42, as before the change. Passes either way, by design.
#[test]
fn a_spec_provided_at_its_parameter_answers_as_before() {
    let src = format!(
        r#"
namespace p074.dflt42
  import anthill.prelude.{{Int64, Type}}
  import anthill.realization.runtime.Dictionary
{DFLT}
  operation pick(d: Dflt) -> d.T = Dflt.dflt[T = d.T]()
  operation go() -> Int64 = pick(Dictionary.instance[Dflt[T = Int64]]())
end
namespace anthill.prelude.Int64
  provides p074.dflt42.Dflt[T = Int64]
  operation dflt() -> Int64 = 42
end
"#
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p074.dflt42.go"), "42");
}

/// `Ord` declares no operation and reaches `WeakOrd.compare` through `provides WeakOrd[T =
/// T]`, a conversion: it has a dictionary, and a clause of it answers `compare`.
#[test]
fn a_sort_reaching_operations_through_its_chain_has_a_dictionary() {
    let body = "  import anthill.prelude.{Ord, WeakOrd}
  operation cmp[X](a: X, b: X) -> Int64 requires Ord[T = X] = WeakOrd.compare(a, b)
  operation go() -> (Int64, Int64, Int64) = (cmp(1, 2), cmp(2, 2), cmp(3, 2))
  operation ord() -> Ord[T = Int64] = Dictionary.instance[Ord[T = Int64]]()";
    let mut interp = interp_for(&program("ord", body));
    assert_eq!(shown(&mut interp, "p074.ord.go"), "(-1, 0, 1)");
    assert!(
        shown(&mut interp, "p074.ord.ord").starts_with("Dictionary("),
        "`Dictionary.instance[Ord[T = Int64]]()` is a dictionary"
    );
}

/// A sort with values of its own holds them: `Symbol`, which provides `PartialEq[T = Symbol]`
/// in its secondary entry.
#[test]
fn a_sort_with_values_of_its_own_holds_them() {
    let body = "  import anthill.reflect.{Symbol, lookup_symbol}
  operation keep(s: Symbol) -> Symbol = s
  operation go() -> Symbol = keep(lookup_symbol(\"anthill.prelude.Int64\"))";
    assert_eq!(answers("sym", body, "go"), "Int64");
    let errors = refused(
        "  import anthill.reflect.Symbol
  operation f() -> Symbol = Dictionary.instance[Symbol]()",
    );
    assert!(says(&errors, "`Symbol` is an abstract sort with values of its own"), "{errors:?}");
}

/// A user's opaque sort holds its own values: `h: Handle` is a `Handle`, though `Handle`
/// provides a spec with an operation at itself, and `Dictionary.instance[Handle]()` is refused,
/// as it is at the library's opaque `anthill.reflect.Term`.
#[test]
fn an_opaque_sort_holds_its_own_values() {
    let src = r#"
namespace p074.opaque
  import anthill.prelude.{String}
  import anthill.realization.runtime.Dictionary
  sort Named
    sort T = ?
    operation name() -> String
  end
  sort Handle = ?
  operation keep(h: Handle) -> Handle = h
end
namespace p074.opaque.Handle
  import anthill.prelude.{String}
  import p074.opaque.{Named}
  provides Named[T = Handle]
  operation name() -> String = "handle"
end
"#;
    let mut interp = interp_for(src);
    match interp.call("p074.opaque.keep", &[Value::Str("h1".into())]) {
        Ok(v) => assert_eq!(show_value(interp.kb(), &v), "\"h1\""),
        Err(e) => panic!("`keep`: {e:?}"),
    }
    let errors = load_errors_of(&format!(
        "{src}\nnamespace p074.opaque2\n  import p074.opaque.Handle\n  import anthill.realization.runtime.Dictionary\n  operation f() -> Handle = Dictionary.instance[Handle]()\nend\n"
    ));
    assert!(says(&errors, "`Handle` is an abstract sort with values of its own"), "{errors:?}");
    let errors = refused(
        "  import anthill.reflect.Term
  operation f() -> Term = Dictionary.instance[Term]()",
    );
    assert!(says(&errors, "`Term` is an abstract sort with values of its own"), "{errors:?}");
}

/// A provision at the sort itself of a sort whose chain declares no operation says nothing of
/// its values: `Clock` providing an operation-less `Tagged[T = Clock]`, as `Error` provides
/// `Effect[T = Error[?]]`, stays an abstract sort without values of its own — refused for now
/// only for having no parameter. FAILS with that exclusion backed out, where `Clock` reads as
/// a sort with values of its own.
#[test]
fn an_operationless_spec_provided_at_a_sort_leaves_its_class() {
    let errors = refused(
        "  sort Tagged
    sort T = ?
  end
  sort Clock
    provides Tagged[T = Clock]
    operation now() -> Int64
  end
  operation f() -> Clock = Dictionary.instance[Clock]()",
    );
    assert!(says(&errors, "`Clock` has operations and no parameter"), "{errors:?}");
}

/// An abstract sort nothing in whose chain declares an operation has values of its own, its
/// providers' (decided with the user 2026-11-14): `openStore` returns a `MemStore` at
/// `KVStore[K = String, V = String]`, as the existential returns of WI-391…488 do. FAILS with
/// such a sort read as a sort with a dictionary, where the return is refused as a provider's
/// value where its dictionary is expected.
#[test]
fn an_operation_free_sort_holds_its_providers_values() {
    let body = "  sort KVStore
    sort K = ?
    sort V = ?
  end
  sort MemStore
    provides KVStore[K = String, V = String]
    entity memStore(n: Int64)
  end
  operation openStore() -> KVStore[K = String, V = String] = memStore(n: 3)";
    assert_eq!(answers("kv", body, "openStore"), "memStore(n: 3)");
}

/// A sort with a dictionary that nothing provides has the dictionary of its own bodies, which
/// stage 3 builds beside a module's (decided with the user 2026-11-14): `ProjAdditive` — the
/// user's T11 provider — is refused naming the stage, where `Additive[T = Bool]`, which other
/// providers answer at other types, is "no impl provides" (above).
#[test]
fn a_sort_nothing_provides_waits_for_stage_3() {
    let errors = refused(
        "  sort Meters
    entity m(v: Int64)
  end
  sort Iso
    sort A = ?
    sort B = ?
    operation to(a: A) -> B
    operation from(b: B) -> A
  end
  sort MetersIso
    provides Iso[A = Int64, B = Meters]
    operation to(a: Int64) -> Meters = m(v: a)
    operation from(b: Meters) -> Int64 =
      match b
        case m(v) -> v
  end
  sort ProjAdditive
    sort X = ?
    sort Y = ?
    requires Additive[T = X]
    requires Iso[A = X, B = Y]
    provides Additive[T = Y]
    operation add(a: Y, b: Y) -> Y = Iso.to(Iso.from(a) + Iso.from(b))
    operation neg(a: Y) -> Y = Iso.to(Additive.neg(Iso.from(a)))
    operation zero() -> Y = Iso.to(Additive.zero[T = X]())
  end
  operation f() -> ProjAdditive[X = Int64, Y = Meters] =
    Dictionary.instance[ProjAdditive[X = Int64, Y = Meters]]()",
    );
    assert!(says(&errors, "nothing provides `ProjAdditive`"), "{errors:?}");
    assert!(says(&errors, "stage 3"), "{errors:?}");
}

/// `S` is read as any written type is: an alias of a spec application is the application, in
/// the bracket and as the type expected (found by /code-review, where `IntAdd` read as a bare
/// sort and was refused).
#[test]
fn an_alias_in_the_bracket_or_the_expected_type_is_the_application() {
    let body = format!(
        "{ADD2}  sort IntAdd = Additive[T = Int64]
  operation viaBracket() -> Int64 = add2(Dictionary.instance[IntAdd](), 2, 3)
  operation viaLet() -> Int64 =
    let k: IntAdd = Dictionary.instance()
    add2(k, 2, 3)"
    );
    let mut interp = interp_for(&program("alias", &body));
    assert_eq!(shown(&mut interp, "p074.alias.viaBracket"), "5");
    assert_eq!(shown(&mut interp, "p074.alias.viaLet"), "5");
}

/// Spellings `Dictionary.instance` refuses rather than reads (found by /code-review): the
/// receiver spelling, which binds no `S` of the built-in; a slot open below the top of an
/// application; and the built-in named bare where a function value is expected, which would
/// load and die where it ran.
#[test]
fn dictionary_instance_refuses_what_it_does_not_read() {
    let errors = refused(
        "  operation f() -> Additive[T = Int64] = Dictionary[S = Additive[T = Int64]].instance()",
    );
    assert!(says(&errors, "got the receiver `Dictionary[S = Additive[T = Int64]]`"), "{errors:?}");
    let errors = refused(&format!(
        "{}\n  operation f() -> Desc[T = Wrap[A = ?]] = Dictionary.instance[Desc[T = Wrap[A = ?]]]()",
        crate::common::DESC_INSTANCES
    ));
    assert!(says(&errors, "leaves `T` with a slot open"), "{errors:?}");
    let errors = refused(
        "  operation apply0(f: () -> Additive[T = Int64]) -> Additive[T = Int64] = f()
  operation f() -> Additive[T = Int64] = apply0(Dictionary.instance)",
    );
    assert!(says(&errors, "`Dictionary.instance` named bare"), "{errors:?}");
}

/// A spec of several parameters none of which an operation receives on says no carrier: its
/// dictionary is at all of them, and a rule head's member spelling may name any (found by
/// /code-review: the first parameter stood in for the provision rung's answer, and `?x:
/// Pairing.B` was refused as "its `A`, not its `B`").
#[test]
fn a_spec_with_no_receiving_parameter_takes_any_member_in_a_rule_head() {
    let body = "  sort Pairing
    sort A = ?
    sort B = ?
    operation make() -> B
  end
  sort PB
    entity pb(k: Int64)
    provides Pairing[A = Int64, B = PB]
    operation make() -> PB = pb(k: 0)
  end
  fact src(pb(k: 1))
  rule mine(?x: Pairing.B) :- src(?x)";
    let mut kb = crate::common::load_kb_with(&program("pairing", body));
    let answers = crate::common::query_unary(&mut kb, "p074.pairing.mine");
    assert_eq!(answers.len(), 1, "{answers:?}");
}

// ── The back-out ledger (measured 2026-11-14, one build, a temporary switch per part, over a
// binary of this file, the three 073 suites it rewrote, `wi_9bkz4`, `wi_kssa4`, `wi_8dxvk`,
// `wi903`, `wi_2kv4y`, `wi402`, `wi1063` and their imports — 286 rows) ─────────────────────
//
// | part backed out | rows that fail |
// |---|---|
// | `Dictionary.instance`'s typer arm (`apply.rs`) | 43: every row here writing a dictionary, the rewritten rows of `wi_p0qgf_spec_instance_values_test` (13), `wi_p0qgf_lambda_instance_test` (11), `wi_dndzf…sum_with…`, `wi_2kv4y…the_advised_bracket…`, `wi_9bkz4…a_clauses_dictionary…` |
// | the refusal of a spec application where a dictionary is expected | `a_spec_application_where_a_dictionary_is_expected_is_refused`; `wi_p0qgf…a_rule_body_writes_no_dictionary_of_its_own`, `…an_application_leaving_the_carrier_unwritten_is_refused` |
// | the receiver spelling refused | `dictionary_instance_refuses_what_it_does_not_read` |
// | `S` fixed by the type expected | `t7_add2_at_a_dictionary`, `an_alias_in_the_bracket_or_the_expected_type_is_the_application`, `wi_p0qgf…an_instance_returned_or_bound` |
// | a slot open below the top refused | `dictionary_instance_refuses_what_it_does_not_read` |
// | a key names the provider | `a_key_names_the_provider`, `dictionary_instance_refuses_a_bracket_it_cannot_read` |
// | a sort nothing provides refused naming stage 3 | `a_sort_nothing_provides_waits_for_stage_3` |
// | that refusal asked before the clause (the defect /code-review found) | `a_sort_nothing_provides_waits_for_stage_3`, `wi_9bkz4…a_clauses_dictionary_needs_no_provider_where_it_is_written` |
// | the built-in named bare refused | `dictionary_instance_refuses_what_it_does_not_read` |
// | the provision rung restored | `a_spec_whose_provider_has_values_of_its_own_still_has_a_dictionary`, `wi_8dxvk…query_domain_answers_an_operation_free_sort_by_provision` |
// | loader-derived `TypeValue` rows counted as a provision at itself | 7: `a_dictionary_is_no_value_of_a_carrier`, `a_sort_nothing_provides_waits_for_stage_3`, `an_operationless_spec_provided_at_a_sort_leaves_its_class`, `dictionary_instance_refuses_what_has_no_dictionary`, `wi_9bkz4` (2), `wi_kssa4…a_spec_typed_value_is_refused_where_the_carrier_is_expected` |
// | an operation-free spec's provision at itself counted | `an_operationless_spec_provided_at_a_sort_leaves_its_class` |
// | an opaque sort read as having values of its own | `an_opaque_sort_holds_its_own_values` |
// | an operation-free sort read as having values of its own (else: a dictionary) | 10: `an_operation_free_sort_holds_its_providers_values`, `dictionary_instance_refuses_what_has_no_dictionary`, `wi402_manifest_provider_test` (5), `wi1063…the_wi401_escape_gate_still_fires`, `wi_8dxvk…`, `wi_9bkz4…a_provision_that_moves…` |
// | a spec with no carrier takes any member in a rule head | `a_spec_with_no_receiving_parameter_takes_any_member_in_a_rule_head` |
// | a later load moving a sealed sort's class refused | `wi_9bkz4…a_provision_that_moves_a_sealed_sort_to_another_class_is_refused` |
// | a dictionary printed as a value | `a_dictionary_prints_as_a_value`, `a_sort_reaching_operations_through_its_chain_has_a_dictionary` |
// | cpp-gen's refusal naming stage 7 (anthill-cpp-gen) | `unsupported_test::a_dictionary_built_in_a_body_is_refused_until_stage_7` |
//
// Two parts failed no row and were removed rather than kept: reading `S` through its aliases
// (an alias is read through before it reaches the built-in, on both carriers) and excluding a
// type parameter from the classes (one declares no operation, so it is operation-free).
// PASS EITHER WAY BY DESIGN: T1, T3, T5 and T9 (no dictionary written), the kept refusals,
// `a_spec_application_where_a_type_is_expected_is_the_type`.
