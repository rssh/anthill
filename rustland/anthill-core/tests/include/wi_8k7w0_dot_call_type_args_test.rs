//! WI-20261026-8K7W0 — a dot call carries the call-site type arguments of the call it
//! resolves to, as its applicative spelling does, where a call's bracket is read: an
//! operation body, a const's value, a rule body's compound expression.
//!
//! `red().score[Score = ByHeat]()` is `Score.score[Score = ByHeat](red())`: the typer
//! replaces a dot by the call it resolves to, and the bracket the loader read off the dot
//! is that call's. A dot that resolves to no operation call refuses it — a field, a
//! column, a `@[simp]` dot rule's rewrite, a receiver that denotes a sort — and in a rule's
//! own term a dot's bracket is refused as an applicative call's is.
//!
//! BACK-OUTS, measured in one build with temporary switches. The bracket dropped where the
//! typer builds the dot's call fails the witness rows, the const and compound-expression
//! row, `[Dst = String]`, the undeclared key and the own-member selection; the `Dst` rows
//! answer either way, `Dst` being inferred from the function. The loader reading no bracket
//! off a dot fails those and the `Dst` rows as well, the end-of-file sweep refusing each
//! bracket instead. `dot_bracket_selects_spec` answering false fails the own-member
//! selection alone. Each refusal of a dot that makes no call, backed out on its own, fails
//! the row of its kind; the supplier tie keeping its bracket-less advice at a call that
//! takes a bracket fails the own-member tie's advice, and `own_call_takes_spec_label`
//! answering false fails the advice of the own member that takes the spec's label, whose
//! applicative repair answers either way. The printer writing no call's bracket fails the
//! printer row — an application's, a construction's and a dot's, each on its own; a woven
//! call's fails nothing, no row printing one — and writing no companion receiver fails its
//! `comp` and `mkOn` calls; that row passes under every other back-out. The rule's own term rows and the controls pass
//! under every back-out by design.

use crate::common::{interp_for, load_errors_of, load_kb_with, one_definite_int};

/// DG57J's program: `ByHeat` and `ByName` both provide `Score[T = Colour]` and answer 3
/// and 1; `Colour` provides nothing.
const TWO_WITNESSES: &str = r#"
namespace k7.two
  import anthill.prelude.{Int64}

  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end

  sort Colour
    entity red
  end

  sort ByHeat
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 = 3
  end

  sort ByName
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 = 1
  end

{decls}
end
"#;

fn two(decls: &str) -> String {
    TWO_WITNESSES.replace("{decls}", decls)
}

/// The `Int64` an operation of no arguments answers, called through the interpreter.
fn call_int(src: &str, qn: &str) -> i64 {
    let mut interp = interp_for(src);
    match interp.call(qn, &[]).unwrap_or_else(|e| panic!("call {qn}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {qn}: expected an Int, got {other:?}"),
    }
}

/// The one load error of `src`, with its `line:col` location cut off.
fn the_refusal(src: &str) -> String {
    let errs = load_errors_of(src);
    let [err] = errs.as_slice() else {
        panic!("expected exactly one refusal, got {errs:#?}");
    };
    unlocated(err)
}

/// A rendered load error past its `line:col: ` location, which a file path may precede.
fn unlocated(err: &str) -> String {
    let parts: Vec<&str> = err.splitn(4, ':').collect();
    let is_num = |s: &str| !s.is_empty() && s.trim().chars().all(|c| c.is_ascii_digit());
    match parts.as_slice() {
        [_, line, col, msg] if is_num(line) && is_num(col) => msg.trim().to_string(),
        [line, col, rest @ ..] if is_num(line) && is_num(col) => rest.join(":").trim().to_string(),
        _ => err.to_string(),
    }
}

#[test]
fn a_dot_selects_each_witness_in_an_operation_body() {
    let src = two(
        "  sort Driver\n    \
           operation heat() -> Int64 = red().score[Score = ByHeat]()\n    \
           operation name() -> Int64 = red().score[Score = ByName]()\n    \
           operation local() -> Int64 =\n      let c = red()\n      c.score[Score = ByName]()\n  \
         end",
    );
    assert_eq!(call_int(&src, "k7.two.Driver.heat"), 3, "`ByHeat`'s `score`");
    assert_eq!(call_int(&src, "k7.two.Driver.name"), 1, "`ByName`'s `score`");
    assert_eq!(call_int(&src, "k7.two.Driver.local"), 1, "a local receiver, the loader's route");
}

/// CONTROL: the applicative spelling answers the same, either way.
#[test]
fn the_applicative_spelling_selects_the_same() {
    let src = two(
        "  sort Driver\n    \
           operation heat() -> Int64 = Score.score[Score = ByHeat](red())\n    \
           operation name() -> Int64 = Score.score[Score = ByName](red())\n  \
         end",
    );
    assert_eq!(call_int(&src, "k7.two.Driver.heat"), 3);
    assert_eq!(call_int(&src, "k7.two.Driver.name"), 1);
}

/// A const's value and a rule body's compound expression read a call's bracket as an
/// operation body does, and a dot's with it.
#[test]
fn a_const_and_a_rule_bodys_compound_expression_read_it() {
    let src = two(
        "  const hot: Int64 = red().score[Score = ByHeat]()\n  \
         sort Driver\n    operation readHot() -> Int64 = hot\n  end\n  \
         rule viaLet(?r) :- ?r <=> (let s = red().score[Score = ByName]()  s + 0)\n  \
         rule viaLambda(?r) :- \
         ?r <=> (let f = lambda (c: Colour) -> c.score[Score = ByHeat]()  f(red()))",
    );
    assert_eq!(call_int(&src, "k7.two.Driver.readHot"), 3, "the const");
    let mut kb = load_kb_with(&src);
    assert_eq!(one_definite_int(&mut kb, "k7.two.viaLet"), Some(1));
    assert_eq!(one_definite_int(&mut kb, "k7.two.viaLambda"), Some(3));
}

/// BAD3V's two shapes, a first hop and a chained one, type and run as the call written
/// applicatively does; `[Dst = String]` is read, so it is refused as it is there.
const MAP: &str = r#"
namespace k7.map
  import anthill.prelude.{List, Int64, String, MappedStream, FiniteCollection}
  import anthill.prelude.FiniteCollection.{collect}

  operation digits(xs: List[T = Int64]) -> Int64 =
    List.foldLeft(xs, 0, lambda (acc, x) -> acc * 10 + x)

{decls}
end
"#;

fn map(decls: &str) -> String {
    MAP.replace("{decls}", decls)
}

#[test]
fn a_dot_map_takes_its_destination_type() {
    let src = map(
        "  operation viaParam(xs: List[T = Int64]) -> Int64 =\n    \
           digits(xs.map[Dst = Int64](lambda x -> x + 1).collect())\n  \
         operation first() -> Int64 = viaParam([1, 2, 3])\n  \
         operation chained() -> Int64 =\n    \
           digits([1, 2].map(lambda x -> x * 3).map[Dst = Int64](lambda y -> y + 1).collect())\n  \
         operation applicative() -> Int64 =\n    \
           digits(collect(MappedStream.map[Dst = Int64]([1, 2, 3], lambda x -> x + 1)))",
    );
    assert_eq!(call_int(&src, "k7.map.first"), 234, "a parameter receiver, the loader's route");
    assert_eq!(call_int(&src, "k7.map.chained"), 47, "a chained hop");
    assert_eq!(call_int(&src, "k7.map.applicative"), 234, "control: the applicative spelling");
}

#[test]
fn a_dot_maps_wrong_destination_is_refused_as_the_applicative_calls() {
    let dot = the_refusal(&map(
        "  operation bad(xs: List[T = Int64]) -> Int64 =\n    \
           digits(xs.map[Dst = String](lambda x -> x + 1).collect())",
    ));
    let app = the_refusal(&map(
        "  operation bad(xs: List[T = Int64]) -> Int64 =\n    \
           digits(collect(MappedStream.map[Dst = String](xs, lambda x -> x + 1)))",
    ));
    assert!(dot.contains("expected Int64 -> String, got Int64 -> Int64"), "{dot}");
    assert_eq!(dot, app, "one refusal, in the same words");
}

const POINT: &str = r#"
namespace k7.point
  import anthill.prelude.{Int64, String, Relation}

  sort P
    entity pt(x: Int64, y: Int64)
    operation getX(p: P) -> Int64 = p.x
    operation regular(p: P, n: Int64) -> Int64 = n
    rule dr: dot_apply(?e, special, ?n) <=> regular(?e, ?n) @[simp]
  end

  sort Box
    sort V = ?
    operation tag() -> Int64 = 7
  end

  sort People
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

{decls}
end
"#;

fn point(decls: &str) -> String {
    POINT.replace("{decls}", decls)
}

/// A key the resolved callee does not declare is refused as on the applicative call.
#[test]
fn an_undeclared_key_is_refused_in_the_applicative_calls_words() {
    let dot = the_refusal(&point("  operation go(p: P) -> Int64 = p.getX[T = Int64]()"));
    let app = the_refusal(&point("  operation go(p: P) -> Int64 = P.getX[T = Int64](p)"));
    assert!(dot.contains("unknown type-param 'T'"), "{dot}");
    assert_eq!(dot, app, "one refusal, in the same words");
}

/// A dot that resolves to no operation call refuses its bracket, naming what it is.
#[test]
fn a_dot_that_makes_no_call_refuses_its_bracket() {
    for (decl, says) in [
        (
            "  operation go(p: P) -> Int64 = p.x[T = Int64]()",
            "the dot reads the field `x` of its receiver",
        ),
        (
            "  operation go() -> Relation[T = (age: Int64)] = person_row.age[T = Int64]()",
            "the dot selects the column `age` of its receiver",
        ),
        (
            "  operation go(p: P) -> Int64 = p.special[T = Int64](7)",
            "the dot is rewritten by a `@[simp]` dot rule of its receiver's sort",
        ),
        (
            "  operation go() -> Int64 =\n    let t = Box[V = Int64]\n    t.tag[T = Int64]()",
            "are not read on a receiver that denotes a sort; write the call on the sort",
        ),
    ] {
        let err = the_refusal(&point(decl));
        assert!(err.contains("call-site type arguments on the dot") && err.contains(says), "{decl}: {err}");
    }
}

/// CONTROL: the same dots without a bracket load and answer.
#[test]
fn the_same_dots_without_a_bracket_answer() {
    let src = point(
        "  sort Driver\n    \
           operation field() -> Int64 = pt(x: 5, y: 6).x()\n    \
           operation rule() -> Int64 = pt(x: 5, y: 6).special(8)\n    \
           operation sorted() -> Int64 =\n      let t = Box[V = Int64]\n      t.tag()\n  \
         end",
    );
    assert_eq!(call_int(&src, "k7.point.Driver.field"), 5);
    assert_eq!(call_int(&src, "k7.point.Driver.rule"), 8);
    assert_eq!(call_int(&src, "k7.point.Driver.sorted"), 7);
}

/// In a rule's own term a dot's bracket is refused as an applicative call's is, naming the
/// call as written.
#[test]
fn a_rule_terms_dot_refuses_its_bracket() {
    for (decl, callee) in [
        ("  rule a(?p, ?r) :- ?r <=> ?p.getX[T = Int64]()", "`getX[…](…)`"),
        ("  rule b(?p, ?r) :- ?p.getX[T = Int64](?r)", "`getX[…](…)`"),
        ("  rule c(p: P, ?r) :- ?r <=> p.getX[T = Int64]()", "`p.getX[…](…)`"),
        ("  rule d(?r) :- ?r <=> pt(x: 3, y: 4).getX[T = Int64]()", "`getX[…](…)`"),
        ("  fact ?x.getX[T = Int64](?y)", "`getX[…](…)`"),
        ("  rule e(?r) :- ?r <=> P.getX[T = Int64](pt(x: 3, y: 4))", "`P.getX[…](…)`"),
    ] {
        let err = the_refusal(&point(decl));
        assert!(
            err.contains(&format!("call-site type arguments {callee} are not supported here"))
                && err.contains("The bracket is read only on a call in an OPERATION BODY"),
            "{decl}: {err}",
        );
    }
}

/// A dot rule's head is no call and introduces no type variable: its bracket, bare or
/// binding, is refused as a fact head's is. Read as a rule head's introducer, `[T]` was
/// refused for want of a bounding guard instead, and with one would have loaded, meaning
/// nothing to the dot rule's firing (measured before the loader skipped a dot's head).
#[test]
fn a_dot_rule_heads_bracket_is_refused() {
    for bracket in ["[T]", "[T = Int64]"] {
        let err = the_refusal(&point(&format!(
            "  sort Q\n    entity q(n: Int64)\n    \
               operation reg(q: Q, n: Int64) -> Int64 = n\n    \
               rule dq: ?e.other{bracket}(?n) <=> reg(?e, ?n) @[simp]\n  end"
        )));
        assert!(
            err.contains("call-site type arguments `other[…](…)` are not supported here"),
            "{bracket}: {err}",
        );
    }
}

/// A dot whose own member backs a spec, beside a witness that provides it for the
/// receiver: the bracket that selects the witness makes the dot the spec operation's call,
/// as written applicatively. Without it the two tie, and the repair is the bracket.
#[test]
fn a_dot_selects_a_witness_over_its_own_member() {
    let ns = "k7.own";
    let src = crate::wi1035_dot_member_supplier_tie_test::body_less(
        ns,
        "    operation describe(x: Leaf) -> Int64 = 7\n",
        crate::wi1027_bodyless_supplier_tie_test::RIVAL_WITNESS,
        "  sort Driver\n    \
           operation dot() -> Int64 = leaf().describe[Desc = Rival]()\n    \
           operation app() -> Int64 = Desc.describe[Desc = Rival](leaf())\n  \
         end\n",
    );
    assert_eq!(call_int(&src, "k7.own.Driver.dot"), 9, "`Rival`'s `describe`");
    assert_eq!(call_int(&src, "k7.own.Driver.app"), 9, "control: the applicative spelling");

    let tie = the_refusal(&crate::wi1035_dot_member_supplier_tie_test::body_less(
        ns,
        "    operation describe(x: Leaf) -> Int64 = 7\n",
        crate::wi1027_bodyless_supplier_tie_test::RIVAL_WITNESS,
        "  sort Driver\n    operation dot() -> Int64 = leaf().describe()\n  end\n",
    ));
    assert!(
        tie.contains("ambiguous dispatch of `k7.own.Desc.describe` on carrier `k7.own.Leaf`")
            && tie.contains("or write `[Spec = Witness]` in the call's bracket list"),
        "{tie}",
    );
}

/// An own member that takes the spec's label for its own call — a type parameter `Desc`,
/// or an anonymous requirement on `Desc` — binds `[Desc = Rival]` written on the dot, and
/// the two still tie. The selection is written on the call applicatively, which answers.
#[test]
fn an_own_member_taking_the_spec_label_sends_the_selection_applicative() {
    let ns = "k7.own";
    for member in [
        "    operation describe[Desc](x: Leaf) -> Int64 = 7\n",
        "    operation describe(x: Leaf) -> Int64 requires Desc[T = Leaf] = 7\n",
    ] {
        let program = |tail: &str| {
            crate::wi1035_dot_member_supplier_tie_test::body_less(
                ns,
                member,
                crate::wi1027_bodyless_supplier_tie_test::RIVAL_WITNESS,
                tail,
            )
        };
        for call in ["leaf().describe()", "leaf().describe[Desc = Rival]()"] {
            let err = the_refusal(&program(&format!(
                "  sort Driver\n    operation dot() -> Int64 = {call}\n  end\n"
            )));
            assert!(
                err.contains("ambiguous dispatch of `k7.own.Desc.describe` on carrier `k7.own.Leaf`")
                    && err.contains(
                        "or write the call applicatively, \
                         `k7.own.Desc.describe[Spec = Witness](…)`, naming a witness sort"
                    ),
                "{member} {call}: {err}",
            );
        }
        let advised = program(
            "  sort Driver\n    \
               operation app() -> Int64 = Desc.describe[Desc = Rival](leaf())\n  \
             end\n",
        );
        assert_eq!(call_int(&advised, "k7.own.Driver.app"), 9, "{member}: `Rival`'s `describe`");
    }
}

/// A qualified key selects nothing — rung 2 refuses one — so the dot is not rerouted on it,
/// and the tie stands. Asked by short name, it panicked in a debug build (`same_label`'s
/// assertion on two qualified names with one short name), measured.
#[test]
fn a_qualified_key_selects_no_witness_on_a_dot() {
    let err = the_refusal(&crate::wi1035_dot_member_supplier_tie_test::body_less(
        "k7.own",
        "    operation describe(x: Leaf) -> Int64 = 7\n",
        crate::wi1027_bodyless_supplier_tie_test::RIVAL_WITNESS,
        "  sort Driver\n    operation dot() -> Int64 = leaf().describe[other.Desc = Rival]()\n  end\n",
    ));
    assert!(
        err.contains("ambiguous dispatch of `k7.own.Desc.describe` on carrier `k7.own.Leaf`"),
        "{err}",
    );
}

/// The text the printer writes for an operation's stored body.
fn printed_body(kb: &anthill_core::kb::KnowledgeBase, qn: &str) -> String {
    let op = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("{qn} is declared"));
    let body = kb.op_body_node(op).unwrap_or_else(|| panic!("{qn} has a body"));
    anthill_core::persistence::print::TermPrinter::new(kb).print_occurrence(body)
}

/// The printer writes a call's bracket, its entries in the type spelling: on the stored
/// body, where the typer has replaced the dot by the call it resolves to, on the body as the
/// loader built it, and in a rule's body. A bracket with no arguments keeps its
/// parentheses, and a companion receiver's instantiation is written before the member; a
/// construction's are written as a call's. A woven call (`apply_within`) writes its bracket
/// too, and no row prints one: the weave reaches the calls of a rule's own term, which take
/// no bracket (WI-20261024-TC54R).
#[test]
fn the_printer_writes_a_calls_bracket() {
    let src = two(
        "  sort Driver\n    \
           operation idt[W](x: W) -> W = x\n    \
           operation zero[W]() -> Int64 = 0\n    \
           operation app() -> Int64 = Score.score[Score = ByHeat](red())\n    \
           operation dot() -> Int64 = red().score[Score = ByName]()\n    \
           operation pos() -> Int64 = Driver.idt[Int64](Driver.idt(3))\n    \
           operation bare() -> Int64 = Driver.zero[W = List[T = Colour]]()\n    \
           operation comp() -> Map[K = String, V = Int64] = Map[K = String, V = Int64].empty()\n    \
           operation mkAt() -> Box[V = Int64] = Box.mk[V = Int64](v: 5)\n    \
           operation mkOn() -> Box[V = Int64] = Box[V = Int64].mk(v: 5)\n  \
         end\n  \
         sort Box\n    sort V = ?\n    entity mk(v: V)\n  end\n  \
         rule viaDot(?r) :- ?r <=> (let s = red().score[Score = ByHeat]()  s + 0)\n",
    )
    .replace("import anthill.prelude.{Int64}", "import anthill.prelude.{Int64, List, Map, String}");
    let kb = load_kb_with(&src);
    for (qn, printed) in [
        ("app", "score[Score = ByHeat](red)"),
        ("dot", "score[Score = ByName](red)"),
        ("pos", "idt[Int64](idt(3))"),
        ("bare", "zero[W = List[T = Colour]]()"),
        ("comp", "].empty()"),
        ("mkAt", "mk[V = Int64](v: 5)"),
        ("mkOn", "Box[V = Int64].mk(v: 5)"),
    ] {
        let got = printed_body(&kb, &format!("k7.two.Driver.{qn}"));
        assert!(got.ends_with(printed), "{qn}: `{got}`");
    }
    let comp = printed_body(&kb, "k7.two.Driver.comp");
    assert!(
        comp.starts_with("Map[") && comp.contains("K = String") && comp.contains("V = Int64"),
        "the receiver's instantiation: `{comp}`",
    );
    let [rule] = kb.rule_ids_by_qn("k7.two.viaDot")[..] else {
        panic!("one clause of viaDot");
    };
    let rule = anthill_core::persistence::print::TermPrinter::new(&kb).print_rule(rule);
    assert!(rule.contains("let s = score[Score = ByHeat](red) in"), "{rule}");

    let untyped = crate::common::try_load_kb_untyped_with(&src).expect("loads untyped");
    assert_eq!(printed_body(&untyped, "k7.two.Driver.dot"), "red.score[Score = ByName]()");
}

