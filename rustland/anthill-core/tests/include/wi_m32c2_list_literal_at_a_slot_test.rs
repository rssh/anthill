//! WI-20261013-M32C2 — A LIST LITERAL AT A SLOT TAKES THE SLOT'S ELEMENT TYPE.
//!
//! ## The defect
//!
//! ```text
//! sort Sp  { operation size(s: Sp) -> Int64 }
//! sort Car { entity car(n: Int64); provides Sp; operation size(c: Car) -> Int64 = 40 }
//! sort Van { entity van(n: Int64); provides Sp; operation size(c: Van) -> Int64 = 2 }
//! operation total(xs: List[T = Sp]) -> Int64 = …
//!
//! total([car(n: 1), van(n: 2)])
//!   type mismatch in list.element 2 (collection-element-join): expected Car, got Van
//! ```
//!
//! A declared return and an annotated `let` already read their element type before the
//! elements (`-> List[T = Sp] = [car(n: 1), van(n: 2)]` loaded); an argument or field slot did
//! so only when its element type named a constructor or was callable. Everywhere else the
//! literal joined its elements first, and `Car ⊔ Van` has no join — each is admissible at
//! `Sp`, neither is the other.
//!
//! ## The decision (user, 2026-10-14)
//!
//! THE SLOT'S TYPE FIRST: an argument or field slot whose element type holds no type
//! parameter the call instantiates — as written, or with what the call's own bracket and
//! receiver fix — declares the literal's element type, as a return and a `let` do, and every
//! element is checked against it. A slot whose element type the call instantiates (the
//! callee's `[A]`, a data sort's `T`, a constructor's sort parameter) declares nothing: the
//! literal joins, and the call instantiates the parameter from that join (kernel-language
//! §8.1). A literal at no expected type joins as before. The alternative — keep the join, and
//! take the slot's type where the elements have none — was declined.
//!
//! A parameter the call instantiates is a WRITTEN one (user, 2026-10-14: "When variable is
//! not written - we can't reference it"). `List[T = Sp]` and `List[T = Sp[T = ?]]` leave `T`
//! unwritten, so each element is checked against `Sp` on its own and a list may hold
//! providers at different `T`; `List[T = Sp[T = X]]` over the operation's own `[X]` is one
//! `X` for the list, and its literal joins.
//!
//! And, in the same change, a call of an ARROW-TYPED VARIABLE reads its slots off the arrow,
//! the list its check already reads, so it takes every slot hint a named operation's call
//! takes; it took none (`f(red(v: 1))` at `(c: Colour.red)` was refused `expected red, got
//! Colour`). A CONSTRUCTION IN AN ARGUMENT is typed at the slot's instance where that reaches
//! a variant in one of its fields (`takeBox(box(x: red(v: 1)))`, user, 2026-10-14) — §8.2 one
//! level down, found by `/code-review`.
//!
//! ## BACK-OUTS, one at a time — this file, and the whole `wi_tests` binary (measured)
//!
//! 1. **The ground arm** of `seq_slot_arg_hint` (a slot declares a ground element type):
//!    **9 fail here** — every row that loads or drives a literal at such a slot, the
//!    construction's and the bracket's included, since they reach the same arm — and **4
//!    elsewhere**, all messages: `alias_written_name_test::a_mismatch_names_an_alias_inside_-
//!    a_type` and three cells of `typer_capability_matrix_test` (`a_literal_is_checked_on_-
//!    every_route_…`, `a_lambda_inside_a_list_literal`, `the_row_remainders`).
//! 2. **The slot read as the signature writes it**, not as the call has it: **2 fail** —
//!    `an_operations_bracket_fixes_its_parameter_for_the_literal` and
//!    `a_staged_literal_reads_the_calls_bracket`. Nothing else in the binary moves.
//! 3. **The staged literal hinted without the call's bracket** (`one_arg_hint(…, None)` in the
//!    visit's staged branch): **1 fails** — `a_staged_literal_reads_the_calls_bracket`.
//! 4. **The constructor peer** `seq_field_expected_from_ctor`: **1 fails** —
//!    `a_constructions_bracket_or_receiver_fixes_its_parameter_for_the_literal`.
//! 5. **A function value's slots** (`function_value_param_slots`): **2 fail** — the two
//!    `a_call_of_an_arrow_typed_variable_…` rows, the second on its message (`expected red,
//!    got Colour` where it names `blue`).
//! 6. **The constructor peer's checking-direction arms read at the expected instance**
//!    (`seq_field_expected_from_ctor` past `fixed`): **1 fails** —
//!    `a_literal_of_variants_in_a_parametric_field_reads_the_expected_instance`.
//! 7. **The slot's instance pushed into a construction argument for a variant field**
//!    (`ctor_arg_unlocks_a_field_hint`'s construction and literal arms): **1 fails** —
//!    `a_construction_in_an_argument_reads_the_slots_instance`.
//! 8. **An unwritten variable read as a parameter of the call** (every variable counted, as
//!    `type_is_ground` counts them): **1 fails** —
//!    `an_unwritten_parameter_is_each_elements_own_and_a_written_one_the_calls`.
//!
//! CONTROLS — green under every back-out, by design and measured:
//! `a_literal_at_no_expected_type_still_joins`, `a_slot_the_call_instantiates_leaves_the_-
//! literal_to_its_join`, `control_a_rule_body_call_answers`; and outside this file the rows of
//! `wi_wbxgx_collection_literal_element_join_test` and `wi_7jdwy_…::control_an_unhinted_-
//! literal_still_types_from_its_elements`, which now reach the join through an unannotated
//! `let`.

use crate::common::{query_unary, try_load_kb_with};
use anthill_core::eval::Value;

fn errs_of(src: &str) -> Vec<String> {
    try_load_kb_with(src)
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e)
}

fn assert_reports(src: &str, needle: &str, what: &str) {
    let errs = errs_of(src);
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{what}: no diagnostic containing {needle:?}; got {errs:#?}"
    );
}

fn run(src: &str, entry: &str) -> i64 {
    crate::common::run_int64(src, entry).unwrap_or_else(|e| panic!("{entry}: {e}"))
}

/// The ticket's sorts: two providers of one spec, each answering its own `size`. `{sp}` is
/// the spec's body, `{prov}` the provision clause — the two spellings the ticket names.
fn program(ns: &str, sp: &str, prov: &str, rest: &str) -> String {
    format!(
        r#"
namespace test.m32c2.{ns}
  import anthill.prelude.{{Int64, Bool, List}}
  sort Sp
{sp}    operation size(s: Sp) -> Int64
  end
  sort Car
    entity car(n: Int64)
    {prov}
    operation size(c: Car) -> Int64 = 40
  end
  sort Van
    entity van(n: Int64)
    {prov}
    operation size(c: Van) -> Int64 = 2
  end
  operation total(xs: List[T = Sp]) -> Int64 = List.foldLeft(xs, 0, lambda (acc, c) -> acc + Sp.size(c))
{rest}
end
"#
    )
}

fn plain(ns: &str, rest: &str) -> String {
    program(ns, "", "provides Sp", rest)
}

/// THE TICKET'S PROGRAM, in both spellings of `Sp` — with no type parameter, and with
/// `sort T = ?` provided at `Int64` — answers 42.
///
/// BACKED OUT (1): refused, `list.element 2 (collection-element-join): expected Car, got Van`.
#[test]
fn the_ticket_program_answers_42_in_both_spellings_of_the_spec() {
    let rest = "  operation q() -> Int64 = total([car(n: 1), van(n: 2)])";
    let bare = plain("bare", rest);
    assert_eq!(run(&bare, "test.m32c2.bare.q"), 42);
    let param = program("param", "    sort T = ?\n", "provides Sp[T = Int64]", rest);
    assert_eq!(run(&param, "test.m32c2.param.q"), 42);
}

/// A LITERAL WHOSE ELEMENTS HAVE NO COMMON TYPE AT THE SLOT is still refused, at the
/// offending element, naming the SLOT's type — in either order.
///
/// BACKED OUT (1): still refused, by the join, naming `Car` and `Int64` instead of `Sp`.
#[test]
fn an_element_the_slot_does_not_admit_is_refused_naming_the_slots_type() {
    let after = plain("after", "  operation q() -> Int64 = total([car(n: 1), 5])");
    assert_reports(
        &after,
        "list.element 2 (collection-element): expected Sp, got Int64",
        "an Int64 after a Car, at a List[T = Sp] slot",
    );
    let before = plain("before", "  operation q() -> Int64 = total([5, car(n: 1)])");
    assert_reports(
        &before,
        "list.element 1 (collection-element): expected Sp, got Int64",
        "the same two elements in the other order name the same slot type",
    );
}

/// AN UNWRITTEN PARAMETER IS NO PARAMETER OF THE CALL: `Sp` bare and `Sp[T = ?]` leave `T`
/// to each element, so a list may hold providers at different `T` and the anonymous `?`
/// declares exactly as the bare spelling does. A WRITTEN one — the operation's own `[X]` —
/// is one `X` for the list, which the call instantiates: the literal is left to its join,
/// and two providers have none, unless the bracket fixes `X`.
///
/// BACKED OUT (8): the first program does not load, `anonymous`'s literal refused by the
/// join. The written-`X` refusal is green either way, by design.
#[test]
fn an_unwritten_parameter_is_each_elements_own_and_a_written_one_the_calls() {
    let mixed = program(
        "mixed",
        "    sort T = ?\n",
        "provides Sp[T = Int64]",
        "  sort Bike\n    entity bike(n: Int64)\n    provides Sp[T = String]\n    \
         operation size(b: Bike) -> Int64 = 5\n  end\n  \
         operation anon(xs: List[T = Sp[T = ?]]) -> Int64 = List.length(xs)\n  \
         operation bare() -> Int64 = total([car(n: 1), bike(n: 2)])\n  \
         operation anonymous() -> Int64 = anon([car(n: 1), van(n: 2)])\n  \
         operation fixedX[X](xs: List[T = Sp[T = X]]) -> Int64 = List.length(xs)\n  \
         operation bracketed() -> Int64 = fixedX[X = Int64]([car(n: 1), van(n: 2)])",
    );
    for (entry, want) in [("bare", 45), ("anonymous", 2), ("bracketed", 2)] {
        assert_eq!(
            run(&mixed, &format!("test.m32c2.mixed.{entry}")),
            want,
            "{entry}"
        );
    }
    let written = program(
        "written",
        "    sort T = ?\n",
        "provides Sp[T = Int64]",
        "  operation fixedX[X](xs: List[T = Sp[T = X]]) -> Int64 = List.length(xs)\n  \
         operation q() -> Int64 = fixedX([car(n: 1), van(n: 2)])",
    );
    assert_reports(
        &written,
        "list.element 2 (collection-element-join): expected Car, got Van",
        "a written X is the call's to instantiate, from the literal's join",
    );
}

/// CONTROL — A LITERAL AT NO EXPECTED TYPE JOINS AS IT DID: an unannotated `let` declares
/// nothing, so `[car(…), van(…)]` there is refused by the join, and `[car(…), car(…)]` is a
/// `List[T = Car]` the slot then admits.
///
/// Green under every back-out, by design.
#[test]
fn a_literal_at_no_expected_type_still_joins() {
    let mixed = plain(
        "nojoin",
        "  operation q() -> Int64 =\n    let xs = [car(n: 1), van(n: 2)]\n    total(xs)",
    );
    assert_reports(
        &mixed,
        "list.element 2 (collection-element-join): expected Car, got Van",
        "an unannotated let joins its literal",
    );
    let same = plain(
        "join",
        "  operation q() -> Int64 =\n    let xs = [car(n: 1), car(n: 2)]\n    total(xs)",
    );
    assert_eq!(run(&same, "test.m32c2.join.q"), 80);
}

/// A FIELD SLOT DECLARES as an argument slot does, by name and by position.
///
/// BACKED OUT (1): both refused by the join.
#[test]
fn a_field_slot_declares_its_element_type() {
    let src = plain(
        "field",
        "  sort Bag\n    entity bag(xs: List[T = Sp])\n  end\n  \
         operation sum(b: Bag) -> Int64 = total(b.xs)\n  \
         operation named() -> Int64 = sum(bag(xs: [car(n: 1), van(n: 2)]))\n  \
         operation positional() -> Int64 = sum(bag([van(n: 2), car(n: 1)]))",
    );
    assert_eq!(run(&src, "test.m32c2.field.named"), 42);
    assert_eq!(run(&src, "test.m32c2.field.positional"), 42);
}

/// THE DECLARATION REACHES A NESTED LITERAL, AND THROUGH AN ALIAS: the outer slot's element
/// type is the inner literal's expected type, and a slot written as an alias of
/// `List[T = Sp]` is that type.
///
/// BACKED OUT (1): both refused by the join.
#[test]
fn the_slot_reaches_a_nested_literal_and_through_an_alias() {
    let src = plain(
        "nested",
        "  operation nest(xss: List[T = List[T = Sp]]) -> Int64 =\n    \
         List.foldLeft(xss, 0, lambda (acc, xs) -> acc + total(xs))\n  \
         sort Sps = List[T = Sp]\n  \
         operation viaAlias(xs: Sps) -> Int64 = total(xs)\n  \
         operation q() -> Int64 = nest([[car(n: 1)], [van(n: 2), van(n: 3)]])\n  \
         operation q2() -> Int64 = viaAlias([car(n: 1), van(n: 2)])",
    );
    assert_eq!(run(&src, "test.m32c2.nested.q"), 44);
    assert_eq!(run(&src, "test.m32c2.nested.q2"), 42);
}

/// THE SLOT DECLARES WHEREVER THE CALL STANDS: a named argument, a generic operation's
/// written slot, a slot beside a `requires`, a spec member called by name and by dot, an
/// `if` condition, a lambda body, a `const`'s value, and the empty literal.
///
/// BACKED OUT (1): fails at its first entry, the literal refused by the join.
#[test]
fn the_slot_declares_at_every_placement_of_the_call() {
    let src = plain(
        "places",
        "  sort Agg\n    operation sum(a: Agg, xs: List[T = Sp]) -> Int64\n  end\n  \
         sort Ag\n    entity ag(k: Int64)\n    provides Agg\n    \
         operation sum(a: Ag, xs: List[T = Sp]) -> Int64 = total(xs)\n  end\n  \
         operation gen[A](xs: List[T = Sp], y: A) -> Int64 = total(xs)\n  \
         operation req[A](a: A, xs: List[T = Sp]) -> Int64 requires Sp[A] = total(xs)\n  \
         const k: Int64 = total([car(n: 1), van(n: 2)])\n  \
         operation named() -> Int64 = total(xs: [car(n: 1), van(n: 2)])\n  \
         operation generic() -> Int64 = gen([car(n: 1), van(n: 2)], true)\n  \
         operation required() -> Int64 = req(car(n: 1), [car(n: 1), van(n: 2)])\n  \
         operation member() -> Int64 = Agg.sum(ag(k: 0), [car(n: 1), van(n: 2)])\n  \
         operation dot() -> Int64 = ag(k: 0).sum([car(n: 1), van(n: 2)])\n  \
         operation cond() -> Int64 = if total([car(n: 1), van(n: 2)]) > 41 then 1 else 0\n  \
         operation inLambda() -> Int64 =\n    \
         List.foldLeft([1, 2], 0, lambda (acc, i) -> acc + total([car(n: i), van(n: i)]))\n  \
         operation viaConst() -> Int64 = k\n  \
         operation empty() -> Int64 = total([])",
    );
    for (entry, want) in [
        ("named", 42),
        ("generic", 42),
        ("required", 42),
        ("member", 42),
        ("dot", 42),
        ("cond", 1),
        ("inLambda", 84),
        ("viaConst", 42),
        ("empty", 0),
    ] {
        assert_eq!(
            run(&src, &format!("test.m32c2.places.{entry}")),
            want,
            "{entry}"
        );
    }
}

/// CONTROL — A RULE BODY'S CALL answers too, and did before: there the literal is lowered to
/// the `cons`/`nil` spine (§4.6) and never reaches the slot's typing. Green under every
/// back-out, measured.
#[test]
fn control_a_rule_body_call_answers() {
    let src = plain(
        "rule",
        "  rule r(?x) :- ?x <=> total([car(n: 1), van(n: 2)])",
    );
    let mut kb = try_load_kb_with(&src).unwrap_or_else(|e| panic!("loads: {e:#?}"));
    let answers = query_unary(&mut kb, "test.m32c2.rule.r");
    assert_eq!(answers.len(), 1, "one answer: {answers:?}");
    assert!(
        matches!(answers[0], (Value::Int(42), true)),
        "a definite 42: {answers:?}"
    );
}

/// CONTROL — A SLOT WHOSE ELEMENT TYPE THE CALL INSTANTIATES DECLARES NOTHING: the callee's
/// own `[A]`, `List.append`'s `T` (whose receiver, a value, fixes nothing — §8.1), and a
/// constructor's sort parameter at a declared return all leave the literal to its join, which
/// two providers do not have. A literal that does join is instantiated by the call as the
/// arguments' join: `List.append(cars, [s])` with `s: Sp` is a list of `Sp`.
///
/// Green under every back-out, by design.
#[test]
fn a_slot_the_call_instantiates_leaves_the_literal_to_its_join() {
    let join = "list.element 2 (collection-element-join): expected Car, got Van";
    let generic = plain(
        "gen",
        "  operation cnt[A](xs: List[T = A]) -> Int64 = List.length(xs)\n  \
         operation q() -> Int64 = cnt([car(n: 1), van(n: 2)])",
    );
    assert_reports(&generic, join, "the callee's own type parameter");
    let append = plain(
        "app",
        "  operation q(ss: List[T = Sp]) -> List[T = Sp] = List.append(ss, [car(n: 1), van(n: 2)])",
    );
    assert_reports(&append, join, "a data sort's parameter");
    let dot = plain(
        "dot",
        "  operation q(ss: List[T = Sp]) -> List[T = Sp] = ss.append([car(n: 1), van(n: 2)])",
    );
    assert_reports(&dot, join, "a data sort's parameter, the receiver a value");
    let ctor = plain(
        "ctor",
        "  sort Box\n    sort V = ?\n    entity box(xs: List[T = V])\n  end\n  \
         operation q() -> Box[V = Sp] = box(xs: [car(n: 1), van(n: 2)])",
    );
    assert_reports(
        &ctor,
        join,
        "a constructor's sort parameter, at a declared return",
    );

    let joins = plain(
        "joins",
        "  operation viaAppend(cs: List[T = Car], s: Sp) -> Int64 = total(List.append(cs, [s]))\n  \
         operation q() -> Int64 = viaAppend([car(n: 1)], van(n: 2))",
    );
    assert_eq!(run(&joins, "test.m32c2.joins.q"), 42);
}

/// WHAT AN OPERATION'S BRACKET FIXES IS THE SLOT'S: `cnt[A = Sp]` declares `Sp` for the
/// literal at `xs: List[T = A]`, where `cnt(…)` leaves it to its join.
///
/// BACKED OUT (1) or (2): refused by the join.
#[test]
fn an_operations_bracket_fixes_its_parameter_for_the_literal() {
    let src = plain(
        "opbracket",
        "  operation cnt[A](xs: List[T = A]) -> Int64 = List.length(xs)\n  \
         operation q() -> Int64 = cnt[A = Sp]([car(n: 1), van(n: 2)])",
    );
    assert_eq!(run(&src, "test.m32c2.opbracket.q"), 2);
}

/// A STAGED LITERAL READS THE CALL'S BRACKET: beside a variable argument the call types the
/// literal before its siblings, and the bracket is bound before any argument is read.
///
/// BACKED OUT (1), (2) or (3): refused by the join.
#[test]
fn a_staged_literal_reads_the_calls_bracket() {
    let src = plain(
        "staged",
        "  operation viaAppend(ss: List[T = Sp]) -> Int64 =\n    \
         total(List.append[T = Sp](ss, [car(n: 1), van(n: 2)]))\n  \
         operation q() -> Int64 = viaAppend([van(n: 3)])",
    );
    assert_eq!(run(&src, "test.m32c2.staged.q"), 44);
}

/// A LITERAL OF VARIANTS IN A FIELD TYPED BY THE SORT'S PARAMETER is classified at the
/// instance the construction is expected at, as a single variant there is (§8.2): the
/// variant is a checking-direction reading, which the expectation reaches.
///
/// BACKED OUT (6): refused, `expected Bag[V = red], got Bag[V = Colour]` — the elements
/// classified at the parent — and the sibling with the same message, at the return rather
/// than at `blue`.
#[test]
fn a_literal_of_variants_in_a_parametric_field_reads_the_expected_instance() {
    let src = plain(
        "varfield",
        "  sort Colour\n    entity red(v: Int64)\n    entity blue(v: Int64)\n  end\n  \
         sort Bag\n    sort V = ?\n    entity bag(xs: List[T = V])\n  end\n  \
         operation mk() -> Bag[V = Colour.red] = bag(xs: [red(v: 1), red(v: 2)])\n  \
         operation n() -> Int64 = List.length(mk().xs)",
    );
    assert_eq!(run(&src, "test.m32c2.varfield.n"), 2);
    let sibling = plain(
        "varsibling",
        "  sort Colour\n    entity red(v: Int64)\n    entity blue(v: Int64)\n  end\n  \
         sort Bag\n    sort V = ?\n    entity bag(xs: List[T = V])\n  end\n  \
         operation mk() -> Bag[V = Colour.red] = bag(xs: [red(v: 1), blue(v: 2)])",
    );
    assert_reports(
        &sibling,
        "list.element 2 (collection-element): expected red, got blue",
        "a sibling variant in the field's literal",
    );
}

/// WHAT A CONSTRUCTION FIXES IS ITS FIELD'S: a constructor's bracket and a sort-application
/// receiver bind `V`, so `xs: List[T = V]` is a `List[T = Sp]` slot.
///
/// BACKED OUT (1) or (4): refused by the join.
#[test]
fn a_constructions_bracket_or_receiver_fixes_its_parameter_for_the_literal() {
    let src = plain(
        "ctorfixed",
        "  sort Box\n    sort V = ?\n    entity box(xs: List[T = V])\n  end\n  \
         operation unbox(b: Box[V = Sp]) -> Int64 = total(b.xs)\n  \
         operation bracket() -> Int64 = unbox(Box.box[V = Sp](xs: [car(n: 1), van(n: 2)]))\n  \
         operation receiver() -> Int64 = unbox(Box[V = Sp].box(xs: [car(n: 1), van(n: 2)]))",
    );
    assert_eq!(run(&src, "test.m32c2.ctorfixed.bracket"), 42);
    assert_eq!(run(&src, "test.m32c2.ctorfixed.receiver"), 42);
}

/// A CONSTRUCTION IN AN ARGUMENT is typed at the slot's instance where that reaches a
/// variant in one of its fields, so §8.2 holds one level down, for a variant and for a
/// literal of variants, as it does at a declared return; a sibling is refused by name.
///
/// BACKED OUT (7): refused, `expected Box[V = red], got Box[V = Colour]` and its `Bag` twin
/// — the construction typed with no expectation, its variant classified at the parent.
#[test]
fn a_construction_in_an_argument_reads_the_slots_instance() {
    let decls = "  sort Colour\n    entity red(v: Int64)\n    entity blue(v: Int64)\n  end\n  \
                 sort Box\n    sort V = ?\n    entity box(x: V)\n  end\n  \
                 sort Bag\n    sort V = ?\n    entity bag(xs: List[T = V])\n  end\n  \
                 operation takeBox(b: Box[V = Colour.red]) -> Int64 = b.x.v\n  \
                 operation takeBag(b: Bag[V = Colour.red]) -> Int64 = List.length(b.xs)\n";
    let src = plain(
        "nested",
        &format!(
            "{decls}  operation named() -> Int64 = takeBox(box(x: red(v: 7)))\n  \
             operation positional() -> Int64 = takeBox(box(red(v: 8)))\n  \
             operation literal() -> Int64 = takeBag(bag(xs: [red(v: 1), red(v: 2)]))"
        ),
    );
    for (entry, want) in [("named", 7), ("positional", 8), ("literal", 2)] {
        assert_eq!(
            run(&src, &format!("test.m32c2.nested.{entry}")),
            want,
            "{entry}"
        );
    }
    let sibling = plain(
        "nestedsib",
        &format!("{decls}  operation q() -> Int64 = takeBag(bag(xs: [red(v: 1), blue(v: 2)]))"),
    );
    assert_reports(
        &sibling,
        "list.element 2 (collection-element): expected red, got blue",
        "a sibling variant in the nested construction's literal",
    );
}

/// A FUNCTION VALUE TAKES THE SLOT HINTS A NAMED OPERATION TAKES: a literal at a written
/// element type, a variant (§8.2), a literal of variants, a bare operation name lifted at an
/// arrow slot, and a two-parameter arrow called positionally and by name.
///
/// BACKED OUT (5): the program is refused — `expected red, got Colour`, a literal with no
/// join, a bare name with no arrow to lift against. (1) fails it at its `list` entry.
#[test]
fn a_call_of_an_arrow_typed_variable_takes_the_slot_hints() {
    let src = plain(
        "arrow",
        "  sort Colour\n    entity red(v: Int64)\n    entity blue(v: Int64)\n  end\n  \
         operation inc(x: Int64) -> Int64 = x + 1\n  \
         operation redV(c: Colour.red) -> Int64 = c.v\n  \
         operation redsV(cs: List[T = Colour.red]) -> Int64 = List.length(cs)\n  \
         operation at41(g: (x: Int64) -> Int64) -> Int64 = g(41)\n  \
         operation pair(a: Int64, c: Colour.red) -> Int64 = a + c.v\n  \
         operation appList(f: (xs: List[T = Sp]) -> Int64) -> Int64 = f([car(n: 1), van(n: 2)])\n  \
         operation appRed(f: (c: Colour.red) -> Int64) -> Int64 = f(red(v: 7))\n  \
         operation appReds(f: (cs: List[T = Colour.red]) -> Int64) -> Int64 = f([red(v: 1), red(v: 2)])\n  \
         operation appName(f: (g: (x: Int64) -> Int64) -> Int64) -> Int64 = f(inc)\n  \
         operation appTwo(f: (a: Int64, c: Colour.red) -> Int64) -> Int64 = f(1, red(v: 2)) + f(c: red(v: 4), a: 8)\n  \
         operation list() -> Int64 = appList(total)\n  \
         operation variant() -> Int64 = appRed(redV)\n  \
         operation variants() -> Int64 = appReds(redsV)\n  \
         operation name() -> Int64 = appName(at41)\n  \
         operation two() -> Int64 = appTwo(pair)",
    );
    for (entry, want) in [
        ("list", 42),
        ("variant", 7),
        ("variants", 2),
        ("name", 42),
        ("two", 15),
    ] {
        assert_eq!(
            run(&src, &format!("test.m32c2.arrow.{entry}")),
            want,
            "{entry}"
        );
    }
}

/// A FUNCTION VALUE'S SLOT CHECKS, naming the sibling variant by its own constructor, as a
/// named operation's slot does.
///
/// BACKED OUT (5): still refused, but `expected red, got Colour` — the parent, not `blue`.
#[test]
fn a_call_of_an_arrow_typed_variable_refuses_a_sibling_variant_by_name() {
    let one = plain(
        "arrowone",
        "  sort Colour\n    entity red(v: Int64)\n    entity blue(v: Int64)\n  end\n  \
         operation appRed(f: (c: Colour.red) -> Int64) -> Int64 = f(blue(v: 1))",
    );
    assert_reports(
        &one,
        "f._1 (op-arg): expected red, got blue",
        "a sibling variant",
    );
    let many = plain(
        "arrowmany",
        "  sort Colour\n    entity red(v: Int64)\n    entity blue(v: Int64)\n  end\n  \
         operation appReds(f: (cs: List[T = Colour.red]) -> Int64) -> Int64 = f([red(v: 1), blue(v: 2)])",
    );
    assert_reports(
        &many,
        "list.element 2 (collection-element): expected red, got blue",
        "a sibling variant in a literal",
    );
}
