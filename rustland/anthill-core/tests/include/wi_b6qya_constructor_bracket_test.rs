//! WI-20261009-B6QYA — the bracket written on a constructor binds the parameters of its
//! sort, as the bracket on an operation binds the operation's and its sort's.
//!
//! THE RULE. A constructor's type arguments are its sort's. Over `sort Box[V]` with
//! `entity mk(v: V)`, the construction `Box.mk[V = Int64](5)` is the one
//! `Box[V = Int64].mk(5)` makes and `CA.mk(5)` over `sort CA = Box[V = Int64]`: the field
//! is checked at the binding and the value is a `Box[V = Int64]`. A key names a parameter
//! of the sort — one no field uses among them — and a positional takes the sort's next
//! parameter no key took, as in the constructor's type `Box.mk[Int64]`. What does not fit
//! is refused in the words an operation's bracket is refused in.
//!
//! BEFORE. The bracket on a constructor was a load error wherever it was written
//! ("call-site type arguments `Box.mk[…](…)` are not supported here"), so two of the
//! three spellings bound the sort's parameter for a constructor and one did not.
//!
//! WITH NO ARGUMENT LIST the bracket is refused, and the refusal advises the applied
//! spelling. BEFORE, `Box.mk[V = Int64]` loaded with the bracket read as the
//! constructor's fields: a keyed entry named no field and was dropped — `[Zork = Int64]`
//! loaded — and a positional one was the field's value, `Box.mk[Int64]` a box holding
//! the type.
//!
//! EVERY ROW HAS ITS OWN SOURCE, as in `wi_hzvqa_alias_receiver_test`.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the loader's read (the `ApplyOrConstructor` frame reading no bracket for an entity,
//!   so the end-of-file sweep refuses it) — FAIL:
//!     the_bracket_on_a_constructor_binds_its_sort_s_parameter
//!     the_three_spellings_give_one_verdict_at_one_site (its constructor bracket third)
//!     a_parameter_no_field_uses_is_bound
//!     a_positional_takes_the_sort_s_next_parameter
//!     a_key_the_sort_does_not_declare_is_refused
//!     a_bracket_on_a_literal_s_constructor_is_refused
//!     the_receiver_and_the_bracket_must_agree
//!     a_named_requirement_slot_is_bound_and_selects
//!     an_eponymous_sort_s_constructor_reads_its_bracket
//!     a_constant_s_initializer_reads_the_bracket
//!     the_bracket_leaves_the_arguments_typed_as_any_other
//!     the_advised_spelling_of_a_bracket_without_arguments_loads
//!     wi839_call_bracket_channel_test::a_bracket_on_an_entity_constructor_call_is_read
//!   the typer's read (`check_constructor_iter` without `seed_constructor_type_args`) —
//!   FAIL, each on the half that asserts what the binding does:
//!     the_bracket_on_a_constructor_binds_its_sort_s_parameter
//!     the_three_spellings_give_one_verdict_at_one_site
//!     a_parameter_no_field_uses_is_bound
//!     a_positional_takes_the_sort_s_next_parameter
//!     a_key_the_sort_does_not_declare_is_refused
//!     the_receiver_and_the_bracket_must_agree
//!     a_named_requirement_slot_is_bound_and_selects
//!     an_eponymous_sort_s_constructor_reads_its_bracket
//!     a_constant_s_initializer_reads_the_bracket
//!     the_advised_spelling_of_a_bracket_without_arguments_loads
//!     wi839_call_bracket_channel_test::a_bracket_on_an_entity_constructor_call_is_read
//!     (`the_bracket_leaves_the_arguments_typed_as_any_other` passes: it guards the
//!     node the loader builds, and binds nothing the fields do not say)
//!   a positional reaching none of the sort's parameters (`positional_limit: 0` in
//!   `seed_constructor_type_args`) — FAIL:
//!     a_positional_takes_the_sort_s_next_parameter
//!   the refusal of a bracket with no argument list (`refuse_bracketed_constructor` not
//!   called) — FAIL:
//!     a_bracket_with_no_argument_list_is_refused
//!     a_bracketed_constructor_in_a_bracket_is_its_type (its refused half)
//!   a bracketed constructor standing as a bracket's entry not classified a type value
//!   (the `bracket_entries` leg of `is_type_value` in the `ApplyOrConstructor` frame; the
//!   entry is then refused as a construction), a bare one not classified (`push_leaf_occ`),
//!   its arguments checked at the constructor and not at its sort by the typer (the
//!   `TypeValue` frame) or bound so by eval (`finish_sort_type`) — FAIL, each on its own:
//!     a_bracketed_constructor_in_a_bracket_is_its_type
//!   a literal's constructor not held to the reader (`check_constructor_iter` without its
//!   `literal` leg) — FAIL:
//!     a_bracket_on_a_literal_s_constructor_is_refused
//!   a positional on a named slot's parameter bound as a plain parameter
//!   (`resolve_call_type_arg_targets`' positional arm answering `Param`) — FAIL:
//!     a_named_requirement_slot_is_bound_and_selects (its positional refusals, the
//!     constructor's and the operation's)
//!
//!   PASS UNDER EVERY BACK-OUT, by design — the fence:
//!     a_constructor_in_a_clause_takes_no_bracket — a clause's term is matched, not built.
//!     the_three_spellings_give_one_verdict_at_one_site, its operation rows and its
//!       receiver and alias thirds — those spellings bound before.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The sorts and aliases the rows are about, indented for a namespace body.
const DECLS: &str = r#"
  sort Box[V]
    entity mk(v: V)
    entity hole
    operation wrap(x: V) -> Self = mk(x)
    operation unbox(b: Self) -> V = match b
      case mk(v) -> v
    operation count(b: Box) -> Int64 = 3
  end
  sort Pair[L, R]
    entity pair(l: L, r: R)
    entity left(l: L)
    operation fst(p: Self) -> L = match p
      case pair(l, r) -> l
      case left(l) -> l
    operation tag(p: Pair[L = Int64, R = String]) -> Int64 = 7
  end
  sort Colour
    entity rgb(r: Int64)
    operation red(c: Colour) -> Int64 = match c
      case rgb(r) -> r
  end
  sort CA = Box[V = Int64]
  sort CB = Box
"#;

fn source(ns: &str, body: &str) -> String {
    format!("namespace test.{ns}\n  import anthill.prelude.{{Type, Bool, Error}}\n{DECLS}\n{body}\nend\n")
}

/// `test.<ns>.go() -> <ret> = <expr>` beside the declarations.
fn go(ns: &str, ret: &str, expr: &str) -> String {
    source(ns, &format!("  operation go() -> {ret} = {expr}"))
}

/// Load `source`, call `test.<ns>.go()`, and hand back its value as text.
fn run_source(ns: &str, source: &str) -> String {
    let mut interp = interp_for(source);
    let value = interp
        .call(&format!("test.{ns}.go"), &[])
        .unwrap_or_else(|e| panic!("{ns}: {e:?}"));
    match value {
        Value::Int(n) => n.to_string(),
        Value::Str(s) => s.to_string(),
        other => panic!("{ns}: expected an Int64 or a String, got {other:?}"),
    }
}

/// The value of `go() -> <ret> = <expr>`.
fn run(ns: &str, ret: &str, expr: &str) -> String {
    run_source(ns, &go(ns, ret, expr))
}

/// The refusals of a source that must not load, rendered.
fn refusal_of(ns: &str, source: &str) -> String {
    let errs = try_load_kb_with(source)
        .err()
        .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
    format!("{errs:?}")
}

/// The refusals of `go() -> <ret> = <expr>`.
fn refusal(ns: &str, ret: &str, expr: &str) -> String {
    refusal_of(ns, &go(ns, ret, expr))
}

// ── the rule ────────────────────────────────────────────────────────────────

/// The ticket's program: the field is checked at the binding and the value is the sort at
/// it — with the sort named, and with the constructor named alone.
#[test]
fn the_bracket_on_a_constructor_binds_its_sort_s_parameter() {
    for (tag, mk) in [("dotted", "Box.mk"), ("bare", "mk")] {
        let ns = format!("b6ok{tag}");
        assert_eq!(run(&ns, "Int64", &format!("Box.unbox({mk}[V = Int64](5))")), "5", "{ns}");

        let ns = format!("b6field{tag}");
        let rendered = refusal(&ns, "Int64", &format!("Box.count({mk}[V = Int64](\"s\"))"));
        assert!(
            rendered.contains("mk.v (entity-field): expected Int64, got String"),
            "{ns}: {rendered}"
        );

        // The value is the sort at the binding, with a field or without one.
        for (kind, args) in [("mk", "mk[V = Int64](5)"), ("hole", "hole[V = Int64]()")] {
            let ns = format!("b6at{kind}{tag}");
            let ctor = if tag == "dotted" { format!("Box.{args}") } else { args.to_string() };
            let body = format!("  operation go() -> Int64 =\n    let c: Box[V = String] = {ctor}\n    1");
            let rendered = refusal_of(&ns, &source(&ns, &body));
            assert!(
                rendered.contains(
                    "c.annotation (let-binding): expected Box[V = String], got Box[V = Int64]"
                ),
                "{ns}: {rendered}"
            );
        }
    }
    // With no bracket the parameter is the field's, as it was.
    assert_eq!(run("b6plain", "String", "Box.unbox(Box.mk(\"s\"))"), "s");
}

/// The callee's bracket, the receiver's bracket and an alias are three spellings of one
/// binding, for an operation and for a constructor: each takes the argument the binding
/// admits and refuses the other one at the same site.
#[test]
fn the_three_spellings_give_one_verdict_at_one_site() {
    for (member, site) in [
        ("mk", "mk.v (entity-field): expected Int64, got String"),
        ("wrap", "wrap.x (op-arg): expected Int64, got String"),
    ] {
        for (tag, good, bad) in [
            ("callee", format!("Box.{member}[V = Int64](5)"), format!("Box.{member}[V = Int64](\"s\")")),
            ("recv", format!("Box[V = Int64].{member}(5)"), format!("Box[V = Int64].{member}(\"s\")")),
            ("alias", format!("CA.{member}(5)"), format!("CA.{member}(\"s\")")),
        ] {
            let ns = format!("b6three{member}{tag}");
            assert_eq!(run(&ns, "Int64", &format!("Box.unbox({good})")), "5", "{ns}");
            let ns = format!("b6threebad{member}{tag}");
            let rendered = refusal(&ns, "Int64", &format!("Box.count({bad})"));
            assert!(rendered.contains(site), "{ns}: {rendered}");
        }
    }
}

/// Every parameter of the sort may be named, one no field of the constructor uses among
/// them: `left(l: L)` says nothing of `R`, and the bracket does.
#[test]
fn a_parameter_no_field_uses_is_bound() {
    assert_eq!(run("b6unused", "Int64", "Pair.tag(Pair.left[R = String](5))"), "7");
    let rendered = refusal("b6unusedbad", "Int64", "Pair.tag(Pair.left[R = Int64](5))");
    assert!(
        rendered.contains(
            "tag.p (op-arg): expected Pair[L = Int64, R = String], got Pair[L = Int64, R = Int64]"
        ),
        "{rendered}"
    );
    // The receiver's spelling of the same pair of programs.
    assert_eq!(run("b6unusedrecv", "Int64", "Pair.tag(Pair[R = String].left(5))"), "7");
}

/// A positional takes the sort's next parameter no key took, in the order the sort
/// declares them — the reading the constructor's type `Box.mk[Int64]` has — and one past
/// the sort's parameters is refused.
#[test]
fn a_positional_takes_the_sort_s_next_parameter() {
    assert_eq!(run("b6pos", "Int64", "Box.unbox(Box.mk[Int64](5))"), "5");
    let rendered = refusal("b6posbad", "Int64", "Box.count(Box.mk[Int64](\"s\"))");
    assert!(
        rendered.contains("mk.v (entity-field): expected Int64, got String"),
        "{rendered}"
    );
    assert_eq!(run("b6postwo", "Int64", "Pair.tag(Pair.pair[Int64, String](1, \"s\"))"), "7");
    // `R` is taken by its key, so the positional is `L`.
    assert_eq!(run("b6posmixed", "Int64", "Pair.tag(Pair.pair[R = String, Int64](1, \"s\"))"), "7");
    let rendered = refusal("b6posmixedbad", "Int64", "Pair.tag(Pair.pair[R = String, Int64](\"x\", \"s\"))");
    assert!(
        rendered.contains("pair.l (entity-field): expected Int64, got String"),
        "{rendered}"
    );
    for (ns, expr, limit) in [
        ("b6posover", "Box.count(Box.mk[Int64, String](5))", "at most 1 positional type argument(s), got 2"),
        ("b6posnone", "Colour.red(Colour.rgb[Int64](5))", "at most 0 positional type argument(s), got 1"),
    ] {
        let rendered = refusal(ns, "Int64", expr);
        assert!(rendered.contains(limit), "{ns}: {rendered}");
    }
}

/// A key names a parameter of the sort. One the sort does not declare — a field's name,
/// a spec's short name among them — is refused, and so is one written twice.
#[test]
fn a_key_the_sort_does_not_declare_is_refused() {
    for (ns, expr, why) in [
        ("b6zork", "Box.count(Box.mk[Zork = Int64](5))", "unknown type-param 'Zork'"),
        ("b6fieldkey", "Box.count(Box.mk[v = Int64](5))", "unknown type-param 'v'"),
        ("b6twice", "Box.count(Box.mk[V = Int64, V = Int64](5))", "type-param 'V' bound twice"),
        ("b6noparams", "Colour.red(Colour.rgb[V = Int64](5))", "unknown type-param 'V'"),
    ] {
        let rendered = refusal(ns, "Int64", expr);
        assert!(rendered.contains(why), "{ns}: {rendered}");
    }
    // A free-standing entity declares no parameter.
    let ns = "b6free";
    let body = "  entity Free(x: Int64)\n  operation go() -> Free = Free[Zork = Int64](x: 1)";
    let rendered = refusal_of(ns, &source(ns, body));
    assert!(rendered.contains("unknown type-param 'Zork'"), "{rendered}");
}

/// A literal's constructor named directly belongs to no sort that declares a parameter,
/// and a bracket on it is refused entry by entry; without one it is the literal.
#[test]
fn a_bracket_on_a_literal_s_constructor_is_refused() {
    let literal = |ns: &str, ret: &str, expr: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{List}}\n\
             \x20 import anthill.reflect.{{ListLiteral, TupleLiteral, SetLiteral}}\n\
             \x20 operation lit() -> {ret} = {expr}\n\
             \x20 operation go() -> Int64 = 1\n\
             end\n"
        )
    };
    for (ns, ret, expr, why) in [
        ("b6litkey", "List[T = Int64]", "ListLiteral[Zork = Int64](1, 2)", "unknown type-param 'Zork'"),
        ("b6litpos", "(Int64, Int64)", "TupleLiteral[Int64](1, 2)", "at most 0 positional type argument(s), got 1"),
    ] {
        let rendered = refusal_of(ns, &literal(ns, ret, expr));
        assert!(rendered.contains(why), "{ns}: {rendered}");
    }
    let ns = "b6litplain";
    assert_eq!(run_source(ns, &literal(ns, "List[T = Int64]", "ListLiteral(1, 2)")), "1");
}

/// Where a receiver — written, or an alias — and the constructor's bracket bind one
/// parameter, they must agree, and each binds what the other leaves.
#[test]
fn the_receiver_and_the_bracket_must_agree() {
    for (ns, expr) in [
        ("b6bothsame", "Box.unbox(Box[V = Int64].mk[V = Int64](5))"),
        ("b6aliassame", "Box.unbox(CA.mk[V = Int64](5))"),
        ("b6aliasbare", "Box.unbox(CB.mk[V = Int64](5))"),
    ] {
        assert_eq!(run(ns, "Int64", expr), "5", "{ns}");
    }
    assert_eq!(
        run("b6botheach", "Int64", "Pair.tag(Pair[L = Int64].pair[R = String](1, \"s\"))"),
        "7"
    );
    for (ns, expr) in [
        ("b6bothdiffer", "Box.count(Box[V = Int64].mk[V = String](5))"),
        ("b6aliasdiffer", "Box.count(CA.mk[V = String](\"s\"))"),
    ] {
        let rendered = refusal(ns, "Int64", expr);
        assert!(
            rendered.contains("expected the receiver's V = Int64, got the callee bracket's V = String"),
            "{ns}: {rendered}"
        );
    }
}

/// A requirement slot the sort names is a parameter, and binding it on a constructor
/// selects the provider as binding it on the receiver does: by length `"aa"` and `"bb"`
/// are one element. A sort that may not be selected is refused in both spellings alike,
/// and an anonymous requirement's spec name is no key of a constructor.
#[test]
fn a_named_requirement_slot_is_bound_and_selects() {
    let slots = |ns: &str, body: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{Int64, String, WeakOrd, SortedSet, Type}}\n\
             \x20 import anthill.prelude.String.{{length}}\n\
             \x20 import anthill.prelude.Numeric.{{sub}}\n\
             \x20 sort ByLength\n\
             \x20   provides WeakOrd[T = String]\n\
             \x20   operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))\n\
             \x20 end\n\
             \x20 sort ConcOrd\n\
             \x20   entity conc\n\
             \x20   provides WeakOrd[T = String]\n\
             \x20   operation compare(a: String, b: String) -> Int64 = 0\n\
             \x20 end\n\
             {body}\n\
             end\n"
        )
    };
    let sized = |tip: &str, second: &str| {
        format!(
            "  operation go() -> Int64 =\n    SortedSet.size(SortedSet.insert(SortedSet.insert({tip}, \"aa\"), \"{second}\"))"
        )
    };
    for (tag, tip) in [
        ("callee", "SortedSet.tip[T = String, O = ByLength]()"),
        ("calleepos", "SortedSet.tip[String, ByLength]()"),
        ("recv", "SortedSet[T = String, O = ByLength].tip()"),
    ] {
        for (second, want) in [("bb", "1"), ("b", "2")] {
            let ns = format!("b6slot{tag}{second}");
            assert_eq!(run_source(&ns, &slots(&ns, &sized(tip, second))), want, "{ns}");
        }
    }
    for (ns, tip) in [
        ("b6slotconccallee", "SortedSet.tip[T = String, O = ConcOrd]()"),
        ("b6slotconccalleepos", "SortedSet.tip[String, ConcOrd]()"),
        ("b6slotconcrecv", "SortedSet[T = String, O = ConcOrd].tip()"),
        ("b6slotconcrecvpos", "SortedSet[String, ConcOrd].tip()"),
    ] {
        let body = format!("  operation go() -> Int64 = SortedSet.size({tip})");
        let rendered = refusal_of(ns, &slots(ns, &body));
        assert!(rendered.contains("SortedSet.tip.selection"), "{ns}: {rendered}");
    }
    let ns = "b6slotanon";
    let body = "  operation go() -> Int64 = SortedSet.size(SortedSet.tip[T = String, WeakOrd = ByLength]())";
    let rendered = refusal_of(ns, &slots(ns, body));
    assert!(rendered.contains("unknown type-param 'WeakOrd'"), "{rendered}");

    // The same of an operation's own slot: a positional that reaches the parameter a
    // requirement names writes a witness as the key does. By length `"aa"` is after `"b"`.
    let pick = "  operation pick[T, O](a: T, b: T) -> Int64 requires O: WeakOrd[T] = WeakOrd.compare(a, b)\n";
    for (tag, bracket) in [("key", "[T = String, O = ByLength]"), ("pos", "[String, ByLength]")] {
        let ns = format!("b6slotop{tag}");
        let body = format!("{pick}  operation go() -> Int64 = pick{bracket}(\"aa\", \"b\")");
        assert_eq!(run_source(&ns, &slots(&ns, &body)), "1", "{ns}");
    }
    for (tag, bracket) in [("key", "[T = String, O = ConcOrd]"), ("pos", "[String, ConcOrd]")] {
        let ns = format!("b6slotopconc{tag}");
        let body = format!("{pick}  operation go() -> Int64 = pick{bracket}(\"aa\", \"b\")");
        let rendered = refusal_of(&ns, &slots(&ns, &body));
        assert!(rendered.contains("pick.selection"), "{ns}: {rendered}");
    }
}

/// A sort and its constructor of one name: applied to arguments it is the construction,
/// and its bracket binds; with a bracket alone it is the type, as it was.
#[test]
fn an_eponymous_sort_s_constructor_reads_its_bracket() {
    let wrap = |ns: &str, body: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{Type}}\n\
             \x20 sort Wrap[T]\n\
             \x20   entity Wrap(x: T)\n\
             \x20   operation open(w: Self) -> T = w.x\n\
             \x20 end\n\
             {body}\n\
             end\n"
        )
    };
    let ns = "b6epon";
    let body = "  operation go() -> Int64 = Wrap.open(Wrap[T = Int64](5))";
    assert_eq!(run_source(ns, &wrap(ns, body)), "5");
    let ns = "b6eponbad";
    let body = "  operation go() -> Int64 = Wrap.open(Wrap[T = Int64](\"s\"))";
    let rendered = refusal_of(ns, &wrap(ns, body));
    assert!(
        rendered.contains("Wrap.x (entity-field): expected Int64, got String"),
        "{rendered}"
    );
    let ns = "b6epontype";
    let body = "  operation ty() -> Type = Wrap[T = Int64]\n  operation go() -> Int64 = 1";
    assert_eq!(run_source(ns, &wrap(ns, body)), "1");
}

/// A constant's initializer is a value definition, and a construction in it reads its
/// bracket as one in an operation body does.
#[test]
fn a_constant_s_initializer_reads_the_bracket() {
    let ns = "b6const";
    let body = "  const five: Box[V = Int64] = Box.mk[V = Int64](5)\n  operation go() -> Int64 = Box.unbox(five)";
    assert_eq!(run_source(ns, &source(ns, body)), "5");
    // Refused at the field, where the bracket is read, and not at the constant's type.
    let ns = "b6constbad";
    let body = "  const five: Box[V = String] = Box.mk[V = String](5)\n  operation go() -> Int64 = 1";
    let rendered = refusal_of(ns, &source(ns, body));
    assert!(
        rendered.contains("mk.v (entity-field): expected String, got Int64"),
        "{rendered}"
    );
}

/// A constructor's arguments are typed from its declared fields — an arrow-typed field
/// lets a bare operation name stand for the function, a ground field type fixes a call's
/// own parameter — and they are with a bracket as without one.
#[test]
fn the_bracket_leaves_the_arguments_typed_as_any_other() {
    let hints = |ns: &str, expr: &str| {
        format!(
            "namespace test.{ns}\n\
             \x20 import anthill.prelude.{{List, Type}}\n\
             \x20 import anthill.prelude.List.{{nil}}\n\
             \x20 import anthill.prelude.Numeric.{{add}}\n\
             \x20 sort Fb[V]\n\
             \x20   entity fb(f: (x: V) -> V)\n\
             \x20   operation run(b: Self, x: V) -> V = match b\n\
             \x20     case fb(f) -> f(x)\n\
             \x20 end\n\
             \x20 sort Holder[V]\n\
             \x20   entity hold(c: List[T = Int64], v: V)\n\
             \x20   operation size(h: Holder) -> Int64 = 4\n\
             \x20 end\n\
             \x20 operation inc(x: Int64) -> Int64 = add(x, 1)\n\
             \x20 operation poly[A]() -> List[T = A] = nil\n\
             \x20 operation go() -> Int64 = {expr}\n\
             end\n"
        )
    };
    let ns = "b6arrow";
    assert_eq!(run_source(ns, &hints(ns, "Fb.run(Fb.fb[V = Int64](inc), 1)")), "2");
    let ns = "b6call";
    assert_eq!(run_source(ns, &hints(ns, "Holder.size(Holder.hold[V = Int64](poly(), 1))")), "4");
}

// ── a bracket with no argument list ─────────────────────────────────────────

/// A constructor written with a bracket and no argument list is refused in a value
/// position, whatever the bracket says. Before, each of these loaded: the keyed entries
/// dropped, the positional one read as the field.
#[test]
fn a_bracket_with_no_argument_list_is_refused() {
    for (ns, ret, expr, written) in [
        ("b6barekey", "Int64", "Box.count(Box.mk[V = Int64])", "Box.mk"),
        ("b6barezork", "Int64", "Box.count(Box.mk[Zork = Int64])", "Box.mk"),
        ("b6barepos", "Int64", "Box.count(Box.mk[Int64])", "Box.mk"),
        ("b6barehole", "Int64", "Box.count(Box.hole[V = Int64])", "Box.hole"),
        ("b6barename", "Int64", "Box.count(hole[V = Int64])", "hole"),
        ("b6barealias", "Int64", "Box.count(CB.hole[V = Int64])", "CB.hole"),
    ] {
        let rendered = refusal(ns, ret, expr);
        assert!(
            rendered.contains(&format!(
                "the bracket on the constructor `{written}[…]` is written with no argument list"
            )) && rendered.contains(&format!("Write `{written}[…]()`")),
            "{ns}: {rendered}"
        );
    }
}

/// An entry of a bracket is a type argument, and a bracketed constructor standing there is
/// the constructor's type: `Box[V = Pair.left[R = String]]` is a type value, evaluated as
/// one, and equal to itself written twice. Its own arguments are its sort's and are held
/// to them. Standing alone, the same text is the refused construction.
#[test]
fn a_bracketed_constructor_in_a_bracket_is_its_type() {
    let kinds = "  operation kind(t: Type) -> Int64 = 6\n  operation same(t: Type, u: Type) -> Bool = anthill.prelude.PartialEq.eq(t, u)\n";
    for (ns, expr) in [
        ("b6entry", "kind(Box[V = Pair.left[R = String]])"),
        ("b6entrypos", "kind(Box[V = Pair.left[Int64, String]])"),
        ("b6entrynested", "kind(Box[V = Box[V = Pair.left[R = String]]])"),
        (
            "b6entrysame",
            "if same(Box[V = Pair.left[R = String]], Box[V = Pair.left[R = String]]) then 6 else 0",
        ),
        (
            "b6entrydiffer",
            "if same(Box[V = Pair.left[R = String]], Box[V = Pair.left[R = Int64]]) then 0 else 6",
        ),
    ] {
        let body = format!("{kinds}  operation go() -> Int64 = {expr}");
        assert_eq!(run_source(ns, &source(ns, &body)), "6", "{ns}");
    }
    // The same of a constructor named bare, and of a type value used as a receiver.
    let body = format!("{kinds}  operation go() -> Int64 = kind(Box[V = Pair.left])");
    assert_eq!(run_source("b6entrybare", &source("b6entrybare", &body)), "6");
    let ns = "b6entryrecv";
    let body = "  operation go() -> Int64 =\n    let t = Box[V = Pair.left[L = Int64, R = String]]\n    Box.count(t.mk(left(5)))";
    assert_eq!(run_source(ns, &source(ns, body)), "3");
    let ns = "b6entryrecvbad";
    let body = "  operation go() -> Int64 =\n    let t = Box[V = Pair.left[L = Int64, R = String]]\n    Box.count(t.mk(5))";
    let rendered = refusal_of(ns, &source(ns, body));
    assert!(
        rendered.contains("mk.v (entity-field): expected left[L = Int64, R = String], got Int64"),
        "{ns}: {rendered}"
    );
    for (ns, expr, why) in [
        ("b6entryzork", "kind(Box[V = Pair.left[Zork = String]])", "has no type parameter named 'Zork'"),
        ("b6entryover", "kind(Box[V = Pair.left[Int64, String, Bool]])", "is over-applied"),
    ] {
        let body = format!("{kinds}  operation go() -> Int64 = {expr}");
        let rendered = refusal_of(ns, &source(ns, &body));
        assert!(rendered.contains(why), "{ns}: {rendered}");
    }
    let rendered = refusal("b6entryalone", "Int64", "Pair.tag(Pair.left[R = String])");
    assert!(
        rendered.contains("the bracket on the constructor `Pair.left[…]` is written with no argument list"),
        "{rendered}"
    );
}

/// The spelling the refusal advises, written out: it loads, binds, and is refused where
/// the binding does not fit — with a field and without one, through an alias, and with a
/// parameter of the enclosing operation in the bracket.
#[test]
fn the_advised_spelling_of_a_bracket_without_arguments_loads() {
    for (ns, expr) in [
        ("b6advhole", "Box.count(Box.hole[V = Int64]())"),
        ("b6advname", "Box.count(hole[V = Int64]())"),
        ("b6advalias", "Box.count(CB.hole[V = Int64]())"),
        ("b6advfields", "Box.count(Box.mk[V = Int64](5))"),
    ] {
        assert_eq!(run(ns, "Int64", expr), "3", "{ns}");
    }
    let ns = "b6advparam";
    let body = "  operation empty[W](w: W) -> Box[V = W] = Box.hole[V = W]()\n  operation go() -> Int64 = Box.count(empty(1))";
    assert_eq!(run_source(ns, &source(ns, body)), "3");
    let ns = "b6advparambad";
    let body = "  operation empty[W](w: W) -> Box[V = W] = Box.hole[V = Int64]()\n  operation go() -> Int64 = 1";
    let rendered = refusal_of(ns, &source(ns, body));
    assert!(rendered.contains("got Box[V = Int64]"), "{rendered}");
}

// ── the fence ───────────────────────────────────────────────────────────────

/// In a clause's term positions a constructor is a term the clause matches, not a call,
/// and its bracket is not read: a rule body, standing alone or under an `if`, and a fact.
#[test]
fn a_constructor_in_a_clause_takes_no_bracket() {
    for (ns, clause) in [
        ("b6rule", "  rule r(?v) :- ?v <=> Box.mk[V = Int64](5)"),
        (
            "b6ruleif",
            "  rule r(?v) :- ?v <=> (if true then Box.mk[V = Int64](5) else Box.mk[V = Int64](6))",
        ),
        ("b6fact", "  rule held(?b) :- ?b <=> 1\n  fact held(Box.mk[V = Int64](5))"),
    ] {
        let body = format!("{clause}\n  operation go() -> Int64 = 1");
        let rendered = refusal_of(ns, &source(ns, &body));
        assert!(
            rendered.contains("call-site type arguments `Box.mk[…](…)` are not supported here"),
            "{ns}: {rendered}"
        );
    }
}

