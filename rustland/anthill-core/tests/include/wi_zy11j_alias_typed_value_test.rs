//! WI-20261009-ZY11J — a type alias written bare in a type position is the type it stands
//! for.
//!
//! THE RULE. Over `sort CA = Box[V = Int64]`, `b: CA` is `b: Box[V = Int64]`; over `sort
//! CB = Box`, `b: CB` is `b: Box`, its slots left open as the written name leaves them;
//! over `sort PA = Pair[L = Int64]`, `p: PA` is `p: Pair[L = Int64]`. It holds wherever a
//! type is written — a parameter, a result, a field, an annotation, a type argument, a
//! row inside one — and not among the elements of an operation's own `effects` clause,
//! where the effect rules follow an alias themselves and name it as written
//! (`TypeSite`). A clause binding's value is such a place too: `requires Show[T = SI]`
//! and `provides Tag[T = CA]` are about the type, in a sort's clause and in an
//! operation's (`Loader::clause_alias_type`); a parameter of the declaring sort that the
//! alias names is that parameter, in the form a clause holds one.
//!
//! BEFORE. The alias applied to further arguments was read through (`IntPair[R =
//! String]`), and the alias written bare was left as its own name, which is no sort:
//!
//!   - the sort's own operations refused the value — `Box.unbox(b)` with `b: CA` was
//!     "Box.unbox.dispatch: … no impl provides Box", the callee's sort read as a spec the
//!     carrier `CA` must provide;
//!   - so did a spec's, at a carrier typed by an alias — "`BI` provides no `Feed`";
//!   - a slot the alias leaves open was open to anything: `via(b: CB) -> Int64 = b.v`
//!     loaded, and `via(Box.mk("s"))` returned the string. The written `b: Box` is
//!     refused, "expected Int64, got b.V";
//!   - an arrow's row naming a bound alias (`@ {E}` over `effects E = Boom`) did not admit
//!     the label the alias stands for;
//!   - a requirement written at an alias could not be supplied, and of two provisions of
//!     one type, one written through the alias, a call ran one in silence.
//!
//! EVERY ROW HAS ITS OWN SOURCE, as in `wi_hzvqa_alias_receiver_test`, and stands beside
//! the same program with the type written out.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the reading (`Loader::bare_alias_type` answering `None`, in a type position and in a
//!   clause alike) — FAIL: every test here but the two named below, and
//!     wi_snjpr_alias_in_a_name_test::a_field_of_a_slot_the_alias_leaves_open_is_that_slot
//!     wi_80zv8_bare_own_sort_test::a_partial_reference_and_an_alias_leave_the_rest_to_a_wildcard
//!     wi_0rp29_call_binding_test::an_option_alias_is_not_wrapped_control
//!     wi_728rw_dotted_spec_member_test::fixed_nested_alias_member_remains_the_fixed_type
//!   the last three by the type their refusal prints, which was the alias's name.
//!   the reading in a type position alone (`Loader::bare_alias_read` handing the name's
//!   child on) — FAIL: the same, less the two clause tests,
//!   `a_requirement_written_at_an_alias_is_asked_at_its_type` and
//!   `a_provision_written_at_an_alias_is_a_provision_at_its_type`.
//!   the reading of a name reached as a child of a sort (the dotted branch of the
//!   `Simple` arm handing its child on unread) — FAIL:
//!     an_alias_reached_by_a_path_is_read_as_the_bare_name_is
//!     wi_728rw_dotted_spec_member_test::fixed_nested_alias_member_remains_the_fixed_type
//!   an operation's own row read as a type (`Loader::own_row_element_to_value` at
//!   `TypeSite::Type`) — FAIL:
//!     an_operations_own_row_names_its_alias_as_written
//!     wi_rsrp5_effect_label_routes_test::a_bound_row_alias_is_followed_by_the_modify_gate_as_it_already_was_by_registration
//!   the label under a `-`, and the label under a guard, read as a type whatever row the
//!   atom stands in (each arm handing on `TypeSite::Type`) — FAIL, each on its own:
//!     an_operations_own_row_names_its_alias_as_written
//!   a clause binding's value read as written — in a sort's clause
//!   (`sort_binding_to_value`'s `Simple` arm not asking `clause_alias_type`) — FAIL:
//!     a_requirement_written_at_an_alias_is_asked_at_its_type
//!     a_provision_written_at_an_alias_is_a_provision_at_its_type
//!   — and in an operation's `requires` (`bare_contract_spec` under the bracket) — FAIL:
//!     a_requirement_written_at_an_alias_is_asked_at_its_type
//!   a bare link recorded read through (`record_alias_target` without its `Simple` arm)
//!   — FAIL:
//!     a_spec_named_through_a_chain_is_refused_where_a_link_owns_members
//!     wi_fs8m3_provides_at_alias_address_test::a_provision_at_an_alias_of_an_alias_names_the_sort
//!
//!   a parameter-naming alias read through wherever it is written
//!   (`Loader::within_declaring_scope_of` answering `true`) — FAIL:
//!     an_alias_that_names_a_parameter_is_read_only_inside_its_sort
//!
//!   PASS WITH THE READING BACKED OUT, by design:
//!     an_operations_own_row_names_its_alias_as_written — THE FENCE: it fails with either
//!       site of the exception backed out;
//!     a_spec_named_through_a_chain_is_refused_where_a_link_owns_members — the record's
//!       own guard, which the reading does not touch;
//!     the `written` half of every row — the type written out names no alias;
//!     wi_snjpr_alias_in_a_name_test::a_value_typed_by_an_alias_has_its_fields — a field
//!       read already went through the alias in the typer.
//!
//!   The same reading with the exception at EVERY effect row — an arrow's, and a row
//!   written as a type argument — was measured too: the whole workspace passed, and
//!   `an_alias_in_an_arrows_row_is_the_label_it_stands_for` is what it costs. The rules
//!   that follow an alias read an operation's own row only (kernel-language.md §5.5).
//!
//!   an alias whose type holds a variable left as written in a clause binding
//!   (`clause_alias_type` reading a ground type alone) — FAIL:
//!     a_clause_binding_naming_its_sorts_parameter_through_an_alias_is_about_that_parameter
//!     a_clause_binding_at_an_alias_with_an_open_slot_is_asked_at_its_type
//!   an alias taken to name a parameter whenever its type holds a variable
//!   (`bare_alias_type` asking whether the type is ground) — FAIL:
//!     an_alias_with_an_open_slot_is_its_type_in_another_namespace
//!   an alias's recorded types handed to every use as they are (`open_slots_anew` doing
//!   nothing) — FAIL:
//!     an_open_slot_of_an_alias_is_open_anew_at_each_use
//!   — and at an application of the alias alone (`type_alias_application` not calling
//!   it) — FAIL: the same row, at its applied half.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The sorts and aliases the rows are about, indented for a namespace body.
const DECLS: &str = r#"
  sort Box[V]
    entity mk(v: V)
    operation unbox(b: Self) -> V = b.v
    operation same(b: Self) -> Self = b
    operation unboxV(b: Box[V = V]) -> V = b.v
    operation count(b: Box) -> Int64 = 1
  end
  sort CA = Box[V = Int64]
  sort CB = Box
  sort CS = Box[V = String]
  sort CC = CA
  sort Pair[L, R]
    entity pair(l: L, r: R)
    operation snd(p: Self) -> R = p.r
  end
  sort PA = Pair[L = Int64]

  sort Feed[T]
    operation next(f: Self) -> T
    operation twice(f: Self) -> T = next(f)
  end
  sort Holder[C, Element]
    operation peek(c: C) -> Element
    operation peek2(c: C) -> Element = peek(c)
  end
  sort Bx[A]
    entity bx(a: A)
    provides Feed[T = A]
    provides Holder[C = Bx[A], Element = A]
    operation next(f: Bx[A]) -> A = f.a
    operation peek(c: Bx[A]) -> A = c.a
  end
  sort BI = Bx[A = Int64]
  sort BB = Bx
"#;

fn source(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Type, Bool, Int64, String, List, Iterable, Effect, Modify}}\n  import anthill.prelude.PartialEq.{{eq}}\n{DECLS}\n{body}\nend\n"
    )
}

/// Load, call `test.<ns>.go()`, and hand back its value as [`shown`].
fn run(ns: &str, body: &str) -> String {
    let mut interp = interp_for(&source(ns, body));
    let value = interp
        .call(&format!("test.{ns}.go"), &[])
        .unwrap_or_else(|e| panic!("{ns}: {e:?}"));
    shown(value)
}

/// A value as the text the rows compare: an integer's digits, a string's contents.
fn shown(value: Value) -> String {
    match value {
        Value::Int(n) => n.to_string(),
        Value::Str(s) => s.to_string(),
        other => panic!("expected an Int64 or a String, got {other:?}"),
    }
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, body: &str) -> String {
    let errs = try_load_kb_with(&source(ns, body))
        .err()
        .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
    format!("{errs:?}")
}

/// `go() -> Int64` over `b`, a `let` annotated `ty` and bound to `init`.
fn bound(ty: &str, init: &str, call: &str) -> String {
    format!("  operation go() -> Int64 =\n    let b: {ty} = {init}\n    {call}")
}

/// `go() -> Int64` handing `arg` to `via`, declared by `decl`.
fn through(decl: &str, arg: &str) -> String {
    format!("  operation {decl}\n  operation go() -> Int64 = via({arg})")
}

// ── the sort's own operations ───────────────────────────────────────────────

/// The ticket's five programs, each beside the same program with the type written out.
#[test]
fn a_sorts_own_operations_take_a_value_typed_by_its_alias() {
    for (name, call) in [
        ("unbox", "Box.unbox(b)"),
        ("dot", "b.unbox()"),
        ("same", "Box.same(b).v"),
        ("unboxv", "Box.unboxV(b)"),
    ] {
        for (spelling, ty) in [("alias", "CA"), ("chain", "CC"), ("written", "Box[V = Int64]")] {
            let ns = format!("zy11j{name}{spelling}");
            assert_eq!(run(&ns, &bound(ty, "Box.mk(5)", call)), "5", "{ns}");
        }
    }
    for (spelling, ty) in [("alias", "CA"), ("written", "Box[V = Int64]")] {
        let ns = format!("zy11jparam{spelling}");
        let decl = format!("via(b: {ty}) -> Int64 = Box.unbox(b)");
        assert_eq!(run(&ns, &through(&decl, "Box.mk(5)")), "5", "{ns}");
    }
}

/// An alias at another instance is refused where the value is used, as the written type
/// is: the box holds a `String` and an `Int64` is asked.
#[test]
fn an_alias_at_another_instance_is_refused_at_the_use() {
    for (spelling, ty) in [("alias", "CS"), ("written", "Box[V = String]")] {
        let rendered = refusal(
            &format!("zy11jother{spelling}"),
            &bound(ty, "Box.mk(\"s\")", "Box.unbox(b)"),
        );
        assert!(
            rendered.contains("go.return (op-return): expected Int64, got String"),
            "{spelling}: {rendered}"
        );
    }
}

// ── a slot the alias leaves open ────────────────────────────────────────────

/// `sort CB = Box` fixes nothing and `sort PA = Pair[L = Int64]` leaves `R`: a parameter
/// typed by either has that slot open, as the written sort has, so a body may not take it
/// for an `Int64`. Before, each alias row loaded and `go` returned the string.
#[test]
fn a_slot_an_alias_leaves_open_is_open_as_the_written_sort_leaves_it() {
    for (name, decl_of, arg, slot) in [
        (
            "field",
            (|ty: &str| format!("via(b: {ty}) -> Int64 = b.v")) as fn(&str) -> String,
            "Box.mk(\"s\")",
            "b.V",
        ),
        ("own", |ty| format!("via(b: {ty}) -> Int64 = Box.unbox(b)"), "Box.mk(\"s\")", "b.V"),
    ] {
        for (spelling, ty) in [("alias", "CB"), ("written", "Box")] {
            let ns = format!("zy11jopen{name}{spelling}");
            let rendered = refusal(&ns, &through(&decl_of(ty), arg));
            assert!(
                rendered.contains(&format!("via.return (op-return): expected Int64, got {slot}")),
                "{ns}: {rendered}"
            );
        }
    }
    for (name, body) in [("field", "p.r"), ("own", "Pair.snd(p)")] {
        for (spelling, ty) in [("alias", "PA"), ("written", "Pair[L = Int64]")] {
            let ns = format!("zy11jpartial{name}{spelling}");
            let decl = format!("via(p: {ty}) -> Int64 = {body}");
            let rendered = refusal(&ns, &through(&decl, "pair(l: 1, r: \"s\")"));
            assert!(
                rendered.contains("via.return (op-return): expected Int64, got p.R"),
                "{ns}: {rendered}"
            );
        }
    }
    // A spec's operation at such a carrier, the same.
    for (spelling, ty) in [("alias", "BB"), ("written", "Bx")] {
        let ns = format!("zy11jopenspec{spelling}");
        let decl = format!("via(b: {ty}) -> Int64 = Feed.twice(b)");
        let rendered = refusal(&ns, &through(&decl, "Bx.bx(\"s\")"));
        assert!(
            rendered.contains("via.return (op-return): expected Int64, got b.A"),
            "{ns}: {rendered}"
        );
    }
}

/// What does not read the open slot is taken: `count(b: Box)` takes any box, and the
/// slot is the result's where the result is declared so.
#[test]
fn an_open_slot_is_usable_as_the_written_sorts_is() {
    for (spelling, ty) in [("alias", "CB"), ("written", "Box")] {
        let ns = format!("zy11jcount{spelling}");
        let decl = format!("via(b: {ty}) -> Int64 = Box.count(b)");
        assert_eq!(run(&ns, &through(&decl, "Box.mk(\"s\")")), "1", "{ns}");
        let ns = format!("zy11jslot{spelling}");
        let body = format!(
            "  operation via(b: {ty}) -> b.V = Box.unbox(b)\n  operation go() -> Int64 = via(Box.mk(5))"
        );
        assert_eq!(run(&ns, &body), "5", "{ns}");
    }
}

// ── a spec's operations ─────────────────────────────────────────────────────

/// A carrier typed by an alias is the carrier: a spec's operation received on the spec
/// (`Feed.next(f: Self)`) or on its carrier parameter (`Holder.peek(c: C)`), body-less
/// or defaulted, written or through the dot. Before, each alias row was refused —
/// "`BI` provides no `Feed`", or at `<op>.dispatch`.
#[test]
fn a_specs_operations_take_a_carrier_typed_by_an_alias() {
    for (name, call) in [
        ("next", "Feed.next(b)"),
        ("nextdot", "b.next()"),
        ("twice", "Feed.twice(b)"),
        ("peek", "Holder.peek(b)"),
        ("peekdot", "b.peek()"),
        ("peek2", "Holder.peek2(b)"),
    ] {
        for (spelling, ty) in [("alias", "BI"), ("written", "Bx[A = Int64]")] {
            let ns = format!("zy11j{name}{spelling}");
            assert_eq!(run(&ns, &bound(ty, "Bx.bx(5)", call)), "5", "{ns}");
        }
    }
}

/// A requirement over an operation's own parameter, or over its sort's, is asked at the
/// sort the alias stands for. Before: "requirement `Conv[A = MI, …]` cannot be supplied".
#[test]
fn a_requirement_is_asked_at_what_the_alias_stands_for() {
    let decls = "  sort Conv[A, B]\n    operation conv(a: A) -> B\n  end\n  \
                 sort Mx[U]\n    entity mx(u: U)\n    provides Conv[A = Mx[U], B = Int64]\n    \
                 operation conv(a: Mx[U]) -> Int64 = 9\n  end\n  sort MI = Mx[U = Int64]\n  \
                 operation convert[P, Q](x: P) -> Q requires Conv[A = P, B = Q] = Conv.conv(x)\n  \
                 sort Tab[K, V]\n    requires Conv[A = K, B = V]\n    \
                 operation get(k: K) -> V = Conv.conv(k)\n  end\n";
    for (name, call) in [("op", "convert(b)"), ("sort", "Tab.get(b)")] {
        for (spelling, ty) in [("alias", "MI"), ("written", "Mx[U = Int64]")] {
            let ns = format!("zy11jreq{name}{spelling}");
            let body = format!("{decls}{}", bound(ty, "Mx.mx(1)", call));
            assert_eq!(run(&ns, &body), "9", "{ns}");
        }
    }
}

// ── wherever a type is written ──────────────────────────────────────────────

/// A result, a field and a type argument typed by an alias, each handed to a spec's
/// operation; and an alias of a type that names another alias inside it.
#[test]
fn an_alias_is_read_through_wherever_a_type_is_written() {
    for (name, body) in [
        (
            "result",
            "  operation mk() -> BI = Bx.bx(5)\n  operation go() -> Int64 = Holder.peek2(mk())"
                .to_string(),
        ),
        (
            "field",
            "  sort Hold\n    entity hold(h: BI)\n  end\n  \
             operation go() -> Int64 =\n    let x = hold(h: Bx.bx(5))\n    Holder.peek2(x.h)"
                .to_string(),
        ),
        (
            "fielddot",
            "  sort Hold\n    entity hold(h: BI)\n  end\n  \
             operation go() -> Int64 =\n    let x = hold(h: Bx.bx(5))\n    x.h.next()"
                .to_string(),
        ),
        (
            "argument",
            "  operation peekOf[E](l: List[T = E], x: E) -> Int64 requires Holder[C = E, Element = Int64] = Holder.peek(x)\n  \
             operation go() -> Int64 =\n    let l: List[T = BI] = [Bx.bx(4)]\n    peekOf(l, Bx.bx(5))"
                .to_string(),
        ),
    ] {
        let ns = format!("zy11jwhere{name}");
        assert_eq!(run(&ns, &body), "5", "{ns}");
    }
    // An alias whose own type names an alias: `List[T = BI]`.
    let nested = "  sort LB = List[T = BI]\n  operation go() -> Int64 =\n    \
                  let l: LB = [Bx.bx(5), Bx.bx(6)]\n    l.length()";
    assert_eq!(run("zy11jnested", nested), "2");
}

/// A library sort's operations, and a callback's parameter read off the receiver: `r` is
/// a `Row` because `b` is a `List[T = Row]`. Before: "List.length.dispatch: … no impl
/// provides List", and `r.flag` on an unresolved receiver.
#[test]
fn a_library_sorts_operations_take_a_value_typed_by_an_alias() {
    let decls = "  sort Row\n    entity row(flag: Bool, n: Int64)\n  end\n  \
                 sort IL = List[T = Int64]\n  sort RL = List[T = Row]\n";
    for (name, ty, init, call, answer) in [
        ("length", "IL", "[1, 2, 3]", "List.length(b)", "3"),
        ("lengthdot", "IL", "[1, 2, 3]", "b.length()", "3"),
        (
            "exists",
            "RL",
            "[row(flag: true, n: 4)]",
            "if Iterable.exists(b, lambda r -> r.flag) then 1 else 0",
            "1",
        ),
        (
            "existsdot",
            "RL",
            "[row(flag: true, n: 4)]",
            "if b.exists(lambda r -> r.flag) then 1 else 0",
            "1",
        ),
    ] {
        let ns = format!("zy11jlib{name}");
        let body = format!("{decls}{}", bound(ty, init, call));
        assert_eq!(run(&ns, &body), answer, "{ns}");
    }
}

/// The alias reached by a path is read as the bare name is: through a namespace, through
/// an import, and as a child of the sort that declares it. Before, `Host.HA` — the child
/// of a sort — was lowered on its own route and stayed the alias's name through the first
/// cut of this change: refused at `Box.unbox.dispatch`, and `Host.HB`'s open slot open to
/// anything.
#[test]
fn an_alias_reached_by_a_path_is_read_as_the_bare_name_is() {
    let decls = "  namespace inner\n    sort IA = Box[V = Int64]\n  end\n  \
                 sort Host\n    sort HA = Box[V = Int64]\n    sort HB = Box\n    entity h\n  end\n";
    for (name, ty) in [("namespace", "inner.IA"), ("child", "Host.HA")] {
        let ns = format!("zy11jpath{name}");
        let body = format!("{decls}{}", bound(ty, "Box.mk(5)", "Box.unbox(b)"));
        assert_eq!(run(&ns, &body), "5", "{ns}");
        let ns = format!("zy11jpathparam{name}");
        let decl = format!("via(b: {ty}) -> Int64 = Box.unbox(b)");
        assert_eq!(run(&ns, &format!("{decls}{}", through(&decl, "Box.mk(5)"))), "5", "{ns}");
    }
    let imported = format!(
        "{decls}  import test.zy11jpathimport.inner.{{IA}}\n{}",
        bound("IA", "Box.mk(5)", "Box.unbox(b)")
    );
    assert_eq!(run("zy11jpathimport", &imported), "5");
    let rendered = refusal(
        "zy11jpathopen",
        &format!("{decls}{}", through("via(b: Host.HB) -> Int64 = b.v", "Box.mk(\"s\")")),
    );
    assert!(
        rendered.contains("via.return (op-return): expected Int64, got b.V"),
        "{rendered}"
    );
}

/// An alias of a type that is no sort application — a tuple, an arrow — and one whose
/// type holds a value. Before: "f.p (op-arg): expected P2, got (a: Int64, b: Bool)"; the
/// callback "f.apply: … unknown functor"; and `Vec.elem.dispatch` for the last.
#[test]
fn an_alias_of_a_tuple_an_arrow_or_a_type_holding_a_value_is_that_type() {
    let vec = "  sort Vec[E, N]\n    entity vec(e: E)\n    operation elem(x: Self) -> E = x.e\n  end\n  \
               sort VI3 = Vec[E = Int64, N = 3]\n  sort V3 = Vec[N = 3]\n";
    for (name, body, answer) in [
        (
            "tuple",
            "  sort P2 = (a: Int64, b: Bool)\n  operation f(p: P2) -> Int64 = p.a\n  \
             operation go() -> Int64 = f((a: 3, b: true))"
                .to_string(),
            "3",
        ),
        (
            "arrow",
            "  sort Fn1 = (x: Int64) -> Int64\n  operation app(f: Fn1, v: Int64) -> Int64 = f(v)\n  \
             operation go() -> Int64 = app(lambda x -> x + 1, 4)"
                .to_string(),
            "5",
        ),
        ("value", format!("{vec}{}", bound("VI3", "vec(e: 1)", "Vec.elem(b)")), "1"),
        (
            "valueparam",
            format!("{vec}{}", through("via(v: VI3) -> Int64 = Vec.elem(v)", "vec(e: 1)")),
            "1",
        ),
    ] {
        let ns = format!("zy11jshape{name}");
        assert_eq!(run(&ns, &body), answer, "{ns}");
    }
    // The slot such an alias leaves open is open, as the written type's is.
    for (spelling, ty) in [("alias", "V3"), ("written", "Vec[N = 3]")] {
        let ns = format!("zy11jshapeopen{spelling}");
        let decl = format!("via(v: {ty}) -> Int64 = Vec.elem(v)");
        let rendered = refusal(&ns, &format!("{vec}{}", through(&decl, "vec(e: \"s\")")));
        assert!(
            rendered.contains("via.return (op-return): expected Int64, got v.E"),
            "{ns}: {rendered}"
        );
    }
}

/// An alias that also owns members (`namespace X` beside `sort X = …`) has two readings
/// as a name and one as a type: `b: X` is a `Box[V = Int64]`, and `X.extra` is still
/// `X`'s own. Before, the typed value was refused at `Box.unbox.dispatch`.
#[test]
fn an_alias_that_owns_members_is_its_type_where_a_type_is_written() {
    let decls = "  sort X = Box[V = Int64]\n  namespace X\n    operation extra() -> Int64 = 3\n  end\n";
    for (name, body, answer) in [
        ("let", bound("X", "Box.mk(5)", "Box.unbox(b)"), "5"),
        ("param", through("via(b: X) -> Int64 = b.unbox()", "Box.mk(5)"), "5"),
        ("member", "  operation go() -> Int64 = X.extra()".to_string(), "3"),
    ] {
        let ns = format!("zy11jowned{name}");
        assert_eq!(run(&ns, &format!("{decls}{body}")), answer, "{ns}");
    }
}

/// A provision is found whichever way its clause and the value spell the type. Before,
/// the clause written out and the value typed by the alias did not meet: "`CA` provides
/// no `Tag`".
#[test]
fn a_provision_and_a_value_meet_through_an_alias_on_either_side() {
    for (clause, at) in [("alias", "CA"), ("written", "Box[V = Int64]")] {
        for (value, ty) in [("alias", "CA"), ("written", "Box[V = Int64]")] {
            let ns = format!("zy11jprov{clause}{value}");
            let body = format!(
                "  sort Tag[T]\n    operation tag(x: T) -> Int64\n  end\n  \
                 sort W\n    provides Tag[T = {at}]\n    operation tag(x: {at}) -> Int64 = 8\n  end\n{}",
                bound(ty, "Box.mk(5)", "Tag.tag(b)")
            );
            assert_eq!(run(&ns, &body), "8", "{ns}");
        }
    }
}

/// An alias OF a parameter of the sort declaring it is that parameter: over `sort Cell[T]`
/// with `sort TA = T`, a result and an argument typed `TA` are the cell's `T`, held to it.
#[test]
fn an_alias_of_its_sorts_parameter_is_that_parameter() {
    let cell = "  sort Cell[T]\n    sort TA = T\n    entity cell(t: T)\n    \
                operation get(c: Self) -> TA = c.t\n    \
                operation put(c: Self, x: TA) -> Int64 = 1\n  end\n";
    for (name, go, answer) in [
        ("get", "Int64 = Cell.get(cell(t: 5))", "5"),
        ("put", "Int64 = Cell.put(cell(t: 5), 6)", "1"),
    ] {
        let ns = format!("zy11jparamalias{name}");
        assert_eq!(run(&ns, &format!("{cell}  operation go() -> {go}")), answer, "{ns}");
    }
    for (name, go, refused) in [
        ("get", "String = Cell.get(cell(t: 5))", "go.return (op-return): expected String, got Int64"),
        ("put", "Int64 = Cell.put(cell(t: 5), \"s\")", "put.x (op-arg): expected Int64, got String"),
    ] {
        let ns = format!("zy11jparamaliasbad{name}");
        let rendered = refusal(&ns, &format!("{cell}  operation go() -> {go}"));
        assert!(rendered.contains(refused), "{ns}: {rendered}");
    }
}

/// OUTSIDE the sort that declares the parameter, an alias that names it is not read
/// through: the parameter is nobody's there. `f(x: Outer.OS) -> Int64 = x` is refused,
/// the alias being a name nothing conforms to. Read through — as the first delivery of
/// this change did — `x` was any type at all, the declaration loaded, and `f("s")`
/// answered the string. Inside the sort, and in an entry at its address, the same alias
/// is the parameter.
#[test]
fn an_alias_that_names_a_parameter_is_read_only_inside_its_sort() {
    let outer = "  sort Outer[S]\n    sort OB = Box[V = S]\n    sort OS = S\n    entity outer(o: S)\n    \
                 operation inside(b: OB) -> S = Box.unbox(b)\n    operation own(x: OS) -> S = x\n  end\n";
    for (name, decl, arg, refused) in [
        ("param", "via(x: Outer.OS) -> Int64 = x", "\"s\"", "via.x (op-arg): expected OS, got String"),
        ("applied", "via(b: Outer.OB) -> Int64 = 1", "Box.mk(\"s\")", "via.b (op-arg): expected OB, got Box[V = String]"),
    ] {
        let ns = format!("zy11joutside{name}");
        let rendered = refusal(&ns, &format!("{outer}{}", through(decl, arg)));
        assert!(rendered.contains(refused), "{ns}: {rendered}");
    }
    for (name, go) in [
        ("inside", "Outer.inside(Box.mk(5))"),
        ("own", "Outer.own(5)"),
    ] {
        let ns = format!("zy11jwithin{name}");
        assert_eq!(run(&ns, &format!("{outer}  operation go() -> Int64 = {go}")), "5", "{ns}");
    }
    let entry = format!(
        "{outer}  namespace Outer\n    operation later(b: OB) -> S = Box.unbox(b)\n  end\n  \
         operation go() -> Int64 = Outer.later(Box.mk(5))"
    );
    assert_eq!(run("zy11jwithinentry", &entry), "5");
}

/// An alias that names a parameter of the sort declaring it is at that parameter:
/// `b: OB` inside `sort Outer[S]` is `b: Box[V = S]`. Before: "unbox.b (op-arg): expected
/// Box[V = ?_], got OB".
#[test]
fn an_alias_that_names_its_sorts_parameter_is_at_that_parameter() {
    for (spelling, decl, ty) in [
        ("alias", "    sort OB = Box[V = S]\n", "OB"),
        ("written", "", "Box[V = S]"),
    ] {
        let ns = format!("zy11jouter{spelling}");
        let body = format!(
            "  sort Outer[S]\n{decl}    entity outer(o: S)\n    \
             operation viaOuter(b: {ty}) -> S = Box.unbox(b)\n  end\n  \
             operation go() -> Int64 = Outer.viaOuter(Box.mk(5))"
        );
        assert_eq!(run(&ns, &body), "5", "{ns}");
    }
}

// ── a clause written at an alias ────────────────────────────────────────────

/// A spec over one parameter, a sort providing it at itself, and an alias of that sort.
const SHOWN: &str = "  sort Show[T]\n    operation show(x: T) -> Int64\n  end\n  \
                     sort Sx[A]\n    entity sx(a: A)\n    provides Show[T = Sx[A]]\n    \
                     operation show(x: Sx[A]) -> Int64 = 7\n  end\n  sort SI = Sx[A = Int64]\n";

/// A requirement written at an alias is the requirement at its type, in an operation's
/// clause and in a sort's, whichever way the parameter spells the type. Before, each row
/// with the alias in the clause was refused at the call: "requirement `Show[T = SI]`
/// cannot be supplied … no impl provides Show".
#[test]
fn a_requirement_written_at_an_alias_is_asked_at_its_type() {
    let spellings = [("alias", "SI"), ("written", "Sx[A = Int64]")];
    for (clause, at) in spellings {
        for (param, ty) in spellings {
            let ns = format!("zy11jreqop{clause}{param}");
            let decl = format!("via(x: {ty}) -> Int64 requires Show[T = {at}] = Show.show(x)");
            assert_eq!(run(&ns, &format!("{SHOWN}{}", through(&decl, "Sx.sx(5)"))), "7", "{ns}");

            let ns = format!("zy11jreqsort{clause}{param}");
            let body = format!(
                "{SHOWN}  sort Use\n    requires Show[T = {at}]\n    entity u\n    \
                 operation f(x: {ty}) -> Int64 = Show.show(x)\n  end\n  \
                 operation go() -> Int64 = Use.f(Sx.sx(5))"
            );
            assert_eq!(run(&ns, &body), "7", "{ns}");
        }
        // Handed on to an operation that requires it of its own parameter.
        let ns = format!("zy11jreqforward{clause}");
        let body = format!(
            "{SHOWN}  operation g[P](x: P) -> Int64 requires Show[T = P] = Show.show(x)\n  \
             operation via(x: SI) -> Int64 requires Show[T = {at}] = g(x)\n  \
             operation go() -> Int64 = via(Sx.sx(5))"
        );
        assert_eq!(run(&ns, &body), "7", "{ns}");
    }
    // A requirement nothing provides is refused through the alias as it is written out,
    // and names the sort.
    for (spelling, at) in [("alias", "NA"), ("written", "NoShow")] {
        let ns = format!("zy11jreqnone{spelling}");
        let body = format!(
            "{SHOWN}  sort NoShow\n    entity noshow\n  end\n  sort NA = NoShow\n  \
             operation via(x: NoShow) -> Int64 requires Show[T = {at}] = 1\n  \
             operation go() -> Int64 = via(noshow)"
        );
        let rendered = refusal(&ns, &body);
        assert!(
            rendered.contains(&format!("requirement `test.{ns}.Show[T = test.{ns}.NoShow]` cannot be supplied")),
            "{ns}: {rendered}"
        );
    }
}

/// Two provisions of one type, one written through the alias, are two provisions of it:
/// the call is refused as ambiguous, as the pair written out is, and the bracket the
/// refusal advises picks one. Before, the alias row loaded and the call ran the second
/// provider in silence.
#[test]
fn a_provision_written_at_an_alias_is_a_provision_at_its_type() {
    for (spelling, at) in [("alias", "CA"), ("written", "Box[V = Int64]")] {
        let providers = format!(
            "  sort Tag[T]\n    operation tag(x: T) -> Int64\n  end\n  \
             sort W1\n    provides Tag[T = {at}]\n    operation tag(x: {at}) -> Int64 = 8\n  end\n  \
             sort W2\n    provides Tag[T = Box[V = Int64]]\n    \
             operation tag(x: Box[V = Int64]) -> Int64 = 9\n  end\n"
        );
        let ns = format!("zy11jtwo{spelling}");
        let rendered = refusal(
            &ns,
            &format!("{providers}  operation go() -> Int64 = Tag.tag(Box.mk(5))"),
        );
        assert!(
            rendered.contains("ambiguous dispatch of") && rendered.contains("2 instances provide"),
            "{ns}: {rendered}"
        );
        for (pick, answer) in [("W1", "8"), ("W2", "9")] {
            let ns = format!("zy11jtwo{spelling}{}", pick.to_lowercase());
            let body = format!(
                "{providers}  operation go() -> Int64 = Tag.tag[Tag = {pick}](Box.mk(5))"
            );
            assert_eq!(run(&ns, &body), answer, "{ns}");
        }
    }
}

/// A clause binding written through an alias that names a parameter of its sort is about
/// that parameter, as the clause with the type written out is: an operation's
/// requirement, the sort's, and a provision. Before, each alias row was refused where its
/// written twin loaded — the operation's as "expected `requires Show[…]` covering abstract
/// type parameter", the provision's as a member that "takes less than the spec's".
#[test]
fn a_clause_binding_naming_its_sorts_parameter_through_an_alias_is_about_that_parameter() {
    for (spelling, at) in [("alias", "OS"), ("written", "Sx[A = S]")] {
        let outer = |members: &str| {
            format!(
                "{SHOWN}  sort Outer[S]\n    sort OS = Sx[A = S]\n    entity outer(o: S)\n{members}  end\n"
            )
        };
        let ns = format!("zy11jparamreqop{spelling}");
        let body = format!(
            "{}  operation go() -> Int64 = Outer.tell(Sx.sx(5))",
            outer(&format!(
                "    operation tell(x: Sx[A = S]) -> Int64 requires Show[T = {at}] = Show.show(x)\n"
            ))
        );
        assert_eq!(run(&ns, &body), "7", "{ns}");

        let ns = format!("zy11jparamreqsort{spelling}");
        let body = format!(
            "{}  operation go() -> Int64 = Outer.f(Sx.sx(5))",
            outer(&format!(
                "    requires Show[T = {at}]\n    operation f(x: Sx[A = S]) -> Int64 = Show.show(x)\n"
            ))
        );
        assert_eq!(run(&ns, &body), "7", "{ns}");
    }
    for (spelling, at) in [("alias", "OB"), ("written", "Box[V = S]")] {
        let ns = format!("zy11jparamprov{spelling}");
        let body = format!(
            "  sort Tag[T]\n    operation tag(x: T) -> Int64\n  end\n  \
             sort Wrap[S]\n    sort OB = Box[V = S]\n    entity wrap(w: S)\n    \
             provides Tag[T = {at}]\n    operation tag(x: Box[V = S]) -> Int64 = 9\n  end\n  \
             operation go() -> Int64 = Tag.tag(Box.mk(\"s\"))"
        );
        assert_eq!(run(&ns, &body), "9", "{ns}");
    }
    // …and a member that does not fit is told the same thing in both spellings: the
    // spec's parameter is the sort's own, which the member's `Int64` is narrower than.
    for (spelling, at) in [("alias", "OP"), ("written", "S")] {
        let ns = format!("zy11jparamnofit{spelling}");
        let body = format!(
            "  sort Tag[T]\n    operation tag(x: T) -> Int64\n  end\n  \
             sort Wrap[S]\n    sort OP = S\n    entity wrap(w: S)\n    \
             provides Tag[T = {at}]\n    operation tag(x: Int64) -> Int64 = 9\n  end\n  \
             operation go() -> Int64 = 1"
        );
        let rendered = refusal(&ns, &body);
        assert!(
            rendered.contains("takes less than the spec's") && rendered.contains("every `S`"),
            "{ns}: {rendered}"
        );
    }
}

// ── an alias whose type leaves a slot open ──────────────────────────────────

/// An alias whose definition leaves a slot open with `?` — `sort Some = Box[V = ?]` — names
/// no type parameter, and is its type wherever it is written: in another namespace too.
/// Before, the use from another namespace was refused, "expected Box, got Some".
#[test]
fn an_alias_with_an_open_slot_is_its_type_in_another_namespace() {
    for (spelling, ty) in [("alias", "Some"), ("written", "Bag[V = ?]")] {
        let ns = format!("zy11jopenfar{spelling}");
        let src = format!(
            "namespace test.{ns}lib\n  import anthill.prelude.{{Int64}}\n  \
             sort Bag[V]\n    entity bag(v: V)\n    operation count(b: Bag) -> Int64 = 1\n  end\n  \
             sort Some = Bag[V = ?]\nend\n\
             namespace test.{ns}\n  import anthill.prelude.{{Int64}}\n  \
             import test.{ns}lib.{{Bag, Some}}\n  import test.{ns}lib.Bag.{{bag}}\n  \
             operation via(x: {ty}) -> Int64 = Bag.count(x)\n  \
             operation go() -> Int64 = via(bag(v: 5))\nend\n"
        );
        let mut interp = interp_for(&src);
        let value = interp
            .call(&format!("test.{ns}.go"), &[])
            .unwrap_or_else(|e| panic!("{ns}: {e:?}"));
        assert_eq!(shown(value), "1", "{ns}");
    }
}

/// The slot is open anew at each place the alias is written, as each written `?` is: two
/// parameters typed by the alias take two boxes. Before, the second was held to the
/// first's: "expected Some (Box[V = Int64]), got Box[V = String]". It is still a box.
#[test]
fn an_open_slot_of_an_alias_is_open_anew_at_each_use() {
    for (spelling, ty) in [("alias", "Some"), ("written", "Box[V = ?]")] {
        let ns = format!("zy11jopentwo{spelling}");
        let body = format!(
            "  sort Some = Box[V = ?]\n  operation two(a: {ty}, b: {ty}) -> Int64 = 1\n  \
             operation go() -> Int64 = two(Box.mk(1), Box.mk(\"s\"))"
        );
        assert_eq!(run(&ns, &body), "1", "{ns}");

        let ns = format!("zy11jopentwobad{spelling}");
        let body = format!(
            "  sort Some = Box[V = ?]\n  operation two(a: {ty}, b: {ty}) -> Int64 = 1\n  \
             operation go() -> Int64 = two(Box.mk(1), \"s\")"
        );
        let rendered = refusal(&ns, &body);
        assert!(
            rendered.contains("two.b (op-arg)") && rendered.contains("got String"),
            "{ns}: {rendered}"
        );
    }
    // The same where the alias is applied to the parameter it leaves unwritten.
    for (spelling, ty) in [("alias", "HP[R = Int64]"), ("written", "Pair[L = ?, R = Int64]")] {
        let ns = format!("zy11jopenapplied{spelling}");
        let body = format!(
            "  sort HP = Pair[L = ?]\n  operation two(a: {ty}, b: {ty}) -> Int64 = 1\n  \
             operation go() -> Int64 = two(Pair.pair(l: 1, r: 2), Pair.pair(l: \"s\", r: 3))"
        );
        assert_eq!(run(&ns, &body), "1", "{ns}");
    }
}

/// A clause binding written through such an alias is the clause with the type written
/// out. Before, the alias row was refused: "requirement `Show[T = SomeSx]` cannot be
/// supplied".
#[test]
fn a_clause_binding_at_an_alias_with_an_open_slot_is_asked_at_its_type() {
    for (spelling, at) in [("alias", "SomeSx"), ("written", "Sx[A = ?]")] {
        let ns = format!("zy11jopenreq{spelling}");
        let decl = format!("via(x: Sx[A = Int64]) -> Int64 requires Show[T = {at}] = Show.show(x)");
        let body = format!("{SHOWN}  sort SomeSx = Sx[A = ?]\n{}", through(&decl, "Sx.sx(5)"));
        assert_eq!(run(&ns, &body), "7", "{ns}");
    }
}

/// An alias of an alias is judged link by link where a clause names it as its spec: a
/// link that also owns members has two readings, through the chain as written directly.
/// The alias's record keeps a bare link as the name it is written with for this.
#[test]
fn a_spec_named_through_a_chain_is_refused_where_a_link_owns_members() {
    let decls = "  sort Spec1[T]\n    operation one(x: T) -> Int64\n  end\n  \
                 sort S1 = Spec1[T = Int64]\n  namespace S1\n    operation extra() -> Int64 = 3\n  end\n  \
                 sort S2 = S1\n";
    for (spelling, spec) in [("chain", "S2"), ("direct", "S1")] {
        let ns = format!("zy11jlink{spelling}");
        let body = format!(
            "{decls}  sort Imp\n    provides {spec}\n    operation one(x: Int64) -> Int64 = x\n  end\n  \
             operation go() -> Int64 = Spec1.one(4)"
        );
        let rendered = refusal(&ns, &body);
        assert!(
            rendered.contains("is declared both as a type alias and with members of its own"),
            "{ns}: {rendered}"
        );
    }
}

// ── effect rows ─────────────────────────────────────────────────────────────

/// A registered effect kind, an operation that declares it, and a sort that names it by
/// `effects E = Boom`.
fn host(call: &str) -> String {
    format!(
        "  sort Boom\n    entity bang\n  end\n  namespace Boom\n    provides Effect[T = Boom]\n  end\n  \
         operation risky() -> Int64 effects Boom = 7\n  \
         sort Host\n    effects E = Boom\n    entity h\n    operation {call}\n  end\n"
    )
}

/// An alias in a row written inside a type is the label it stands for: `@ {E}` over
/// `effects E = Boom` admits a callback that incurs `Boom`, as `@ {Boom}` does, and
/// `@ {EffP, -E}` refuses it, as `-Boom` does. Before, the first was refused — "the
/// lambda argument declares `Boom`, which the closed row does not admit" — and the second
/// was refused for `EffP`, "unconstrained".
#[test]
fn an_alias_in_an_arrows_row_is_the_label_it_stands_for() {
    for (spelling, label) in [("alias", "E"), ("written", "Boom")] {
        let ns = format!("zy11jarrow{spelling}");
        let decls = host(&format!(
            "call(f: () -> Int64 @ {{{label}}}) -> Int64 effects {{{label}}} = f()"
        ));
        let body = format!(
            "{decls}  operation go() -> Int64 effects Boom = Host.call(lambda () -> risky())"
        );
        assert_eq!(run(&ns, &body), "7", "{ns}");

        let ns = format!("zy11jlacks{spelling}");
        let decls = host(&format!(
            "call[EffP](f: () -> Int64 @ {{EffP, -{label}}}) -> Int64 effects {{EffP}} = f()"
        ));
        let body = format!(
            "{decls}  operation go() -> Int64 effects Boom = Host.call(lambda () -> risky())"
        );
        let rendered = refusal(&ns, &body);
        assert!(
            rendered.contains("to lack `Boom` (its `-…` lacks-constraint)"),
            "{ns}: {rendered}"
        );
    }
}

/// In an operation's OWN row the alias is kept as it is written, bare, under a `-` and
/// under a guard: the effect rules follow it, and name the element the author wrote
/// beside what it stands for. Read through there, the refusal named a label that is
/// nowhere in the source.
#[test]
fn an_operations_own_row_names_its_alias_as_written() {
    for (name, row, written) in [
        ("bare", "{E}", "`E`"),
        ("path", "{B.E}", "`E`"),
        ("guarded", "{ E :- eq(p, 0) }", "`E`"),
        ("absent", "{EffP, -E}", "`-E`"),
    ] {
        let bracket = if name == "absent" { "[EffP]" } else { "" };
        let op = format!("    operation run{bracket}(p: Int64) -> Int64 effects {row} = p\n");
        // Bound to a `Modify` of a type: the target rule refuses it.
        let ns = format!("zy11jown{name}");
        let body = format!(
            "  sort Thing\n    entity thing(v: String)\n  end\n  \
             sort B\n    effects E = Modify[Thing]\n    entity b(tag: String)\n{op}  end\n  \
             operation go() -> Int64 = 1"
        );
        let rendered = refusal(&ns, &body);
        assert!(
            rendered.contains(&format!(
                "declares effect {written}, which names `Modify[T = Thing]`, whose target is a TYPE"
            )),
            "{ns}: {rendered}"
        );
        // Bound to a sort nothing registered as an effect: the registration rule does.
        let ns = format!("zy11junreg{name}");
        let body = format!(
            "  sort Boop\n    entity boop\n  end\n  \
             sort B\n    effects E = Boop\n    entity b(tag: String)\n{op}  end\n  \
             operation go() -> Int64 = 1"
        );
        let rendered = refusal(&ns, &body);
        assert!(
            rendered.contains("declares effect `E`, but `test.")
                && rendered.contains("Boop` is not a REGISTERED effect kind"),
            "{ns}: {rendered}"
        );
    }
}
