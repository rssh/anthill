//! WI-20261103-95S43 — a projection off a value typed by a type-var of the spec a body is written
//! in is this instance's member, at every reader of that body.
//!
//! In `sort Coll { sort C = ?  sort Elem = ?  operation first(c: C) -> Elem … }`, `c.Elem` off `c:
//! C` is the element of the collection `c` is, and inside `Coll` that is `Elem`. A sibling call
//! already read its callee's signature so (`this_instance_member`, WI-20261001-80ZV8), and a
//! body-less `has(c: C, e: c.Elem)` loaded; the body's own readers refused it, "cannot project
//! 'Elem' off an abstract receiver with no concrete sort": a `let`'s annotation, a lambda's
//! binder, the body's own signature (`-> c.Elem` at `pick.return`, a parameter `e: c.Elem`), and
//! the `Eq` key check, which refused `Set[T = c.Elem]` as not judged ("type 'Coll.C' has no
//! member 'Elem'").
//!
//! Now every body reader reads it through the one gate ([`own_carrier_member`]). The receiver may
//! be typed by ANY type-var of the spec — the sort carrier is all of them (decision 4 of
//! `docs/design/spec-carrier-set.md`), so `e.C` off `e: Elem` reads as `c.Elem` off `c: C`, in
//! either declaration order (the user, 2026-11-28; read off the one parameter `spec_carrier_param`
//! answers, the verdict turned on the order). The spec is a sort with a dictionary (not a data
//! sort, whose type-var is the type of a part: `Box`, `Pair2`), the member is not the receiver's
//! own type-var, and no `requires` clause about that type-var binds the member to another type (`Storage[C = S, Key = Int64]` beside the sort's own `Key`, which is
//! WI-20261103-G5FK3's) — a clause that binds it to the spec's own parameter
//! (`requires Walk[C = C, Elem = Elem]`) agrees, and reads. The sibling call reads through the
//! same gate, which closes it to a sort with values of its own (`Mk`'s `peek(a)` read `a.B`), to
//! a type-var read as a member of itself, and to a clause that binds the member otherwise. A
//! default body's declared row reads the same way (`effects c.E`).
//!
//! AND A NESTED CALL IS NOT HINTED WITH A PROJECTION. `has(c, first(c))` over `e: c.Elem` was
//! refused while `let x = first(c)` then `has(c, x)` loaded: the outer call handed `first(c)`
//! its parameter's type, `c.Elem` in `has`'s names, as the expected type, and `first` was placed
//! at `Elem = c.Elem`, "another instance". `nested_call_arg_hint`'s doc said the ground gate
//! skipped a projection; one off a value reference is ground. Outside any spec the same hint
//! pinned `nothing()`'s `X` to `k`'s `s.E` in `k(leaf(e: 1), nothing())`. The test is the call's
//! (`one_arg_hint`): a constructor's field type is checked as written, and a rigid projection
//! there still hints.
//!
//! BACK-OUTS, MEASURED (2026-11-28) — each ONE part put back, over this file's 13 rows and the
//! 197 of `wi_80zv8_*`, `wi_sg16k_*`, `wi_7ab56_*`, `wi590_*` and `wi_bh1jz_*` beside them (none
//! of which fails under any part):
//!
//!  * The body readers not reading it (`project_off_receiver`'s `Receivers::Own` arm removed) — 6:
//!    [`each_reader_reads_the_own_carrier_projection_as_the_instances_member`] (each spelling is
//!    refused "cannot project 'Elem' off an abstract receiver", as before),
//!    [`the_reading_does_not_turn_on_the_declaration_order`],
//!    [`a_nested_sibling_call_is_at_this_instance`] (at `take`'s parameter),
//!    [`a_requires_that_binds_the_member_to_the_specs_own_parameter_reads`],
//!    [`a_default_body_declares_its_row_through_the_carrier`], and
//!    [`the_member_is_the_instances_and_no_other_type`], refused for the projection and not for
//!    the `1`.
//!  * The receiver held to the one parameter `spec_carrier_param` answers — 1:
//!    [`the_reading_does_not_turn_on_the_declaration_order`] (each order refuses one reading).
//!  * The class gate put back to `spec_is_self_representing` alone — 1:
//!    [`a_sibling_call_reads_through_the_same_gate`] (`Mk`'s `peek(a)` loads).
//!  * The receiver's-own-type-var gate removed — 2: [`a_type_var_is_no_member_of_itself`] (`let
//!    y: x.T = x` loads) and [`a_sibling_call_reads_through_the_same_gate`] (`Sp`'s `peek(x)`
//!    loads).
//!  * The `requires` gate removed — 2: [`a_requires_that_binds_the_member_otherwise_is_not_read`]
//!    (`let j: s.Key = k` loads, `s.Key` read as `H`'s own `Key`) and
//!    [`a_sibling_call_reads_through_the_same_gate`] (`H`'s `look(s)` loads).
//!  * Every clause about the type-var that declares the member stopping the reading, one binding
//!    it to the spec's own parameter too — 1:
//!    [`a_requires_that_binds_the_member_to_the_specs_own_parameter_reads`].
//!  * The `Eq` key check not reading it (`read_projection_key` given no reading) — 1:
//!    [`each_reader_reads_the_own_carrier_projection_as_the_instances_member`], its `key` row
//!    refused "not judged … type 'Coll.C' has no member 'Elem'".
//!  * A call's nested argument hinted with a projection (`one_arg_hint`'s test removed) — 2:
//!    [`a_nested_sibling_call_is_at_this_instance`] ("`first` at `Coll[Elem = c.Elem]`, another
//!    instance") and [`a_nested_call_is_not_hinted_in_the_callees_names`] ("expected Option[T =
//!    Int64], got Option[T = s.E]").
//!  * The test put in `nested_call_arg_hint` instead, which a constructor's field shares — 1:
//!    [`a_constructor_field_still_hints_a_nested_call`] ("X unconstrained").
//!  * The sibling call's declared-slot test removed (found by the second /code-review, measured on
//!    its own row after the others) — 1:
//!    [`a_sibling_call_reads_only_at_the_slot_its_parameter_is_declared_at`] (refused as "another
//!    instance", the callee's `c.Elem` read as this instance's `Elem`).
//!
//! PASS EITHER WAY BY DESIGN: [`a_member_the_spec_does_not_declare_is_refused`], the control;
//! [`a_call_reads_the_projection_off_the_provisions_at_its_argument`], added after the back-outs
//! were measured, which pins the call's reading and no part of this change; and
//! [`a_data_sorts_element_is_no_carrier`], the ticket's `Box` and `Pair2`, which the class gate
//! put back to `spec_is_self_representing` refuses too — every data sort answers it `true`,
//! MEASURED for `Box`, `Pair2` and a field-less `entity tag` sort — and `Box` the
//! receiver's-own-type-var gate besides.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `Coll` with `member` in its body, `Bag` providing it at `Int64`, and `go`, which calls
/// `Coll.pick` at a `Bag` of 7.
fn coll(ns: &str, member: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Set}}
  sort Coll
    sort C = ?
    sort Elem = ?
    operation first(c: C) -> Elem
{member}
  end
  sort Bag
    entity bag(x: Int64)
    provides Coll[C = Self, Elem = Int64]
    operation first(b: Self) -> Int64 = b.x
  end
  operation go() -> Int64 = Coll.pick(bag(x: 7))
end
"#
    )
}

/// `src` is refused, naming each of `tokens`.
#[track_caller]
fn assert_refused(src: &str, tokens: &[&str], why: &str) {
    assert_refused_naming(&load_errors_of(src), tokens, why);
}

/// The four spellings of the ticket, and a parameter typed by the projection, each in a spec's
/// default body: each loads, and runs at `Bag` to the element `first` gives. The `key` row's
/// capability is the LOAD: the `Eq` key check judges `Set[T = c.Elem]` there (nothing in the
/// standard library provides `Set`, so no set is built to apply the lambda to); its back-out is
/// the refusal "not judged".
#[test]
fn each_reader_reads_the_own_carrier_projection_as_the_instances_member() {
    let rows = [
        (
            "let",
            "    operation pick(c: C) -> Elem =\n      let e: c.Elem = first(c)\n      e",
            7,
        ),
        (
            "lambda",
            "    operation pick(c: C) -> Elem =\n      let h = lambda (e: c.Elem) -> e\n      h(first(c))",
            7,
        ),
        ("return", "    operation pick(c: C) -> c.Elem = first(c)", 7),
        (
            "key",
            "    operation pick(c: C) -> Int64 =\n      let h = lambda (s: Set[T = c.Elem]) -> 3\n      3",
            3,
        ),
        (
            "parameter",
            "    operation take(c: C, e: c.Elem) -> Elem = e\n    operation pick(c: C) -> Elem =\n      let x = first(c)\n      take(c, x)",
            7,
        ),
    ];
    for (tag, member, value) in rows {
        let ns = format!("wi95s43.reads.{tag}");
        assert_eq!(run_int64(&coll(&ns, member), &format!("{ns}.go")), Ok(value), "{tag}");
    }
}

/// THE READING DOES NOT TURN ON THE DECLARATION ORDER: beside `wrap(e: Elem) -> C`, which takes
/// `Elem` as `first(c: C)` takes `C`, `c.Elem` off `c: C` and `e.C` off `e: Elem` both read, with
/// `C` declared first and with `Elem` first, and run (`7 * 100 + 8`). Read off the one parameter
/// `spec_carrier_param` answers, the first declared, each was refused in one of the two orders.
#[test]
fn the_reading_does_not_turn_on_the_declaration_order() {
    for (tag, params) in [("c_first", "    sort C = ?\n    sort Elem = ?"), ("elem_first", "    sort Elem = ?\n    sort C = ?")] {
        let ns = format!("wi95s43.order.{tag}");
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Coll
{params}
    operation wrap(e: Elem) -> C
    operation first(c: C) -> Elem
    operation pick(c: C) -> Elem =
      let e: c.Elem = first(c)
      e
    operation rewrap(c: C) -> C =
      let e = first(c)
      let d: e.C = wrap(e)
      d
  end
  sort Bag
    entity bag(x: Int64)
    provides Coll[C = Self, Elem = Int64]
    operation wrap(e: Int64) -> Self = bag(x: e + 1)
    operation first(b: Self) -> Int64 = b.x
  end
  operation go() -> Int64 = Coll.pick(bag(x: 7)) * 100 + Coll.first(Coll.rewrap(bag(x: 7)))
end
"#
        );
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(708), "{tag}");
    }
}

/// A CALL STILL READS IT OFF THE PROVISIONS AT ITS ARGUMENT, and which provisions cover an argument
/// is read at the one parameter dispatch reads (kernel-language.md §5.1, "Dispatch still reads one
/// parameter"): `Coll.back(7)` over `back(e: Elem) -> e.C` reads `Bag`'s `C` and runs where `Elem`
/// is declared first, and is refused where `C` is — `Int64` has no member `C`, `Bag`'s provision
/// being filed at `C`. Refused, never read as another type. PINS THE CALL'S ORDER DEPENDENCE, which
/// is dispatch's and not this reading's: the body's `wrap(e)` against `-> e.C` loads in both orders.
#[test]
fn a_call_reads_the_projection_off_the_provisions_at_its_argument() {
    let program = |ns: &str, params: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Coll
{params}
    operation wrap(e: Elem) -> C
    operation first(c: C) -> Elem
    operation back(e: Elem) -> e.C = wrap(e)
  end
  sort Bag
    entity bag(x: Int64)
    provides Coll[C = Self, Elem = Int64]
    operation wrap(e: Int64) -> Self = bag(x: e + 1)
    operation first(b: Self) -> Int64 = b.x
  end
  operation go() -> Int64 = Coll.first(Coll.back(7))
end
"#
        )
    };
    let ns = "wi95s43.call.elem_first";
    assert_eq!(run_int64(&program(ns, "    sort Elem = ?\n    sort C = ?"), &format!("{ns}.go")), Ok(8));
    assert_refused(
        &program("wi95s43.call.c_first", "    sort C = ?\n    sort Elem = ?"),
        &["back.return", "type 'anthill.prelude.Int64' has no member 'C'"],
        "`Coll.back(7)` with `C` declared first",
    );
}

/// A call whose argument is a call of the spec's own operation: `take(c, first(c))` over `e:
/// c.Elem` places `first` at this instance, as `let x = first(c)` does, and runs.
#[test]
fn a_nested_sibling_call_is_at_this_instance() {
    let ns = "wi95s43.nested";
    let member = "    operation take(c: C, e: c.Elem) -> Elem = e\n    operation pick(c: C) -> Elem = take(c, first(c))";
    assert_eq!(run_int64(&coll(ns, member), &format!("{ns}.go")), Ok(7));
}

/// The reading is the instance's member and no other type: the lambda over `c.Elem` applied to
/// `1` is refused, as the instance's `Elem` is any type.
#[test]
fn the_member_is_the_instances_and_no_other_type() {
    let member = "    operation pick(c: C) -> Elem =\n      let h = lambda (e: c.Elem) -> e\n      h(1)";
    assert_refused(
        &coll("wi95s43.other", member),
        &["h._1 (op-arg)", "got Int64"],
        "`lambda (e: c.Elem)` applied to `1`",
    );
}

/// A DATA SORT'S "CARRIER" IS AN ELEMENT: `put(x: T)` beside `entity box(v: T)` takes `T`, and
/// `mk(a: A, b: B)` beside `entity p2(a: A, b: B)` takes `A`. Off them, `x.T` and `a.B` stay the
/// refusal they were.
#[test]
fn a_data_sorts_element_is_no_carrier() {
    let boxed = r#"
namespace wi95s43.box
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity box(v: T)
    operation put(x: T) -> Box[T = T] =
      let y: x.T = x
      box(v: y)
  end
end
"#;
    assert_refused(boxed, &["cannot project 'T' off an abstract receiver"], "`x.T` in Box");
    let pair = r#"
namespace wi95s43.pair
  import anthill.prelude.{Int64}
  sort Pair2
    sort A = ?
    sort B = ?
    entity p2(a: A, b: B)
    operation mk(a: A, b: B) -> Pair2[A = A, B = B] =
      let y: a.B = b
      p2(a: a, b: y)
  end
end
"#;
    assert_refused(pair, &["cannot project 'B' off an abstract receiver"], "`a.B` in Pair2");
}

/// A SIBLING CALL READS ITS CALLEE THROUGH THE SAME GATE, each of whose refusals loaded there:
/// `peek(a)` over `peek(a: A) -> a.B` in `Mk`, a sort with values of its own (one an operation
/// returns), read `a.B` as `Mk`'s `B`; `peek(x)` over `peek(x: T) -> x.T` read a type-var as a
/// member of itself; and `look(s)` over `look(s: S) -> s.Key` read `H`'s own `Key` under `requires
/// Storage[C = S, Key = Int64]` (MEASURED, each loaded before).
#[test]
fn a_sibling_call_reads_through_the_same_gate() {
    let own_values = r#"
namespace wi95s43.sibling.own_values
  import anthill.prelude.{Int64}
  sort Mk
    sort A = ?
    sort B = ?
    operation make(a: A, b: B) -> Self
    operation peek(a: A) -> a.B
    operation put(a: A) -> B = peek(a)
  end
end
"#;
    assert_refused(own_values, &["cannot project 'B' off an abstract receiver"], "`peek(a)` in Mk");
    let carrier = r#"
namespace wi95s43.sibling.carrier
  import anthill.prelude.{Int64}
  sort Sp
    sort T = ?
    operation peek(x: T) -> x.T
    operation put(x: T) -> T = peek(x)
  end
end
"#;
    assert_refused(carrier, &["peek.return", "cannot project 'T' off an abstract receiver"], "`peek(x)` in Sp");
    let rebound = r#"
namespace wi95s43.sibling.rebound
  import anthill.prelude.{Int64, Bool}
  sort Storage
    sort C = ?
    sort Key = ?
    operation get(s: C, k: Key) -> Bool
  end
  sort H
    sort S = ?
    sort Key = ?
    requires Storage[C = S, Key = Int64]
    operation look(s: S) -> s.Key
    operation g(s: S) -> Key = look(s)
  end
end
"#;
    assert_refused(rebound, &["look.return", "cannot project 'Key' off an abstract receiver"], "`look(s)` in H");
}

/// A SIBLING CALL READS ITS CALLEE ONLY AT THE SLOT ITS PARAMETER IS DECLARED AT: `pick(key(c))`
/// over `pick(c: C) -> c.Elem`, the argument a `K`, is at `Coll[C = K]`, another instance, and its
/// `c.Elem` is not this instance's `Elem` — it is refused at `pick.return`, the projection unread.
/// Read off any type-var's rigid with the slot unasked, it was read as this instance's `Elem`
/// and the call refused only afterwards, as "another instance" (MEASURED).
#[test]
fn a_sibling_call_reads_only_at_the_slot_its_parameter_is_declared_at() {
    let src = r#"
namespace wi95s43.slot
  import anthill.prelude.{Int64}
  sort Coll
    sort C = ?
    sort Elem = ?
    sort K = ?
    operation first(c: C) -> Elem
    operation key(c: C) -> K
    operation pick(c: C) -> c.Elem
    operation use(c: C) -> Elem = pick(key(c))
  end
end
"#;
    let errs = load_errors_of(src);
    assert_refused_naming(&errs, &["pick.return", "cannot project 'Elem' off an abstract receiver"], "`pick(key(c))`");
    assert!(!errs.join(" | ").contains("another instance"), "refused for the projection: {errs:#?}");
}

/// A TYPE-VAR IS NO MEMBER OF ITSELF: `x.T` off `x: T` asks the `T` of `x`'s type — a call reads
/// the receiver's own binding of it — not the instance's `T`.
#[test]
fn a_type_var_is_no_member_of_itself() {
    let src = r#"
namespace wi95s43.carrier
  import anthill.prelude.{Int64}
  sort Sp
    sort T = ?
    operation f(x: T) -> Int64 =
      let y: x.T = x
      0
  end
end
"#;
    assert_refused(src, &["cannot project 'T' off an abstract receiver"], "`x.T` off `x: T`");
}

/// A `requires` CLAUSE THAT BINDS THE MEMBER TO ANOTHER TYPE makes the projection two types —
/// the sort's own `Key` and the clause's `Int64` — and which is not this reading's to say
/// (WI-20261103-G5FK3): `let j: s.Key = k` over `k: Key` stays refused, where read as the sort's
/// own `Key` it loads.
#[test]
fn a_requires_that_binds_the_member_otherwise_is_not_read() {
    let src = r#"
namespace wi95s43.rebound
  import anthill.prelude.{Int64, Bool}
  sort Storage
    sort C = ?
    sort Key = ?
    operation get(s: C, k: Key) -> Bool
  end
  sort H
    sort S = ?
    sort Key = ?
    requires Storage[C = S, Key = Int64]
    operation g(s: S, k: Key) -> Key =
      let j: s.Key = k
      j
  end
end
"#;
    assert_refused(src, &["cannot project 'Key' off an abstract receiver"], "`s.Key` under the clause");
}

/// A `requires` CLAUSE THAT BINDS THE MEMBER TO THE SPEC'S OWN PARAMETER names one type, and the
/// projection reads — in the body and at a sibling call: `Coll requires Walk[C = C, Elem =
/// Elem]`, as the standard library's `FiniteCollection requires Iterable[C = C, Element =
/// Element, E = E]`.
#[test]
fn a_requires_that_binds_the_member_to_the_specs_own_parameter_reads() {
    let src = r#"
namespace wi95s43.agrees
  import anthill.prelude.{Int64}
  sort Walk
    sort C = ?
    sort Elem = ?
    operation step(c: C) -> Elem
  end
  sort Coll
    sort C = ?
    sort Elem = ?
    requires Walk[C = C, Elem = Elem]
    operation first(c: C) -> Elem
    operation peek(c: C) -> c.Elem
    operation pick(c: C) -> Elem =
      let e: c.Elem = first(c)
      peek(c)
  end
  sort Bag
    entity bag(x: Int64)
    provides Walk[C = Self, Elem = Int64]
    provides Coll[C = Self, Elem = Int64]
    operation step(b: Self) -> Int64 = b.x
    operation first(b: Self) -> Int64 = b.x
    operation peek(b: Self) -> Int64 = b.x + 1
  end
  operation go() -> Int64 = Coll.pick(bag(x: 7))
end
"#;
    assert_eq!(run_int64(src, "wi95s43.agrees.go"), Ok(8));
}

/// A DEFAULT BODY DECLARES ITS ROW THROUGH THE CARRIER: `effects c.E` off `c: C` is the
/// instance's `E`, which the sibling calls it makes incur, and runs at a provider binding `E =
/// {}`. It was refused "cannot project 'E' off an abstract receiver" (MEASURED).
#[test]
fn a_default_body_declares_its_row_through_the_carrier() {
    let src = r#"
namespace wi95s43.effects
  import anthill.prelude.{Int64}
  sort Src
    sort C = ?
    effects E = ?
    operation next(c: C) -> Int64
      effects E
    operation twice(c: C) -> Int64
      effects c.E
    = next(c) + next(c)
  end
  sort Bag
    entity bag(x: Int64)
    provides Src[C = Self, E = {}]
    operation next(b: Self) -> Int64 = b.x
  end
  operation go() -> Int64 = Src.twice(bag(x: 7))
end
"#;
    assert_eq!(run_int64(src, "wi95s43.effects.go"), Ok(14));
}

/// CONTROL — a member the spec does not declare stays refused, naming it.
#[test]
fn a_member_the_spec_does_not_declare_is_refused() {
    let member = "    operation pick(c: C) -> Elem =\n      let e: c.Nope = first(c)\n      first(c)";
    assert_refused(
        &coll("wi95s43.nope", member),
        &["cannot project 'Nope'"],
        "`c.Nope`",
    );
}

/// OUTSIDE ANY SPEC, a nested call is not hinted with its slot's projection either: `nothing()`'s
/// `X` was pinned to `k`'s own `s.E` and refused against the slot's `Option[T = Int64]`. Nothing
/// else fixes `X` here, and the refusal says so.
#[test]
fn a_nested_call_is_not_hinted_in_the_callees_names() {
    let src = r#"
namespace wi95s43.hint
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{none}
  sort Leaf
    sort E = ?
    entity leaf(e: E)
  end
  operation nothing[X]() -> Option[T = X] = none
  operation k(s: Leaf[E = Int64], v: Option[T = s.E]) -> Int64 = 1
  operation go() -> Int64 = k(leaf(e: 1), nothing())
end
"#;
    let errs = load_errors_of(src);
    assert_refused_naming(&errs, &["nothing.type_arg", "unconstrained"], "`nothing()` in `k`");
    assert!(
        !errs.join(" | ").contains("s.E"),
        "the refusal names no type in `k`'s names: {errs:#?}"
    );
}

/// CONTROL for where the hint stops: a CONSTRUCTOR's field type is checked as written, and a
/// rigid projection there still hints the nested call — `holder(v: nothing())` over `v: Option[T
/// = MemStore.Key]` loads and runs. With the projection test inside `nested_call_arg_hint`, which
/// both kinds of slot share, it was refused "X unconstrained" (MEASURED; found by /code-review).
#[test]
fn a_constructor_field_still_hints_a_nested_call() {
    let src = r#"
namespace wi95s43.field
  import anthill.prelude.{Int64, Bool, Option}
  import anthill.prelude.Option.{none}
  sort Storage
    sort C = ?
    sort Key = ?
    operation get(s: C, k: Key) -> Bool
  end
  sort MemStore
    entity mem(n: Int64)
    provides Storage[C = Self, Key = Int64]
    operation get(s: Self, k: Int64) -> Bool = true
  end
  sort Holder
    entity holder(v: Option[T = MemStore.Key])
  end
  operation nothing[X]() -> Option[T = X] = none
  operation go() -> Int64 =
    match holder(v: nothing())
      case holder(v: none) -> 5
      case _ -> 6
end
"#;
    assert_eq!(run_int64(src, "wi95s43.field.go"), Ok(5));
}
