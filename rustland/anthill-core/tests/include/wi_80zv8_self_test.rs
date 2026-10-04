//! WI-20261001-80ZV8 (proposal 070), stage (b) — `Self`, AND THE PROJECTION `s.Self`.
//!
//! `Self`, written inside a sort's definition, is that sort applied to its OWN parameters
//! (070 §1.2): in `sort Car` with `sort V = ?` it is `Car[V = V]`, and in a sort without
//! parameters it is the sort. The loader replaces it with the written form where a type is
//! lowered, so nothing after name resolution sees it. `s.Self` is the whole parameterized
//! type of the value `s` (§1.5); it was `s.Sort`, which is now an ordinary missing member.
//!
//! This stage ADDS the spelling and changes no reading: a bare self reference still means
//! what it meant (the tie is removed at stage (e)).
//!
//! Every row that can RUNS — an operation to its value, a relation to its answers — and the
//! rows asserting a LOAD verdict name the refusal a back-out makes disappear.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-03), each part present but disabled, over this file's 36 rows:
//!
//! 1. THE TYPE LOWERING READS `Self` (`type_expr_to_child_inner`'s `Simple` arm). 22 FAIL:
//!    the signature (the no-parameter return among them), entity-field, spec, witness, enum,
//!    secondary-entry and parameterless-sort rows, [`self_in_a_provides_binding_runs_at_one_instance`],
//!    [`self_in_a_provision_block_is_the_providing_sort`], the `requires` row and the
//!    mixed-spelling row (their members are typed `Self`), both `Self` rule-bound rows and
//!    [`a_head_typed_self_guards_its_own_carrier`] (the head's bound is then unresolved),
//!    [`self_outside_a_sort_is_refused`] (it is refused, but as an unknown name),
//!    [`self_in_a_let_annotation_is_this_instance`] and
//!    [`self_in_a_call_bracket_is_this_instance`].
//! 2. `Self[…]` IS REFUSED (that function's `Parameterized` arm). 1 FAILS:
//!    [`self_with_bindings_is_refused`].
//! 3. THE BINDING-VALUE LOWERING READS `Self` (`sort_binding_to_value`). 6 FAIL: the two
//!    `provides` rows, the two provision-block rows, the mixed-spelling row and
//!    [`self_in_a_requires_binding_is_supplied_at_the_instance`].
//! 4. THE RULE PARAMETER FORM READS `Self` (`parse_arg_is_self_type`). 1 FAILS:
//!    [`self_as_a_rule_variable_bound_answers_as_the_sort_does`] — `pick` answers nothing.
//! 5. A NAME DOOR REFUSES `Self` (`refuse_unresolved_self`). 1 FAILS:
//!    [`self_where_no_type_is_read_is_refused`] (it loads).
//! 6. A DECLARATION NAMED `Self` IS REFUSED — (a) the declarations pass 1 logs
//!    (`reserved_self_name_errors`), (b) an operation's own parameters
//!    (`refuse_reserved_self_params`), (c) an entity's fields
//!    (`register_declared_field_types`). 1 FAILS under each:
//!    [`a_declaration_named_self_is_refused`].
//! 7. THE PROJECTION IS NAMED `Self` (`project_type_member`, and the member rule's reader). 2
//!    FAIL: both projection rows.
//! 8. `Self` STOPS AT A NAMESPACE (`enclosing_sort_for_self`). 1 FAILS:
//!    [`self_outside_a_sort_is_refused`] — a plain namespace nested in a sort reads the sort.
//! 9. A HEAD TYPED `Self` GUARDS ITS CARRIER (`typed_head_guards_its_own_carrier`'s arm). 1
//!    FAILS: [`a_head_typed_self_guards_its_own_carrier`] (refused as an unguarded join).
//!
//! Every row fails under at least one part but seven, which pass with or without this ticket
//! BY DESIGN. The five named `…_written_form` are the same programs spelled `Car[V = V]` (or
//! the sort's own name), and say that `Self` is that type and no other.
//! [`a_head_typed_self_guards_its_own_carrier_controls`] says the guard was not loosened.
//! [`self_as_a_call_head_or_a_require_binding_is_refused`] pins two refusals this ticket did
//! not write: they are what keeps `Self` loud in two positions it is not read in.
//!
//! The parse-level Rust generator reads `Self` on its own (`codegen::rust::names_this_sort`);
//! its row and back-out are `codegen_test::self_generates_what_the_sorts_own_name_generates`.

use crate::common::{
    assert_refused_naming, load_errors_of as load_errors, load_kb_with, run_int64 as run_src,
    shown_rows,
};

// ── An operation's parameters and return ────────────────────────────────────

/// `mix` takes two cars and returns the second's content; `same` returns its argument.
/// `self_ty` is how the sort names its own instance, `second` the car handed to `mix`.
fn signature_program(ns: &str, self_ty: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Car
    sort V = ?
    entity car(v: V)
    operation mix(a: {self_ty}, b: {self_ty}) -> V = b.v
    operation same(a: {self_ty}) -> {self_ty} = a
  end
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40)
    Car.mix(k1, Car.same({second}))
end
"#
    )
}

/// `Self` IN A PARAMETER AND A RETURN IS THE SORT AT ITS OWN PARAMETERS: `mix(a: Self, b:
/// Self) -> V` over two `Car[V = Int64]` runs to the second's content, through `same(a:
/// Self) -> Self`.
#[test]
fn self_in_a_signature_runs_at_one_instance() {
    assert_eq!(
        run_src(&signature_program("wi80zv8.sig1", "Self", "car(v: 41)"), "wi80zv8.sig1.go"),
        Ok(41)
    );
}

/// EVERY `Self` IN ONE SIGNATURE IS THE SAME INSTANCE: a `Car[V = String]` beside a
/// `Car[V = Int64]` is refused at `mix`'s second parameter.
#[test]
fn self_in_a_signature_refuses_a_second_instance() {
    assert_refused_naming(
        &load_errors(&signature_program("wi80zv8.sig2", "Self", "car(v: \"s\")")),
        &["mix.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "`b: Self` at the instance `a` fixed",
    );
}

/// CONTROL — the same two verdicts with the type written out. Passes with or without this
/// ticket by design: it says `Self` is `Car[V = V]` and not some third thing.
#[test]
fn self_in_a_signature_is_the_written_form() {
    assert_eq!(
        run_src(
            &signature_program("wi80zv8.sig3", "Car[V = V]", "car(v: 41)"),
            "wi80zv8.sig3.go"
        ),
        Ok(41)
    );
    assert_refused_naming(
        &load_errors(&signature_program("wi80zv8.sig4", "Car[V = V]", "car(v: \"s\")")),
        &["mix.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "the written form refuses what `Self` refuses",
    );
}

/// AN OPERATION WITH NO PARAMETER OF ITS SORT MAY RETURN `Self`: nothing in the arguments
/// fixes the sort's parameter, so the call's context does — an annotation in `go`, the
/// field it is put into in `go2`. `empty() -> Self` is what the bare `-> MyList` has been.
#[test]
fn self_as_the_return_of_an_operation_with_no_parameter_of_its_sort() {
    let src = r#"
namespace wi80zv8.empty1
  import anthill.prelude.{Int64, String}
  sort MyList
    sort T = ?
    entity mnil
    entity mcons(head: T, tail: Self)
    operation empty() -> Self = mnil
    operation size(xs: Self) -> Int64 =
      match xs
        case mnil() -> 0
        case mcons(_, rest) -> 1 + size(rest)
  end
  operation go() -> Int64 =
    let xs: MyList[T = Int64] = MyList.empty()
    MyList.size(mcons(head: 7, tail: xs))
  operation go2() -> Int64 =
    MyList.size(mcons(head: 1, tail: mcons(head: 2, tail: MyList.empty())))
end
"#;
    assert_eq!(run_src(src, "wi80zv8.empty1.go"), Ok(1));
    assert_eq!(run_src(src, "wi80zv8.empty1.go2"), Ok(2));
}

// ── An entity field ─────────────────────────────────────────────────────────

fn field_program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort MyList
    sort T = ?
    entity mnil
    entity mcons(head: T, tail: Self)
    operation first(xs: Self, dflt: T) -> T =
      match xs
        case mnil() -> dflt
        case mcons(h, _) -> h
    operation second(xs: Self, dflt: T) -> T =
      match xs
        case mnil() -> dflt
        case mcons(_, rest) -> first(rest, dflt)
  end
{body}
end
"#
    )
}

/// `Self` IN AN ENTITY FIELD IS THE SORT THAT DECLARES THE ENTITY, not the entity:
/// `mcons(head: T, tail: Self)` holds a `MyList` at this list's element, so a match binds
/// `rest` at it and `second` reads the second element.
#[test]
fn self_in_an_entity_field_is_the_declaring_sort() {
    let src = field_program(
        "wi80zv8.fld1",
        r#"  operation go() -> Int64 =
    let xs: MyList[T = Int64] = mcons(head: 1, tail: mcons(head: 2, tail: mnil))
    MyList.second(xs, 0)"#,
    );
    assert_eq!(run_src(&src, "wi80zv8.fld1.go"), Ok(2));
}

/// …AND AT THIS INSTANCE: a tail of another element type is refused at the field.
#[test]
fn self_in_an_entity_field_refuses_another_instance() {
    let src = field_program(
        "wi80zv8.fld2",
        r#"  operation go() -> MyList[T = Int64] =
    mcons(head: 1, tail: mcons(head: "s", tail: mnil))"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["mcons.tail (entity-field): expected MyList[T = Int64], got MyList[T = String]"],
        "`tail: Self` at the head's element",
    );
}

// ── `provides` and `requires` bindings ──────────────────────────────────────

/// The ticket's acceptance fixture: `Car` provides `Rel` at itself twice, and `mix` runs
/// its first argument's callback on its second's content.
fn rel_program(ns: &str, self_ty: &str, second_ty: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Rel[A = {self_ty}, B = {self_ty}]
    operation mix(a: {self_ty}, b: {self_ty}) -> Int64 = match a case car(_, g) -> g(b.v)
  end
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40, f: lambda (x: Int64) -> x + 1)
    let k2: {second_ty} = {second}
    Rel.mix(k1, k2)
end
"#
    )
}

/// `Self` AS A `provides` BINDING: `provides Rel[A = Self, B = Self]` with `mix(a: Self, b:
/// Self)` runs through the spec at one instance — `g(41)` is 42.
#[test]
fn self_in_a_provides_binding_runs_at_one_instance() {
    let src = rel_program(
        "wi80zv8.rel1",
        "Self",
        "Car[V = Int64]",
        "car(v: 41, f: lambda (x: Int64) -> x + 1)",
    );
    assert_eq!(run_src(&src, "wi80zv8.rel1.go"), Ok(42));
}

/// …AND `Rel.mix` OVER TWO INSTANCES IS REFUSED AT LOAD: the binding is this instance in
/// both slots, so the call may not hand an `Int64` callback a `String`.
#[test]
fn self_in_a_provides_binding_refuses_a_second_instance() {
    let src = rel_program(
        "wi80zv8.rel2",
        "Self",
        "Car[V = String]",
        "car(v: \"s\", f: lambda (x: String) -> 9)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["mix.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "`B = Self` at the receiver's instance",
    );
}

/// CONTROL — the written binding, both verdicts. Passes with or without this ticket by
/// design (the ticket measured it on 2026-10-01).
#[test]
fn self_in_a_provides_binding_is_the_written_form() {
    let one = rel_program(
        "wi80zv8.rel3",
        "Car[V = V]",
        "Car[V = Int64]",
        "car(v: 41, f: lambda (x: Int64) -> x + 1)",
    );
    assert_eq!(run_src(&one, "wi80zv8.rel3.go"), Ok(42));
    let two = rel_program(
        "wi80zv8.rel4",
        "Car[V = V]",
        "Car[V = String]",
        "car(v: \"s\", f: lambda (x: String) -> 9)",
    );
    assert_refused_naming(
        &load_errors(&two),
        &["mix.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "the written binding refuses what `Self` refuses",
    );
}

/// THE TWO SPELLINGS MEET IN ONE SORT: a binding written `Self` beside a member typed
/// `Car[V = V]`, and the reverse. The binding lowering and the type lowering each have
/// their own canon for a parameter, and the member rule compares across them — so each
/// mixed pair must run exactly as the same-spelling pairs above do.
#[test]
fn self_and_the_written_form_meet_in_one_sort() {
    let ok = "car(v: 41, f: lambda (x: Int64) -> x + 1)";
    for (ns, binding, member) in [
        ("wi80zv8.mix1", "Self", "Car[V = V]"),
        ("wi80zv8.mix2", "Car[V = V]", "Self"),
    ] {
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, f: (x: V) -> Int64)
    provides Rel[A = {binding}, B = {binding}]
    operation mix(a: {member}, b: {member}) -> Int64 = match a case car(_, g) -> g(b.v)
  end
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40, f: lambda (x: Int64) -> x + 1)
    let k2: Car[V = Int64] = {ok}
    Rel.mix(k1, k2)
end
"#
        );
        assert_eq!(
            run_src(&src, &format!("{ns}.go")),
            Ok(42),
            "binding `{binding}`, member `{member}`"
        );
    }
}

/// `Self` AS A `requires` BINDING: `Car requires Show2[X = Self]`, supplied by a witness at
/// `Car[V = Int64]`; `shown` dispatches through it.
#[test]
fn self_in_a_requires_binding_is_supplied_at_the_instance() {
    let src = r#"
namespace wi80zv8.req1
  import anthill.prelude.{Int64, String}
  sort Show2
    sort X = ?
    operation show(x: X) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V)
    requires Show2[X = Self]
    operation shown(c: Self) -> Int64 = Show2.show(c)
  end
  sort CarShow
    provides Show2[X = Car[V = Int64]]
    operation show(x: Car[V = Int64]) -> Int64 = 7
  end
  operation go() -> Int64 =
    let k: Car[V = Int64] = car(v: 1)
    Car.shown(k)
end
"#;
    assert_eq!(run_src(src, "wi80zv8.req1.go"), Ok(7));
}

// ── Where `Self` is resolved: a spec, a witness, an enum, a secondary entry ──

/// IN A SPEC `Self` IS THE SPEC, and in its carrier the carrier: `Feed.next(s: Self) ->
/// Self` is implemented by `MyList.next(xs: Self) -> Self`, the member rule matching the
/// two receivers by their sorts. The call through the spec runs the carrier's members.
#[test]
fn self_in_a_spec_is_the_spec_and_in_its_carrier_the_carrier() {
    let src = r#"
namespace wi80zv8.spec1
  import anthill.prelude.{Int64, String}
  sort Feed
    sort T = ?
    operation next(s: Self) -> Self
    operation peek(s: Self, dflt: T) -> T
  end
  sort MyList
    sort T = ?
    entity mnil
    entity mcons(head: T, tail: Self)
    provides Feed[T = T]
    operation next(xs: Self) -> Self =
      match xs
        case mnil() -> xs
        case mcons(_, rest) -> rest
    operation peek(xs: Self, dflt: T) -> T =
      match xs
        case mnil() -> dflt
        case mcons(h, _) -> h
  end
  operation go() -> Int64 =
    let xs: MyList[T = Int64] = mcons(head: 1, tail: mcons(head: 2, tail: mnil))
    Feed.peek(Feed.next(xs), 0)
end
"#;
    assert_eq!(run_src(src, "wi80zv8.spec1.go"), Ok(2));
}

fn witness_program(ns: &str, ret: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Cmp
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort BoxCmp
    sort E = ?
    entity bc(e: E)
    provides Cmp[T = Box[T = E]]
    operation cmp(a: Box[T = E], b: Box[T = E]) -> Int64 = 5
    operation again(w: Self) -> Self = w
    operation tag(w: Self) -> Int64 = 3
  end
  operation keep() -> {ret} = BoxCmp.again(bc(e: 1))
  operation go() -> Int64 = BoxCmp.tag(BoxCmp.again(bc(e: 1)))
end
"#
    )
}

/// IN A WITNESS `Self` IS THE WITNESS, not the sort it provides for: `BoxCmp` supplies
/// `Cmp` for `Box`, and its `again(w: Self) -> Self` returns a `BoxCmp[E = Int64]`.
#[test]
fn self_in_a_witness_is_the_witness() {
    let src = witness_program("wi80zv8.wit1", "BoxCmp[E = Int64]");
    assert_eq!(run_src(&src, "wi80zv8.wit1.go"), Ok(3));
}

/// …so declaring that result as the CARRIER is refused.
#[test]
fn self_in_a_witness_is_not_the_carrier() {
    assert_refused_naming(
        &load_errors(&witness_program("wi80zv8.wit2", "Box[T = Int64]")),
        &["keep.return (op-return): expected Box[T = Int64], got BoxCmp[E = Int64]"],
        "`Self` in a witness is the witness sort",
    );
}

fn provision_block_program(ns: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Pairing
    sort A = ?
    sort B = ?
    operation right(a: A, b: B) -> Int64
  end
  sort Box
    sort V = ?
    entity box(v: V, f: (x: V) -> Int64)
    provides Pairing[A = Self, B = Self] where
      operation right(a: Self, b: Self) -> Int64 = match a case box(_, g) -> g(b.v)
    end
  end
  operation go() -> Int64 =
    let k1: Box[V = Int64] = box(v: 1, f: lambda (x: Int64) -> x + 8)
    Pairing.right(k1, {second})
end
"#
    )
}

/// IN A PROVISION BLOCK (proposal 066) `Self` IS THE PROVIDING SORT — the block is written
/// inside it — in the clause's bindings and in the member alike.
#[test]
fn self_in_a_provision_block_is_the_providing_sort() {
    let src = provision_block_program(
        "wi80zv8.blk1",
        "box(v: 1, f: lambda (x: Int64) -> x)",
    );
    assert_eq!(run_src(&src, "wi80zv8.blk1.go"), Ok(9));
}

/// …at ONE instance.
#[test]
fn self_in_a_provision_block_refuses_a_second_instance() {
    let src = provision_block_program(
        "wi80zv8.blk2",
        "box(v: \"s\", f: lambda (x: String) -> 0)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["right.b (op-arg): expected Box[V = Int64], got Box[V = String]"],
        "`b: Self` in the block is the provider's instance",
    );
}

/// IN AN `enum` BODY `Self` is the enum at its own parameter: `orElse(o: Self, other:
/// Self) -> Self` keeps the element type through to `get`.
#[test]
fn self_in_an_enum_body_is_the_enum() {
    let src = r#"
namespace wi80zv8.enum1
  import anthill.prelude.{Int64, String}
  enum Opt
    sort T = ?
    entity nothing
    entity just(value: T)
    operation orElse(o: Self, other: Self) -> Self =
      match o
        case nothing() -> other
        case just(_) -> o
    operation get(o: Self, dflt: T) -> T =
      match o
        case nothing() -> dflt
        case just(v) -> v
  end
  operation go() -> Int64 =
    let a: Opt[T = Int64] = nothing
    let b: Opt[T = Int64] = just(value: 7)
    Opt.get(Opt.orElse(a, b), 0)
end
"#;
    assert_eq!(run_src(src, "wi80zv8.enum1.go"), Ok(7));
}

fn secondary_entry_program(ns: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Car
    sort V = ?
    entity car(v: V)
  end
  namespace Car
    operation pick(a: Self, b: Self) -> V = b.v
  end
  operation go() -> Int64 =
    let k1: Car[V = Int64] = car(v: 40)
    Car.pick(k1, {second})
end
"#
    )
}

/// IN A SECONDARY ENTRY (`namespace Car` at the sort's address, proposal 059) `Self` is
/// that sort: the entry is scoped by the sort's parameters, and its operation is the
/// sort's member.
#[test]
fn self_in_a_secondary_entry_is_the_sort_at_that_address() {
    let src = secondary_entry_program("wi80zv8.sec1", "car(v: 41)");
    assert_eq!(run_src(&src, "wi80zv8.sec1.go"), Ok(41));
}

/// …at ONE instance.
#[test]
fn self_in_a_secondary_entry_refuses_a_second_instance() {
    assert_refused_naming(
        &load_errors(&secondary_entry_program("wi80zv8.sec2", "car(v: \"s\")")),
        &["pick.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "`b: Self` in the entry is the sort's instance",
    );
}

/// IN A SORT WITHOUT PARAMETERS `Self` IS THE SORT, and it nests like any type: `id(t:
/// Self) -> Self` over `Tag`, and a `Tree` holding a `List[T = Self]` of its own kind.
#[test]
fn self_without_parameters_and_self_nested_in_another_type() {
    let src = r#"
namespace wi80zv8.plain1
  import anthill.prelude.{Int64, String, List}
  sort Tag
    entity red
    entity green
    operation id(t: Self) -> Self = t
    operation code(t: Self) -> Int64 =
      match t
        case red() -> 1
        case green() -> 2
  end
  sort Tree
    sort T = ?
    entity leaf(v: T)
    entity node(kids: List[T = Self])
    operation size(t: Self) -> Int64 =
      match t
        case leaf(_) -> 1
        case node(ks) -> List.length(ks)
  end
  operation go() -> Int64 =
    let t: Tree[T = Int64] = node(kids: [leaf(v: 1), leaf(v: 2), leaf(v: 3)])
    Tag.code(Tag.id(green)) + Tree.size(t)
end
"#;
    assert_eq!(run_src(src, "wi80zv8.plain1.go"), Ok(5));
}

// ── An annotation inside a body ─────────────────────────────────────────────

fn let_annotation_program(ns: &str, self_ty: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Car
    sort V = ?
    entity car(v: V)
    operation keep(a: {self_ty}) -> V =
      let same: {self_ty} = a
      same.v
  end
  operation go() -> Int64 = Car.keep(car(v: 5))
end
"#
    )
}

/// `Self` IN A `let` ANNOTATION IS THIS INSTANCE: `let same: Self = a` binds `same` at the
/// operation's own instance, so `same.v` is a `V`. It waited on WI-20261001-89WZR — a `let`
/// annotation naming a type parameter in scope was a different type from the parameter, so
/// this line was refused, and so was the same line written `Car[V = V]`.
#[test]
fn self_in_a_let_annotation_is_this_instance() {
    assert_eq!(
        run_src(&let_annotation_program("wi80zv8.let1", "Self"), "wi80zv8.let1.go"),
        Ok(5)
    );
}

/// CONTROL — the written form of the same line. It passes with or without THIS ticket by
/// design (it is WI-20261001-89WZR's row, driven there as well).
#[test]
fn self_in_a_let_annotation_is_the_written_form() {
    assert_eq!(
        run_src(
            &let_annotation_program("wi80zv8.let2", "Car[V = V]"),
            "wi80zv8.let2.go"
        ),
        Ok(5)
    );
}

/// `Self` IN A CALL'S BRACKET IS THIS INSTANCE: `id[A = Self](a)` runs, and the same bracket
/// over a `Car[V = Int64]` argument is refused naming this instance — the bracket holds the
/// argument to it. That second half is WI-20261001-89WZR's (a bracket's value is read at the
/// body's own parameters): read as written it LOADED, the argument pinning `V`.
#[test]
fn self_in_a_call_bracket_is_this_instance() {
    let src = |ns: &str, arg: &str, ret: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  operation id[A](x: A) -> A = x
  sort Car
    sort V = ?
    entity car(v: V)
    operation keep(a: Self, o: Car[V = Int64]) -> {ret} = id[A = Self]({arg})
  end
  operation go() -> Int64 = Car.keep(car(v: 5), car(v: 6)).v
end
"#
        )
    };
    assert_eq!(
        run_src(&src("wi80zv8.br1", "a", "Self"), "wi80zv8.br1.go"),
        Ok(5)
    );
    assert_refused_naming(
        &load_errors(&src("wi80zv8.br2", "o", "Car[V = Int64]")),
        &["id.x (op-arg): expected Car[V = ?V], got Car[V = Int64]"],
        "`id[A = Self](o)` with `o: Car[V = Int64]`",
    );
}

// ── A rule-variable bound ───────────────────────────────────────────────────

/// One sort, one relation over its values, bounded by `bound` in the `?x: T` form and in
/// the parameter form `c: T`.
fn rule_bound_program(ns: &str, bound: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Tag
    entity red
    entity green
    rule item(?x) :- ?x = red()
    rule liked(?x: {bound}) :- item(?x)
    rule pick(c: {bound}) :- item(c)
  end
end
"#
    )
}

/// `Self` AS A RULE-VARIABLE BOUND, in both spellings of a typed column. The parameter
/// form is the one that was silently wrong: `rule pick(c: Self) :- item(c)` read `c` as a
/// label over an unknown constant, loaded clean and answered NOTHING (MEASURED), where
/// `c: Tag` answers `red`.
#[test]
fn self_as_a_rule_variable_bound_answers_as_the_sort_does() {
    let mut kb = load_kb_with(&rule_bound_program("wi80zv8.rule1", "Self"));
    let red = vec![("red".to_owned(), true)];
    assert_eq!(shown_rows(&mut kb, "wi80zv8.rule1.Tag.liked"), red, "`?x: Self`");
    assert_eq!(shown_rows(&mut kb, "wi80zv8.rule1.Tag.pick"), red, "`c: Self`");
}

/// CONTROL — the sort's own name in the same two positions. Passes with or without this
/// ticket by design.
#[test]
fn self_as_a_rule_variable_bound_is_the_written_form() {
    let mut kb = load_kb_with(&rule_bound_program("wi80zv8.rule2", "Tag"));
    let red = vec![("red".to_owned(), true)];
    assert_eq!(shown_rows(&mut kb, "wi80zv8.rule2.Tag.liked"), red);
    assert_eq!(shown_rows(&mut kb, "wi80zv8.rule2.Tag.pick"), red);
}

fn rule_tie_program(ns: &str, bound: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Box
    sort T = ?
    entity box(v: T)
    rule twin(?x: {bound}, ?y: {bound}) :- ?y = ?x
  end
  rule both(1) :- Box.twin(box(v: 1), box(v: 1))
  rule mixed(1) :- Box.twin(box(v: 1), box(v: "s"))
end
"#
    )
}

/// TWO `Self` BOUNDS OF ONE RULE ARE ONE INSTANCE, as in a signature: `twin(?x: Self, ?y:
/// Self)` answers for two `Int64` boxes and has no answer for an `Int64` box beside a
/// `String` one — the first column pins the parameter and the second is checked against it.
#[test]
fn self_bounds_of_one_rule_are_one_instance() {
    let mut kb = load_kb_with(&rule_tie_program("wi80zv8.rule3", "Self"));
    assert_eq!(
        shown_rows(&mut kb, "wi80zv8.rule3.both"),
        vec![("1".to_owned(), true)],
        "two boxes of one element type"
    );
    assert_eq!(
        shown_rows(&mut kb, "wi80zv8.rule3.mixed"),
        Vec::<(String, bool)>::new(),
        "an Int64 box beside a String box"
    );
}

/// CONTROL — the written `Box[T = T]` in both bounds, the same two answers. Passes with or
/// without this ticket by design.
#[test]
fn self_bounds_of_one_rule_are_the_written_form() {
    let mut kb = load_kb_with(&rule_tie_program("wi80zv8.rule4", "Box[T = T]"));
    assert_eq!(shown_rows(&mut kb, "wi80zv8.rule4.both"), vec![("1".to_owned(), true)]);
    assert_eq!(shown_rows(&mut kb, "wi80zv8.rule4.mixed"), Vec::<(String, bool)>::new());
}

fn guarded_join_program(ns: &str, bound: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Spec
    rule p(?x)
    rule p(0) :- true
  end
  sort A
    entity a1
    requires {ns}.Spec
    rule p(?x: {bound}) :- ?x = a1()
  end
end
"#
    )
}

/// A HEAD TYPED `Self` GUARDS ITS OWN CARRIER, as one typed with the sort's name does: the
/// clause may then join the predicate a `requires` exposes (the C666A rule). The check
/// reads the annotation's NAME, and `Self` resolves to nothing — MEASURED before its arm:
/// `rule p(?x: Self)` was refused as "the unguarded rule head `p`" where `rule p(?x: A)`
/// loads.
#[test]
fn a_head_typed_self_guards_its_own_carrier() {
    let errs = load_errors(&guarded_join_program("wi80zv8.guard1", "Self"));
    assert!(errs.is_empty(), "`rule p(?x: Self)` joins as `?x: A` does, got: {errs:?}");
}

/// CONTROL — the sort's own name loads, and NO annotation is still refused: the row above
/// is about `Self`, not about the guard having been loosened. Both verdicts pass with or
/// without this ticket by design.
#[test]
fn a_head_typed_self_guards_its_own_carrier_controls() {
    let named = load_errors(&guarded_join_program("wi80zv8.guard2", "A"));
    assert!(named.is_empty(), "`rule p(?x: A)` loads, got: {named:?}");
    let unguarded = r#"
namespace wi80zv8.guard3
  import anthill.prelude.{Int64}
  sort Spec
    rule p(?x)
    rule p(0) :- true
  end
  sort A
    entity a1
    requires wi80zv8.guard3.Spec
    rule p(1) :- true
  end
end
"#;
    assert_refused_naming(
        &load_errors(unguarded),
        &["the unguarded rule head `p`"],
        "a head with no annotation",
    );
}

// ── Where `Self` means nothing ──────────────────────────────────────────────

/// OUTSIDE A SORT `Self` IS A LOAD ERROR: a namespace-level operation has no enclosing
/// sort, and a plain namespace nested in a sort body is not the sort (its operations are
/// not the sort's members).
#[test]
fn self_outside_a_sort_is_refused() {
    let top = r#"
namespace wi80zv8.out1
  import anthill.prelude.{Int64}
  operation outside(x: Self) -> Int64 = 1
end
"#;
    assert_refused_naming(
        &load_errors(top),
        &["`Self` names the sort it is written in", "not written inside a sort"],
        "a namespace-level operation",
    );
    let nested = r#"
namespace wi80zv8.out2
  import anthill.prelude.{Int64}
  sort Car
    sort V = ?
    entity car(v: V)
    namespace helpers
      operation pick(a: Self) -> Int64 = 1
    end
  end
end
"#;
    assert_refused_naming(
        &load_errors(nested),
        &["`Self` names the sort it is written in", "not written inside a sort"],
        "a plain namespace nested in a sort body",
    );
}

/// `Self` TAKES NO BINDINGS: it is one instance, the sort at its own parameters; another
/// is written with the sort's name, which the refusal offers.
#[test]
fn self_with_bindings_is_refused() {
    let src = r#"
namespace wi80zv8.bind1
  import anthill.prelude.{Int64}
  sort Car
    sort V = ?
    entity car(v: V)
    operation narrow(a: Self[V = Int64]) -> Int64 = 1
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["`Self` takes no bindings", "`Car[…]`"],
        "`Self[V = Int64]`",
    );
}

/// `Self` IS RESERVED: no sort, type parameter, entity, entity field, operation, operation
/// type parameter or operation parameter may take the name. Each is refused naming what it
/// is. (A field would give `x.Self` two readings: the field, and the whole-type projection.)
#[test]
fn a_declaration_named_self_is_refused() {
    let reserved = "`Self` is reserved";
    for (ns, decl, what) in [
        ("d1", "sort Self\n    entity a\n  end", "no sort may be called `Self`"),
        (
            "d2",
            "sort Holder\n    sort Self = ?\n    entity h(v: Int64)\n  end",
            "no sort may be called `Self`",
        ),
        (
            "d3",
            "sort Other\n    entity Self\n  end",
            "no entity may be called `Self`",
        ),
        (
            "d4",
            "sort Other\n    entity o\n    operation Self(x: Int64) -> Int64 = x\n  end",
            "no operation may be called `Self`",
        ),
        (
            "d5",
            "operation gen[Self](x: Int64) -> Int64 = x",
            "no type parameter may be called `Self`",
        ),
        (
            "d6",
            "operation val(Self: Int64) -> Int64 = 1",
            "no parameter may be called `Self`",
        ),
        (
            "d7",
            "entity Rec(Self: Int64)",
            "no field may be called `Self`",
        ),
    ] {
        let src = format!(
            "\nnamespace wi80zv8.{ns}\n  import anthill.prelude.{{Int64}}\n  {decl}\nend\n"
        );
        assert_refused_naming(&load_errors(&src), &[reserved, what], decl);
    }
}

/// WHERE NOTHING READS A TYPE, `Self` IS REFUSED RATHER THAN INTERNED: as a term it used to
/// become an unknown constant of that name and load clean.
#[test]
fn self_where_no_type_is_read_is_refused() {
    let src = r#"
namespace wi80zv8.term1
  import anthill.prelude.{Int64}
  sort Tag
    entity red
    rule weird(?x) :- ?x = Self
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["`Self` is a type", "It means nothing here"],
        "`Self` as a term",
    );
}

/// A QUALIFIED CALL'S HEAD AND A `require[…]` BINDING ARE NOT TYPE POSITIONS `Self` IS READ
/// IN: both are refused by those positions' own unknown-name refusals, not read as the sort.
#[test]
fn self_as_a_call_head_or_a_require_binding_is_refused() {
    let head = r#"
namespace wi80zv8.head1
  import anthill.prelude.{Int64}
  sort Car
    sort V = ?
    entity car(v: V)
    operation same(a: Self) -> Self = a
    operation twice(a: Self) -> Self = Self.same(a)
  end
end
"#;
    assert_refused_naming(
        &load_errors(head),
        &["Self.same", "unknown functor"],
        "`Self.same(a)`",
    );
    let require = r#"
namespace wi80zv8.reqgoal1
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Tag
    entity red
    rule viaDict(?d) :- ?d = require[Desc[T = Self]]
  end
end
"#;
    assert_refused_naming(
        &load_errors(require),
        &["`Self` in it names neither a sort"],
        "`require[Desc[T = Self]]`",
    );
}

// ── The projection `s.Self` ─────────────────────────────────────────────────

fn projection_program(ns: &str, member: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  operation echo(l: List) -> l.{member} = l
  operation go() -> Int64 =
    let xs: List[T = Int64] = [4, 5, 6]
    let ys: List[T = Int64] = echo(xs)
    List.length(ys)
end
"#
    )
}

/// `s.Self` IS THE VALUE'S WHOLE PARAMETERIZED TYPE, outside any sort: `echo(l: List) ->
/// l.Self` returns a `List[T = Int64]` for one.
#[test]
fn the_self_projection_is_the_values_whole_type() {
    assert_eq!(
        run_src(&projection_program("wi80zv8.proj1", "Self"), "wi80zv8.proj1.go"),
        Ok(3)
    );
}

/// `s.Sort` IS AN ORDINARY MISSING MEMBER: the rename has no second spelling.
#[test]
fn the_sort_projection_is_an_ordinary_missing_member() {
    assert_refused_naming(
        &load_errors(&projection_program("wi80zv8.proj2", "Sort")),
        &["has no member 'Sort'"],
        "`l.Sort`",
    );
}
