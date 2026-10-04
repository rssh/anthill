//! WI-20261001-80ZV8 (proposal 070), stage (e) — THE IMPLICIT TIE IS REMOVED.
//!
//! Until this stage a reference to the enclosing sort that left a slot out was read as THIS
//! instance by a family of readers, each on its own side of the typer: a load-time pass wrote
//! the sort's parameter into the slot (`elaborate_self_ties`, WI-1082), a body filled it with
//! the enclosing sort's rigid, a call left it for the unifier's canonical channel
//! (`unify_parameterized_with_sort_ref`) and checked the result (`enforce_member_tie`,
//! WI-374), the slot expansion skipped the callee's own sort, the member rule and the two call
//! binders read a provision's bare carrier name at the carrier's own parameters, and the
//! derived domain closed a bare recursive field on the sort's own head. Stage (d) had the
//! LOADER write a `?` into every such slot, so that none of them met one.
//!
//! All of it is deleted, the loader's `?` with it: a slot left out is open on the enclosing
//! sort as on any other, and this instance is `Self`.
//!
//! ── WHAT A DELETION CAN BE MEASURED BY ───────────────────────────────────────
//!
//! The readers are gone, so they cannot be "backed out". Three measurements stand in their
//! place (2026-10-04). The second and third are on a temporary binary of 45 suites — every
//! `wi_80zv8_*` and `wi_0rp29_*` file, and the suites of the tickets the readers came from
//! (WI-374, 424, 1056, 1059, 1061, 1063, 1078, 1082, 1083, …); 970 rows before this file:
//!
//! 1. BEFORE ANYTHING WAS DELETED, WHAT STILL REACHED EACH READER — a probe at the point
//!    where each one ACTS, logged per test over the whole workspace (8491 rows). Never
//!    reached: the load-time pass (signature and field halves), the body's and the
//!    declaration's self fill, the member tie's refusal, the top-level self exception of the
//!    slot expansion, and the member rule's reading of a bare carrier name. Still reached:
//!    the canonical channel, in every row, through a constructor's bare parent type; the
//!    call binders' this-instance arms, by bindings written `Self` (35 rows) — these are
//!    how `T = Self` is held to the receiver and STAY, without the bare reading; the deep
//!    expansion's self exception (3 rows); and the loader's `?` (16 rows, each a fixture
//!    that writes its own sort bare).
//! 2. THE CHANNEL OFF, a constructor's own expected type read at the sort's own parameters
//!    instead (`check_constructor_iter`). 10 rows of the workspace FAILED, all through the
//!    one other reader of a constructor's bare parent — the hint a constructor's argument is
//!    typed from (`ctor_field_expected`): `wi_5nszy_arrow_reaches_a_nested_bare_name_test`
//!    (7), `wi_2tmb5 the_arrow_slot_and_the_polymorphic_slot_agree`, `typer_capability_matrix
//!    a_bare_operation_name_across_its_routes`, `wi_jsfhg
//!    a_variant_type_nested_in_a_parameterized_type_is_inhabited`. Those are the rows that
//!    fail if the hint goes back to the bare name (part 6 below).
//! 3. ON THE COMMITTED TREE, THE LOADER'S `?` ALONE SWITCHED OFF — the readers still there,
//!    and nothing between them and a slot left out. 6 of the 970 rows FAIL: `wi1078
//!    a_self_sort_return_that_leaves_a_slot_open_is_opened_at_the_consumer`, `wi836
//!    the_bare_sort_ref_spelling_is_any_instance_and_its_result_is_opened`,
//!    `wi_0rp29_call_binding an_alias_of_the_carrier_in_a_binding_is_the_carrier`, and three
//!    of `wi_80zv8_bare_own_sort` —
//!    `a_bare_reference_to_the_enclosing_sort_is_the_sort_at_a_wildcard`,
//!    `a_partial_reference_and_an_alias_leave_the_rest_to_a_wildcard`,
//!    `what_the_carrier_rule_leaves_alone_loads_and_runs` — and 5 of this file's 6, every
//!    one but the `Self` control. Those eleven say the readers were the tie, and that the
//!    `?` was all that stood between a program and them. On the committed tree as it
//!    stands, the `?` written, 4 of this file fail: [`a_bare_carrier_binding_is_any_
//!    instance_and_still_the_carrier`] on what the open slot prints,
//!    [`a_recursive_field_written_bare_has_no_derived_domain_and_self_has`], and the two
//!    rows about an alias, each by a reading that tree does not have — an alias that writes
//!    the `?` or holds the sort, to the carrier rule; a witness's alias of the carrier, to
//!    the call binder.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! What this stage ADDED can be backed out. MEASURED (2026-10-04, on the tree this file is
//! committed with), each part present but disabled, on a temporary binary of 52 suites and
//! 1038 rows — the 45 above and the suites of measurement 2's ten rows:
//!
//! 1. THE CARRIER'S BARE NAME IN ITS OWN PROVISION IS BOUND AT THE CALL (typing/carrier.rs
//!    `bind_spec_params_from_carrier_param`; the name left to the late pass again). 2 FAIL:
//!    [`a_bare_carrier_binding_is_any_instance_and_still_the_carrier`] and
//!    `wi_0rp29_call_binding an_alias_of_the_carrier_in_a_binding_is_the_carrier`. With the
//!    arm asking for the carrier's OWN name, an alias unread, as it did for a witness's
//!    provision before this stage: 3 FAIL, those two and
//!    [`a_witness_binding_an_alias_of_the_carrier_holds_its_argument_to_it`].
//! 2. THE DERIVED DOMAIN DECLINES A FIELD NAMING ITS OWN SORT BARE (fill_derive.rs; the
//!    name repaired to the sort's self type again). 1 FAILS:
//!    [`a_recursive_field_written_bare_has_no_derived_domain_and_self_has`].
//! 3. THIS INSTANCE IS THE CARRIER WITH EVERY PARAMETER WRITTEN (typing/signature.rs
//!    `is_this_instance`; a reference that leaves a slot out counted again). 2 FAIL, the
//!    two of part 1.
//! 4. THE CARRIER RULE READS A PARAMETER'S TYPE THROUGH ITS ALIASES (typing/sorts.rs
//!    `check_sort_parameter_carriers`; the type read as written). 1 FAILS:
//!    [`a_sort_parameter_beside_an_alias_of_the_sort_needs_a_carrier`]. That row also fails
//!    with the rule not run, honouring no carrier, or reading a use off variables only —
//!    `wi_80zv8_bare_own_sort_test`'s part 8, where the rule's own ledger is.
//! 5. A BINDING WRITTEN AT THE CARRIER'S OWN PARAMETERS IS HELD TO THE RECEIVER
//!    (typing/signature.rs `this_instance_binding_at` answering none) — NOT part of the
//!    tie, and this is the measurement that says so. 6 FAIL: `wi_0rp29_call_binding
//!    a_nested_carrier_binding_holds_a_self_receiver_call_to_this_instance`,
//!    `wi_0rp29_member_rule
//!    a_binding_naming_the_carrier_holds_a_self_receiver_call_to_this_instance`,
//!    `wi_0rp29_review9`'s `a_lambda_hint_reads_a_ground_receivers_binding_first`,
//!    `a_lambda_hint_reads_the_receivers_binding_first` and
//!    `a_lambda_reads_a_wider_siblings_field_by_the_receivers_binding`, and
//!    `wi_80zv8_written_wildcard a_provision_at_self_is_the_receivers_instance`. None of
//!    this file.
//! 6. THE HINT A CONSTRUCTOR'S ARGUMENT IS TYPED FROM READS THE SORT AT ITS OWN PARAMETERS
//!    (typing/arg_hints.rs `ctor_field_expected`; the bare name again). 10 FAIL,
//!    measurement 2's rows; none of this file.
//!
//! NOT MEASURED BY ANY ROW, and said so: that a constructor meets its own expected type at
//! the sort's own parameters (typing/constructor.rs `check_constructor_iter`). With the bare
//! name back there no row of the 52 suites fails — the fields have bound the parameters by
//! the time the expectation is met — and a row written to tell the two apart passed both
//! ways and was dropped. It is kept as the reading the hint beside it has to agree with.
//!
//! Two rows pass under every part, by design.
//! [`a_slot_left_out_is_open_in_a_parameter_a_body_and_a_return`] is measurement 3's row:
//! nothing is left on this tree to turn it round. [`a_carrier_binding_written_self_is_this_
//! instance`] is the control of the row above it, and passes on every tree measured.
//!
//! Every row that can RUNS and names its value; a row about a refusal names what it prints.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// `Car provides Rel[A = Self, B = {binding}]`, with a member that takes any `Car` second, and
/// `Rel.mix(x, {second})` over an `Int64` car `x` and a `String` car `y`.
fn carrier_binding_program(ns: &str, binding: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
    provides Rel[A = Self, B = {binding}]
    operation mix[W](a: Self, b: Car[V = W]) -> Int64 = b.n + 1
  end
  sort MyCar = Car
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1, n: 1)
    let y: Car[V = String] = car(v: "s", n: 6)
    Rel.mix(x, {second})
end
"#
    )
}

/// THE CARRIER'S BARE NAME IN ITS OWN PROVISION IS ANY INSTANCE — AND STILL A `Car`. Behind
/// `B = Car` a second instance runs (6 + 1), and an `Int64` is refused by name: `B` is bound
/// at the call to the carrier at a slot of its own. The written `?` and the alias say the
/// same; only what the open slot prints differs (`?V` for one left out, `?_` for one
/// written).
///
/// The loader used to write the `?` into the bare name, which made it the written spelling.
/// With nothing written the binder read the bare name as a ref-shaped leaf and left it for
/// its late pass — by which time the argument had bound `B` — and `Rel.mix(x, 5)` LOADED
/// (MEASURED, before the binder bound the carrier's name in its own provision as it does in
/// a witness's).
#[test]
fn a_bare_carrier_binding_is_any_instance_and_still_the_carrier() {
    for (n, binding, open) in [
        ("b1", "Car", "?V"),
        ("b2", "MyCar", "?V"),
        ("b3", "Car[V = ?]", "?_"),
    ] {
        let refused = carrier_binding_program(&format!("wi80zv8e.{n}x"), binding, "5");
        assert_refused_naming(
            &load_errors(&refused),
            &[&format!("mix.b (op-arg): expected Car[V = {open}], got Int64")],
            binding,
        );
        let ns = format!("wi80zv8e.{n}y");
        assert_eq!(
            run_src(&carrier_binding_program(&ns, binding, "y"), &format!("{ns}.go")),
            Ok(7),
            "{binding}: a second instance"
        );
    }
}

/// CONTROL — `B = Self` IS THIS INSTANCE: the second instance is refused, and the same
/// instance runs. It is what `B = Car` must stay different from. Passes with or without this
/// stage and under every back-out of the header (MEASURED), by design: what the call binders
/// make of a binding written at the carrier's own parameters (`this_instance_binding_at`) is
/// held by six other rows (the header's part 5), and this program reads the same without it.
#[test]
fn a_carrier_binding_written_self_is_this_instance() {
    let two = carrier_binding_program("wi80zv8e.s1", "Self", "y");
    assert_refused_naming(
        &load_errors(&two),
        &["mix.b (op-arg): expected Car[V = Int64], got Car[V = String]"],
        "a second instance behind `B = Self`",
    );
    let one = carrier_binding_program("wi80zv8e.s2", "Self", "x");
    assert_eq!(run_src(&one, "wi80zv8e.s2.go"), Ok(2));
}

/// …AND IN A WITNESS'S PROVISION AN ALIAS OF THE CARRIER IS THE CARRIER TOO. The binder's arm
/// for a carrier's bare name asked whether the binding IS the carrier's own name, so `B =
/// MyCar` in a witness was a ref-shaped leaf of another name, left to the late pass — and
/// `Rel.mix(x, 5)` LOADED there on the committed tree (MEASURED) while `B = Car` beside it
/// was refused. One arm reads both provisions now, through the alias.
///
/// CONTROL: a second instance of the carrier runs behind either spelling (6 + 1).
#[test]
fn a_witness_binding_an_alias_of_the_carrier_holds_its_argument_to_it() {
    let program = |ns: &str, binding: &str, second: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Rel
    sort A = ?
    sort B = ?
    operation mix(a: A, b: B) -> Int64
  end
  sort Car
    sort V = ?
    entity car(v: V, n: Int64)
  end
  sort MyCar = Car
  sort CarRel
    provides Rel[A = Car, B = {binding}]
    operation mix[X, Y](a: Car[V = X], b: Car[V = Y]) -> Int64 = b.n + 1
  end
  operation go() -> Int64 =
    let x: Car[V = Int64] = car(v: 1, n: 1)
    let y: Car[V = String] = car(v: "s", n: 6)
    Rel.mix(x, {second})
end
"#
        )
    };
    for (n, binding) in [("w1", "Car"), ("w2", "MyCar")] {
        assert_refused_naming(
            &load_errors(&program(&format!("wi80zv8e.{n}x"), binding, "5")),
            &["mix.b (op-arg): expected Car[V = ?V], got Int64"],
            binding,
        );
        let ns = format!("wi80zv8e.{n}y");
        assert_eq!(run_src(&program(&ns, binding, "y"), &format!("{ns}.go")), Ok(7), "{binding}");
    }
}

/// `sort Chain` with a recursive field typed `next`, a two-colour element sort, and `rest`.
fn chain_program(ns: &str, next: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Colour
    entity red
    entity green
  end
  sort Chain
    sort T = ?
    entity stop
    entity link(item: T, next: {next})
  end
{rest}
end
"#
    )
}

/// THE DERIVED DOMAIN READS A BARE RECURSIVE FIELD AS THE TYPER DOES. `link(item: T, next:
/// Chain)` holds a tail of ANY element type, so `Chain` has no element domain to fill and its
/// domain is declined, saying why and naming `Self`; written `next: Self` the recursion
/// closes and a typed head enumerates — two cells over two colours, four chains.
///
/// The derivation used to repair the sort's own bare name to its self type ("a list of the
/// SAME elements": the tie, on the rule side), which the loader's `?` had been hiding.
#[test]
fn a_recursive_field_written_bare_has_no_derived_domain_and_self_has() {
    let bare = crate::common::load_kb_with(&chain_program("wi80zv8e.d1", "Chain", ""));
    let chain = bare.try_resolve_symbol("wi80zv8e.d1.Chain").unwrap();
    assert!(!bare.has_sort_domain(chain));
    let why = bare.sort_domain_decline_reason(chain).unwrap_or_default();
    assert!(
        why.contains("no type arguments") && why.contains("`Self` is this one"),
        "the decline should say the field is bare and offer `Self`: {why}"
    );
    // The control: a sort in the same file with no such field derives.
    let colour = bare.try_resolve_symbol("wi80zv8e.d1.Colour").unwrap();
    assert!(bare.has_sort_domain(colour));

    let mut tied = crate::common::load_kb_with(&chain_program(
        "wi80zv8e.d2",
        "Self",
        "  rule two(?c: Chain[T = Colour]) :- ?c <=> link(?, link(?, stop()))",
    ));
    let chain = tied.try_resolve_symbol("wi80zv8e.d2.Chain").unwrap();
    assert!(tied.has_sort_domain(chain));
    let goal = crate::common::query_pattern_term(&mut tied, "wi80zv8e.d2.two(?c)");
    let definite = tied
        .resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count();
    assert_eq!(definite, 4);
}

/// `sort Pair` with `get` for its one operation, and four aliases: of the sort, of the sort
/// with one slot fixed, of the sort at two written `?`, and of a list of it.
fn alias_program(ns: &str, get: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, List}}
  sort Pair
    sort L = ?
    sort R = ?
    entity pair(l: L, r: R)
    {get}
  end
  sort MyPair = Pair
  sort IntPair = Pair[L = Int64]
  sort AnyPair = Pair[L = ?, R = ?]
  sort Pairs = List[T = Pair]
  operation go() -> Int64 = {go}
end
"#
    )
}

/// THE CARRIER RULE READS AN ALIAS OF THE SORT AS THE SORT. `get(p: MyPair) -> L` takes any
/// pair and returns the operation's own `L`, exactly as `get(p: Pair) -> L` does, and is
/// refused in the same words; `IntPair` fixes `L` and leaves `R` open, so it is `R` that
/// has no carrier beside it.
///
/// The loader's `?` followed an alias to the enclosing sort, so the check met the sort's
/// own name there. With the fill deleted both signatures LOADED (MEASURED, against the
/// committed tree refusing them) — an alias is a sort of another name — and the check reads
/// an alias as the type it stands for now (`check_sort_parameter_carriers`).
///
/// EVERY alias, so two more are refused that the committed tree LOADED (MEASURED) — the
/// loader followed only an alias of the sort that left a slot out: one that WRITES the `?`
/// (`sort AnyPair = Pair[L = ?, R = ?]`, refused as `get(p: Pair[L = ?, R = ?]) -> L` always
/// was), and one that HOLDS the sort (`sort Pairs = List[T = Pair]`, as `get(p: List[T =
/// Pair]) -> L` was).
///
/// CONTROLS, which run: a slot the alias FIXES is not an open one (`IntPair`'s `L`: the
/// `L` beside it is the operation's own, taken from `d`), and a carrier beside the alias
/// carries.
#[test]
fn a_sort_parameter_beside_an_alias_of_the_sort_needs_a_carrier() {
    for (n, get, lacks) in [
        ("a1", "operation get(p: MyPair) -> L", "`L` used with no carrier: `p` is any `Pair`"),
        ("a2", "operation get(p: IntPair) -> R", "`R` used with no carrier: `p` is any `Pair`"),
        ("a5", "operation get(p: AnyPair) -> L", "`L` used with no carrier: `p` is any `Pair`"),
        ("a6", "operation get(p: Pairs) -> L", "`L` used with no carrier: `p` holds any `Pair`"),
    ] {
        let ns = format!("wi80zv8e.{n}");
        assert_refused_naming(
            &load_errors(&alias_program(&ns, get, "0")),
            &[&format!("type mismatch in {ns}.Pair.get.p"), lacks],
            get,
        );
    }
    let fixed = alias_program(
        "wi80zv8e.a3",
        "operation get(p: IntPair, d: L) -> L = d",
        r#"Pair.get(pair(l: 1, r: "s"), 42)"#,
    );
    assert_eq!(run_src(&fixed, "wi80zv8e.a3.go"), Ok(42));
    let carried = alias_program(
        "wi80zv8e.a4",
        "operation get(s: Self, p: MyPair) -> L = s.l",
        r#"Pair.get(pair(l: 42, r: 1), pair(l: "a", r: true))"#,
    );
    assert_eq!(run_src(&carried, "wi80zv8e.a4.go"), Ok(42));
}

/// `sort Box` with `rest` inside it, and an operation `go` outside.
fn box_program(ns: &str, members: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Box
    sort T = ?
    entity box(v: T)
{members}
  end
  operation takes_int(b: Box[T = Int64]) -> Int64 = 1
  operation go() -> Int64 = {go}
end
"#
    )
}

/// NOTHING WRITES THE OPEN SLOT ANY MORE, AND EVERY POSITION READS IT OPEN. Inside `sort Box`
/// a bare `Box` is any box — in a parameter (two instances run), in a body (the parameter's
/// slot is its own unknown, so it is no `Box[T = Int64]`), and in a return (the operation
/// picks, so the caller cannot read it as a box of `Int64`). `Self` in the same places is
/// this instance.
///
/// These are the verdicts stage (d) gave through the loader's `?`. They are the rows that
/// hold the deletion: with the `?` no longer written, each reader that took a slot left out
/// as this instance would turn one of them round — see the header, part 3.
#[test]
fn a_slot_left_out_is_open_in_a_parameter_a_body_and_a_return() {
    let both = "    operation both(a: Box, b: Box) -> Int64 = 2";
    let two = box_program("wi80zv8e.p1", both, r#"Box.both(box(v: 1), box(v: "s"))"#);
    assert_eq!(run_src(&two, "wi80zv8e.p1.go"), Ok(2));

    let body = "    operation peek(b: Box) -> Int64 = takes_int(b)";
    assert_refused_naming(
        &load_errors(&box_program("wi80zv8e.p2", body, "0")),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = b.T]"],
        "a bare parameter read in its body as a box of `Int64`",
    );

    let ret = "    operation some(b: Self) -> Box = b";
    assert_refused_naming(
        &load_errors(&box_program("wi80zv8e.p3", ret, "takes_int(Box.some(box(v: 1)))")),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = ?T]"],
        "a bare return read as a box of `Int64`",
    );

    let this = "    operation same(a: Self, b: Self) -> Self = a";
    assert_refused_naming(
        &load_errors(&box_program(
            "wi80zv8e.p4",
            this,
            r#"takes_int(Box.same(box(v: 1), box(v: "s")))"#,
        )),
        &["same.b (op-arg): expected Box[T = Int64], got Box[T = String]"],
        "a second instance where the parameter is `Self`",
    );
    let one = box_program("wi80zv8e.p5", this, "takes_int(Box.same(box(v: 1), box(v: 2)))");
    assert_eq!(run_src(&one, "wi80zv8e.p5.go"), Ok(1));
}
