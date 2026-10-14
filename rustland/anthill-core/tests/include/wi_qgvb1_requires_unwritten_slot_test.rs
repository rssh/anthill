//! WI-20261003-QGVB1 — A `requires` THAT LEAVES SLOTS UNWRITTEN.
//!
//! `requires Storage[C = P]` leaves `Key` and `Val` unwritten, which is `Storage[C = P, Key =
//! ?, Val = ?]` (kernel-language §8.1): the spec at any binding of them, and they are no
//! element of a call. Decided with the user 2026-10-14 for every reader: the provision check,
//! the member rule, and a call. The requirement is met by the dictionary at the bindings it
//! writes — a covering `requires` of the caller, or the provisions answering the rest where
//! they name one type for each open slot; provisions naming different types are a tie. A
//! projection the requirement lends (`P.Key`) is read through the provision that answers it,
//! and where none says one type a call cannot read it. A written `?` is held as a slot left
//! out, in a sort's clause and an operation's.
//!
//! ## Back-outs, one at a time — the whole `anthill-core` crate (measured)
//!
//! 1. **Open slots in a requirement's goal** (`requires_chain_goals`: neither held out of σ
//!    nor completed): 14 fail — 11 here, every row that loads or reads a slot a sort's
//!    requirement leaves open; and `provision_written_through_alias_test::a_projection_
//!    rebuilt_…`, `wi_0rp29_review9_regressions_test::a_rigid_type_projection_under_…` and
//!    `wi_a3nnd_checked_provisions_test::a_second_answer_for_an_open_slot_…`.
//! 2. **Their completion alone** (`complete_open_slots_at_carrier`): the same 14.
//! 3. **The member rule's reading** (`ProjectionReader::at_provision`): 5 fail — the two
//!    member rows, `a_call_reads_its_result_…`, and the alias and review-9 rows.
//! 4. **A written `?` held as a slot left out** (loader, `normalize_op_requires_entry`): 4
//!    fail — `a_requirement_writing_its_other_slots_as_wildcards_…`, `a_member_restating_…`,
//!    `a_default_body_reads_…` and `a_parametric_carrier_whose_own_requirement_…`.
//! 5. **A call reading a parameter's projection through the lending requirement**
//!    (`ground_sort_param_projection`, and the operation branch of
//!    `ground_rigid_projection_if_concrete`): 9 fail — the call rows, the member rows, the
//!    witness, the parametric carrier and `an_operations_requirement_lends_…`.
//! 6. **A projection that does not read refused** (`UnreadProjection::why_unread`): 2 fail —
//!    `a_projection_no_provision_says_…` and `an_operations_requirement_two_provisions_…`.
//! 7. **An open demand slot covered by any supply** (`supply_covers_demanded_keys`): 2 fail —
//!    `a_parametric_carrier_whose_own_requirement_…` and
//!    `wi826_cover_walk_orientation_test::partially_bound_entry_leaves_…`.
//! 8. **A call's sort half completed at its carrier** (`dep_completed_at_carrier` on the sort
//!    half, a sort's open slot read as unwritten there): 2 fail — `a_call_of_the_requiring_…`
//!    and `a_witness_says_…`.
//! 9. **One answer, not the carrier's first** (`open_slots_said` taking the first provision
//!    where two name the slot apart): 5 fail — the three tie rows, the two unread rows, and
//!    the seal row.
//! 10. **The open search noted for the seal** (`note_open_slot_search`): 1 fails —
//!    `wi_a3nnd_checked_provisions_test::a_second_answer_for_an_open_slot_…`.
//! 11. **The tie named** (`OpenSlotsNamedApart`): 3 fail — the two tie rows and the seal row.
//! 12. **An open slot no element of the call** (`unconstrained_elements`) and **the tie's
//!    account standing alone** (the no-route arm): each fails
//!    `two_provisions_naming_an_open_slot_apart_are_refused_at_a_call` on its wording.
//!
//! Pass under every back-out, by design: `a_requirement_writing_every_slot_is_met_as_before`,
//! and the refusals the parent commit made too — a carrier with no `Storage` or another
//! `Key`, a member taking another type, an open slot supplying a written one, a parametric
//! carrier whose own requirement is absent or writes the slot otherwise.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// The three sorts every row shares: a spec with two parameters beside its carrier, and a
/// carrier that provides it at `String` / `Int64`. `{SP}` is the requiring spec, `{CAR}` its
/// provider; `{NS}` keeps each row's names apart.
fn program(ns: &str, sp: &str, car: &str, tail: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, List, Option}}
  sort Storage
    sort C = ?
    sort Key = ?
    sort Val = ?
    operation get(s: C, k: Key) -> Val
  end
  sort MemStore
    entity memStore
    provides Storage[C = MemStore, Key = String, Val = Int64]
    operation get(s: MemStore, k: String) -> Int64 = 7
  end
{sp}
{car}
{tail}
end
"#
    )
}

fn sp_requiring(clause: &str) -> String {
    format!(
        r#"  sort Sp
    sort P = ?
    requires {clause}
    operation size(s: Self) -> Int64
  end"#
    )
}

const CAR_AT_MEMSTORE: &str = r#"  sort Car
    entity car(n: Int64)
    provides Sp[P = MemStore]
    operation size(c: Car) -> Int64 = c.n
  end"#;

const GO_SIZE: &str = "  operation go() -> Int64 = Sp.size(car(n: 42))";

// ── (a) the provision check ─────────────────────────────────────────────────────────────────

#[test]
fn a_requirement_leaving_its_other_slots_unwritten_is_met_by_the_carriers_provision() {
    let src = program(
        "qgvb1.a_unwritten",
        &sp_requiring("Storage[C = P]"),
        CAR_AT_MEMSTORE,
        GO_SIZE,
    );
    assert_eq!(run_src(&src, "qgvb1.a_unwritten.go"), Ok(42));
}

#[test]
fn a_requirement_writing_its_other_slots_as_wildcards_is_met_by_the_carriers_provision() {
    let src = program(
        "qgvb1.a_wild",
        &sp_requiring("Storage[C = P, Key = ?, Val = ?]"),
        CAR_AT_MEMSTORE,
        GO_SIZE,
    );
    assert_eq!(run_src(&src, "qgvb1.a_wild.go"), Ok(42));
}

#[test]
fn a_requirement_writing_every_slot_is_met_as_before() {
    let src = program(
        "qgvb1.a_written",
        &sp_requiring("Storage[C = P, Key = String, Val = Int64]"),
        CAR_AT_MEMSTORE,
        GO_SIZE,
    );
    assert_eq!(run_src(&src, "qgvb1.a_written.go"), Ok(42));
}

#[test]
fn a_carrier_providing_no_storage_is_still_refused() {
    let car = r#"  sort Car
    entity car(n: Int64)
    provides Sp[P = Car]
    operation size(c: Car) -> Int64 = c.n
  end"#;
    for (ns, clause) in [
        ("qgvb1.none_unwritten", "Storage[C = P]"),
        ("qgvb1.none_wild", "Storage[C = P, Key = ?, Val = ?]"),
    ] {
        let src = program(ns, &sp_requiring(clause), car, GO_SIZE);
        assert_refused_naming(
            &load_errors(&src),
            &["provides 'qgvb1.", "which requires", "Storage"],
            ns,
        );
    }
}

#[test]
fn a_carrier_whose_storage_binds_a_written_slot_otherwise_is_still_refused() {
    for (ns, clause) in [
        ("qgvb1.other_key", "Storage[C = P, Key = Int64]"),
        ("qgvb1.other_val", "Storage[C = P, Key = ?, Val = String]"),
    ] {
        let src = program(ns, &sp_requiring(clause), CAR_AT_MEMSTORE, GO_SIZE);
        assert_refused_naming(&load_errors(&src), &["which requires", "Storage"], ns);
    }
}

// ── (b) the declaration rule ────────────────────────────────────────────────────────────────

fn sp_with_op(clause: &str) -> String {
    format!(
        r#"  sort Sp
    sort P = ?
    requires {clause}
    operation size(s: Self) -> Int64
    operation op(s: Self, x: P.Key) -> Int64
  end"#
    )
}

fn car_with_op(x: &str) -> String {
    format!(
        r#"  sort Car
    entity car(n: Int64)
    provides Sp[P = MemStore]
    operation size(c: Car) -> Int64 = c.n
    operation op(c: Car, x: {x}) -> Int64 = 42
  end"#
    )
}

const GO_OP: &str = r#"  operation go() -> Int64 = Sp.op(car(n: 1), "k")"#;

#[test]
fn a_member_restating_the_specs_projection_fits_it() {
    for (ns, clause) in [
        ("qgvb1.b_unwritten", "Storage[C = P]"),
        ("qgvb1.b_wild", "Storage[C = P, Key = ?, Val = ?]"),
        (
            "qgvb1.b_written",
            "Storage[C = P, Key = String, Val = Int64]",
        ),
    ] {
        let src = program(ns, &sp_with_op(clause), &car_with_op("MemStore.Key"), GO_OP);
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42), "{ns}");
    }
}

#[test]
fn a_member_taking_the_projections_value_fits_it() {
    for (ns, clause) in [
        ("qgvb1.bs_unwritten", "Storage[C = P]"),
        (
            "qgvb1.bs_written",
            "Storage[C = P, Key = String, Val = Int64]",
        ),
    ] {
        let src = program(ns, &sp_with_op(clause), &car_with_op("String"), GO_OP);
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42), "{ns}");
    }
}

#[test]
fn a_member_taking_another_type_than_the_projections_is_refused() {
    for (ns, clause) in [
        ("qgvb1.bi_unwritten", "Storage[C = P]"),
        (
            "qgvb1.bi_written",
            "Storage[C = P, Key = String, Val = Int64]",
        ),
    ] {
        let src = program(ns, &sp_with_op(clause), &car_with_op("Int64"), GO_OP);
        assert_refused_naming(
            &load_errors(&src),
            &["its own member 'op' does not fit"],
            ns,
        );
    }
}

// ── the call ────────────────────────────────────────────────────────────────────────────────

#[test]
fn a_call_checks_its_argument_against_the_projection_as_the_carrier_says_it() {
    let src = program(
        "qgvb1.call_arg",
        &sp_with_op("Storage[C = P]"),
        &car_with_op("MemStore.Key"),
        "  operation go() -> Int64 = Sp.op(car(n: 1), 5)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["op.x", "expected String, got Int64"],
        "an Int64 passed where the carrier's Key is String",
    );
}

#[test]
fn a_call_reads_its_result_typed_by_the_projection_as_the_carrier_says_it() {
    let sp = r#"  sort Sp
    sort P = ?
    requires Storage[C = P]
    operation size(s: Self) -> Int64
    operation op(s: Self, x: P.Key) -> P.Val
  end"#;
    let car = r#"  sort Car
    entity car(n: Int64)
    provides Sp[P = MemStore]
    operation size(c: Car) -> Int64 = c.n
    operation op(c: Car, x: MemStore.Key) -> MemStore.Val = 41
  end"#;
    let src = program(
        "qgvb1.call_result",
        sp,
        car,
        r#"  operation go() -> Int64 = Sp.op(car(n: 1), "k") + 1"#,
    );
    assert_eq!(run_src(&src, "qgvb1.call_result.go"), Ok(42));
}

/// The requirement's dictionary is the one the completed goal names: a default body of the
/// requiring spec reaches `MemStore.get` through it.
#[test]
fn a_default_body_reads_the_requirement_at_the_carriers_provision() {
    for (ns, clause) in [
        ("qgvb1.body_unwritten", "Storage[C = P]"),
        ("qgvb1.body_wild", "Storage[C = P, Key = ?, Val = ?]"),
    ] {
        let sp = format!(
            r#"  sort Sp
    sort P = ?
    requires {clause}
    operation store(s: Self) -> P
    operation fetch(s: Self, k: P.Key) -> P.Val = Storage.get(s.store(), k)
  end"#
        );
        let car = r#"  sort Car
    entity car(n: Int64)
    provides Sp[P = MemStore]
    operation store(c: Car) -> MemStore = memStore
  end"#;
        let src = program(
            ns,
            &sp,
            car,
            r#"  operation go() -> Int64 = Sp.fetch(car(n: 1), "k") + 35"#,
        );
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42), "{ns}");
    }
}

// ── the slot is the requirement's, not the requiring spec's ─────────────────────────────────

/// `Sp`'s own `Key` is no binding of `Storage`'s: the clause leaves `Storage`'s `Key` open, and
/// `Car`'s `Key = Int64` for `Sp` says nothing of it. σ by short name reached the open slot as
/// though it were written `Key = Key`, and the provision was refused "nothing provides
/// `Storage[C = MemStore, Key = Int64, …]`" (MEASURED on the parent commit).
#[test]
fn a_parameter_of_the_requiring_spec_named_as_the_open_slot_does_not_fill_it() {
    let sp = r#"  sort Sp
    sort P = ?
    sort Key = ?
    requires Storage[C = P]
    operation size(s: Self) -> Int64
  end"#;
    let car = r#"  sort Car
    entity car(n: Int64)
    provides Sp[P = MemStore, Key = Int64]
    operation size(c: Car) -> Int64 = c.n
  end"#;
    let src = program("qgvb1.same_name", sp, car, GO_SIZE);
    assert_eq!(run_src(&src, "qgvb1.same_name.go"), Ok(42));
}

// ── a carrier the provision leaves a parameter ──────────────────────────────────────────────

fn box_providing(own_requires: &str) -> String {
    format!(
        r#"  sort Box
    sort X = ?
    entity box(x: X)
{own_requires}
    provides Sp[P = X]
    operation store(b: Self) -> X = b.x
  end"#
    )
}

fn sp_fetching(clause: &str) -> String {
    format!(
        r#"  sort Sp
    sort P = ?
    requires {clause}
    operation store(s: Self) -> P
    operation fetch(s: Self, k: P.Key) -> P.Val = Storage.get(s.store(), k)
  end"#
    )
}

/// `Box[X]` provides `Sp[P = X]` under its own `requires Storage[C = X, Key = String]`, which
/// is a `Storage[C = X]`: the slot the spec's requirement leaves open is any type, and the
/// one the box's writes is one of them. Refused on the parent commit in both spellings, the
/// requirement's open slot compared with the box's `String` as though it were written.
#[test]
fn a_parametric_carrier_whose_own_requirement_writes_the_open_slot_meets_it() {
    for (ns, clause) in [
        ("qgvb1.box_unwritten", "Storage[C = P]"),
        ("qgvb1.box_wild", "Storage[C = P, Key = ?, Val = ?]"),
    ] {
        let src = program(
            ns,
            &sp_fetching(clause),
            &box_providing("    requires Storage[C = X, Key = String]"),
            r#"  operation go() -> Int64 = Sp.fetch(box(x: memStore), "k") + 35"#,
        );
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(42), "{ns}");
    }
}

#[test]
fn a_parametric_carrier_with_no_requirement_of_its_own_is_still_refused() {
    let src = program(
        "qgvb1.box_bare",
        &sp_fetching("Storage[C = P]"),
        &box_providing(""),
        r#"  operation go() -> Int64 = Sp.fetch(box(x: memStore), "k")"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["'qgvb1.box_bare.Box' provides 'qgvb1.box_bare.Sp', which requires"],
        "a box that says nothing of its X's Storage",
    );
}

#[test]
fn a_parametric_carrier_whose_own_requirement_writes_the_slot_otherwise_is_still_refused() {
    let src = program(
        "qgvb1.box_other",
        &sp_fetching("Storage[C = P, Key = String]"),
        &box_providing("    requires Storage[C = X, Key = Int64]"),
        r#"  operation go() -> Int64 = 1"#,
    );
    assert_refused_naming(
        &load_errors(&src),
        &["'qgvb1.box_other.Box' provides 'qgvb1.box_other.Sp', which requires"],
        "a box whose X has Storage at another Key",
    );
}

// ── a call of an operation of the requiring sort ────────────────────────────────────────────

/// The call builds the sort's dictionary at the carrier its argument names, the open slots
/// said by that carrier's provision. Refused on the parent commit "element `Key =
/// Storage.Key` is unconstrained at this call site" — the slot read as written, where the
/// same clause on the OPERATION (`f[X](x: X) requires Storage[C = X]`) loaded.
#[test]
fn a_call_of_the_requiring_sorts_operation_builds_its_dictionary_at_the_carrier() {
    let sp = r#"  sort Sp2
    sort P = ?
    requires Storage[C = P]
    operation f(x: P) -> Int64 = 1
    operation g(x: P, k: P.Key) -> P.Val = Storage.get(x, k)
  end"#;
    let src = program(
        "qgvb1.direct",
        sp,
        "",
        r#"  operation go() -> Int64 = Sp2.f(memStore) + Sp2.g(memStore, "k") * 5 + 6"#,
    );
    assert_eq!(run_src(&src, "qgvb1.direct.go"), Ok(42));
}

/// A WITNESS says the slot where the carrier provides nothing itself: `LeafLeaf` provides
/// `Pair[P = Leaf, Q = Leaf]`, so `Partial`'s `Pair[P = MT]` at `MT = Leaf` is it, and the
/// projection `MT.Q` at that call is `Leaf` — from a caller that holds the dictionary and from
/// one that holds none.
#[test]
fn a_witness_says_the_open_slot_at_a_call() {
    let src = r#"
namespace qgvb1.witness
  import anthill.prelude.{Int64, Bool}
  sort Leaf
    entity leaf
  end
  sort Pair
    sort P = ?
    sort Q = ?
    operation pd(a: P, b: Q) -> Int64
  end
  sort LeafLeaf
    provides Pair[P = Leaf, Q = Leaf]
    operation pd(a: Leaf, b: Leaf) -> Int64 = 21
  end
  sort Partial
    sort MT = ?
    requires Pair[P = MT]
    operation p(x: MT, y: MT.Q) -> Int64 = Pair.pd(x, y)
  end
  sort Holder
    requires Pair[P = Leaf, Q = Leaf]
    operation h() -> Int64 = Partial.p(leaf(), leaf())
  end
  operation go() -> Int64 = Partial.p(leaf(), leaf()) + Holder.h()
end
"#;
    assert_eq!(run_src(src, "qgvb1.witness.go"), Ok(42));
}

/// An open slot of the caller's requirement supplies no requirement that WRITES it: inside
/// `Partial`, whose `Pair[P = MT]` holds a dictionary at some `Q`, `Callee`'s `Pair[P = MT, Q =
/// Pebble]` is not that dictionary, and with no provider at `Q = Pebble` the call is refused.
#[test]
fn an_open_slot_of_the_callers_requirement_supplies_no_written_one() {
    let src = r#"
namespace qgvb1.supply
  import anthill.prelude.{Int64, Bool}
  sort Leaf
    entity leaf
  end
  sort Pebble
    entity pebble
  end
  sort Pair
    sort P = ?
    sort Q = ?
    operation pd(a: P, b: Q) -> Int64
  end
  sort LeafLeaf
    provides Pair[P = Leaf, Q = Leaf]
    operation pd(a: Leaf, b: Leaf) -> Int64 = 7
  end
  sort Callee
    sort CP = ?
    sort CQ = ?
    requires Pair[P = CP, Q = CQ]
    operation c(a: CP, b: CQ) -> Int64 = Pair.pd(a, b)
  end
  sort Partial
    sort MT = ?
    requires Pair[P = MT]
    operation p(x: MT) -> Int64 = Callee.c(x, pebble())
  end
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["Callee.c.requires", "Q = qgvb1.supply.Pebble"],
        "Partial's open Q supplying Callee's Q = Pebble",
    );
}

// ── two provisions that name the open slot apart ────────────────────────────────────────────

/// `Leaf`, `Pebble`, `Pair[P, Q]` with `LeafLeaf` at `Pair[P = Leaf, Q = Leaf]` and
/// `AnyPebble[X]` at `Pair[P = X, Q = Pebble]`: two provisions answer `Pair[P = Leaf]`, naming
/// `Q` apart. `{tail}` is the rest of the namespace.
fn pair_apart(ns: &str, tail: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
  sort Leaf
    entity leaf
  end
  sort Pebble
    entity pebble
  end
  sort Pair
    sort P = ?
    sort Q = ?
    operation pd(a: P, b: Q) -> Int64
  end
  sort LeafLeaf
    provides Pair[P = Leaf, Q = Leaf]
    operation pd(a: Leaf, b: Leaf) -> Int64 = 7
  end
  sort AnyPebble
    sort X = ?
    provides Pair[P = X, Q = Pebble]
    operation pd(a: X, b: Pebble) -> Int64 = 8
  end
{tail}
end
"#
    )
}

const PARTIAL_READS_Q: &str = r#"  sort Partial
    sort MT = ?
    requires Pair[P = MT]
    operation p(x: MT, y: MT.Q) -> Int64 = Pair.pd(x, y)
  end"#;

/// The requirement says neither dictionary, so it is refused, naming both — and not as an
/// unconstrained element of the call with the advice to declare a slot for it, which neither
/// pinning nor a slot repairs. Completed from the
/// carrier's own reading, `LeafLeaf` was taken and `AnyPebble` never weighed: beside `p(x: MT,
/// y: MT.Q)`, `Partial.p(leaf(), leaf())` ran to 7 and `pebble()` was refused "expected Leaf"
/// (MEASURED on the first cut of this change).
#[test]
fn two_provisions_naming_an_open_slot_apart_are_refused_at_a_call() {
    let tail = r#"  sort Partial
    sort MT = ?
    requires Pair[P = MT]
    operation p(x: MT) -> Int64 = 1
  end
  operation go() -> Int64 = Partial.p(leaf())"#;
    let errors = load_errors(&pair_apart("qgvb1.apart_call", tail));
    assert_refused_naming(
        &errors,
        &["Partial.p", "leaves `Q` unwritten", "LeafLeaf", "AnyPebble"],
        "a call whose requirement two provisions answer apart",
    );
    // `Q` is no element of the call, and no slot of the caller's is what is missing.
    let joined = errors.join(" | ");
    assert!(
        !joined.contains("unconstrained at this call site"),
        "{joined}"
    );
    assert!(!joined.contains("declare a requirement slot"), "{joined}");
}

#[test]
fn two_provisions_naming_an_open_slot_apart_are_refused_at_a_provision() {
    let tail = r#"  sort Sp2
    sort P = ?
    requires Pair[P = P]
    operation size(s: Self) -> Int64
  end
  sort Car
    entity car(n: Int64)
    provides Sp2[P = Leaf]
    operation size(c: Car) -> Int64 = 1
  end"#;
    assert_refused_naming(
        &load_errors(&pair_apart("qgvb1.apart_prov", tail)),
        &[
            "'qgvb1.apart_prov.Car' provides 'qgvb1.apart_prov.Sp2'",
            "leaves `Q` unwritten",
            "LeafLeaf",
            "AnyPebble",
        ],
        "a provision whose requirement two provisions answer apart",
    );
}

/// A caller's `requires` that writes the slot supplies the requirement — but the CALL still
/// has to read `MT.Q` to check `y`, and no provision says it: refused in both spellings, where
/// it would otherwise take any argument against a dictionary at `Q = Pebble` (`leaf()` reached
/// `AnyPebble.pd` as its `Pebble`, MEASURED on the first cut of this change).
#[test]
fn a_projection_no_provision_says_does_not_read_at_a_call() {
    for (ns, y) in [
        ("qgvb1.unread_leaf", "leaf()"),
        ("qgvb1.unread_peb", "pebble()"),
    ] {
        let tail = format!(
            "{PARTIAL_READS_Q}\n  sort Holder\n    requires Pair[P = Leaf, Q = Pebble]\n    \
             operation h() -> Int64 = Partial.p(leaf(), {y})\n  end"
        );
        assert_refused_naming(
            &load_errors(&pair_apart(ns, &tail)),
            &["`MT.Q` does not read at this call"],
            ns,
        );
    }
}

// ── the same requirement on an operation ────────────────────────────────────────────────────

/// An operation's own `requires Pair[P = X]` lends `X.Q` the same way: read at the call through
/// the one provision that answers `Pair[P = Leaf]` — here a WITNESS, which the carrier's own
/// view did not consult — so `y` is checked against `Leaf`. On the parent commit `X.Q` stayed
/// the neutral and the argument was not checked at all: both `leaf()` and `pebble()` loaded.
#[test]
fn an_operations_requirement_lends_its_projection_through_the_one_provision() {
    let leaf_leaf_only = r#"
namespace NS
  import anthill.prelude.{Int64, Bool}
  sort Leaf
    entity leaf
  end
  sort Pebble
    entity pebble
  end
  sort Pair
    sort P = ?
    sort Q = ?
    operation pd(a: P, b: Q) -> Int64
  end
  sort LeafLeaf
    provides Pair[P = Leaf, Q = Leaf]
    operation pd(a: Leaf, b: Leaf) -> Int64 = 42
  end
  operation f[X](x: X, y: X.Q) -> Int64 requires Pair[P = X] = Pair.pd(x, y)
  operation go() -> Int64 = f(leaf(), Y)
end
"#;
    let src = leaf_leaf_only
        .replace("NS", "qgvb1.op_one")
        .replace("Y)", "leaf())");
    assert_eq!(run_src(&src, "qgvb1.op_one.go"), Ok(42));
    let src = leaf_leaf_only
        .replace("NS", "qgvb1.op_wrong")
        .replace("Y)", "pebble())");
    assert_refused_naming(
        &load_errors(&src),
        &["f.y", "expected Leaf, got Pebble"],
        "a Pebble where the one provision says Leaf",
    );
}

/// Two provisions naming `Q` apart: the call cannot read `X.Q`, in either spelling of `y`.
#[test]
fn an_operations_requirement_two_provisions_name_apart_does_not_read() {
    for (ns, y) in [
        ("qgvb1.op_apart_leaf", "leaf()"),
        ("qgvb1.op_apart_peb", "pebble()"),
    ] {
        let tail = format!(
            "  operation f[X](x: X, y: X.Q) -> Int64 requires Pair[P = X] = Pair.pd(x, y)\n  \
             operation go() -> Int64 = f(leaf(), {y})"
        );
        assert_refused_naming(
            &load_errors(&pair_apart(ns, &tail)),
            &["`X.Q` does not read at this call"],
            ns,
        );
    }
}
