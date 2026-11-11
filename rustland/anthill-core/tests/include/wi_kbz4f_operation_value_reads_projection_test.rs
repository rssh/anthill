//! WI-20261104-KBZ4F — an operation taken as a function value reads a projection off its own
//! parameter at the instance the value is used at, as a call reads it.
//!
//! Over `g[P](x: P) -> P.Val requires Storage[C = P]` and `app[A, B](f: (x: A) -> B, a: A) -> B
//! = f(a)`, `app(g, memStore)` was refused "expected Int64, got P.Val", and the row twin `app(g,
//! mem)` over `effects {P.E}` "undeclared effect: P.E", where `g(memStore)` and `g(mem)` load.
//! The eta arrow is a ∀ over `P`, and a reference instantiates it at a fresh variable — but `P.Val`
//! names `g`'s own `P`, and the call `app` fixes the fresh one. Now the lift writes such a
//! projection as the member of the instance of the requirement that lends it, `Storage[C =
//! P].Val`, so the instantiation reaches it, and every walk reads the member once its carrier
//! is fixed (`instance_member_at`); a row's labels are the row it reads to.
//!
//! Found beside it, the same root: at a slot that fixes the carrier where the value is written,
//! `applyStr(g)` over `applyStr(f: (x: MemStore) -> String)` LOADED and returned `MemStore`'s
//! `Int64` — the member stayed a neutral, which the argument's check skips — and `applyErr(h)`
//! over a slot `@ {Error}` was refused "declares `P.E`, which the closed row does not admit". The
//! sort's own `requires` (`Sp.sg`, `Sp.g`) gives the same verdicts at such a slot.
//!
//! ## Back-outs, one at a time
//!
//! Measured by temporary switches over this file and 25 nearby suites (`wi_jgw88`, `wi_dnx0e`,
//! `wi_gvgsq`, `wi_qgvb1`, `wi1083`, `wi1063`, `wi1085`, `wi1087`, `wi275`, both `wi383`, `wi428`,
//! `wi844`, `wi_02err`, `wi_7ezs6`, `wi_mhf0b`, `wi_sg16k`, `wi_vnqtr`'s function-value,
//! projection-path and inline-parameter files, `wi_xqgew`, `wi_xsvcs`, `wi1010`, `wi1012`; 251
//! rows). Each fails rows of this file only:
//!
//! 1. **The projection kept as written in the eta lift**: 7 — every row but the two controls,
//!    the ticket's programs refused as on the parent and the `String` slot loading.
//! 2. **The walk reading an instance member only where it grounds**: 2 —
//!    `a_slot_that_fixes_the_carrier_reads_the_member` ("got MemStore -> Storage[C =
//!    MemStore].Val") and `a_projected_parameter_is_read_at_the_carrier`.
//! 3. **No reading in the instance member's grounding arm**: 4 — the two above, the ticket's
//!    programs and `two_references_read_their_own_carriers` ("got Storage[C = StrStore].Val").
//! 4. **The instance's subject not walked**: 3 — the sort-clause slot rows (`Sp.sg` loads at the
//!    `String` slot; `Sp.g` "declares `Strm[C = P].E`") and the unread row, which prints `?P`.
//! 5. **No row label read where a row is decomposed** (`read_instance_member`): 1 —
//!    `a_slot_with_a_row_reads_the_carriers_row`, "declares `{Error}`".
//! 6. **A label that reads to a row not spliced**: the same row, the same words.
//! 7. **No unread instance member reported**: 1 —
//!    `a_carrier_whose_provision_leaves_the_row_unwritten_is_refused`, "undeclared effect:
//!    Strm[C = Lz].E".
//!
//! Pass under every back-out, by design: `the_direct_calls_are_unchanged` and
//! `forwarding_through_a_type_parameter_is_refused_as_the_direct_call_is`.
//!
//! Measured and not here, on the parent too with no projection: a value made where the carrier
//! is not yet fixed holds no dictionary when two sorts provide the spec — `app(g2, memStore)`
//! over `g2[P](x: P) -> Int64 requires Storage[C = P]` loads and stops at run time ("`__req_storage`
//! not bound"); a `let` annotation does not instantiate a type-parameterized operation (`let h:
//! (x: Int64) -> Int64 = idp` over `idp[P](x: P) -> P` is refused); and the sort's own clause at
//! a carrier a later argument fixes (`app(Sp.t, memStore)`) is refused as an unsatisfiable
//! requirement (WI-420).

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `src` is refused once, naming each of `expected`.
#[track_caller]
fn assert_refused_once(src: &str, expected: &[&str], why: &str) {
    let errs = load_errors_of(src);
    assert_eq!(errs.len(), 1, "{why}: one refusal: {errs:#?}");
    assert_refused_naming(&errs, expected, why);
}

/// `Storage` with a carrier and two members, provided at `MemStore` (`Key = String`, `Val =
/// Int64`), beside `decls`.
fn storage_program(ns: &str, decls: &str) -> String {
    storage_program_with(ns, "", decls)
}

/// [`storage_program`] with `Storage` provided at `StrStore` too (`Key = Int64`, `Val = String`).
fn two_stores_program(ns: &str, decls: &str) -> String {
    let str_store = r#"
  sort StrStore
    entity strStore
    provides Storage[C = StrStore, Key = Int64, Val = String]
    operation get(s: StrStore) -> String = "s"
    operation at(s: StrStore, k: Int64) -> String = "t"
  end"#;
    storage_program_with(ns, str_store, decls)
}

fn storage_program_with(ns: &str, more: &str, decls: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Storage
    sort C = ?
    sort Key = ?
    sort Val = ?
    operation get(s: C) -> Val
    operation at(s: C, k: Key) -> Val
  end
  sort MemStore
    entity memStore
    provides Storage[C = MemStore, Key = String, Val = Int64]
    operation get(s: MemStore) -> Int64 = 7
    operation at(s: MemStore, k: String) -> Int64 = 9
  end{more}
  operation g[P](x: P) -> P.Val requires Storage[C = P] = Storage.get(x)
  operation g3[P](x: P, k: P.Key) -> P.Val requires Storage[C = P] = Storage.at(x, k)
  sort Sp
    sort P = ?
    requires Storage[C = P]
    operation sg(x: P) -> P.Val = Storage.get(x)
  end
  operation app[A, B](f: (x: A) -> B, a: A) -> B = f(a)
{decls}
end
"#
    )
}

/// The carriers [`strm_program`] provides `Strm` at: `Mem` (`E = {Error}`), `Pure` (`E = {}`),
/// `Lz` (`E` unwritten).
const MEM: &str = r#"
  sort Mem
    entity mem
    provides Strm[C = Mem, E = {Error}]
    operation step(s: Mem) -> Int64 effects {Error} = 7
  end"#;
const PURE: &str = r#"
  sort Pure
    entity pure
    provides Strm[C = Pure, E = {}]
    operation step(s: Pure) -> Int64 = 5
  end"#;
const LZ: &str = r#"
  sort Lz
    entity lz
    provides Strm[C = Lz]
    operation step(s: Lz) -> Int64 = 4
  end"#;

/// `Strm` with a carrier and a row `E`, provided at `carriers`, beside `decls`. A value made where
/// the carrier is not yet fixed holds a dictionary where one provision answers (the two-providers
/// note at [`two_references_read_their_own_carriers`]), so a program that runs one names one.
fn strm_program(ns: &str, carriers: &[&str], decls: &str) -> String {
    let carriers = carriers.concat();
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Error}}
  sort Strm
    sort C = ?
    effects E = ?
    operation step(s: C) -> Int64 effects {{E}}
  end{carriers}
  operation h[P](x: P) -> Int64 effects {{P.E}} requires Strm[C = P] = Strm.step(x)
  sort Sp
    sort P = ?
    requires Strm[C = P]
    operation g(x: P) -> Int64 effects {{P.E}} = Strm.step(x)
  end
  operation app[A, R](f: (x: A) -> Int64 @ {{R}}, a: A) -> Int64 effects {{R}} = f(a)
{decls}
end
"#
    )
}

/// The ticket's two programs run to 7, and the result is the carrier's member wherever it is
/// used (`app(g, memStore) + 1`). Parent: "expected Int64, got P.Val" and "undeclared effect:
/// P.E".
#[test]
fn an_operation_value_reads_its_projection_at_the_carrier_a_later_argument_fixes() {
    let src = storage_program(
        "wi_kbz4f.ty",
        "  operation main() -> Int64 = app(g, memStore)\n  \
         operation plus() -> Int64 = app(g, memStore) + 1",
    );
    assert_eq!(run_int64(&src, "wi_kbz4f.ty.main"), Ok(7));
    assert_eq!(run_int64(&src, "wi_kbz4f.ty.plus"), Ok(8));
    let src = strm_program(
        "wi_kbz4f.row",
        &[MEM],
        "  operation main() -> Int64 effects {Error} = app(h, mem)",
    );
    assert_eq!(run_int64(&src, "wi_kbz4f.row.main"), Ok(7));
    let src = strm_program(
        "wi_kbz4f.rowpure",
        &[PURE],
        "  operation main() -> Int64 = app(h, pure)",
    );
    assert_eq!(run_int64(&src, "wi_kbz4f.rowpure.main"), Ok(5));
}

/// The caller is held to the row of the carrier, not to `P.E`: `app(h, mem)` under no row is
/// refused naming `Error`, as `h(mem)` is.
#[test]
fn a_caller_is_held_to_the_row_of_the_carrier() {
    for (ns, call) in [
        ("wi_kbz4f.held.value", "app(h, mem)"),
        ("wi_kbz4f.held.direct", "h(mem)"),
    ] {
        let src = strm_program(
            ns,
            &[MEM, PURE],
            &format!("  operation main() -> Int64 = {call}"),
        );
        assert_refused_once(&src, &["main.effects", "got undeclared effect: Error"], ns);
    }
}

/// Two references to one operation are two instances: `g` at `StrStore` (`Val = String`) and
/// at `MemStore` (`Val = Int64`) in one call, the result the second's member. Read at the type
/// alone: with two providers of `Storage` the value made at the reference holds no dictionary,
/// and the run stops where `g` calls `Storage.get` — as it does for a `g` returning `Int64`,
/// with no projection, on the parent.
#[test]
fn two_references_read_their_own_carriers() {
    let both =
        "  operation both[A, B, C, D](f: (x: A) -> B, h: (y: C) -> D, a: A, c: C) -> D = h(c)\n";
    let src = two_stores_program(
        "wi_kbz4f.two",
        &format!("{both}  operation main() -> Int64 = both(g, g, strStore, memStore)"),
    );
    assert_eq!(
        load_errors_of(&src),
        Vec::<String>::new(),
        "each reference at its own carrier"
    );
    let src = two_stores_program(
        "wi_kbz4f.two.swapped",
        &format!("{both}  operation main() -> Int64 = both(g, g, memStore, strStore)"),
    );
    assert_refused_once(
        &src,
        &["main.return", "expected Int64, got String"],
        "the second reference is at StrStore",
    );
}

/// A parameter typed by the projection takes the carrier's member: `MemStore`'s `Key` is
/// `String`, so `app2(g3, memStore, "k")` runs and `app2(g3, memStore, 3)` is refused.
#[test]
fn a_projected_parameter_is_read_at_the_carrier() {
    let app2 = "  operation app2[A, K, B](f: (x: A, k: K) -> B, a: A, k: K) -> B = f(a, k)\n";
    let src = storage_program(
        "wi_kbz4f.key",
        &format!("{app2}  operation main() -> Int64 = app2(g3, memStore, \"k\")"),
    );
    assert_eq!(run_int64(&src, "wi_kbz4f.key.main"), Ok(9));
    let src = storage_program(
        "wi_kbz4f.key.bad",
        &format!("{app2}  operation main() -> Int64 = app2(g3, memStore, 3)"),
    );
    assert_refused_once(
        &src,
        &["app2.f", "got (x: MemStore, k: String) -> Int64"],
        "an Int64 key where MemStore's Key is String",
    );
}

/// At a slot that fixes the carrier where the value is written, the value has the carrier's
/// member, on the operation's own clause and on its sort's alike: a slot `-> Int64` runs, a slot
/// `-> String` is refused. Parent: the `String` slot loaded and answered `MemStore`'s `Int64`.
#[test]
fn a_slot_that_fixes_the_carrier_reads_the_member() {
    for (ns, value) in [("wi_kbz4f.slot.op", "g"), ("wi_kbz4f.slot.sort", "Sp.sg")] {
        let src = storage_program(
            ns,
            &format!(
                "  operation applyMem(f: (x: MemStore) -> Int64) -> Int64 = f(memStore)\n  \
                 operation main() -> Int64 = applyMem({value})"
            ),
        );
        assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(7), "{ns}");
        let src = storage_program(
            &format!("{ns}.str"),
            &format!(
                "  operation applyStr(f: (x: MemStore) -> String) -> String = f(memStore)\n  \
                 operation main() -> String = applyStr({value})"
            ),
        );
        assert_refused_once(
            &src,
            &[
                "applyStr.f",
                "expected MemStore -> String, got MemStore -> Int64",
            ],
            ns,
        );
    }
}

/// A slot's closed row admits the carrier's row: `@ {Error}` takes the value at `Mem`, `@ {}`
/// refuses it naming `Error`, on either clause. Parent: both refused naming `P.E`.
#[test]
fn a_slot_with_a_row_reads_the_carriers_row() {
    for (ns, value) in [
        ("wi_kbz4f.rowslot.op", "h"),
        ("wi_kbz4f.rowslot.sort", "Sp.g"),
    ] {
        let src = strm_program(
            ns,
            &[MEM, PURE],
            &format!(
                "  operation applyErr(f: (x: Mem) -> Int64 @ {{Error}}) -> Int64 effects {{Error}} = f(mem)\n  \
                 operation main() -> Int64 effects {{Error}} = applyErr({value})"
            ),
        );
        assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(7), "{ns}");
        let src = strm_program(
            &format!("{ns}.closed"),
            &[MEM, PURE],
            &format!(
                "  operation applyPure(f: (x: Mem) -> Int64 @ {{}}) -> Int64 = f(mem)\n  \
                 operation main() -> Int64 = applyPure({value})"
            ),
        );
        assert_refused_once(
            &src,
            &[
                "applyPure.f",
                "declares `Error`, which the closed row does not admit",
            ],
            ns,
        );
    }
}

/// At a carrier whose provision leaves the row unwritten the value is refused naming the
/// requirement, as the direct call is (`UnreadProjection`).
#[test]
fn a_carrier_whose_provision_leaves_the_row_unwritten_is_refused() {
    for (ns, call, words) in [
        (
            "wi_kbz4f.unread.value",
            "app(h, lz)",
            [
                "`Strm[C = Lz].E` does not read at this call",
                "no one provision answering `Strm[C = Lz]` names one type for `E`",
            ],
        ),
        (
            "wi_kbz4f.unread.direct",
            "h(lz)",
            ["`P.E` does not read at this call", "leaves `E` unwritten"],
        ),
    ] {
        let src = strm_program(
            ns,
            &[MEM, LZ],
            &format!("  operation main() -> Int64 = {call}"),
        );
        assert_refused_once(
            &src,
            &[words[0], words[1], "write it in the requirement"],
            ns,
        );
    }
}

/// CONTROL — the direct calls the values are measured against.
#[test]
fn the_direct_calls_are_unchanged() {
    let src = storage_program(
        "wi_kbz4f.direct.ty",
        "  operation main() -> Int64 = g(memStore)",
    );
    assert_eq!(run_int64(&src, "wi_kbz4f.direct.ty.main"), Ok(7));
    let src = strm_program(
        "wi_kbz4f.direct.row",
        &[MEM, PURE],
        "  operation main() -> Int64 effects {Error} = h(mem)",
    );
    assert_eq!(run_int64(&src, "wi_kbz4f.direct.row.main"), Ok(7));
}

/// CONTROL — a caller forwarding the member through its own type parameter is refused, as the
/// direct call `g(y)` is ("expected Q.Val, got P.Val"): neither reads `Q.Val` as the instance
/// member it is. Not this ticket's.
#[test]
fn forwarding_through_a_type_parameter_is_refused_as_the_direct_call_is() {
    for (ns, call) in [
        ("wi_kbz4f.fwd.value", "app(g, y)"),
        ("wi_kbz4f.fwd.direct", "g(y)"),
    ] {
        let src = storage_program(
            ns,
            &format!("  operation forward[Q](y: Q) -> Q.Val requires Storage[C = Q] = {call}"),
        );
        assert_refused_once(&src, &["forward.return", "expected Q.Val"], ns);
    }
}
