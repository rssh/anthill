//! WI-20260907-VM9Q7 — a query answer that is a literal prints ONE way, whatever
//! carrier it rides.
//!
//! A literal answer arrives on one of three carriers: a hash-consed `Value::Term` over
//! `Term::Const` (the FACT spelling, `f(v: ?r)` over `fact f(v: 3.0)`), a `Const`
//! occurrence (the `<=>` spelling, `?r <=> 3.0`), or a native scalar — and
//! `KnowledgeBase::answer_binding` now folds the first two to the third. The CLI's
//! `render_value` used to spell each carrier its own way, so the same answer printed
//! differently depending on how the rule reached it. It now reads a literal through
//! `TermView::as_literal` and writes it through `write_literal` on every carrier.
//!
//! One row per `Literal` variant, each asking BOTH spellings — the census at
//! `render_value`'s site, driven rather than stated.
//!
//! ── CONTROL ─────────────────────────────────────────────────────────────
//!
//! Each row names the back-out it fails on; all measured.
//!
//!   * `render_value`'s literal row backed out (the per-carrier native arms restored:
//!     `f.to_string()`, `format!("{s:?}")`, …) — `a_float_keeps_its_decimal_point`
//!     (`?r = 3`) and `wi863_operator_arithmetic_test::float_division_computes`
//!     (`6.0 / 2.0` as `3`). With the fold's `Term` half ALSO backed out — the code as
//!     it stood before this ticket — the float row still fails, on its `eq_` spelling
//!     alone: EMVCB already folded a `Const` occurrence, so `?r <=> 3.0` printed `3`.
//!     That is what made the printer a defect of its own rather than a cost of the fold.
//!   * `write_anthill_string`'s control-character escape backed out —
//!     `a_string_prints_its_surface_spelling`: ESC reaches the terminal raw, on both
//!     spellings. The same row fails on the DECODER's back-out (the old pass-through
//!     reads the fixture's `\u{1b}` as `u{1b}`).
//!   * `write_literal`'s two non-finite arms backed out —
//!     `a_non_finite_float_prints_its_const_name` (`inf.0`).
//!
//! PASSES EITHER WAY, BY DESIGN — `int_bigint_and_bool_agree`: the three variants whose
//! native `Display` already spelled what `write_literal` does. Kept so a later change
//! to either renderer cannot split them silently. And the string row passes the
//! printer back-out by coincidence, not design: Rust's `{:?}` happens to spell ESC
//! `\u{1b}` too — it differs from `write_anthill_string` on other characters (a
//! zero-width space, which `{:?}` escapes and an anthill literal holds raw), which is
//! why the printer's own row is the float one.

use crate::common::{anthill, write_temp};

/// A fact and a `<=>` rule per `Literal` variant. The string holds an ESC, spelled with
/// the `\u{…}` escape (spec §2.4) — the character that makes a raw print a live terminal
/// sequence.
const SRC: &str = "namespace vm9q7\n  \
   import anthill.prelude.{Int64, BigInt, Float, Bool, String}\n  \
   sort Lit\n    \
     entity i(v: Int64)\n    \
     entity b(v: BigInt)\n    \
     entity f(v: Float)\n    \
     entity t(v: Bool)\n    \
     entity s(v: String)\n  \
   end\n  \
   fact i(v: 7)\n  \
   fact b(v: 123456789012345678901234567890)\n  \
   fact f(v: 3.0)\n  \
   fact t(v: true)\n  \
   fact s(v: \"a\\u{1b}b\")\n  \
   rule fact_i(?r) :- i(v: ?r)\n  \
   rule fact_b(?r) :- b(v: ?r)\n  \
   rule fact_f(?r) :- f(v: ?r)\n  \
   rule fact_t(?r) :- t(v: ?r)\n  \
   rule fact_s(?r) :- s(v: ?r)\n  \
   rule eq_i(?r) :- ?r <=> 7\n  \
   rule eq_b(?r) :- ?r <=> 123456789012345678901234567890\n  \
   rule eq_f(?r) :- ?r <=> 3.0\n  \
   rule eq_t(?r) :- ?r <=> true\n  \
   rule eq_s(?r) :- ?r <=> \"a\\u{1b}b\"\n  \
   rule eq_inf(?r) :- ?r <=> 1.0 / 0.0\n  \
   rule eq_ninf(?r) :- ?r <=> 0.0 - 1.0 / 0.0\n  \
   rule eq_nan(?r) :- ?r <=> 0.0 / 0.0\n\
   end\n";

/// Written ONCE: `write_temp`'s path is per process, not per call, so the rows below —
/// which run in parallel — would otherwise truncate the file under each other's reads.
fn fixture() -> &'static std::path::Path {
    static PATH: std::sync::OnceLock<std::path::PathBuf> = std::sync::OnceLock::new();
    PATH.get_or_init(|| write_temp("vm9q7.anthill", SRC))
}

/// The rendered value of the sole answer of `vm9q7.<rule>(?r)`.
fn answer(rule: &str) -> String {
    let path = fixture();
    let out = anthill(&[
        "query",
        "-p",
        path.to_str().unwrap(),
        &format!("vm9q7.{rule}(?r)"),
    ]);
    assert_eq!(out.code, 0, "`{rule}` must answer; stderr:\n{}", out.stderr);
    let rows: Vec<&str> = out
        .stdout
        .lines()
        .filter_map(|l| l.trim().strip_prefix("?r = "))
        .collect();
    match rows.as_slice() {
        [one] => one.to_string(),
        other => panic!(
            "`{rule}` must answer ONE row; got {other:?}\nstdout:\n{}",
            out.stdout
        ),
    }
}

/// Both spellings of one variant print `want`.
fn both_spellings_print(variant: &str, want: &str) {
    for rule in [format!("fact_{variant}"), format!("eq_{variant}")] {
        assert_eq!(
            answer(&rule),
            want,
            "`{rule}` renders its literal's surface spelling"
        );
    }
}

/// THE CONTROL THE TICKET NAMES: `wi863`'s `6.0 / 2.0` prints `3.0`. Fails when the
/// printer is backed out.
#[test]
fn a_float_keeps_its_decimal_point() {
    both_spellings_print("f", "3.0");
}

/// A control character prints as the escape that reads back as it — never raw, which
/// would put the KB's data on the terminal as a live sequence. Fails when
/// `write_anthill_string`'s control-character escape is backed out.
#[test]
fn a_string_prints_its_surface_spelling() {
    both_spellings_print("s", "\"a\\u{1b}b\"");
}

/// The IEEE specials have NO literal (`float_literal` is digits-dot-digits), so they print
/// as the consts the language names them by (spec §2.4). Neither earlier spelling would
/// do: `write_literal`'s "add `.0`" garbled `inf` into `inf.0`, and Rust's own `inf`
/// reloads silently as an identifier. Only the `<=>` spelling: a fact cannot write one
/// that loads as the Float yet (the loader does not fold a const in fact data). Fails
/// when `write_literal`'s two non-finite arms are backed out.
#[test]
fn a_non_finite_float_prints_its_const_name() {
    assert_eq!(answer("eq_inf"), "Float.infinity");
    assert_eq!(answer("eq_ninf"), "Float.negativeInfinity");
    assert_eq!(answer("eq_nan"), "Float.nan");
}

/// Passes either way, by design.
#[test]
fn int_bigint_and_bool_agree() {
    both_spellings_print("i", "7");
    both_spellings_print("b", "123456789012345678901234567890");
    both_spellings_print("t", "true");
}
