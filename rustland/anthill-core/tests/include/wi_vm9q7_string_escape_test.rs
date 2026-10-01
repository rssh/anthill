//! WI-20260907-VM9Q7 — the `\u{HEX}` string escape (spec §2.4), and the loud refusal of
//! every escape the language does not define.
//!
//! WHY IT IS HERE. VM9Q7 made a literal answer print one way on every carrier, through
//! `write_literal` — and for a `String` that spelling wrote a control character RAW,
//! because the language had no escape to spell one: `anthill query` over a fact holding
//! ESC put a live terminal sequence on stdout. The escape closes that, and the encoder
//! (`write_anthill_string`) and decoder (`parse::convert::decode_string_escapes`) are one
//! contract, so this file drives them through each other: printed text, parsed back.
//!
//! An UNKNOWN escape used to pass its trailing char through — `"\u{1b}"` read as
//! `"u{1b}"`, a different string with nothing said — so the escape could not be added
//! without making the refusal loud first.
//!
//! ── CONTROL ─────────────────────────────────────────────────────────────
//!
//! Restore the pass-through decoder and ALL THREE fail:
//!   * `a_u_escape_reads_the_character_it_names` — `"au{1b}b"`;
//!   * `printed_text_reads_back_as_the_string` — the encoder's `\u{…}` reads back wrong;
//!   * `a_malformed_escape_is_refused_at_its_literal` — every row loads clean.
//!
//! Back out only the ENCODER's control-character escape and exactly ONE fails, measured:
//! `printed_text_reads_back_as_the_string`, on its no-raw-control-character assertion
//! — NOT on the round trip, which holds either way, since a raw control character in
//! source still reads as itself. So that row is two checks, one per half of the
//! contract. The encoder's product-path row is `anthill-cli`'s
//! `wi_vm9q7_literal_rendering_test`, where the raw character is what reaches the
//! terminal.

use anthill_core::persistence::print::write_anthill_string;

/// The sole definite `String` answer of `qn`.
fn sole_string(src: &str, qn: &str) -> String {
    let mut kb = crate::common::load_kb_with(src);
    let vs = crate::common::definite_unary(&mut kb, qn);
    match vs.as_slice() {
        [v] => crate::common::scalar_str(&kb, v)
            .unwrap_or_else(|| panic!("`{qn}` must answer a String, got {v:?}")),
        other => panic!("`{qn}` must answer ONE definite row; got {other:?}"),
    }
}

/// A one-fact program whose `value` answers the string `literal` spells.
fn program(ns: &str, literal: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.String\n  \
         sort S\n    entity s(v: String)\n  end\n  \
         fact s(v: {literal})\n  \
         rule value(?r) :- s(v: ?r)\n\
         end\n"
    )
}

/// Fails on a back-out.
#[test]
fn a_u_escape_reads_the_character_it_names() {
    for (literal, want) in [
        (r#""a\u{1b}b""#, "a\u{1b}b"),
        (r#""\u{0}""#, "\u{0}"),
        (r#""\u{1F600}""#, "\u{1F600}"),
        (r#""\u{10FFFF}""#, "\u{10FFFF}"),
        // Upper- and lower-case hex alike.
        (r#""\u{7F}\u{7f}""#, "\u{7f}\u{7f}"),
    ] {
        assert_eq!(
            sole_string(&program("vm9q7.read", literal), "vm9q7.read.value"),
            want,
            "{literal}"
        );
    }
}

/// THE CONTRACT: whatever the encoder prints, the parser reads back as the same string.
/// Covers every character class the encoder treats specially — the named escapes, C0
/// and C1 controls, DEL — beside ones it must leave alone. Fails on a back-out.
#[test]
fn printed_text_reads_back_as_the_string() {
    for original in [
        "plain",
        "quote \" and backslash \\",
        "newline \n return \r tab \t",
        "ESC \u{1b}[31mred\u{1b}[0m",
        "NUL \u{0} BEL \u{7} DEL \u{7f}",
        "C1 NEL \u{85} CSI \u{9b}",
        "non-ASCII é ✓ \u{1F600}",
        "a literal \\u{1b} stays text",
    ] {
        let mut literal = String::new();
        write_anthill_string(original, &mut literal);
        assert!(
            !literal.chars().any(char::is_control),
            "the printed literal holds no raw control character: {literal:?}"
        );
        assert_eq!(
            sole_string(&program("vm9q7.trip", &literal), "vm9q7.trip.value"),
            original,
            "printed as {literal}"
        );
    }
}

/// Every escape the language does not define is a PARSE error, located at the literal
/// and naming the escape — not a different string read silently. Fails on a back-out.
#[test]
fn a_malformed_escape_is_refused_at_its_literal() {
    for (literal, needle) in [
        (r#""a\qb""#, "unknown escape `\\q`"),
        (r#""\x1b""#, "unknown escape `\\x`"),
        (r#""\u1b""#, "malformed `\\u` escape"),
        (r#""\u{}""#, "malformed `\\u` escape"),
        (r#""\u{1234567}""#, "malformed `\\u` escape"),
        (r#""\u{+1b}""#, "malformed `\\u` escape"),
        (r#""\u{1b""#, "malformed `\\u` escape"),
        (r#""\u{d800}""#, "not a Unicode scalar value"),
        (r#""\u{110000}""#, "not a Unicode scalar value"),
    ] {
        let src = program("vm9q7.bad", literal);
        let errs = match anthill_core::parse::parse(&src) {
            Ok(_) => panic!("{literal} must be refused; it parsed clean"),
            Err(errs) => errs,
        };
        let hit = errs
            .iter()
            .find(|e| e.message.contains(needle))
            .unwrap_or_else(|| panic!("{literal}: expected `{needle}`, got {errs:#?}"));
        let (start, end) = (hit.span.start as usize, hit.span.end as usize);
        assert_eq!(
            &src[start..end],
            literal,
            "{literal}: located AT the literal; {hit:?}"
        );
        assert_eq!(
            errs.iter().filter(|e| e.message.contains(needle)).count(),
            1,
            "{literal}: reported once; {errs:#?}"
        );
    }
}
