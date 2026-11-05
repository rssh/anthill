//! WI-906 — `@[unfold]` is not a rewrite tag; `@[simp]` is the one enablement
//! (kernel-language.md §5.3).
//!
//! WHAT IT WAS. A second tag that enabled an equation at the RESOLVER alone
//! (`fire_simp_equation` accepted `@[simp]` OR `@[unfold]`) and never at the typer
//! (`simp_rewrite::is_simp_equation` was `@[simp]`-only). No sentence of the spec said
//! how the two differed; the difference was which predicate each firing site asked, and
//! nothing in the standard library or the examples used it. MEASURED while deciding: an
//! `@[unfold]` DOT rule fired at no dot call a program writes (`?h.bump(5)` in an
//! operation body or a rule body answered "no such member"). Removed by the user's
//! decision, 2026-11-05.
//!
//! WHY A REFUSAL AND NOT SILENCE. A block's keys are free-form (`@[Marker]` is data a
//! rule body can read), so with the tag gone nothing would read `unfold` — an equation
//! that carried it would load as an untagged, inert law, with no diagnostic. It is
//! refused instead, by the converter (`parse::convert`'s `convert_meta_entry`), which
//! every written entry passes through: a proof step's block, which the loader never
//! lowers, included. Keyed by the key's LAST segment, as the loader stores a key.
//!
//! CONTROLS. Every refusal row FAILS with that check backed out: the source parses and
//! loads clean (an equation's law inert). `the_same_equation_under_simp_runs` and
//! `the_same_proof_step_without_the_tag_parses` pass either way by design.

use anthill_core::parse;

use crate::common::{parses_clean, run_int64};

/// `test.<name>`, holding `body`.
fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64}}\n  \
         import anthill.prelude.PartialEq.{{eq}}\n  fact a(1)\n{body}\nend\n"
    )
}

/// `src` fails to parse with exactly ONE error, the `@[unfold]` refusal, located at the
/// written key.
#[track_caller]
fn assert_unfold_refused(name: &str, src: &str) {
    let errs = match parse::parse(src) {
        Ok(_) => panic!("{name}: `@[unfold]` must be refused, but the source parsed clean"),
        Err(errs) => errs,
    };
    let [e] = errs.as_slice() else {
        panic!("{name}: expected the one `@[unfold]` refusal, got {errs:?}");
    };
    assert!(
        e.message.contains("`@[unfold]` is not a rewrite tag"),
        "{name}: expected the `@[unfold]` refusal, got {e:?}"
    );
    let at = &src[e.span.start as usize..e.span.end as usize];
    assert!(at.ends_with("unfold"), "{name}: the refusal must point at the key, not {at:?}");
}

/// ON AN EQUATION — where the tag used to mean something — in every spelling an
/// equation takes a tag: `rule` and `fact`, bodyless and guarded, alone, beside
/// `@[simp]`, and with a qualified key (stored by its last segment, so `@[a.unfold]` is
/// the same entry). Without the refusal each loads an inert law.
#[test]
fn unfold_on_an_equation_is_refused() {
    for (name, body) in [
        ("uf.rule", "  operation g(x: Int64) -> Int64 = x\n  rule g(?x) <=> 20 @[unfold]"),
        ("uf.fact", "  operation h(x: Int64) -> Int64 = x\n  fact h(?x) <=> 30 @[unfold]"),
        (
            "uf.guarded",
            "  operation g(x: Int64) -> Int64 = x\n  rule g(?x) = 10 :- a(1) @[unfold]",
        ),
        (
            "uf.beside",
            "  operation g(x: Int64) -> Int64 = x\n  rule g(?x) <=> 20 @[simp, unfold]",
        ),
        (
            "uf.qualified",
            "  operation g(x: Int64) -> Int64 = x\n  rule g(?x) <=> 20 @[a.unfold]",
        ),
    ] {
        assert_unfold_refused(name, &ns(name, body));
    }
}

/// OFF AN EQUATION — where it was refused before, as a rewrite tag off an equation — it
/// is refused for itself.
#[test]
fn unfold_off_an_equation_is_refused_for_itself() {
    for (name, body) in [
        ("uf.op", "  operation g(x: Int64) -> Int64 = x @[unfold]"),
        ("uf.pred", "  rule p(?x) :- a(?x) @[unfold]"),
        ("uf.denial", "  rule ⊥ :- a(2) @[unfold]"),
        ("uf.plainfact", "  fact b(1) @[unfold]"),
        ("uf.constraint", "  constraint c: eq(?x, 1) :- a(?x) @[unfold]"),
        ("uf.sort", "  sort S = ? @[unfold]"),
        ("uf.entity", "  entity box(v: Int64) @[unfold]"),
        ("uf.const", "  const k: Int64 = 3 @[unfold]"),
    ] {
        assert_unfold_refused(name, &ns(name, body));
    }
}

/// A STRUCTURED PROOF's step takes a block too (`proof_step`'s `meta_block`), and the
/// loader never lowers it — a step is encoded from its label, heads and body alone. So a
/// refusal placed at the loader's lowering missed it (found by `/code-review`); at the
/// converter it does not.
const PROOF_SRC: &str = "namespace test.uf.proof\n  \
     rule lemma_x: gte(?x, 0.0) :- gte(?x, 5.0)\n  \
     proof lemma_x\n    \
     rule h1: gte(?x, 3.0) :- gte(?x, 5.0) TAG by z3(logic: \"LRA\")\n  \
     end\nend\n";

#[test]
fn unfold_on_a_proof_step_is_refused() {
    assert_unfold_refused("uf.proof", &PROOF_SRC.replace("TAG", "@[unfold]"));
}

/// The control for the row above: the same step with no tag parses, so the refusal is
/// the tag's and not the fixture's.
#[test]
fn the_same_proof_step_without_the_tag_parses() {
    parses_clean(&PROOF_SRC.replace("TAG", ""));
}

/// The refusal names the tag, the ticket, and the spelling to write instead. (It is a
/// PARSE error, so the file never reaches the loader — which is also why this reads
/// `parse::parse` rather than a load helper: those treat an unparsable user source as a
/// broken fixture and panic.)
#[test]
fn the_refusal_says_what_to_write() {
    let src = ns(
        "uf.msg",
        "  operation g(x: Int64) -> Int64 = x\n  rule g(?x) <=> 20 @[unfold]",
    );
    let errs = match parse::parse(&src) {
        Ok(_) => panic!("`@[unfold]` must be refused"),
        Err(errs) => errs,
    };
    let [e] = errs.as_slice() else {
        panic!("expected one error, got {errs:?}");
    };
    for needle in ["`@[unfold]`", "WI-906", "`@[simp]`"] {
        assert!(e.message.contains(needle), "the refusal must mention {needle}: {e:?}");
    }
}

/// The equation the first row refuses, tagged `@[simp]`: it loads and runs. Passes
/// either way by design — it is the control that the refusal is the TAG's, not the
/// equation's.
#[test]
fn the_same_equation_under_simp_runs() {
    let src = ns(
        "uf.simp",
        "  operation g(x: Int64) -> Int64 = x\n  rule g(?x) <=> 20 @[simp]\n  \
         operation run() -> Int64 = g(1)",
    );
    assert_eq!(run_int64(&src, "test.uf.simp.run"), Ok(20));
}
