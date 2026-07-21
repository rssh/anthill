//! WI-790 — the `_N` positional-field-label convention has ONE owner.
//!
//! `positional_label` / `positional_label_index` / `is_positional_label_at`
//! (intern.rs) are the sole spelling of the 1-based `_1, _2, _3` convention (spec
//! §4.5). It was written out at nine producers and five recognizers before, and
//! had drifted in two directions: `persistence/term_ser.rs` minted ZERO-based
//! keys, and three recognizers admitted the leading-zero `_01` that WI-786's
//! classifier (correctly) called a USER label.
//!
//! The rules themselves are unit-tested in `intern.rs`. These are the END-TO-END
//! consequences — what a store actually contains, what reading it back yields,
//! and what the two recognizers whose behaviour changed now decide.

use anthill_core::intern::{positional_label, positional_label_index, Symbol};
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::term_ser;

use smallvec::SmallVec;

/// `Triple` declares its first two fields under the synthetic names themselves,
/// which is what lets a mixed positional/named term reload through the ordinary
/// schema path: `load_entry` rejects a key absent from the schema, so without
/// these declarations the round trip would stop at `UnknownField` and could not
/// witness WHERE the slots land.
const TRIPLE_SRC: &str = r#"
namespace test.wi790
  import anthill.prelude.{String}
  sort Triple
    entity Triple(_1: String, _2: String, c: String)
  end
end
"#;

/// Assert `Triple("first", "second", c: "named")` — TWO positional args, so a
/// one-slot shift is OBSERVABLE. With a single positional arg the zero-based bug
/// only produced the unreachable `_0`; with two it also changed which value the
/// reachable `_1` names, and that is the half that silently corrupts.
fn assert_mixed_fact(kb: &mut KnowledgeBase) -> anthill_core::kb::RuleId {
    let functor = kb.try_resolve_symbol("test.wi790.Triple").expect("Triple resolved");
    let c_sym = kb.intern("c");
    let first = kb.alloc(Term::Const(Literal::String("first".into())));
    let second = kb.alloc(Term::Const(Literal::String("second".into())));
    let named = kb.alloc(Term::Const(Literal::String("named".into())));

    let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
    pos_args.push(first);
    pos_args.push(second);
    let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    named_args.push((c_sym, named));

    let term = kb.alloc(Term::Fn { functor, pos_args, named_args });
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("wi790_domain");
    kb.assert_fact(term, sort, domain, None)
}

fn serialize_mixed_fact(kb: &mut KnowledgeBase) -> String {
    let rid = assert_mixed_fact(kb);
    term_ser::serialize_json(kb, "test.wi790.Triple", &[rid]).expect("serialize_json")
}

/// The store's positional keys are the ones the convention mints, and the
/// zero-based key that no reader interprets is gone.
///
/// The key assertions go through `positional_label` rather than the literals
/// `_1`/`_2`, so they track the owner instead of re-spelling it a tenth time —
/// while the `_0` assertion pins the literal that must NEVER appear. `_0` is
/// outside the 1-based image, so every reader declines it: `field_access`
/// (eval/builtins.rs) maps `_N` to slot `N-1`, and `field_step_in_value`
/// (kb/load.rs) filtered `n >= 1`.
#[test]
fn positional_slots_serialize_under_their_minted_labels() {
    let mut kb = crate::common::load_kb_with(TRIPLE_SRC);
    let json = serialize_mixed_fact(&mut kb);
    let data = &serde_json::from_str::<serde_json::Value>(&json).expect("valid JSON")["data"];

    assert_eq!(data[positional_label(0)], serde_json::json!("first"));
    assert_eq!(data[positional_label(1)], serde_json::json!("second"));
    assert_eq!(data["c"], serde_json::json!("named"));
    assert!(!json.contains("\"_0\""), "zero-based positional key in store: {json}");
}

/// The ACCEPTANCE property: the slots reload to the SAME indices they were
/// written from — not merely that the round trip succeeds.
///
/// This is the half that was silently WRONG rather than merely unreadable. Under
/// the zero-based encoding `"second"` (source slot 1) was written under `_1`, and
/// `_1` denotes slot 0 everywhere else in the system, so a value that made this
/// round trip came back one slot to the left. Reading each key back through
/// `positional_label_index` — the same function every consumer now asks — is what
/// makes that visible: the assertion is on the INDEX each value answers to, not on
/// the key's spelling. Measured on the parent commit, this read
/// `[(None, "first"), (None, "named"), (Some(0), "second")]`.
#[test]
fn positional_slots_reload_to_the_same_indices() {
    let mut kb = crate::common::load_kb_with(TRIPLE_SRC);
    let json = serialize_mixed_fact(&mut kb);

    // Reload into a FRESH KB so nothing is answered by the terms still interned
    // from the write side.
    let mut reloaded = crate::common::load_kb_with(TRIPLE_SRC);
    let domain = reloaded.make_name_term("wi790_domain");
    let count = term_ser::load_json(&mut reloaded, &json, domain).expect("load_json");
    assert_eq!(count, 1, "one fact reloaded");

    let functor = reloaded.try_resolve_symbol("test.wi790.Triple").expect("Triple resolved");
    let facts = reloaded.rules_by_functor(functor);
    assert_eq!(facts.len(), 1, "exactly one reloaded Triple fact");

    // The reloaded fact is all-named (`load_entry` rebuilds by field name), so the
    // labels ARE the slot record. Decode each one through the convention.
    let head = reloaded.rule_head(facts[0]);
    let Term::Fn { named_args, .. } = reloaded.get_term(head) else {
        panic!("reloaded fact is not a Fn term");
    };
    let mut by_index: Vec<(Option<usize>, String)> = Vec::new();
    for &(sym, val) in named_args.iter() {
        let label = reloaded.resolve_sym(sym).to_string();
        let Term::Const(Literal::String(s)) = reloaded.get_term(val) else {
            panic!("field `{label}` is not a string literal");
        };
        by_index.push((positional_label_index(&label), s.to_string()));
    }
    by_index.sort();

    assert_eq!(
        by_index,
        vec![
            // `c` is a genuine name, not a slot — it decodes to no index.
            (None, "named".to_string()),
            (Some(0), "first".to_string()),
            (Some(1), "second".to_string()),
        ],
        "each value must answer to the index it was written from"
    );
}

// ── the recognizers the same routing narrowed ──────────────────
//
// Three of the five recognizers spelled a bare `parse::<usize>()` and so called
// the leading-zero `_01` synthetic, while WI-786's classifier called it a USER
// label. All now ask `is_positional_label_at`, and the decision went WI-786's
// way. Each behaviour below was MEASURED on both sides of the change.

/// `kb/typing.rs`'s `is_positional_tuple_names` decides whether two equal-arity
/// PARAMETER LISTS may zip by position — legitimate only when one side carries the
/// synthetic names and so makes no claim about which slot is which.
///
/// MEASURED: `(_01: Int64, _02: Int64) -> Int64` used to satisfy
/// `(p: Int64, q: Int64) -> Int64`, the one cell this change moves. It is now
/// refused, which is what makes `_01` a user label CONSISTENTLY: it lands with the
/// `(a: Int64, b: Int64)` control (refused, and refused before too), not with the
/// genuinely-synthetic controls.
#[test]
fn leading_zero_param_names_no_longer_zip_by_position() {
    fn loads(spelling: &str) -> bool {
        crate::common::try_load_kb_with(&format!(
            r#"
namespace test.wi790.params
  import anthill.prelude.{{Int64}}
  operation take2(f: (p: Int64, q: Int64) -> Int64) -> Int64 = f(1, 2)
  operation pass(g: {spelling}) -> Int64 = take2(g)
end
"#
        ))
        .is_ok()
    }

    // THE CHANGE: a leading-zero list makes a NAMED claim, so it must agree by
    // name like any other. Loaded before WI-790.
    assert!(
        !loads("(_01: Int64, _02: Int64) -> Int64"),
        "`_01, _02` is a user-named parameter list and must not zip against `p, q`"
    );
    // …and it now behaves exactly like this control, which was always refused.
    assert!(!loads("(a: Int64, b: Int64) -> Int64"), "control: user names must not zip");

    // The genuinely synthetic spellings still zip — the escape hatch is intact,
    // and narrowing it away would have been the easy over-correction here. All
    // three are positive cases, so one program covers them (each `load_kb_with`
    // re-parses the whole stdlib; the negatives above need their own, since a
    // refused operation fails the entire load).
    assert!(
        crate::common::try_load_kb_with(
            r#"
namespace test.wi790.params.ok
  import anthill.prelude.{Int64}
  operation take2(f: (p: Int64, q: Int64) -> Int64) -> Int64 = f(1, 2)
  operation positional(g: (Int64, Int64) -> Int64) -> Int64 = take2(g)
  operation synthetic(g: (_1: Int64, _2: Int64) -> Int64) -> Int64 = take2(g)
  operation matching(g: (p: Int64, q: Int64) -> Int64) -> Int64 = take2(g)
end
"#
        )
        .is_ok(),
        "positional, explicit `_1, _2`, and name-matching lists must all still zip"
    );
}

/// `persistence/print.rs`'s `is_positional_name` was the LOOSEST recognizer: any
/// `_` + digits at ANY index counted as positional, and the caller then ERASED the
/// label. Both losing shapes are asserted here as print-then-reparse IDENTITIES,
/// which is the property that actually matters — a printer that merely "keeps the
/// label" could still emit text the parser rejects.
///
/// MEASURED before the fix: `(_01: Int64, b: Int64)` and `(_2: Int64, b: Int64)`
/// BOTH printed as `(Int64, b: Int64)` — text the parser refuses outright for
/// mixing positional and named fields, so the printed form did not round-trip at
/// all; and where such text does reparse, slot 0 is minted `_1`, a silent RENAME.
///
/// This closes the printer half of the same divergence, which WI-789 filed
/// separately: narrowing the RULE fixes `_01`, threading the INDEX fixes `_2`, and
/// neither is a fix on its own.
#[test]
fn printer_round_trips_labels_outside_the_convention() {
    // All four spellings load, so ONE program covers them — `load_kb_with`
    // re-parses the entire stdlib per call (~0.5s), which four calls would pay
    // four times.
    let src = r#"
namespace test.wi790.print
  import anthill.prelude.{Int64}
  operation leading_zero(t: (_01: Int64, b: Int64)) -> Int64 = 0
  operation wrong_index(t: (_2: Int64, b: Int64)) -> Int64 = 0
  operation genuine(t: (Int64, Int64)) -> Int64 = 0
  operation underscore_name(t: (a: Int64, _b: Int64)) -> Int64 = 0
end
"#;
    let kb = crate::common::load_kb_with(src);
    let printed = |op: &str| -> String {
        let sym = kb.try_resolve_symbol(&format!("test.wi790.print.{op}")).expect("op symbol");
        let info = anthill_core::kb::op_info::lookup_operation_info(&kb, sym).expect("op info");
        match info.params.first().expect("param") {
            (_, anthill_core::eval::Value::Term { id, .. }) => {
                anthill_core::persistence::print::TermPrinter::new(&kb).print_term(*id)
            }
            (_, other) => panic!("param should be a ground type, got {other:?}"),
        }
    };

    // THE TWO FIXES. Each printing is the source text verbatim, so it reparses to
    // the same type rather than to a renamed one.
    assert_eq!(printed("leading_zero"), "(_01: Int64, b: Int64)", "`_01` is a user label");
    assert_eq!(printed("wrong_index"), "(_2: Int64, b: Int64)", "`_2` in slot 0 is a user label");

    // A genuine positional tuple still prints WITHOUT labels — the point of the
    // recognizer, and what a blunt "keep every `_` label" fix would have broken.
    assert_eq!(printed("genuine"), "(Int64, Int64)");
    // Control: a `_`-prefixed non-numeric label was never at risk.
    assert_eq!(printed("underscore_name"), "(a: Int64, _b: Int64)");
}

/// The printings above are not merely stable strings — they REPARSE, in the same
/// position, to a type that prints identically. That is the round trip WI-789
/// asked for, and the property the erased forms could not have: `(Int64, b:
/// Int64)` is rejected by the parser outright.
#[test]
fn printed_tuple_types_are_a_reparse_fixpoint() {
    let program = |spellings: [&str; 2]| {
        format!(
            r#"
namespace test.wi790.fix
  import anthill.prelude.{{Int64}}
  operation a(t: {}) -> Int64 = 0
  operation b(t: {}) -> Int64 = 0
end
"#,
            spellings[0], spellings[1]
        )
    };
    let printed_both = |src: &str| -> [String; 2] {
        let kb = crate::common::load_kb_with(src);
        ["a", "b"].map(|op| {
            let sym = kb.try_resolve_symbol(&format!("test.wi790.fix.{op}")).expect("op symbol");
            let info = anthill_core::kb::op_info::lookup_operation_info(&kb, sym).expect("op info");
            match info.params.first().expect("param") {
                (_, anthill_core::eval::Value::Term { id, .. }) => {
                    anthill_core::persistence::print::TermPrinter::new(&kb).print_term(*id)
                }
                (_, other) => panic!("param should be a ground type, got {other:?}"),
            }
        })
    };

    let gen1 = printed_both(&program(["(_01: Int64, b: Int64)", "(_2: Int64, b: Int64)"]));
    assert_eq!(gen1, ["(_01: Int64, b: Int64)", "(_2: Int64, b: Int64)"]);

    // Feed each printing back through the parser in the same position. Reaching
    // here at all proves the text PARSES; equality proves it means the same type.
    let gen2 = printed_both(&program([gen1[0].as_str(), gen1[1].as_str()]));
    assert_eq!(gen2, gen1, "printing must be a fixpoint — reparsing may not rename a field");
}
