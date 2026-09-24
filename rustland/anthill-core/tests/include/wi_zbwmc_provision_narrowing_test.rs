//! WI-20260923-ZBWMC — a PROVISION narrows the bare-spec sugar inside its carrier; only a
//! provision does; and where the carrier's provisions do not agree, the sugar is refused.
//!
//! WI-201's carrier-in-scope narrowing makes `Spec.Member`, written in an operation
//! signature inside a carrier that provides `Spec[Member = X]`, mean `X` — the Rust
//! `impl Spec for C { type Member = X; … Self::Member … }` reading. The bindings are
//! pre-scanned from the block the operation stands in (`scan_sort_carrier_bindings`), and
//! that scan had two arms that had each drifted from the one spelling of a provision:
//!
//! * its `provides` arm was DEAD. It gated on the head of the lowered spec, which is
//!   the `anthill.reflect.SortView` wrapper rather than the spec, so every parameterized
//!   provision was skipped as a non-spec and recorded nothing;
//! * its `fact` arm still narrowed, from `fact Spec[Member = X]` — the spelling
//!   WI-20260917-S8JYF retired as a provision. Inside a sort that no longer provides
//!   the spec, a plain fact kept deciding what a type in a signature meant.
//!
//! So the retired spelling was the only one that narrowed. MEASURED before the fix:
//! `provides Store[State = WIS]` left a body reading `s.n` off an `s: Store.State`
//! refused, while `fact Store[State = WIS]` in the same place loaded and ran.
//!
//! Making the arm live made the rest of the narrowing reachable, and the review of it
//! measured what that exposed — each has a section below: a carrier the operation could
//! not spell (another sort's abstract member, a family, an operation), several bindings
//! for one member (a later provision re-admitted a dropped one), a binding written in
//! another block of the same sort (059: a sort's provisions are the sort's wherever they
//! are written), a nested namespace inheriting the sort's narrowing, and a spec gate that
//! read a symbol's FIRST-declared kind. And two things the scan did beside the narrowing:
//! it converted every sort-body fact head before `load_fact` did, and it lowered each
//! provision spec a second time.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! ELEVEN BACK-OUTS, each PRESENT-BUT-WRONG rather than deleted, and each APPLIED AND RUN
//! twice: over the WHOLE `wi_tests` binary (5 039 rows run, 3 ignored), where no row outside
//! this file, `wi201_bare_spec_member_sugar_test` (`W201` below) and
//! `parameterized_provides_block_test` failed under any of them; and again over those three
//! files once every arm of a looped row had become a row of its own — the population the
//! lists below name, exhaustively. Every row not named passed.
//!
//! **1 — THE PRE-FIX GATE**: the spec read off the lowered view's own head, the `SortView`
//! wrapper, so nothing narrows. **17 ROWS**: every row here that needs a narrowing —
//! [`a_provision_narrows_the_spec_member_to_its_carrier`],
//! [`a_positional_provision_narrows_like_the_named_one`],
//! [`a_provision_written_after_its_users_still_narrows`],
//! [`a_secondary_entry_narrows_from_its_own_provision`],
//! [`a_value_carrying_provision_narrows_its_type_member`],
//! [`a_spec_whose_namespace_entry_comes_first_still_narrows`],
//! [`the_providing_sorts_own_parameter_is_a_carrier`] — the five ambiguity rows (with no
//! narrowing there is nothing to refuse), and W201's five: `carrier_in_scope_narrows_to_bound_type`,
//! `…_narrowing_is_real`, `…_is_order_independent`, `…_positional_binding`,
//! `conflicting_carrier_bindings_do_not_narrow`.
//!
//! **2 — THE `fact` ARM**, restored beside the fixed one. **3 ROWS**:
//! [`a_fact_spelled_claim_does_not_narrow`] (the fact narrows again and the program loads),
//! and both sort-body fact rows, [`an_omitted_option_in_a_sort_body_fact_is_none`] and
//! [`an_undefined_head_argument_in_a_sort_body_fact_is_refused`] — the arm's conversion,
//! memoized, is what `load_fact` read.
//!
//! **3 — THE `kind_of` SPEC GATE.** **1 ROW**:
//! [`a_spec_whose_namespace_entry_comes_first_still_narrows`].
//!
//! **4 — NO WHOLE-SORT CHECK** (`check_bare_spec_narrowings` not run). **6 ROWS**: the five
//! ambiguity rows — [`two_bindings_in_one_block_are_an_ambiguity`],
//! [`a_third_provision_does_not_readmit_a_carrier`],
//! [`a_binding_in_an_entry_makes_the_bodys_narrowing_ambiguous`],
//! [`a_binding_in_the_body_makes_an_entrys_narrowing_ambiguous`],
//! [`a_family_beside_a_carrier_is_an_ambiguity`] — and W201's
//! `conflicting_carrier_bindings_do_not_narrow`.
//!
//! **5 — THE HEAD-ONLY CARRIER TEST** (`Ref | Ident | Fn` at the top). **4 ROWS**: the four
//! `…_keeps_the_generic_reading` rows, each narrowing to what no signature could spell.
//!
//! **6 — A NAMESPACE THAT SCANS NOTHING** (a `namespace <Sort>` entry installs no block).
//! **2 ROWS**: [`a_secondary_entry_narrows_from_its_own_provision`] and
//! [`a_binding_in_the_body_makes_an_entrys_narrowing_ambiguous`].
//!
//! **7 — A NAMESPACE THAT INHERITS** its enclosing block, as the loader stood (so it also
//! scans nothing). **3 ROWS**: [`a_namespace_nested_in_a_sort_body_does_not_narrow`], and
//! 6's two.
//!
//! **8 — A SECOND LOWERING** (`load_provides_clause` lowering afresh). **1 ROW**:
//! [`a_described_provision_binding_is_described_once`].
//!
//! **9 — NO DUPLICATE CHECK** in a spec clause. **2 ROWS**:
//! [`a_name_bound_twice_in_a_provision_is_refused`],
//! [`a_name_bound_twice_in_a_requirement_is_refused`].
//!
//! **10 — A BINDING BLOCK READ OFF ITS SPEC'S HEAD** (`provides_block_identity`). **1 ROW**, in
//! `parameterized_provides_block_test`: `a_parameterized_binding_block_is_about_its_base_spec`.
//!
//! **11 — HASH-CONSED VIEWS ONLY** (the scan skipping a value-carried spec). **1 ROW**:
//! [`a_value_carrying_provision_narrows_its_type_member`].
//!
//! **PASS UNDER ALL ELEVEN, BY DESIGN** — the baselines:
//! [`the_own_parameter_written_directly_is_the_baseline`], [`no_claim_is_the_generic_reading`],
//! [`the_carrier_written_directly_is_not_ambiguous`],
//! [`an_omitted_option_in_a_namespace_fact_is_none`],
//! [`an_undefined_head_argument_in_a_namespace_fact_is_refused`],
//! [`distinct_names_in_a_spec_clause_are_not_a_duplicate`], and
//! `parameterized_provides_block_test`'s `a_bare_binding_block_is_about_its_spec`.

use crate::common::{assert_refused_naming, definite_unary, interp_for, try_load_kb_with};
use anthill_core::eval::Value;

// ── the fixture ────────────────────────────────────────────────────────────────────────

/// A spec `Store` with a sole type member `State`, two state shapes `WIS` / `WIS2`, and a
/// carrier `FileStore` whose sort body is `body`, followed — when `entry` is not empty —
/// by a `namespace FileStore` secondary entry holding `entry`. `prelude` is written
/// before the spec. `go()` returns `FileStore.count(wis(n: 7))`.
fn program(ns: &str, prelude: &str, body: &str, entry: &str) -> String {
    let entry = if entry.is_empty() {
        String::new()
    } else {
        format!("  namespace FileStore\n{entry}\n  end\n")
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}
{prelude}
  sort Store
    sort State = ?
    operation peek(s: State) -> Bool
  end

  sort WIS
    entity wis(n: Int64)
  end

  sort WIS2
    entity wis2(n: Int64)
  end

  sort FileStore
{body}
  end
{entry}
  operation go() -> Int64 = FileStore.count(wis(n: 7))
end
"#
    )
}

/// `FileStore`'s two operations, both written through the sugar: `peek`, the spec member
/// it implements, and `count`, which reads the field `n` off its parameter. That read
/// typechecks only if `Store.State` IS `WIS` here — an abstract carrier has no `n`.
fn ops(ty: &str) -> String {
    format!(
        "    operation peek(s: {ty}) -> Bool = true\n    \
         operation count(s: {ty}) -> Int64 = s.n"
    )
}

const PROVIDES_WIS: &str = "    provides Store[State = WIS]";

/// The sugar, in a block of `FileStore`.
fn sugar() -> String {
    ops("Store.State")
}

fn body_with(claims: &[&str]) -> String {
    let mut lines: Vec<String> = claims.iter().map(|c| format!("    {c}")).collect();
    lines.push(sugar());
    lines.join("\n")
}

/// Load `src`, call `ns.go()`, and return its `Int64`.
fn run(ns: &str, src: &str) -> i64 {
    let mut interp = interp_for(src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}"),
    }
}

fn load_errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// The refusal the GENERIC reading gets: `Store.State` is the existential `?State`, which
/// has no `n`. The mark of "did not narrow" — and, beside the negative, of "was not the
/// ambiguity refusal either".
fn assert_generic(errs: &[String], why: &str) {
    assert_refused_naming(errs, &["?State.n", "declare no 'n'"], why);
    assert!(
        !errs.iter().any(|e| e.contains("names no one type")),
        "{why}: this is the generic reading, not an ambiguity: {errs:#?}"
    );
}

/// The ambiguity refusal, naming every binding the carrier gives `State`.
fn assert_ambiguous(errs: &[String], bound: &str, why: &str) {
    assert_refused_naming(
        errs,
        &["`Store.State` names no one type", &format!("bound to {bound}")],
        why,
    );
}

// ── a provision narrows ────────────────────────────────────────────────────────────────

/// THE PROVISION NARROWS: inside `FileStore provides Store[State = WIS]`, `Store.State`
/// is `WIS`, so `count` reads `s.n` and the call returns the field. Under the pre-fix gate
/// the load is refused twice over: at `s.n` ("the specs constraining it declare no 'n'"),
/// and at `peek`, whose un-narrowed signature `requires` what the spec's does not.
#[test]
fn a_provision_narrows_the_spec_member_to_its_carrier() {
    let ns = "wizbwmc.named";
    assert_eq!(run(ns, &program(ns, "", &body_with(&[PROVIDES_WIS.trim()]), "")), 7);
}

/// A POSITIONAL provision records the same carrier as the named one: the lowering maps
/// `Store[WIS]` onto the spec's declared parameter, so the scan reads a named binding
/// either way.
#[test]
fn a_positional_provision_narrows_like_the_named_one() {
    let ns = "wizbwmc.pos";
    assert_eq!(run(ns, &program(ns, "", &body_with(&["provides Store[WIS]"]), "")), 7);
}

/// The provision may FOLLOW the operations that use it: the scan reads the parse items
/// before the body loads, so source order decides nothing.
#[test]
fn a_provision_written_after_its_users_still_narrows() {
    let ns = "wizbwmc.after";
    let body = format!("{}\n{PROVIDES_WIS}", sugar());
    assert_eq!(run(ns, &program(ns, "", &body, "")), 7);
}

/// A `namespace <Sort>` SECONDARY ENTRY is the sort's block too (059), so a provision
/// written in one narrows the operations written beside it.
#[test]
fn a_secondary_entry_narrows_from_its_own_provision() {
    let ns = "wizbwmc.entry";
    let entry = format!("{PROVIDES_WIS}\n{}", sugar());
    assert_eq!(run(ns, &program(ns, "", "", &entry)), 7);
}

/// A provision whose spec carries a VALUE binding (`Sized[WIS, 3]`: the `3` is a
/// value-in-type) lowers to a value-carried view, which the scan decodes through the
/// carrier-agnostic view reader: the TYPE member it binds still narrows, and the value
/// binding stays out of it. The old scan read hash-consed views only and skipped this
/// one whole.
#[test]
fn a_value_carrying_provision_narrows_its_type_member() {
    let ns = "wizbwmc.valued";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Sized
    sort T = ?
    sort N = ?
  end
  sort WIS
    entity wis(n: Int64)
  end
  sort Carrier
    provides Sized[WIS, 3]
    operation count(s: Sized.T) -> Int64 = s.n
  end
  operation go() -> Int64 = Carrier.count(wis(n: 7))
end
"#
    );
    assert_eq!(run(ns, &src), 7);
}

/// The spec's name may be declared as a namespace FIRST (a secondary entry of the spec
/// written before `sort Store`). The scan's old spec gate asked `kind_of` — the
/// first-declared kind, documented display-only — so that order read the spec as a
/// namespace and turned narrowing off, and across files the CLI's file-name order decided
/// it (MEASURED). The gate is gone: the sugar's own gate (`has_kind`) is the one that
/// fires.
#[test]
fn a_spec_whose_namespace_entry_comes_first_still_narrows() {
    let ns = "wizbwmc.specfirst";
    let src = program(ns, "  namespace Store\n  end", &body_with(&[PROVIDES_WIS.trim()]), "");
    assert_eq!(run(ns, &src), 7);
}

/// `Box`, providing `Store[State = T]` at its own type parameter, with `badT(s: {ty}) ->
/// Int64 = s` — refused at `s`'s type, which is what this pair reads.
fn own_parameter_program(label: &str, ty: &str) -> String {
    format!(
        r#"
namespace wizbwmc.ownparam.{label}
  import anthill.prelude.{{Int64, Bool}}
  sort Store
    sort State = ?
  end
  sort Box
    sort T = ?
    provides Store[State = T]
    operation badT(s: {ty}) -> Int64 = s
  end
end
"#
    )
}

/// A carrier bound to the providing sort's OWN type parameter narrows to that parameter —
/// the same type writing `T` there gives: returning it as an `Int64` is refused as `?T`,
/// not as the generic `?State`. The admissibility check must keep this while it refuses
/// another sort's abstract member (the four rows below).
#[test]
fn the_providing_sorts_own_parameter_is_a_carrier() {
    let errs = load_errors(&own_parameter_program("sugar", "Store.State"));
    assert_refused_naming(&errs, &["expected Int64, got ?T"], "the sugar");
}

/// THE BASELINE for the row above: `T` written directly. It never reads the sugar.
#[test]
fn the_own_parameter_written_directly_is_the_baseline() {
    let errs = load_errors(&own_parameter_program("direct", "T"));
    assert_refused_naming(&errs, &["expected Int64, got ?T"], "the direct spelling");
}

// ── only a provision narrows, and only to a type the block could spell ────────────────

/// THE PIN: a `fact Store[State = WIS]` in the carrier's body is not a provision
/// (S8JYF), so it lends no carrier member, and `Store.State` stays the existential —
/// `s.n` is refused exactly as it is with no claim at all (the next row).
#[test]
fn a_fact_spelled_claim_does_not_narrow() {
    let src = program("wizbwmc.pinfact", "", &body_with(&["fact Store[State = WIS]"]), "");
    assert_generic(&load_errors(&src), "a fact");
}

/// THE BASELINE for the pin: no claim at all, the sugar's generic reading.
#[test]
fn no_claim_is_the_generic_reading() {
    let src = program("wizbwmc.pinnone", "", &body_with(&[]), "");
    assert_generic(&load_errors(&src), "no claim");
}

/// `provides Store[State = {bound}]` beside the sugar, with `Other` (declaring an abstract
/// member `X`) and an operation `helper` in scope.
fn unspellable(label: &str, bound: &str) -> Vec<String> {
    let prelude = "  import anthill.prelude.List\n  \
                   sort Other\n    sort X = ?\n  end\n  \
                   operation helper(x: Int64) -> Int64 = x";
    let body = body_with(&[&format!("provides Store[State = {bound}]")]);
    load_errors(&program(&format!("wizbwmc.unspellable.{label}"), prelude, &body, ""))
}

/// A carrier NO SIGNATURE HERE COULD SPELL keeps the generic reading. Another sort's
/// abstract member is the one that was unsound: the typer reads it as a free parameter,
/// so narrowing to it let `idWis(s: Store.State) -> WIS = s` load and
/// `FileStore.idWis(5).n` die at run time (MEASURED), where the same text written `s:
/// Other.X` is refused at load.
#[test]
fn another_sorts_abstract_member_keeps_the_generic_reading() {
    assert_generic(&unspellable("foreign", "Other.X"), "Other.X");
}

/// ... and the spec's own abstract member, the same way.
#[test]
fn the_specs_own_member_keeps_the_generic_reading() {
    assert_generic(&unspellable("specown", "Store.State"), "Store.State");
}

/// ... a FAMILY (`List[T = ?]`), a variable no operation's `type_params` holds. The old
/// head-only test took it and refused `idAny(s: Store.State) -> Store.State = s` as
/// returning another `List` than it took (MEASURED: `expected List[T = ?_], got List[T =
/// s.T]`), where the generic reading loads.
#[test]
fn a_family_keeps_the_generic_reading() {
    assert_generic(&unspellable("family", "List[T = ?]"), "List[T = ?]");
}

/// ... and an operation (`helper`), which is not a type at all.
#[test]
fn an_operation_keeps_the_generic_reading() {
    assert_generic(&unspellable("operation", "helper"), "helper");
}

/// A plain namespace nested in a sort body is not the sort's block: its operations are
/// not the sort's, so the sort's provision does not narrow there. (A nested SORT already
/// started from its own block; a namespace inherited its parent's.)
#[test]
fn a_namespace_nested_in_a_sort_body_does_not_narrow() {
    let ns = "wizbwmc.nested";
    let body = format!(
        "{PROVIDES_WIS}\n    namespace Helpers\n  {}\n    end\n    \
         operation count(s: WIS) -> Int64 = s.n",
        ops("Store.State").replace("peek", "peekH")
    );
    assert_generic(&load_errors(&program(ns, "", &body, "")), "nested");
}

// ── where the carrier's provisions disagree, the sugar is refused ──────────────────────

/// SEVERAL BINDINGS IN ONE BLOCK: `Store.State` names no one type, which design §5.3
/// calls a loud ambiguity. It used to fall back to the generic reading without a word.
#[test]
fn two_bindings_in_one_block_are_an_ambiguity() {
    let claims = ["provides Store[State = WIS]", "provides Store[State = WIS2]"];
    let src = program("wizbwmc.several.two", "", &body_with(&claims), "");
    assert_ambiguous(&load_errors(&src), "WIS, WIS2", "two");
}

/// A THIRD PROVISION DOES NOT RE-ADMIT A CARRIER. The old rule DROPPED a conflicting
/// entry and remembered nothing, so the next provision found it vacant: WIS, WIS2, WIS
/// narrowed to WIS and loaded clean, and three different carriers narrowed to the last
/// (MEASURED) — the source-order winner the rule's own comment said it avoided.
#[test]
fn a_third_provision_does_not_readmit_a_carrier() {
    let claims = [
        "provides Store[State = WIS]",
        "provides Store[State = WIS2]",
        "provides Store[State = WIS]",
    ];
    let src = program("wizbwmc.several.aba", "", &body_with(&claims), "");
    assert_ambiguous(&load_errors(&src), "WIS, WIS2", "aba");
}

/// A BINDING WRITTEN IN ANOTHER BLOCK of the same sort makes the narrowing wrong: the
/// body narrows from its own provision, and only once every file has loaded can the check
/// see the entry's. MEASURED before the check: the body's `WIS` narrowed, and a call with
/// a `WIS2` was refused `expected WIS, got WIS2` — swapping where the provisions stood
/// swapped the carrier.
#[test]
fn a_binding_in_an_entry_makes_the_bodys_narrowing_ambiguous() {
    let src = program(
        "wizbwmc.split.body",
        "",
        &body_with(&[PROVIDES_WIS.trim()]),
        "    provides Store[State = WIS2]",
    );
    assert_ambiguous(&load_errors(&src), "WIS, WIS2", "sugar in the body");
}

/// ... and the reverse: the sugar in the entry, the other binding in the body. The
/// relation lists the body's provision first, as it loaded first.
#[test]
fn a_binding_in_the_body_makes_an_entrys_narrowing_ambiguous() {
    let entry = format!("{PROVIDES_WIS}\n{}", sugar());
    let src = program("wizbwmc.split.entry", "", "    provides Store[State = WIS2]", &entry);
    assert_ambiguous(&load_errors(&src), "WIS2, WIS", "sugar in the entry");
}

/// A FAMILY BESIDE A CARRIER: `provides Store[State = ?x]` provides the spec at every
/// state, and `provides Store[State = WIS]` at one — two bindings, so an ambiguity like
/// any other. The old rule skipped the family before comparing and narrowed to `WIS`
/// (MEASURED: a call passing another type was refused `expected WIS, got B`).
#[test]
fn a_family_beside_a_carrier_is_an_ambiguity() {
    let claims = ["provides Store[State = ?x]", PROVIDES_WIS.trim()];
    let src = program("wizbwmc.family", "", &body_with(&claims), "");
    assert_ambiguous(&load_errors(&src), "?x, WIS", "family");
}

/// THE BASELINE for the ambiguity rows: the carrier written where the sugar was, under
/// two conflicting provisions (one in the body, one in the entry). It never reads the
/// sugar, so the ambiguity check has nothing to say, and it runs. It writes no `peek`:
/// one member cannot fit the spec's `peek` at both `WIS` and `WIS2`, which the member-fit
/// check would refuse, and a spec member without a body is not owed by its provider.
#[test]
fn the_carrier_written_directly_is_not_ambiguous() {
    let ns = "wizbwmc.ctl";
    let body = format!("{PROVIDES_WIS}\n    operation count(s: WIS) -> Int64 = s.n");
    let src = program(ns, "", &body, "    provides Store[State = WIS2]");
    assert_eq!(run(ns, &src), 7);
}

// ── what the scan did beside the narrowing ─────────────────────────────────────────────
//
// A SORT-BODY FACT LOADS LIKE A NAMESPACE-LEVEL ONE. The scan's `fact` arm converted every
// fact head of a sort body before the body loaded, with none of `load_fact`'s context;
// `convert_term` memoizes per parse node, so `load_fact` got that conversion back, and a
// sort-body fact escaped two rules its namespace twin obeys (MEASURED, a release build from
// before the change): WI-716 — an omitted `Option` field is `none` (the sort-body `fact
// rec(id: 1)` stored `note: ?note`, so `rec(id: 1, note: some(?))` answered); and B8ESG —
// a head argument naming nothing is refused (`fact stored(cons(…))`, `cons` not imported,
// loaded). Each rule is a pair below: the sort-body row, and its namespace twin as the
// baseline, which was right before and after.

/// `rec(id: 1)` with its `Option` field omitted, written inside `sort Holder` or at
/// namespace level, and two relations over it.
fn omitted_option(label: &str, open: &str, close: &str) -> (Vec<Option<i64>>, usize) {
    let ns = format!("wizbwmc.facts.{label}");
    let src = format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Option}}\n  \
         import anthill.prelude.Option.{{none, some}}\n  \
         sort Rec\n    entity rec(id: Int64, note: Option[T = Int64])\n  end\n\
         {open}  fact rec(id: 1)\n{close}  \
         rule noted(?i) :- rec(id: ?i, note: some(?))\n  \
         rule unnoted(?i) :- rec(id: ?i, note: none)\nend\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    let unnoted = definite_unary(&mut kb, &format!("{ns}.unnoted"));
    let unnoted = unnoted
        .iter()
        .map(|v| crate::common::scalar_int(&kb, v))
        .collect();
    (unnoted, definite_unary(&mut kb, &format!("{ns}.noted")).len())
}

#[test]
fn an_omitted_option_in_a_sort_body_fact_is_none() {
    let (unnoted, noted) = omitted_option("body", "  sort Holder\n", "  end\n");
    assert_eq!(unnoted, vec![Some(1)], "the fact is there, and its omitted note is `none`");
    assert_eq!(noted, 0, "`none` does not match `some(?)`");
}

/// THE BASELINE for the row above.
#[test]
fn an_omitted_option_in_a_namespace_fact_is_none() {
    let (unnoted, noted) = omitted_option("ns", "", "");
    assert_eq!(unnoted, vec![Some(1)], "the fact is there, and its omitted note is `none`");
    assert_eq!(noted, 0, "`none` does not match `some(?)`");
}

fn undefined_head_argument(label: &str, open: &str, close: &str) -> Vec<String> {
    load_errors(&format!(
        "namespace wizbwmc.b8.{label}\n  import anthill.prelude.{{Int64, List}}\n\
         {open}  fact stored(cons(head: 1, tail: nil))\n{close}end\n"
    ))
}

#[test]
fn an_undefined_head_argument_in_a_sort_body_fact_is_refused() {
    let errs = undefined_head_argument("body", "  sort Holder\n", "  end\n");
    assert_refused_naming(&errs, &["head argument term `cons` names nothing"], "body");
}

/// THE BASELINE for the row above.
#[test]
fn an_undefined_head_argument_in_a_namespace_fact_is_refused() {
    let errs = undefined_head_argument("ns", "", "");
    assert_refused_naming(&errs, &["head argument term `cons` names nothing"], "namespace");
}

/// ONE WRITTEN DESCRIPTION, ONE FACT. The scan lowered each provision spec, and
/// `load_provides_clause` lowered it again; a described binding emits its
/// `DescriptionInfo` per lowering, and nothing collapses a fact the way the rendering
/// dedup collapses a report, so a sort-body provision described its binding twice
/// (`index: 0` and `index: 1`, MEASURED) while the same clause at namespace level
/// described it once. The pre-scan's lowering is now the one the provision takes.
#[test]
fn a_described_provision_binding_is_described_once() {
    let src = "namespace wizbwmc.desc\n  import anthill.prelude.{Int64}\n  \
               sort Store\n    sort State = ?\n  end\n  \
               sort FileStore\n    provides Store[State = ?x {< the zbwmc carrier >}?]\n  end\nend\n";
    let kb = crate::common::load_kb_with(src);
    let desc = kb
        .try_resolve_symbol("anthill.reflect.DescriptionInfo")
        .expect("DescriptionInfo is declared");
    let written = kb
        .rules_by_functor(desc)
        .iter()
        .filter(|&&rid| {
            let head = kb.rule_head_value(rid);
            let content = crate::common::entity_field(&kb, head, "content", 1);
            crate::common::scalar_str(&kb, &content).as_deref() == Some("the zbwmc carrier")
        })
        .count();
    assert_eq!(written, 1, "one written description, one fact");
}

/// `sort Holder { {clause} }` over a two-parameter spec `Pair2`.
fn spec_clause(label: &str, clause: &str) -> Vec<String> {
    load_errors(&format!(
        "namespace wizbwmc.dup.{label}\n  import anthill.prelude.{{Int64, Bool}}\n  \
         sort Pair2\n    sort A = ?\n    sort B = ?\n  end\n  \
         sort Holder\n    {clause}\n  end\nend\n"
    ))
}

/// A NAME BOUND TWICE IN A SPEC CLAUSE is refused. It used to load, and the two view
/// decoders then read it differently — the term one kept both values, the value one read
/// the first twice — so whether the sugar narrowed turned on whether some OTHER binding of
/// the clause was denoted (MEASURED). A type position already refused it (WI-764); a
/// clause may also bind operations by name, so only this part of that check applies there.
#[test]
fn a_name_bound_twice_in_a_provision_is_refused() {
    let errs = spec_clause("provides", "provides Pair2[A = Int64, A = Bool]");
    assert_refused_naming(&errs, &["binds the type parameter 'A' more than once"], "provides");
}

/// ... and in a `requires` clause, which lowers through the same door.
#[test]
fn a_name_bound_twice_in_a_requirement_is_refused() {
    let errs = spec_clause("requires", "requires Pair2[A = Int64, A = Bool]");
    assert_refused_naming(&errs, &["binds the type parameter 'A' more than once"], "requires");
}

/// THE BASELINE: distinct names are not a duplicate.
#[test]
fn distinct_names_in_a_spec_clause_are_not_a_duplicate() {
    let errs = spec_clause("ctl", "provides Pair2[A = Int64, B = Bool]");
    assert!(
        !errs.iter().any(|e| e.contains("more than once")),
        "distinct names are not a duplicate: {errs:#?}"
    );
}
