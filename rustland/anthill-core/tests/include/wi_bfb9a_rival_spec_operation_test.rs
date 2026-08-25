//! WI-20260824-BFB9A — ONE SPEC OPERATION, ONE SYMBOL.
//!
//! A FREE-STANDING `operation` may not take a name that already denotes a SPEC
//! OPERATION at the address it is written. `wi521_prelude_test` holds the headline row
//! — `a_free_standing_eq_rivalling_the_spec_op_is_refused`, the INVERSION of the test
//! WI-521 wrote to demonstrate that such a declaration loads clean. THIS file holds a
//! row for each leg of `check_rival_spec_operations`, and each says which back-out
//! fails it.
//!
//! WHY A SEPARATE FILE: several of these are NEGATIVE rows — programs that must LOAD —
//! and a negative sharing a fixture with the positive arm cannot show which leg admitted
//! it.
//!
//! ONE KB RECIPE. Every row here goes through `crate::common::try_load_kb_with*`, which
//! is the same load `interp_for` builds on (stdlib + the `anthill-stl` host bindings,
//! parsed once per test binary). An earlier version of this file had its own stdlib-only
//! loader for the error half while driving the value half through `interp_for`, so the
//! two assertions of one test were about two different KBs — found by `/code-review`.

use anthill_core::eval::Value;
use anthill_core::kb::{load, KnowledgeBase};

/// The rendered load errors for the stdlib + `extra` ([] = clean).
fn errs_for(extra: &str) -> Vec<String> {
    crate::common::try_load_kb_with(extra)
        .err()
        .unwrap_or_default()
}

/// [`errs_for`] over several user files that KNOW THEIR PATHS — for the rows about two
/// files writing text at one address, where the diagnostic names the reading file.
fn errs_for_named(files: &[(&str, &str)]) -> Vec<String> {
    crate::common::try_load_kb_with_named_files(files)
        .err()
        .unwrap_or_default()
}

/// The subset of `errs` this rule raised. Keyed on the sentence's own opening rather
/// than on a name that appears in other diagnostics too: `PartialEq.eq` is named by the
/// override checks as well, so a `contains("eq")` filter would count theirs.
fn rival_errs(errs: &[String]) -> Vec<&String> {
    errs.iter()
        .filter(|e| e.contains("would declare a second symbol of that name"))
        .collect()
}

/// The CONTROL for the exemption that keeps the stdlib loadable: a same-named operation
/// declared as a SORT MEMBER is not a rival and loads clean. `Set.eq` / `Map.eq` /
/// `Pair.eq` / `TotalFloat.eq` are this shape, which is why the stdlib survives BFB9A —
/// and this row fails if the refusal is ever widened past free-standing declarations.
///
/// PASSES BOTH WITH AND WITHOUT THE REFUSAL, by design: it measures the exemption's
/// boundary, not the refusal. Its value is in what it would catch on a future widening.
///
/// AND IT DRIVES THE OPERATION, not merely loads it. Asserting `errs.is_empty()` alone
/// stays green if `eq` resolves to nothing at all; calling it proves the member is the
/// reachable `eq` for this carrier.
#[test]
fn a_sort_member_eq_is_not_a_rival() {
    let src = r#"
namespace test.bfb9a.carrier
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Box
    entity boxed(v: Int64)
    provides PartialEq[T = Box]
    operation eq(a: Box, b: Box) -> Bool = true
  end
  -- The driver: `true` here is only reachable through `Box`'s own member, since two
  -- DIFFERENT boxes are not structurally equal.
  operation use_eq() -> Bool = eq(boxed(1), boxed(2))
end
"#;
    let errs = errs_for(src);
    assert!(
        errs.is_empty(),
        "a carrier's own `eq`, declared as a sort member under `provides`, is the shape \
         the refusal tells authors to write and must load clean; got: {errs:?}"
    );
    let mut interp = crate::common::interp_for(src);
    let got = interp
        .call("test.bfb9a.carrier.use_eq", &[])
        .expect("the carrier's own eq must be callable");
    assert_eq!(
        format!("{got:?}"),
        "Bool(true)",
        "the carrier's member `eq` is what a call reaches — it returns `true` by \
         construction, where a structural equality on two different boxes would be \
         false; got {got:?}"
    );
}

/// A NAME THE SCOPE ANSWERS WITH SOMETHING ELSE IS A CAPTURE, NOT A RIVAL — the leg
/// that makes the rule ask what the name DENOTES rather than which table it is in.
///
/// With `import test.bfb9aarith.Arith.{add}` in scope, a bare `add` in that file never
/// denoted `anthill.prelude.Additive.add`, so declaring one does not rival the tier.
/// (What it DOES do is capture `test.bfb9aarith.Arith.add` — a real question, and
/// `check_name_captures`' rather than this pass's, which does not reach namespace level.)
///
/// THE PAIR IS THE MEASUREMENT, and only the pair: the second half is byte-identical but
/// for the import line, and IS refused. A single "loads clean" row would pass with the
/// whole rule deleted.
#[test]
fn an_imported_unrelated_add_is_a_capture_not_a_rival() {
    // The other `add` is a SORT MEMBER — a free-standing one would be a rival itself,
    // and `Arith` is not parametric, so `Arith.add` is not a spec operation either.
    const LIB: &str = r#"
namespace test.bfb9aarith
  import anthill.prelude.{Int64}
  sort Arith
    entity arith
    operation add(a: Int64, b: Int64) -> Int64 = 7
  end
end
"#;
    let shadowed = format!(
        r#"{LIB}
namespace test.bfb9a.shadow
  import anthill.prelude.{{Int64}}
  import test.bfb9aarith.Arith.{{add}}
  operation add(a: Int64) -> Int64 = 1
end
"#
    );
    let shadow_errs = errs_for(&shadowed);
    assert!(
        rival_errs(&shadow_errs).is_empty(),
        "a name an import already answers is a CAPTURE of that symbol, not a rival of \
         the tier; got: {shadow_errs:?}"
    );
    let bare = format!(
        r#"{LIB}
namespace test.bfb9a.shadow
  import anthill.prelude.{{Int64}}
  operation add(a: Int64) -> Int64 = 1
end
"#
    );
    let errs = errs_for(&bare);
    let rivals = rival_errs(&errs);
    assert_eq!(
        rivals.len(),
        1,
        "with the import removed the same declaration DOES rival `Additive.add` — this \
         half is what stops the row above from passing with the rule deleted; got: \
         {errs:?}"
    );
    assert!(
        rivals[0].contains("anthill.prelude.Additive.add"),
        "and it names the spec operation; got: {rivals:?}"
    );
}

/// AN IMPORT OF THE DECLARATION'S OWN SYMBOL IS NOT AN ANSWER, and one line of code
/// decided this the other way.
///
/// `resolve_captured_name` skips the scope's own locals, so a declaration normally does
/// not find itself — but an `import test.bfb9a.selfimp.{eq}` written INSIDE
/// `test.bfb9a.selfimp` reaches it through the import rung, and the previous cut of this
/// pass took that as "the name denotes something here" and stood down. MEASURED then:
/// this program produced 0 rival errors and the same program without the import
/// produced 1. One import line silenced the whole rule.
///
/// FAILS IF the candidate loop stops at `other == decl.sym` instead of CONTINUING past
/// it (the shape `check_name_captures` uses three functions away).
#[test]
fn an_import_of_the_declarations_own_symbol_does_not_silence_the_rule() {
    let with_import = r#"
namespace test.bfb9a.selfimp
  import anthill.prelude.{Bool, Int64}
  import test.bfb9a.selfimp.{eq}
  operation eq(a: Int64, b: Int64) -> Bool = false
end
"#;
    let without = r#"
namespace test.bfb9a.selfimp
  import anthill.prelude.{Bool, Int64}
  operation eq(a: Int64, b: Int64) -> Bool = false
end
"#;
    let with_errs = errs_for(with_import);
    assert_eq!(
        rival_errs(&with_errs).len(),
        1,
        "an import of the declaration's own symbol must not excuse it; got: {with_errs:?}"
    );
    let without_errs = errs_for(without);
    assert_eq!(
        rival_errs(&without_errs).len(),
        1,
        "the control: the same file without the import, which is what the previous cut \
         got right; got: {without_errs:?}"
    );
}

/// AN IMPORT OF THE SPEC OPERATION ITSELF DOES NOT EXCUSE THE RIVAL — the inverse trap.
///
/// Asking "does anything resolve in scope?" and standing down if so would make
/// `import anthill.prelude.PartialEq.{eq}` beside `operation eq(…)` load CLEAN: the one
/// line that makes the collision real would defeat the rule whose purpose is that
/// collision. Asking what the name DENOTES gets it right by construction — an import of
/// the spec op denotes the spec op.
///
/// FAILS IF the scope leg is changed to "any in-scope answer stands the rule down".
#[test]
fn an_import_of_the_spec_op_does_not_excuse_a_rival() {
    let errs = errs_for(
        r#"
namespace test.bfb9a.imported
  import anthill.prelude.{Bool, Int64, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  operation eq(a: Int64, b: Int64) -> Bool = false
end
"#,
    );
    let rivals = rival_errs(&errs);
    assert_eq!(rivals.len(), 1, "must still be refused; got: {errs:?}");
    assert!(
        rivals[0].contains("anthill.prelude.PartialEq.eq"),
        "and it names the spec operation the import brought in; got: {rivals:?}"
    );
}

/// A DOTTED FREE-STANDING OPERATION IS THE SAME DECLARATION WEARING A PATH.
///
/// `operation Inner.eq(…)` inside a namespace declares into `Inner` — and when `Inner`
/// is a NAMESPACE (which `ensure_intermediate_namespaces` mints if nothing else declared
/// it) the operation is free-standing there. The first cut of this rule lived in
/// `load_operation` and skipped `segments.len() != 1` on the ground that a dotted name is
/// "the member case wearing a path"; driven, this program loaded clean while the undotted
/// spelling at the same address was refused — same address, two spellings, opposite
/// verdicts. Reading `DeclSite::scope` / `DeclSite::local`, which are the address AFTER
/// that minting, makes the two arrive identical.
///
/// FAILS IF the pass is moved back to a per-declaration hook that reads the written
/// name's segments.
#[test]
fn a_dotted_free_standing_operation_is_refused_too() {
    let errs = errs_for(
        r#"
namespace test.bfb9a.dotted
  import anthill.prelude.{Bool, Int64}
  operation Inner.eq(a: Int64, b: Int64) -> Bool = true
end
"#,
    );
    let rivals = rival_errs(&errs);
    assert_eq!(
        rivals.len(),
        1,
        "the dotted spelling is refused too; got: {errs:?}"
    );
    assert!(
        rivals[0].contains("test.bfb9a.dotted.Inner"),
        "and the scope it names is the one declared INTO, not the enclosing namespace; \
         got: {rivals:?}"
    );
}

/// ONE MISTAKE, ONE MESSAGE. Two same-named operations in one namespace are ONE name
/// taking ONE meaning it should not have, and the duplicate declaration is already
/// WI-1049's error. The first cut fired per declaration SITE and produced two
/// byte-identical rival messages on top of it — three errors for one mistake.
///
/// FAILS IF the `reported` set is dropped, or keyed on the declaration site rather than
/// on `(scope, name)`.
#[test]
fn two_declarations_of_one_name_get_one_rival_message() {
    let errs = errs_for(
        r#"
namespace test.bfb9a.twice
  import anthill.prelude.{Bool, Int64}
  operation eq(a: Int64, b: Int64) -> Bool = true
  operation eq(a: Int64, b: Int64, c: Int64) -> Bool = false
end
"#,
    );
    assert_eq!(
        rival_errs(&errs).len(),
        1,
        "one name, one rival message — the duplicate declaration is a separate \
         diagnostic and is expected among these; got: {errs:?}"
    );
}

/// A SIBLING FILE'S READING IS ASKED TOO, AND THE MESSAGE NAMES IT.
///
/// An import resolves only in the file that wrote it (WI-995), so two files writing text
/// at one address read one name differently. Here the DECLARING file imports an unrelated
/// `add` — so on its own reading the declaration is a capture, not a rival — while the
/// sibling file writing at the same address has no such import and its bare `add` still
/// meant `Additive.add`. The declaration repoints the sibling's text, so it is refused;
/// and because the reader is not the declaring file, the message says whose reading
/// earned the refusal.
///
/// THE PAIR IS THE MEASUREMENT: give the sibling the same import and the program loads.
///
/// FAILS IF the per-file loop is replaced by a single resolution, or if `read_in` is
/// dropped (the second assertion). Before `read_in` existed the message was identical
/// either way, telling the author to repair a relationship their file does not have —
/// found by `/code-review`.
#[test]
fn a_sibling_files_reading_is_asked_too() {
    // A SORT MEMBER again, and in a namespace DISJOINT from `test.bfb9a.sib` — a
    // sub-namespace of it would put this file's text at the shared address too, and the
    // row is about which file reads the name, so the lib must not be one of the readers.
    const LIB: &str = r#"
namespace test.bfb9asibarith
  import anthill.prelude.{Int64}
  sort Arith
    entity arith
    operation add(a: Int64, b: Int64) -> Int64 = 7
  end
end
"#;
    const DECLARER: &str = r#"
namespace test.bfb9a.sib
  import anthill.prelude.{Int64}
  import test.bfb9asibarith.Arith.{add}
  operation add(a: Int64) -> Int64 = 1
end
"#;
    let errs = errs_for_named(&[
        ("lib.anthill", LIB),
        ("declarer.anthill", DECLARER),
        (
            "sibling.anthill",
            r#"
namespace test.bfb9a.sib
  import anthill.prelude.{Int64}
  operation plain(a: Int64) -> Int64 = 2
end
"#,
        ),
    ]);
    let rivals = rival_errs(&errs);
    assert_eq!(
        rivals.len(),
        1,
        "a sibling file that never imported the other `add` still read the bare name as \
         `Additive.add`, so the declaration is refused; got: {errs:?}"
    );
    assert!(
        rivals[0].contains("sibling.anthill"),
        "and the message names the file whose reading earned it, since that is not the \
         declaration's own; got: {rivals:?}"
    );
    let both_import = errs_for_named(&[
        ("lib.anthill", LIB),
        ("declarer.anthill", DECLARER),
        (
            "sibling.anthill",
            r#"
namespace test.bfb9a.sib
  import anthill.prelude.{Int64}
  import test.bfb9asibarith.Arith.{add}
  operation plain(a: Int64) -> Int64 = 2
end
"#,
        ),
    ]);
    assert!(
        rival_errs(&both_import).is_empty(),
        "with EVERY file at that address reading `add` as the imported one, no reader is \
         repointed and the program loads; got: {both_import:?}"
    );
}

/// THE POPULATION, DRIVEN — every short name the implicit tier answers, declared
/// free-standing in its own namespace, in ONE load.
///
/// The refused set is TWELVE, asserted literally rather than re-derived from the
/// predicate the pass uses: a population computed the same way the code computes it
/// cannot disagree with it. What the literal catches is a change of MEANING — a tier
/// entry that starts or stops being a spec operation.
///
/// THE NAMES COME FROM `load::implicit_tier_short_names`, which reads the tier's table.
/// The previous version SCRAPED THIS CRATE'S SOURCE (`read_to_string("src/kb/load.rs")`
/// then `split('"').step_by(2)`), where one `"` inside a table comment silently
/// unbalances the parity and drops names while every assertion still passes — found by
/// `/code-review`.
///
/// IT WAS TEN, AND `div` / `mod` JOINING IS WI-20260824-VT8CF — the whole of that
/// ticket, read off this one list. Both names were already tier entries and already
/// SOME spec operation's short name, so they always passed the pass's spelling gate;
/// what they lacked was a parametric carrier at the address the tier resolved to
/// (`anthill.prelude.Int64.{div,mod}`). Repointing the tier at `Divisible.div` /
/// `EuclideanDomain.mod` moved them across with nothing added to the pass. The old
/// doc's warning still holds and is why the census is driven rather than counted: "tier
/// names that some spec op carries" would have said twelve all along and been the wrong
/// question — only the load answers.
///
/// `rem` is NOT here, and that is the same distinction from the other side: it is an
/// `EuclideanDomain` member, so it IS a spec operation, but no operator mints it and it
/// is not a tier entry — so a free-standing `rem` shadows nothing and is not refused.
///
/// FAILS IF the refusal widens (a name joins) or narrows (one leaves).
#[test]
fn the_refusal_population_is_the_twelve_spec_operations() {
    let names = load::implicit_tier_short_names();
    // WI-20260825-5W3RJ SHRANK THIS FROM 62 TO 34, and the floor moved with it. The
    // tier used to carry a second table — the 28 addresses of the forms the CONVERTER
    // synthesizes — which is now gone: a desugared node names its reflect declaration
    // outright, so it never was a bare name to be resolved. Nothing this row asks about
    // left with it; no synthesized form was ever a spec operation, and the refused set
    // below is unchanged.
    assert!(
        names.len() > 30,
        "sanity: the implicit prelude should carry dozens of names, got {}",
        names.len()
    );
    let mut src = String::new();
    for (i, n) in names.iter().enumerate() {
        src.push_str(&format!(
            "namespace test.bfb9a.pop{i}\n  import anthill.prelude.{{Int64}}\n  \
             operation {n}(a: Int64) -> Int64 = 1\nend\n"
        ));
    }
    let errs = errs_for(&src);
    let rivals = rival_errs(&errs);
    let mut refused: Vec<&str> = names
        .iter()
        .copied()
        .filter(|n| {
            rivals
                .iter()
                .any(|e| e.contains(&format!("operation '{n}' in scope")))
        })
        .collect();
    refused.sort_unstable();
    assert_eq!(
        refused,
        vec![
            "add", "div", "eq", "gt", "gte", "lt", "lte", "mod", "mul", "neg", "neq", "sub"
        ],
        "the tier names that denote a SPEC operation are exactly these twelve; every \
         other entry is a constructor, a literal carrier, a reflection sort, a primitive \
         with no spec, or an operation on a non-parametric carrier. `div` and `mod` are \
         WI-20260824-VT8CF's; drop them and this is the pre-ticket list. Rival errors: \
         {rivals:?}"
    );
}

/// THE RULE IS UNIFORMLY OFF IN A KB WITH NO STDLIB SOURCES, and that is a property to
/// pin rather than to discover.
///
/// `spec_op_parent_sort` reads the parent's `sort T = ?` declarations, which only the
/// stdlib FILES carry — `register_prelude` defines the prelude's symbols and no type
/// params — so `spec_operation_short_names` is empty and nothing is refused. It is a
/// user-visible property of `anthill query --no-stdlib`: the same file is refused with
/// the stdlib and answers without it.
///
/// The alternative is worse and was the FIRST implementation's: gating on
/// `by_qualified_name` alone made `eq` refusable while `neg` / `div` / `mod` were not, so
/// the same program was legal or illegal in ways that split the tier's own names.
///
/// FAILS IF the empty-population early return is replaced by something that refuses on
/// symbol identity alone.
#[test]
fn a_stdlib_less_kb_refuses_nothing() {
    let kb = KnowledgeBase::new();
    assert!(
        load::spec_operation_short_names(&kb).is_empty(),
        "a KB with no stdlib sources knows no parametric sorts, so it knows no spec \
         operations and this rule has nothing to refuse"
    );
    // And the same KB after `register_prelude` — the state a `--no-stdlib` load reaches,
    // where the prelude's SYMBOLS exist and their type params do not.
    let mut prelude_only = KnowledgeBase::new();
    load::register_prelude(&mut prelude_only);
    assert!(
        !load::implicit_target_orphans(&prelude_only).contains(&"anthill.prelude.PartialEq.eq"),
        "sanity: `register_prelude` does define the tier's target symbol — it is not an \
         orphan there"
    );
    assert!(
        load::spec_operation_short_names(&prelude_only).is_empty(),
        "…and it is still not a SPEC operation there, because no `sort T = ?` came with \
         it — so the rule stays uniformly off rather than partly on"
    );
}

/// THE INVERTED GAP — WI-20260824-VT8CF, and this row IS its measurement.
///
/// It used to assert the opposite, and the ONE-LINE HISTORY is the point. `mod`'s tier
/// target was `anthill.prelude.Int64.mod`; `Int64` declares no `sort T = ?`, so
/// `spec_op_parent_sort` answered `None`, this rule correctly stood down, and a
/// namespace-level `operation mod(…)` captured a minted `%` SILENTLY — the row asserted
/// `Int(99)`, the local declaration's value, where `7 % 2` is 1.
///
/// NOTHING WAS ADDED TO THIS PASS TO CLOSE IT. The tier was repointed at
/// `anthill.prelude.EuclideanDomain.mod`, which IS parametric, so the existing rule
/// reaches it by construction. That is why the repair belonged in the library rather
/// than in a guard: a name the tier answers is refusable exactly when what it points at
/// can be `provides`-ed, and division could not be until it had a spec.
///
/// DRIVEN THROUGH AN OPERATION BODY, not a rule, and the second half still matters:
/// `:- eq(7 % 2, 1)` answers 0 definite solutions with or without the shadow, because
/// `eq` never binds and the goal suspends, so it would measure nothing either way.
///
/// BACKING THE CHANGE OUT — repoint `PRELUDE_QUALIFIED`'s `div`/`mod` entries at
/// `anthill.prelude.Int64.{div,mod}` — makes both halves fail: no rival error, and the
/// unshadowed value below stops being reachable because the shadow takes it.
#[test]
fn a_free_standing_mod_is_refused_now_that_its_tier_target_is_a_spec_op() {
    let src = r#"
namespace test.bfb9a.modgap
  import anthill.prelude.{Int64}
  operation mod(a: Int64, b: Int64) -> Int64 = 99
  operation drive() -> Int64 = 7 % 2
end
"#;
    let errs = errs_for(src);
    let rivals = rival_errs(&errs);
    assert_eq!(
        rivals.len(),
        1,
        "`EuclideanDomain.mod` IS a spec operation, so the free-standing `mod` is now \
         refused — one message, at the declaration; got: {errs:?}"
    );
    assert!(
        rivals[0].contains("anthill.prelude.EuclideanDomain.mod"),
        "and the message must name the spec operation the declaration silenced, so the \
         author knows which carrier to move it onto; got: {}",
        rivals[0]
    );

    // …and WITHOUT the shadow the minted `%` means the carrier's operation. The arm
    // above cannot show this (its program does not load), so the value half is driven on
    // the same expression with the declaration removed — which is the control for
    // "refused" being a repair rather than merely a refusal.
    let unshadowed = r#"
namespace test.bfb9a.modok
  import anthill.prelude.{Int64}
  operation drive() -> Int64 = 7 % 2
end
"#;
    assert!(
        rival_errs(&errs_for(unshadowed)).is_empty(),
        "sanity: the same program without the declaration is not refused"
    );
    let mut interp = crate::common::interp_for(unshadowed);
    let got = interp
        .call("test.bfb9a.modok.drive", &[])
        .expect("the body must evaluate");
    assert_eq!(
        format!("{got:?}"),
        "Int(1)",
        "`7 % 2` is 1 — `EuclideanDomain.mod` dispatched to `Int64.mod`, with no import \
         written anywhere. Got {got:?}"
    );
}

/// THE EXEMPTION LEG, RE-SUBJECTED. `mod` was this file's witness that a tier entry on a
/// NON-PARAMETRIC carrier is not refused; the row above took it away by making `mod`
/// parametric, so the leg needs a subject that still is one or it goes untested — a rule
/// can stop standing down and nothing would say so.
///
/// `anthill.prelude.BigInt.to_bigint` is that subject: a `PRELUDE_QUALIFIED` entry, so
/// the tier really does answer a bare `to_bigint`, on a carrier with no `sort T = ?` and
/// therefore no `provides BigInt[T = …]` to prescribe. There is no repair to name, so
/// the declaration stands. §5.1 lists it, `Bool.and` beside it.
///
/// PASSES BOTH WAYS BY DESIGN with respect to VT8CF — it measures the exemption, not the
/// refusal. It fails if `is_rivalled_spec_operation` drops its parametric requirement,
/// which is the direction that would make the rule refuse names it cannot repair.
#[test]
fn a_non_parametric_carriers_operation_is_still_not_a_spec_op() {
    let src = r#"
namespace test.bfb9a.tobigintgap
  import anthill.prelude.{Int64, BigInt}
  operation to_bigint(n: Int64) -> Int64 = 99
  operation drive() -> Int64 = to_bigint(7)
end
"#;
    let errs = errs_for(src);
    assert!(
        rival_errs(&errs).is_empty(),
        "`BigInt.to_bigint` sits on a non-parametric carrier, so a free-standing \
         `to_bigint` has no provision to be moved onto and is not refused; got: {errs:?}"
    );
    let mut interp = crate::common::interp_for(src);
    let got = interp
        .call("test.bfb9a.tobigintgap.drive", &[])
        .expect("the body must evaluate");
    assert_eq!(
        format!("{got:?}"),
        "Int(99)",
        "and the local declaration is what a written `to_bigint` reaches — the exemption \
         is a REACHABLE shadow, not merely an unraised diagnostic. Got {got:?}"
    );
}

/// A `namespace X` AT A SORT'S ADDRESS IS A MEMBER SITE, NOT A NAMESPACE ONE — the
/// exemption's own boundary, MEASURED here rather than argued from `is_sort_scope`'s
/// name.
///
/// 059 R2/R3 makes such a block a SECONDARY ENTRY to the sort's scope, which "may add
/// members and spec claims", so an operation written there is a member exactly like one
/// in the sort's own body. The declaration below therefore registers `Foo.eq` and no
/// `test.bfb9a.dual.eq`, and is not a rival. A previous `/code-review` reported the
/// dual-kind symbol (`sort Foo` and `namespace Foo` share one symbol, WI-926/956) as an
/// escape from this pass; it is not, and this row is why.
///
/// PASSES BOTH WAYS by design — like `a_sort_member_eq_is_not_a_rival`, it measures the
/// exemption's boundary rather than the refusal. It fails if the member exemption is
/// narrowed to a sort's MAIN entry.
#[test]
fn a_secondary_entry_is_a_member_site() {
    let src = r#"
namespace test.bfb9a.dual
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Foo
    entity foo(v: Int64)
    provides PartialEq[T = Foo]
  end
  namespace Foo
    operation eq(a: Foo, b: Foo) -> Bool = true
  end
  operation use_eq() -> Bool = eq(foo(1), foo(2))
end
"#;
    let errs = errs_for(src);
    assert!(
        rival_errs(&errs).is_empty(),
        "an operation in a SECONDARY ENTRY to a sort is a member of that sort, not a \
         free-standing declaration; got: {errs:?}"
    );
    let mut interp = crate::common::interp_for(src);
    let got = interp
        .call("test.bfb9a.dual.use_eq", &[])
        .expect("the member declared in the secondary entry must be callable");
    assert_eq!(
        format!("{got:?}"),
        "Bool(true)",
        "and it IS `Foo`'s `eq` — `true` by construction, where a structural equality \
         on two different `foo`s would be false; got {got:?}"
    );
}

/// A NAMESPACE-LESS DECLARATION IS FREE-STANDING TOO. `<global>` is a scope like any
/// other for this rule — it is not a sort — so an `operation eq` written in a file with
/// no `namespace` is refused on the same terms.
///
/// AND IT IS THE ONE ADDRESS WHERE THE RIVAL IS ALSO AMBIGUOUS, which is why the row
/// records the whole error list rather than only its own message: `<global>` is a
/// non-enclosing parent of every scope (WI-980/987), so the declaration is reachable
/// from inside the stdlib's own namespaces, where it ties with the prelude's `eq`. That
/// is the exact footgun WI-521 removed for the FALLBACK by making the implicit prelude
/// lowest-precedence — see this file's sibling `wi521_prelude_test`, whose header used
/// to state the property as "a user name that clashes with a prelude name is NEVER
/// ambiguous". It is not, one scope over, and the assertion below is what says so.
///
/// FAILS IF `<global>` is added to the pass's exclusions (the first assertion). The
/// second is a property of THIS address and must not be read as a general one —
/// `wi521_prelude_test::a_free_standing_eq_rivalling_the_spec_op_is_refused` is the
/// namespaced counterpart, and it reports exactly one error.
#[test]
fn a_namespace_less_declaration_is_free_standing_too() {
    let errs = errs_for(
        r#"
import anthill.prelude.{Bool, Int64}
operation eq(a: Int64, b: Int64) -> Bool = true
"#,
    );
    assert_eq!(
        rival_errs(&errs).len(),
        1,
        "a namespace-less `operation eq` is free-standing and refused; got: {errs:?}"
    );
    assert!(
        errs.iter().any(|e| e.contains("mbiguous")),
        "and — unlike a namespaced one — it ALSO goes ambiguous inside the stdlib's own \
         scopes, because `<global>` is a non-enclosing parent of every scope. This is \
         the assertion `wi521_prelude_test`'s header can no longer make in general; got: \
         {errs:?}"
    );
}

/// THE RULE IS ABOUT SPEC OPERATIONS, NOT ABOUT THE TIER'S TABLE — and this is the only
/// row that separates the two readings.
///
/// The separating shape needs a name whose TIER target is NOT a spec operation, plus an
/// IMPORT that makes the same spelling denote one at this address. `to_bigint` is that
/// name: it is a `PRELUDE_QUALIFIED` entry resolving to `anthill.prelude.BigInt.to_bigint`
/// on a non-parametric carrier, so a bare one is not refused (the population row above
/// proves it, and `a_non_parametric_carriers_operation_is_still_not_a_spec_op` drives the
/// shadow it leaves reachable). Importing a PARAMETRIC sort's member of that spelling
/// makes the declaration a rival, and the message names that member.
///
/// IT USED TO BE `div`, AND WI-20260824-VT8CF TOOK THE SUBJECT AWAY — `div`'s tier target
/// is now `Divisible.div`, parametric, so the "without import" control would be refused
/// too and the row would stop separating anything. The spec is DECLARED HERE rather than
/// borrowed from the stdlib for exactly that reason: a row whose subject is a library
/// accident expires when the library changes, and this one already did once.
///
/// FAILS IF the pass is narrowed to "the name's TIER target is a spec operation" — under
/// which the import would be irrelevant and this program would load. Both halves are
/// driven: the import removed is the second assertion, and it loads clean.
#[test]
fn a_spec_op_reached_only_by_import_is_a_rival_too() {
    let spec = r#"
namespace test.bfb9a.widening
  import anthill.prelude.{Int64}
  sort Widening
    sort T = ?
    operation to_bigint(n: T) -> Int64
  end
end
"#;
    let errs = errs_for_named(&[
        ("widening.anthill", spec),
        (
            "importer.anthill",
            r#"
namespace test.bfb9a.importedspec
  import anthill.prelude.{Int64}
  import test.bfb9a.widening.Widening.{to_bigint}
  operation to_bigint(a: Int64) -> Int64 = 1
end
"#,
        ),
    ]);
    let rivals = rival_errs(&errs);
    assert_eq!(
        rivals.len(),
        1,
        "an imported spec operation is denoted here, so the declaration rivals it; got: \
         {errs:?}"
    );
    assert!(
        rivals[0].contains("test.bfb9a.widening.Widening.to_bigint"),
        "and it names the IMPORTED spec operation, NOT the tier's \
         `BigInt.to_bigint`; got: {rivals:?}"
    );

    let without_import = errs_for_named(&[
        ("widening.anthill", spec),
        (
            "tier.anthill",
            r#"
namespace test.bfb9a.tierbigint
  import anthill.prelude.{Int64}
  operation to_bigint(a: Int64) -> Int64 = 1
end
"#,
        ),
    ]);
    assert!(
        rival_errs(&without_import).is_empty(),
        "with no import the tier answers `BigInt.to_bigint`, whose carrier is not \
         parametric, so this rule stands down — the IMPORT is what changed the verdict, \
         which is the whole point of the row; got: {without_import:?}"
    );
}

/// A SIBLING NAMESPACE OF THE NAME ENDS THE LADDER, so the tier is not what the name
/// denotes and this rule stands down.
///
/// `check_name_captures` EXCUSES a namespace candidate — a namespace has no value
/// reading, so nothing a body reads is silently repointed — and the first cut of this
/// pass copied that excuse. Wrong here: the excuse is about whether a capture HARMS, and
/// this pass's question is whether the name RESOLVES. The middle row below is the proof
/// that it does: with `namespace add` in scope, a bare `add` stops reaching
/// `Additive.add` and says so loudly.
///
/// FAILS IF the namespace candidate is skipped without ending the ladder: the first
/// assertion picks up a rival error naming `anthill.prelude.Additive.add`, which the
/// middle row proves the address does not denote. Found by `/code-review`.
///
/// THE MIDDLE ROW'S SENTENCE WENT FROM PLURAL TO SINGULAR under WI-20260825-1WBZT, and
/// the change is that ticket's whole claim in one diagnostic. It read "`add` is a member
/// of sorts Numeric, Ring" — TWO different operations under one spelling, resolved only
/// because the implicit tier deterministically answered `Numeric.add`. One
/// `Additive.add` declaration is what makes it "a member of sort Additive"; `Numeric`
/// and `algebra.Ring` now reach that one by `provides`.
#[test]
fn a_sibling_namespace_of_the_name_stands_the_rule_down() {
    const SHADOWED: &str = r#"
namespace test.bfb9a.nsshadow
  import anthill.prelude.{Int64}
  namespace add
    operation marker(a: Int64) -> Int64 = 0
  end
  namespace inner
    import anthill.prelude.{Int64}
    operation add(a: Int64, b: Int64) -> Int64 = 1
  end
end
"#;
    let errs = errs_for(SHADOWED);
    assert!(
        rival_errs(&errs).is_empty(),
        "a `namespace add` at the enclosing address ends the ladder, so `add` in the \
         child scope never denoted `Additive.add`; got: {errs:?}"
    );
    // THE MIDDLE ROW: the same shadow, with a REFERENCE instead of a declaration. It
    // shows the namespace really does beat the tier — which is what makes the refusal
    // above wrong rather than merely unhelpful.
    let shadowed_ref = errs_for(
        r#"
namespace test.bfb9a.nsref
  import anthill.prelude.{Int64}
  namespace add
    operation marker(a: Int64) -> Int64 = 0
  end
  namespace inner
    import anthill.prelude.{Int64}
    operation use_add(a: Int64) -> Int64 = add(a, 1)
  end
end
"#,
    );
    assert!(
        shadowed_ref
            .iter()
            .any(|e| e.contains("`add` is a member of sort Additive")
                && e.contains("not in scope as a bare name here")),
        "with `namespace add` in scope a bare `add(a, 1)` must NOT reach `Additive.add` — \
         and the DISTINGUISHING sentence is asserted, not merely non-emptiness, because \
         any unrelated failure would otherwise be read as proof of the shadow; got: \
         {shadowed_ref:?}"
    );
    // AND THE CONTROL WITHOUT THE SHADOW: the same declaration IS refused, so the row
    // above is not passing because the rule is off.
    let no_shadow = errs_for(
        r#"
namespace test.bfb9a.nsplain
  import anthill.prelude.{Int64}
  namespace inner
    import anthill.prelude.{Int64}
    operation add(a: Int64, b: Int64) -> Int64 = 1
  end
end
"#,
    );
    assert_eq!(
        rival_errs(&no_shadow).len(),
        1,
        "with the `namespace add` removed the tier answers and the declaration is a \
         rival; got: {no_shadow:?}"
    );
}

/// AN EXPOSED CONSTRUCTOR OF A SIBLING SORT IS REACHED BY A BARE NAME, so it ends the
/// ladder too — and this is the one place the rule must NOT reuse
/// `resolve_captured_name`.
///
/// §8.6 leaks an enum's / sort's constructors to the ENCLOSING namespace so they can be
/// written unqualified there. `resolve_captured_name` deliberately does NOT follow that
/// link (059's amended clause 3: members and constructors are named per TYPE, and
/// following it refuses the stdlib itself). This pass asks a different question — what a
/// reference written here resolves to — so it asks
/// `SymbolTable::resolve_ignoring_own_locals`, which follows it.
///
/// THE MIDDLE ROW IS THE PROOF, again: the bare `eq(a)` below CONSTRUCTS an `S`, so the
/// exposed constructor really is what the name denotes there.
///
/// FAILS IF the pass goes back to `resolve_captured_name`: the first assertion picks up
/// a rival error naming `anthill.prelude.PartialEq.eq`. Found by `/code-review`.
#[test]
fn an_exposed_constructor_stands_the_rule_down() {
    let errs = errs_for(
        r#"
namespace test.bfb9a.expose
  import anthill.prelude.{Bool, Int64}
  sort S
    entity eq(v: Int64)
  end
  namespace inner
    import anthill.prelude.{Bool, Int64}
    operation eq(a: Int64, b: Int64) -> Bool = true
  end
end
"#,
    );
    assert!(
        rival_errs(&errs).is_empty(),
        "`S`'s exposed constructor `eq` is what a bare `eq` denotes at that address, so \
         the declaration captures IT, not the spec operation; got: {errs:?}"
    );
    // THE MIDDLE ROW: the same shape with a REFERENCE. It loads AND runs, so the bare
    // name really does reach the constructor.
    let src = r#"
namespace test.bfb9a.exposeref
  import anthill.prelude.{Bool, Int64}
  sort S
    entity eq(v: Int64)
  end
  namespace inner
    import anthill.prelude.{Bool, Int64}
    operation useit(a: Int64) -> test.bfb9a.exposeref.S = eq(a)
  end
end
"#;
    assert!(
        errs_for(src).is_empty(),
        "sanity: the reference form loads; got: {:?}",
        errs_for(src)
    );
    let mut interp = crate::common::interp_for(src);
    let got = interp
        .call("test.bfb9a.exposeref.inner.useit", &[Value::Int(7)])
        .expect("the exposed constructor must be callable by its bare name");
    // THE FUNCTOR BY QUALIFIED NAME, not by the `Debug` spelling: an `Entity`'s debug
    // form prints `Symbol(2564)`, which names nothing and would make a `contains("eq")`
    // assertion pass on almost anything.
    let functor = match &got {
        Value::Entity { functor, pos, .. } => {
            assert_eq!(format!("{pos:?}"), "[Int(7)]", "the argument rode through");
            *functor
        }
        other => panic!("a bare `eq(a)` must CONSTRUCT, got {other:?}"),
    };
    assert_eq!(
        interp.kb().qualified_name_of(functor),
        "test.bfb9a.exposeref.S.eq",
        "and what it constructs is `S`'s own exposed constructor — which is what makes \
         the row above a real denotation rather than a guess"
    );
}
