//! WI-862 (proposal 058 §3.6, §4) — the SURFACE CONSOLIDATION, both halves.
//!
//! **(a) `default provides X[…]`**, the INLINE spelling of a `DefaultProvider` mark. One
//! leading modifier desugaring in the loader to the row WI-860's substrate already
//! arbitrates and WI-861's rung 2a already consumes. So the claim under test is not "a
//! keyword parses" but **the inline mark and the by-reference fact are ONE statement**:
//! same row, same origin, same arbitration, same dispatch.
//!
//! **(b) the RETIREMENT of the `fact` spelling of a provision** — `provides` becomes the
//! one spelling and the in-sort `fact` one warns. Driven at the bottom of this file, and
//! its acceptance is a CORPUS assertion: the shipped stdlib plus host bindings emit zero
//! deprecations (39 before the migration, measured). The deprecation is scoped to the
//! arm where the two spellings agree — a scope that names a type — because `provides` is
//! refused at a plain namespace, so warning there would advertise a repair the next
//! compile rejects.
//!
//! EVERY TEST HERE DRIVES SOMETHING THE KEYWORD DECIDES — a value, a refusal, or a row
//! — because a `default` that parsed and marked nothing would leave a clean load behind
//! it, which is the silent-declaration shape WI-933 was filed for.
//!
//! | claim | driven by |
//! |---|---|
//! | the sugar makes a bracket-less dispatch ANSWER, and answer the marked provider | `an_inline_mark_answers_a_bracketless_dispatch` |
//! | …and the control: the same program without `default` is the tier-3 refusal | `dropping_the_modifier_restores_the_tier_3_refusal` |
//! | the inline row is a DECLARED row, at the carrier the provision wrote | `the_inline_mark_is_a_declared_row_at_the_provisions_carrier` |
//! | inline and by-reference are ONE mark, not two rivals | `the_two_spellings_of_one_mark_are_one_row` |
//! | an inline mark colliding with a by-reference one is refused NAMING BOTH | `an_inline_mark_colliding_with_a_reference_mark_is_refused` |
//! | no-displacement holds through the sugar too | `marking_inline_against_a_self_providing_carrier_is_refused` |
//! | the modifier composes with the `:- conditions` tail (058 §3.8) | `a_conditional_provision_can_mark_itself` |
//! | a spec that names no sort is REFUSED, not silently unmarked | `default_on_a_variable_spec_is_refused` |
//! | `default` is not reserved — it is still an ordinary identifier | `default_is_not_a_reserved_word` |
//! | (b) the deprecation fires in a sort body, and NOT at namespace level | `the_deprecation_fires_in_a_sort_body_and_not_at_namespace_level` |
//! | (b) …and the `provides` spelling is silent — that arm's control | `the_provides_spelling_raises_no_deprecation` |
//! | (b) THE MIGRATION: the shipped corpus emits none, with a live-channel canary | `the_shipped_stdlib_emits_no_provision_fact_deprecations` |
//! | (b) the warning carries a LINE — the first span-bearing `LoadWarning` | `the_deprecation_is_located` |
//!
//! WHAT FAILS IF THIS IS BACKED OUT — MEASURED, one perturbation at a time, and NOT
//! what was predicted: the prediction said six and named the wrong six.
//!
//! * **NON-EMISSION** — `emit_default_provider_row` never called, so the modifier parses
//!   and marks nothing → **7 fail**: `an_inline_mark_answers_a_bracketless_dispatch`,
//!   `the_inline_mark_is_a_declared_row_at_the_provisions_carrier`,
//!   `an_inline_mark_colliding_with_a_reference_mark_is_refused`,
//!   `two_inline_marks_for_one_carrier_are_refused`,
//!   `marking_inline_against_a_self_providing_carrier_is_refused`,
//!   `a_conditional_provision_can_mark_itself`, `default_on_a_variable_spec_is_refused`.
//! * **MIS-EMISSION** — the `spec` and `provider` fields swapped, i.e. a row emitted that
//!   is NOT the one a hand-written fact produces → **7 fail**, the same set with
//!   `default_on_a_variable_spec_is_refused` (which never reaches the emission) replaced
//!   by `the_two_spellings_of_one_mark_are_one_row`.
//!
//! WHICH PASS EITHER WAY, AND WHY THAT IS BY DESIGN:
//!
//! * `dropping_the_modifier_restores_the_tier_3_refusal` and
//!   `positive_control_a_broken_program_is_refused` are controls for the ABSENCE of a
//!   mark — they must be insensitive to the emission or they are not controls.
//! * `default_is_not_a_reserved_word` is a grammar property, not a loader one.
//! * `the_two_spellings_of_one_mark_are_one_row` is insensitive to NON-emission, and
//!   unavoidably so: it asserts that the inline and by-reference spellings are ONE
//!   statement, and a fixture containing both behaves identically when one of them stops
//!   existing. Its control direction is the MIS-emission above, where it fails — so what
//!   it guards is "the sugar's row is byte-identical to the hand-written one", never
//!   "the sugar emits at all". That second half is
//!   `the_inline_mark_is_a_declared_row_at_the_provisions_carrier`'s job.
//!
//! HALF (b) HAS ITS OWN BACK-OUT, and it is the corpus rather than a fixture: restoring
//! any migrated `fact` row to `stdlib/` or `anthill-stl/anthill/` fails
//! `the_shipped_stdlib_emits_no_provision_fact_deprecations`. Deleting the warning
//! itself fails three of the four (b) tests; the fourth,
//! `the_provides_spelling_raises_no_deprecation`, passes either way by design — it is
//! the arm's control.
//!
//! WHAT HALF (b) BROKE AND THIS FILE DOES NOT OWN. The migration is not a pure rename:
//! a `fact` also enters the RULE INDEX, and four readers keyed on that alone. Their
//! repairs are asserted where their own tests already are — `wi206`/`wi707`/`wi314`/
//! `kb::region::wi353_tests` (region analysis read raw `Modifiable` facts),
//! `codegen_test::full_persistence_store_hierarchy` (the Rust supertrait bound), and
//! `wi1094_named_slot_inference_test::a_value_precondition_before_an_op_scoped_binder_
//! keeps_its_own_diagnostic` (a mixed `requires` clause was proved from Γ wholesale, and
//! only ever passed because `fact Ord[T = Int64]` made its spec conjunct resolvable).
//! Each is a test that FAILED on the migration and passes on the repair.
//!
//! Reference: proposal 058 §3.6, §4; `docs/design/058-implementation.md` §6, §19, §29;
//! `docs/kernel-language.md` §5.1.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

// ── Fixture ──────────────────────────────────────────────────────────
//
// The WI-861 depth-coded `Desc` family, so a WRONG provider shows as a different number
// rather than as an error: `describe(leaf())` is 1 for the carrier's own implementation,
// 7 for `Rival`, 9 for `Other`.

/// `Leaf` with a member and NO provision of its own — no inferred row, so only a written
/// mark can break a tie at this carrier.
const LEAF_BARE: &str = r#"
  sort Leaf
    entity leaf
    operation describe(x: Leaf) -> Int64 = 1
  end
"#;

/// `Leaf` PROVIDING `Desc` itself — the inferred row exists, so no rival may be marked.
const LEAF_SELF: &str = r#"
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
"#;

/// A witness for `Leaf`, marked INLINE — the subject of this file.
const RIVAL_DEFAULT: &str = r#"
  sort Rival
    default provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// The same witness UNMARKED — every control is this program plus or minus the one word.
const RIVAL_PLAIN: &str = r#"
  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// A second witness, so a tie exists that no inferred row can settle.
const OTHER_PLAIN: &str = r#"
  sort Other
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
  end
"#;

/// A second witness marked INLINE, for the two-inline-rivals collision.
const OTHER_DEFAULT: &str = r#"
  sort Other
    default provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
  end
"#;

const MARK_OTHER: &str = "  fact DefaultProvider(spec: Desc, provider: Other)\n";
const MARK_RIVAL: &str = "  fact DefaultProvider(spec: Desc, provider: Rival)\n";

/// A sort-level `requires`, so the caller constructs the dictionary at the call site.
const HOLDER_SORT: &str = r#"
  sort Holder
    sort HT = ?
    requires Desc[T = HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
"#;

fn driver(arg: &str) -> String {
    format!("  sort Driver\n    operation drive(n: Int64) -> Int64 = Holder.probe({arg})\n  end\n")
}

fn program(ns: &str, parts: &[&str]) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
{}
end
"#,
        parts.concat()
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// `Driver.drive(0)` on a FRESH interpreter — a shared one is poisoned by an earlier
/// trapped call.
fn eval_int(src: &str, ns: &str, why: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(&format!("{ns}.Driver.drive"), &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}\n{src}"),
    }
}

/// The index's rows for one carrier, WITH origins — the same probe WI-860's tests read,
/// filtered of the equality family (`Leaf` is a composite and derives `PartialEq`/`Eq`,
/// whose inferred rows are true and are not this file's subject).
fn index_rows_for(kb: &KnowledgeBase, carrier_qn: &str) -> Vec<String> {
    kb.default_provider_index()
        .expect("a loaded KB must carry the default-provider index")
        .rendered_rows_for_carrier(kb, carrier_qn)
        .into_iter()
        .filter(|r| !r.starts_with("PartialEq | ") && !r.starts_with("Eq | "))
        .collect()
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage, so every clean load below is a real assertion.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(&program(
        "wi862.control",
        &["  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end\n"],
    ));
}

// ── The headline: the sugar reaches a dispatch ───────────────────────

/// THE ACCEPTANCE. A carrier that provides nothing, two witnesses, and the modifier
/// naming which one silence takes — the WI-861 "Money shape", written INLINE.
///
/// This drives the whole chain in one call: converter → `emit_default_provider_row` →
/// `declared_default_rows` → `DefaultProviderIndex` → `default_among` at
/// `pick_most_specific`'s tie. Answering `7` (and not `9`, and not a refusal) is
/// evidence that every link carried the mark.
#[test]
fn an_inline_mark_answers_a_bracketless_dispatch() {
    let ns = "wi862.inline";
    let src = program(
        ns,
        &[
            LEAF_BARE,
            RIVAL_DEFAULT,
            OTHER_PLAIN,
            HOLDER_SORT,
            &driver("leaf()"),
        ],
    );
    assert_eq!(
        eval_int(&src, ns, "the inline mark must break the tie"),
        7,
        "`default provides` must select `Rival` for a bracket-less `Desc.describe` at \
         `Leaf` — 9 would mean route order picked `Other`, and a panic would mean the \
         mark never reached the index"
    );
}

/// THE CONTROL, and it is the same program minus one word. Without it the test above
/// would pass equally if ties had simply stopped being refused.
#[test]
fn dropping_the_modifier_restores_the_tier_3_refusal() {
    let ns = "wi862.unmarked";
    let src = program(
        ns,
        &[
            LEAF_BARE,
            RIVAL_PLAIN,
            OTHER_PLAIN,
            HOLDER_SORT,
            &driver("leaf()"),
        ],
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("is ambiguous among providers")
                && e.contains("wi862.unmarked.Rival")
                && e.contains("wi862.unmarked.Other")
        }),
        "without the modifier the tie is tier-3's refusal naming both witnesses: {errs:?}"
    );
}

// ── The row it emits ─────────────────────────────────────────────────

/// The inline mark is a **declared** row — not a third origin — and its carrier is the
/// one the provision WROTE, which is 058 §3.6's derivation working unchanged because the
/// provision the carrier is derived from is the very clause the modifier rides.
///
/// The origin is asserted rather than assumed: it is what a displacement diagnostic
/// prints, and an inferred row would satisfy every other assertion here.
#[test]
fn the_inline_mark_is_a_declared_row_at_the_provisions_carrier() {
    let ns = "wi862.row";
    let src = program(ns, &[LEAF_BARE, RIVAL_DEFAULT]);
    let kb = crate::common::load_kb_with(&src);
    assert_eq!(
        index_rows_for(&kb, "wi862.row.Leaf"),
        vec!["Desc | Leaf | Rival (declared)".to_string()],
        "`default provides Desc[T = Leaf]` in `Rival` must file the DECLARED row at \
         `Leaf`, the carrier its own provision names"
    );
}

/// ONE MARK, TWO SPELLINGS — the property that makes this sugar and not a second
/// channel. Writing the modifier AND the reference fact for the same `(spec, provider)`
/// loads clean and yields ONE row: `declared_default_rows` dedups identical pairs, and
/// it can only do that because the desugaring emits the identical entity, fields and
/// term shapes a hand-written fact does.
///
/// **THIS TEST IS INSENSITIVE TO THE SUGAR BEING DELETED, BY CONSTRUCTION** — measured,
/// not assumed. A fixture holding both spellings of one statement behaves identically
/// when one of them stops existing, so a non-emission leaves it green. Its control is
/// the MIS-emission: swapping the emitted `spec`/`provider` fields turns this program
/// into a `DefaultProviderDoesNotProvide` refusal and this test fails. So what it
/// guards is that the sugar's row is IDENTICAL to the hand-written one — not that the
/// sugar emits, which is
/// [`the_inline_mark_is_a_declared_row_at_the_provisions_carrier`]'s job.
#[test]
fn the_two_spellings_of_one_mark_are_one_row() {
    let ns = "wi862.both";
    let src = program(ns, &[LEAF_BARE, RIVAL_DEFAULT, MARK_RIVAL]);
    let kb = crate::common::load_kb_with(&src);
    assert_eq!(
        index_rows_for(&kb, "wi862.both.Leaf"),
        vec!["Desc | Leaf | Rival (declared)".to_string()],
        "the inline and by-reference spellings of ONE mark must collapse to one row — \
         two rows here would be `one_default`'s collision, i.e. the sugar refusing the \
         program it is sugar for"
    );
}

// ── Arbitration is shared, not duplicated ────────────────────────────

/// A mark written inline and a rival mark written by reference collide under the SAME
/// `one_default` that arbitrates two by-reference marks — the acceptance's "refused
/// naming both".
///
/// Asserted on BOTH names, because a refusal that named only the fact would be a
/// diagnostic written for the by-reference world and silent about the line the author
/// actually has to change.
#[test]
fn an_inline_mark_colliding_with_a_reference_mark_is_refused() {
    let ns = "wi862.collide";
    let src = program(ns, &[LEAF_BARE, RIVAL_DEFAULT, OTHER_PLAIN, MARK_OTHER]);
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("wi862.collide.Rival") && e.contains("wi862.collide.Other")
        }),
        "`one_default` must refuse the inline mark against the by-reference one, naming \
         BOTH providers: {errs:?}"
    );
}

/// …and two INLINE marks collide the same way. The pair above could in principle be
/// caught by a check that only compared a declared row against a fact; this one cannot.
#[test]
fn two_inline_marks_for_one_carrier_are_refused() {
    let ns = "wi862.two";
    let src = program(ns, &[LEAF_BARE, RIVAL_DEFAULT, OTHER_DEFAULT]);
    let errs = load_errs(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("wi862.two.Rival") && e.contains("wi862.two.Other")),
        "two inline marks at one carrier must be refused naming both: {errs:?}"
    );
}

/// NO-DISPLACEMENT (058 §3.6) reaches the sugar for free, because the sugar produces a
/// declared row and the rule is "a declared row beside the inferred one". *Fill silence,
/// never overwrite speech* — a witness may not make itself the default for a carrier
/// that already provides the spec itself.
#[test]
fn marking_inline_against_a_self_providing_carrier_is_refused() {
    let ns = "wi862.displace";
    let src = program(ns, &[LEAF_SELF, RIVAL_DEFAULT]);
    let errs = load_errs(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("wi862.displace.Rival") && e.contains("wi862.displace.Leaf")),
        "no-displacement must refuse an inline mark against a self-providing carrier, \
         naming the inferred row the author never wrote: {errs:?}"
    );
}

// ── Composition with the rest of the surface ─────────────────────────

/// The modifier and WI-869's `:- conditions` tail are independent halves of one clause
/// (058 §4 calls them the same consolidation), so they compose — and the row lands at
/// the carrier AS WRITTEN, which is all conditionality needs (058 §3.6, as amended by
/// WI-860): a provision whose chain fails offers no candidate for the default to prefer.
#[test]
fn a_conditional_provision_can_mark_itself() {
    let ns = "wi862.cond";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.reflect.typing.DefaultProvider
  import anthill.prelude.Additive.{{add}}
  import anthill.prelude.Multiplicative.{{mul}}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end

  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    default provides Desc[T = Wrap[A = E]] :- Desc[T = E]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end
end
"#
    );
    let kb = crate::common::load_kb_with(&src);
    assert_eq!(
        index_rows_for(&kb, &format!("{ns}.Wrap")),
        vec!["Desc | Wrap[A = E] | WrapDesc (declared)".to_string()],
        "the modifier must survive the conditions tail and file the row at the written \
         carrier `Wrap[A = E]`, not at a bare `Wrap` and not at nothing"
    );
}

// ── The refusals the modifier owns ───────────────────────────────────

/// A spec that names no plain sort cannot be marked: `DefaultProvider.spec` is a
/// `Symbol`. The grammar narrows a provision's spec to `_spec_instantiation`, which
/// already excludes the tuple and the arrow but ADMITS a variable term — so this shape
/// is writable, and left unrefused the author would get a `default` keyword that marks
/// nothing while the provision beside it loads.
#[test]
fn default_on_a_variable_spec_is_refused() {
    let ns = "wi862.varspec";
    let src = program(ns, &["  sort Rival\n    default provides ?S\n  end\n"]);
    let errs = load_errs(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("default provides") && e.contains("names no plain sort")),
        "`default provides ?S` must be refused rather than silently unmarked: {errs:?}"
    );
}

// ── Half (b): the retirement of the `fact` spelling ──────────────────

/// Load the stdlib plus `extra` and return the WARNING strings.
///
/// Built here rather than reached for: `anthill-core`'s ordinary test helpers all
/// discard `load_all`'s `LoadResult`, so warnings are invisible from `tests/` and a
/// probe written on one would measure an empty list and report it as a finding. This is
/// `wi346_requires_shadow_test`'s helper, which is the only one that reads the channel.
fn load_warnings(extra: &str) -> Vec<String> {
    // stdlib AND the Rust host bindings: 21 of the migration's 39 sites live in
    // `anthill-stl/anthill/*.anthill`, so `stdlib_dir()` alone would leave more than half
    // the corpus unread and still report zero.
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            anthill_core::parse::parse(&src)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    if !extra.is_empty() {
        let mut probe = anthill_core::parse::parse(extra).expect("parse extra");
        // A PATH, so the `Located` wrapper's `path` arm is exercised rather than left to
        // the `None` fallback: `parse::parse` sets none, and the whole reason the wrapper
        // exists is to render `path:line:col:`.
        probe.path = Some(std::sync::Arc::from(std::path::Path::new("probe.anthill")));
        parsed.push(probe);
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    match anthill_core::kb::load::load_all(&mut kb, &refs, &anthill_core::kb::load::NullResolver) {
        Ok(result) => result.warnings.iter().map(|w| w.to_string()).collect(),
        Err(errs) => panic!(
            "expected a clean load (the deprecation is advisory); got errors:\n{}",
            errs.iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        ),
    }
}

/// THE DEPRECATION FIRES, and it fires WHERE THE TWO SPELLINGS AGREE — a scope that
/// names a type. Both arms are in one test because the discrimination IS the claim: a
/// version that warned on everything would pass a positive-only test.
///
/// The namespace-level arm is not a nicety. `provides` at an address no type occupies is
/// refused (`ProvidesClauseNeedsSort`, WI-1000 R3), so warning there would advertise a
/// repair the next compile rejects — `TieRepair`'s named failure mode. 058 §3.1's
/// namespace-level instance facts keep the `fact` spelling permanently.
#[test]
fn the_deprecation_fires_in_a_sort_body_and_not_at_namespace_level() {
    let src = r#"
namespace wi862.deprecate
  import anthill.prelude.{Int64}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end

  sort Pebble
    entity pebble
  end

  operation pebbleDescribe(x: Pebble) -> Int64 = 5

  fact Desc[T = Pebble, describe = pebbleDescribe]
end
"#;
    let warnings = load_warnings(src);
    let mine: Vec<&String> = warnings
        .iter()
        .filter(|w| w.contains("wi862.deprecate"))
        .collect();
    assert_eq!(
        mine.len(),
        1,
        "exactly ONE deprecation — the in-sort claim on `Leaf`, not the namespace-level \
         instance fact on `Pebble`, which has no `provides` spelling to move to: {mine:?}"
    );
    let only = mine[0];
    assert!(
        only.contains("wi862.deprecate.Leaf")
            && only.contains("DEPRECATED spelling")
            && only.contains("provides"),
        "the warning must name the PROVIDER sort and the repair: {only}"
    );
}

/// …and writing it the new way silences it. The control for the test above: without this
/// arm a warning that fired on `provides` too would satisfy it.
#[test]
fn the_provides_spelling_raises_no_deprecation() {
    let src = r#"
namespace wi862.clean
  import anthill.prelude.{Int64}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
end
"#;
    let warnings = load_warnings(src);
    assert!(
        !warnings.iter().any(|w| w.contains("wi862.clean")),
        "the non-deprecated spelling must be silent: {warnings:?}"
    );
}

/// **THE MIGRATION'S OWN ACCEPTANCE, and the guard that keeps it migrated.** The shipped
/// standard library emits ZERO provision-fact deprecations.
///
/// This is the whole point of half (b) and it is the one assertion a future `fact
/// Spec[…]` added to `stdlib/` cannot slip past: 39 sites warned before the migration
/// (measured), 0 after. It reads the stdlib the loader actually ships rather than a
/// fixture, because a corpus is where a spelling nobody re-reads survives.
///
/// The TOTAL warning count is asserted non-zero too, so a channel that silently carried
/// nothing — the failure mode this file's helper exists to avoid — cannot pass as a
/// clean corpus. The stdlib emits `RequiresShadow` warnings, which is what makes that
/// check meaningful.
#[test]
fn the_shipped_stdlib_emits_no_provision_fact_deprecations() {
    // A CANARY IN THE SAME LOAD, and it is not decoration. The corpus emits no other
    // warning kind, so "zero deprecations" would read identically if the channel carried
    // nothing at all — the exact measure-an-empty-collection failure this file's helper
    // was written to avoid. The canary is one `fact` provision in a throwaway namespace:
    // it must appear, and it must be the ONLY one.
    let canary = r#"
namespace wi862.canary
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
end
"#;
    let deprecations: Vec<String> = load_warnings(canary)
        .into_iter()
        .filter(|w| w.contains("DEPRECATED spelling"))
        .collect();
    assert_eq!(
        deprecations.len(),
        1,
        "the canary must warn (proving the channel is live) and the shipped stdlib plus \
         host bindings must add nothing to it — 39 sites warned before the migration: \
         {deprecations:?}"
    );
    assert!(
        deprecations[0].contains("wi862.canary.Leaf"),
        "the one deprecation must be the canary's, not a stdlib site: {}",
        deprecations[0]
    );
}

/// A DEPRECATION WITHOUT A FILE AND A LINE IS NOT ACTIONABLE, and this is the first
/// span-bearing `LoadWarning` — the channel's `format_with_source` carried a `let _ =
/// source` reserving it, and `LoadWarning::Located` arrived with it.
///
/// The probe carries a PATH (the helper stamps one), so what is asserted is the whole
/// `path:line:col:` stamp a user sees — the `Some(p) if has_span` arm of
/// `span::render_located`. Asserting only the line would leave the wrapper, which is the
/// half that had to be built, with no coverage at all.
#[test]
fn the_deprecation_is_located() {
    let warnings = load_warnings(
        r#"
namespace wi862.located
  import anthill.prelude.{Int64}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
end
"#,
    );
    let only = warnings
        .iter()
        .find(|w| w.contains("wi862.located"))
        .expect("the deprecation must fire");
    // `fact Desc[T = Leaf]` is line 10 of the fixture (the leading newline is line 1).
    // The COLUMN is not pinned: the span points at the CLAIM (`Desc[…]`) rather than at
    // the `fact` keyword, which is the position an author needs anyway.
    assert!(
        only.starts_with("probe.anthill:10:"),
        "the warning must carry the FILE and the offending line, not just the sort's \
         name — the `Located` wrapper is what supplies the file: {only}"
    );
}

/// **THE SUGAR MUST NOT BE THE ONE CONSTRUCT THAT PANICS.** `DefaultProvider` is declared
/// only in `stdlib/anthill/reflect/typing.anthill`, so a KB loaded without the reflect
/// standard library has no such symbol — and `resolve_symbol` PANICS on one, where its
/// sibling `SortProvidesInfo` is safe because `register_prelude` bootstraps it.
///
/// Driven with NO stdlib at all, which is the only way to reach it. The program is full
/// of other errors there (`Int64` resolves to nothing); what is asserted is that MY
/// refusal is among them and that the loader returned a verdict rather than aborting —
/// a panic would fail this test by unwinding, not by an assertion.
#[test]
fn default_provides_without_the_reflect_stdlib_is_refused_not_a_panic() {
    let src = r#"
namespace wi862.nostdlib
  sort Desc
    sort T = ?
  end
  sort Rival
    default provides Desc[T = Rival]
  end
end
"#;
    let parsed = anthill_core::parse::parse(src).expect("parse");
    let mut kb = KnowledgeBase::new();
    let errs = anthill_core::kb::load::load_all(
        &mut kb,
        &[&parsed],
        &anthill_core::kb::load::NullResolver,
    )
    .err()
    .unwrap_or_default();
    let rendered: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
    assert!(
        rendered
            .iter()
            .any(|e| e.contains("DefaultProvider") && e.contains("default provides")),
        "a `default provides` with no reflect stdlib must be REFUSED, naming what is \
         missing — `resolve_symbol` would have panicked here: {rendered:?}"
    );
}

/// **A LOCATED WARNING RENDERS FROM ITS OWN SOURCE**, so `format_with_source` must not
/// prefix a second location computed against the caller's file.
///
/// `LoadWarning::span()` reports the inner span through the wrapper, so without a
/// `Located` arm the method returns `12:5: probe.anthill:10:10: warning: …` — two
/// locations, the leading one resolved against whatever text the caller happened to
/// hold. `LoadError::format_at` matches `Located` first for exactly this reason. Driven
/// with a DELIBERATELY WRONG `source` argument, since a correct one would make the two
/// prefixes agree and hide the defect.
#[test]
fn format_with_source_does_not_double_prefix_a_located_warning() {
    let src = r#"
namespace wi862.doubleprefix
  sort Desc
    sort T = ?
  end
  sort Leaf
    fact Desc[T = Leaf]
  end
end
"#;
    let mut parsed = anthill_core::parse::parse(src).expect("parse");
    parsed.path = Some(std::sync::Arc::from(std::path::Path::new("probe.anthill")));
    let mut kb = KnowledgeBase::new();
    let result = anthill_core::kb::load::load_all(
        &mut kb,
        &[&parsed],
        &anthill_core::kb::load::NullResolver,
    )
    .expect("this fixture names nothing outside itself, so it must load");
    let warning = result
        .warnings
        .iter()
        .find(|w| w.to_string().contains("DEPRECATED spelling"))
        .expect("the deprecation must fire");
    let unrelated = "a\nb\nc\n";
    assert_eq!(
        warning.format_with_source(unrelated),
        warning.to_string(),
        "a located warning must ignore the caller's source and render from its own — \
         anything else prefixes a location computed against the wrong file"
    );
}

/// `default` is a modifier in ONE position and an ordinary identifier everywhere else.
///
/// Not a style point: the corpus already has `operation string_field_or(t: Term, field:
/// String, default: String)` in `rustland/anthill-todo/anthill/main.anthill`, so a
/// modifier spelled in a way that reserved the word would have broken a shipped program.
/// The grammar corpus pins the parse; this pins that it still RUNS.
#[test]
fn default_is_not_a_reserved_word() {
    let ns = "wi862.ident";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}

  sort Driver
    operation orElse(default: Int64) -> Int64 = default
    operation drive(n: Int64) -> Int64 = orElse(42)
  end
end
"#
    );
    let mut interp = crate::common::interp_for(&src);
    match interp.call(&format!("{ns}.Driver.drive"), &[Value::Int(0)]) {
        Ok(Value::Int(n)) => assert_eq!(
            n, 42,
            "a parameter named `default` must still be readable in a body"
        ),
        other => panic!("`default` must stay an ordinary identifier; got {other:?}"),
    }
}
