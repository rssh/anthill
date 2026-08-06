//! WI-860 (proposal 058 phase 8b) — the DEFAULTS SUBSTRATE: `DefaultProvider` rows,
//! `self_provides` / `default_provider`, and the two load checks.
//!
//! 058 §3.6's learnable core, which is what these tests are organised around:
//!
//! > a silent dispatch takes the carrier's own provision, or the one a
//! > `DefaultProvider` fact names; two such rows for one carrier refuse to load;
//! > no row means say which.
//!
//! NOTHING CONSUMES THE INDEX YET — rung 2a (the classifier's tie reading it) is phase
//! 8c, WI-861. So every test here drives the RELATION or the REFUSAL, never a dispatch:
//! a green load proves nothing about a relation whose consumers do not exist, which is
//! exactly the shape "it loads clean is not evidence" warns about.
//!
//! | claim | driven by |
//! |---|---|
//! | the relations answer, and the Rust index materializes THE SAME rows | `the_index_materializes_the_relation_over_the_whole_corpus` |
//! | the carrier's own provision is its default, inferred | `a_carriers_own_provision_is_its_inferred_default` |
//! | a mark names an existing provider; the carrier is DERIVED | `a_declared_mark_takes_its_carrier_from_the_providers_provision` |
//! | `one_default` refuses two declared rows | `two_marked_rivals_for_one_carrier_are_refused` |
//! | NO-DISPLACEMENT, derived — refused BY `one_default`, naming the inferred row | `marking_a_rival_against_a_self_providing_carrier_is_refused` |
//! | a ground row beside a parametric one for one family is refused | `a_ground_default_beside_a_parametric_one_is_refused` |
//! | …and two DISJOINT ground rows are NOT (the control for that rule) | `two_disjoint_ground_defaults_coexist` |
//! | check 1: a mark on a non-provider is refused | `a_mark_on_a_sort_that_does_not_provide_the_spec_is_refused` |
//! | a CONDITIONAL provision's mark loads, at the carrier its provision claims | `a_conditional_provisions_default_is_recorded_at_its_written_carrier` |
//! | the fork WI-859 left: a carrier owning no member still self-provides | `a_carrier_owning_no_member_still_self_provides` |
//! | both faces of each refusal render ONE message body | `the_two_faces_of_each_refusal_are_one_message` |
//! | a mark written as a RULE is refused, not silently skipped | `a_default_provider_written_as_a_rule_is_refused` |
//!
//! WHAT FAILS IF THIS IS BACKED OUT — MEASURED, one back-out at a time, not predicted,
//! and RE-measured after the review's changes rather than carried over:
//!
//! * the INFERRED leg deleted → 4 fail: `a_carriers_own_provision_is_its_inferred_default`,
//!   `marking_a_rival_against_a_self_providing_carrier_is_refused` (which then LOADS —
//!   no-displacement is that leg and nothing else), `a_carrier_owning_no_member_still_
//!   self_provides`, and the corpus agreement test. The other 8 pass either way, by
//!   design: they are the declared leg and the refusals it alone reaches.
//! * `carrier_views_overlap` reduced to base-symbol equality — the obvious thing to
//!   reach for, since a dispatch carrier IS a symbol everywhere else — → 1 fails,
//!   `two_disjoint_ground_defaults_coexist`, which is that rule's only control.
//! * `DefaultCollision` collapsed to one wording (the pre-review state) → 4 fail, one
//!   per arm plus the two-faces test. Each arm therefore has a control, which is the
//!   property `TieRepair`'s doc demands and the property WI-1012 found WI-842's test
//!   lacking.
//! * the derived-mark refusal deleted → 1 fails,
//!   `a_default_provider_written_as_a_rule_is_refused`.
//! * `type_display_name_occ`'s new `Expr::Apply` arm deleted → 1 fails across the whole
//!   2307-test binary, `a_conditional_provisions_default_is_recorded_at_its_written_carrier`.
//!   So the arm is driven, and adding it moved no other diagnostic's text.
//!
//! REFERENCE: proposal 058 §3.6; `docs/design/058-implementation.md` §6, §19.

use anthill_core::kb::defaults::DefaultCollision;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::typing::type_display_name_value;
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// The load diagnostics of `src`, empty when it loads clean.
fn load_errors(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// Resolve `anthill.reflect.typing.<rel>` at the given arity with every argument a
/// fresh variable, rendering each solution as `"a | b | …"` — the RELATION's own answer,
/// read through SLD, which is the only reading that can disagree with the Rust index.
///
/// Rendered through `type_display_name_value`, the CARRIER-NEUTRAL renderer, because
/// these answers arrive on both carriers: a name normalized by `extract_sort_ref` comes
/// back as a `Value::Term`, while a field read straight off a matched fact comes back as
/// a `Value::Node` occurrence. Gating on `Value::Term` here panicked on the declared
/// leg alone.
fn relation_rows(kb: &mut KnowledgeBase, rel: &str, arity: usize) -> Vec<String> {
    let qn = format!("anthill.reflect.typing.{rel}");
    let sym = kb
        .try_resolve_symbol(&qn)
        .unwrap_or_else(|| panic!("`{qn}` does not resolve — the relation did not load"));
    let vars: Vec<_> = (0..arity)
        .map(|i| {
            let s = kb.intern(&format!("a{i}"));
            let vid = kb.fresh_var(s);
            kb.alloc(Term::Var(Var::Global(vid)))
        })
        .collect();
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(&vars),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let mut out: Vec<String> = sols
        .iter()
        .map(|sol| {
            let cells: Vec<String> = vars
                .iter()
                .map(|v| {
                    let bound = kb.reify(*v, &sol.subst);
                    type_display_name_value(kb, &bound)
                })
                .collect();
            cells.join(" | ")
        })
        .collect();
    out.sort();
    out.dedup();
    out
}

/// The materialized index's rows, through its OWN rendered probe — the same `spec |
/// carrier | provider` shape [`relation_rows`] renders `default_provider(?S, ?C, ?W)`
/// into, so the two are comparable as sets. WI-859's rule: a probe hands out a rendering,
/// not a `TermId` whose meaning is internal to the store.
fn index_rows(kb: &KnowledgeBase) -> Vec<String> {
    kb.default_provider_index()
        .expect("a loaded KB must carry the default-provider index")
        .rendered_rows(kb)
}

/// The index's rows for ONE carrier, WITH each row's origin.
fn index_rows_for(kb: &KnowledgeBase, carrier_qn: &str) -> Vec<String> {
    kb.default_provider_index()
        .expect("a loaded KB must carry the default-provider index")
        .rendered_rows_for_carrier(kb, carrier_qn)
}

/// A local spec + a self-providing carrier, with `extra` appended — so every fixture
/// below is this program plus a delta, and a control is the same program minus the
/// delta rather than a retyped twin.
fn program(ns: &str, extra: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
{extra}end
"#
    )
}

/// THE ACCEPTANCE, and the guard against the one failure this arrangement invites.
///
/// 058 §3.6 puts the defaults in the reflect layer and `docs/design/058-implementation.md`
/// §6 materializes them into a Rust index "the `EqDispatchIndex` pattern — the relations
/// are the authority, the hot path reads the index". Two derivations of one relation is
/// precisely the shape WI-838's cross-kind blind spot was built out of, so this asserts
/// they answer THE SAME ROWS — over the whole stdlib and the Rust host bindings, not
/// over a fixture, since the corpus is where a policy the Rust side inherited by
/// accident would show.
///
/// Both sides must be non-trivial for the equality to mean anything: the stdlib is full
/// of self-providing carriers, so the row count is asserted to be large rather than
/// merely equal. (A pass that returned nothing and a relation that answered nothing
/// would otherwise agree perfectly.)
#[test]
fn the_index_materializes_the_relation_over_the_whole_corpus() {
    let mut kb = crate::common::load_kb_with(&program("test.wi860.agree", ""));
    let from_relation = relation_rows(&mut kb, "default_provider", 3);
    let from_index = index_rows(&kb);
    assert!(
        from_relation.len() > 50,
        "the stdlib's self-providing carriers should give the relation many rows, got {}: {:?}",
        from_relation.len(),
        from_relation
    );
    assert_eq!(
        from_relation, from_index,
        "the SLD relation and the materialized index must answer the same rows — the \
         relation is the authority and the index is its materialization, so a difference \
         is a drift, not a preference"
    );
}

/// "The carrier's own provision is its default", INFERRED — the clause that lets the
/// shipped standard library carry defaults with no edits at all (058 §3.6).
///
/// Driven at both layers: `self_provides` answers the pair, and the index holds the row
/// with `origin = Inferred`. The origin is asserted rather than assumed because it is
/// what a displacement diagnostic prints, and a row derived by the DECLARED leg would
/// satisfy every other assertion here.
#[test]
fn a_carriers_own_provision_is_its_inferred_default() {
    let mut kb = crate::common::load_kb_with(&program("test.wi860.own", ""));
    assert!(
        relation_rows(&mut kb, "self_provides", 2).contains(&"Leaf | Desc".to_string()),
        "`self_provides` must hold for a carrier's own provision: {:?}",
        relation_rows(&mut kb, "self_provides", 2)
            .into_iter()
            .filter(|r| r.contains("Leaf"))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        index_rows_for(&kb, "test.wi860.own.Leaf"),
        vec!["Desc | Leaf | Leaf (inferred from the carrier's own provision)".to_string()],
        "one carrier, one own provision, ONE row — and INFERRED, which is the half a \
         no-displacement diagnostic names and the half a DECLARED mark on the same \
         carrier would also satisfy every other assertion here"
    );
}

/// A DECLARED mark states `(spec, provider)` and NOT the carrier: the carrier is derived
/// from the provider's own provision (058 §3.6). This is the clause that makes a mark
/// usable on a library you cannot edit, and the one that makes conditionality compose.
///
/// `Twig` is a WITNESS for `Leaf` — a rival backend for a carrier that does not provide
/// `Desc` itself, which is why marking it is legal here and refused in
/// `marking_a_rival_against_a_self_providing_carrier_is_refused`.
#[test]
fn a_declared_mark_takes_its_carrier_from_the_providers_provision() {
    let src = r#"namespace test.wi860.declared
  import anthill.prelude.Int64
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort Twig
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact DefaultProvider(spec: Desc, provider: Twig)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert!(
        relation_rows(&mut kb, "default_provider", 3).contains(&"Desc | Leaf | Twig".to_string()),
        "the mark names (Desc, Twig) and the relation must supply the CARRIER `Leaf` \
         from Twig's own provision: {:?}",
        relation_rows(&mut kb, "default_provider", 3)
            .into_iter()
            .filter(|r| r.contains("Twig"))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        index_rows_for(&kb, "test.wi860.declared.Leaf"),
        vec!["Desc | Leaf | Twig (declared)".to_string()],
        "the row is keyed at the CARRIER `Leaf` and names the marked PROVIDER `Twig`"
    );
}

/// `one_default` — two marked rivals for one carrier refuse to load, NAMING BOTH.
///
/// A default is what a call that says NOTHING takes, so unlike a tier-3 tie there is no
/// use site at which to select: the refusal has to be at load or nowhere.
#[test]
fn two_marked_rivals_for_one_carrier_are_refused() {
    let src = r#"namespace test.wi860.two
  import anthill.prelude.Int64
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort Twig
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  sort Branch
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
  end

  fact DefaultProvider(spec: Desc, provider: Twig)
  fact DefaultProvider(spec: Desc, provider: Branch)
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| {
            e.contains("ambiguous default: carrier 'Leaf' has 2 default providers")
                && e.contains("test.wi860.two.Twig")
                && e.contains("test.wi860.two.Branch")
                && e.contains("keep exactly one `DefaultProvider(spec: Desc, provider: …)` row \
                              per carrier")
        }),
        "`one_default` must refuse the pair, name BOTH declarations, and give the \
         SAME-CARRIER repair — one carrier, one row: {errs:?}"
    );
    // THE CONTROL: the same program with ONE mark loads. Without it the assertion above
    // would also pass on a check that refused every marked program.
    let one = src.replace("  fact DefaultProvider(spec: Desc, provider: Branch)\n", "");
    assert!(load_errors(&one).is_empty(), "one mark must load: {:?}", load_errors(&one));
}

/// NO-DISPLACEMENT, and it needs NO RULE: for a self-providing carrier the inferred row
/// already exists, so an explicit mark naming a rival violates `one_default`.
///
/// *Fill silence, never overwrite speech* — no one line can flip what every linked
/// library's bracket-less dispatch means. The diagnostic must NAME the inferred row, or
/// the author reads `one_default` as firing on a single declaration they wrote once.
///
/// This is the test the ticket's acceptance names, and the one that fails if the
/// INFERRED leg is deleted: with only declared rows the program below loads clean.
#[test]
fn marking_a_rival_against_a_self_providing_carrier_is_refused() {
    let rival = r#"
  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact DefaultProvider(spec: Desc, provider: Rival)
"#;
    let errs = load_errors(&program("test.wi860.displace", rival));
    assert!(
        errs.iter().any(|e| {
            e.contains("default displaced: carrier 'Leaf' provides")
                && e.contains("test.wi860.displace.Rival")
                && e.contains("inferred from the carrier's own provision")
                && e.contains("fill silence, never overwrite speech")
                && e.contains("`[Desc = <provider>]` bracket")
        }),
        "the displacing mark must be refused BY `one_default`, with the INFERRED row \
         NAMED — an author who wrote one line must be told what the second row is — and \
         with the DISPLACEMENT repair, not the delete-a-duplicate one: {errs:?}"
    );
    // THE CONTROL, and it is what makes the refusal about DISPLACEMENT rather than about
    // the rival existing: the identical program with the mark deleted LOADS. Two
    // providers coexist (058 tier 3); only the DEFAULT is unique.
    let unmarked = rival.replace("  fact DefaultProvider(spec: Desc, provider: Rival)\n", "");
    let errs = load_errors(&program("test.wi860.coexist", &unmarked));
    assert!(errs.is_empty(), "an unmarked rival must still coexist: {errs:?}");
}

/// Two default rows whose carriers UNIFY are refused — a ground row beside a parametric
/// one for one family.
///
/// Admitting the pair would mean RANKING defaults by specificity at every silent
/// dispatch, a tier the ladder does not have. 058 §3.6 pins the refusal rather than
/// inheriting the question, and `docs/design/058-implementation.md` §6 says why: it is a
/// boundary-3-style widening and would need its own measurement.
#[test]
fn a_ground_default_beside_a_parametric_one_is_refused() {
    let errs = load_errors(&overlapping_program("test.wi860.overlap", "Int64", "E"));
    assert!(
        errs.iter().any(|e| {
            e.contains("overlapping defaults")
                && e.contains("Box[T = Int64]")
                && e.contains("Box[T = E]")
                && e.contains("test.wi860.overlap.Ground")
                && e.contains("test.wi860.overlap.Param")
                && e.contains("Give the two marks disjoint carriers, or delete one")
        }),
        "`Box[T = Int64]` and `Box[T = E]` are one family and two rows — and the message \
         must be the OVERLAPPING one, naming BOTH carriers. The same-carrier wording \
         (\"carrier 'X' has 2 default providers … keep exactly one row per carrier\") \
         describes a different program and advises a repair already satisfied here: \
         {errs:?}"
    );
}

/// THE CONTROL for the rule above, and the arm that makes it UNIFICATION rather than
/// "same base sort": two GROUND rows at disjoint applications of one family coexist.
///
/// `Box[T = Int64]` and `Box[T = String]` share a base and describe no carrier in
/// common, so neither is ever consulted where the other applies. A check keyed on the
/// carrier's base SYMBOL — the key every dispatch reader uses, and the obvious thing to
/// reach for — refuses this program; that is the whole reason a default row keeps the
/// carrier VIEW beside its base.
#[test]
fn two_disjoint_ground_defaults_coexist() {
    let src = overlapping_program("test.wi860.disjoint", "Int64", "String");
    assert!(
        load_errors(&src).is_empty(),
        "two defaults at DISJOINT applications of one family must load: {:?}",
        load_errors(&src)
    );
    let kb = crate::common::load_kb_with(&src);
    let mut rows = index_rows_for(&kb, "test.wi860.disjoint.Box");
    rows.sort();
    assert_eq!(
        rows,
        vec![
            "Desc | Box[T = Int64] | Ground (declared)".to_string(),
            "Desc | Box[T = String] | Param (declared)".to_string(),
        ],
        "both rows key the same carrier BASE — which is exactly why the check cannot"
    );
}

/// Two witnesses for one parametric family, each marked default, at the applications
/// `a` and `b`. `E` is `Param`'s own type parameter, so passing it yields the PARAMETRIC
/// carrier `Box[T = E]`; any sort name yields a ground one.
fn overlapping_program(ns: &str, a: &str, b: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, String}}
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Box
    sort T = ?
    entity box(v: T)
  end

  sort Ground
    provides Desc[T = Box[T = {a}]]
    operation describe(x: Box[T = {a}]) -> Int64 = 1
  end

  sort Param
    sort E = ?
    provides Desc[T = Box[T = {b}]]
    operation describe(x: Box[T = {b}]) -> Int64 = 2
  end

  fact DefaultProvider(spec: Desc, provider: Ground)
  fact DefaultProvider(spec: Desc, provider: Param)
end
"#
    )
}

/// CHECK 1 (058 §3.5, re-read at load) — a mark naming a sort that does not provide the
/// spec is refused, and the message says what DOES provide it.
///
/// Not merely a courtesy: the row's carrier is DERIVED from the provider's provision, so
/// without this check the mark names no carrier, produces no row, and does nothing — an
/// author would have written a default and gotten silence.
#[test]
fn a_mark_on_a_sort_that_does_not_provide_the_spec_is_refused() {
    let stray = r#"
  sort Stray
    entity stray
  end

  fact DefaultProvider(spec: Desc, provider: Stray)
"#;
    let errs = load_errors(&program("test.wi860.check1", stray));
    assert!(
        errs.iter().any(|e| {
            e.contains("DefaultProvider(spec: Desc, provider: Stray)")
                && e.contains("does not provide the spec")
                && e.contains("test.wi860.check1.Leaf")
        }),
        "the mark must be refused, and the candidates that DO provide `Desc` named: {errs:?}"
    );
    // THE CONTROL: marking the sort that DOES provide it is the same program otherwise,
    // and it loads. (`Leaf` self-provides, so the mark is the same row said twice — see
    // `carriers_provided_by`'s dedup, not a displacement.)
    let marked = stray.replace("provider: Stray", "provider: Leaf");
    let errs = load_errors(&program("test.wi860.check1ok", &marked));
    assert!(errs.is_empty(), "marking the actual provider must load: {errs:?}");
}

/// A CONDITIONAL provision's default row is recorded AT THE CARRIER ITS PROVISION
/// CLAIMS — `Box[T = E]`, not `Box` — which is what 058 §3.6 means by the mark deriving
/// its carrier from the provider's own provision.
///
/// AND THE MEASUREMENT THAT CORRECTS THE PROPOSAL'S WORDING. §3.6 says conditionality
/// "composes for free" because "the rule joins the mark with `provides`, and a
/// conditional provision provides only where its chain discharges". MEASURED here: the
/// reflect `provides` relation holds UNCONDITIONALLY — WI-1033 states it outright
/// (`provides` says the claim was written, `provides_when` says under what) — so
/// `default_provider` answers at `Box[T = E]` for every `E`, not only where the
/// condition holds. What actually composes is narrower and still sufficient: the row
/// carries the carrier AS WRITTEN, so the default can only ever be consulted for a
/// candidate that ALREADY resolved, and a provision whose condition fails produces no
/// candidate to prefer. The conditionality is the provision's, enforced where the
/// provision is used — not a filter on this relation.
///
/// "Vacuously inert while no rival exists" is the acceptance's other half, asserted as
/// exactly one row for the carrier.
#[test]
fn a_conditional_provisions_default_is_recorded_at_its_written_carrier() {
    let src = r#"namespace test.wi860.conditional
  import anthill.prelude.Int64
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Box
    sort T = ?
    entity box(v: T)
  end

  sort BoxDesc
    sort E = ?
    provides Desc[T = Box[T = E]] :- Desc[T = E]
    operation describe(x: Box[T = E]) -> Int64 = 3
  end

  fact DefaultProvider(spec: Desc, provider: BoxDesc)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let rows = relation_rows(&mut kb, "default_provider", 3);
    assert!(
        rows.contains(&"Desc | Box[T = E] | BoxDesc".to_string()),
        "the row must key the carrier the provision WROTE — `Box[T = E]`, not `Box`: {:?}",
        rows.iter().filter(|r| r.contains("Box")).collect::<Vec<_>>()
    );
    assert_eq!(
        index_rows_for(&kb, "test.wi860.conditional.Box"),
        vec!["Desc | Box[T = E] | BoxDesc (declared)".to_string()],
        "one provision, one row, at the carrier the CLAUSE wrote — vacuously inert while \
         no rival exists"
    );
    // AGREEMENT ON A PARAMETRIC CARRIER. The corpus-wide agreement test cannot reach this:
    // every stdlib row is INFERRED, so its carrier is a minted bare name and the two sides
    // never compare a `Base[p = v]` rendering. Here they do, and it is the only place the
    // relation's occurrence-carried carrier is checked against the index's term-carried
    // one.
    assert!(
        index_rows(&kb).contains(&"Desc | Box[T = E] | BoxDesc".to_string()),
        "the index must render the parametric carrier the same way the relation does: {:?}",
        index_rows(&kb)
    );
}

/// BOTH FACES OF EACH REFUSAL RENDER ONE MESSAGE BODY, and this is not decoration.
///
/// `LoadError` has two renderings: `Display`, and `format_at` for a span-bearing error
/// wrapped in `Located`. A POST-LOAD pass's errors are never `Located`, so everything a
/// user sees — `anthill load`, `anthill check`, this suite — comes from `Display`.
/// MEASURED: the first cut put the actionable half (that a self-providing carrier is
/// ALREADY its own default, and what to delete) in `format_at` alone, where nothing could
/// reach it, and the CLI printed the terse sentence. Both faces now read one owner in
/// `kb::defaults`, so a future edit cannot re-open that gap silently.
///
/// Compared for EQUALITY rather than for family resemblance — the
/// `ambiguous_spec_op_dispatch_message` discipline, one refusal over. Neither variant is
/// span-bearing, so there is no `line:col` prefix to strip.
#[test]
fn the_two_faces_of_each_refusal_are_one_message() {
    use anthill_core::kb::load::LoadError;
    let ambiguous = LoadError::AmbiguousDefaultProvider {
        spec: "ns.Desc".to_string(),
        carrier: "Leaf".to_string(),
        providers: vec!["'ns.Rival' at carrier 'Leaf' (declared)".to_string()],
        collision: DefaultCollision::Displaced,
    };
    let not_a_provider = LoadError::DefaultProviderDoesNotProvide {
        spec: "ns.Desc".to_string(),
        provider: "ns.Stray".to_string(),
        provides: vec!["ns.Leaf".to_string()],
    };
    let loc = anthill_core::span::LineIndex::new("");
    for err in [&ambiguous, &not_a_provider] {
        let display = err.to_string();
        assert!(!display.is_empty(), "a face that rendered nothing would pass a bare equality");
        assert_eq!(display, err.format_at(&loc), "the two faces must render ONE message body");
    }
    // The clauses whose absence is the defect this pins — the repair, not the complaint.
    assert!(
        ambiguous.to_string().contains("fill silence, never overwrite speech"),
        "the displacement repair must reach the face the CLI prints: {ambiguous}"
    );
    assert!(
        not_a_provider.to_string().contains("would name no carrier and do nothing"),
        "check 1's reason must reach the face the CLI prints: {not_a_provider}"
    );
}

/// A `DefaultProvider` written as a RULE is REFUSED — the one shape where the relation
/// and the index would answer different things.
///
/// `default_provider` resolves through SLD and would take a derived mark; the index and
/// both load checks read FACTS. MEASURED before the refusal existed: the program below
/// loaded clean, the relation answered the derived row, and the index held nothing for it
/// — a default that `one_default` could not arbitrate and check 1 never saw. So it is a
/// load error rather than a silent skip, and the repair names the form that works.
#[test]
fn a_default_provider_written_as_a_rule_is_refused() {
    let derived = r#"
  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact Marker(x: 1)

  rule DefaultProvider(spec: Desc, provider: Rival) :- Marker(x: 1)
"#;
    let errs = load_errors(&program("test.wi860.derived", derived));
    assert!(
        errs.iter().any(|e| {
            e.contains("is written as a RULE")
                && e.contains("staying invisible to `one_default` and to the materialized index")
                && e.contains("Write `fact DefaultProvider(spec: …, provider: …)`")
        }),
        "a derived mark must be refused, not skipped — the relation would answer from it: \
         {errs:?}"
    );
    // THE CONTROL, and it is what makes the refusal about the RULE FORM rather than about
    // the mark: the same program with `rule …:- Marker` replaced by a plain fact is
    // refused for a DIFFERENT reason (displacement), i.e. it gets past this reader.
    let as_fact = derived.replace("rule DefaultProvider(spec: Desc, provider: Rival) :- Marker(x: 1)",
                                  "fact DefaultProvider(spec: Desc, provider: Rival)");
    let errs = load_errors(&program("test.wi860.derivedctl", &as_fact));
    assert!(
        errs.iter().all(|e| !e.contains("is written as a RULE")),
        "the fact spelling must reach the ordinary checks: {errs:?}"
    );
}

/// THE FORK WI-859 LEFT FOR THIS PHASE, decided and driven: *does a carrier that owns no
/// member self-provide at all?*
///
/// YES. `self_provides` is a relation over PROVISIONS — who supplies the dictionary for
/// this `(spec, carrier)` — and a carrier whose spec ops all have DEFAULT BODIES supplies
/// a perfectly good dictionary made of those defaults. The alternative (gate the row on
/// `carrier_own_op`, the criterion `SupplyRoute::Own` uses) would make a carrier's
/// default row appear and disappear as its members are added and removed, which is not
/// what *the carrier's own instance* means.
///
/// It matters beyond the definition: with the gate, the program below would have NO
/// inferred row, so a mark on a rival would load — no-displacement would hold for
/// carriers with members and silently not for carriers without.
#[test]
fn a_carrier_owning_no_member_still_self_provides() {
    let src = r#"namespace test.wi860.nomember
  import anthill.prelude.Int64
  import anthill.reflect.typing.DefaultProvider

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert!(
        relation_rows(&mut kb, "self_provides", 2).contains(&"Leaf | Desc".to_string()),
        "a carrier whose spec op is served by a DEFAULT BODY still self-provides"
    );
    // The consequence, driven: no-displacement holds for it too. Built by reopening the
    // namespace rather than by `replace("end\n", …)`, which would also hit the two sort
    // terminators.
    let displacing = src.trim_end().trim_end_matches("end").to_string()
        + r#"
  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact DefaultProvider(spec: Desc, provider: Rival)
end
"#;
    let errs = load_errors(&displacing);
    assert!(
        errs.iter().any(|e| e.contains("default displaced: carrier 'Leaf' provides")),
        "the memberless carrier's inferred row must still refuse a displacing mark, with \
         the DISPLACEMENT wording: {errs:?}"
    );
}
