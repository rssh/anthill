//! WI-20260913-KXNEX — A WRITTEN `provides` CLAUSE MUST NAME A CARRIER.
//!
//! §5.1: "a `provides` clause names its PROVIDER by WHERE it is written, and its CARRIER
//! by its bindings". A clause over a spec that HAS a carrier parameter and binds nothing
//! at it therefore names no carrier — and until this ticket it LOADED CLEAN and failed
//! `OperationBodyMissing` at the first call, against a provider that implements the
//! operation.
//!
//! ## The measurement this is built on (WI-20260830-7MK73, commit ad00948e)
//!
//! `sort guardians.LiveLlm` declared `operation complete(self: LiveLlm, p: Prompt)` and
//! `provides Llm[E = {External}]`. `guardians.summarize(llm, …)`, whose body is
//! `llm.complete(p)`, driven with a `live_llm(…)` value, died
//! `OperationBodyMissing { name: "guardians.Llm.complete" }`. Writing
//! `provides Llm[C = LiveLlm, E = {External}]` fixed it with NO other change; the same
//! held for `FakeLlm`, and for the BARE `FileHarness provides Harness` /
//! `LoadChecker provides Checker`. Nothing reported any of the four at load.
//!
//! ## Why it was silent: two readers, one `None`
//!
//! The typer's provider-keyed reading accepted the clause; dispatch's carrier-keyed
//! reading (`provision_binds_param_to_carrier`) needs the carrier parameter bound and
//! found nothing. `provision_carrier_binding` answers `None` for BOTH shapes, and its own
//! doc audits the disagreement: the `dispatch_carrier` builtin mints the PROVIDER, while
//! the witness reader and the dot-call match DECLINE. This check does not reconcile the
//! two readings — it removes the shape that makes them differ for a clause an author
//! wrote. The refusal is a LOAD ERROR rather than a default of the carrier parameter to
//! the enclosing sort: decidable at the declaration, needing no call site, and the repair
//! it prescribes is one binding.
//!
//! ## What fails when the check is backed out
//!
//! ALL FOUR refusals: `a_provision_binding_a_non_carrier_parameter_is_refused`,
//! `a_bare_provision_of_a_carrier_parameter_spec_is_refused`,
//! `a_positional_binding_landing_on_a_non_carrier_parameter_is_refused`, and
//! `reverting_the_guardians_carrier_bindings_is_refused_at_load`, which drives the
//! original measurement over the shipped example. Every CONTROL here passes either way BY
//! DESIGN — each names a shape the rule must not touch, and a rule that refused one would
//! be caught by it. `a_bound_carrier_loads_and_the_abstract_call_dispatches` is the
//! exception among the controls, and the pairing is what makes it evidence rather than
//! decoration: MEASURED with the check backed out and `C = Impl` struck from its
//! provision, it LOADS CLEAN and then panics
//! `OperationBodyMissing { name: "test.kxnex.Spec.run" }` at the call — bit for bit the
//! guardians failure, reproduced in nine lines. It is the test that defect would have
//! been caught by, because it CALLS through an abstract receiver instead of asserting
//! that a declaration loaded.
//!
//! Enforcement: `kb::typing::check_provision_names_carrier`. Spec: kernel-language §5.1.
//! Adjacent, and NOT a prerequisite either way: WI-20260909-M8QWJ (could anything run a
//! body-less operation) — its question 3 defers exactly this case.

use anthill_core::eval::value::Value;

/// A spec with a carrier parameter `C` and an inert second parameter `U`, an implementing
/// carrier, and — the part that matters — an operation taking the spec ABSTRACTLY whose
/// body dot-calls the spec op. That last operation is the guardians `summarize` shape, and
/// it is what turns "the provision loaded" into "the provision dispatches".
///
/// `Spec.run` is deliberately BODY-LESS: with no default to fall back on, a `probe()`
/// that answers at all is proof the carrier's member was reached through the provision.
///
/// `U` STANDS IN FOR THE GUARDIANS ROW, and the substitution is deliberate. The measured
/// clause was `provides Llm[E = {{External}}]`, binding an EFFECT row and not the carrier;
/// what makes it the defect is "a parameter that is not the carrier", not which kind of
/// parameter. Using an inert type parameter keeps each refusal below to ONE diagnostic:
/// with a real row, `drive` must declare `effects {{s.E}}`, and a provision that names no
/// carrier ALSO leaves that projection unresolvable — a second, honest error that would
/// force these assertions to stop counting. The row shape itself is not lost: it is driven
/// verbatim, against the shipped sources, by
/// [`reverting_the_guardians_carrier_bindings_is_refused_at_load`].
fn program(provision: &str) -> String {
    format!(
        r#"namespace test.kxnex
  import anthill.prelude.Int64

  sort Spec
    sort C = ?
    sort U = ?
    operation run(self: C, p: Int64) -> Int64
  end

  sort Impl
    import anthill.prelude.Int64
    import test.kxnex.Spec
    entity impl
    operation run(self: Impl, p: Int64) -> Int64 = p + 1
    {provision}
  end

  operation drive(s: Spec, p: Int64) -> Int64 = s.run(p)
  operation probe() -> Int64 = drive(impl(), 41)
end
"#
    )
}

/// The load errors of a program, as rendered strings — `Vec::new()` when it loads.
fn load_errors(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(errs) => errs,
    }
}

/// EXACTLY ONE refusal, and it names each of the four things the diagnostic owes the
/// author: the spec, its carrier PARAMETER, the provider, and the repair. Asserting only
/// "it was refused" would pass for any unrelated load error the fixture happened to
/// provoke — and the parameter in particular is nowhere in the clause the author is
/// looking at (which parameter carries a spec is read off the spec's OPERATIONS), so a
/// message that omitted it would name no repair at all.
fn expect_carrier_refusal(errs: &[String], spec: &str, param: &str, provider: &str, why: &str) {
    assert_eq!(
        errs.len(),
        1,
        "{why}: expected exactly one refusal, got {errs:#?}"
    );
    let e = &errs[0];
    for needle in [
        spec,
        &format!("carrier parameter `{param}`"),
        provider,
        &format!("provides {spec}[{param} = {provider}"),
    ] {
        assert!(
            e.contains(needle),
            "{why}: the refusal must contain {needle:?} — got {e:?}"
        );
    }
}

// ── 1. The two refusals ──────────────────────────────────────────────────────────────

/// THE GUARDIANS SHAPE. `provides Spec[U = Int64]` binds a parameter that is not the
/// carrier and nothing at the carrier parameter, so it names no carrier — refused AT LOAD,
/// where it used to load clean and fault at the first call. The measured clause bound an
/// effect row in that position (`provides Llm[E = {External}]`); see [`program`] for why
/// the stand-in, and the guardians test below for the row itself.
#[test]
fn a_provision_binding_a_non_carrier_parameter_is_refused() {
    expect_carrier_refusal(
        &load_errors(&program("provides Spec[U = Int64]")),
        "test.kxnex.Spec",
        "C",
        "test.kxnex.Impl",
        "a provision binding everything but the carrier",
    );
}

/// THE BARE SHAPE — `FileHarness provides Harness`, the other half of the measurement.
/// It binds nothing at all, so it cannot name a carrier either.
///
/// NOT the same question as a bare provision of a spec with NO carrier parameter, which
/// `a_provision_of_a_carrier_parameter_less_spec_loads` keeps legal: the rule is about the
/// parameter existing and going unbound, never about the clause having no brackets.
#[test]
fn a_bare_provision_of_a_carrier_parameter_spec_is_refused() {
    expect_carrier_refusal(
        &load_errors(&program("provides Spec")),
        "test.kxnex.Spec",
        "C",
        "test.kxnex.Impl",
        "a bare provision of a carrier-parameter spec",
    );
}

// ── 2. The control that DRIVES the capability ────────────────────────────────────────

/// THE CONTROL THAT IS EVIDENCE, not decoration: the SAME program with `C = Impl` loads
/// AND the call dispatches. `drive`'s receiver is the abstract `Spec` and its body is
/// `s.run(p)`, so the answer can only come from `Impl.run` having been found THROUGH the
/// provision — which is precisely the step that was failing.
///
/// This is the test the original defect would have been caught by. Its predecessor in
/// `examples/guardians` had only ever been LOADED, and "it loads clean" is exactly what
/// the defect did.
#[test]
fn a_bound_carrier_loads_and_the_abstract_call_dispatches() {
    let src = program("provides Spec[C = Impl, U = Int64]");
    assert!(
        load_errors(&src).is_empty(),
        "binding the carrier must load: {:?}",
        load_errors(&src)
    );
    match crate::common::interp_for(&src)
        .call("test.kxnex.probe", &[])
        .unwrap_or_else(|e| panic!("call test.kxnex.probe: {e:?}"))
    {
        Value::Int(i) => assert_eq!(
            i, 42,
            "the abstract receiver must reach `Impl.run` through the provision"
        ),
        other => panic!("call test.kxnex.probe: expected Int, got {other:?}"),
    }
}

// ── 3. The controls the rule must not touch ──────────────────────────────────────────

/// A SPEC WITH NO CARRIER PARAMETER — §5.1's `sort List provides Stream[T, {}]` case, and
/// every SELF-REPRESENTING stdlib spec (`Stream`, `FiniteStream`, `LogicalStream`), whose
/// operations receive the spec ITSELF. There is no parameter to demand: dispatch is
/// directed by the receiver value's own sort, and the provision records its provider.
///
/// Measured shipped instance: `anthill.stage0.GithubForge provides Forge`, a BARE clause
/// in a secondary entry, where `Forge.*` take `f: Forge`.
#[test]
fn a_provision_of_a_carrier_parameter_less_spec_loads() {
    let src = r#"namespace test.kxnex.noparam
  import anthill.prelude.Int64

  sort SelfRep
    sort T = ?
    operation size(s: SelfRep) -> Int64
  end

  sort Holder
    entity holder
    operation size(s: Holder) -> Int64 = 3
    provides SelfRep
  end
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "a spec whose operations receive the spec itself has no carrier parameter to \
         bind, so a bare provision of it names its provider and is legal: {:?}",
        load_errors(src)
    );
}

/// A WITNESS — `sort LeafDesc { provides Desc[T = Leaf] }`, where provider and carrier are
/// DIFFERENT sorts (058 §3.6, WI-1069). It binds the carrier parameter explicitly, which
/// is the very thing this rule demands, so it must be untouched: the rule asks whether the
/// parameter is bound, never whether it is bound to the enclosing sort.
#[test]
fn a_witness_binding_a_foreign_carrier_loads() {
    let src = r#"namespace test.kxnex.witness
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort LeafDesc
    import anthill.prelude.Int64
    import test.kxnex.witness.Leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "a witness names its carrier in the binding: {:?}",
        load_errors(src)
    );
}

/// THE CARRIER BOUND TO THE PROVIDER'S OWN TYPE PARAMETER — `sort Box[T] { provides
/// Desc[T = Box[T = T]] }`. The binding names a parameterized view of the provider, not a
/// bare sort, and WI-859 folds that shape into the SELF-PROVIDER kind.
///
/// IT IS WHY THE CHECK ASKS "BOUND AT ALL" rather than reusing
/// `provision_binding_at_param`, whose sort-like base filter answers `None` here. Backing
/// that choice out refuses the stdlib — `List provides Ord[T = List[T = E]]` and its
/// neighbours are all this shape.
#[test]
fn a_carrier_bound_through_the_providers_own_parameter_loads() {
    let src = r#"namespace test.kxnex.ownparam
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Box
    import anthill.prelude.Int64
    sort E = ?
    entity box(v: E)
    operation describe(x: Box[E = E]) -> Int64 = 5
    provides Desc[T = Box[E = E]]
  end
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "a carrier written as a view of the provider's own parameter is still a carrier \
         the author named: {:?}",
        load_errors(src)
    );
}

/// A POSITIONAL carrier binding — `provides Spec[Impl]`, no `C =`. It binds the carrier
/// as surely as the named spelling does, and the rule asks what the clause BINDS, not how
/// it is spelled.
///
/// PAIRED WITH ITS REFUSAL BELOW, because separately neither says anything: a check that
/// ignored positionals entirely would refuse this one, and a check that treated any
/// positional as "the carrier is bound" would accept the other. Together they pin the
/// mapping — positionals fill the DECLARED parameters, in order, skipping those a named
/// binding already took, which is the rule `check_provider_requires` applies to the same
/// shape.
#[test]
fn a_positional_carrier_binding_loads() {
    let src = r#"namespace test.kxnex.pos
  import anthill.prelude.Int64

  sort Spec
    sort C = ?
    sort U = ?
    operation run(self: C, p: Int64) -> Int64
  end

  sort Impl
    import anthill.prelude.Int64
    import test.kxnex.pos.Spec
    entity impl
    operation run(self: Impl, p: Int64) -> Int64 = p + 1
    provides Spec[Impl]
  end
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "`C` is declared first, so the positional binds it: {:?}",
        load_errors(src)
    );
}

/// THE SAME CLAUSE, REFUSED, and ONE character of the SPEC moved. `U` is now declared
/// first, so `provides Spec[Impl]` binds `U` and leaves `C` empty — a carrier the author
/// believes they named and did not.
///
/// The provider is untouched between this and the test above; only the spec's parameter
/// ORDER differs. That is what makes the pair a measurement of the mapping rather than of
/// the clause.
#[test]
fn a_positional_binding_landing_on_a_non_carrier_parameter_is_refused() {
    let src = r#"namespace test.kxnex.posbad
  import anthill.prelude.Int64

  sort Spec
    sort U = ?
    sort C = ?
    operation run(self: C, p: Int64) -> Int64
  end

  sort Impl
    import anthill.prelude.Int64
    import test.kxnex.posbad.Spec
    entity impl
    operation run(self: Impl, p: Int64) -> Int64 = p + 1
    provides Spec[Impl]
  end
end
"#;
    expect_carrier_refusal(
        &load_errors(src),
        "test.kxnex.posbad.Spec",
        "C",
        "test.kxnex.posbad.Impl",
        "a positional that lands on the spec's first parameter, which is not its carrier",
    );
}

// ── 4. The ticket's own measurement, over the shipped example ────────────────────────

/// THE MEASUREMENT, RE-RUN. Strip the four `C = …` bindings from a scratch copy of
/// `examples/guardians/lib` and the example is refused AT LOAD — where before this ticket
/// it loaded clean and faulted at run time.
///
/// It reads the SHIPPED files rather than a transcription, so it cannot drift from them:
/// if a fifth carrier is added with the binding omitted, the clean-load half of this test
/// is what says so. The `assert!(… > 0)` on the substitution count is the guard that makes
/// the refusal half honest — a renamed binding would otherwise silently leave the sources
/// untouched and assert a refusal of a program nobody had broken.
#[test]
fn reverting_the_guardians_carrier_bindings_is_refused_at_load() {
    let lib = crate::common::examples_dir().join("guardians").join("lib");
    let mut sources: Vec<String> = crate::common::collect_anthill_files(&lib)
        .into_iter()
        .map(|p| std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}")))
        .collect();
    assert!(!sources.is_empty(), "no sources under {lib:?}");
    let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
    assert!(
        crate::common::try_load_kb_with_files(&refs).is_ok(),
        "the SHIPPED guardians lib must load — this half is the control, and it is what \
         catches a fifth carrier written without its `C =` binding"
    );

    // The four bindings the measurement added, reverted to what shipped before it.
    let reverts = [
        ("provides Llm[C = LiveLlm, E = {External}]", "provides Llm[E = {External}]"),
        ("provides Llm[C = FakeLlm, E = {}]", "provides Llm[E = {}]"),
        ("provides Harness[C = FileHarness]", "provides Harness"),
        ("provides Checker[C = LoadChecker]", "provides Checker"),
    ];
    let mut hits = 0usize;
    for src in &mut sources {
        for (bound, bare) in &reverts {
            hits += src.matches(bound).count();
            *src = src.replace(bound, bare);
        }
    }
    assert_eq!(
        hits, 4,
        "expected to revert exactly the four measured bindings — if the example's \
         spelling changed, this test's subject moved with it and the revert below would \
         be asserting about a program nobody broke"
    );

    let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
    let errs = match crate::common::try_load_kb_with_files(&refs) {
        Ok(_) => panic!(
            "the reverted guardians lib loaded CLEAN — which is the defect itself: before \
             this ticket these four provisions named no carrier and the failure waited \
             until `summarize`'s `llm.complete(p)` ran"
        ),
        Err(errs) => errs,
    };
    for (spec, provider) in [
        ("guardians.Llm", "guardians.LiveLlm"),
        ("guardians.Llm", "guardians.FakeLlm"),
        ("guardians.Harness", "guardians.FileHarness"),
        ("guardians.Checker", "guardians.LoadChecker"),
    ] {
        assert!(
            errs.iter()
                .any(|e| e.contains("names no carrier") && e.contains(spec) && e.contains(provider)),
            "each reverted provision must be refused by NAME — missing {provider} / {spec} \
             in {errs:#?}"
        );
    }
}
