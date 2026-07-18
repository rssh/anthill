//! WI-752 — ONE dotted-name ladder, consulted by EVERY position.
//!
//! Six resolvers in `kb/load.rs` resolve a dotted name, and before this ticket they
//! used FIVE different ladders. The divergence — not any one of the ladders — is what
//! produced WI-729, WI-749, WI-750 and WI-751 in sequence: each fixed ONE resolver and
//! left the others spelling the same question differently.
//!
//! The headline symptom was position-dependence: in `namespace app`, `util.f()`
//! resolved (term position, by head-qualification) while `util.T` reported `unresolved
//! type name 'util.T'` — the same spelling, the same scope, opposite answers, because
//! `remap_name` carried the ABSOLUTE rung and no head-qualified one.
//!
//! The ladder now lives ONCE, in `resolve_dotted_in_kb`:
//!   1. head-qualification (SCOPE-RELATIVE), then
//!   2. the absolute qualified name, guarded by `head_owns_path`.
//!
//! WHAT THESE TESTS ARE FOR. Every test below writes ONE dotted spelling and checks
//! that every position agrees about it — so a future rung added to one resolver and
//! forgotten in the others fails here rather than shipping as the next WI-75x. The
//! rungs' own semantics (precedence, the partial-miss guard, the `Field` refusal) stay
//! pinned by `wi751_namespace_root_shadow_test`; this file pins their UNIFORMITY.

use std::collections::HashMap;

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use anthill_core::{kb::load, parse};

use crate::common::{interp_for, load_kb_with, try_load_kb_with};

/// The qualified name the QUERY-pattern position (`resolve_name_in_kb_opt`, reached via
/// `anthill query --pattern`) binds a dotted functor to. Mirrors the CLI's own path —
/// `fact <pattern>`, `scan_definitions`, `convert_query_term` at `_global` — so this
/// measures the shipped entry point rather than a private helper.
fn query_pattern_functor_qn(kb: &mut KnowledgeBase, pattern: &str) -> String {
    let src = format!("fact {pattern}");
    let parsed = parse::parse(&src).expect("parse query pattern");
    let _ = load::scan_definitions(kb, &[&parsed]);
    let global_raw = kb.make_name_term("_global").raw();
    let mut var_map = HashMap::new();
    for item in &parsed.items {
        if let anthill_core::parse::ir::Item::Fact(f) = item {
            let t = load::convert_query_term(
                kb,
                &parsed.terms,
                &parsed.symbols,
                f.term,
                global_raw,
                &mut var_map,
            );
            if let Term::Fn { functor, .. } = kb.get_term(t) {
                return kb.qualified_name_of(*functor).to_string();
            }
        }
    }
    panic!("query pattern `{pattern}` produced no Fn term");
}

/// THE HEADLINE. One namespace, one scope, one spelling family — `util.<member>`,
/// reachable ONLY by head-qualification (there is no top-level `util`). Term functor,
/// type reference and rule citation must all resolve it.
///
/// `typeSite` is the test's whole reason for existing: before WI-752 this exact source
/// failed with `unresolved type name 'util.T' in scope 'typeSite'` while `callSite` two
/// lines above resolved `util.f()` without complaint.
#[test]
fn wi752_head_qualified_path_resolves_in_every_position() {
    const SRC: &str = r#"
namespace app.util
  import anthill.prelude.{Int64, Bool}
  sort T
    entity t(v: Int64)
  end
  operation f() -> Int64 = 41
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 7)
  rule rel(?x) :- q(row: ?x)
end

namespace app
  import anthill.prelude.{Int64, Bool}
  -- TERM FUNCTOR position
  operation callSite() -> Int64 effects Error = util.f()
  -- TYPE REFERENCE position
  operation typeSite(x: util.T) -> Int64 = 2
  -- RULE CITATION position (bare `Sort.rule` reference, drained)
  operation citeSite() -> Bool effects Error = util.rel.isEmpty
end
"#;
    try_load_kb_with(SRC).unwrap_or_else(|errs| {
        panic!(
            "`util.f()`, `util.T` and `util.rel` are the SAME dotted spelling in the \
             SAME scope — every position must read the same ladder and resolve it; \
             got:\n{}",
            errs.join("\n")
        )
    });

    let mut interp = interp_for(SRC);
    match interp.call("app.callSite", &[]).expect("`util.f()` must run") {
        Value::Int(n) => assert_eq!(n, 41, "`util.f()` must reach `app.util.f`"),
        other => panic!("expected the helper's Int, got {other:?}"),
    }
    // The rule citation reaches a NON-empty relation — proof the name bound the
    // relation `app.util.rel` (extent {7}) rather than merely loading.
    match interp.call("app.citeSite", &[]).expect("`util.rel.isEmpty` must run") {
        Value::Bool(b) => assert!(
            !b,
            "`util.rel` must bind the relation `app.util.rel`, whose extent is {{7}}"
        ),
        other => panic!("expected a Bool, got {other:?}"),
    }
}

/// The ABSOLUTE rung, in every position. Reaching it needs the head slot taken by a
/// NON-namespace (a namespace head owns its paths — `head_owns_path`), so `sort myroot`
/// is load-bearing: it makes head-qualification miss and hands the name to rung 2.
///
/// GREEN BEFORE WI-752, deliberately kept: WI-751 gave the term functor and the rule
/// citation this rung, and the type reference's bare `by_qualified_name` lookup happened
/// to agree here. It is a UNIFORMITY guard, not a bug detector — it fails if a future
/// change reaches the absolute rung from some positions and not others. What the type
/// position did NOT share was the guard beside that rung, which the next test measures.
#[test]
fn wi752_absolute_path_resolves_in_every_position() {
    const SRC: &str = r#"
namespace myroot.inner
  import anthill.prelude.{Int64, Bool}
  sort T
    entity t(v: Int64)
  end
  operation helper() -> Int64 = 41
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 7)
  rule rel(?x) :- q(row: ?x)
end

namespace test.wi752abs
  import anthill.prelude.{Int64, Bool}
  sort myroot
    entity mr(row: Int64)
  end
  operation callSite() -> Int64 effects Error = myroot.inner.helper()
  operation typeSite(x: myroot.inner.T) -> Int64 = 2
  operation citeSite() -> Bool effects Error = myroot.inner.rel.isEmpty
end
"#;
    try_load_kb_with(SRC).unwrap_or_else(|errs| {
        panic!(
            "with `sort myroot` holding the head slot, every position must fall to the \
             ABSOLUTE rung and resolve `myroot.inner.*`; got:\n{}",
            errs.join("\n")
        )
    });

    let mut interp = interp_for(SRC);
    match interp.call("test.wi752abs.callSite", &[]).expect("the absolute call must run") {
        Value::Int(n) => assert_eq!(n, 41, "must reach `myroot.inner.helper`"),
        other => panic!("expected an Int, got {other:?}"),
    }
}

/// THE GUARD, in the TYPE position. A PARTIAL miss — the head resolving correctly to a
/// nearer namespace, only a later segment absent — must stay LOUD rather than re-rooting
/// the path at a same-spelled top-level twin.
///
/// The term position has refused this since WI-751 (`head_owns_path`). The type position
/// had a bare `by_qualified_name` lookup with no such guard, so it silently teleported:
/// `x.Missing` inside `outer.user` bound the top-level `x.Missing`, a genuinely
/// different sort. The `String` field is the detector — a value of the teleported sort
/// carries it, so the two sorts are distinguishable if anything downstream resolves.
///
/// Asserting "fails" is not enough: the failure must name `x.Missing`, and must be
/// unchanged by whether the global twin exists at all.
#[test]
fn wi752_partial_miss_stays_loud_in_type_position() {
    const WITH_GLOBAL_TWIN: &str = r#"
namespace outer.x
  import anthill.prelude.Int64
  sort Present
    entity p(v: Int64)
  end
end

namespace x
  import anthill.prelude.String
  sort Missing
    entity m(v: String)
  end
end

namespace outer.user
  import anthill.prelude.Int64
  operation useIt(a: x.Missing) -> Int64 = 1
end
"#;
    // byte-identical but for the global twin, which is what makes the pair a control
    const NO_GLOBAL_TWIN: &str = r#"
namespace outer.x
  import anthill.prelude.Int64
  sort Present
    entity p(v: Int64)
  end
end

namespace x
  import anthill.prelude.String
  sort Unrelated
    entity u(v: String)
  end
end

namespace outer.user
  import anthill.prelude.Int64
  operation useIt(a: x.Missing) -> Int64 = 1
end
"#;
    for (src, label) in [(WITH_GLOBAL_TWIN, "with"), (NO_GLOBAL_TWIN, "without")] {
        let errs = try_load_kb_with(src).err().unwrap_or_else(|| {
            panic!(
                "`x.Missing` names no member of the sibling `outer.x` that the head \
                 resolves to — the TYPE position must refuse it {label} a same-spelled \
                 top-level `x.Missing`, exactly as the term position does"
            )
        });
        assert!(
            errs.iter().any(|e| e.contains("x.Missing")),
            "the miss must be reported against the NAME `x.Missing` {label} a global \
             twin; got: {errs:?}"
        );
    }
}

/// The QUERY resolver (`resolve_name_in_kb_opt`) binds the same dotted text to the same
/// symbol the loader does.
///
/// It used to rank the ABSOLUTE reading FIRST and carry no head-qualification rung at
/// all. `anthill query` itself runs at `_global`, where a head resolves to a top-level
/// namespace and the two readings coincide — which is exactly why this divergence
/// survived four fixes unnoticed. But the SAME resolver is called from inside the loader
/// at a NAMESPACE scope: `contract_proof_target_qn` resolves the `<op>` prefix of a
/// contract-proof target `<op>.requires`, and there the missing rung was live.
///
/// So `proof util.f.requires` inside `namespace app` is the discriminating case: the
/// prefix `util.f` needs head-qualification, and without it the target degraded to the
/// unqualified text the author wrote. The emitted `ProofRecord` carries the resolved QN,
/// so the assertion reads the symbol the resolver actually bound.
#[test]
fn wi752_query_resolver_agrees_with_the_loader_on_a_dotted_prefix() {
    const SRC: &str = r#"
namespace app.util
  import anthill.prelude.Int64
  operation f(b: Int64) -> Int64
    requires neq(b, 0)
    = b
end

namespace app
  proof util.f.requires
    by z3(timeout: 1000)
  end
end
"#;
    let mut kb = load_kb_with(SRC);
    let records = proof_record_targets(&mut kb);
    assert!(
        records.iter().any(|r| r.contains("app.util.f.requires")),
        "the contract-proof target `util.f.requires` must resolve its dotted prefix \
         `util.f` by head-qualification — the same rung the term and type positions \
         read — and record the fully-qualified `app.util.f.requires`; the query \
         resolver having no such rung is how the loader and `anthill query` came to \
         bind one dotted text to two different symbols. got: {records:#?}"
    );
}

/// The rendered `ProofRecord` facts in `kb`, for reading back which symbol a proof
/// target resolved to.
fn proof_record_targets(kb: &mut KnowledgeBase) -> Vec<String> {
    let sort_term = kb.make_name_term("anthill.realization.ProofRecord");
    let rules = kb.by_sort(sort_term);
    let heads: Vec<_> = rules.iter().map(|&r| kb.rule_head(r)).collect();
    let printer = anthill_core::persistence::print::TermPrinter::new(kb);
    heads.into_iter().map(|h| printer.print_term(h)).collect()
}

/// FOURTH ITEM — a head-qualified hit hidden by `internal` must FALL THROUGH to the
/// absolute rung, not terminate the descent.
///
/// The old per-rung gate (`accept_qualified_hit`) reported `ForbiddenInternalAccess` and
/// returned, so an unrelated shadowing declaration carrying an `internal` member of the
/// right name broke an otherwise-valid absolute path AND named a symbol the author never
/// wrote. The pair below is byte-identical but for the internal member's NAME, so the
/// only thing that can explain a divergence is the terminating gate.
#[test]
fn wi752_internal_head_hit_falls_through_to_the_absolute_rung() {
    const COLLIDING: &str = r#"
namespace lib
  import anthill.prelude.Int64
  operation util() -> Int64 = 41
end

namespace test.wi752int
  import anthill.prelude.Int64
  sort lib
    internal operation util() -> Int64 = 2
  end
  operation callSite() -> Int64 effects Error = lib.util()
end
"#;
    // identical but for the internal member's name — it no longer collides, so the
    // absolute rung was always reachable here
    const CONTROL: &str = r#"
namespace lib
  import anthill.prelude.Int64
  operation util() -> Int64 = 41
end

namespace test.wi752int
  import anthill.prelude.Int64
  sort lib
    internal operation utilX() -> Int64 = 2
  end
  operation callSite() -> Int64 effects Error = lib.util()
end
"#;
    for (src, label) in [(COLLIDING, "colliding"), (CONTROL, "renamed (the control)")] {
        try_load_kb_with(src).unwrap_or_else(|errs| {
            panic!(
                "with an {label} `internal` member, `lib.util()` must still reach the \
                 absolute `lib.util` — a rung's hit being unusable is a reason to try \
                 the NEXT rung, not to stop; got:\n{}",
                errs.join("\n")
            )
        });
        let mut interp = interp_for(src);
        match interp.call("test.wi752int.callSite", &[]).expect("`lib.util()` must run") {
            Value::Int(n) => assert_eq!(
                n, 41,
                "with an {label} `internal` member, `lib.util()` must answer the \
                 absolute `lib.util` (41)"
            ),
            other => panic!("expected an Int, got {other:?}"),
        }
    }
}

/// The fall-through must not become a LOOPHOLE. When `internal` hides the only reading
/// there is, the precise `ForbiddenInternalAccess` still stands — skipping a hidden hit
/// means "keep descending", never "pretend it resolved".
///
/// GREEN BEFORE WI-752: this guards the NEW code, not the old defect. Making a hidden
/// hit non-terminal is exactly the change that could have turned this diagnostic into a
/// generic unknown-name error, so it is asserted alongside the fall-through it bounds.
#[test]
fn wi752_internal_with_no_other_reading_still_reports() {
    const SRC: &str = r#"
namespace lib.secret
  import anthill.prelude.Int64
  internal operation hidden() -> Int64 = 1
end

namespace test.wi752intloud
  import anthill.prelude.Int64
  sort lib
    entity l(v: Int64)
  end
  operation bad() -> Int64 effects Error = lib.secret.hidden()
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("an `internal` operation with no other reading must NOT load");
    assert!(
        errs.iter().any(|e| e.contains("hidden") && e.contains("internal")),
        "the forbidden-internal diagnostic must survive the fall-through — it is the \
         precise finding, and losing it to a generic unknown-name error is the \
         regression this guards; got: {errs:?}"
    );
}

/// THE RE-ROUTE GATE (`qualified_name_resolves`) reads the ladder under `Any` — the ONE
/// deliberate deviation in the family, because its question is "does this path have an
/// ANSWER", not "which symbol does it denote".
///
/// It used to gate its head-qualified rung on visibility while leaving the absolute rung
/// beside it blind, so a hit hidden by `internal` counted as resolving or not depending
/// purely on which rung found it. When it counts as NOT resolving, the dot-call re-route
/// peels the name into a member chain and the precise diagnostic is buried under an
/// INVENTED member miss. The assertion is therefore about WHICH error survives.
///
/// `rule lib:` is load-bearing, and finding that out is why this fixture looks the way
/// it does. A first cut used a plain `namespace lib` and asserted only that the internal
/// diagnostic appeared — it passed under BOTH settings, because with nothing named `lib`
/// in the citing scope the decomposition rungs (`dot_receiver_binder`,
/// `rule_prefix_split`) fail anyway and the gate's answer changes nothing. The labelled
/// rule gives rung 3 something to find, so the gate's verdict is the ONLY thing deciding
/// between the two outcomes. Measured both ways: under `VisibleOnly` the head-qualified
/// hit is filtered, `head_owns_path` stands the absolute rung down, the gate declines,
/// and the error becomes `anthill.prelude.Relation.hidden … no such member (dot
/// dispatch)` — a member miss on a relation the author never mentioned.
#[test]
fn wi752_reroute_gate_keeps_the_precise_internal_diagnostic() {
    const SRC: &str = r#"
namespace lib
  import anthill.prelude.Int64
  internal operation hidden() -> Int64 = 1
end

namespace test.wi752gate
  import anthill.prelude.Int64
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)
  rule lib: rel(?x) :- q(row: ?x)
  operation bad() -> Int64 effects Error = lib.hidden()
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`lib.hidden` is internal to `lib` — the call must NOT load");
    assert!(
        errs.iter().any(|e| e.contains("hidden") && e.contains("internal")),
        "the qualified path has an ANSWER — a forbidden `internal` one — so the gate \
         must keep the name whole and report it; got: {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("no such member")),
        "the gate declined on the strength of the `internal` hit, so `lib.hidden()` was \
         peeled into a member access on the relation `lib` — burying a precise finding \
         under a member miss the author never wrote; got: {errs:?}"
    );
}
