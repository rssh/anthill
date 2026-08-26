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
//!   1. head-qualification (SCOPE-RELATIVE) — the head's DECLARED member, then the
//!      member it offers by `provides` (WI-20260825-X9RRN), then
//!   2. the absolute qualified name, guarded by `head_owns_path`.
//!
//! WI-1075 gave rung 2 its own SPELLING and retired the implicit reading: `a.b.c` is
//! rung 1 and nothing else (a miss under the head is loud), `..a.b.c` is rung 2 and
//! nothing else. The fixtures below that reached rung 2 therefore write `..` — and the
//! uniformity claim is unchanged and stronger, because the marker must be understood by
//! every position too. The ONE implicit-absolute route left is the visibility
//! fall-through this file pins (`wi752_internal_head_hit_falls_through_to_the_absolute_rung`):
//! a hit REJECTED FOR VISIBILITY has not bound the path, which is a different question
//! from a miss, and `head_owns_path` — now `hidden_hit_ends_the_path` — is what is left
//! deciding it.
//!
//! WHAT THESE TESTS ARE FOR. Every test below writes ONE dotted spelling and checks
//! that every position agrees about it — so a future rung added to one resolver and
//! forgotten in the others fails here rather than shipping as the next WI-75x. The
//! rungs' own semantics (precedence, the partial-miss guard, the `Field` refusal) stay
//! pinned by `wi751_namespace_root_shadow_test`; this file pins their UNIFORMITY.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

use crate::common::{interp_for, load_kb_with, try_load_kb_with};

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
    match interp
        .call("app.callSite", &[])
        .expect("`util.f()` must run")
    {
        Value::Int(n) => assert_eq!(n, 41, "`util.f()` must reach `app.util.f`"),
        other => panic!("expected the helper's Int, got {other:?}"),
    }
    // The rule citation reaches a NON-empty relation — proof the name bound the
    // relation `app.util.rel` (extent {7}) rather than merely loading.
    match interp
        .call("app.citeSite", &[])
        .expect("`util.rel.isEmpty` must run")
    {
        Value::Bool(b) => assert!(
            !b,
            "`util.rel` must bind the relation `app.util.rel`, whose extent is {{7}}"
        ),
        other => panic!("expected a Bool, got {other:?}"),
    }
}

/// THE PROVISION HALF OF RUNG 1, in every position (WI-20260825-X9RRN, completed by
/// WI-20260826-XFTC7). Same claim as the headline one spelling over: `Mid` DECLARES
/// nothing, and `Mid.f` / `Mid.Inner` / `Mid.rel` reach `Base`'s through
/// `provides Base[T = T]`.
///
/// THIS FILE IS WHERE THE ROW BELONGS, and the file's own header says why: it pins the
/// ladder's UNIFORMITY, so that "a future rung added to one resolver and forgotten in the
/// others fails here rather than shipping as the next WI-75x". The rung's SEMANTICS —
/// which edge kinds it follows, what a second hit means, that rung 1 still wins — are
/// `wi_x9rrn_provided_member_address_test`'s and, for the type position,
/// `wi_xftc7_provided_child_in_type_position_test`'s.
///
/// IT EARNED ITS KEEP IMMEDIATELY, which is the argument for writing a uniformity row at
/// all. Added with the type position in it, this row FAILED while the other two passed:
/// `load::try_rigid_type_projection` carries its own qualified-child join —
/// `by_qualified_name.get("{sort_qn}.{member}")`, rung 1 written a second time — and it
/// had rung 1's gap, so `x: Mid.Inner` fell through to a rigid projection and was refused
/// as "type 'Mid' has no member 'Inner'". Nothing else in the suite could see it; the
/// second reader was found by asking this file's question, not by reading the code.
///
/// FAILS IF the provision rung is backed out — in whichever position lost it, which is
/// precisely what a uniformity row is for.
#[test]
fn wi752_provided_member_resolves_in_every_position() {
    const SRC: &str = r#"
namespace app2.base
  import anthill.prelude.{Int64, Bool}
  sort Base
    sort T = ?
    sort Inner
      entity inner(v: Int64)
    end
    operation f() -> Int64 = 41
    -- A FACT-BACKED relation, like the headline row's: an `eq`-only body binds nothing,
    -- so `rel` would drain empty and `isEmpty` could not tell a bound name from an
    -- unbound one.
    sort Q
      entity q(row: Int64)
    end
    fact q(row: 7)
    rule rel(?x) :- q(row: ?x)
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
end

namespace app2
  import anthill.prelude.{Int64, Bool}
  import app2.base.{Mid}
  -- TERM FUNCTOR position
  operation callSite() -> Int64 effects Error = Mid.f()
  -- TYPE REFERENCE position
  operation typeSite(x: Mid.Inner) -> Int64 = 2
  -- RULE CITATION position
  operation citeSite() -> Bool effects Error = Mid.rel.isEmpty
end
"#;
    try_load_kb_with(SRC).unwrap_or_else(|errs| {
        panic!(
            "`Mid.f()`, `Mid.Inner` and `Mid.rel` are the SAME dotted spelling reached \
             through the SAME `provides` edge — every position must resolve it \
             (WI-20260825-X9RRN, WI-20260826-XFTC7); got:\n{}",
            errs.join("\n")
        )
    });

    let mut interp = interp_for(SRC);
    match interp.call("app2.callSite", &[]).expect("`Mid.f()` must run") {
        Value::Int(n) => assert_eq!(
            n, 41,
            "`Mid.f()` must reach `app2.base.Base.f` through the conversion"
        ),
        other => panic!("expected the helper's Int, got {other:?}"),
    }
    // The citation reaches a NON-empty relation — proof the name bound `Base.rel` rather
    // than merely loading.
    match interp
        .call("app2.citeSite", &[])
        .expect("`Mid.rel.isEmpty` must run")
    {
        Value::Bool(b) => assert!(
            !b,
            "`Mid.rel` must bind the relation `app2.base.Base.rel`, whose extent is {{7}}"
        ),
        other => panic!("expected a Bool, got {other:?}"),
    }
}

/// The ABSOLUTE rung, in every position — since WI-1075 spelled `..`, which is what
/// makes this a request rather than a rescue. `sort myroot` remains load-bearing in a
/// new way: it is what the marked path has to SURVIVE, and its unmarked twin below is
/// loud under exactly that declaration.
///
/// GREEN BEFORE WI-752, deliberately kept: WI-751 gave the term functor and the rule
/// citation this rung, and the type reference's bare `by_qualified_name` lookup happened
/// to agree here. It is a UNIFORMITY guard, not a bug detector — it fails if a future
/// change reaches the absolute reading from some positions and not others, which is now
/// also the question "does every position understand `..`". What the type position did
/// NOT share was the guard beside that rung, which the next test measures.
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
  operation callSite() -> Int64 effects Error = ..myroot.inner.helper()
  operation typeSite(x: ..myroot.inner.T) -> Int64 = 2
  operation citeSite() -> Bool effects Error = ..myroot.inner.rel.isEmpty
end
"#;
    try_load_kb_with(SRC).unwrap_or_else(|errs| {
        panic!(
            "with `sort myroot` holding the head slot, every position must read `..` as \
             the ABSOLUTE spelling and resolve `myroot.inner.*`; got:\n{}",
            errs.join("\n")
        )
    });

    let mut interp = interp_for(SRC);
    match interp
        .call("test.wi752abs.callSite", &[])
        .expect("the absolute call must run")
    {
        Value::Int(n) => assert_eq!(n, 41, "must reach `myroot.inner.helper`"),
        other => panic!("expected an Int, got {other:?}"),
    }

    // The UNMARKED twin, per position. WI-1075: `sort myroot` takes the head slot, the
    // path misses under it, and there is no implicit re-root — in EVERY position, which
    // is this file's claim applied to the new rule.
    for (marked, position) in [
        ("..myroot.inner.helper()", "term functor"),
        ("..myroot.inner.T", "type reference"),
        ("..myroot.inner.rel.isEmpty", "rule citation"),
    ] {
        let relative = SRC.replace(marked, marked.trim_start_matches(".."));
        let errs = try_load_kb_with(&relative).err().unwrap_or_else(|| {
            panic!(
                "the UNMARKED path in {position} position must be loud under `sort \
                 myroot` — a position that kept the implicit absolute reading is the \
                 divergence this file exists to catch"
            )
        });
        // The RENDERING is position-dependent once the path fails to resolve (the term
        // functor reports an unknown functor, the citation decomposes into unresolved
        // segments), and pinning it here would be pinning the FALLBACK rather than the
        // rule. What is pinned is that each position refuses, and refuses about the
        // path that was written.
        assert!(
            errs.iter().any(|e| e.contains("myroot") || e.contains("inner")),
            "the {position} miss must be about the path's segments; got: {errs:?}"
        );
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

/// The QUERY resolver (`resolve_name_in_kb`) binds the same dotted text to the same
/// symbol the loader does.
///
/// It used to rank the ABSOLUTE reading FIRST and carry no head-qualification rung at
/// all. `anthill query` itself runs at `<global>`, where a head resolves to a top-level
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
    // WI-922: found by HEAD FUNCTOR, which is the RESOLVED symbol —
    // `kb.intern(qn)` mints a different one in a disjoint space.
    let sort_sym = kb
        .try_resolve_symbol("anthill.realization.ProofRecord")
        .expect("resolve anthill.realization.ProofRecord");
    let rules = kb.rules_by_functor(sort_sym);
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
/// wrote.
///
/// THE PAIR CHANGED WITH WI-1075, and the change is what makes it sharp. Both halves are
/// still byte-identical but for the internal member's NAME, and they now ANSWER
/// DIFFERENTLY:
///
/// | fixture | reading |
/// |---|---|
/// | `internal util` — COLLIDES | rung 1 HITS and is hidden → not a binding → the absolute reading answers 41 |
/// | `internal utilX` — the CONTROL | rung 1 does not hit at all → a plain miss → **loud** |
///
/// Before WI-1075 both answered 41, because the absolute rung fired unconditionally and
/// the control could not distinguish "the hit was unusable" from "there was no hit". The
/// fall-through is keyed on a HIDDEN HIT, and that is exactly what the pair now measures
/// — conflating the two (the naive form of WI-1075) fails the COLLIDING half, and
/// dropping the miss's loudness fails the control.
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
    // identical but for the internal member's name — it no longer collides, so rung 1
    // produces no hit at all and the path is an ordinary relative miss
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
    try_load_kb_with(COLLIDING).unwrap_or_else(|errs| {
        panic!(
            "with a COLLIDING `internal` member, `lib.util()` must still reach the \
             absolute `lib.util` — a rung's hit being unusable is a reason to try the \
             NEXT reading, not to stop; got:\n{}",
            errs.join("\n")
        )
    });
    let mut interp = interp_for(COLLIDING);
    match interp
        .call("test.wi752int.callSite", &[])
        .expect("`lib.util()` must run")
    {
        Value::Int(n) => assert_eq!(
            n, 41,
            "the hidden hit did not bind the path, so `lib.util()` answers the absolute \
             `lib.util` (41), not the `internal` member's 2"
        ),
        other => panic!("expected an Int, got {other:?}"),
    }

    let errs = try_load_kb_with(CONTROL).err().unwrap_or_else(|| {
        panic!(
            "THE CONTROL: with the internal member RENAMED there is no hit to be hidden, \
             so `lib.util()` is a plain miss under the `sort lib` its head binds — and \
             WI-1075 makes that loud. A clean load here means the fall-through fires on \
             a MISS too, which is the implicit absolute reading back again"
        )
    });
    assert!(
        errs.iter().any(|e| e.contains("lib.util")),
        "the control's miss must name `lib.util`; got: {errs:?}"
    );
}

/// The fall-through must not become a LOOPHOLE. When `internal` hides the only reading
/// there is, the precise `ForbiddenInternalAccess` still stands — skipping a hidden hit
/// means "keep descending", never "pretend it resolved".
///
/// GREEN BEFORE WI-752: this guards the NEW code, not the old defect. Making a hidden
/// hit non-terminal is exactly the change that could have turned this diagnostic into a
/// generic unknown-name error, so it is asserted alongside the fall-through it bounds.
///
/// WI-1075 spelled the path `..`, which is what keeps the fixture's SUBJECT. Unmarked, it
/// is now a plain relative miss under the `sort lib` its head binds, and the loud finding
/// would be that miss rather than the forbidden access — a correct answer to a different
/// question. Marked, the reading reaches `lib.secret.hidden` and is refused for
/// visibility, which is the loophole this test is about.
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
  operation bad() -> Int64 effects Error = ..lib.secret.hidden()
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("an `internal` operation with no other reading must NOT load");
    assert!(
        errs.iter()
            .any(|e| e.contains("hidden") && e.contains("internal")),
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
///
/// WI-1075 spelled the path `..`, for the same reason as the test above: unmarked, the
/// head binds the labelled rule `lib` and the path misses under it, so the finding would
/// be that miss. The gate's question — "does this path have an ANSWER, hidden or not" —
/// needs a path that HAS one, and `..lib.hidden` is how that is written now.
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
  operation bad() -> Int64 effects Error = ..lib.hidden()
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`lib.hidden` is internal to `lib` — the call must NOT load");
    assert!(
        errs.iter()
            .any(|e| e.contains("hidden") && e.contains("internal")),
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
