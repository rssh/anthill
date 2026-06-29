//! WI-345 — loader warnings channel.
//!
//! The loader gained a non-fatal diagnostics channel (`LoadWarning`),
//! surfaced via `LoadResult::warnings`, so lint-style passes can report
//! legal-but-suspicious constructs without failing the load. This file pins
//! the substrate: the type renders as an advisory, and a clean load threads
//! an (empty) `warnings` vec all the way out through `load_all`. WI-346 is
//! the first pass that actually emits into the channel.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError, LoadWarning, LoadResult};
use anthill_core::parse;

fn load_stdlib_result() -> Result<LoadResult, Vec<LoadError>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
}

#[test]
fn load_warning_other_renders_as_advisory() {
    let w = LoadWarning::Other { message: "operation `size` shadows `Iterable.size`".to_string() };
    let s = format!("{w}");
    assert!(s.contains("warning:") && s.contains("size"),
        "a LoadWarning should render as an advisory line naming the issue; got: {s}");
    // `format_with_source` is the span-aware twin of `Display`; the span-less
    // `Other` ignores the source text and renders the bare message.
    assert_eq!(w.format_with_source("any source text"), s);
}

#[test]
fn clean_stdlib_load_carries_only_phase_a_finite_shadows() {
    // End-to-end: the channel is wired through `load_all` → `LoadResult`.
    // The field threads out of the merged result and carries no SPURIOUS
    // advisories. The only warnings are the KNOWN requires-shadows from
    // finiteness (proposal library/003): `FiniteCollection` (which `requires
    // Iterable`) re-homes ops `Iterable` also carries, so WI-346 flags the shadow.
    //   * Phase A (WI-585), TRANSITIONAL: `size` / `foldLeft` / `foldRight` —
    //     Phase C (WI-589) removes these from `Iterable`, so they vanish then.
    //   * Phase B (WI-588), PERMANENT: `map` / `filter` — `Iterable` KEEPS its
    //     lazy (maybe-infinite → `Stream`) `map`/`filter`, while `FiniteCollection`
    //     adds finite (→ `FiniteStream`) ones; both coexist by design (dispatch
    //     picks the finite one on a finite carrier by provision-graph distance),
    //     so this shadow does NOT go away in Phase C. (Teaching WI-346 to not warn
    //     on a covariant-return refinement would silence it — a possible follow-up.)
    // After Phase C the count drops to the 2 permanent map/filter shadows.
    let result = load_stdlib_result().expect("stdlib should load cleanly");
    let msgs: Vec<String> = result.warnings.iter().map(|w| w.to_string()).collect();
    let is_finite_shadow = |m: &String| {
        m.contains("in `anthill.prelude.FiniteCollection`")
            && m.contains("shadows the inherited `anthill.prelude.Iterable.")
    };
    let unexpected: Vec<&String> = msgs.iter().filter(|m| !is_finite_shadow(m)).collect();
    assert!(unexpected.is_empty(),
        "the only stdlib warnings should be the FiniteCollection/Iterable \
         shadows; got unexpected: {unexpected:?}");
    for op in ["size", "foldLeft", "foldRight", "map", "filter"] {
        assert!(msgs.iter().any(|m| is_finite_shadow(m) && m.contains(&format!("`{op}`"))),
            "expected the FiniteCollection shadow warning for `{op}`; got: {msgs:?}");
    }
    assert_eq!(msgs.len(), 5,
        "exactly the five finite shadows (Phase A size/foldLeft/foldRight + \
         Phase B map/filter); got: {msgs:?}");
}
