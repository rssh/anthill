//! WI-1075 — ABSOLUTE PATHS GET A SPELLING (`..a.b.c`), AND A BARE DOTTED PATH BECOMES
//! PURELY RELATIVE. One spelling per meaning.
//!
//! THE DEFECT. A qualified path whose HEAD is SHADOWED used to re-root at the bare
//! GLOBAL twin instead of resolving relatively — silently. The dotted ladder's second
//! rung ("the name IS some symbol's own fully-qualified name") had two jobs that are
//! INDISTINGUISHABLE AT THE POINT OF DECISION — head resolves locally, rung 1 misses,
//! rung 2 hits:
//!
//! | | |
//! |---|---|
//! | capability | `outer.inner.g` with `outer` shadowed — rung 2 supplies the RIGHT answer |
//! | defect     | `inner.g` with `inner` shadowed — rung 2 supplies a FOREIGN answer |
//!
//! The only difference is whether the author meant the path absolutely, which is not in
//! the text — a relative path can COINCIDE with some other symbol's fully-qualified
//! name. So every rule keyed on the old syntax picks one side and loses the other.
//! Measured before this ticket: standing rung 2 down whenever the head resolved failed
//! 8 tests, 4 of them WI-751's capability.
//!
//! THE DESIGN. `a.b.c` binds its head where the reference is written and resolves the
//! rest under that binding; a miss under that head is LOUD. `..a.b.c` goes straight to
//! `by_qualified_name`, the channel `import` already uses, so nothing can shadow it. The
//! marker REPLACES the implicit absolute reading rather than joining it — two spellings
//! for one meaning, differing only in a rare corner, is the defect proposal 059 R4
//! refuses for `fact Spec[X]` vs `provides Spec[X]`, and the safe spelling would be the
//! one nobody writes because the unmarked one appears to work.
//!
//! WHAT THESE TESTS DRIVE — and what fails when the change is backed out (restore the
//! unconditional `dotted_absolute` rung under `dotted_by_head`):
//!
//!  * [`wi1075_shadowed_head_that_misses_is_loud`] — row 3 fails: the call loads clean
//!    and answers the FOREIGN `g`. Rows 1 and 2 pass either way, BY DESIGN: they are the
//!    two rows WI-1075 leaves alone, and they are here to bound the change to one row.
//!  * [`wi1075_absolute_spelling_reaches_the_root_under_a_shadowed_head`] — passes
//!    either way for the `..` half (the old rung answered the same symbol); the LOUD
//!    half is what fails, and it is the whole point of the pair.
//!  * [`wi1075_unshadowed_relative_path_still_reaches_the_root`] — passes either way by
//!    design. It is the ZERO-MIGRATION claim: with nothing shadowing the head, the scope
//!    walk reaches `<global>` where a top-level namespace is an ordinary local, so an
//!    unmarked FQN still resolves by head-qualification alone.
//!  * [`wi1075_member_miss_under_a_namespace_root_stays_loud`] — passes either way
//!    (WI-751's `head_owns_path` already refused it). The control that says the new rule
//!    did not merely re-derive an old one.
//!  * [`wi1075_visibility_fall_through_is_not_a_miss`] — fails when the fall-through is
//!    conflated with a miss, which is the naive one-line version of this change.
//!  * [`wi1075_rung_two_census_stays_zero`] — fails if any corpus program depends on the
//!    implicit absolute reading.

use anthill_core::eval::Value;
use anthill_core::kb::load;

use crate::common::{interp_for, try_load_kb_with};

/// The three defect rows drive ONE unedited body — `inner.g(v)` written inside
/// `outer.inner.Box` — and differ only in what is declared AROUND it.
const BASE: &str = r#"
namespace outer
  import anthill.prelude.Int64
  namespace inner
    import anthill.prelude.Int64
    operation g(x: Int64) -> Int64 = 100
    sort Box
      entity box(v: Int64)
      operation use(v: Int64) -> Int64 effects Error = inner.g(v)
    end
  end
end
"#;

/// Row 2 = [`BASE`] plus a member `Box.inner`, spelled like the enclosing namespace, so
/// the head `inner` binds to IT and the path misses UNDER it. Nothing else changes.
const SHADOWED: &str = r#"
namespace outer
  import anthill.prelude.Int64
  namespace inner
    import anthill.prelude.Int64
    operation g(x: Int64) -> Int64 = 100
    sort Box
      entity box(v: Int64)
      operation inner(n: Int64) -> Int64 = 0
      operation use(v: Int64) -> Int64 effects Error = inner.g(v)
    end
  end
end
"#;

/// Row 3 = row 2 plus a TOP-LEVEL `inner.g` for the old rung 2 to re-root at. Returning a
/// DIFFERENT type is the control that proves WHICH `g` a reading bound — before WI-1075
/// this fixture failed with `expected Int64, got Bool`, i.e. the top-level one won.
const TOP_LEVEL_TWIN: &str = r#"
namespace inner
  import anthill.prelude.{Int64, Bool}
  operation g(x: Int64) -> Bool = true
end
"#;

/// ROW 3 IS THE WHOLE CHANGE. All three rows, driven for the VALUE each answers rather
/// than for loading — the failure being fixed is precisely a name resolving to the WRONG
/// thing, which loading cannot see.
///
/// | fixture | before WI-1075 | now |
/// |---|---|---|
/// | base | `outer.inner.g` → 100 | unchanged |
/// | + `Box.inner` | LOUD `unknown functor` | unchanged |
/// | + `Box.inner` AND a top-level `namespace inner` | loads clean, calls the TOP-LEVEL `g` | LOUD |
///
/// Row 3's top-level `g` returns `Bool` where the intended one returns `Int64`, so the
/// two readings are distinguishable at load: binding the foreign `g` reports a TYPE
/// error, binding nothing reports the NAME. Asserting only "row 3 fails" would pass on
/// the old code, which also failed — with the wrong finding.
#[test]
fn wi1075_shadowed_head_that_misses_is_loud() {
    // ROW 1 — nothing shadows the head. The relative reading resolves it, as before.
    let mut interp = interp_for(BASE);
    match interp
        .call("outer.inner.Box.use", &[Value::Int(7)])
        .expect("`inner.g(v)` must run with nothing shadowing `inner`")
    {
        Value::Int(n) => assert_eq!(n, 100, "row 1 must reach `outer.inner.g`"),
        other => panic!("expected the local `g`'s Int, got {other:?}"),
    }

    // ROW 2 — the head is shadowed and the path misses under it, with no global twin.
    // Loud before this ticket and loud now: the row that says the change is bounded.
    let errs = try_load_kb_with(SHADOWED)
        .err()
        .expect("row 2: `inner.g` names no member of the `Box.inner` its head binds");
    assert!(
        errs.iter()
            .any(|e| e.contains("inner.g") && e.contains("unknown functor")),
        "row 2 must report the NAME `inner.g`; got: {errs:?}"
    );

    // ROW 3 — the same file plus a top-level `namespace inner`. THE DEFECT.
    let row3 = format!("{TOP_LEVEL_TWIN}{SHADOWED}");
    let errs = try_load_kb_with(&row3).err().unwrap_or_else(|| {
        panic!(
            "row 3: with `Box.inner` shadowing the head, `inner.g` must NOT be re-read \
             as the top-level `inner.g` — that reading is now spelled `..inner.g`"
        )
    });
    let joined = errs.join("\n");
    assert!(
        joined.contains("inner.g") && joined.contains("unknown functor"),
        "row 3 must report the same NAME miss row 2 does — the presence of an unrelated \
         top-level `inner` may not change what `inner.g` means; got:\n{joined}"
    );
    assert!(
        !joined.contains("got Bool"),
        "row 3 bound the TOP-LEVEL `inner.g` (the `Bool`-returning twin): the path \
         silently re-rooted at a namespace the author never named; got:\n{joined}"
    );
}

/// THE CAPABILITY, and its now-loud twin. Same fixture, same shadowed head, two
/// spellings — and they must ANSWER DIFFERENTLY, which is the property the single old
/// spelling could not have.
///
/// `..inner.g` reaches the top-level `inner.g` (returning `x + 900`, so the value names
/// the binding); the unmarked `inner.g` beside it is the loud miss. Driving only the
/// `..` half would pass on the old code too, where the unmarked spelling reached the
/// same symbol — the pair is what makes this a test of the SEPARATION.
#[test]
fn wi1075_absolute_spelling_reaches_the_root_under_a_shadowed_head() {
    const TOP_LEVEL: &str = r#"
namespace inner
  import anthill.prelude.Int64
  operation g(x: Int64) -> Int64 = 900
end
"#;
    const MARKED: &str = r#"
namespace outer
  import anthill.prelude.Int64
  namespace inner
    import anthill.prelude.Int64
    operation g(x: Int64) -> Int64 = 100
    sort Box
      entity box(v: Int64)
      operation inner(n: Int64) -> Int64 = 0
      operation use(v: Int64) -> Int64 effects Error = ..inner.g(v)
    end
  end
end
"#;
    let src = format!("{TOP_LEVEL}{MARKED}");
    try_load_kb_with(&src).unwrap_or_else(|errs| {
        panic!(
            "`..inner.g` is the ABSOLUTE spelling — it must reach the top-level \
             `inner.g` with `Box.inner` shadowing the head; got:\n{}",
            errs.join("\n")
        )
    });
    let mut interp = interp_for(&src);
    match interp
        .call("outer.inner.Box.use", &[Value::Int(7)])
        .expect("`..inner.g(v)` must run")
    {
        Value::Int(n) => assert_eq!(
            n, 900,
            "`..inner.g` must bind the TOP-LEVEL `inner.g` (900), not the enclosing \
             `outer.inner.g` (100) — an absolute path names the root"
        ),
        other => panic!("expected an Int, got {other:?}"),
    }

    // The unmarked twin, byte-identical but for the two marker characters.
    let unmarked = src.replace("..inner.g(v)", "inner.g(v)");
    let errs = try_load_kb_with(&unmarked).err().unwrap_or_else(|| {
        panic!(
            "the UNMARKED `inner.g` must be loud under the same shadowed head — if both \
             spellings resolve, the marker is decoration and the defect is still writable"
        )
    });
    assert!(
        errs.iter().any(|e| e.contains("inner.g")),
        "the unmarked twin must report the NAME `inner.g`; got: {errs:?}"
    );

    // The OUTERMOST segment shadowed too — WI-751's capability, in its new spelling.
    // `..outer.inner.g` must reach `outer.inner.g` with a member `Box.outer` in the way.
    let both_shadowed = MARKED
        .replace(
            "      operation inner(n: Int64) -> Int64 = 0\n",
            "      operation inner(n: Int64) -> Int64 = 0\n      operation outer(n: Int64) -> Int64 = 0\n",
        )
        .replace("..inner.g(v)", "..outer.inner.g(v)");
    let src = format!("{TOP_LEVEL}{both_shadowed}");
    try_load_kb_with(&src).unwrap_or_else(|errs| {
        panic!(
            "`..outer.inner.g` must resolve with BOTH `outer` and `inner` shadowed by \
             members of the enclosing sort — an absolute path needs no import and is \
             immune to shadowing of even its outermost segment; got:\n{}",
            errs.join("\n")
        )
    });
    let mut interp = interp_for(&src);
    match interp
        .call("outer.inner.Box.use", &[Value::Int(7)])
        .expect("`..outer.inner.g(v)` must run")
    {
        Value::Int(n) => assert_eq!(n, 100, "`..outer.inner.g` must bind `outer.inner.g`"),
        other => panic!("expected an Int, got {other:?}"),
    }
}

/// ZERO MIGRATION, driven rather than asserted. With NOTHING shadowing the head, an
/// unmarked fully-qualified path resolves exactly as before — and it does so through the
/// RELATIVE reading, because the scope walk goes out to `<global>`, where a top-level
/// namespace is an ordinary local.
///
/// That is why retiring the implicit absolute reading cost no rewrites: `..` is needed
/// ONLY where something shadows the head. The census instrument is the evidence that
/// rung 1 carried it — a delta of zero over this load means no path here was re-read
/// absolutely.
///
/// PASSES EITHER WAY BY DESIGN. Backing the change out cannot break it; it is here to
/// bound the change, and its companion is [`wi1075_rung_two_census_stays_zero`].
#[test]
fn wi1075_unshadowed_relative_path_still_reaches_the_root() {
    const SRC: &str = r#"
namespace outer.inner
  import anthill.prelude.Int64
  operation g(x: Int64) -> Int64 = 100
end

namespace elsewhere
  import anthill.prelude.Int64
  operation use(n: Int64) -> Int64 effects Error = outer.inner.g(n)
end
"#;
    load::reset_absolute_fallthrough_hits();
    let mut interp = interp_for(SRC);
    match interp
        .call("elsewhere.use", &[Value::Int(7)])
        .expect("an unmarked FQN with nothing shadowing its head must run")
    {
        Value::Int(n) => assert_eq!(n, 100, "`outer.inner.g` must reach `outer.inner.g`"),
        other => panic!("expected an Int, got {other:?}"),
    }
    assert_eq!(
        load::absolute_fallthrough_hits(),
        0,
        "the unshadowed FQN must resolve by HEAD-QUALIFICATION — the head `outer` binds \
         the top-level namespace at `<global>`. A non-zero count here would mean it \
         resolved by the absolute route instead, and the zero-migration claim would rest \
         on a route this ticket removes"
    );
}

/// THE CONTROL for the guard that survived: a genuine member miss under a NAMESPACE root
/// stays loud, and did before this ticket too (WI-751's `head_owns_path`, renamed
/// `hidden_hit_ends_the_path` now that a miss no longer routes through it).
///
/// The head `x` resolves CORRECTLY to the sibling `outer.x`; only `bar` is absent. The
/// `String` return on the top-level `x.bar` is the detector: a re-rooted path fails on
/// the RETURN TYPE instead of on the name.
///
/// PASSES EITHER WAY BY DESIGN — it says the new rule did not merely re-derive an old
/// one, and that widening "loud" to every head did not cost the namespace head its
/// message.
#[test]
fn wi1075_member_miss_under_a_namespace_root_stays_loud() {
    const SRC: &str = r#"
namespace outer.x
  import anthill.prelude.Int64
  operation foo() -> Int64 = 41
end

namespace x
  import anthill.prelude.String
  operation bar() -> String = "teleported"
end

namespace outer.user
  import anthill.prelude.Int64
  operation useIt() -> Int64 effects Error = x.bar()
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`x.bar()` names no member of the sibling `outer.x` the head resolves to");
    let joined = errs.join("\n");
    assert!(
        joined.contains("x.bar") && joined.contains("unknown functor"),
        "the miss must be reported against the NAME `x.bar`; a return-type error means \
         the path re-rooted at the top-level `x`; got:\n{joined}"
    );
}

/// A HIT REJECTED FOR VISIBILITY IS NOT A MISS (WI-752, kept alive by WI-1075).
///
/// A head-qualified hit hidden by `internal` has not BOUND the path — the citing scope
/// may not see it — so the descent continues to the absolute reading, which is the one
/// implicit-absolute route WI-1075 deliberately leaves standing. Conflating it with a
/// miss is the naive one-line version of this change, and it breaks four wi752 tests.
///
/// FAILS WHEN CONFLATED. The value assertion is the point: the local `sort lib` carries
/// an `internal util` returning 2, the top-level `lib.util` returns 41, so the answer
/// names which one bound. The census self-check is the other half — this shape MUST move
/// the instrument that [`wi1075_rung_two_census_stays_zero`] reads as zero, or that zero
/// is an instrument nobody can move.
#[test]
fn wi1075_visibility_fall_through_is_not_a_miss() {
    const SRC: &str = r#"
namespace lib
  import anthill.prelude.Int64
  operation util() -> Int64 = 41
end

namespace test.wi1075vis
  import anthill.prelude.Int64
  sort lib
    internal operation util() -> Int64 = 2
  end
  operation callSite() -> Int64 effects Error = lib.util()
end
"#;
    load::reset_absolute_fallthrough_hits();
    let mut interp = interp_for(SRC);
    assert!(
        load::absolute_fallthrough_hits() > 0,
        "INSTRUMENT SELF-CHECK: this fixture is the visibility fall-through, so it must \
         MOVE the census counter. A counter nothing moves reports zero over the corpus \
         for free"
    );
    match interp
        .call("test.wi1075vis.callSite", &[])
        .expect("`lib.util()` must still reach the absolute `lib.util`")
    {
        Value::Int(n) => assert_eq!(
            n, 41,
            "the hidden `internal` hit must not bind the path — a rung's hit being \
             UNUSABLE is a reason to try the next reading, not to stop"
        ),
        other => panic!("expected an Int, got {other:?}"),
    }
}

/// AN ABSOLUTE PATH IS A REFERENCE — it names the symbol whose qualified name it spells,
/// and cannot INTRODUCE one.
///
/// A declaration cannot spell `..` at all: the grammar admits `absolute_name` only in
/// reference positions, so `namespace ..a.b` is a parse error. A clause HEAD is a term,
/// which makes it the one place the shape is writable outside a reference.
///
/// NEITHER SHAPE MINTS, and that is why the refusal is needed rather than optional: the
/// marker is built from the separator, so every marked name contains a `.`, and
/// `rule_introduced_functor_name` already refuses any such name ("a qualified name
/// references an existing symbol; it never introduces one"). With no mint the head falls
/// to the WI-476 bare intern and the clause is stored under a symbol nothing can cite —
/// dead and silent. `refuse_unresolvable_absolute_head` is what makes it loud, at the
/// LOAD of a rule and of a fact alike.
///
/// FAILS WHEN THE REFUSAL IS BACKED OUT: both fixtures load clean, each carrying a
/// clause nothing can reach. The CONTROL is the same head unmarked, which introduces its
/// relation as always — so the refusal is keyed on the marker, not on the head being new.
#[test]
fn wi1075_an_absolute_path_may_not_introduce_a_rule_head() {
    const MARKED: &str = r#"
namespace test.wi1075head
  import anthill.prelude.Int64
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)
  rule ..nosuchtop(?x) :- q(row: ?x)
end
"#;
    let errs = try_load_kb_with(MARKED).err().unwrap_or_else(|| {
        panic!(
            "a rule head spelled `..nosuchtop` names a ROOT symbol that does not exist; \
             minting it would define a scope-local named `..nosuchtop` that no reference \
             can ever reach"
        )
    });
    assert!(
        errs.iter().any(|e| e.contains("..nosuchtop")),
        "the refusal must name the path the author wrote; got: {errs:?}"
    );

    // CONTROL: the same head unmarked introduces the relation, as it always has.
    let unmarked = MARKED.replace("..nosuchtop", "nosuchtop");
    try_load_kb_with(&unmarked).unwrap_or_else(|errs| {
        panic!(
            "an UNMARKED new head still introduces its name — the refusal above is keyed \
             on the marker, not on the head being new; got:\n{}",
            errs.join("\n")
        )
    });

    // A `fact` HEAD is a term too, and the mint guard does not run there — so the
    // reference position is what has to refuse it. MEASURED before this was added:
    // `fact ..zzq(row: 1)` loaded clean and asserted a fact under a bare symbol named
    // literally `..zzq`, reachable by nothing and attached to no declaration.
    const FACT: &str = r#"
namespace test.wi1075fact
  import anthill.prelude.Int64
  fact ..nosuchtop(row: 1)
end
"#;
    let errs = try_load_kb_with(FACT).err().unwrap_or_else(|| {
        panic!(
            "`fact ..nosuchtop(row: 1)` names a ROOT symbol that does not exist — a \
             marked path that resolves to nothing is an error, never a bare intern"
        )
    });
    assert!(
        errs.iter().any(|e| e.contains("..nosuchtop")),
        "the fact-head refusal must name the path; got: {errs:?}"
    );
}

/// A PATH DOES NOT NAME A FIELD — in EITHER reading.
///
/// Entity fields are registered under the constructor's qualified name
/// (`<ns>.Sort.entity.field`), so BOTH a head-qualified join and a bare
/// `by_qualified_name` lookup can land on one. A field is reached by dot DISPATCH on a
/// value, never by a path, so the hit is a category error — and the refusal therefore
/// belongs to the LADDER, not to one reading.
///
/// FAILS WHEN THE FILTER SITS ONLY ON THE RELATIVE READING (where WI-751 left it):
/// `..data.Holder.user.name` then resolves to the FIELD while the unmarked twin
/// correctly refuses — the two spellings of one question disagreeing, which is the exact
/// shape this ticket exists to remove. Driven from both sides so neither can drift.
#[test]
fn wi1075_neither_reading_binds_a_field_by_path() {
    const SRC: &str = r#"
namespace data
  import anthill.prelude.Int64
  sort Holder
    entity user(name: Int64)
  end
end

namespace test.wi1075field
  import anthill.prelude.Int64
  operation bad() -> Int64 effects Error = MARKdata.Holder.user.name()
end
"#;
    for (marker, label) in [("", "relative"), ("..", "absolute")] {
        let src = SRC.replace("MARK", marker);
        let errs = try_load_kb_with(&src).err().unwrap_or_else(|| {
            panic!(
                "the {label} spelling bound the entity FIELD `data.Holder.user.name` — a \
                 field is reached by dot dispatch on a value, never by a path"
            )
        });
        assert!(
            errs.iter().any(|e| e.contains("data.Holder.user.name")),
            "the {label} refusal must name the whole path the author wrote — losing the \
             path text is how the marked form's diagnostic degraded to `name.apply`; \
             got: {errs:?}"
        );
    }
}

/// EVERY REFERENCE POSITION CAN SPELL THE MARKER. The ladder is shared (WI-752), but the
/// SPELLING has to be admitted per grammar position — so retiring the implicit absolute
/// rung without giving a position the marker silently removes a reading rather than
/// renaming it.
///
/// FAILS WHEN A POSITION IS MISSED: measured, `describe`, the `proof` target and
/// `Ref(…)` took bare `$.name` after the first cut of this ticket, so a citation under a
/// shadowed head stopped loading with NO spelling that worked — `describe
/// myroot.inner.helper` refused, `describe ..myroot.inner.helper` a syntax error. The
/// corpus census cannot see this: no corpus file has a shadowed head.
#[test]
fn wi1075_every_reference_position_admits_the_marker() {
    const HELPERS: &str = r#"
namespace myroot.inner
  import anthill.prelude.Int64
  operation helper() -> Int64 = 41
end
"#;
    // `sort myroot` takes the head slot, so ONLY the marked spelling can reach the
    // namespace — each position below is a genuine test of the marker, not of the
    // relative reading that would carry it anyway.
    const SHADOW: &str = "  sort myroot\n    entity mr(row: Int64)\n  end\n";
    for (position, text) in [
        ("describe", "  describe ..myroot.inner.helper {< the helper >}\n"),
        (
            "Ref(…)",
            "  operation r() -> Int64 effects Error = Ref(..myroot.inner.helper)\n",
        ),
        (
            "term functor",
            "  operation t() -> Int64 effects Error = ..myroot.inner.helper()\n",
        ),
    ] {
        let src = format!(
            "{HELPERS}\nnamespace test.wi1075pos\n  import anthill.prelude.Int64\n{SHADOW}{text}end\n"
        );
        try_load_kb_with(&src).unwrap_or_else(|errs| {
            panic!(
                "the {position} position must admit `..myroot.inner.helper` — a position \
                 that cannot spell the marker lost its absolute reading outright; \
                 got:\n{}",
                errs.join("\n")
            )
        });
    }
}

/// THE MARKER AND ITS HEAD SEGMENT ARE ONE TOKEN, so `.. a.b` with a space is not a path.
///
/// Pinned in Rust, not only in the tree-sitter corpus, because the decision is
/// load-bearing beyond parsing: gluing is what puts the marker in the head SEGMENT's
/// text, which is how a marked path reaches `resolve_dotted_in_kb` as one string. A
/// future split into `'::'` + `name` would keep every resolution test passing (the
/// converter could re-prefix) and would silently make `.. a.b` legal — two spellings for
/// one path, which is the shape this whole ticket is about.
#[test]
fn wi1075_the_marker_is_glued_to_its_head_segment() {
    const SPACED: &str = r#"
namespace test.wi1075spaced
  import anthill.prelude.Int64
  operation bad() -> Int64 effects Error = .. inner.g(1)
end
"#;
    let errs = crate::common::parse_errs(SPACED);
    assert!(
        !errs.is_empty(),
        "`.. inner.g` must not parse — the marker is part of its head segment's token"
    );
    // The control: the same line without the space parses.
    crate::common::parses_clean(&SPACED.replace(".. inner.g", "..inner.g"));
}

/// THE CENSUS, RE-RUN. No program in the corpus depends on an unmarked path being read
/// absolutely — measured over stdlib + `anthill-stl` (loaded by every fixture here), the
/// examples, `anthill-testcases` and this project's own `anthill-todo` work items.
///
/// This is the migration evidence, kept executable, and it is TWO claims: every project
/// still loads clean, and no path in one took the absolute route. A file that acquires
/// such a dependency fails HERE, naming the corpus, rather than by loading differently
/// somewhere downstream.
///
/// The instrument is self-checked by [`wi1075_visibility_fall_through_is_not_a_miss`],
/// which drives a shape that must move it — so this zero is coverage and not silence.
#[test]
fn wi1075_rung_two_census_stays_zero() {
    let root = crate::common::workspace_root();
    // Each PROJECT is loaded as a unit — its files assume each other, and the stdlib is
    // supplied by `try_load_kb_with_files`. Loading them all into one KB instead would
    // collide on the examples that declare the same namespaces, and loading a file alone
    // would report imports the census does not care about.
    let projects = [
        root.join("examples/github-todo"),
        root.join("examples/sql-store"),
        root.join("examples/webots-modelling"),
        root.join("examples/classic-mini"),
        root.join("anthill-testcases/ring-polynom"),
        root.join("anthill-todo"),
    ];
    // The stdlib + `anthill-stl` themselves: they load under EVERY project below, so a
    // path of theirs would be counted many times over — but the census asks "is the
    // count zero", and a stdlib site would show up under the first project just as well.
    let mut censused = 0usize;
    load::reset_absolute_fallthrough_hits();
    for dir in &projects {
        let files = crate::common::collect_anthill_files(dir);
        assert!(
            !files.is_empty(),
            "the census must actually READ {} — an empty corpus is a zero for the wrong \
             reason",
            dir.display()
        );
        censused += files.len();
        let sources: Vec<String> = files
            .iter()
            .map(|p| {
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
            })
            .collect();
        let refs: Vec<&str> = sources.iter().map(String::as_str).collect();
        // The verdict is READ, never discarded (WI-966): a project that stops loading is
        // the loudest possible form of "a corpus site depended on the implicit absolute
        // reading", and a census run over a KB that never finished loading would report
        // its zero for the wrong reason.
        crate::common::try_load_kb_with_files(&refs).unwrap_or_else(|errs| {
            panic!(
                "{} no longer loads. WI-1075 retired the implicit ABSOLUTE reading of an \
                 unmarked path — if a site here meant the root, spell it `..a.b.c`; \
                 got:\n{}",
                dir.display(),
                errs.join("\n")
            )
        });
    }
    assert_eq!(
        load::absolute_fallthrough_hits(),
        0,
        "a corpus file was resolved through the implicit ABSOLUTE reading of an UNMARKED \
         path. WI-1075 retired that reading; the site must spell the path `..a.b.c` if \
         it means the root, or be repaired if it means a member of the head it shadows"
    );
    // 32 project files at the time of writing, each loaded over the whole stdlib +
    // `anthill-stl`. The floor guards against a corpus that silently empties — the
    // per-directory assertion above already catches one project vanishing.
    assert!(
        censused >= 30,
        "the census read only {censused} project files — too few to be the corpus it \
         claims (it also carries the whole stdlib under each project)"
    );
}
