//! WI-751 — a scope-local declaration sharing a NAMESPACE ROOT SEGMENT must not
//! disable qualified references under that root.
//!
//! `remap_name_str_inner` resolves a dotted name that no scope defines AS WRITTEN by
//! HEAD-QUALIFICATION: split on the first dot, resolve the head IN SCOPE, append the
//! tail to the head's qualified path. A local declaration spelled like a namespace
//! ROOT captures that head slot, so `myroot.inner.helper` was looked up as
//! `<ns>.myroot.inner.helper`, missed, and fell through to the WI-476 bare intern —
//! leaving the typer to report `unknown functor` against the CALL while the cause was
//! an unrelated declaration the expression never mentions.
//!
//! WHICH declarations take the slot, measured rather than assumed: a LABELLED rule
//! (`rule myroot: r(?x) :- …`), a `sort`, and an `operation` do. A head-predicate rule
//! (`rule myroot(?x) :- …`, the spelling WI-751 was FILED with) does NOT — `scan_rule_goal`
//! only mints the head-functor Goal when the name is not already in scope, so with the
//! namespace visible no Goal is defined and the head keeps resolving to it. The ticket's
//! own repro therefore loaded clean at HEAD; the defect is real but its trigger is the
//! LABEL form, and it was never rule-specific. A `let` binder does not take the slot
//! either: the head rung reads `resolve_in_scope`, which does not see local binders.
//!
//! THE FIX IS TWO RUNGS, NOT ONE.
//!  * `absolute_qualified` — a name that IS some symbol's fully-qualified name resolves
//!    to that symbol, ranked BELOW head-qualification
//!    (`wi751_scope_relative_root_beats_a_top_level_namespace`).
//!  * `head_owns_path` — the guard that keeps it from firing on a PARTIAL miss. An
//!    earlier cut had only the first rung and silently re-rooted `x.bar` at a
//!    same-spelled top-level namespace when the nearer `outer.x` merely lacked `bar`
//!    (`wi751_partial_miss_under_an_owning_root_stays_loud`). "Head-qualification
//!    missed" is NOT "the name resolves to nothing".
//!
//! Plus two reach fixes, both verified to fail before them: the `Field` refusal in
//! `resolve_dotted_by_head` (entity fields register as `<entity_qn>.<field>`, so a local
//! `sort data { entity user(name: …) }` made head-qualification HIT and capture
//! `data.user.name()`), and the same absolute rung in `resolve_qualified_rule_readonly`,
//! without which the BARE rule-reference citation stayed broken while the applied call
//! was fixed.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The namespace every fixture cites by its absolute path.
const HELPERS: &str = r#"
namespace myroot.inner
  operation helper() -> Int64 = 41
end
"#;

/// ACCEPTANCE: each declaration shape that occupies the root's name slot, against a
/// control with no such declaration. All must load AND answer the same value — an
/// inert declaration cannot change what a fully-qualified path means.
///
/// The EVAL comparison is the point: loading only proves the name resolved to
/// something, and the failure being fixed is precisely a name resolving to the wrong
/// thing. The load is done through `try_load_kb_with` FIRST so a regression names the
/// SHAPE that broke; `interp_for` alone panics with a generic "load failed with N
/// errors" from the shared helper and discards which fixture it was.
#[test]
fn wi751_root_shadowing_declaration_keeps_qualified_paths() {
    const LABELLED_RULE: &str = r#"
namespace test.wi751rule
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)
  rule myroot: r(?x) :- q(row: ?x)
  operation useIt() -> Int64 effects Error = myroot.inner.helper()
end
"#;
    const SORT: &str = r#"
namespace test.wi751sort
  sort myroot
    entity mr(row: Int64)
  end
  operation useIt() -> Int64 effects Error = myroot.inner.helper()
end
"#;
    const OPERATION: &str = r#"
namespace test.wi751op
  operation myroot() -> Int64 = 7
  operation useIt() -> Int64 effects Error = myroot.inner.helper()
end
"#;
    const CONTROL: &str = r#"
namespace test.wi751ctl
  operation useIt() -> Int64 effects Error = myroot.inner.helper()
end
"#;
    for (src, ns, shape) in [
        (LABELLED_RULE, "test.wi751rule", "a labelled rule"),
        (SORT, "test.wi751sort", "a sort"),
        (OPERATION, "test.wi751op", "an operation"),
        (CONTROL, "test.wi751ctl", "nothing (the control)"),
    ] {
        let source = format!("{HELPERS}{src}");
        try_load_kb_with(&source).unwrap_or_else(|errs| {
            panic!(
                "with {shape} named after the namespace root `myroot`, the absolute \
                 path `myroot.inner.helper()` must still resolve; got:\n{}",
                errs.join("\n")
            )
        });
        let mut interp = interp_for(&source);
        match interp.call(&format!("{ns}.useIt"), &[]).unwrap_or_else(|e| {
            panic!("with {shape} named after the root, the call must run; got {e:?}")
        }) {
            Value::Int(n) => assert_eq!(
                n, 41,
                "with {shape} named after the root, `myroot.inner.helper()` must reach \
                 `myroot.inner.helper` — the control answers 41 with no such declaration"
            ),
            other => panic!("expected the helper's Int, got {other:?}"),
        }
    }
}

/// PRECEDENCE — the rung's ORDER, and why it sits BELOW head-qualification.
///
/// Both dotted rungs hit here and they DISAGREE: head-qualification resolves the head
/// `x` in scope to the SIBLING namespace `outer.x` (41), while the absolute rung reads
/// the top-level namespace `x` (99). Head-qualification is scope-RELATIVE, so it must
/// win — otherwise the fix installs WI-751's own disease in the opposite direction,
/// letting any top-level namespace capture qualified paths a nearer same-rooted
/// namespace already answers. Inverting the two rungs makes this return 99.
#[test]
fn wi751_scope_relative_root_beats_a_top_level_namespace() {
    const SRC: &str = r#"
namespace outer.x
  operation foo() -> Int64 = 41
end

namespace x
  operation foo() -> Int64 = 99
end

namespace outer.user
  operation useIt() -> Int64 effects Error = x.foo()
end
"#;
    let mut interp = interp_for(SRC);
    match interp.call("outer.user.useIt", &[]).expect("`x.foo()` must run") {
        Value::Int(n) => assert_eq!(
            n, 41,
            "`x.foo()` inside `outer.user` must mean the SIBLING `outer.x.foo` that \
             scope resolution finds, not the top-level `x.foo` — a scope-relative \
             reading outranks a bare global path"
        ),
        other => panic!("expected an Int, got {other:?}"),
    }
}

/// THE GUARD (`head_owns_path`) — a PARTIAL miss must stay loud.
///
/// This is the regression an earlier cut of WI-751 shipped, and the sharpest test here.
/// The head `x` resolves CORRECTLY to the sibling `outer.x`; only the later segment
/// `bar` is absent. That is a member miss on the namespace the head actually named —
/// NOT a licence to re-root the whole path at the same-spelled top-level `x`.
///
/// The `String` return on the top-level `x.bar` is the detector: if the path teleports,
/// the load fails on the RETURN TYPE (`expected Int64, got String`) instead of on the
/// name, which is exactly how the regression was caught. So asserting "fails" is not
/// enough — the failure must be the NAME miss, and must be unchanged by whether the
/// global twin exists at all.
#[test]
fn wi751_partial_miss_under_an_owning_root_stays_loud() {
    const WITH_GLOBAL_TWIN: &str = r#"
namespace outer.x
  operation foo() -> Int64 = 41
end

namespace x
  operation bar() -> String = "teleported"
end

namespace outer.user
  operation useIt() -> Int64 effects Error = x.bar()
end
"#;
    // byte-identical but for the global twin, which is what makes the pair a control
    const NO_GLOBAL_TWIN: &str = r#"
namespace outer.x
  operation foo() -> Int64 = 41
end

namespace x
  operation other() -> String = "unrelated"
end

namespace outer.user
  operation useIt() -> Int64 effects Error = x.bar()
end
"#;
    for (src, label) in
        [(WITH_GLOBAL_TWIN, "with"), (NO_GLOBAL_TWIN, "without")]
    {
        let errs = try_load_kb_with(src).err().unwrap_or_else(|| {
            panic!(
                "`x.bar()` names no member of the sibling `outer.x` that the head \
                 resolves to — it must NOT load {label} a same-spelled top-level `x.bar`"
            )
        });
        let joined = errs.join("\n");
        assert!(
            joined.contains("x.bar") && joined.contains("unknown functor"),
            "the miss must be reported against the NAME `x.bar` {label} a global twin; \
             a return-type error here means the path silently re-rooted at the \
             top-level `x`; got:\n{joined}"
        );
    }
}

/// An AMBIGUOUS head must not be resolved past. `resolve_dotted_by_head` returns None
/// on `Ambiguous`, so without the guard the absolute rung answered instead and silently
/// picked one reading of a name the loader is on record as unable to choose.
#[test]
fn wi751_ambiguous_head_is_not_resolved_past() {
    const SRC: &str = r#"
namespace p1
  sort X
    entity x1(v: Int64)
  end
end
namespace p2
  sort X
    entity x2(v: Int64)
  end
end
namespace X.deep
  operation f() -> String = "global"
end
namespace test.wi751amb
  import p1.*
  import p2.*
  operation g() -> Int64 effects Error = X.deep.f()
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`X` is ambiguous — `X.deep.f()` must not silently resolve through it");
    assert!(
        !errs.iter().any(|e| e.contains("got String")),
        "resolving past the ambiguous head binds the top-level `X.deep.f` (String); \
         got: {errs:?}"
    );
}

/// REACH 1 — an entity FIELD must not capture a namespace path. Fields register under
/// the constructor's qualified name, so `sort data { entity user(name: Int64) }`
/// supplies a complete `<ns>.data.user.name` for the head `data` to land on: without
/// the `Field` refusal, head-qualification HITS and `data.user.name()` is captured from
/// the namespace `data.user`. This is the HIT half of the defect — the absolute rung
/// alone cannot reach it, because head-qualification never misses.
#[test]
fn wi751_entity_field_does_not_capture_a_namespace_path() {
    const SRC: &str = r#"
namespace data.user
  operation name() -> Int64 = 41
end

namespace test.wi751field
  sort data
    entity user(name: Int64)
  end
  operation useIt() -> Int64 effects Error = data.user.name()
end
"#;
    let mut interp = interp_for(SRC);
    match interp.call("test.wi751field.useIt", &[]).expect("`data.user.name()` must run") {
        Value::Int(n) => assert_eq!(
            n, 41,
            "`data.user.name()` must reach the operation in namespace `data.user`, not \
             the local entity's `name` FIELD — a field is reached by dot dispatch on a \
             value, never by a qualified path"
        ),
        other => panic!("expected the operation's Int, got {other:?}"),
    }
}

/// REACH 2 — the BARE rule-reference citation resolves under a shadowed root too.
/// `resolve_qualified_rule_readonly` is the probe the bare (`try_qualified_rule_ref`)
/// and prefix (`rule_prefix_split`) citation paths share; shipping the absolute rung
/// only in `remap_name_str_inner` fixed the applied CALL and left these broken — the
/// WI-729/749/750 citation forms, decomposed into field accesses on a name that
/// resolves.
#[test]
fn wi751_rule_reference_citation_under_a_shadowed_root() {
    const DATA: &str = r#"
namespace myroot.inner
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)
  rule rel(?x) :- q(row: ?x)
end
"#;
    const BARE: &str = r#"
namespace test.wi751bare
  import anthill.prelude.{Int64, Bool}
  sort myroot
    entity mr(row: Int64)
  end
  operation cite() -> Bool effects Error = myroot.inner.rel.isEmpty
end
"#;
    const APPLIED: &str = r#"
namespace test.wi751applied
  import anthill.prelude.{Int64, List, Unit}
  sort myroot
    entity mr(row: Int64)
  end
  operation cite() -> List[Int64] effects Error = myroot.inner.rel.takeN(1)
end
"#;
    for (src, form) in [(BARE, "bare"), (APPLIED, "applied")] {
        try_load_kb_with(&format!("{DATA}{src}")).unwrap_or_else(|errs| {
            panic!(
                "the {form} rule-reference citation `myroot.inner.rel` must resolve \
                 with a `sort myroot` shadowing the root, exactly as the applied call \
                 form does — one probe, one answer; got:\n{}",
                errs.join("\n")
            )
        });
    }
}

/// The WI-749 footgun the ticket asks to pin: a rule LABEL may itself be DOTTED
/// (`rule a.b:` defines the LITERAL scope key `a.b`), so a whole-name SCOPE hit and an
/// absolute-name hit can both exist for one text and only their order decides.
///
/// The fixture carries a COMPETING top-level `namespace a` with a member `b`, so
/// `absolute_qualified("a.b")` genuinely hits — without it the collision is not
/// exercised at all and the test cannot detect a rung hoisted above scope resolution.
/// The two rules have DISTINCT extents so the assertion can tell which relation won.
#[test]
fn wi751_dotted_rule_label_outranks_both_dotted_rungs() {
    const SRC: &str = r#"
namespace a
  operation b() -> Int64 = 99
end

namespace test.wi751label
  import anthill.prelude.{Int64, Bool, List}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)
  fact q(row: 2)
  sort R
    entity r(row: Int64)
  end
  fact r(row: 7)

  rule a: r1(?x) :- q(row: ?x)
  rule a.b: r2(?x) :- r(row: ?x)

  -- the dotted LABEL `a.b`, drained: must be relation `a.b` (extent {7}),
  -- neither relation `a` (extent {1,2}) nor the top-level operation `a.b`.
  operation citeWhole() -> List[Int64] effects Error = a.b.takeN(5)
end
"#;
    let mut interp = interp_for(SRC);
    let got = interp
        .call("test.wi751label.citeWhole", &[])
        .expect("the dotted-label citation must run");
    let rendered = format!("{got:?}");
    // Match on rendered VALUES (`Int(7)`), never bare digits — the debug rendering also
    // carries `Symbol(1002)`-style ids, so a digit search reports false leaks.
    assert!(
        rendered.contains("Int(7)"),
        "`a.b` must be the relation labelled `a.b` (extent {{7}}) — a scope-local whole \
         name outranks BOTH dotted rungs, so neither relation `a` (extent {{1,2}}) nor \
         the top-level `a.b` may win; got {rendered}"
    );
    assert!(
        !rendered.contains("Int(1)") && !rendered.contains("Int(2)"),
        "the citation leaked relation `a`'s extent — the rule PREFIX won over the whole \
         name; got {rendered}"
    );
}

/// NO SILENT RESCUE. A path that names nothing stays the loud unknown-functor error.
///
/// The SHORT-name half pins WI-476's property (an unimported short name is never
/// rescued by a scan of the KB), which is the reason `absolute_qualified` is
/// dotted-only. Note it does NOT by itself exercise that guard: `by_qualified_name` is
/// keyed by FULL name, so `helper` misses whether or not the guard is present. The
/// guard is defensive — it states that a short name is not a path — and the names it
/// could otherwise admit are top-level namespace roots, which `resolve_in_scope` always
/// finds before this rung is reached.
#[test]
fn wi751_unresolvable_paths_stay_loud() {
    const NO_SUCH_PATH: &str = r#"
namespace test.wi751loud1
  sort myroot
    entity mr(row: Int64)
  end
  operation bad() -> Int64 effects Error = myroot.inner.nosuchmember()
end
"#;
    const SHORT_NAME_UNIMPORTED: &str = r#"
namespace test.wi751loud2
  operation bad() -> Int64 effects Error = helper()
end
"#;
    for (src, needle) in
        [(NO_SUCH_PATH, "myroot.inner.nosuchmember"), (SHORT_NAME_UNIMPORTED, "helper")]
    {
        let source = format!("{HELPERS}{src}");
        let errs = try_load_kb_with(&source)
            .err()
            .unwrap_or_else(|| panic!("`{needle}` names nothing reachable — must NOT load"));
        assert!(
            errs.iter().any(|e| e.contains(needle) && e.contains("unknown functor")),
            "`{needle}` must stay the loud unknown-functor error rather than being \
             rescued by the absolute rung; got: {errs:?}"
        );
    }
}

/// The absolute rung applies the SAME `internal` visibility gate the head-qualified
/// rung does — it bypasses `resolve_in_scope`'s filter identically, so a hidden hit
/// must be the precise `ForbiddenInternalAccess`, never a silent resolution.
///
/// The local `sort lib` is load-bearing: it makes head-qualification MISS, so the
/// reference reaches the absolute rung rather than the head one.
#[test]
fn wi751_absolute_path_respects_internal_visibility() {
    const SRC: &str = r#"
namespace lib.secret
  internal operation hidden() -> Int64 = 1
end

namespace test.wi751internal
  sort lib
    entity l(v: Int64)
  end
  operation bad() -> Int64 effects Error = lib.secret.hidden()
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("an `internal` operation named by its absolute path must NOT load");
    assert!(
        errs.iter().any(|e| e.contains("hidden") && e.contains("internal")),
        "naming an `internal` symbol by its absolute path must report the forbidden \
         internal access, not resolve silently; got: {errs:?}"
    );
}
