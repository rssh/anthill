//! WI-872 — A SORT'S IDENTITY IS ITS RESOLVED SYMBOL, NEVER ITS LAST SEGMENT, and
//! `types_compatible`'s nominal leg is where that was not true.
//!
//! `sort_sym_compatible` compared `local_name_of(a) == local_name_of(b)` under the
//! comment *"handles qualified vs short name"* — the unsound short-name comparison of two
//! SORT identities that WI-672 deleted `same_symbol` for (spec §8.6; CLAUDE.md's
//! no-short-name-comparison rule). Because that is the nominal leg of the whole subtype
//! relation and not some peripheral filter, ONE branch produced TWO OPPOSITE symptoms:
//!
//!  * **ACCEPTANCE** at an argument position — `operation takeA(f: a.Foo)` swallowed a
//!    `b.Foo` from another namespace. A silent wrong value, and the half WI-872 never
//!    named. `a_sort_from_another_namespace_is_refused_at_a_parameter` is its witness.
//!  * **REFUSAL** at a dispatch — a local `sort Pair` / `Set` / `Map` was offered the
//!    PRELUDE sort's provision, whose condition then resolved at the prelude sort's OWN
//!    parameter and failed (`no impl matches — unresolved: PartialEq[T =
//!    anthill.prelude.Pair.A]`), so those short names were effectively RESERVED against a
//!    user sort. `a_local_sort_may_share_a_prelude_providers_short_name` is its witness.
//!
//! WHICH ROWS MEASURE THE CHANGE, stated because most do not. With the fix backed out
//! (stashed, rebuilt, re-driven — not reasoned about):
//!
//! | fixture                                     | backed out | fixed   |
//! |---------------------------------------------|------------|---------|
//! | local `Set` / `Map` / `Pair`, `(Float,Int64)`| REFUSED    | 1       |
//! | local `List` / `Option` / `Stream`           | 1          | 1       |
//! | local `Duple` (unclaimed name)               | 1          | 1       |
//! | two-namespace `Foo` at a parameter           | LOADED     | refused |
//! | two-namespace `Foo` under `List[T = …]`      | LOADED     | refused |
//!
//! So `Set`/`Map`/`Pair` and the two `Foo` cases are the assertions that FAIL when the
//! change is backed out; `List`/`Option`/`Stream`/`Duple` pass EITHER WAY and are kept
//! only as the shape control — they are why "the refusal is attributable to the NAME"
//! is a measurement rather than a guess. The ticket's IMPACT claim that every prelude-
//! provided short name is reserved is therefore too wide: at this shape only three are.
//!
//! WHY THE `Float` FIELD IS LOAD-BEARING (WI-1098's feedback on this ticket): WI-1098
//! derives `provides PartialEq`+`Eq` for a TOTAL composite, so an all-`Int64` local
//! `Pair` carries its OWN provision and loads with the defect fully present. One `Float`
//! field derives `NonEq` instead, leaves the carrier with no provision of its own, and
//! puts the prelude's back in play. An all-`Int64` fixture here would measure nothing.
//!
//! THE DIAGNOSTIC HALF (WI-872 (b)) is `the_collision_is_named_in_the_diagnostic`: both
//! sides render by SHORT name, so a namespace-only difference reached WI-795's
//! cause-agnostic backstop and printed *"the difference is in a component this diagnostic
//! does not print; please report it"* — true of an unknown cause, wrong here, where the
//! difference is a namespace and is the repair.
//!
//! Reference: `docs/kernel-language.md` §8.6; `sort_sym_compatible`'s doc comment carries
//! the measurement; WI-672; WI-1098.

use anthill_core::eval::Value;

/// A composite of the WI-1098-underivable shape under `name`, plus an operation that
/// DRIVES its equality. `PartialEq.eq` is the call whose dispatch the defect broke — a
/// load-only fixture would keep passing if `same` resolved to nothing.
fn composite(name: &str, ctor: &str) -> String {
    format!(
        "\nnamespace wi872.shadow\n  \
         import anthill.prelude.{{Int64, Float, Bool, PartialEq}}\n  \
         sort {name}\n    entity {ctor}(a: Float, b: Int64)\n  end\n  \
         sort Use\n    \
         operation same(n: Int64) -> Int64 =\n      \
         if PartialEq.eq({ctor}(a: 1.0, b: 2), {ctor}(a: 1.0, b: 2)) then 1 else 0\n  \
         end\nend\n"
    )
}

fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

/// Two namespaces each declaring `sort Foo`, and a third that takes `wi872.a.Foo` at
/// `param_type` while passing a `wi872.b.Foo`. Only the constructor is imported from
/// `b` — importing both sorts would collide on the short name at the import itself,
/// which is a different (and correctly reported) refusal.
fn two_namespace_foo(param_type: &str, arg: &str) -> String {
    format!(
        "\nnamespace wi872.a\n  import anthill.prelude.{{Int64}}\n  \
         sort Foo\n    entity mkfoo(x: Int64)\n  end\nend\n\
         \nnamespace wi872.b\n  import anthill.prelude.{{Int64}}\n  \
         sort Foo\n    entity mkfoo2(y: Int64)\n  end\nend\n\
         \nnamespace wi872.use\n  \
         import anthill.prelude.{{Int64, List}}\n  \
         import anthill.prelude.List.{{cons, nil}}\n  \
         import wi872.a.{{Foo}}\n  \
         import wi872.b.{{mkfoo2}}\n  \
         sort Use\n    \
         operation takeA(f: {param_type}) -> Int64 = 1\n    \
         operation drive() -> Int64 = takeA({arg})\n  end\nend\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(src) {
        Err(e) => e,
        Ok(_) => panic!("expected a load error, the program loaded clean"),
    }
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so the
/// "loads and evaluates" assertions below are real and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(
        "\nnamespace wi872.control\n  import anthill.prelude.{Int64}\n  \
         sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end\nend\n",
    );
}

// ── Symptom 1: the REFUSAL (the half WI-872 was filed for) ───────────

/// A user sort may be named for a prelude sort that provides an instance. DRIVEN, not
/// loaded: `same` must COMPUTE 1, so the dispatch the defect broke has to reach the
/// composite's own field-wise equality.
///
/// `Set`, `Map` and `Pair` are the rows that fail when the change is backed out.
/// `List`, `Option` and `Stream` pass either way — kept as the shape control, since
/// without them "these three are refused" would not distinguish a name effect from a
/// shape effect. `Duple` names nothing in the prelude and is the baseline.
#[test]
fn a_local_sort_may_share_a_prelude_providers_short_name() {
    for (name, ctor) in [
        // Discriminating: refused at HEAD, computes 1 with the fix.
        ("Set", "mkset"),
        ("Map", "mkmap"),
        ("Pair", "mkpair"),
        // Pass either way — the shape control.
        ("List", "mklist"),
        ("Option", "mkoption"),
        ("Stream", "mkstream"),
        ("Duple", "mkduple"),
    ] {
        assert_eq!(
            eval_int(
                &composite(name, ctor),
                "wi872.shadow.Use.same",
                &format!("a local `sort {name}` must compute its own field-wise equality"),
            ),
            1,
            "`{name}` is a user sort; the prelude's provision for its short name must \
             not be offered for it (WI-872)",
        );
    }
}

// ── Symptom 2: the ACCEPTANCE (the half the ticket never named) ──────

/// A value of `wi872.b.Foo` is NOT a `wi872.a.Foo`. This LOADED CLEAN before the fix —
/// the argument check's nominal leg matched the two by last segment — so this is the
/// soundness direction, and it fails when the change is backed out.
#[test]
fn a_sort_from_another_namespace_is_refused_at_a_parameter() {
    let errs = load_errs(&two_namespace_foo("Foo", "mkfoo2(y: 7)"));
    assert!(
        errs.iter().any(|e| e.contains("takeA.f")),
        "the refusal must land on the argument, not somewhere incidental: {errs:?}"
    );
}

/// The same collision NESTED under a parameterized type. A separate arm because the
/// diagnostic's walk is what makes it reachable — a bare-`sort_ref`-only cause would
/// leave this printing the untargeted note, and it is exactly as wrong here.
#[test]
fn a_nested_sort_from_another_namespace_is_refused() {
    let errs = load_errs(&two_namespace_foo(
        "List[T = Foo]",
        "cons(head: mkfoo2(y: 7), tail: nil())",
    ));
    assert!(
        errs.iter().any(|e| e.contains("takeA.f")),
        "the nested collision must be refused at the argument: {errs:?}"
    );
}

// ── WI-872 (b): the diagnostic ───────────────────────────────────────

/// Both sides render by SHORT name, so the message reads `expected Foo, got Foo`. It
/// must say WHY, and the two qualified names ARE the repair.
///
/// The `Foo2` arm is the CONTROL and it is what makes this an assertion about the
/// COLLISION rather than about any mismatch: two sorts with DIFFERENT short names render
/// differently, so no note is due, and none is emitted. Both arms pass with the change
/// backed out only in the sense that neither program exists there — the `Foo` arm cannot
/// run at all, because at HEAD it LOADS.
#[test]
fn the_collision_is_named_in_the_diagnostic() {
    for (param, arg, why) in [
        ("Foo", "mkfoo2(y: 7)", "bare"),
        (
            "List[T = Foo]",
            "cons(head: mkfoo2(y: 7), tail: nil())",
            "nested",
        ),
    ] {
        let errs = load_errs(&two_namespace_foo(param, arg));
        let joined = errs.join("\n");
        assert!(
            joined.contains("wi872.a.Foo") && joined.contains("wi872.b.Foo"),
            "the {why} collision must name BOTH qualified sorts — that is the repair: {errs:?}"
        );
        assert!(
            !joined.contains("please report it"),
            "the {why} collision has a KNOWN cause and must not fall through to WI-795's \
             cause-agnostic backstop: {errs:?}"
        );
    }

    let ctrl = load_errs(&two_namespace_foo("Foo", "mkfoo2(y: 7)").replace(
        "sort Foo\n    entity mkfoo2",
        "sort Foo2\n    entity mkfoo2",
    ));
    let ctrl_joined = ctrl.join("\n");
    assert!(
        ctrl_joined.contains("expected Foo, got Foo2"),
        "CONTROL: distinct short names render differently, so the pair says everything \
         on its own: {ctrl:?}"
    );
    assert!(
        !ctrl_joined.contains("share the short name"),
        "CONTROL: no collision, so no collision note — without this the note above \
         would be evidence of nothing: {ctrl:?}"
    );
}
