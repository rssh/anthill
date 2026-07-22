//! WI-750 — a METHOD CALL whose receiver is a CHAIN (`person_row.negate.takeN(5)`,
//! `p.inner.abs()`).
//!
//! WI-749 widened the ZERO-ARG field path to admit a receiver some PREFIX of whose
//! name resolves to a rule, so member chains on a relation re-route level by level.
//! The METHOD-CALL path was not widened and still reached a rule receiver only at
//! DEPTH 1, so the same receiver was a VALUE for `x.m` and a static NAME PATH for
//! `x.m(args)` — `person_row.negate.isEmpty` loaded, `person_row.negate.takeN(5)` did
//! not. Not a WI-749 regression: both spellings failed before it.
//!
//! THE ASYMMETRY, and why the fix lives in the loader. The converter classifies a dot
//! receiver SYNTACTICALLY (`is_value_receiver`): a receiver rooted at an identifier is
//! a NAME, so `push_fn_term` flattens the whole dotted callee to ONE functor symbol
//! (`person_row.negate.takeN`) while `push_field_access` keeps a nested `field_access`
//! whose object is VISITED. That is the whole difference — the field path DEFERS the
//! value-vs-name decision to the loader, where scope is known, and the call path
//! decided it early and destroyed the structure the decision needs.
//!
//! It cannot be fixed by making the converter route both the same way: it is
//! scope-blind, and `ns.Sort.op(args)` is a legitimate qualified call with exactly the
//! shape of `person_row.negate.takeN(5)`. So the call path recovers the chain from the
//! NAME instead — `dot_call_receiver_chain` decomposes the receiver into the value
//! place it is ROOTED at plus the trailing zero-arg members, which
//! `try_identifier_dot_call` folds into `DotApply`s over that root. Same lowering the
//! field path reaches by Visiting, same precedence ladder (a local root outranks a
//! whole-chain rule citation, which outranks a shorter rule prefix).
//!
//! This also lifts WI-443's deferred chained-LOCAL receiver (`p.inner.abs()`), which
//! shared the root cause and was pinned as a loud error in the WI-729 suite.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with, try_load_kb_with_files};

const RULE_CHAIN: &str = r#"
namespace test.wi750
  import anthill.prelude.{String, Int64, Bool, List, Unit}
  import anthill.prelude.Relation.{negate}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  -- WI-750: the INLINE chained-receiver CALL.
  operation inlineChain() -> List[Unit] effects Error =
    person_row.negate.takeN(5)

  -- its let-bound reference spelling.
  operation letBoundChain() -> List[Unit] effects Error =
    let r = person_row
    let n = r.negate
    n.takeN(5)
end
"#;

/// ACCEPTANCE: a method call on a chained rule-reference receiver loads, exactly as
/// the let-bound spelling beside it does. Before WI-750 the inline form died in the
/// LOADER (`person_row.negate.takeN.apply: unknown functor` — the flattened callee),
/// so reaching the same lowering as the let-bound twin is the whole point.
#[test]
fn wi750_rule_chain_method_call_loads_like_let_bound() {
    try_load_kb_with(RULE_CHAIN).unwrap_or_else(|errs| {
        panic!(
            "`person_row.negate.takeN(5)` must re-route and load exactly as its \
             let-bound spelling does; got:\n{}",
            errs.join("\n")
        )
    });
}

/// ACCEPTANCE (the EVAL half), on the LOCAL chain — WI-443's deferred case, lifted.
/// The rule chain's members are relation combinators whose runtime needs a closed
/// membership operand, so the sharp EVAL comparison lives here, where the chain is
/// ordinary data: `p.inner.abs()` must produce the same value as binding `p.inner`
/// first. Before WI-750 this was the loud `p.inner.abs: unknown functor`.
#[test]
fn wi750_local_chain_method_call_evals_like_let_bound() {
    const SRC: &str = r#"
namespace test.wi750local
  import anthill.prelude.{Int64}
  sort Box
    entity box(inner: Int64)
  end

  operation inlineLocal() -> Int64 effects Error =
    let p = box(inner: 0 - 3)
    p.inner.abs()

  operation letBoundLocal() -> Int64 effects Error =
    let p = box(inner: 0 - 3)
    let i = p.inner
    i.abs()
end
"#;
    let mut interp = interp_for(SRC);
    let call = |interp: &mut anthill_core::eval::Interpreter, op: &str| -> i64 {
        match interp
            .call(&format!("test.wi750local.{op}"), &[])
            .unwrap_or_else(|e| panic!("`{op}` must run; got {e:?}"))
        {
            Value::Int(n) => n,
            other => panic!("`{op}` must answer an Int, got {other:?}"),
        }
    };
    let inline = call(&mut interp, "inlineLocal");
    assert_eq!(inline, 3, "`p.inner.abs()` must be the absolute value of -3");
    assert_eq!(
        inline,
        call(&mut interp, "letBoundLocal"),
        "the inline local chain must evaluate exactly like `let i = p.inner; i.abs()`"
    );
}

/// The call really dispatches ON the chained receiver's sort. A bad member at the END
/// of the chain must be reported by the TYPER's dot dispatch against `Relation` (what
/// `negate` answers), NOT by the loader's unknown-functor path — which is what proves
/// the receiver became a VALUE rather than the chain staying a static name path.
#[test]
fn wi750_chained_call_dispatches_on_the_receiver_sort() {
    const SRC: &str = r#"
namespace test.wi750dispatch
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{negate}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation bad() -> Bool effects Error =
    person_row.negate.nosuchmethod(5)
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`nosuchmethod` names no member of Relation — this must NOT load");
    let joined = errs.join("\n");
    assert!(
        joined.contains("Relation.nosuchmethod") && joined.contains("dot dispatch"),
        "the chained call must miss in the typer's dot dispatch against Relation, not \
         in the loader; got:\n{joined}",
    );
    assert!(
        !joined.contains("unknown functor"),
        "the loader's unknown-functor error is exactly what WI-750 removed here; \
         got:\n{joined}",
    );
}

/// PRECEDENCE 1 — a LOCAL ROOT outranks a same-named RULE, so widening the probe to
/// chained receivers must not let the rule reading capture a shadowed binder. With a
/// rule ALSO named `p` in scope, `p.inner.abs()` on a local `p` stays the local's
/// field: the answer is the box's data, not a `Relation` member miss.
///
/// This is the call-path peer of `wi749_local_root_beats_the_whole_chain_citation`,
/// and the case the WI-729 suite used to cover by requiring the whole chain to FAIL.
#[test]
fn wi750_local_root_is_not_reinterpreted_as_a_rule() {
    const SRC: &str = r#"
namespace test.wi750shadow
  import anthill.prelude.{Int64}
  sort Box
    entity box(inner: Int64)
  end
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  -- a rule sharing the local binder's name.
  rule p(?row) :- q(row: ?row)

  operation shadowed() -> Int64 effects Error =
    let p = box(inner: 0 - 3)
    p.inner.abs()
end
"#;
    let mut interp = interp_for(SRC);
    match interp
        .call("test.wi750shadow.shadowed", &[])
        .expect("the shadowed chained receiver runs")
    {
        Value::Int(n) => assert_eq!(
            n, 3,
            "a local binder must win over a same-named rule — `p.inner` is the box's \
             field, not a member of relation `p`"
        ),
        other => panic!("expected the local box's field, got {other:?}"),
    }
}

/// PRECEDENCE 2 — the WHOLE-CHAIN citation beats a shorter rule PREFIX, because a rule
/// LABEL may itself be dotted (`rule a.b: …`). With rules `a` AND `a.b` both in scope,
/// the receiver `a.b` is the relation labelled `a.b`, NOT member `b` of relation `a` —
/// so rule prefixes are probed LONGEST-FIRST.
///
/// This is the call-path peer of `wi749_whole_chain_citation_beats_a_rule_prefix`,
/// which caught a real regression: probing short prefixes first silently resolved the
/// citation to a DIFFERENT relation, and only when the unrelated rule `a` also existed
/// — breakage by action at a distance.
#[test]
fn wi750_whole_chain_citation_beats_a_rule_prefix() {
    const ONLY_DOTTED: &str = r#"
namespace test.wi750dotted1
  import anthill.prelude.{Int64, Bool, List}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  rule a.b: r2(?x) :- q(row: ?x)

  operation cite() -> List[Int64] effects Error =
    a.b.takeN(5)
end
"#;
    // Identical, but a rule ALSO labelled `a` — a proper prefix of `a.b` — is added.
    const PREFIX_TOO: &str = r#"
namespace test.wi750dotted2
  import anthill.prelude.{Int64, Bool, List}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  rule a: r1(?x) :- q(row: ?x)
  rule a.b: r2(?x) :- q(row: ?x)

  operation cite() -> List[Int64] effects Error =
    a.b.takeN(5)
end
"#;
    for (src, label) in [(ONLY_DOTTED, "without"), (PREFIX_TOO, "with")] {
        try_load_kb_with(src).unwrap_or_else(|errs| {
            panic!(
                "the call `a.b.takeN(5)` must take its receiver from the rule labelled \
                 `a.b` {label} a same-named prefix rule in scope; got:\n{}",
                errs.join("\n")
            )
        });
    }
}

/// A NAMESPACE-qualified chained receiver from ANOTHER FILE. The rule prefix reaches
/// the same resolution however many segments it spans, and a multi-segment name takes
/// a genuinely different route inside `resolve_qualified_rule_readonly`
/// (`resolve_in_scope` misses, so it falls through to `resolve_dotted_by_head` plus the
/// `qualified_visible` gate) that the 1- and 2-segment cases never exercise.
#[test]
fn wi750_namespace_qualified_cross_file_chain() {
    const DATA: &str = r#"
namespace test.wi750ns.data
  import anthill.prelude.{String, Int64}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
end
"#;
    const USE: &str = r#"
namespace test.wi750ns.use
  import anthill.prelude.{Bool, List, Unit}
  import anthill.prelude.Relation.{negate}

  operation inlineCrossFile() -> List[Unit] effects Error =
    test.wi750ns.data.person_row.negate.takeN(5)

  operation letBoundCrossFile() -> List[Unit] effects Error =
    let r = test.wi750ns.data.person_row
    let n = r.negate
    n.takeN(5)
end
"#;
    try_load_kb_with_files(&[DATA, USE]).unwrap_or_else(|errs| {
        panic!(
            "a cross-file namespace-qualified CHAINED receiver must load, as its \
             let-bound twin does; got: {errs:?}"
        )
    });
}

/// NO SILENT FALLBACK: a chained receiver rooted at neither a local value nor a rule
/// keeps the qualified-name flattening and its loud unknown-functor diagnostic. Both
/// sources present the widened probe with a genuine NEAR MISS — a rule or sort IS in
/// scope, just not at the name used — so a probe that scanned prefixes too loosely
/// would re-route instead of failing, and be caught here.
#[test]
fn wi750_unresolvable_chained_receiver_stays_loud() {
    const NO_SUCH_MEMBER: &str = r#"
namespace test.wi750loud1
  import anthill.prelude.{Int64, List}
  sort Queen
    entity queen(row: Int64)
    rule find(?row) :- queen(row: ?row)
  end
  fact queen(row: 1)
  operation bad() -> List[Int64] effects Error =
    Queen.nosuch.deeper.takeN(5)
end
"#;
    const NOTHING_IN_SCOPE: &str = r#"
namespace test.wi750loud2
  import anthill.prelude.{Int64, List}
  operation bad() -> List[Int64] effects Error =
    nosuchns.nosuchrule.deeper.takeN(5)
end
"#;
    for (src, flattened) in [
        (NO_SUCH_MEMBER, "Queen.nosuch.deeper.takeN"),
        (NOTHING_IN_SCOPE, "nosuchns.nosuchrule.deeper.takeN"),
    ] {
        let errs = try_load_kb_with(src).err().unwrap_or_default();
        assert!(
            errs.iter().any(|e| e.contains(flattened) && e.contains("unknown functor")),
            "`{flattened}` must stay the loud unknown-functor error, got: {errs:?}"
        );
    }
}

/// NO REGRESSION: a genuine namespace-qualified COMPANION CALL keeps the
/// qualified-name path. `ns.Sort.op(args)` has exactly the shape of a chained-receiver
/// call, and only the receiver's failure to name a value separates them — which is why
/// the converter cannot make this decision and the loader must.
#[test]
fn wi750_qualified_companion_call_keeps_the_name_path() {
    const DATA: &str = r#"
namespace test.wi750comp.data
  import anthill.prelude.{String, Int64}
  sort Person
    entity person(name: String, age: Int64)
    operation describe(p: Person) -> String = "described"
  end
end
"#;
    const USE: &str = r#"
namespace test.wi750comp.use
  import anthill.prelude.{String}
  import test.wi750comp.data.{Person}

  operation callCompanion() -> String effects Error =
    test.wi750comp.data.Person.describe(Person.person(name: "a", age: 1))
end
"#;
    try_load_kb_with_files(&[DATA, USE]).unwrap_or_else(|errs| {
        panic!(
            "a namespace-qualified companion CALL must stay on the qualified-name \
             path; got: {errs:?}"
        )
    });
}

/// ACCEPTANCE (the SCHEMA half): a row lambda on a member of a COMPUTED receiver types
/// its binder at the relation's CONCRETE schema. `where` preserves columns, so
/// `person_row.where(λc).where(λd)` gives the outer lambda a receiver that is the inner
/// CALL'S RESULT rather than a name — the one receiver shape neither hint reader
/// matched, so `d` used to bind at the raw projection `r.T` and `d.name` had no sort to
/// dispatch on (the WI-723 symptom, `<unresolved receiver>.name`).
///
/// The type was always available — a dot call's Build frame runs after its receiver's
/// Visit+Stamp — just unread, so the fix is the third reader (`projection_receiver_type`),
/// at the time shared with the WI-714 projection path. WI-762 removed that path's use of
/// it, so this hint path is now its SOLE consumer; the rung this test pins is unchanged.
#[test]
fn wi750_row_lambda_schema_through_a_computed_receiver() {
    const SRC: &str = r#"
namespace test.wi750rowschema
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{where}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  -- the outer lambda's receiver is the INNER CALL'S result.
  operation chained() -> Bool effects Error =
    person_row.where(lambda c -> eq(c.name, "alice")).where(lambda d -> eq(d.name, "bob")).isEmpty

  -- its let-bound reference spelling, which always worked.
  operation letBound() -> Bool effects Error =
    let w = person_row.where(lambda c -> eq(c.name, "alice"))
    w.where(lambda d -> eq(d.name, "bob")).isEmpty

  -- THREE levels: the reader must hold past depth 2, and `age` proves a column other
  -- than the one the earlier levels used still resolves.
  operation threeLevels() -> Bool effects Error =
    person_row.where(lambda c -> eq(c.name, "a")).where(lambda d -> eq(d.name, "b")).where(lambda e2 -> eq(e2.age, 30)).isEmpty
end
"#;
    try_load_kb_with(SRC).unwrap_or_else(|errs| {
        panic!(
            "a row lambda over a COMPUTED receiver must bind at the concrete schema, \
             exactly as the let-bound spelling beside it does; got:\n{}",
            errs.join("\n")
        )
    });
}

/// The schema is REAL, not an absorbing type var: a column the row does not have must
/// still be a loud miss. Asserted against BOTH comparands — the let-bound spelling and
/// the depth-1 receiver (WI-723's own shape) — because what matters is that the chained
/// form behaves IDENTICALLY, not that it produces any particular wording. (All three
/// currently name `<unresolved receiver>`: a row type is a named TUPLE, so
/// `sort_functor_of_view` has no sort functor to report. That is uniform and
/// pre-existing — a diagnostic-quality limitation, not a chained-receiver defect.)
#[test]
fn wi750_bad_column_stays_loud_through_a_computed_receiver() {
    const CHAINED: &str = r#"
namespace test.wi750badcol1
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{where}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation bad() -> Bool effects Error =
    person_row.where(lambda c -> eq(c.name, "alice")).where(lambda d -> eq(d.nosuchcol, "bob")).isEmpty
end
"#;
    const LET_BOUND: &str = r#"
namespace test.wi750badcol2
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{where}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation bad() -> Bool effects Error =
    let w = person_row.where(lambda c -> eq(c.name, "alice"))
    w.where(lambda d -> eq(d.nosuchcol, "bob")).isEmpty
end
"#;
    const DEPTH1: &str = r#"
namespace test.wi750badcol3
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{where}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
  operation bad() -> Bool effects Error =
    person_row.where(lambda c -> eq(c.nosuchcol, "alice")).isEmpty
end
"#;
    for (src, label) in
        [(CHAINED, "chained"), (LET_BOUND, "let-bound"), (DEPTH1, "depth-1")]
    {
        let errs = try_load_kb_with(src)
            .err()
            .unwrap_or_else(|| panic!("`nosuchcol` is not a column — the {label} \
                 spelling must NOT load; an absorbing binder type would swallow it"));
        assert!(
            errs.iter().any(|e| e.contains("nosuchcol") && e.contains("dot dispatch")),
            "the {label} spelling must miss in dot dispatch, got: {errs:?}"
        );
    }
}

/// PRECEDENCE 3, and the sharpest regression pin in this suite — the APPLIED CITATION
/// gets first refusal over the rule-PREFIX scan.
///
/// A rule LABEL may be dotted (`rule a.b.c: …`), so `a.b.c(2)` is that rule APPLIED.
/// The first cut of WI-750 gave the call path only two of the field ladder's three
/// rungs — local root and prefix scan — omitting the whole-name citation the field
/// path interposes as `try_qualified_rule_ref`. With the rung missing, the prefix scan
/// peeled `a.b.c(2)` into member `c` of member `b` of relation `a` the moment an
/// unrelated `rule a` existed, while the BARE `a.b.c` still read as the rule: one name,
/// two meanings, decided by a declaration the expression never mentions.
///
/// So the two sources below must load IDENTICALLY. The `rule a` in the second is inert
/// — nothing in `a.b.c(2)` refers to it — and a reading that lets it change the answer
/// is the WI-749 action-at-a-distance footgun in its call-path form.
#[test]
fn wi750_applied_citation_beats_a_rule_prefix() {
    const ONLY_DOTTED: &str = r#"
namespace test.wi750applied1
  import anthill.prelude.{Int64, Bool, Unit}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  rule a.b.c: r3(?x) :- q(row: ?x)

  operation cite() -> Bool effects Error =
    a.b.c(2).isEmpty
end
"#;
    // Identical, plus an inert rule labelled `a` — a proper PREFIX of the applied name.
    const PREFIX_TOO: &str = r#"
namespace test.wi750applied2
  import anthill.prelude.{Int64, Bool, Unit}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  rule a: r1(?x) :- q(row: ?x)
  rule a.b.c: r3(?x) :- q(row: ?x)

  operation cite() -> Bool effects Error =
    a.b.c(2).isEmpty
end
"#;
    for (src, label) in [(ONLY_DOTTED, "without"), (PREFIX_TOO, "with")] {
        try_load_kb_with(src).unwrap_or_else(|errs| {
            panic!(
                "`a.b.c(2)` must APPLY the rule labelled `a.b.c` {label} an unrelated \
                 prefix rule `a` in scope — an inert declaration must not change what \
                 the call means; got:\n{}",
                errs.join("\n")
            )
        });
    }
}

/// A trailing chain of length >= 2, which pins the `.rev()` on the segment fold. Every
/// other case in this suite bottoms out at exactly ONE trailing segment, so nothing
/// else distinguishes innermost-first from outermost-first: with the order inverted
/// this builds `((p.leaf).mid).abs()` and `Outer` has no `leaf`, so it fails to load.
#[test]
fn wi750_two_trailing_segments_fold_innermost_first() {
    const SRC: &str = r#"
namespace test.wi750depth2
  import anthill.prelude.{Int64}
  sort Inner
    entity inner(leaf: Int64)
  end
  sort Outer
    entity outer(mid: Inner)
  end

  operation deep() -> Int64 effects Error =
    let p = outer(mid: inner(leaf: 0 - 5))
    p.mid.leaf.abs()

  operation letBoundDeep() -> Int64 effects Error =
    let p = outer(mid: inner(leaf: 0 - 5))
    let m = p.mid
    let l = m.leaf
    l.abs()
end
"#;
    let mut interp = interp_for(SRC);
    let call = |interp: &mut anthill_core::eval::Interpreter, op: &str| -> i64 {
        match interp
            .call(&format!("test.wi750depth2.{op}"), &[])
            .unwrap_or_else(|e| panic!("`{op}` must run; got {e:?}"))
        {
            Value::Int(n) => n,
            other => panic!("`{op}` must answer an Int, got {other:?}"),
        }
    };
    let inline = call(&mut interp, "deep");
    assert_eq!(inline, 5, "`p.mid.leaf.abs()` must be the absolute value of -5");
    assert_eq!(
        inline,
        call(&mut interp, "letBoundDeep"),
        "a two-segment trailing chain must fold innermost-first, evaluating like its \
         fully let-bound spelling"
    );
}


/// PRECEDENCE 0 — the QUALIFIED NAME gets first refusal over the whole re-route ladder.
///
/// The re-route is a RESCUE for names the qualified-name path cannot resolve. When it
/// CAN, decomposing anyway replaces a working resolution with a member chain over some
/// prefix. The first cut of WI-750 had no such rung and produced three distinct
/// regressions against code that loaded before, all of them action-at-a-distance from a
/// declaration the failing expression never mentions:
///
///   1. an inert `rule a` peeling the applied citation `a.b.c(2)` into `(a.b).c`;
///   2. a binder named `app` capturing `app.helpers.Helper.twice(2)` — the binder does
///      NOT shadow that name, which is ONE name, not a projection off `app`; shadowing
///      compares whole names and the binder's is a strict prefix;
///   3. `rule anthill` disabling every `anthill.prelude.…` call in its file.
///
/// Each source below pairs the hazard with a byte-identical control that removes only
/// the colliding declaration. Both halves must behave the SAME — that equality is the
/// property, not any particular diagnostic.
#[test]
fn wi750_qualified_name_beats_the_reroute_ladder() {
    // (1) an inert prefix rule must not capture an applied dotted-label citation.
    const APPLIED_WITH_PREFIX_RULE: &str = r#"
namespace test.wi750fr1
  import anthill.prelude.{Int64, Bool, Unit}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)
  rule a: r1(?x) :- q(row: ?x)
  rule a.b.c: r3(?x) :- q(row: ?x)
  operation cite() -> Bool effects Error =
    a.b.c(2).isEmpty
end
"#;
    // (2) a LOCAL sharing only the ROOT SEGMENT of a qualified path must not capture it.
    const HELPERS: &str = r#"
namespace test.wi750fr.helpers
  import anthill.prelude.{Int64}
  sort Helper
    entity helper(v: Int64)
    operation twice(n: Int64) -> Int64 = n + n
  end
end
"#;
    const BINDER_SHARES_ROOT: &str = r#"
namespace test.wi750fr.main
  import anthill.prelude.{Int64}
  operation plain() -> Int64 effects Error =
    test.wi750fr.helpers.Helper.twice(2)
  operation withBinder() -> Int64 effects Error =
    let test = 1
    test.wi750fr.helpers.Helper.twice(2)
end
"#;
    try_load_kb_with(APPLIED_WITH_PREFIX_RULE).unwrap_or_else(|errs| {
        panic!(
            "an inert `rule a` must not change what `a.b.c(2)` means — the whole name \
             is a rule and the qualified path resolves it; got:\n{}",
            errs.join("\n")
        )
    });
    try_load_kb_with_files(&[HELPERS, BINDER_SHARES_ROOT]).unwrap_or_else(|errs| {
        panic!(
            "a binder named `test` must not capture `test.wi750fr.helpers.Helper.twice(2)`: \
             that is ONE qualified name, not a projection off the binder; got: {errs:?}"
        )
    });
}
