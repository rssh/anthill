//! WI-749 (WI-714 follow-up F2) — a ZERO-ARG MEMBER on a rule-reference value
//! (`person_row.isEmpty`, `Person.rows.isEmpty`).
//!
//! The zero-arg dual of WI-729's method-call re-route, and INDEPENDENT of
//! qualification: the bare-UNQUALIFIED spelling failed too, so this predates
//! WI-729 — a WI-723/WI-280 gap, not a regression.
//!
//! WI-723 widened the METHOD-CALL receiver probe to accept a RULE (a rule reference
//! IS a `Relation[T]` value, WI-714), but the FIELD-ACCESS path never got that
//! widening: it gated on the chain's ROOT naming a local binder / op param, and a
//! rule root answers `None`. The chain then stayed a `field_access`, whose member
//! `Ident` lowered to an unresolved `var_ref` — the loud
//! `isEmpty.name: expected resolved name, got unresolved`.
//!
//! The gate now also admits a receiver some PREFIX of whose name resolves to a rule.
//! Note what did NOT change: the receiver is still VISITED, never synthesized — at
//! the level where the prefix is exact it collapses to `var_ref(Ref(rule))` on its
//! own (`load_var_ref` for the bare name, `try_qualified_rule_ref` for the dotted
//! chain), which is why both spellings ride the citation lowering WI-714 already
//! landed rather than a second copy of it.
//!
//! Nothing was blocked before (`let r = person_row; r.isEmpty` works) — only the
//! inline spelling. These tests pin the inline spellings to the let-bound one.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with, try_load_kb_with_files};

/// Both inline spellings — bare-UNQUALIFIED (`person_row`) and bare-QUALIFIED
/// (`Person.rows`) — each against ITS OWN let-bound reference. The two relations are
/// deliberately given OPPOSITE emptiness (`person_row` matches alice; `Person.rows`
/// filters on an age no fact has) so that a receiver resolving to the wrong one of
/// them is a visible `true`/`false` flip rather than a silent agreement.
const SRC: &str = r#"
namespace test.wi749
  import anthill.prelude.{String, Int64, Bool}

  sort Person
    entity person(name: String, age: Int64)
    -- EMPTY: no fact has age 999.
    rule rows(?name, ?age) :- person(name: ?name, age: 999)
  end
  fact person(name: "alice", age: 30)

  -- NON-EMPTY.
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  -- the let-bound spellings (WI-714 citation + WI-280 dot field): the references.
  operation letBoundBare() -> Bool effects Error =
    let r = person_row
    r.isEmpty

  operation letBoundQualified() -> Bool effects Error =
    let r = Person.rows
    r.isEmpty

  -- WI-749: the INLINE spellings.
  operation inlineBare() -> Bool effects Error =
    person_row.isEmpty

  operation inlineQualified() -> Bool effects Error =
    Person.rows.isEmpty
end
"#;

fn call_bool(interp: &mut anthill_core::eval::Interpreter, op: &str) -> bool {
    interp
        .call(&format!("test.wi749.{op}"), &[])
        .unwrap_or_else(|e| panic!("`{op}` must run; got {e:?}"))
        .as_bool()
        .unwrap_or_else(|| panic!("`{op}` must answer a Bool"))
}

/// ACCEPTANCE: both inline spellings load and EVAL equal to their own let-bound
/// reference — and the two references disagree, so the comparison has real content.
#[test]
fn wi749_zero_arg_member_on_rule_ref_matches_let_bound() {
    let mut interp = interp_for(SRC);
    let bare = call_bool(&mut interp, "letBoundBare");
    let qualified = call_bool(&mut interp, "letBoundQualified");
    assert!(!bare, "`person_row` matches alice, so it is NOT empty");
    assert!(qualified, "`Person.rows` filters on age 999, so it IS empty");
    assert_eq!(
        call_bool(&mut interp, "inlineBare"),
        bare,
        "`person_row.isEmpty` must evaluate exactly like `let r = person_row; r.isEmpty`"
    );
    assert_eq!(
        call_bool(&mut interp, "inlineQualified"),
        qualified,
        "`Person.rows.isEmpty` must evaluate like `let r = Person.rows; r.isEmpty` — \
         and since the two relations differ in emptiness, this also proves the \
         qualified receiver did not resolve to the other relation in scope"
    );
}

/// ACCEPTANCE (the TYPE half): the re-routed receiver carries the relation's CONCRETE
/// schema, not an open type var that would absorb any demand. `names` has one free
/// column of type `String`, so `splitFirst`'s row type is observable in a mismatch —
/// the error must name `String`. (This is the zero-arg analogue of WI-729's row-binder
/// schema test, and guards the WI-723/WI-726 failure mode where `Relation[T]` was left
/// unbound: every other test here answers `Bool`, which is schema-blind.)
#[test]
fn wi749_receiver_schema_is_concrete_through_the_reroute() {
    const SRC: &str = r#"
namespace test.wi749schema
  import anthill.prelude.{String, Int64}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule names(?name) :- person(name: ?name, age: ?)

  operation probe() -> Int64 effects Error =
    names.splitFirst
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`splitFirst` answers an Option, not an Int64 — this must NOT load");
    let joined = errs.join("\n");
    assert!(
        joined.contains("String"),
        "the mismatch must expose the relation's CONCRETE column type (String) — an \
         unresolved schema var would print no such type; got:\n{joined}",
    );
}

/// The member really dispatches ON the `Relation`. `size` is the sharp probe: a
/// relation is MAYBE-INFINITE, so `Relation` deliberately stops short of
/// `FiniteCollection` and provides no `size` / `collect` (the finiteness cut, WI-589).
/// Asking for it must be a loud dot-dispatch miss ON the relation — only reachable if
/// the re-route dispatched the member on the rule-reference value in the first place.
#[test]
fn wi749_member_dispatches_on_the_relation_sort() {
    const SRC: &str = r#"
namespace test.wi749dispatch
  import anthill.prelude.{String, Int64}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation bad() -> Int64 effects Error =
    person_row.size
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`Relation` provides no `size` — this must NOT load");
    let joined = errs.join("\n");
    assert!(
        joined.contains("Relation.size") && joined.contains("dot dispatch"),
        "`person_row.size` must be a dot-dispatch miss on Relation (no `size`: a \
         relation is maybe-infinite); got:\n{joined}",
    );
}

/// A NAMESPACE-qualified receiver from ANOTHER FILE (a 4-segment prefix). The prefix
/// reaches the same rule resolution regardless of how many segments it spans — and a
/// multi-segment name takes a genuinely different route inside
/// `resolve_qualified_rule_readonly` (`resolve_in_scope` misses, so it falls through
/// to `resolve_dotted_by_head` plus the `qualified_visible` gate), which the 1- and
/// 2-segment cases never exercise.
#[test]
fn wi749_namespace_qualified_cross_file_receiver() {
    const DATA: &str = r#"
namespace test.wi749ns.data
  import anthill.prelude.{String, Int64}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
end
"#;
    const USE: &str = r#"
namespace test.wi749ns.use
  import anthill.prelude.{Bool}

  operation inlineCrossFile() -> Bool effects Error =
    test.wi749ns.data.person_row.isEmpty

  operation letBoundCrossFile() -> Bool effects Error =
    let r = test.wi749ns.data.person_row
    r.isEmpty
end
"#;
    let kb = try_load_kb_with_files(&[DATA, USE]).unwrap_or_else(|errs| {
        panic!("a cross-file namespace-qualified receiver must load; got: {errs:?}")
    });
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register builtins");
    let call = |interp: &mut anthill_core::eval::Interpreter, op: &str| {
        interp
            .call(&format!("test.wi749ns.use.{op}"), &[])
            .unwrap_or_else(|e| panic!("`{op}` must run; got {e:?}"))
            .as_bool()
            .unwrap_or_else(|| panic!("`{op}` must answer a Bool"))
    };
    let inline = call(&mut interp, "inlineCrossFile");
    assert!(!inline, "the cross-file relation matches alice, so it is NOT empty");
    assert_eq!(
        inline,
        call(&mut interp, "letBoundCrossFile"),
        "the 4-segment inline spelling must evaluate like its let-bound twin"
    );
}

/// PRECEDENCE, and the reason the re-routes are three ORDERED passes rather than one
/// widened gate. A rule LABEL may itself be dotted (`rule a.b: …`), which `scan_rule`
/// defines as the joined name — so with rules `a` AND `a.b` both in scope, a proper
/// PREFIX and the WHOLE chain both resolve to rules. The whole-chain CITATION must
/// win: `a.b` is the relation labelled `a.b`, NOT member `b` of relation `a`.
///
/// This is a REGRESSION pin. Probing prefixes before the citation made `let r = a.b`
/// fail with `Relation.b: no such member (dot dispatch)` — and only when the
/// same-source rule `a` was ALSO present, so the citation broke by ACTION AT A
/// DISTANCE from an unrelated declaration.
#[test]
fn wi749_whole_chain_citation_beats_a_rule_prefix() {
    const ONLY_DOTTED: &str = r#"
namespace test.wi749dotted1
  import anthill.prelude.{Int64, Bool}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  rule a.b: r2(?x) :- q(row: ?x)

  operation cite() -> Bool effects Error =
    let r = a.b
    r.isEmpty
end
"#;
    // Identical, but a rule ALSO labelled `a` — a proper prefix of `a.b` — is added.
    const PREFIX_TOO: &str = r#"
namespace test.wi749dotted2
  import anthill.prelude.{Int64, Bool}
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  rule a: r1(?x) :- q(row: ?x)
  rule a.b: r2(?x) :- q(row: ?x)

  operation cite() -> Bool effects Error =
    let r = a.b
    r.isEmpty
end
"#;
    for (src, label) in [(ONLY_DOTTED, "without"), (PREFIX_TOO, "with")] {
        try_load_kb_with(src).unwrap_or_else(|errs| {
            panic!(
                "the citation `a.b` must resolve to the rule labelled `a.b` {label} a \
                 same-named prefix rule in scope; got:\n{}",
                errs.join("\n")
            )
        });
    }
}

/// NO REGRESSION: a LOCAL binder still wins, and this pins the case the ordering
/// actually decides — a local ROOT beating the whole-chain CITATION. With a rule
/// labelled `p.x` in scope, `p.x` on a local `p` must stay the local's FIELD, because
/// the local-root pass runs before `try_qualified_rule_ref`. (The plain 1-segment
/// shadow — a local shadowing a same-named rule — is already pinned by the WI-729
/// suite, which routes through this same field path.)
#[test]
fn wi749_local_root_beats_the_whole_chain_citation() {
    const SRC: &str = r#"
namespace test.wi749shadow
  import anthill.prelude.{Int64, Bool}
  sort Box
    entity box(x: Int64)
  end
  sort Q
    entity q(row: Int64)
  end
  fact q(row: 1)

  -- a rule whose LABEL spells exactly the local field access below.
  rule p.x: rx(?n) :- q(row: ?n)

  operation shadowed() -> Int64 effects Error =
    let p = box(x: 7)
    p.x
end
"#;
    let mut interp = interp_for(SRC);
    let r = interp
        .call("test.wi749shadow.shadowed", &[])
        .expect("the shadowed receiver runs");
    match r {
        Value::Int(n) => assert_eq!(
            n, 7,
            "a local binder's field must win over a rule LABELLED `p.x` — `p.x` is \
             the box's field, not the relation"
        ),
        other => panic!("expected the local box's field, got {other:?}"),
    }
}

/// NO SILENT FALLBACK: a receiver naming neither a local value nor a rule keeps the
/// `field_access` path and its loud unresolved-name diagnostic. Both sources present
/// the widened gate with a genuine NEAR MISS — a rule IS in scope, just not at the
/// name used — so a gate that probed too loosely (any symbol kind, or a short-name /
/// last-segment match) would re-route instead of failing, and be caught here.
#[test]
fn wi749_unresolvable_receiver_stays_loud() {
    const NO_SUCH_MEMBER: &str = r#"
namespace test.wi749loud1
  import anthill.prelude.{Int64, Bool}
  sort Queen
    entity queen(row: Int64)
    rule find(?row) :- queen(row: ?row)
  end
  fact queen(row: 1)
  operation bad() -> Bool effects Error =
    Queen.nosuch.isEmpty
end
"#;
    const NOTHING_IN_SCOPE: &str = r#"
namespace test.wi749loud2
  import anthill.prelude.{Int64, Bool}
  sort Queen
    entity queen(row: Int64)
    rule find(?row) :- queen(row: ?row)
  end
  fact queen(row: 1)
  operation bad() -> Bool effects Error =
    nosuchns.nosuchrule.isEmpty
end
"#;
    for src in [NO_SUCH_MEMBER, NOTHING_IN_SCOPE] {
        let errs = try_load_kb_with(src)
            .err()
            .expect("a receiver naming neither a local nor a rule must NOT load");
        assert!(
            errs.iter().any(|e| e.contains("isEmpty") && e.contains("unresolved")),
            "the miss must stay the loud unresolved-name error, got: {errs:?}"
        );
    }
}

/// A `field_access` carrying NAMED ARGS is not an accessor at all — the converter
/// emits this builtin with an empty `named_args` on both of its paths, so one with
/// them is a user-written call to a functor that merely shares the reserved name.
/// Re-routing it would build a zero-arg `DotApply` and silently DROP those argument
/// subtrees unvisited (they would never be name-resolved or typed), so the whole
/// re-route ladder declines and the ordinary path reports them.
///
/// This does not constrain dot calls: `p.m(a: 1)` is a CALL, and that path threads
/// named args into the `DotApply` frame as `ApplyArg(some(name), value)`. Only the
/// zero-arg accessor shape is at issue here.
#[test]
fn wi749_named_args_on_field_access_are_not_dropped() {
    const SRC: &str = r#"
namespace test.wi749named
  import anthill.prelude.{String, Int64, Bool}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation bad() -> Bool effects Error =
    field_access(person_row, isEmpty, extra: nosuchthing(1, 2, 3))
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("the dropped `extra:` subtree names `nosuchthing` — this must NOT load");
    assert!(
        errs.iter().any(|e| e.contains("nosuchthing")),
        "the named-arg subtree must be VISITED and its unknown functor reported, not \
         discarded by a re-route; got: {errs:?}"
    );
}

/// The gate scans every PREFIX of the receiver, so a member ON a member re-routes
/// level by level exactly as a local-rooted chain (`p.x.y`) does — the routing
/// decision stays uniform instead of falling off a cliff at depth 2.
///
/// This is the POSITIVE pin, and it is what makes the prefix scan load-bearing rather
/// than speculative: `negate` is zero-arg and returns a `Relation`, so
/// `person_row.negate.isEmpty` is a real depth-2 pure-name chain. Probing only the
/// FULL receiver name would not re-route the outer level — `person_row.negate` names
/// no rule — and the member would fall back to the loader's unresolved-name error.
///
/// NOTE the asymmetry with the METHOD-CALL path, which is PRE-EXISTING and deliberate:
/// `person_row.negate.takeN(5)` still fails loudly, because that path SYNTHESIZES its
/// receiver from a single symbol and so has no way to express a chained one — WI-443
/// defers exactly that, and defers it for chained LOCAL receivers (`p.inner.abs()`,
/// pinned in the WI-729 suite) in the same way. This path can chain precisely because
/// it VISITS the receiver instead.
#[test]
fn wi749_chained_member_reroutes_level_by_level() {
    const SRC: &str = r#"
namespace test.wi749chain
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{negate}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  -- depth-2 pure-name chain: a zero-arg member ON a zero-arg member.
  operation chained() -> Bool effects Error =
    person_row.negate.isEmpty

  -- the let-bound reference spelling for that same chain.
  operation letBound() -> Bool effects Error =
    let r = person_row
    let n = r.negate
    n.isEmpty
end
"#;
    try_load_kb_with(SRC).unwrap_or_else(|errs| {
        panic!(
            "`person_row.negate.isEmpty` must re-route at BOTH levels and load, \
             exactly as the let-bound spelling beside it does; got:\n{}",
            errs.join("\n")
        )
    });
}

/// The NEGATIVE half of the same chain: a bad member at depth 2 must be reported by
/// the TYPER's dot dispatch against the inner member's type (`Bool`), NOT by the
/// loader's unresolved-name path — which is what proves both levels really became dot
/// calls rather than the whole thing staying a static name path.
#[test]
fn wi749_chained_bad_member_misses_in_the_typer() {
    const SRC: &str = r#"
namespace test.wi749chainbad
  import anthill.prelude.{String, Int64, Bool}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation bad() -> Bool effects Error =
    person_row.isEmpty.nosuchmember
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("`nosuchmember` names no member of Bool — this must NOT load");
    let joined = errs.join("\n");
    assert!(
        joined.contains("Bool.nosuchmember") && joined.contains("dot dispatch"),
        "the chain must re-route at BOTH levels and miss in the typer's dot dispatch \
         against Bool, not in the loader; got:\n{joined}",
    );
    assert!(
        !joined.contains("expected resolved name"),
        "the loader's unresolved-name error is exactly what WI-749 removed here; \
         got:\n{joined}",
    );
}
