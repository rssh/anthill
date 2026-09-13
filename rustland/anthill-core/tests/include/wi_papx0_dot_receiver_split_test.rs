//! WI-20260824-PAPX0 — the dot-receiver split (proposal 055 umbrella A step 4,
//! `docs/design/055-implementation.md` §4). DECISION: option B, THE DENOTATION
//! DECIDES — a receiver whose type is `Type` and whose denotation is a known
//! sort resolves `.m` in THAT SORT's scope, not among `Type`'s own members.
//!
//! WHAT WAS WRONG. One value, three spellings, two answers, decided by whether
//! the receiver's root happened to be let-bound:
//!
//!   Box.tag()                            -> 7   (loader: the qualified name
//!                                                 resolves whole, rung 1)
//!   Box[V = Int64].tag()                 -> 7   (converter: the object is an
//!                                                 `application`, so a NAME)
//!   let t = Box[V = Int64]; t.tag()      -> REFUSED, "no such member (dot
//!                                          dispatch)" against
//!                                          `anthill.prelude.Type`
//!
//! `sort Type = ?` is an opaque handle declaring no members, so every dispatch
//! rung answered about the wrong sort. And the third spelling is the ONLY one
//! that reaches the typer's `DotApply` frame at all: a syntactically-type
//! receiver arrives as a NAME and bypasses the dot frame entirely, which is why
//! the fix is a binder channel rather than a receiver-node classification.
//!
//! CONTROLS — which rows fail when the change is backed out (drop the
//! `type_denotations` lookup in the `DotApply` frame), and which do not:
//!
//!   FAIL ON BACK-OUT (they are the change):
//!     `a_let_bound_type_receiver_resolves_in_the_denoted_sort`
//!     `the_denoted_sorts_type_arguments_ride_the_call`
//!     `a_missing_member_names_the_denoted_sort_not_type`
//!   PASS EITHER WAY BY DESIGN (they are the fences):
//!     `the_two_name_route_spellings_are_unchanged` — neither ever reached the
//!        dot frame, so this row says the fix did not disturb the routes that
//!        already worked.
//!     `a_shadowing_rebind_drops_the_denotation` — the SOUNDNESS row. It passes
//!        on back-out because without the channel nothing resolves in `Box`
//!        anyway. AND IT DOES NOT DRIVE THE `clear_type_denotation` ARM EITHER:
//!        measured, removing that arm leaves all six rows GREEN. `let t = 1`
//!        mints a FRESH binder symbol (WI-550's shadowing-correct identities),
//!        so the denotation map — keyed by `Symbol` — never collides, and a
//!        lambda binder shadowing a let does not inherit it either (its
//!        receiver types as `<unresolved receiver>`, so the branch never runs).
//!        NOTHING IN THIS SUITE DRIVES THAT ARM. It is kept as the pairing
//!        `clear_receiver_alias` already has, and this row is what would catch
//!        the regression if binder freshness ever changed — but calling it a
//!        control for the clear would credit it with an observation nobody
//!        made.
//!     `a_denotation_lost_through_a_call_still_refuses` — the declared SCOPE
//!        BOUNDARY. Recovering it needs a `Type` that carries its head, which
//!        is a different ticket; this row pins that it is out and stays out.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

const SRC: &str = r#"
namespace test.papx0
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
    operation wrap(x: V) -> V = x
  end

  operation bare_name() -> Int64 = Box.tag()
  operation written_bracket() -> Int64 = Box[V = Int64].tag()

  operation via_binder() -> Int64 =
    let t = Box[V = Int64]
    t.tag()

  operation binder_carries_args() -> Int64 =
    let t = Box[V = Int64]
    t.wrap(5)
end
"#;

fn call_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp
        .call(&format!("test.papx0.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op}: {e:?}"))
    {
        Value::Int(n) => n,
        other => panic!("{op}: expected an Int64, got {other:?}"),
    }
}

/// THE ROW THIS TICKET EXISTS FOR. Before the change this did not merely answer
/// differently — it refused to load.
#[test]
fn a_let_bound_type_receiver_resolves_in_the_denoted_sort() {
    let mut interp = interp_for(SRC);
    assert_eq!(
        call_int(&mut interp, "via_binder"),
        7,
        "`t.tag()` with `t` denoting Box must reach Box's `tag`, not look for a \
         member of the opaque `Type`"
    );
}

/// The denotation is the INSTANTIATION, not just the head: `Box[V = Int64]` and
/// `Box[V = String]` denote different things, and the member's signature must be
/// read at the receiver's bindings. Driven in both directions — the value comes
/// back, AND a wrong-typed argument is refused against `Int64` rather than
/// unifying with a free `V`.
#[test]
fn the_denoted_sorts_type_arguments_ride_the_call() {
    let mut interp = interp_for(SRC);
    assert_eq!(call_int(&mut interp, "binder_carries_args"), 5);

    // The discriminating half: with the bindings dropped, `V` would be free and
    // `"s"` would unify with it. It must be refused at `Int64`.
    let errs = try_load_kb_with(
        r#"
namespace test.papx0bad
  sort Box[V]
    entity mk(v: V)
    operation wrap(x: V) -> V = x
  end
  operation binder_bad() -> Int64 =
    let t = Box[V = Int64]
    t.wrap("s")
end
"#,
    )
    .err()
    .expect("a String argument must be refused at V = Int64");
    let rendered = format!("{errs:?}");
    // THE SITE, NOT JUST THE SUBSTRINGS. Measured: with the bindings dropped the
    // refusal is `binder_bad.return (op-return): expected Int64, got String`, which
    // contains BOTH substrings too — so asserting only those passed in both worlds
    // and measured nothing. Only `wrap.x (op-arg)` says the receiver's `V = Int64`
    // reached the ARGUMENT check.
    assert!(
        rendered.contains("wrap.x") && rendered.contains("op-arg"),
        "the refusal must land on the ARGUMENT, not the return: {rendered}"
    );
    assert!(
        rendered.contains("expected Int64") && rendered.contains("got String"),
        "the receiver's V = Int64 must reach the argument check: {rendered}"
    );
}

/// The denotation is KNOWN and the sort has no such member: the refusal must
/// name the denoted sort. Reporting "no such member of `anthill.prelude.Type`"
/// is a true sentence about the wrong sort and sends the author looking for a
/// member of `Type`.
#[test]
fn a_missing_member_names_the_denoted_sort_not_type() {
    let errs = try_load_kb_with(
        r#"
namespace test.papx0miss
  sort Box[V]
    entity mk(v: V)
  end
  operation gone() -> Int64 =
    let t = Box[V = Int64]
    t.nosuch()
end
"#,
    )
    .err()
    .expect("a missing member must still be refused");
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("Box"),
        "the refusal must name the DENOTED sort: {rendered}"
    );
    assert!(
        !rendered.contains("prelude.Type"),
        "the refusal must NOT name the opaque Type handle: {rendered}"
    );
}

/// FENCE. Both name-route spellings bypass the typer's dot frame entirely, so
/// the change cannot have moved them. Passes either way by design; its job is to
/// say the two routes that already worked still do, at the same values.
///
/// ITS OWN SOURCE, NOT `SRC`, AND THAT IS THE WHOLE POINT. Measured: sharing
/// `SRC` with the arms made this row fail on back-out too -- not because a
/// name-route spelling moved, but because `SRC` also contains `via_binder`,
/// which does not LOAD once the branch is gone, so the KB never builds and
/// `bare_name` cannot be called either. A control that shares a fixture with
/// the thing it controls measures the fixture.
#[test]
fn the_two_name_route_spellings_are_unchanged() {
    let mut interp = interp_for(
        r#"
namespace test.papx0names
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
  end
  operation bare_name() -> Int64 = Box.tag()
  operation written_bracket() -> Int64 = Box[V = Int64].tag()
end
"#,
    );
    for op in ["bare_name", "written_bracket"] {
        let got = interp
            .call(&format!("test.papx0names.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        assert!(
            matches!(got, Value::Int(7)),
            "{op}: the name routes never reach the dot frame and must be untouched,              got {got:?}"
        );
    }
}

/// SOUNDNESS. A shadowing `let` rebinds the name's identity, so the outer
/// denotation must not survive it -- the same hazard `clear_receiver_alias`
/// guards for the alias channel. The inner `t` is an `Int64`, and the dot must
/// dispatch there, never in `Box`.
#[test]
fn a_shadowing_rebind_drops_the_denotation() {
    let errs = try_load_kb_with(
        r#"
namespace test.papx0shadow
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
  end
  operation shadowed() -> Int64 =
    let t = Box[V = Int64]
    let t = 1
    t.tag()
end
"#,
    )
    .err()
    .expect("`tag` is not a member of Int64, so this must refuse");
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("Int64"),
        "the inner binding decides the receiver: {rendered}"
    );
    assert!(
        !rendered.contains("papx0shadow.Box"),
        "the outer denotation must not survive the rebind: {rendered}"
    );
}

/// SCOPE BOUNDARY, pinned so it is a decision rather than a surprise. The
/// denotation is lost through an operation call -- `Type` is opaque and carries
/// no head -- so this stays refused under option B. Recovering it needs a `Type`
/// that carries its instantiation, which is a separate ticket.
#[test]
fn a_denotation_lost_through_a_call_still_refuses() {
    let errs = try_load_kb_with(
        r#"
namespace test.papx0thru
  import anthill.prelude.{Type}
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
  end
  operation id_ty(x: Type) -> Type = x
  operation through_call() -> Int64 =
    let t = id_ty(Box[V = Int64])
    t.tag()
end
"#,
    )
    .err()
    .expect("the denotation does not survive a call under option B");
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("Type"),
        "with no denotation the receiver is the opaque Type, and the refusal says so: \
         {rendered}"
    );
}

/// CONTROL (3) OF THE TICKET — the ambiguity refusal, DRIVEN rather than shipped
/// as an unreachable guard.
///
/// Design §4 closes with "if a surface can name both a companion member and a
/// `Type` member and no existing rule orders them, refuse the ambiguity naming
/// both routes", and §8 repeats it. Under option B that collision needs `Type`
/// to declare a member, and today's stdlib `sort Type = ?` declares none — so
/// the trigger had to be CONSTRUCTED, not found. It is constructible: `Type` is
/// an ordinary sort a program can reopen, and a fixture that adds `tag` to it
/// loads clean.
///
/// MEASURED BEFORE THE GUARD: with `tag` on BOTH `Type` and `Box`, `t.tag()`
/// answered 7 and never mentioned the other route — the lookup-order settlement
/// §4 forbids. FAILS ON BACK-OUT of the two-route lookup (it answers 7 again).
///
/// Both lookups ALWAYS run. That is what separates this from §8's banned
/// fallback, which is retrying one route after the other FAILS; no answer here
/// depends on which question was asked first.
#[test]
fn a_member_on_both_routes_is_refused_naming_both() {
    let errs = try_load_kb_with(
        r#"
namespace anthill.prelude
  sort Type
    -- a genuine member OF THE `Type` VALUE: it takes the receiver, which is
    -- what makes `t.tag()` a second live route beside `Box`'s companion `tag()`.
    operation tag(t: Type) -> Int64 = 99
  end
end

namespace test.papx0ambig
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
  end
  operation both() -> Int64 =
    let t = Box[V = Int64]
    t.tag()
end
"#,
    )
    .err()
    .expect("a member on both routes must be refused, not silently resolved");
    let rendered = format!("{errs:?}");
    // BOTH routes must be named -- asserting only that "some diagnostic mentioning
    // the sort was raised" is what this ticket's control text rules out.
    assert!(
        rendered.contains("Box.tag"),
        "the companion route must be named: {rendered}"
    );
    assert!(
        rendered.contains("Type.tag"),
        "the `Type`-member route must be named: {rendered}"
    );
    assert!(
        rendered.contains("no rule orders them"),
        "the refusal must say WHY it refuses rather than report a miss: {rendered}"
    );
}

/// FENCE for the arm above: a member that exists ONLY on `Type` is not the
/// companion arm's business. It must fall through to the ordinary dispatch --
/// which is already asking about `Type` -- and resolve there, not be swallowed
/// by the two-route check or refused as missing from the denoted sort.
#[test]
fn a_member_only_on_type_still_resolves_by_the_ordinary_route() {
    let mut interp = interp_for(
        r#"
namespace anthill.prelude
  sort Type
    operation only_on_type(t: Type) -> Int64 = 99
  end
end

namespace test.papx0onlytype
  sort Box[V]
    entity mk(v: V)
  end
  operation reach() -> Int64 =
    let t = Box[V = Int64]
    t.only_on_type()
end
"#,
    );
    let got = interp
        .call("test.papx0onlytype.reach", &[])
        .unwrap_or_else(|e| panic!("only_on_type: {e:?}"));
    assert!(
        matches!(got, Value::Int(99)),
        "a `Type`-only member must still reach `Type`'s ordinary dispatch, got {got:?}"
    );
}

/// REGRESSION ROW (/code-review, driven). The first cut of this arm RETURNED
/// unconditionally, which made every rung below it unreachable for a
/// `Type`-typed receiver: `try_fire_dot_rule`, `find_spec_op_for_provided_sort`,
/// the JSFHG parent rung, field access and relation projection. `sort.anthill`
/// declares `fact Eq[T = Type]`, so `t.eq(u)` had WORKED through the spec route
/// and stopped loading — while the same call with the denotation lost still
/// loaded beside it. A new admission is a RUNG, never a gate in front of the
/// ladder.
///
/// FAILS if the arm ever returns unconditionally again.
#[test]
fn a_spec_route_reachable_through_type_is_not_shadowed_by_the_new_rung() {
    let mut interp = interp_for(
        r#"
namespace test.papx0spec
  sort Box[V]
    entity mk(v: V)
  end
  operation same() -> Bool =
    let t = Box[V = Int64]
    let u = Box[V = Int64]
    t.eq(u)
end
"#,
    );
    let got = interp
        .call("test.papx0spec.same", &[])
        .unwrap_or_else(|e| panic!("eq through the Type spec route: {e:?}"));
    assert!(
        matches!(got, Value::Bool(_)),
        "`fact Eq[T = Type]` makes `eq` reachable on a type value; the denoted-sort \
         rung must not shadow it, got {got:?}"
    );
}

/// SOUNDNESS (/code-review, driven). Only a COMPANION member — one that does not
/// take the receiver — may be called with the args unshifted. An INSTANCE member
/// resolved here and synthesized that way silently DROPPED the receiver:
/// `t.combine(p, q)` became `combine(p, q)` and LOADED. Worse than a miss: the
/// same member then behaved oppositely depending only on whether the binder held
/// a type or a value.
#[test]
fn an_instance_member_of_the_denoted_sort_is_not_called_with_the_receiver_dropped() {
    let errs = try_load_kb_with(
        r#"
namespace test.papx0inst
  sort Box[V]
    entity mk(v: V)
    operation combine(a: Box[V], b: Box[V]) -> Int64 = 1
  end
  operation drop_it() -> Int64 =
    let t = Box[V = Int64]
    t.combine(mk(v: 1), mk(v: 2))
end
"#,
    )
    .err()
    .expect("an instance member must not be taken by the companion rung");
    let rendered = format!("{errs:?}");
    assert!(
        rendered.contains("combine"),
        "the refusal should still be about `combine`: {rendered}"
    );
}

/// One alias hop must keep the denotation. `let u = t` records `u -> [t]` in the
/// peer `receiver_aliases` channel; without de-aliasing the read, this restored
/// the VERBATIM pre-fix diagnostic one `let` later.
#[test]
fn an_alias_hop_keeps_the_denotation() {
    let mut interp = interp_for(
        r#"
namespace test.papx0hop
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
  end
  operation hop() -> Int64 =
    let t = Box[V = Int64]
    let u = t
    u.tag()
end
"#,
    );
    let got = interp
        .call("test.papx0hop.hop", &[])
        .unwrap_or_else(|e| panic!("alias hop: {e:?}"));
    assert!(matches!(got, Value::Int(7)), "got {got:?}");
}

/// A POSITIONAL bracket is not admitted by this rung, and the row exists because
/// admitting it was a FALSE ACCEPT rather than a gap: `recv_type` is read
/// downstream by `term_backed_bindings`, which consults named keys only, so
/// `Box[Int64]` arrived with no bindings, `V` went free, and `t.wrap("s")` LOADED
/// where the written `Box[Int64].wrap("s")` correctly refuses. The rung stands
/// down and the ladder answers exactly as it did before.
#[test]
fn a_positional_bracket_is_not_admitted_and_does_not_loosen_the_argument_check() {
    let errs = try_load_kb_with(
        r#"
namespace test.papx0pos
  sort Box[V]
    entity mk(v: V)
    operation wrap(x: V) -> V = x
  end
  operation pos_bad() -> Int64 =
    let t = Box[Int64]
    t.wrap("s")
end
"#,
    )
    .err()
    .expect("a positional denotation must not silently accept a String at V = Int64");
    let rendered = format!("{errs:?}");
    assert!(!rendered.is_empty(), "{rendered}");
}

/// A receiver denoting `Type` ITSELF made both lookups return the SAME symbol, so
/// the ambiguity refusal reported one route as two.
#[test]
fn a_receiver_denoting_type_itself_is_not_reported_as_two_routes() {
    let errs = try_load_kb_with(
        r#"
namespace anthill.prelude
  sort Type
    operation tag(t: Type) -> Int64 = 99
  end
end

namespace test.papx0self
  import anthill.prelude.{Type}
  operation selfish() -> Int64 =
    let t = Type
    t.tag()
end
"#,
    );
    if let Err(e) = errs {
        let rendered = format!("{e:?}");
        assert!(
            !rendered.contains("names BOTH"),
            "one route must not be reported as two: {rendered}"
        );
    }
}
