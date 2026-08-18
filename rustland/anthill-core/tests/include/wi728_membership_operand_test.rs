//! WI-728 (proposal 052, follow-up to WI-714) — `negate`'s MEMBERSHIP-relation operand is
//! enforced at LOAD, not only at runtime.
//!
//! `negate(r)` builds `negation(query: r.query)`, which the resolver lowers to NAF. NAF over
//! a relation with a FREE column FLOUNDERS (`not p(?x)` with `?x` unbound is undecidable), so
//! the operand must be a MEMBERSHIP relation — zero columns, which is `T = Unit` after the
//! schema 1-collapse. Until this ticket that requirement lived ONLY in the host builtin, so
//! `negate(person_name)` type-checked and blew up when the stream was pulled.
//!
//! The fix is a type-level PREDICATE in the signature, not a check keyed on `negate`:
//!
//!     operation negate(r: Relation) -> Relation[T = Membership[T = r.T], E = r.E]
//!
//! `Membership[T]` joins `Concat` / `Without` / `Project` / `FieldOf` as a member of the
//! type-constructor family, reducing at the same return-type normalization boundary — it
//! accepts `Unit` and raises on any other schema. It is the family's first UNARY member and
//! its first PREDICATE one (it computes nothing; it asserts).
//!
//! TWO REVIEW FINDINGS ABOUT THE FAMILY, not about `negate`, land here — one repaired, one
//! deliberately not:
//!   * REPAIRED: an un-discharged projection operand was read as a CONCRETE schema, which
//!     refused a legal wrapper with a fabricated column
//!     (`a_wrapper_with_a_bare_relation_parameter_still_loads`).
//!   * NOT REPAIRED, BY DECISION: the boundary reduces in ONE pass, so `TYPE_CTORS`'s array
//!     ORDER decides which nested ctor gets stranded. A fixpoint was written and measured —
//!     it works, and it fails exactly one test in the workspace:
//!     `wi776_one_collapse_diagnostic_test::concat_over_a_collapsed_without_still_stalls`,
//!     whose stated purpose is to fail if anyone makes this reduce so the decision gets
//!     re-read. Re-read: kernel-language.md §"1-collapse" records it as a weighed and
//!     DECLINED limit of the paired type-and-value collapse. So the order stands, and what
//!     this ticket owes it is the placement rule it implies —
//!     `a_predicate_over_another_ctors_result_still_reduces` checks that `Membership` sits
//!     where a predicate cannot be the stranded one.
//!
//! THE CONTROL, MEASURED (not predicted) — three back-outs, because the change has
//! separable halves and they answer different questions. Counts below are over the tests
//! that existed when each was measured; the two family repairs carry their own controls at
//! their sites, since backing out `Membership` does not back either of them out.
//!
//!   1. UNREGISTER THE REDUCER — drop `&MEMBERSHIP_CTOR` from `TYPE_CTORS`, leaving the sort
//!      and every signature intact. This is the sharpest control and the likeliest real
//!      regression: the sort still resolves, so nothing fails to parse; the reduction simply
//!      stops running. Measured 4 passed / 4 failed —
//!      `negate_of_a_one_column_relation_is_a_load_error`,
//!      `negate_of_a_two_column_relation_names_its_columns`,
//!      `membership_is_general_not_keyed_on_negate` and
//!      `a_deferred_assertion_reduces_once_the_schema_grounds`.
//!   2. Restore `negate`'s OLD return (`-> Relation[T = Unit, E = r.E]`), leaving the ctor
//!      registered. Measured 3 passed / 2 failed (of the 5 tests that existed then): the two
//!      `negate_of_a_*_relation` tests flip to a CLEAN load — exactly what the old wi714 test
//!      asserted (it loaded, then failed at the call).
//!   3. Also delete the `Membership` sort and its import. Measured 2 passed / 3 failed:
//!      `membership_is_general_not_keyed_on_negate` joins them, though for the weaker reason
//!      that its fixture's `import` line no longer resolves — which is why control 1 exists.
//!
//! WHAT PASSES EITHER WAY, BY DESIGN (measured under control 1, the one that leaves every
//! fixture loadable):
//!   * `membership_operand_still_loads_and_runs` — the accepted path; it pins that the new
//!     assertion does not refuse what NAF can actually decide, a claim about what did NOT
//!     change.
//!   * `abstract_schema_defers_to_the_runtime_guard` — the escape is the WI-734
//!     abstract-operand rule plus the family's declared-return gate, and the runtime guard
//!     it falls through to predates this ticket. It is here to pin that the runtime guard is
//!     still REACHABLE, so removing it would be a real loss rather than dead-code cleanup.
//!     On its own it cannot tell "the assertion deferred" from "the assertion never ran" —
//!     both end in a clean load and a runtime refusal — so
//!     `a_deferred_assertion_reduces_once_the_schema_grounds` is its discriminator.
//!   * `a_wrapper_with_a_bare_relation_parameter_still_loads` — a REGRESSION test, so it
//!     passes before WI-728 and after the fix and fails only in between; its own control is
//!     stated at its site (remove the projection arm from `operand_not_yet_known`).
//!   * `a_unit_typed_column_is_indistinguishable_from_no_columns` — a recorded LIMIT of the
//!     1-collapse, not a behaviour this ticket introduced or could remove.
//!   * `a_predicate_over_another_ctors_result_still_reduces` — a FAMILY property, not a
//!     `Membership` behaviour; its control is moving `&MEMBERSHIP_CTOR` earlier in
//!     `TYPE_CTORS`, stated at its site.

use crate::common::{interp_for, try_load_kb_with};

/// A relation with ONE free column (`person_name : Relation[String]`) is not a membership
/// relation, so negating it would flounder. That is now refused at LOAD.
///
/// The 1-collapse has already dropped the column's NAME by the time the schema reaches type
/// position (§"1-collapse"), so the message names the column's TYPE — the one thing the
/// load-time check cannot recover that the runtime guard, reading the value's own `columns`
/// list, can.
#[test]
fn wi728_negate_of_a_one_column_relation_is_a_load_error() {
    let src = r#"
namespace test.wi728one
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{negate}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  -- one free head variable → Relation[(name: String)]: a column, not a membership relation
  rule person_name(?name) :- person(name: ?name, age: ?)

  operation bad() -> Bool effects Error =
    let r = negate(person_name)
    r.isEmpty
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_else(|| {
        panic!("negate over a relation with a free column must be a LOAD error, not a clean load")
    });
    let joined = errs.join("\n");
    assert!(
        joined.contains("Membership") && joined.contains("free column(s): name"),
        "the load error must NAME the offending column — WI-20260818-YQB1Y dropped the \
         1-collapse, so a one-column schema spells its column and the message no longer has \
         to fall back to naming the column's TYPE; got: {joined}"
    );
    assert!(
        joined.contains("close the columns first"),
        "the load error must point at the remedy, got: {joined}"
    );
}

/// A relation with TWO free columns still SPELLS them (no 1-collapse), so the message names
/// the columns themselves — the named-tuple arm of the diagnostic.
#[test]
fn wi728_negate_of_a_two_column_relation_names_its_columns() {
    let src = r#"
namespace test.wi728two
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{negate}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  -- two free head variables → Relation[(name: String, age: Int64)]
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  operation bad() -> Bool effects Error =
    let r = negate(person_row)
    r.isEmpty
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("negate over a two-column relation must be a LOAD error"));
    let joined = errs.join("\n");
    assert!(
        joined.contains("free column(s): name, age"),
        "the load error must name both offending columns, got: {joined}"
    );
}

/// The ACCEPTED path, DRIVEN rather than merely loaded: a 0-column (membership) relation
/// still types AND runs. `has_zed` has no solution, so NAF succeeds and the negation is
/// non-empty — the assertion reduces `Membership[T = Unit]` to `Unit` and gets out of the way.
#[test]
fn wi728_membership_operand_still_loads_and_runs() {
    let src = r#"
namespace test.wi728ok
  import anthill.prelude.{String, Int64, Bool, Option, Unit}
  import anthill.prelude.Relation.{negate}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  -- zero free head variables → Relation[Unit]: a membership relation
  rule has_zed() :- person(name: "zed", age: ?)
  rule has_alice() :- person(name: "alice", age: ?)

  operation negateEmptyIsEmpty() -> Bool effects Error =
    let r = negate(has_zed)
    r.isEmpty

  operation negateProvableIsEmpty() -> Bool effects Error =
    let r = negate(has_alice)
    r.isEmpty
end
"#;
    let mut interp = interp_for(src);
    let empty_operand = interp
        .call("test.wi728ok.negateEmptyIsEmpty", &[])
        .expect("negate(has_zed).isEmpty");
    assert_eq!(
        empty_operand.as_bool(),
        Some(false),
        "negate of an UNPROVABLE membership relation is non-empty (NAF succeeds)"
    );
    let provable_operand = interp
        .call("test.wi728ok.negateProvableIsEmpty", &[])
        .expect("negate(has_alice).isEmpty");
    assert_eq!(
        provable_operand.as_bool(),
        Some(true),
        "negate of a PROVABLE membership relation is empty (NAF fails)"
    );
}

/// `Membership` is a member of the type-constructor FAMILY, keyed on its own sort symbol —
/// nothing in the typer knows what `negate` is. Both halves are over a user's OWN sort, with
/// no `Relation` anywhere: the closed schema reduces and loads clean, the open one is the
/// same loud error.
///
/// BOTH HALVES PIN THE REDUCTION, not merely the sort's existence (review-found). The
/// accepted half asserts the REDUCED type is visible to a downstream consumer — `useClosed`
/// returns `Slot[T = Unit]`, which only type-checks if `Membership[T = Unit]` actually became
/// `Unit`; an unreduced residual is refused there, so "it loaded" is evidence the reduction
/// fired. The refused half pins a phrase only `membership_schema_type` emits: an UNREDUCED
/// ctor prints WITH its operand, so a `Membership`-and-`Int64` assertion would also pass on
/// the reduction being unregistered entirely — the likelier regression than deleting the sort.
#[test]
fn wi728_membership_is_general_not_keyed_on_negate() {
    let accepted = r#"
namespace test.wi728genok
  import anthill.prelude.{Unit, Membership}

  sort Slot
    sort T = ?
    entity slot(value: T)
    operation close(s: Slot) -> Slot[T = Membership[T = s.T]]
  end

  -- The declared return is the REDUCED `Unit`, so this conforms only if the reduction ran.
  operation useClosed(s: Slot[T = Unit]) -> Slot[T = Unit] = Slot.close(s)
end
"#;
    try_load_kb_with(accepted).unwrap_or_else(|errs| {
        panic!("a CLOSED schema must reduce through `Membership` on any sort, got: {errs:#?}")
    });

    let refused = r#"
namespace test.wi728genbad
  import anthill.prelude.{Unit, Int64, Membership}

  sort Slot
    sort T = ?
    entity slot(value: T)
    operation close(s: Slot) -> Slot[T = Membership[T = s.T]]
  end

  operation useOpen(s: Slot[T = Int64]) -> Slot[T = Unit] = Slot.close(s)
end
"#;
    let errs = try_load_kb_with(refused)
        .err()
        .unwrap_or_else(|| panic!("`Membership` over a non-`Unit` schema must be a LOAD error"));
    let joined = errs.join("\n");
    assert!(
        joined.contains("requires a CLOSED schema") && joined.contains("Int64"),
        "the refusal must be the REDUCTION's own, naming the offending operand, got: {joined}"
    );
}

/// REGRESSION (review-found, measured): a wrapper whose parameter is written BARE — exactly
/// how `negate` itself writes it, to keep `E` open — still loads.
///
/// Inside such a wrapper there is no receiver type to project `r.T` against, so the
/// projection survives elimination and reaches the ctor un-discharged. The first cut read
/// that as a CONCRETE schema and refused the program with a fabricated column ("one free
/// column of type `r.T`"). It is case 3 of [`operand_not_yet_known`]: not yet known, so the
/// ctor stays symbolic. `Membership` is where this became reachable — every binary member
/// has a second operand that is usually still a variable, which deferred the whole ctor
/// before its projection operand was ever inspected.
///
/// CONTROL: this fails with the projection arm removed from `operand_not_yet_known`, and
/// loads clean both before WI-728 and after the fix.
#[test]
fn wi728_a_wrapper_with_a_bare_relation_parameter_still_loads() {
    let src = r#"
namespace test.wi728bare
  import anthill.prelude.{String, Int64, Bool, Relation}
  import anthill.prelude.Relation.{negate}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule has_zed() :- person(name: "zed", age: ?)

  -- `r.T` cannot be discharged here: the parameter names no schema to project.
  operation once(r: Relation) -> Relation effects Error = negate(r)

  operation useIt() -> Bool effects Error =
    let r = once(has_zed)
    r.isEmpty
end
"#;
    let mut interp = interp_for(src);
    let v = interp
        .call("test.wi728bare.useIt", &[])
        .expect("a bare-parameter wrapper must load AND run");
    assert_eq!(
        v.as_bool(),
        Some(false),
        "negate of an unprovable membership relation is non-empty, through a bare wrapper"
    );
}

/// WI-728'S KNOWN LIMIT, RETIRED (WI-20260818-YQB1Y) — rewritten rather than patched, which
/// is what its own note asked for ("if it now does, the 1-collapse changed and this recorded
/// limit should be retired").
///
/// A ONE-column relation whose column type IS `Unit` used to 1-collapse to exactly the `Unit`
/// a ZERO-column relation presents, so `Membership` ACCEPTED it at load and only the drain's
/// runtime guard refused it. No type-level predicate could separate the two, because at type
/// level they were the same value.
///
/// Dropping the collapse separates them for free, without touching the `()`-vs-`Unit` typing
/// gap: a zero-column schema is still `Unit`, and a one-`Unit`-column one is `(t: Unit)` — a
/// named tuple with one free column, refused by `Membership`'s ordinary arm.
///
/// CONTROL: this FAILS on a back-out — the program loads clean on the pre-change tree, which
/// is precisely what the retired limit recorded.
#[test]
fn wi728_a_unit_typed_column_is_distinguishable_from_no_columns() {
    let src = r#"
namespace test.wi728unitcol
  import anthill.prelude.{String, Bool, Unit}
  import anthill.prelude.Relation.{negate}

  sort Person
    entity person(name: String, tag: Unit)
  end
  fact person(name: "alice", tag: unit())

  -- ONE free column, of type Unit → the schema is `(t: Unit)`, which a ZERO-column
  -- relation's `Unit` is not. The type tells them apart.
  rule person_tag(?t) :- person(name: ?, tag: ?t)

  operation caught() -> Bool effects Error =
    let r = negate(person_tag)
    r.isEmpty
end
"#;
    let errs = try_load_kb_with(src)
        .err()
        .expect("a one-`Unit`-column relation must be refused at LOAD, not only at the drain");
    let joined = errs.join("\n");
    assert!(
        joined.contains("Membership") && joined.contains("free column(s): t"),
        "the LOAD error names the column, where this used to slip through to the runtime \
         guard; got: {joined}"
    );
}

/// The WI-734 abstract-operand rule, for the family's first UNARY member: a schema that is
/// NOT YET KNOWN leaves `Membership` symbolic rather than raising, so a generic wrapper over
/// `negate` is expressible.
///
/// And the residual ESCAPES when the wrapper widens its own return to a bare `Relation`
/// (the family's declared-return gate — `return_reducible_ctors` reads the DECLARED return,
/// so a signature that does not propagate the ctor never re-reduces it). That escape is
/// exactly why the host builtin's runtime guard stays: it reads the VALUE's own `columns`
/// list, a population no type sees. Both halves are driven here.
#[test]
fn wi728_abstract_schema_defers_to_the_runtime_guard() {
    let src = r#"
namespace test.wi728abs
  import anthill.prelude.{String, Int64, Bool, Relation}
  import anthill.prelude.Relation.{negate}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule person_name(?name) :- person(name: ?name, age: ?)
  rule has_zed() :- person(name: "zed", age: ?)

  -- `S` is abstract here, so `Membership[T = S]` stays SYMBOLIC (it may ground at a call).
  -- The bare `Relation` return then lets the residual escape unreduced.
  operation wrapNegate[S](r: Relation[T = S]) -> Relation effects Error = negate(r)

  operation closedThroughWrapper() -> Bool effects Error =
    let r = wrapNegate(has_zed)
    r.isEmpty

  operation openThroughWrapper() -> Bool effects Error =
    let r = wrapNegate(person_name)
    r.isEmpty
end
"#;
    // The generic wrapper LOADS — the assertion is deferred, not raised against `S`.
    let mut interp = interp_for(src);
    // A membership operand still runs through the wrapper.
    let closed = interp
        .call("test.wi728abs.closedThroughWrapper", &[])
        .expect("wrapNegate(has_zed).isEmpty");
    assert_eq!(
        closed.as_bool(),
        Some(false),
        "negate of an unprovable membership relation is non-empty, wrapper or not"
    );
    // A free-column operand escaped the load-time check, so the RUNTIME guard catches it.
    let mut interp = interp_for(src);
    let err = interp
        .call("test.wi728abs.openThroughWrapper", &[])
        .expect_err("a free-column operand that escaped the type check must still be refused");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("membership") || msg.contains("free column") || msg.contains("flounder"),
        "the runtime guard must still refuse a non-membership operand, got: {msg}"
    );
}

/// The other half of the WI-734 abstract-operand rule, and the DISCRIMINATOR for the test
/// above: a deferred assertion is deferred, not DISCARDED. The same generic wrapper, with
/// its own return PROPAGATING the ctor (`-> Relation[T = Membership[T = S]]`, as `join` /
/// `fix` propagate `Concat` / `Without`), re-reduces at the concrete call — so the free-column
/// operand is caught at LOAD after all, one level out.
///
/// Without this the sibling test is consistent with two different stories — "the assertion
/// deferred" and "the assertion never ran" — and could not tell them apart, since both end
/// in a clean load and a runtime refusal. This one can: it loads clean at the MEMBERSHIP call
/// and raises at the free-column one, which only a residual that survived and then reduced
/// can produce.
#[test]
fn wi728_a_deferred_assertion_reduces_once_the_schema_grounds() {
    let program = |call: &str| {
        format!(
            r#"
namespace test.wi728defer
  import anthill.prelude.{{String, Int64, Bool, Relation, Membership}}
  import anthill.prelude.Relation.{{negate}}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)

  rule person_name(?name) :- person(name: ?name, age: ?)
  rule has_zed() :- person(name: "zed", age: ?)

  -- PROPAGATES the ctor, so the residual re-reduces at each concrete call.
  operation wrapNegate[S](r: Relation[T = S]) -> Relation[T = Membership[T = S]] effects Error =
    negate(r)

  operation useIt() -> Bool effects Error =
    let r = wrapNegate({call})
    r.isEmpty
end
"#
        )
    };
    // The wrapper itself types against the ABSTRACT `S` — so it loads, and its membership
    // call reduces to `Unit` and runs.
    let mut interp = interp_for(&program("has_zed"));
    let closed = interp
        .call("test.wi728defer.useIt", &[])
        .expect("a propagating wrapper over a membership relation still runs");
    assert_eq!(
        closed.as_bool(),
        Some(false),
        "negate of an unprovable membership relation is non-empty, through a propagating wrapper"
    );
    // The same wrapper over a FREE-COLUMN relation: `S` grounds to `String` at the call, the
    // residual reduces there, and the assertion fires — at LOAD, not at the drain.
    let errs = try_load_kb_with(&program("person_name"))
        .err()
        .unwrap_or_else(|| panic!("a residual that grounds to a free-column schema must RAISE"));
    let joined = errs.join("\n");
    assert!(
        joined.contains("Membership") && joined.contains("close the columns first"),
        "the deferred assertion must fire once `S` grounds, got: {joined}"
    );
}

/// THE FAMILY'S ARRAY ORDER IS LOAD-BEARING, and `Membership` is LAST because of it
/// (review-found, measured).
///
/// `reduce_type_ctor` treats a sibling family member as an operand that is NOT YET KNOWN, so
/// an outer ctor DEFERS on it. The boundary makes ONE pass in `TYPE_CTORS` order, so a
/// sibling sitting LATER reduces afterwards and the outer ctor is never revisited. For a
/// COMPUTING member that stranding is caught downstream — an unreduced ctor offers no schema,
/// so any use of the result fails loudly, which `wi776_one_collapse_diagnostic_test::concat_-
/// over_a_collapsed_without_still_stalls` pins deliberately (a weighed and declined limit,
/// kernel-language.md §"1-collapse"). For a PREDICATE it would NOT be caught: a stranded
/// predicate leaves a perfectly usable type and simply loses its assertion.
///
/// So the placement is the guard, and this test is what makes it a checked property rather
/// than a comment: a `Membership` whose operand is another family member still reduces,
/// because every member that can appear inside it runs first.
///
/// CONTROL, MEASURED — and not where predicted, which is the point of measuring. Moving
/// `&MEMBERSHIP_CTOR` ahead of `&WITHOUT_CTOR` in `TYPE_CTORS` fails the ACCEPTED half, not
/// the refused one: the predicate never reduces, so the residual `Membership[T =
/// Without[…]]` no longer matches the declared `Slot[T = Unit]` and a CORRECT program is
/// refused. The assertion is skipped in both halves either way; whether the skip is NOTICED
/// depends on whether anything downstream compares against the reduced form. That is exactly
/// why the placement is a rule stated at `TYPE_CTORS` rather than something to rely on
/// being caught — here a declared return catches it, and at `negate`'s own use site, where
/// the result is just consumed as a stream, nothing would.
#[test]
fn wi728_a_predicate_over_another_ctors_result_still_reduces() {
    // `Without` drops both columns, so its residual is `Unit` — which `Membership` accepts.
    let accepted = r#"
namespace test.wi728orderok
  import anthill.prelude.{Int64, String, Bool, Unit, Without, Membership}
  sort Slot
    sort T = ?
    entity slot(value: T)
    operation closeAll[D](s: Slot, ...d: D)
      -> Slot[T = Membership[T = Without[T = s.T, Drop = D]]]
  end

  -- Declaring the REDUCED `Unit` conforms only if BOTH reductions ran, in order.
  operation useIt(s: Slot[T = (a: Int64, b: String)]) -> Slot[T = Unit] =
    Slot.closeAll(s, a: 1, b: "x")
end
"#;
    try_load_kb_with(accepted).unwrap_or_else(|errs| {
        panic!(
            "a predicate over another ctor's result must reduce — `Membership` runs after \
             every member that can appear in its operand; got: {errs:#?}"
        )
    });

    // The same shape where the inner drop leaves a column: the assertion must FIRE, which it
    // can only do if it saw the reduced operand rather than a residual.
    let refused = accepted
        .replace("test.wi728orderok", "test.wi728orderbad")
        .replace(r#"Slot.closeAll(s, a: 1, b: "x")"#, "Slot.closeAll(s, a: 1)");
    let errs = try_load_kb_with(&refused).err().unwrap_or_else(|| {
        panic!("a residual with a column left must be REFUSED by the predicate, not accepted")
    });
    assert!(
        errs.join("\n").contains("requires a CLOSED schema"),
        "the refusal must be the predicate's own, got: {errs:#?}"
    );
}
