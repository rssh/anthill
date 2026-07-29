//! WI-841 (proposal 058 §4.2 / §4.4 / §4.5 / §9 phase 2) — SELECT: a call-site
//! bracket binds a REQUIREMENT SLOT, so a use site can name the provider it wants.
//!
//! WHAT PHASE 0 AND 1 LEFT. WI-839 made every written bracket key either read or
//! REPORTED; WI-840 gave a slot a NAME and made that name a type parameter. Neither
//! made a key SELECT anything, and rule (1) did not even span the enclosing sort:
//! MEASURED before this ticket, `Box.mk[T = String](5)` on `sort Box { sort T = ? }`
//! was `unknown type-param 'T'`, so §5.3's construction-site selection had nothing to
//! stand on. Four pieces landed: the sort-level seeding rung, key→slot resolution,
//! witness validation, and `resolve`'s step 0.
//!
//! THE PIN IS OBSERVABLE IN A VALUE, which is more than §9 phase 2 asks for. The
//! ticket expects only that a bogus witness go loud, on the grounds that AddM and MulM
//! cannot coexist until phase 3b. But two providers whose DISPATCH CARRIERS differ
//! coexist today — a ground `fact Monoid[T = Int64]` beside a parametric `fact
//! Monoid[T = E]` — and unpinned, `pick_most_specific` takes the ground one. So one
//! program computes 5 or 99 by its bracket key alone, with the bracket-less control
//! measuring what the search picks
//! (`selection_overrides_the_search_and_the_value_shows_it`). That is tier 1 beating
//! tier 2 in a value, not merely in a diagnostic.
//!
//! FOUR SILENT DROPS WERE FOUND BY DRIVING, all of them "the pin named a provider and
//! nothing used it", and each is pinned below by a test that FAILED before its fix:
//!   * a witness providing the spec at OTHER bindings was refused on the spec-op
//!     route, LOADED CLEAN and died `Internal(… __req_monoid not bound …)` at eval on
//!     the dictionary route, and was silently IGNORED on the value-directed one. Fixed
//!     at the SITE (`check_selection_bindings`), so one check answers all three —
//!     enumerating the consumers is what WI-839's own review had to undo;
//!   * an OP-SCOPED `requires` clause decoded to a goal with NO BINDINGS, which every
//!     provider matches, so the site check passed vacuously on that route until it got
//!     the reader its shape needs (`goal_from_op_requires_entry`);
//!   * a pinned dep that failed to project fell back to `Ok(None)` — "no dictionary,
//!     carry on" — which is a defensible answer to a requirement nobody spoke about
//!     and no answer at all to one the author named a provider for.
//!
//! Reference: docs/proposals/058-modular-instances.md §4.2, §4.4, §4.5, §9 phase 2.

use anthill_core::eval::Value;

/// One spec with a WITNESS-sort provider (no constructors — §4.4 check 3 refuses a
/// concrete one), a second spec so a wrong-spec witness is expressible, and a sort
/// that provides nothing. `combine` returns Int64 rather than `T` so every program
/// below can read its answer as a number.
const SPECS: &str = r#"
  sort Monoid
    sort T = ?
    operation combine(a: T, b: T) -> Int64
  end
  sort AddM
    fact Monoid[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = add(a, b)
  end
  sort Marker
    sort M = ?
    operation tag(x: M) -> Int64
  end
  sort NoProv
  end
"#;

/// A second Monoid provider at a DIFFERENT dispatch carrier (a type parameter), so
/// the two coexist under today's coherence rule while both answer a concrete
/// `Monoid[T = Int64]` goal. Its answer is 99, distinguishable from AddM's `add`.
const PARAMETRIC_RIVAL: &str = r#"
  sort AnyM
    sort E = ?
    fact Monoid[T = E]
    operation combine(a: E, b: E) -> Int64 = 99
  end
"#;

/// A provider of the SAME spec at OTHER bindings — it passes the base-level "does W
/// provide Monoid" check and can only be caught by a binding-precise one.
const OTHER_BINDINGS: &str = r#"
  sort StrM
    fact Monoid[T = String]
    operation combine(a: String, b: String) -> Int64 = 7
  end
"#;

fn program(ns: &str, extra: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  import anthill.prelude.{{Int64, Bool, String}}\n\
         {SPECS}{extra}{body}\nend\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

fn refused_with(src: &str, needle: &str, why: &str) {
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{why}; expected a diagnostic containing {needle:?}, got: {errs:?}",
    );
}

fn loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got load errors: {errs:?}");
    }
}

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one. The load doubles as the clean-load gate (`interp_for` panics on a
/// dirty load), so a value assertion also asserts the program loads.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    match eval_fresh(src, entry) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

// ── Positive controls ────────────────────────────────────────────────

/// The harness reports breakage: a program with an unknown sort must fail to load,
/// so every `loads_clean` below is a real assertion rather than a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    let src = program(
        "wi841.control",
        "",
        "  sort Holder\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    );
    assert!(!load_errs(&src).is_empty());
}

// ── Piece 1: rule (1)'s SORT-LEVEL seeding rung (§2.2 rows 5-6) ──────

/// §9 phase 2's first acceptance, verbatim: `Box.mk[T = String](5)` fails at the
/// ARGUMENT, not at the return.
///
/// The distinction is the whole rung. Before WI-839 this program errored at the
/// RETURN (`expected Box[T = String], got Box[T = Int64]`) — `T` had been inferred
/// from the argument and the binding contributed NOTHING; after WI-839 it was
/// `unknown type-param 'T'`, heard but still unbindable. Now the binding lands first
/// and the argument is checked against it, which is what a type argument means.
#[test]
fn a_call_bracket_binds_the_enclosing_sorts_type_param() {
    let src = program(
        "wi841.sortlevel",
        "",
        r#"  sort Box
    sort T = ?
    entity box(v: T)
    operation mk(v: T) -> Box[T = T] = box(v: v)
  end
  sort Use
    operation go(n: Int64) -> Box[T = String] = Box.mk[T = String](5)
  end"#,
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("mk.v") && e.contains("expected String, got Int64")),
        "the bracket must PIN `T = String` so the argument `5` is the mismatch; got: {errs:?}",
    );
    assert!(
        !errs.iter().any(|e| e.contains("go.return") || e.contains("unknown type-param")),
        "and neither the RETURN (the pre-WI-839 report, where the binding meant nothing) \
         nor `unknown type-param` (the post-WI-839 one, where it was merely heard) may \
         still be what this program says; got: {errs:?}",
    );
}

/// The same binding AGREEING loads and runs — the rung binds, it does not merely
/// reject. Without this, the test above would pass on an implementation that refused
/// every sort-level key.
#[test]
fn an_agreeing_sort_level_binding_loads_and_runs() {
    let src = program(
        "wi841.sortlevelok",
        "",
        r#"  sort Box
    sort T = ?
    entity box(v: T)
    operation mk(v: T) -> Box[T = T] = box(v: v)
    operation peek(b: Box[T = Int64]) -> Int64 = b.v
  end
  sort Use
    operation go(n: Int64) -> Int64 = Box.peek(Box.mk[T = Int64](5))
  end"#,
    );
    assert_eq!(eval_int(&src, "wi841.sortlevelok.Use.go", "an agreeing bracket must run"), 5);
}

/// An UNMATCHED key on the same callee stays the WI-839 diagnostic: widening rule (1)
/// to a second scope must not turn "no such parameter" into a silent accept.
#[test]
fn an_unknown_key_on_a_sort_level_callee_is_still_loud() {
    let src = program(
        "wi841.sortlevelbogus",
        "",
        r#"  sort Box
    sort T = ?
    entity box(v: T)
    operation mk(v: T) -> Box[T = T] = box(v: v)
  end
  sort Use
    operation go(n: Int64) -> Box[T = Int64] = Box.mk[Bogus = String](5)
  end"#,
    );
    refused_with(&src, "unknown type-param 'Bogus'", "an unmatched key names no slot");
}

// ── Piece 2: key → slot, and the value it selects ────────────────────

const HOLDER_SORT_LEVEL: &str = r#"  sort Holder
    sort HT = ?
    requires Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 = Monoid.combine(a, b)
  end
"#;

fn driver(call: &str) -> String {
    format!("  sort Driver\n    operation go(n: Int64) -> Int64 = {call}\n  end")
}

/// §9 phase 2's second acceptance, and MORE than it asks: the pin does not merely
/// agree with the search, it OVERRIDES it, and the override is a different number.
///
/// `AddM` (ground `Monoid[T = Int64]`) and `AnyM` (parametric `Monoid[T = E]`)
/// coexist because their DISPATCH CARRIERS differ, and both answer the concrete goal;
/// unpinned, `pick_most_specific` takes the ground one. So the three rows below are
/// one program read three ways — and the bracket-less control is what makes the two
/// pinned rows mean something, by measuring what tier 2 would have said.
#[test]
fn selection_overrides_the_search_and_the_value_shows_it() {
    let build = |call: &str| {
        program("wi841.override", PARAMETRIC_RIVAL, &format!("{HOLDER_SORT_LEVEL}{}", driver(call)))
    };
    let searched = build("Holder.probe(2, 3)");
    let pinned_add = build("Holder.probe[Monoid = AddM](2, 3)");
    let pinned_any = build("Holder.probe[Monoid = AnyM](2, 3)");

    assert_eq!(
        eval_int(&searched, "wi841.override.Driver.go", "tier 2 picks the most specific"),
        5,
        "CONTROL: with no bracket the search takes the GROUND provider",
    );
    assert_eq!(
        eval_int(&pinned_add, "wi841.override.Driver.go", "pinning the search's own answer"),
        5,
    );
    assert_eq!(
        eval_int(&pinned_any, "wi841.override.Driver.go", "pinning the LESS specific one"),
        99,
        "tier 1 outranks tier 2: `[Monoid = AnyM]` selects the provider the search \
         would not have chosen, and the answer changes with it",
    );
}

/// TWO DIFFERENTLY-PINNED CALLS ON ONE GOAL, IN ONE PROGRAM — §1's driver, as far as
/// phase 2 can carry it (`AddM` beside `MulM` on ONE carrier still waits for phase 3b;
/// these two coexist because their dispatch carriers differ).
///
/// Written as DIRECT SPEC-OP calls on purpose. That is the route through
/// `dispatch_spec_op_cached`, the one memoized on `resolve_cache` — and the two calls
/// share their whole memo key (same op, same goal, same scope, same σ regime) except
/// the SELECTION, so this is the only shape in which the selection's presence IN THE
/// KEY decides anything. Measured: the sort-level twin of this test stays green when
/// the selection is dropped from the key, because a Direct call's dictionary is built
/// by `build_concrete_dispatch_dict`, which that memo does not serve.
#[test]
fn two_calls_pinning_different_witnesses_do_not_share_a_memo_entry() {
    let src = program(
        "wi841.twopins",
        PARAMETRIC_RIVAL,
        r#"  sort Driver
    operation added(n: Int64) -> Int64 = Monoid.combine[Monoid = AddM](2, 3)
    operation anyed(n: Int64) -> Int64 = Monoid.combine[Monoid = AnyM](2, 3)
    operation go(n: Int64) -> Int64 = add(mul(1000, Driver.added(n)), Driver.anyed(n))
  end"#,
    );
    assert_eq!(
        eval_int(&src, "wi841.twopins.Driver.go", "two pins in one program"),
        5099,
        "1000·5 + 99: the two calls share a goal, a scope and an op, so only the \
         SELECTION distinguishes them — one answer twice means the memo collided",
    );
}

/// EXPLICIT BEATS DEFERRED, not just searched. Inside a body whose own sort
/// `requires Monoid[T = HT]`, an unbracketed `Monoid.combine` DEFERS — the enclosing
/// frame's dictionary answers it, and the caller filled that frame from the search.
/// A bracket at the same site must outrank that (§4.1 tier 1): the deferral is a
/// forward, and a forward is what the pin is instead of.
///
/// The control is the same body without the bracket, which measures what the
/// deferral hands down. Without the gate the two rows read alike, since the pin is
/// swallowed before any resolution runs — inside a `requires`-carrying sort, which is
/// where selection is most wanted.
#[test]
fn a_pin_outranks_a_deferral_to_the_enclosing_frame() {
    let build = |call: &str| {
        program(
            "wi841.deferral",
            PARAMETRIC_RIVAL,
            &format!(
                r#"  sort Holder
    sort HT = ?
    requires Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 = {call}
  end
{}"#,
                driver("Holder.probe(2, 3)")
            ),
        )
    };
    assert_eq!(
        eval_int(&build("Monoid.combine(a, b)"), "wi841.deferral.Driver.go", "the deferral"),
        5,
        "CONTROL: unbracketed, the body reads the frame dictionary the search filled",
    );
    assert_eq!(
        eval_int(
            &build("Monoid.combine[Monoid = AnyM](a, b)"),
            "wi841.deferral.Driver.go",
            "the pin inside a requires-carrying body",
        ),
        99,
        "the bracket must be honoured rather than deferred past",
    );
}

/// The same key on an OP-SCOPED `requires` (§4.2's own `fold[Monoid = AddM]` shape).
/// Its threading rides on value-direction rather than a dictionary — an op-scoped
/// chain has no frame slots at all (WI-822 leg 1, undelivered) — so what phase 2 owes
/// here is that the key RESOLVES and the witness is CHECKED, which the sibling test
/// below measures.
#[test]
fn a_spec_short_name_selects_an_op_scoped_slot() {
    let src = program(
        "wi841.opscoped",
        "",
        &format!(
            r#"  sort Holder
    sort HT = ?
    operation probe(a: HT, b: HT) -> Int64 requires Monoid[T = HT] = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[Monoid = AddM](2, 3)")
        ),
    );
    assert_eq!(eval_int(&src, "wi841.opscoped.Driver.go", "op-scoped selection runs"), 5);
}

/// §4.2's "a direct spec-op call is the same case": the callee has no `requires` of
/// its own, and the thing selected is the dispatching dictionary — `requirements[0]`
/// — so the DISPATCHED SPEC's own short name is admitted as a key.
#[test]
fn a_direct_spec_op_call_selects_its_own_dispatch() {
    let src = program(
        "wi841.direct",
        "",
        &driver("Monoid.combine[Monoid = AddM](2, 3)"),
    );
    assert_eq!(eval_int(&src, "wi841.direct.Driver.go", "a direct spec-op call selects"), 5);
}

/// Rule (1) SUBSUMES the named-slot case (§4.2): a binder is an ordinary type
/// parameter, so binding it is a type-argument binding — and it must ALSO select,
/// which is the half WI-840 left undone (there, `[m = AddM]` loaded and meant
/// nothing). Both scopes, since a sort's named slot is bindable at a call on its
/// member as well as in a type application.
#[test]
fn a_named_slot_binder_selects_at_both_levels() {
    let sort_level = program(
        "wi841.namedsort",
        PARAMETRIC_RIVAL,
        &format!(
            r#"  sort Holder
    sort HT = ?
    requires m: Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[m = AnyM](2, 3)")
        ),
    );
    assert_eq!(
        eval_int(&sort_level, "wi841.namedsort.Driver.go", "a sort-level binder selects"),
        99,
        "the answer must be AnyM's 99, not the search's 5 — else the binder bound a \
         parameter and selected nothing, which is exactly the WI-840 state",
    );

    let op_level = program(
        "wi841.namedop",
        PARAMETRIC_RIVAL,
        &format!(
            r#"  sort Holder
    sort HT = ?
    operation probe(a: HT, b: HT) -> Int64 requires m: Monoid[T = HT] = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[m = AnyM](2, 3)")
        ),
    );
    assert_eq!(
        eval_int(&op_level, "wi841.namedop.Driver.go", "an op-level binder selects"),
        99,
    );
}

/// A slot the author NAMED is no longer answered by its spec's short name: the binder
/// is the way to reach it (rule 1), and leaving the short name pointing at the same
/// slot would let ONE bracket bind it twice, through two keys, with two witnesses.
/// The named slot is subtracted from its spec's anonymous population by SPEC, not by
/// position — the sort-level position indexes a list the typer does not hold.
#[test]
fn a_named_slot_is_not_also_reachable_by_its_spec_short_name() {
    let src = program(
        "wi841.namedonly",
        "",
        &format!(
            r#"  sort Holder
    sort HT = ?
    requires m: Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[Monoid = AddM](2, 3)")
        ),
    );
    refused_with(
        &src,
        "unknown type-param 'Monoid'",
        "the only anonymous Monoid slot was named, so no slot is left for rule (2)",
    );
}

// ── The three refusals §9 phase 2 names ──────────────────────────────

/// A QUALIFIED key is REFUSED, not resolved (§4.2). Rule (1) already refuses one
/// (measured: a qualified spelling of a REAL type param is `unknown type-param`), and
/// rule (2) adds no resolution rung — so selection cannot come to depend on the
/// CALLER's imports, while the supply path takes no scope at all. It also keeps
/// `same_label`'s own `debug_assert`, which fires on a partially-qualified pair, out
/// of reach: a key with a dot never enters the lookup.
#[test]
fn a_qualified_key_is_refused() {
    let src = program(
        "wi841.qualified",
        "",
        &format!("{HOLDER_SORT_LEVEL}{}", driver("Holder.probe[wi841.qualified.Monoid = AddM](2, 3)")),
    );
    refused_with(
        &src,
        "unknown type-param 'wi841.qualified.Monoid'",
        "a qualified key is refused with the rung-(1) message, not resolved by rung (2)",
    );
}

/// A short name AMBIGUOUS across two anonymous slots is the loud error, and the gate
/// that makes rule (2) sound: without "unambiguous among the remaining anonymous
/// slots" this is the short-name identity comparison WI-672 deleted. The message must
/// name the slots and point at the fix (name one).
#[test]
fn a_short_name_ambiguous_across_two_anonymous_slots_is_loud() {
    let src = program(
        "wi841.ambig",
        "",
        &format!(
            r#"  sort Holder
    sort HT = ?
    requires Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 requires Monoid[T = HT] = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[Monoid = AddM](2, 3)")
        ),
    );
    refused_with(
        &src,
        "names more than one requirement slot",
        "two anonymous slots of one spec leave the short name no unique answer",
    );
    refused_with(&src, "requires <name>: Monoid", "and the message must name the fix");
}

/// An operation type parameter colliding with its ENCLOSING SORT's is refused AT THE
/// DECLARATION. Phase 2 INHERITS this from WI-840 rather than adding it, and asserts
/// it because it is what licenses `call_bracket_scopes` to CONCATENATE the two scopes
/// instead of laddering them: with the guard, no key can hit two targets; without it,
/// the concatenation would be a silent capture the reader cannot see.
#[test]
fn an_op_type_param_colliding_with_its_sorts_is_refused_at_the_declaration() {
    let src = program(
        "wi841.collide",
        "",
        r#"  sort Box
    sort T = ?
    operation mk[T](v: T) -> Int64 = 0
  end"#,
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("T") && e.contains("Box")),
        "the collision must be named at the declaration; got: {errs:?}",
    );
}

// ── §4.4 witness validation ──────────────────────────────────────────

/// Check 1, base level: the witness must provide the spec at all. Both halves are
/// named because either can be the typo.
#[test]
fn a_witness_that_provides_nothing_is_loud() {
    let src = program(
        "wi841.noprov",
        "",
        &format!("{HOLDER_SORT_LEVEL}{}", driver("Holder.probe[Monoid = NoProv](2, 3)")),
    );
    refused_with(&src, "does not provide", "a non-provider cannot be selected");
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| e.contains("NoProv") && e.contains("Monoid")),
        "the message must name BOTH the witness and the spec; got: {errs:?}",
    );
}

/// A slot binding's VALUE denotes a witness SORT. Bound to something else there is no
/// provider to check and no impl to pin, so it is refused rather than folded into the
/// type-parameter half and the slot called bound.
#[test]
fn a_slot_bound_to_a_non_sort_is_refused() {
    let src = program(
        "wi841.notasort",
        "",
        &format!("{HOLDER_SORT_LEVEL}{}", driver("Holder.probe[Monoid = 42](2, 3)")),
    );
    refused_with(&src, "must name a WITNESS SORT", "a literal is no witness");
}

/// Check 1 again, on a witness that provides a DIFFERENT spec — the other way the
/// pair can be wrong.
#[test]
fn a_witness_of_another_spec_is_loud() {
    let src = program(
        "wi841.wrongspec",
        "",
        &format!("{HOLDER_SORT_LEVEL}{}", driver("Holder.probe[Monoid = Marker](2, 3)")),
    );
    refused_with(&src, "does not provide", "a provider of another spec is not a witness here");
}

/// Check 3 (§1.1): a CONCRETE provider — a sort with constructors — is a backend
/// whose VALUES carry their own sort, so value-directed dispatch is already deciding
/// and an explicit witness could only agree redundantly or contradict silently.
/// Refuse, do not prefer. The criterion is read through `sorts_with_constructors`,
/// the same owner the witness-coherence exemption uses, so the two cannot drift.
#[test]
fn selecting_a_concrete_provider_is_refused_not_preferred() {
    let src = program(
        "wi841.concrete",
        r#"
  sort Pebble
    entity pebble
    fact Monoid[T = Pebble]
    operation combine(a: Pebble, b: Pebble) -> Int64 = 3
  end
"#,
        &driver("Monoid.combine[Monoid = Pebble](pebble(), pebble())"),
    );
    refused_with(
        &src,
        "is a CONCRETE provider",
        "where the value decides, an explicit witness is refused (§4.4 check 3)",
    );

    // CONTROL: the same program without the bracket loads and runs, so the refusal is
    // about the SELECTION and not about the program.
    let control = program(
        "wi841.concreteok",
        r#"
  sort Pebble
    entity pebble
    fact Monoid[T = Pebble]
    operation combine(a: Pebble, b: Pebble) -> Int64 = 3
  end
"#,
        &driver("Monoid.combine(pebble(), pebble())"),
    );
    assert_eq!(eval_int(&control, "wi841.concreteok.Driver.go", "the value-directed call runs"), 3);
}

/// Check 3 does not leak into rule (1)'s ordinary business: a type-argument binding
/// naming a CONCRETE sort is not a selection and must keep loading. Structurally it
/// cannot — only a slot target carries a witness — and this pins it, because the two
/// live one `match` arm apart.
#[test]
fn a_concrete_type_argument_is_not_a_selection() {
    let src = program(
        "wi841.concretearg",
        r#"
  sort Pebble
    entity pebble
  end
"#,
        r#"  sort Box
    sort T = ?
    entity box(v: T)
    operation mk(v: T) -> Box[T = T] = box(v: v)
  end
  sort Use
    operation go(n: Int64) -> Box[T = Pebble] = Box.mk[T = Pebble](pebble())
  end"#,
    );
    loads_clean(&src, "binding a type PARAMETER to a concrete sort is not a witness selection");
}

// ── §4.5 step 0, and the routes that must not swallow a pin ──────────

/// NON-VACUITY for the binding-precise half of check 1, on all THREE routes a slot
/// can be served by. `StrM` provides `Monoid` — so the base-level check passes — but
/// at `T = String`, and every call below is at `T = Int64`.
///
/// Each row FAILED differently before the site check existed: the spec-op route was
/// already loud, the dictionary route LOADED CLEAN and died `Internal(… __req_monoid
/// not bound …)` at eval, and the op-scoped route silently IGNORED the pin and
/// computed the searched answer. That spread is the argument for checking at the
/// site: only two of the three routes have a place to complain from.
#[test]
fn a_pin_at_other_bindings_is_loud_on_every_route() {
    let sort_level = program(
        "wi841.otherbind1",
        OTHER_BINDINGS,
        &format!("{HOLDER_SORT_LEVEL}{}", driver("Holder.probe[Monoid = StrM](2, 3)")),
    );
    refused_with(&sort_level, "does not provide", "dictionary route");

    let op_scoped = program(
        "wi841.otherbind2",
        OTHER_BINDINGS,
        &format!(
            r#"  sort Holder
    sort HT = ?
    operation probe(a: HT, b: HT) -> Int64 requires Monoid[T = HT] = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[Monoid = StrM](2, 3)")
        ),
    );
    refused_with(&op_scoped, "does not provide", "value-directed route");

    let spec_op = program(
        "wi841.otherbind3",
        OTHER_BINDINGS,
        &driver("Monoid.combine[Monoid = StrM](2, 3)"),
    );
    refused_with(&spec_op, "does not provide", "spec-op dispatch route");

    // The op-scoped route again, written POSITIONALLY (`requires Monoid[HT]`) — the
    // spelling the stdlib itself uses (`requires Eq[T]`, prelude/list.anthill:58).
    // MEASURED: reading only the clause's NAMED arguments left this goal with no
    // bindings, which every provider matches, so the row above passed while its twin
    // here loaded clean — a check that reads as covering the common case and did not.
    let positional = program(
        "wi841.otherbind4",
        OTHER_BINDINGS,
        &format!(
            r#"  sort Holder
    sort HT = ?
    operation probe(a: HT, b: HT) -> Int64 requires Monoid[HT] = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[Monoid = StrM](2, 3)")
        ),
    );
    refused_with(&positional, "does not provide", "value-directed route, positional requires");

    // CONTROL for that row: the positional spelling with the RIGHT witness still
    // loads and runs, so the refusal is about the bindings and not about positionals.
    let positional_ok = program(
        "wi841.otherbind5",
        "",
        &format!(
            r#"  sort Holder
    sort HT = ?
    operation probe(a: HT, b: HT) -> Int64 requires Monoid[HT] = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[Monoid = AddM](2, 3)")
        ),
    );
    assert_eq!(
        eval_int(&positional_ok, "wi841.otherbind5.Driver.go", "positional + right witness"),
        5,
    );

    // CONTROL: `StrM` is a legitimate provider — the SAME witness at its own bindings
    // loads and runs, so the three refusals are about the BINDINGS, not about StrM.
    let ok = program(
        "wi841.otherbindok",
        OTHER_BINDINGS,
        &format!(
            r#"  sort Holder
    sort HT = ?
    requires Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 = Monoid.combine(a, b)
  end
  sort Driver
    operation go(n: Int64) -> Int64 = Holder.probe[Monoid = StrM]("a", "b")
  end"#,
        ),
    );
    assert_eq!(eval_int(&ok, "wi841.otherbindok.Driver.go", "StrM at its own bindings"), 7);
}

/// NON-VACUITY for the Strategy-1/2 SKIP: explicit selection outranks a FORWARD
/// exactly as it outranks a search (§4.1 tier 1). Here the caller's own frame covers
/// the dep, so without the skip the pin would be forwarded past in silence; with it,
/// the pin reaches construction, fails at the abstract element, and is refused AT
/// LOAD. The bracket-less control still runs, so the refusal is the bracket's.
#[test]
fn a_pin_is_not_forwarded_past_by_a_covering_caller_frame() {
    let body = |call: &str| {
        format!(
            r#"{HOLDER_SORT_LEVEL}  sort Outer
    sort OT = ?
    requires Monoid[T = OT]
    operation run(a: OT, b: OT) -> Int64 = {call}
  end
{}"#,
            driver("Outer.run(2, 3)")
        )
    };
    let pinned = program(
        "wi841.forward",
        OTHER_BINDINGS,
        &body("Holder.probe[Monoid = StrM](a, b)"),
    );
    refused_with(
        &pinned,
        "from the selected witness",
        "a pinned dep that does not project is a LOAD refusal naming the pin, never a \
         silent no-dict that dies at eval",
    );

    let control = program("wi841.forwardok", OTHER_BINDINGS, &body("Holder.probe(a, b)"));
    assert_eq!(
        eval_int(&control, "wi841.forwardok.Driver.go", "the unpinned forward still works"),
        5,
    );
}

/// A selection does NOT reach SUB-resolutions (§4.5): rule (2)'s candidate set is the
/// CALLEE's slots, and extending it into the resolution tree would make key
/// resolution depend on which witness was pinned. Here the pinned witness is
/// CONDITIONAL — it resolves its own `:-` subgoal by SEARCH — and the program runs,
/// which it could not if the pin had been re-applied to the subgoal (`Inner` is not a
/// provider of the subgoal's spec).
#[test]
fn a_selection_does_not_reach_sub_resolutions() {
    let src = program(
        "wi841.subgoal",
        r#"
  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end
  sort WrapM
    sort E = ?
    requires Monoid[T = E]
    fact Monoid[T = Wrap[A = E]]
    operation combine(a: Wrap[A = E], b: Wrap[A = E]) -> Int64 =
      add(1000, Monoid.combine(a.inner, b.inner))
  end
"#,
        &format!(
            r#"  sort Holder
    sort HT = ?
    requires Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[Monoid = WrapM](wrap(inner: 2), wrap(inner: 3))")
        ),
    );
    assert_eq!(
        eval_int(&src, "wi841.subgoal.Driver.go", "a conditional witness still searches its subgoal"),
        1005,
        "1000 + AddM's 2+3: the pin selected WrapM at the TOP goal, and WrapM's own \
         `requires Monoid[T = E]` subgoal was answered by SEARCH (AddM), not by the pin",
    );
}

/// One bracket may not select two DIFFERENT witnesses for one spec: a pin is keyed by
/// the SPEC at `resolve`'s step 0, so two witnesses under one key have no meaning to
/// give. Refused here rather than first-matched, so 058 phase 3b — which lets two
/// providers coexist — cannot silently inherit a first-match.
#[test]
fn two_witnesses_for_one_spec_in_one_bracket_are_refused() {
    let src = program(
        "wi841.conflict",
        PARAMETRIC_RIVAL,
        &format!(
            r#"  sort Holder
    sort HT = ?
    requires m: Monoid[T = HT]
    operation probe(a: HT, b: HT) -> Int64 requires Monoid[T = HT] = Monoid.combine(a, b)
  end
{}"#,
            driver("Holder.probe[m = AddM, Monoid = AnyM](2, 3)")
        ),
    );
    refused_with(
        &src,
        "selects two providers",
        "the binder and the short name reached the same spec with different witnesses",
    );
}

// ── Controls: nothing that loaded before may change ──────────────────

/// The bracket's ORIGINAL meaning is untouched: an op-level type argument still binds
/// its parameter, and its diagnostics are still WI-839's. Rule (1) puts the
/// operation's own scope FIRST for exactly this reason — no existing program shifts.
#[test]
fn an_op_level_type_argument_still_binds_and_still_reports() {
    let ok = program(
        "wi841.oplevel",
        "",
        r#"  sort Id
    operation idy[A](x: A) -> A = x
    operation go(n: Int64) -> Int64 = Id.idy[A = Int64](n)
  end"#,
    );
    loads_clean(&ok, "an op-level binding is unchanged");

    let bogus = program(
        "wi841.oplevelbogus",
        "",
        r#"  sort Id
    operation idy[A](x: A) -> A = x
    operation go(n: Int64) -> Int64 = Id.idy[Bogus = Int64](n)
  end"#,
    );
    refused_with(&bogus, "unknown type-param 'Bogus'", "WI-839's message is unchanged");
}

/// A POSITIONAL binding reaches the enclosing sort's parameters too — rule (1) is one
/// rule over one concatenated list, so a positional counts through it. Selection
/// stays NAME-only by contrast: a requirement slot has no position a caller could
/// count to, since the two lists it might index are separate and the sort-level one
/// is the FACT order at every typer-side reader.
#[test]
fn a_positional_binding_reaches_the_sorts_params_and_selection_stays_by_name() {
    let src = program(
        "wi841.positional",
        "",
        r#"  sort Box
    sort T = ?
    entity box(v: T)
    operation mk(v: T) -> Box[T = T] = box(v: v)
    operation peek(b: Box[T = Int64]) -> Int64 = b.v
  end
  sort Use
    operation go(n: Int64) -> Int64 = Box.peek(Box.mk[Int64](5))
  end"#,
    );
    assert_eq!(
        eval_int(&src, "wi841.positional.Use.go", "a positional binds the sort's param"),
        5,
    );

    // A positional PAST the concatenated list is still over-application, not a slot.
    let excess = program(
        "wi841.positionalexcess",
        "",
        &format!("{HOLDER_SORT_LEVEL}{}", driver("Holder.probe[Int64, Int64](2, 3)")),
    );
    refused_with(
        &excess,
        "over-applied",
        "a positional never selects a requirement slot, so the second one has no target",
    );
}

/// The `requires`-covered call with NO bracket is untouched — the search still
/// answers it. This is the shape the whole stdlib is written in, and the control that
/// the pin machinery only fires when a bracket says so.
#[test]
fn an_unbracketed_requires_call_is_unchanged() {
    let src = program(
        "wi841.nobracket",
        "",
        &format!("{HOLDER_SORT_LEVEL}{}", driver("Holder.probe(2, 3)")),
    );
    assert_eq!(eval_int(&src, "wi841.nobracket.Driver.go", "the search answers it"), 5);
}
