//! WI-20260911-073GH — A CONSTRUCTOR NAMED `f` ANYWHERE TOOK THE IDENTIFIER `f` AWAY
//! FROM THE WHOLE LANGUAGE, and the prelude was the first casualty.
//!
//! `sort Bit { entity t; entity f }`, in a file with no operation of its own, refused
//! the load with five copies of
//!
//! ```text
//! error: constructor 'f' given 1 positional argument(s) but has 0 unfilled field(s) (declares: none)
//! ```
//!
//! and no location. The errors were not about the user's file at all: they were raised
//! while loading the PRELUDE, whose `List.foldLeft`, `List.foldRight`,
//! `List.mapElemsOnto`, `Option.optionFlatMap`, `Option.optionMap`,
//! `Result.resultFlatMap`, `Result.resultMap` and `Delay.delayFlatMap` each APPLY a
//! parameter named `f` — 8 raises, which the CLI's dedup printed as five lines. The
//! scan defines every name across every file before any load pass runs
//! (`scan_definitions`, CLAUDE.md), so a user file's `entity f` was already in the KB
//! when the prelude's bodies were converted. Renaming the entity to `ff` loaded clean;
//! so did naming it `x`, `s` or `args`. It was never the letter — it was the name of an
//! APPLIED PARAMETER somewhere in the loaded corpus.
//!
//! ## WHERE IT CAME FROM
//!
//! `emit_operation_equation` lowers an operation's body a SECOND time (the first is
//! `convert_expr_term`'s occurrence walk) to build the defining equation
//! `eq(op(?p…), body[params → ?pᵢ])`. It is called from the tail of `load_operation`,
//! AFTER that function restored the enclosing scope — so the body was converted with
//! the operation's own parameters invisible. Every parameter reference then fell down
//! the resolution ladder to its last rung, WI-476's bare `intern(name)` "resolves to
//! nothing" symbol, and `rewrite_param_refs` recognised a parameter by that bare
//! spelling afterwards.
//!
//! That bare symbol is scope-less and global, and `register_entity_field_names_scan`
//! deliberately registers each entity's field schema under it too (for sugar-generated
//! facts, which reference `kb.intern("WorkItem")`). So `intern("f")` carried a 0-field
//! schema the moment ANY entity named `f` was scanned, `positional_to_named_plan`
//! answered `OverArity` for the application `f(x)`, and the loud-error principle did
//! the rest — loudly, about the wrong thing.
//!
//! ## THE FIX, AND WHY IT IS THE SCOPE AND NOT A TABLE
//!
//! The equation is now lowered IN `op_scope`. A scope's own locals short-circuit
//! `resolve_in_scope`, so the declared `SymbolKind::Param` place shadows whatever the
//! enclosing scope calls `f` — at a FUNCTOR position exactly as at a leaf, with no
//! position that has to remember to consult a shadowing table first (`rule_param_vars`'
//! shape, which is consulted at the two `Term::Ident` arms and NOT at a functor: see
//! `applying_a_rule_clause_parameter_is_refused_either_way` for what that costs and why
//! it costs nothing here). `rewrite_param_refs` correspondingly reads a parameter by the
//! op-scoped place symbol (`Loader::op_param_symbol`, off WI-352's `arg_places`) rather
//! than by the bare intern.
//!
//! THAT IS ONE OF TWO BINDER CLASSES, and the first cut of this ticket shipped only it.
//! A `let` / `lambda` / `match` binder opens a scope too, and `convert_term` kept NO
//! local-name frames for those — `visit_load` pushed them and this walk did not — so
//! `let f = …; f(n)` was captured exactly as an applied parameter had been, measured
//! cross-file. `convert_term_inner` now pushes `build_pattern_scope_frame` over the
//! children `binder_form_layout` says are scoped, which is the same sentence as the
//! parameter half: the two lowerings of ONE body must agree about which names are bound.
//! Driven by `a_let_bound_name_that_is_also_a_constructor_still_applies`.
//!
//! ## AND THE OTHER HALF: A NAME THAT RESOLVES TO NOTHING
//!
//! The scope and the binder frames answer for a name that RESOLVES — they shadow a
//! constructor the citing scope can actually see. The complementary case is a name that
//! resolves to NOTHING, which lands on WI-476's scope-less bare `intern(name)` and takes
//! the schema of any entity, anywhere in the corpus, sharing its short name.
//! `KnowledgeBase::written_entity_field_names` closes it: a written functor that
//! resolved to nothing is not an entity application. Driven by
//! `a_stranger_entity_does_not_rename_a_written_terms_arguments` and
//! `a_zero_field_stranger_is_an_ordinary_undeclared_term`.
//!
//! NEITHER SUBSUMES THE OTHER, and it took backing each out to know it. With only the
//! gate, this file's own fixture still fails: `entity f` sits in `sort Bit` in the SAME
//! namespace, so §8.6's variant-exposure edge makes `f` RESOLVE at the operation's
//! scope, and only the frame can shadow it. With only the frames, a stranger in another
//! file still reshapes a fact term. Measured both ways.
//!
//! ## WHAT IT STILL DOES NOT DO
//!
//! An APPLIED parameter is still DROPPED from the equation this walk emits, and that is
//! pre-existing rather than introduced here: `rewrite_param_refs` rewrites `Ident`/`Ref`
//! LEAVES and never a `Term::Fn` FUNCTOR, so `operation twice(k, n) = k(k(n))` emits
//! `eq(twice(?#1, ?#0), k(k(?#0)))` — head variable `?#1` unused, functor `k` denoting
//! nothing. Every higher-order prelude equation has the same shape (`optionMap`,
//! `foldLeft`, …) and always did. What this ticket changes is only that the COLLIDING
//! case used to be a loud (and wrong) refusal and is now as silent as the rest; the
//! equation itself is no worse. Whether such an equation should be expressed through an
//! apply form or not emitted at all is a question about the equation channel, not about
//! name capture, and is not answered here.
//! ## WHAT THE TICKET SAID AND WHAT WAS MEASURED
//!
//! The ticket's CAUSE named the EVAL twin — `finish_constructor`'s desugar and
//! `KnowledgeBase::is_constructor_symbol` — and read the symptom as "every call in every
//! operation body fails". Both are off, and the probe says so: a backtrace at the
//! `PositionalPlan::OverArity` arm put ALL 8 raises in `load_operation →
//! emit_operation_equation → convert_term`, a LOAD-time path, and the user file in the
//! headline measurement has no operation body for a call to fail in. The gate is
//! `entity_field_names`, not `is_constructor_symbol`; the ticket's route (2) (stop
//! keying the constructor table on the bare short symbol) would also have closed it,
//! and is not needed once the parameter is in scope.
//!
//! ## WHICH ROWS MOVE — MEASURED, by restoring `kb/load.rs` and `kb/mod.rs` to HEAD
//!
//! `scripts/test.sh -p anthill-core --test wi_tests -- wi994 wi_073gh` runs 16 rows:
//! **16 passed** with the change, **8 passed / 8 failed** with the whole of it backed
//! out. The eight that move:
//!
//! ```text
//!   the_prelude_still_folds_beside_an_entity_named_f          fixture does not LOAD
//!   a_callback_parameter_named_after_a_constructor_applies    fixture does not LOAD
//!   a_let_bound_name_that_is_also_a_constructor_still_applies fixture does not LOAD
//!   a_shadowing_binder_binds_its_own_use_in_the_emitted_equation
//!   a_stranger_entity_does_not_rename_a_written_terms_arguments
//!   a_zero_field_stranger_is_an_ordinary_undeclared_term      fixture does not LOAD
//!   wi994 …one_variant_name_exposed_by_two_namespaces_is_ambiguous   2 errors, not 1
//!   wi994 …two_distinct_references_…_still_report_twice              4 errors, not 2
//! ```
//!
//! WHICH HALF MOVES WHICH, measured separately along the way: backing out the SCOPE half
//! alone reddens the first two and both wi994 rows. The `let` row needs the BINDER half
//! specifically — measured against a build carrying the scope half and not the binder
//! one, where the cross-file fixture in its own doc refused the load. The two stranger
//! rows need the `written_entity_field_names` gate, and nothing else moves them.
//!
//! The eight that PASS EITHER WAY are the by-design controls
//! (`a_value_only_parameter_was_never_affected`,
//! `an_over_arity_constructor_application_is_still_refused`,
//! `applying_a_rule_clause_parameter_is_refused_either_way`,
//! `the_let_value_still_sees_the_enclosing_scope`), wi994's three, and wi979's one. Each
//! WI-073GH control carries its OWN fixture, with no `entity f` in it, precisely so that
//! claim can be true — a by-design control sharing a fixture that stops loading would
//! redden for someone else's reason and measure nothing. Together they say this change
//! stopped a BINDER, and a name that denotes nothing, being read as a constructor
//! without stopping constructor arity from being checked.
//!
//! Two of the eight failures are in `wi994_variant_exposure_test`, and they are
//! **WI-1005** — one ambiguity reported twice, once per scope the same occurrence was
//! resolved at. The second resolution WAS this walk, at the enclosing scope; now that it
//! runs at the operation's own scope the two renderings coincide and the injective
//! `dedup_key` (WI-745) collapses them, which is WI-1005's "eliminate a producer rather
//! than widen the key" reached from the other side. The numbers are at those rows.

use anthill_core::kb::KnowledgeBase;

/// The POISONED fixture: the declaration that used to take the identifier away
/// (`entity f`), an APPLIED parameter that shares a constructor's short name (`g`), and
/// two bodies that reach the prelude — one through `foldLeft`, which is one of the 8
/// sites `entity f` broke, and one through `length`, which is the call the ticket named.
///
/// Nothing here loads with the fix backed out, so every row over it is a MEASUREMENT.
/// The two by-design controls live in fixtures of their own.
const SRC: &str = r#"
namespace test.wi073gh
  import anthill.prelude.{Int64, List}

  -- THE DECLARATION. `f` is the prelude's callback-parameter name throughout
  -- `List` / `Option` / `Result` / `Delay`.
  sort Bit
    entity t
    entity f
  end

  sort Shape
    entity g

    -- (d) in the ticket: the parameter `g` is APPLIED, and a nullary `entity g` is
    -- declared two lines above it.
    operation twice(g: (v: Int64) -> Int64, n: Int64) -> Int64 = g(g(n))

    -- The prelude's `List.foldLeft(xs, init, f)` — whose OWN body is
    -- `foldLeft(t, f(init, h), f)`, an applied parameter named `f`.
    operation sum(xs: List[T = Int64]) -> Int64 =
      List.foldLeft(xs, 0, lambda (acc: Int64, x: Int64) -> acc + x)

    -- The ticket's own (a): `length(args)` beside `entity f`.
    operation count(xs: List[T = Int64]) -> Int64 = List.length(xs)

    -- The SECOND binder class: `f` is a `let` binder here, not a declared
    -- parameter. Found by `/code-review` after the parameter half had landed.
    operation viaLet(n: Int64) -> Int64 =
      let f = lambda (v: Int64) -> v + 1
      f(n)
  end

  rule gtwice(?r) :- ?r <=> Shape.twice(lambda (v: Int64) -> v + 1, 1)
  rule gfold(?r)  :- ?r <=> Shape.sum([1, 2, 3])
  rule gcount(?r) :- ?r <=> Shape.count([1, 2, 3])
  rule glet(?r)   :- ?r <=> Shape.viaLet(1)
end
"#;

/// The VALUE-ONLY control, in its OWN fixture with no `entity f` anywhere — so it loads
/// on both sides of the change and the row really does pass either way. Sharing [`SRC`]
/// would have made it redden on a back-out for the fixture's reason rather than its own,
/// which is exactly the thing a control must not do.
const SRC_VALUE_ONLY: &str = r#"
namespace test.wi073gh.valueonly
  import anthill.prelude.{Int64}
  sort Shape
    entity h
    -- `h` is a parameter used only as a VALUE, never applied. A leaf reference was
    -- always rewritten by name, so this row never moved.
    operation keep(h: Int64) -> Int64 = h
  end
  rule gkeep(?r) :- ?r <=> Shape.keep(9)
end
"#;

/// THE TERM-POSITION fixture, and the SECOND half of the same root cause. Two
/// namespaces in one source: the first DECLARES entities, the second imports nothing
/// from it and writes their short names anyway.
///
/// `ff` / `zz` are the colliding spellings; `gg` / `qq` are their controls, matching no
/// entity anywhere. The whole point is that each colliding row must behave exactly like
/// its control — an entity the citing namespace cannot see, did not import and did not
/// name must not decide what a written term is.
const SRC_STRANGER: &str = r#"
namespace test.wi073gh.stranger.decl
  import anthill.prelude.{Int64}
  sort Boxed
    entity ff(a: Int64)
  end
  sort Bit
    entity t
    entity zz
  end
end

namespace test.wi073gh.stranger
  fact holdsF(ff(1))
  fact holdsG(gg(1))
  fact holdsZ(zz(1))
  fact holdsQ(qq(1))
end
"#;

/// Two `let`-bodied operations: one whose binder SHADOWS the parameter, one whose `let`
/// VALUE reads the parameter. Together they pin both halves of `binder_form_layout`'s
/// rule — the pattern is inside the scope it opens, the `let` value is outside it.
const SRC_SHADOW: &str = r#"
namespace test.wi073gh.shadow
  import anthill.prelude.{Int64}
  sort S
    operation shadow(x: Int64) -> Int64 =
      let x = 100
      x + 1
    operation reads_param(n: Int64) -> Int64 =
      let y = n + 1
      y * 2
  end
end
"#;

fn kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

/// The `(binding occurrence, use)` symbol pair of the `let` in `<op>`'s emitted defining
/// equation — `eq(<op>(?p…), let_expr(pattern_var(B), value, body))`, where `B` is the
/// binding occurrence and the use is the leaf of the same name inside `body`.
///
/// Reads the EQUATION (`rules_by_functor(PartialEq.eq)`) rather than the op-body
/// occurrence, because the equation is the artifact `emit_operation_equation` builds and
/// the only one this ticket's scope change reaches.
fn shadow_equation_binder_symbols(
    kb: &mut KnowledgeBase,
    op_short: &str,
) -> (anthill_core::intern::Symbol, anthill_core::intern::Symbol) {
    use anthill_core::kb::term::Term;
    let eq_sym = kb
        .try_resolve_symbol("anthill.prelude.PartialEq.eq")
        .expect("the equation functor must resolve");
    for rid in kb.rules_by_functor(eq_sym) {
        let head = kb.rule_head(rid);
        let Term::Fn { pos_args, .. } = kb.get_term(head) else {
            continue;
        };
        if pos_args.len() != 2 {
            continue;
        }
        let (call, body) = (pos_args[0], pos_args[1]);
        let Term::Fn { functor, .. } = kb.get_term(call) else {
            continue;
        };
        if kb.local_name_of(*functor) != op_short {
            continue;
        }
        // `let_expr(pattern_var(B), value, body)` — the layout `binder_form_layout` names.
        let Term::Fn { pos_args: le, .. } = kb.get_term(body) else {
            panic!("{op_short}: equation body is not a `let_expr`");
        };
        assert_eq!(le.len(), 3, "{op_short}: `let_expr` takes pattern/value/body");
        let (pat, let_body) = (le[0], le[2]);
        let Term::Fn { pos_args: pv, .. } = kb.get_term(pat) else {
            panic!("{op_short}: `let` pattern is not a `pattern_var`");
        };
        let binding = match kb.get_term(pv[0]) {
            Term::Ident(s) | Term::Ref(s) => *s,
            other => panic!("{op_short}: binding occurrence is {other:?}"),
        };
        let name = kb.local_name_of(binding).to_string();
        let usage = find_leaf_named(kb, let_body, &name)
            .unwrap_or_else(|| panic!("{op_short}: no use of `{name}` in the `let` body"));
        return (binding, usage);
    }
    panic!("no defining equation found for `{op_short}`");
}

/// The first `Ident`/`Ref` leaf under `tid` whose local name is `name`.
fn find_leaf_named(
    kb: &KnowledgeBase,
    tid: anthill_core::kb::term::TermId,
    name: &str,
) -> Option<anthill_core::intern::Symbol> {
    use anthill_core::kb::term::Term;
    match kb.get_term(tid) {
        Term::Ident(s) | Term::Ref(s) if kb.local_name_of(*s) == name => Some(*s),
        Term::Fn {
            pos_args,
            named_args,
            ..
        } => pos_args
            .iter()
            .chain(named_args.iter().map(|(_, t)| t))
            .find_map(|&c| find_leaf_named(kb, c, name)),
        _ => None,
    }
}

/// Solutions for a query pattern written with `test.wi073gh.stranger` in scope — the
/// in-process spelling of `anthill query -i`, because a fact head is not addressable by
/// its qualified name from a query pattern.
fn stranger_hits(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    use anthill_core::kb::resolve::ResolveConfig;
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The sole definite answer of `<qn>(?r)` as an `i64`. A row that answers nothing, or
/// answers something that is not a number, fails here rather than silently comparing
/// empty to empty.
fn answer(kb: &mut KnowledgeBase, qn: &str) -> i64 {
    let vals = crate::common::definite_unary(kb, qn);
    assert_eq!(vals.len(), 1, "{qn}: expected exactly one definite answer");
    crate::common::scalar_int(kb, &vals[0])
        .unwrap_or_else(|| panic!("{qn}: answer is not an Int64: {:?}", vals[0]))
}

/// THE HEADLINE ROW: the prelude's `foldLeft` still folds with an `entity f` in the
/// load. Driven by VALUE — `sum([1, 2, 3])` is 6 — and not by "it loaded", because the
/// whole defect is that a body's defining equation was built from a misread term.
///
/// Backed out, this panics in `load_kb_with`: the fixture does not load at all.
#[test]
fn the_prelude_still_folds_beside_an_entity_named_f() {
    let mut kb = kb();
    assert_eq!(
        answer(&mut kb, "test.wi073gh.gfold"),
        6,
        "`List.foldLeft(xs, 0, +)` over [1, 2, 3]. `foldLeft`'s own body applies its \
         parameter `f`, which is one of the 8 prelude sites `entity f` captured"
    );
    assert_eq!(
        answer(&mut kb, "test.wi073gh.gcount"),
        3,
        "and the ticket's own (a): `length(args)` in an operation body beside \
         `entity f`. It is here because the ticket read the refusal as being ABOUT this \
         call — it never was (module doc), and the row that proves it is `gfold`, which \
         reaches a body that really does apply an `f`"
    );
}

/// THE SECOND BINDER CLASS, and the half `/code-review` found after the first landed:
/// a `let` binder, not a declared parameter.
///
/// `convert_term` kept no let/lambda/match local-name frames — only the OCCURRENCE walk
/// pushed them — so the equation lowering resolved `f` at the enclosing scope however
/// well the parameter half worked, and an unrelated `entity f` captured it again. Driven
/// by VALUE: `viaLet(1)` applies a let-bound lambda and is 2.
///
/// MEASURED cross-file too, which is the shape that says it is not about one file's own
/// declarations: `namespace other.bits { sort Bit { entity t; entity f } }` in a SECOND
/// file, with the operation in a third namespace that imports neither, refused the load
/// with the same location-less message — and loaded clean with that file deleted.
#[test]
fn a_let_bound_name_that_is_also_a_constructor_still_applies() {
    let mut kb = kb();
    assert_eq!(
        answer(&mut kb, "test.wi073gh.glet"),
        2,
        "`let f = λv. v + 1` then `f(n)`, beside `entity f`. The parameter half of this \
         ticket does NOT cover this row — `convert_term` had no binder frames at all"
    );
}

/// THE TICKET'S (d), BY VALUE: a callback parameter whose short name is also a nullary
/// constructor's is applied twice, and `twice(λv. v + 1, 1)` is 3.
///
/// Two applications of `g` in one body (`g(g(n))`) — the probe counted two raises here
/// against the one message the CLI printed, which is why this row is written on the
/// nested form rather than a single call.
#[test]
fn a_callback_parameter_named_after_a_constructor_applies() {
    let mut kb = kb();
    assert_eq!(
        answer(&mut kb, "test.wi073gh.gtwice"),
        3,
        "`twice(λv. v + 1, 1)` applies the parameter `g` twice, beside `entity g`"
    );
}

/// CONTROL — PASSES EITHER WAY, BY DESIGN, and in its own fixture so it can.
///
/// `keep(h) = h` with `entity h` declared beside it. A parameter in VALUE position is a
/// `Term::Ident`/`Ref` leaf that `rewrite_param_refs` matched by name under both the old
/// bare spelling and the new op-scoped one, and no field schema is consulted for a leaf.
/// It is here because it is the half of the ticket's (d) that was never broken: without
/// it, "an entity `h` beside a parameter `h`" would look like part of what moved.
#[test]
fn a_value_only_parameter_was_never_affected() {
    let mut kb = crate::common::load_kb_with(SRC_VALUE_ONLY);
    assert_eq!(
        answer(&mut kb, "test.wi073gh.valueonly.gkeep"),
        9,
        "`keep(9)` reads its parameter as a value, beside `entity h`; unmoved by this \
         change, and in its own fixture so that claim is measurable"
    );
}

/// ONE BINDER, ONE SYMBOL — the equation's own consistency, which the scope half broke
/// once and this row exists to keep.
///
/// `emit_operation_equation` lowers in `op_scope` now, and `binder_form_layout` puts a
/// binder's PATTERN at index 0, before `first_scoped`. The first cut therefore pushed the
/// frame over the scoped children only, leaving the pattern outside it — so in
/// `operation shadow(x: Int64) = let x = 100 <newline> x + 1` the BINDING occurrence
/// resolved to the operation's own `x` (the Param place) and `rewrite_param_refs`
/// substituted it, while the USE, inside the frame, stayed `intern("x")`:
///
/// ```text
///   broken: eq(shadow(?p), let_expr(pattern_var(?p), 100, add(x, 1)))
///   now:    eq(shadow(?p), let_expr(pattern_var(x),  100, add(x, 1)))
/// ```
///
/// A `let` body with a free name, in a rule SLD consults. The frame covers
/// `{pattern} ∪ [first_scoped..]` now — the `let` VALUE stays outside, which
/// `the_let_value_still_sees_the_enclosing_scope` is the other half of.
///
/// This walks the emitted equation rather than calling the operation, deliberately:
/// CALLING it answers 101 through eval's own lowering either way, so a value assertion
/// measures nothing here. Found by `/code-review`.
#[test]
fn a_shadowing_binder_binds_its_own_use_in_the_emitted_equation() {
    let mut kb = crate::common::load_kb_with(SRC_SHADOW);
    let (pattern_sym, use_sym) = shadow_equation_binder_symbols(&mut kb, "shadow");
    assert_eq!(
        pattern_sym, use_sym,
        "the `let`'s binding occurrence and its use must be ONE symbol; they were two \
         (the binding substituted to the parameter's var, the use left as `x`)"
    );
    assert_eq!(
        kb.local_name_of(pattern_sym),
        "x",
        "and that one symbol is the binder's own name, not the parameter it shadows"
    );
}

/// The other half of the layout rule: a `let`'s VALUE is outside the scope its own binder
/// opens, so `let y = n + 1` reads the PARAMETER `n` and not some `n` the pattern bound.
///
/// PASSES EITHER WAY under this ticket's own back-out, and is here for a different job:
/// it is the only row constraining the HOLE in `binder_form_layout`'s scoped set. Widen
/// the frame to every child and `shadow` — whose `let` value is the literal `100` — goes
/// on passing while this one has a value that must read the parameter. Stated as the
/// reason the fixture carries both operations, not as a measurement: the widened variant
/// was not built.
#[test]
fn the_let_value_still_sees_the_enclosing_scope() {
    let mut kb = crate::common::load_kb_with(SRC_SHADOW);
    let (pattern_sym, use_sym) = shadow_equation_binder_symbols(&mut kb, "reads_param");
    assert_eq!(
        pattern_sym, use_sym,
        "`let y = n + 1` then `y * 2`: the binder and its use are one symbol"
    );
    assert_eq!(kb.local_name_of(pattern_sym), "y");
}

/// THE TERM-POSITION HALF, AND THE SILENT ONE. A written functor that resolves to
/// NOTHING must not take the field schema of an entity that happens to share its short
/// name — and the harm is not the refusal, it is the quiet rewrite.
///
/// Before the gate, `fact holdsF(ff(1))` in a namespace that imports nothing was STORED
/// as `ff(a: 1)`, desugared under the declared fields of `Boxed.ff` — a DIFFERENT term
/// from the one written, which is exactly the never-match WI-433's desugar exists to
/// prevent. Each colliding row is asserted against its own control, which is the only
/// way to say "like any other undeclared name" rather than "loads":
///
/// ```text
///                        before   after    control (no entity of that name)
///   holdsF(ff(1))          0        1        holdsG(gg(1))      1
///   holdsF(ff(a: 1))       1        0        holdsG(gg(a: 1))   0
/// ```
///
/// The NAMED row is the discriminator: it matched only because the fact had been
/// silently renamed. The positional row is the other half of the same claim — without
/// it, "0 for the named spelling" is satisfied by the fact having vanished.
#[test]
fn a_stranger_entity_does_not_rename_a_written_terms_arguments() {
    let mut kb = crate::common::load_kb_with(SRC_STRANGER);
    crate::common::supply_invocation_imports(&mut kb, &["test.wi073gh.stranger.*"]);
    assert_eq!(
        stranger_hits(&mut kb, "holdsF(ff(1))"),
        1,
        "the fact was WRITTEN positionally and `ff` resolves to nothing here, so it is          stored positionally and the positional pattern finds it"
    );
    assert_eq!(
        stranger_hits(&mut kb, "holdsF(ff(a: 1))"),
        0,
        "THE DISCRIMINATOR: 1 before the gate, because the fact had been rewritten to          `ff(a: 1)` under the fields of an entity this namespace never imported"
    );
    assert_eq!(
        stranger_hits(&mut kb, "holdsG(gg(1))"),
        1,
        "CONTROL: `gg` matches no entity anywhere. Unmoved — and it is what makes the          two rows above a statement about the STRANGER rather than about `fact`"
    );
    assert_eq!(
        stranger_hits(&mut kb, "holdsG(gg(a: 1))"),
        0,
        "CONTROL, the other polarity. Unmoved"
    );
}

/// THE LOUD HALF OF THE SAME ROW, and the one place this ticket makes a message GO.
///
/// A 0-field stranger produced `constructor 'zz' given 1 positional argument(s) but has
/// 0 unfilled field(s)` — the very message this ticket started from, about a name the
/// citing namespace cannot resolve. It is the same defect as the silent rename above
/// (the plan answers `OverArity` instead of `Assign` when the stranger declares no
/// fields), so it goes the same way: `zz(1)` is now an ordinary undeclared term, exactly
/// like its control `qq(1)`.
///
/// THAT IS A LOUD ERROR BECOMING SILENT, which the repo does not do lightly, so the
/// reason is stated rather than assumed: the message was not about a real over-arity
/// application — `zz` denotes nothing at that site — and the identical program with the
/// functor spelled `qq` always loaded clean. The change makes the two agree; it does not
/// decide whether an undeclared functor in a FACT-HEAD ARGUMENT should be refused at
/// all. That is **WI-20260904-B8ESG**, which predates this ticket and owns the refusal:
/// WI-1058 refuses one in a rule BODY (measured, on both a colliding and a free
/// spelling) and nothing refuses one here. What this row changes for it is that `zz` and
/// `qq` are now equally silent — the accidental refusal of the colliding subset, loud
/// about the wrong thing, is gone — so its census runs over one population.
///
/// Backed out, `load_kb_with` panics on this fixture.
#[test]
fn a_zero_field_stranger_is_an_ordinary_undeclared_term() {
    let mut kb = crate::common::load_kb_with(SRC_STRANGER);
    crate::common::supply_invocation_imports(&mut kb, &["test.wi073gh.stranger.*"]);
    assert_eq!(
        stranger_hits(&mut kb, "holdsZ(zz(1))"),
        1,
        "`zz(1)` is stored as written. Before the gate this fixture did not LOAD: the          0-field stranger made it an over-arity constructor application"
    );
    assert_eq!(
        stranger_hits(&mut kb, "holdsQ(qq(1))"),
        1,
        "CONTROL: `qq` matches no entity anywhere and always loaded clean. It is what          says the row above is now ORDINARY rather than merely tolerated"
    );
}

/// CONTROL, AND THE ROW THAT SEPARATES THE TWO POSSIBLE FIXES: a genuine over-arity
/// CONSTRUCTOR application stays a LOUD load error.
///
/// This is the WI-20260827-T2470 backstop, driven at the two positions that reach it —
/// an OPERATION BODY (the path this ticket changed, written inside the sort body where
/// `f` really does resolve to the constructor) and a FACT term (the path it did not).
/// A repair that stopped checking constructor arity, or that let a body's functor skip
/// the field-schema question, would turn both of these green and nothing else in this
/// file would notice.
///
/// Passes either way, by design.
#[test]
fn an_over_arity_constructor_application_is_still_refused() {
    let in_op_body = crate::common::try_load_kb_with(
        r#"
namespace test.wi073gh.ctl1
  import anthill.prelude.{Int64}
  sort Bit
    entity t
    entity f
    operation bad(n: Int64) -> Bit = f(n)
  end
end
"#,
    );
    crate::common::assert_refused_naming(
        &in_op_body.err().unwrap_or_default(),
        &["constructor 'f'", "0 unfilled field"],
        "an over-arity constructor application in an OPERATION BODY",
    );

    let in_fact = crate::common::try_load_kb_with(
        r#"
namespace test.wi073gh.ctl2
  import anthill.prelude.{Int64}
  sort Bit
    entity t
    entity f
  end
  import test.wi073gh.ctl2.Bit.{f}
  fact holds(f(1))
end
"#,
    );
    crate::common::assert_refused_naming(
        &in_fact.err().unwrap_or_default(),
        &["constructor 'f'", "0 unfilled field"],
        "an over-arity constructor application in a FACT term",
    );
}

/// THE RULE-BODY HALF, MEASURED RATHER THAN ASSUMED — and it is not a capability.
///
/// The ticket asked that the fix "cover rule bodies too", reading the headline
/// measurement as if the user's own bodies were failing. They were not (see the module
/// doc). What a rule body CAN do with a §2.1 sigil-free clause parameter is read it as a
/// value — `rule_param_vars` shadows at both `Term::Ident` arms and that has worked since
/// WI-742. APPLYING one is refused, and this row is the measurement that it is refused
/// WHETHER OR NOT the name collides with a constructor:
///
/// ```text
///   rule r(g: (v: Int64) -> Int64, ?r) :- ?r <=> g(1)   beside `entity g`
///     → "constructor 'g' given 1 positional argument(s) …"      (misleading)
///   rule r(k: (v: Int64) -> Int64, ?r) :- ?r <=> k(1)   no collision
///     → "rule-body term `k` names nothing …"                    (the real diagnosis)
/// ```
///
/// So the collision costs a MESSAGE in a rule body, never an answer — there is no
/// higher-order goal to get wrong, because a functor position cannot hold a variable.
/// Both spellings are asserted refused rather than pinning the misleading text, so a
/// future ticket that either supports the application or repairs the message moves this
/// row deliberately instead of tripping over a frozen string.
///
/// Passes either way, by design.
#[test]
fn applying_a_rule_clause_parameter_is_refused_either_way() {
    let colliding = crate::common::try_load_kb_with(
        r#"
namespace test.wi073gh.ctl3
  import anthill.prelude.{Int64}
  sort Shape
    entity g
    operation plus1(v: Int64) -> Int64 = v + 1
  end
  rule apply2(g: (v: Int64) -> Int64, ?r) :- ?r <=> g(1)
end
"#,
    );
    assert!(
        colliding.is_err(),
        "applying a rule clause parameter whose name is also a constructor's must be \
         refused — the language has no higher-order goal"
    );

    let free = crate::common::try_load_kb_with(
        r#"
namespace test.wi073gh.ctl4
  import anthill.prelude.{Int64}
  sort Shape
    entity g
    operation plus1(v: Int64) -> Int64 = v + 1
  end
  rule apply2(k: (v: Int64) -> Int64, ?r) :- ?r <=> k(1)
end
"#,
    );
    crate::common::assert_refused_naming(
        &free.err().unwrap_or_default(),
        &["names nothing"],
        "the SAME rule with a parameter name no constructor takes — refused too, and \
         this is the refusal that names the real problem",
    );
}
