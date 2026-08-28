//! WI-20260827-T2470 — A POSITIONAL CONSTRUCTOR ARGUMENT IN AN OPERATION BODY BUILT A
//! VALUE THAT COMPARED UNEQUAL to the same constructor written anywhere else, so the
//! operation silently answered NOTHING.
//!
//! `finish_constructor` (`eval/eval.rs`) built `Entity{some, pos:[x], named:[]}` where
//! every other producer of the same constructor builds `Entity{some, pos:[],
//! named:[value: x]}`. Nothing then matched it: the four consumers that decide whether
//! two values are the same all key on the LITERAL shape — `unify_concrete`'s
//! `pa != pb || na != nb` fail-fast, `sem_eq_values`/`views_structurally_equal`, the
//! discrimination tree's `DiscrimKey`, and hash-consing. And the failure is a
//! REFUTATION rather than a suspension, so NAF over it PROVED the falsehood: `g5naf`
//! below answered 1 DEFINITE for `not(C.olit() = some(1))` while `g5` proved the
//! equation has a witness.
//!
//! ## FIVE BOUNDARIES, ONE RULE, AND TWO OF THEM WERE MISSING
//!
//! Positional→named desugar is not optional bookkeeping: it is the obligation carried
//! by every boundary where a USER-WRITTEN positional argument list crosses into a value
//! whose SHAPE IS ITS IDENTITY. There are five, and each of the first three already
//! cited WI-500/WI-433 for doing it:
//!
//! | boundary                                       | site                                   |
//! |------------------------------------------------|----------------------------------------|
//! | loader, fact/rule terms                        | `convert_term_with_expected` (`load.rs`) |
//! | loader, CLI query patterns                     | `load.rs` (WI-433)                     |
//! | runtime value → term                           | `alloc_from_value` (`execute.rs`), `value_to_term` (`node_occurrence.rs`) |
//! | case-arm PATTERN occurrences (WI-580 unfold)   | `fresh_pattern_occ` (`resolve.rs`)     |
//! | **evaluated operation body**                   | **`finish_constructor` (`eval/eval.rs`) — MISSING** |
//! | **unfold arm-body residual**                   | **`anf_flatten` (`resolve.rs`) — MISSING** |
//!
//! The last two are what this ticket adds, and they are TWO INDEPENDENT AXES reaching
//! two different execution paths — `finish_constructor` reaches every GROUND call,
//! `anf_flatten` reaches the UNGROUND case-split the WI-580 unfold expands. `gm` is the
//! only row that moves with `anf_flatten` alone; every other row moves with
//! `finish_constructor` alone. Both were measured by backing each out separately.
//!
//! NORMALIZING AT THE WRITER RATHER THAN THE READER is the design choice, and it is not
//! arbitrary: the readers listed above are four independent consumers, so teaching each
//! of them that `f(1)` and `f(x: 1)` denote one value is four places to drift. All six
//! writers route through the SINGLE owner `positional_to_named_plan`, whose
//! rank-among-NOT-named rule is therefore stated once. The obligation is NOT on every
//! application: it is exactly on functors that HAVE a declared field schema
//! (`entity_field_names(f).is_some()`) and are not reflect FORM meta-ctors. A predicate
//! goal, an operation call, a tuple, a list/set literal have no schema to normalize
//! against, and the plan Skips them.
//!
//! ## THE MEASURED TABLE
//!
//! Four states, each measured by neutralizing the `PositionalPlan::Assign` arm at one
//! or both sites. `(total, definite)`.
//!
//! ```text
//!                                          both OFF   eval only  anf only  both ON
//!                                          (before)                        (THIS CHANGE)
//!   g1   NAMED body, enum                  (1,1)      (1,1)      (1,1)     (1,1)
//!   g4   NAMED body, Option                (1,1)      (1,1)      (1,1)     (1,1)
//!   g6   positional BOTH SIDES, RULE body  (1,1)      (1,1)      (1,1)     (1,1)
//!   gpair `pair(1,2)`, carrier declares Eq (1,1)      (1,1)      (1,1)     (1,1)
//!        — the four rows unmoved in all four states, and the reason the workspace
//!          was green; `gpair` is why (see `a_carrier_with_a_declared_eq_masked_it`)
//!
//!   g2   POSITIONAL body, enum             (0,0)      (1,1)      (0,0)     (1,1)
//!   g5   POSITIONAL body, Option, literal  (0,0)      (1,1)      (0,0)     (1,1)
//!   gbox POSITIONAL body, plain sort       (0,0)      (1,1)      (0,0)     (1,1)
//!   glist POSITIONAL `cons(x, nil)`        (0,0)      (1,1)      (0,0)     (1,1)
//!   gtwo POSITIONAL, TWO fields            (0,0)      (1,1)      (0,0)     (1,1)
//!   gmix MIXED `two(2, a: 1)`              (0,0)      (1,1)      (0,0)     (1,1)
//!   gmg  case arm, GROUND scrutinee        (0,0)      (1,1)      (0,0)     (1,1)
//!   gopm the stdlib's own `optionMap`      (0,0)      (1,1)      (0,0)     (1,1)
//!   gopp the stdlib's own `optionPure`     (0,0)      (1,1)      (0,0)     (1,1)
//!   g5naf NAF over the refutation          (1,1)      (0,0)      (1,1)     (0,0)
//!        — the UNSOUNDNESS: a DEFINITE `not` over an equation with a witness
//!
//!   gm   case split, UNGROUND scrutinee    (0,0)      (0,0)      (1,1)     (1,1)
//!        — the ONLY row the `anf_flatten` half moves, and the only one it moves
//! ```
//!
//! ## THE CENSUS, AND WHY NOTHING FOUND IT
//!
//! Positional constructor applications in operation bodies, counted over each corpus'
//! loaded `op_bodies_iter` (excluding reflect FORM meta-ctors and schema-less functors,
//! i.e. exactly what `positional_to_named_plan` would `Assign`), on the tree at
//! `cf62b618`:
//!
//! ```text
//!   stdlib/anthill                                        49
//!   + rustland/{anthill-cli,anthill-todo,anthill-cpp-gen} 202
//!   + examples/webots-modelling                           53  (+4)
//!   + examples/{github-todo,guardians,sql-store,classic-mini}, anthill-testcases
//!                                                         49  (+0)
//! ```
//!
//! `anthill.prelude.Option.optionPure` (`= some(a)`) and `anthill.prelude.Option.optionMap`
//! (`case some(x) -> some(f(x))`) are BOTH the broken spelling, and they back
//! `provides Monad[M = Option, pure = optionPure, …, map = optionMap]` — so `Monad[Option]`'s
//! `pure` built a value nothing could match. BOTH ARE REACHABLE TODAY, which `gopp` and
//! `gopm` prove by calling them and comparing the result: each answered (0,0) before and
//! (1,1) after. `List.headOption`, `List.nth`, `Stream.find`, `MutableStack.pop` and the
//! rest of the 49 are the same shape.
//!
//! The workspace was nonetheless green, for TWO reasons and it takes both:
//!   * the operation bodies exercised by tests mostly use NAMED arguments; and
//!   * where they do not, the carrier often declares its own `eq`, which MASKS the
//!     divergence completely — `sem_eq_values` dispatches to the declared equality
//!     instead of comparing structurally, and a declared `eq` reads fields by NAME
//!     through `project_field`, which handles both spellings. `Pair` is exactly this
//!     (`gpair` is (1,1) in all four states) and `Option` is not (`g5` is the defect).
//!
//! ## THE READER POPULATION, WHICH IS THE OTHER HALF OF A SPELLING CHANGE
//!
//! Changing what a producer BUILDS reaches everything that READS it, and two Rust-side
//! readers in the test tree destructured `Value::Entity { pos, .. }` directly:
//! `cli_parse_test` (`parse_ok`/`ParsedArgs`/`Binding` payloads) and
//! `wi733_relation_head_eval_test`'s `some_string`. Both went red here, and both were
//! reading a shape rather than a field.
//!
//! The repair is NOT "read `named` instead" — that is the same fault with the other
//! branch taken. One entity reaches a reader on any of three carriers (`Value::Entity`,
//! a hash-consed `Value::Term`, a `Value::Node`), and a leaf `String` on the same three,
//! so an enum match lets the RECEIVER'S CARRIER decide whether its own field is
//! reachable — the bug `project_field` exists to prevent. Both now go through
//! `common::entity_field` / `entity_functor` / `scalar_str`, which read via `TermView`,
//! ask NAME first and positional rank second, and live in ONE place rather than a copy
//! per suite. MEASURED: with this ticket's change backed out both suites stay GREEN,
//! which is the property that says they no longer depend on which spelling the producer
//! chose.
//!
//! ## THE NEIGHBOUR THIS DOES NOT MAKE DEAD
//!
//! `project_field`'s POSITIONAL branch (`resolve.rs`) reads a field off an entity whose
//! args are still in `pos`. Its comment justified itself by "`finish_constructor` does
//! not desugar", which this change makes false — but the branch stays LIVE and is not
//! narrowed here: a `Value::Entity` can still be built positionally in Rust by a host
//! builtin or a reflect bridge without passing through `finish_constructor` at all.
//! MEASURED by neutralizing it and running the whole `anthill-core` suite: EXACTLY ONE
//! test goes red, `field_access_projects_a_value_carried_entity_receiver`, which
//! hand-builds `Point(7)`. So the branch has one witness, and it is a unit test rather
//! than a program — both comments were re-worded to say that, rather than to cite a
//! producer that no longer produces it.
//!
//! (An earlier draft of this note claimed the two `wi733` rows redden with the branch
//! off. They do not: that measurement was taken with this ticket's own fix live and its
//! reader repair not yet made, so it was reading THIS change's regression and crediting
//! the branch.)
//!
//! ## THE ADJACENT DEFECT THIS DOES NOT FIX
//!
//! `gpat`/`gpat0` below are asserted at their CURRENT (wrong) values on purpose. A mixed
//! constructor PATTERN uses a different rule from a mixed constructor APPLICATION: the
//! application `two(2, a: 1)` puts 2 in `b` (rank among NOT-named — `gmix`, fixed here),
//! while the pattern `case two(y, a: 1)` gives `y` field `a`, collides with the named
//! `a: 1`, and silently does not match, so a later arm answers instead. That is
//! WI-20260827-1F0QP, which must flip `gpat` to (1,1) and `gpat0` to (0,0).

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// `(total, definite)`. Both halves are needed: this ticket is about a DECIDED-FALSE
/// (`total 0`) appearing where a definite answer is correct, and the NAF row turns on
/// telling that apart from a suspension (`total > 0, definite 0`).
fn counts(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let def = sols.iter().filter(|s| s.is_definite()).count();
    (sols.len(), def)
}

/// FOUR CARRIERS AND ONE AXIS. Every row here differs from its twin in NOTHING but the
/// POSITIONAL vs NAMED spelling of a constructor argument inside an OPERATION BODY:
/// same carrier, same `Int64` payload, no `eq` override on `MyEnum`/`BoxI`/`Two`/`Option`.
///
/// `MyEnum` is a user `enum`, `BoxI` a plain one-constructor sort, `Two` a TWO-field
/// entity (so the rank-among-not-named rule has something to get wrong), `Option` and
/// `List` the prelude's own. `Pair` is the CONTROL CARRIER: it declares `PartialEq`, so
/// `sem_eq_values` dispatches instead of comparing structurally and the defect is
/// invisible on it — the shape that kept the workspace green.
const SRC: &str = r#"
enum test.t2470.MyEnum
  sort T = ?
  entity enone
  entity esome(value: T)
end
namespace test.t2470
  import anthill.prelude.{Int64, Option, List, Pair}
  import anthill.prelude.Option.{some, optionMap, optionPure}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Pair.{pair}
  import test.t2470.MyEnum.{esome}
  sort BoxI
    entity boxi(v: Int64)
  end
  sort Two
    entity two(a: Int64, b: Int64)
  end
  sort C
    entity red
    entity green
    operation ewrap (x: Int64) -> MyEnum[T = Int64] = esome(value: x)   -- NAMED
    operation ewrap2(x: Int64) -> MyEnum[T = Int64] = esome(x)          -- POSITIONAL
    operation owrapn(x: Int64) -> Option[T = Int64] = some(value: x)    -- NAMED
    operation olit  ()         -> Option[T = Int64] = some(1)           -- POSITIONAL
    operation bwrap (x: Int64) -> BoxI = boxi(x)
    operation lwrap (x: Int64) -> List[T = Int64] = cons(x, nil)
    operation twoPos()         -> Two = two(1, 2)
    operation twoMix()         -> Two = two(2, a: 1)   -- MIXED: 2 fills `b`
    operation pwrap ()         -> Pair[A = Int64, B = Int64] = pair(1, 2)
    -- the stdlib's own two broken spellings, called
    operation inc(x: Int64) -> Int64 = x
    operation omap () -> Option[T = Int64] = optionMap(some(value: 1), inc)
    operation opure() -> Option[T = Int64] = optionPure(1)
    -- WI-20260827-1F0QP: a MIXED constructor PATTERN, which reads the same spelling
    -- `twoMix` writes and disagrees with it. Asserted at its CURRENT value below.
    operation punmix(t: Two) -> Int64 =
      match t
        case two(y, a: 1) -> y
        case two(p, q) -> 0
    -- the case-split: reached by eval when the scrutinee is GROUND and by the WI-580
    -- unfold (`anf_flatten`) when it is not, which is why `gmg` and `gm` differ
    operation mpick(c: C) -> Option[T = Int64] =
      match c
        case red() -> some(1)
        case green() -> some(2)
  end
  rule g1(1)    :- C.ewrap(1)  = esome(value: 1)
  rule g2(1)    :- C.ewrap2(1) = esome(value: 1)
  rule g4(1)    :- C.owrapn(1) = some(value: 1)
  rule g5(1)    :- C.olit()    = some(1)
  rule g6(1)    :- some(1)     = some(1)
  rule g5naf(1) :- not(C.olit() = some(1))
  rule gbox(1)  :- C.bwrap(3)  = boxi(v: 3)
  rule glist(1) :- C.lwrap(4)  = cons(head: 4, tail: nil)
  rule gtwo(1)  :- C.twoPos()  = two(a: 1, b: 2)
  rule gmix(1)  :- C.twoMix()  = two(a: 1, b: 2)
  rule gpair(1) :- C.pwrap()   = pair(fst: 1, snd: 2)
  rule gopm(1)  :- C.omap()    = some(value: 1)
  rule gopp(1)  :- C.opure()   = some(value: 1)
  rule gpat(1)  :- C.punmix(two(a: 1, b: 7)) = 7
  rule gpat0(1) :- C.punmix(two(a: 1, b: 7)) = 0
  rule gmg(1)   :- C.mpick(red()) = some(1)
  rule gm(?c)   :- C.mpick(?c)    = some(1)
end
"#;

fn kb() -> KnowledgeBase {
    crate::common::load_kb_with(SRC)
}

/// THE TICKET'S FIVE ROWS, WITH `g6` AS THE CONTROL THAT LOCATES THE DEFECT.
///
/// BACK OUT the `finish_constructor` desugar and `g2` and `g5` are (0, 0) — a DEFINITE
/// REFUTATION of an equation whose named twin one line above proves. `g1`, `g4` and `g6`
/// pass either way, by design, and `g6` is the one that matters: written in a RULE body,
/// `some(1) = some(1)` is true, because the LOADER canonicalized both sides. So the
/// positional SPELLING is not the defect — only a value BUILT BY AN OPERATION BODY from
/// positional arguments mismatched.
#[test]
fn a_positional_constructor_in_an_operation_body_builds_the_canonical_value() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.t2470.g1(1)"),
        (1, 1),
        "CONTROL: a NAMED constructor argument in an operation body always worked. \
         Unmoved by this change"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.g2(1)"),
        (1, 1),
        "THE DEFECT, on a user `enum`: the SAME operation with its argument written \
         POSITIONALLY. (0, 0) with the `finish_constructor` desugar backed out"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.g4(1)"),
        (1, 1),
        "CONTROL, on the prelude's `Option`. Unmoved"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.g5(1)"),
        (1, 1),
        "THE DEFECT on `Option`, with a LITERAL argument rather than a parameter — so \
         no binder is involved either. (0, 0) backed out"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.g6(1)"),
        (1, 1),
        "THE CONTROL THAT LOCATES IT: positional on BOTH sides of a RULE body is fine, \
         because the loader canonicalizes a rule term. (1, 1) in all four states — the \
         defect is the OPERATION BODY, not the spelling"
    );
}

/// THE POLARITY THAT MAKES IT UNSOUND RATHER THAN MERELY INCOMPLETE.
///
/// The operation did not SUSPEND, it was REFUTED — `total 0`, not `definite 0` — and NAF
/// concludes from an empty search. So a caller could PROVE `not(C.olit() = some(1))`
/// while `g5` proves the equation has a witness. THIS TEST GOES RED on a back-out:
/// `g5naf` is (1, 1) there, a DEFINITE `not` of a true equation.
#[test]
fn naf_over_the_refutation_no_longer_proves_a_falsehood() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.t2470.g5naf(1)"),
        (0, 0),
        "`not(C.olit() = some(1))` must FAIL, since `g5` proves the equation. (1, 1) — a \
         DEFINITE proof of a falsehood — with the `finish_constructor` desugar backed out"
    );
}

/// NOT ABOUT `Option`, NOT ABOUT `enum`, NOT ABOUT ARITY, AND NOT ABOUT EQUALITY.
/// Every row is (0, 0) before and (1, 1) after; none has an `eq` override anywhere.
///
/// `gmix` is the row that DRIVES the rank rule rather than only the pos/named split:
/// `two(2, a: 1)` must put 2 in `b`, the field not already given by name. A repair that
/// filled the LEADING fields instead would put 2 in `a`, collide, and this row would
/// stay red while every single-field row above went green.
#[test]
fn every_declared_entity_shape_reaches_the_canonical_form() {
    let mut kb = kb();
    for (q, why) in [
        ("gbox", "a plain one-constructor sort, one field"),
        ("glist", "the prelude's `List`: `cons(x, nil)`"),
        ("gtwo", "TWO positional fields"),
        (
            "gmix",
            "MIXED: `two(2, a: 1)` — 2 must fill `b`, the field NOT given by name. This \
             is the row that drives the rank-among-not-named rule",
        ),
    ] {
        assert_eq!(
            counts(&mut kb, &format!("test.t2470.{q}(1)")),
            (1, 1),
            "{q}: {why}. (0, 0) with the `finish_constructor` desugar backed out"
        );
    }
}

/// THE STDLIB'S OWN TWO BROKEN SPELLINGS, DRIVEN — the ticket's "whether either is
/// reachable today", answered by CALLING them rather than by reading the source.
///
/// `optionPure` is `= some(a)` and `optionMap`'s live arm is `some(f(x))`; both back
/// `provides Monad[M = Option, pure = optionPure, …, map = optionMap]`. Both are (0, 0)
/// with the `finish_constructor` desugar backed out — so `Monad[Option]`'s `pure` built
/// a value nothing in the language could match, and the corpus never noticed. 49 sites
/// in `stdlib/anthill` are this shape (module doc).
#[test]
fn the_stdlib_option_monad_builds_a_matchable_value() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.t2470.gopp(1)"),
        (1, 1),
        "`optionPure(1)` must equal `some(value: 1)`. (0, 0) backed out"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.gopm(1)"),
        (1, 1),
        "`optionMap(some(value: 1), inc)` likewise — its arm body is `some(f(x))`. \
         (0, 0) backed out"
    );
}

/// THE SECOND AXIS: `anf_flatten`, the WI-580 unfold's ARM-BODY residual.
///
/// The two rows are the SAME operation and differ only in whether the scrutinee is
/// GROUND. Ground, eval reduces the call and `finish_constructor` decides it; unground,
/// the unfold expands one continuation per `match` arm and asserts `unify(residualᵢ,
/// OTHER)` — and the residual is built by `anf_flatten`, which had its own copy of the
/// gap. `unify` is structural by construction, so a positional residual against a named
/// OTHER failed EVERY arm and the goal was decided FALSE.
///
/// THE TWO AXES ARE SEPARATE AND EACH WAS BACKED OUT ALONE. `gm` is (0, 0) with only
/// `finish_constructor` fixed and (1, 1) with only `anf_flatten` fixed; every other row
/// in this file is the exact opposite. Neither fix subsumes the other.
#[test]
fn the_unfold_arm_body_residual_is_canonical_too() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.t2470.gmg(1)"),
        (1, 1),
        "GROUND scrutinee — eval's path. (0, 0) with `finish_constructor` backed out, \
         (1, 1) whatever `anf_flatten` does"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.gm(?c)"),
        (1, 1),
        "UNGROUND scrutinee — the unfold's path, and the ONLY row that measures the \
         `anf_flatten` half. (0, 0) with that arm backed out, even with \
         `finish_constructor` fixed"
    );
    assert_eq!(
        crate::common::query_unary(&mut kb, "test.t2470.gm")
            .into_iter()
            .filter(|(_, d)| *d)
            .count(),
        1,
        "and it DECIDES: exactly one arm (`red`) yields `some(1)`, so the case-split \
         must commit rather than suspend"
    );
}

/// THE CONTROL CARRIER, AND THE REASON THE WORKSPACE WAS GREEN.
///
/// `Pair` declares `PartialEq`, so `sem_eq_values` DISPATCHES to the declared equality
/// instead of taking the structural verdict, and a declared `eq` reads its operands'
/// fields by NAME through `project_field` — which handles the positional spelling. So
/// `gpair` is (1, 1) in ALL FOUR states while the structurally-compared `Option` twin
/// (`g5`) is the defect. A fixture built only from `eq`-declaring carriers would have
/// measured nothing at all.
///
/// This row is also the guard against the fix DISTURBING a carrier it should not touch.
#[test]
fn a_carrier_with_a_declared_eq_masked_it() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.t2470.gpair(1)"),
        (1, 1),
        "`pair(1, 2)` vs `pair(fst: 1, snd: 2)`: (1, 1) in all four states, because \
         `Pair` declares `PartialEq` and the compare never reaches the structural \
         verdict. Unmoved by this change"
    );
}

/// A TUPLE AND A LIST LITERAL KEEP THEIR POSITIONAL SHAPE — the control for the one way
/// this fix could do real damage.
///
/// `positional_to_named_plan` returns `Skip` for `ListLiteral` / `SetLiteral` /
/// `TupleLiteral` (reflect FORM meta-ctors, whose positional shape IS the encoding) and
/// for any functor with no declared field schema. A tuple's positional ORDER IS ITS
/// IDENTITY (kernel-language.md §"named tuples"), so desugaring one would not merely
/// reorder it but change what it denotes.
///
/// This test passes both with and without the change and says so: it is a GUARD, not a
/// measurement of it. Written because the fix sits three lines above the arm that builds
/// `Value::Tuple`, and nothing else in this file would notice.
#[test]
fn a_tuple_and_a_list_literal_keep_their_positional_shape() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.t2470b
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{cons, nil}
  sort D
    entity dd
    operation fst1() -> Int64 = (1, 2)._1
    operation snd1() -> Int64 = (1, 2)._2
    operation lst() -> List[T = Int64] = [1, 2]
  end
  rule gt1(1) :- D.fst1() = 1
  rule gt2(1) :- D.snd1() = 2
  rule gtx()  :- D.fst1() = 2
  rule gl(1)  :- D.lst() = cons(head: 1, tail: cons(head: 2, tail: nil))
end
"#,
    );
    assert_eq!(
        counts(&mut kb, "test.t2470b.gt1(1)"),
        (1, 1),
        "a positional tuple literal BUILT IN AN OPERATION BODY — so `finish_constructor` \
         built it — still has 1 at component `_1`"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470b.gt2(1)"),
        (1, 1),
        "and 2 at `_2`. The two rows read together are what pin the ORDER, which for a \
         tuple IS its identity"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470b.gtx()"),
        (0, 0),
        "THE DISAGREEING VALUE, without which the two rows above are satisfied by a \
         tuple that lost its order entirely: component `_1` is NOT 2"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470b.gl(1)"),
        (1, 1),
        "a list literal's positional args are its ELEMENTS, not fields; \
         `build_list_value` must still see them"
    );
}

/// WI-20260827-1F0QP, PINNED AT ITS CURRENT (WRONG) VALUE so that ticket has a row to
/// flip and so the divergence is not rediscovered.
///
/// `C.twoMix()` writes `two(2, a: 1)` as an APPLICATION and this change makes it mean
/// `two(a: 1, b: 2)` (`gmix`, above). `C.punmix` reads the SAME spelling as a PATTERN,
/// `case two(y, a: 1)`, and gives `y` the LEADING field `a` — which the named `a: 1` has
/// already taken — so the arm silently does not match and the fallthrough answers 0.
///
/// The two sides use two different rules; this ticket fixes only the application side.
/// Asserted here as CURRENT BEHAVIOUR, not as correct behaviour.
#[test]
fn a_mixed_constructor_pattern_still_disagrees_with_a_mixed_application() {
    let mut kb = kb();
    assert_eq!(
        counts(&mut kb, "test.t2470.gmix(1)"),
        (1, 1),
        "the APPLICATION `two(2, a: 1)` means `two(a: 1, b: 2)` — rank among the fields \
         NOT given by name"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.gpat(1)"),
        (0, 0),
        "but the PATTERN `case two(y, a: 1)` does not match `two(a: 1, b: 7)` at all. \
         WI-20260827-1F0QP must make this (1, 1)"
    );
    assert_eq!(
        counts(&mut kb, "test.t2470.gpat0(1)"),
        (1, 1),
        "and it loses SILENTLY: the next arm answers 0 where the program says 7. \
         WI-20260827-1F0QP must make this (0, 0)"
    );
}
