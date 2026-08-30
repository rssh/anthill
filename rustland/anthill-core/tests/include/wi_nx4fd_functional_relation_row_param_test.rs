//! WI-20260830-NX4FD — the ARITY+1 functional-relation view answers for a SPEC
//! OPERATION whose declared effect row is entirely PARAMETERS, where before it
//! answered NOTHING.
//!
//! `size(?ls, ?n)` is `anthill.prelude.FiniteCollection.size(c: C) -> Int64 effects E
//! = List.length(collect(c))`, reached through `List`'s provision; `length(?ls, ?n)`
//! is `List`'s own. Both are rule-less bodied operations at arity+1 over the same
//! `List`, and only the second answered — the first came back `[]`, which a goal with
//! no clauses is indistinguishable from.
//!
//! TWO HALVES, each measured and each with its own row here. WI-20260830-DQD5W fixed
//! the arity+0 `Bool` view and left this one, recording the reason in
//! `functional_relation_arity`'s own doc; both of that note's measurements are
//! re-measured here and ONE OF THEM HAD GONE STALE.
//!
//!   1. **The effect clause.** `functional_relation_arity` read `!sig.effects.
//!      is_empty()` where its `Bool` sibling reads `effect_row_admits_relational_
//!      view` — the row's MEMBERS rather than its length. `effects E` on a sort
//!      declaring `effects E = ?` is a one-member row that names no effect; `List`
//!      instantiates it to `{}`. One line, and it is what
//!      `a_parametric_row_op_whose_chain_needs_nothing_binds` measures.
//!
//!   2. **The SORT half of `resolve_bridge_requirements`.** With (1) in, the hook
//!      FIRES and the bridge then suspended one level down: `FiniteCollection
//!      requires Iterable[C = C, Element = Element, E = E]`, of which the argument
//!      `c: C` pins only `C`. The `all_pinned` gate returned `Unresolvable` for the
//!      whole call. It now completes an open element from a SOLE provider (WI-1091's
//!      op-half precedent, `unique_provider_completion`) and, where that leaves no
//!      unique answer, KEEPS THE SLOT as a recorded absence
//!      (`ResolvedRequiresNode::Unavailable`) instead of aborting.
//!
//!      The second arm is the compile-time producer's OWN answer, which is the whole
//!      argument for it: `Unavailable`'s doc names THIS EXACT SLOT as the shape the
//!      stdlib relies on it for — "`FiniteCollection requires Iterable[C = C]` holds
//!      for a `List` carrier only through `List provides Stream provides Iterable`,
//!      which no `Iterable[C = List[…]]` provision matches … Refusing to build the
//!      dictionary there would reject every program that dispatches such a spec op
//!      without ever reading the evidence (MEASURED: 33 tests)". The typer placed a
//!      marker and ran; the bridge refused and the same call answered nothing.
//!
//! **THE TICKET'S SECOND OBJECTION DID NOT REPRODUCE, and it is corrected rather
//! than inherited.** `functional_relation_arity`'s doc said that widening (1) makes
//! `Iterable.isEmpty(?ls, ?r)` — a chain that IS pinnable — answer "ONE **DEFINITE**
//! solution with `?r` still a free `Var`, over two Boxes whose true answers are
//! `true` and `false`". RE-MEASURED WITH (1) ALONE APPLIED: it answers TWO definite
//! solutions, `Bool(true)` and `Bool(false)`, correctly one per Box. That symptom —
//! one definite solution with the result column free — is verbatim the UN-GATED
//! `Bool` hook's, which DQD5W's own arity gate (`declared_arity == pos_arity +
//! named_arity`, driven by `an_arity_mismatched_bool_goal_takes_the_functional_
//! relation_view`) closed in the same commit. The objection was measured before that
//! gate landed and expired with it; `a_parametric_row_op_whose_chain_needs_nothing_
//! binds` is the row that says so.
//!
//! WHAT FAILS WHEN EACH HALF IS BACKED OUT — measured, not predicted:
//!
//!   * back out (1) alone (restore `if !sig.effects.is_empty() { return None }` in
//!     `functional_relation_arity`): `spec_op_arity_plus_one_goal_binds_its_result`
//!     and `a_parametric_row_op_whose_chain_needs_nothing_binds` fail — both goals
//!     answer `[]`, the ticket's symptom verbatim.
//!   * back out (2)'s COMPLETION arm alone (guard `unique_provider_completion` with
//!     `if op_half`): `an_under_determined_sort_half_slot_completes_from_a_sole_
//!     provider` fails alone — `G.twice(?a, ?r)` answers `[]`, because the slot gets
//!     a marker and the body READS it. The `size` row is unmoved: its `Iterable`
//!     slot has no unique completion either way and always took the marker.
//!   * back out (2)'s MARKER arm alone (make the `None if !op_half` arm return
//!     `Unresolvable` instead of pushing the node):
//!     `spec_op_arity_plus_one_goal_binds_its_result` fails alone.
//!   * back out (2) WHOLE — restore the original `if !all_pinned && !op_half {
//!     return Unresolvable }` — and BOTH of those fail, because that return stood
//!     BEFORE the completion point and so disabled both arms at once. Named because
//!     it is the back-out a reader reaches for first, and it does not attribute:
//!     only the two narrower ones separate the arms.
//!
//! CONTROLS — each passes with either half backed out, each here because it is what
//! the widening could plausibly have broken:
//!
//!   * `carriers_own_operation_still_binds` — `List.length` at arity+1, the row the
//!     ticket names as working today. If it moved, the change reached past the
//!     parametric-row class.
//!   * `a_concretely_effectful_op_is_still_refused_at_arity_plus_one` — a bodied
//!     operation declaring a REAL effect keeps its zero, beside a byte-identical
//!     pure twin that answers. This is the row that says the gate was WIDENED and
//!     not DELETED; a single refused operation is also what an un-drivable fixture
//!     produces.
//!   * `an_unground_receiver_still_suspends` — WI-580 §5's sound CHECKER, not a
//!     generator.
//!   * `an_under_determined_slot_with_no_completion_answers_nothing` — the SOUNDNESS
//!     row. A slot the arguments do not pin and no provider completes gets a marker,
//!     the body's read is refused, and the goal answers `[]`. It answered `[]` before
//!     this ticket too (the whole call was `Unresolvable`); what it says is that the
//!     widening did not trade that honest zero for a definite-looking wrong one,
//!     which is exactly what kernel-language.md §5.3 warns about for this view.

use anthill_core::eval::Value;

use crate::common::{definite_unary, load_kb_with, query_unary};

/// One file, one `List`, two `Box`es of DIFFERENT length, and the spec op beside the
/// carrier's own operation at the same arity. Two rows rather than one so a predicate
/// that answered a constant fails as loudly as one that answered nothing.
const SRC: &str = r#"
namespace nx4fd
  import anthill.prelude.{List, String, Bool, Int64}
  import anthill.prelude.List.{length}
  import anthill.prelude.FiniteCollection.{size}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])
  fact Box(items: [])

  rule own_len(?n)  :- Box(items: ?ls), length(?ls, ?n)
  rule spec_len(?n) :- Box(items: ?ls), size(?ls, ?n)
end
"#;

/// The definite `Int64` answers of a unary rule, sorted — the goal enumerates two
/// `Box`es and their order is not this ticket's subject.
fn ints(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<i64> {
    let mut got: Vec<i64> = definite_unary(kb, qn)
        .iter()
        .map(|v| match v {
            Value::Int(i) => *i,
            other => panic!("{qn}: expected an Int column, got {other:?}"),
        })
        .collect();
    got.sort_unstable();
    got
}

/// THE ACCEPTANCE ROW. `size(?ls, ?n)` must BIND `?n` to each `Box`'s length, exactly
/// as `length(?ls, ?n)` does — the ticket's own fixture, with the empty `Box` added so
/// the two answers DISAGREE and a constant cannot pass.
///
/// Both halves are required: back out either and this answers `[]`.
#[test]
fn spec_op_arity_plus_one_goal_binds_its_result() {
    let mut kb = load_kb_with(SRC);
    let own = ints(&mut kb, "nx4fd.own_len");
    assert_eq!(
        own,
        vec![0, 2],
        "the CONTROL first: `length(?ls, ?n)` is List's own operation and bound its \
         result before this ticket — if it moved, the row below measures something \
         other than the spec-op route"
    );
    let spec = ints(&mut kb, "nx4fd.spec_len");
    assert_eq!(
        spec, own,
        "`size(?ls, ?n)` is `FiniteCollection`'s bodied operation over a row \
         PARAMETER, reached through List's provision; at arity+1 it must bind the \
         same two lengths its carrier's own operation does. `[]` here is the \
         ticket's symptom — a goal with no clauses, which is FALSE rather than an \
         error"
    );
}

/// ATTRIBUTES HALF (1), THE EFFECT CLAUSE — and re-measures the ticket's own
/// counter-example, which did not reproduce (see the module doc).
///
/// `Iterable.isEmpty(c: C) -> Bool effects E` is the parametric-row shape whose CHAIN
/// needs nothing from half (2): `Iterable`'s only requirement is the `EffectsRuntime`
/// kind-anchor, which DQD5W already made a structural leaf. So this row moves with
/// the effect clause ALONE — it fails when that is backed out and passes when only
/// the sort half is.
///
/// Driven in BOTH polarities over two `Box`es whose true answers DISAGREE, because
/// the failure the ticket predicted is a result column left FREE: a row asserting
/// only a solution COUNT is green for that, and a row over one `Box` cannot tell a
/// bound `true` from a predicate that answers `true` for everything.
#[test]
fn a_parametric_row_op_whose_chain_needs_nothing_binds() {
    let src = r#"
namespace nx4fd_f
  import anthill.prelude.{List, String, Bool}
  import anthill.prelude.Iterable.{isEmpty}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])
  fact Box(items: [])

  rule flag(?r) :- Box(items: ?ls), isEmpty(?ls, ?r)
end
"#;
    let mut kb = load_kb_with(src);
    let got = definite_unary(&mut kb, "nx4fd_f.flag");
    let mut bools: Vec<bool> = got
        .iter()
        .map(|v| match v {
            Value::Bool(b) => *b,
            other => panic!(
                "`isEmpty(?ls, ?r)` must BIND `?r` to a Bool; a free `Var` here is \
                 the un-gated Bool hook reporting an answer it never computed. Got \
                 {other:?}"
            ),
        })
        .collect();
    bools.sort_unstable();
    assert_eq!(
        bools,
        vec![false, true],
        "the two `Box`es must get DIFFERENT answers — one is empty and one is not. \
         `[]` is the effect clause backed out; a single answer, or two equal ones, \
         is a predicate that decided nothing. Got {got:?}"
    );
}

/// ATTRIBUTES HALF (2)'s COMPLETION ARM. A SORT-level `requires` whose spec has an
/// element NO argument type pins — `G requires VectorSpace[V, F]` with `twice(a: V)`
/// — is WI-1091's shape one chain-half over: `V := Vec3` comes from the argument and
/// `F` appears in no parameter, so the slot was `Unresolvable` and the whole call
/// died.
///
/// `Vec3` has exactly one `VectorSpace` provision, so the open `F` has exactly one
/// answer and `unique_provider_completion` may take it — "exact rather than lenient",
/// the argument WI-1091 makes for the op half. This is a CAPABILITY row: it asserts
/// the DOUBLED VECTOR, not that anything loaded.
///
/// WHAT FAILS WHEN BACKED OUT (guard the completion with `if op_half`): this alone —
/// the slot falls to the marker arm, `VectorSpace.vec_add(a, a)` READS it,
/// `marker_refusal` refuses, and the goal answers `[]`.
#[test]
fn an_under_determined_sort_half_slot_completes_from_a_sole_provider() {
    let src = r#"
namespace nx4fd_vs
  import anthill.geometry.{Vec3}
  import anthill.prelude.{Float}
  import anthill.prelude.algebra.{VectorSpace}

  sort G
    sort V = ?
    sort F = ?
    requires VectorSpace[V, F]
    operation twice(a: V) -> V = VectorSpace.vec_add(a, a)
  end

  sort Holder
    entity Holder(v: Vec3)
  end
  fact Holder(v: Vec3(x: 1.0, y: 2.0, z: 3.0))

  rule doubled(?r) :- Holder(v: ?a), G.twice(?a, ?r)
end
"#;
    let mut kb = load_kb_with(src);
    let got = definite_unary(&mut kb, "nx4fd_vs.doubled");
    assert_eq!(
        got.len(),
        1,
        "`G.twice(?a, ?r)` must answer once — `[]` is the sort half refusing a slot \
         `Vec3`'s sole `VectorSpace` provision decides. Got {got:?}"
    );
    let Value::Entity { named, .. } = &got[0] else {
        panic!("expected a Vec3 entity, got {:?}", got[0]);
    };
    let read = |label: &str| -> f64 {
        named
            .iter()
            .find(|(sym, _)| kb.local_name_of(*sym) == label)
            .map(|(_, v)| match v {
                Value::Float(f) => *f,
                other => panic!("field `{label}` is not a Float: {other:?}"),
            })
            .unwrap_or_else(|| panic!("no field `{label}` on {:?}", got[0]))
    };
    assert_eq!(
        (read("x"), read("y"), read("z")),
        (2.0, 4.0, 6.0),
        "the completed dictionary must reach `Vec3`'s own `vec_add` and DOUBLE the \
         vector — a solution that merely exists says nothing about which provider \
         the slot was filled from"
    );
}

/// CONTROL — THE SOUNDNESS ROW, and it passes with either half backed out.
///
/// The same sort-level shape as above at a carrier that provides NO `VectorSpace` at
/// all: nothing pins `F` and no provider completes it, so the slot gets the recorded
/// absence and the body's `VectorSpace.vec_add` read is REFUSED. The goal answers
/// `[]`.
///
/// It answered `[]` before this ticket too — the whole call was `Unresolvable`, which
/// suspends. That is the point: the marker arm widened what a call may RUN with, and
/// this says it did not widen what a call may ANSWER. A definite-looking wrong answer
/// here is exactly what kernel-language.md §5.3 warns about for the arity+1 view, and
/// what the ticket predicted (wrongly, on a different fixture) would happen.
#[test]
fn an_under_determined_slot_with_no_completion_answers_nothing() {
    let src = r#"
namespace nx4fd_no
  import anthill.prelude.{Int64}
  import anthill.prelude.algebra.{VectorSpace}

  sort Blob
    entity blob(n: Int64)
  end

  sort G2
    sort V = ?
    sort F = ?
    requires VectorSpace[V, F]
    operation twice(a: V) -> V = VectorSpace.vec_add(a, a)
  end

  fact mark(1)
  rule doubled(?r) :- mark(?m), G2.twice(blob(n: 1), ?r)
end
"#;
    let mut kb = load_kb_with(src);
    let all = query_unary(&mut kb, "nx4fd_no.doubled");
    assert!(
        all.iter().all(|(_, definite)| !definite),
        "a slot nothing pins and nothing completes must not produce a DEFINITE \
         answer — the body reads the requirement, and a dictionary guessed for it \
         would be the wrong one. Got {all:?}"
    );
}

/// CONTROL — `List.length` at arity+1: a bodied, effect-FREE operation, which took
/// this view before the ticket and must keep it. Passes either way; it is here so a
/// regression in `length` is attributed to the widening rather than to the spec-op
/// route. (The acceptance row asserts it first for the same reason; this one names
/// it, so a failure reads as what it is.)
#[test]
fn carriers_own_operation_still_binds() {
    let mut kb = load_kb_with(SRC);
    assert_eq!(
        ints(&mut kb, "nx4fd.own_len"),
        vec![0, 2],
        "`length(?ls, ?n)` is List's own bodied, effect-free operation"
    );
}

/// CONTROL — the gate was WIDENED, not DELETED. A bodied operation declaring a
/// CONCRETE effect (`Error`) keeps its zero at arity+1, beside a byte-identical pure
/// twin that binds. `effect_member_is_parametric` reads the row member's HEAD, so a
/// concrete effect sort is not a parameter.
///
/// The pure twin is what makes the refusal mean anything: one operation answering
/// nothing is also what an un-drivable fixture answers.
#[test]
fn a_concretely_effectful_op_is_still_refused_at_arity_plus_one() {
    let src = r#"
namespace nx4fd_eff
  import anthill.prelude.{Bool, Int64, Error}

  operation pure_twice(x: Int64) -> Int64 = x + x
  operation loud_twice(x: Int64) -> Int64 effects Error = x + x

  fact mark(1)
  rule pure_r(?r) :- mark(?m), pure_twice(21, ?r)
  rule loud_r(?r) :- mark(?m), loud_twice(21, ?r)
end
"#;
    let mut kb = load_kb_with(src);
    let pure = definite_unary(&mut kb, "nx4fd_eff.pure_r");
    assert!(
        matches!(pure.as_slice(), [Value::Int(42)]),
        "the effect-free twin must BIND 42 — otherwise the row below measures an \
         un-drivable fixture rather than the effect gate; got {pure:?}"
    );
    assert_eq!(
        definite_unary(&mut kb, "nx4fd_eff.loud_r").len(),
        0,
        "a CONCRETE effect row (`Error`) must keep the operation out of the \
         functional-relation view — the widening is for row PARAMETERS only"
    );
}

/// CONTROL — the WI-519 residual. The relational view is a sound CHECKER, not a
/// generator (WI-580 §5): an UNGROUND receiver must SUSPEND rather than enumerate.
/// Admitting a parametric row must not turn it into a generator. Passes either way.
#[test]
fn an_unground_receiver_still_suspends() {
    let src = r#"
namespace nx4fd_ung
  import anthill.prelude.{List, String, Int64}
  import anthill.prelude.FiniteCollection.{size}
  fact mark(1)
  rule gen(?n) :- mark(?m), size(?ls, ?n)
end
"#;
    let mut kb = load_kb_with(src);
    assert_eq!(
        definite_unary(&mut kb, "nx4fd_ung.gen").len(),
        0,
        "an unground `size(?ls, ?n)` must not GENERATE — it suspends to a residual"
    );
}

/// FINDING FROM /code-review, DRIVEN — the completion arm's "exact rather than
/// lenient" claim, with a fixture that can tell EXACT from GUESSED. The review's
/// objection was that `an_under_determined_sort_half_slot_completes_from_a_sole_
/// provider` uses a spec with ONE provider, which is right whatever the rule is; a
/// control that varies the provider away from the call's own type was missing.
///
/// Here `Marked[M, N]` has TWO ground providers and the argument pins only `M`:
/// `alpha()` must select `Alpha`'s `code` (11) and `beta()` `Beta`'s (22). The two
/// rows DISAGREE, so a completion that took "the sole provider" — or the first, or
/// the wrong one — answers the same number twice, or the other number, and fails.
/// `unique_provider_completion`'s `could_answer` filter is what excludes the rival on
/// the PINNED element; `N` (open, and different in each provision) is what it
/// completes.
///
/// WHAT FAILS WHEN BACKED OUT (guard the completion with `if op_half`): both rows
/// answer `[]`. So this is evidence as well as a control — it is one of the calls the
/// old whole-call `Unresolvable` refused.
#[test]
fn a_completion_selects_the_provider_the_pinned_element_names() {
    let src = r#"
namespace nx4fd_disc
  import anthill.prelude.{Int64}

  sort Marked
    sort M = ?
    sort N = ?
    operation code() -> Int64
  end
  sort Alpha
    entity alpha
    fact Marked[M = Alpha, N = Beta]
    operation code() -> Int64 = 11
  end
  sort Beta
    entity beta
    fact Marked[M = Beta, N = Alpha]
    operation code() -> Int64 = 22
  end
  sort Ghost
    sort GM = ?
    sort GN = ?
    requires Marked[M = GM, N = GN]
    operation probe(x: GM) -> Int64 = Marked.code()
  end

  fact mark(1)
  rule ra(?x) :- mark(?m), Ghost.probe(alpha(), ?x)
  rule rb(?x) :- mark(?m), Ghost.probe(beta(), ?x)
end
"#;
    let mut kb = load_kb_with(src);
    for (qn, want) in [("nx4fd_disc.ra", 11i64), ("nx4fd_disc.rb", 22i64)] {
        let got = definite_unary(&mut kb, qn);
        assert!(
            matches!(got.as_slice(), [Value::Int(n)] if *n == want),
            "`{qn}` must resolve its `Marked` slot to the provider its PINNED `M` \
             names and answer {want}; a different number is a WRONG dictionary and \
             `[]` is the slot left unfilled. Got {got:?}"
        );
    }
}

/// CONTROL — RIVAL COMPLETIONS LEAVE THE SLOT UNFILLED RATHER THAN GUESS, and it is
/// the other half of the review's objection. Same shape as the row above with NOTHING
/// pinned: `probe(n: Int64)` mentions no element of the spec, so both providers can
/// answer and neither completion is unique.
///
/// Two arms in one fixture, differing only in how many providers exist, because a
/// single answering-nothing row is also what an un-drivable fixture gives:
///  * ONE provider — the only dictionary the goal could ever name — answers `1`.
///  * TWO — nothing decides — answers NOTHING. `unique_provider_completion` returns
///    `None` on the second surviving completion, the slot takes the recorded absence,
///    the body's `Zeroable.zero()` read is refused, and the call residualizes.
///
/// The second arm passes with the change backed out (it answered nothing before too);
/// the FIRST is what makes it a measurement rather than a tautology.
#[test]
fn rival_completions_leave_the_slot_unfilled_rather_than_guess() {
    let base = |extra: &str| {
        format!(
            r#"
namespace nx4fd_hz
  import anthill.prelude.{{Int64}}

  sort Zeroable
    sort T = ?
    operation zero() -> T
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Zeroable[T = Leaf]
    operation zero() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end
{extra}
  sort Ghost
    sort U = ?
    requires Zeroable[T = U]
    operation probe(n: Int64) -> Int64 = Zeroable.describe(Zeroable.zero())
  end

  fact mark(1)
  rule r(?x) :- mark(?m), Ghost.probe(5, ?x)
end
"#
        )
    };
    let mut sole = load_kb_with(&base(""));
    let got = definite_unary(&mut sole, "nx4fd_hz.r");
    assert!(
        matches!(got.as_slice(), [Value::Int(1)]),
        "with ONE `Zeroable` provider the completion is the only dictionary the goal \
         could name, so the call must answer 1 — `[]` here would make the arm below \
         measure an un-drivable fixture. Got {got:?}"
    );
    let mut rivals = load_kb_with(&base(
        r#"
  sort Pebble
    entity pebble
    fact Zeroable[T = Pebble]
    operation zero() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
"#,
    ));
    let got = definite_unary(&mut rivals, "nx4fd_hz.r");
    assert_eq!(
        got.len(),
        0,
        "with TWO providers and nothing pinned, the arguments do not decide — the \
         slot must be left unfilled and the read refused. A `1` or a `5` here is a \
         GUESSED dictionary. Got {got:?}"
    );
}

/// THE WIDENING'S SECOND READER, DRIVEN — and what it does NOT yet deliver.
///
/// `collect_covered_calls` (WI-1040) gates weaving on
/// `functional_relation_arity(..).is_some()`, so widening that predicate widens the
/// weaving population too. WI-1040's own doc records that the last time this
/// population moved wrongly it took `require[PartialEq[T]], eq(?x, ?y)` from ONE
/// solution to ZERO — a silent regression a green corpus did not catch — so
/// /code-review was right that "the suite is green either way" is not evidence about
/// it. MEASURED here instead, both spellings over one `List`:
///
///   * PLAIN `size(?ls, ?n)` — `Int(2)`, definite. The ticket's win.
///   * WOVEN `require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)` — ONE
///     INDEFINITE solution. The goal weaves (the hook now recognizes the callee) and
///     the reduction comes back undecided, so the arity+1 site routes to `unify` and
///     DELAYS, exactly as its WI-1040 clause says a woven call whose dictionary is
///     not bound yet must.
///
/// NOT A REGRESSION, and that is the part that needed the back-out to establish:
/// with the effect clause restored to `!sig.effects.is_empty()` BOTH spellings answer
/// `[]`. So no working call was taken away — the `require` spelling simply does not
/// receive the win, and the two spellings, which agreed at zero, now disagree.
///
/// THE GAP IS THE `require[X]` DICTIONARY, not this view: the woven call carries the
/// clause's `FiniteCollection` dictionary, whose own `Iterable` sub-slot is the very
/// one this ticket had to complete-or-mark on the bridge path, and `find_dictionary`
/// has not had that treatment. Owned by its own item; this row is here so the gap is
/// DRIVEN rather than parked in a note, and it must be re-aimed to expect `Int(2)` on
/// both spellings when that lands.
#[test]
fn the_woven_spelling_does_not_yet_receive_the_win() {
    let src = r#"
namespace nx4fd_weave
  import anthill.prelude.{List, String, Bool, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])

  rule woven(?ls, ?n) :- require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)
  rule plain(?ls, ?n) :- size(?ls, ?n)

  rule answer_woven(?n) :- Box(items: ?ls), woven(?ls, ?n)
  rule answer_plain(?n) :- Box(items: ?ls), plain(?ls, ?n)
end
"#;
    let mut kb = load_kb_with(src);
    let plain = definite_unary(&mut kb, "nx4fd_weave.answer_plain");
    assert!(
        matches!(plain.as_slice(), [Value::Int(2)]),
        "the PLAIN spelling is the ticket's win and must answer 2 — without it the \
         arm below measures nothing. Got {plain:?}"
    );
    let woven = query_unary(&mut kb, "nx4fd_weave.answer_woven");
    assert!(
        woven.iter().all(|(_, definite)| !definite),
        "the woven spelling must not report a DEFINITE answer it did not compute; a \
         definite solution here would be the `unify` site binding the result to the \
         call term. Got {woven:?}"
    );
    assert!(
        !woven.is_empty(),
        "…and it must DELAY rather than silently answer nothing: a woven call whose \
         dictionary is not bound is what WI-1040's `unify` clause exists to keep \
         suspending. If this now answers `Int(2)`, the `require[X]` dictionary gap \
         has been closed and this whole row should be re-aimed at equality with the \
         plain spelling. Got {woven:?}"
    );
}
