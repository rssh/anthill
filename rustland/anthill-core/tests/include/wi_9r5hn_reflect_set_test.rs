//! WI-20260923-9R5HN — anthill-stl's reflect set is `HOST_FNS` rows named by binding
//! blocks, so a rule body can REDUCE it. What that visibility changes, measured.
//!
//! The 24 operations `register_reflect_builtins` bound by qualified name (`KB.sorts` /
//! `operations` / `constructors` / `fields` / …, the namespace-level symbol and term-shape
//! ops, `Substitution.apply` / `compose` / `bindings`, `kernel.not`) ran from an operation
//! body and were INVISIBLE to `is_interpreter_mapped_op`. At a rule-body operand that is
//! not merely "does not reduce": `eq` compared the UN-REDUCED CALL structurally and
//! DECIDED, so a negation over one concluded a positive fact from a call that never ran —
//! kernel-language.md §5.2's decided-false decline, the soundness gap WI-880 closed for
//! the accessor half of this namespace.
//!
//! ── MEASURED BEFORE / AFTER, same fixture, definite answers ────────────────────
//!
//!   row                                                  before        after
//!   KB.constructors(kb(), Color) = ["red","green"]       0             1
//!   KB.constructors(kb(), Color) = ["red"]               0             0
//!   not(KB.constructors(kb(), Color) = ["red","green"])  1 (UNSOUND)   0
//!   KB.fields(kb(), pt) <=> [x, y] / [y, x]              0 / 0         1 / 0
//!   can_be_sort(as_term(Color))   (a bare Bool goal)     0             1
//!   can_be_sort(as_term(7))                              0             0
//!   not(can_be_sort(as_term(Color)))                     1 (UNSOUND)   0
//!   mk() <=> some(?s), lookup(?s, "x") → 7 / 8 / none    0 / 0 / 0     1 / 0 / 0
//!   term_as_int(KB.reflect(kb(), ConstRepr(7))) = 7 / 8  0 / 0         1 / 0
//!   KB.reify(kb(), as_term(7)) <=> ConstRepr(7) / (8)    0 / 0         1 / 0
//!   KB.sorts(kb(), some(<ns>)) <=> [one SortInfo] / []   0 / 0         1 / 0
//!   term_as_sort(as_term(Color)) / (as_term(7)) <=> some 0 / 0         1 / 0
//!   can_be_sort(sort_as_term(Color))                     0             1
//!   lookup(compose(?s, ?s), "x") → 7 / none              0 / 0         1 / 0
//!
//! "before" is the pre-ticket CLI (`anthill query`) over this file's fixtures; every
//! `before` row answered with total 0 (decided) except the `Substitution` rows, which
//! suspended — `mk()` could not run at all (below).
//!
//! THREE READS HAD TO WIDEN FOR THE "after" COLUMN, each measured refusing on the carrier a
//! rule body hands it, each a by-CARRIER answer to a by-content question:
//!   * `expect_term` (every `Term`-typed argument of the moved functions) matched
//!     `Value::Term` alone — `can_be_sort(as_term(Color))` refused "expected Term, got
//!     Node". A read that needs only the argument's shape goes through `TermView` now
//!     (nothing transient is interned); `kernel.not` / `KB.reify` lower it by content.
//!   * `reflect.unify` did the same, so `unify(fresh_var("x"), as_term(7), kb())` refused
//!     "expected Term, got Int64" in an OPERATION body — `as_term` is the identity — and the
//!     one producer of a `Substitution` was unreachable from a rule.
//!   * the four `Substitution` operations matched `Value::Substitution` alone, and a
//!     substitution bound by `<=>` reaches the next call σ-walked into a SPLICED occurrence:
//!     "expected Substitution, got Node". They read through `Value::carried` now.
//!
//! TWO MORE, found by /code-review once the rows above were in: `KB.reflect`'s decoder
//! matched `Value::Entity` (a rule-body `ConstRepr(…)` is a `Value::Node`) and reads
//! through the view now; `KB.sorts(kb, some(ns))` compared `ns` against each sort's SHORT
//! name, so a namespace never matched — a WRONG answer on every carrier, in an operation
//! body too (`eval::reflect_builtins`'s `kb_sorts_filters_by_namespace`).
//!
//! NOT DRIVEN, and said here: `Substitution.apply(…)` cannot be WRITTEN in a rule body —
//! it is a load error ("apply.arity … got 0 arguments"), MEASURED identical before and
//! after this ticket. The `apply` segment is read as the reflect `apply` FORM — the
//! last-segment keying WI-20260904-FSNZ5 owns.
//! Its eval face is driven from an operation body (`eval::reflect_builtins`' tests).
//!
//! AND ONE ARENA, which is the ticket's prerequisite: `mk()` runs in one scratch bridge
//! interpreter and `Substitution.lookup` in another, so the handle crosses arenas. With the
//! receiver-arena read put back (`interp`'s slot table indexed by the handle's slot), the
//! `lookup` rows PANIC the process — MEASURED, `index out of bounds: the len is 0 but the
//! index is 0` from `anthill query`. `SubstHandle::with_subst` reads the arena that minted
//! the handle; `eval::subst_arena`'s and `eval::reflect_builtins`' cross-arena tests drive it
//! below the resolver.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// DEFINITE solutions only — a suspension must not read as success.
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// Definite + floundered: a "decided" answer is `total == answers`.
fn total(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

const FIXTURE: &str = r#"
namespace wi9r5hn.rb
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{KB, Term, Substitution, FieldInfo, unify, as_term, fresh_var, term_as_int, can_be_sort}

  sort Color
    entity red
    entity green
  end
  sort Pt
    entity pt(x: Int64, y: Int64)
  end

  rule ctors(1)     :- KB.constructors(KB.kb(), Color) = ["red", "green"]
  rule ctors_no(1)  :- KB.constructors(KB.kb(), Color) = ["red"]
  rule ctors_neg(1) :- not(KB.constructors(KB.kb(), Color) = ["red", "green"])
  rule fields(1)    :- KB.fields(KB.kb(), pt) <=> [FieldInfo(name: "x", type_name: ?), FieldInfo(name: "y", type_name: ?)]
  rule fields_no(1) :- KB.fields(KB.kb(), pt) <=> [FieldInfo(name: "y", type_name: ?), FieldInfo(name: "x", type_name: ?)]

  rule cbs(1)       :- can_be_sort(as_term(Color))
  rule cbs_lit(1)   :- can_be_sort(as_term(7))
  rule cbs_neg(1)   :- not(can_be_sort(as_term(Color)))

  operation mk() -> Option[T = Substitution] = unify(fresh_var("x"), as_term(7), KB.kb())
  rule look7(1)     :- mk() <=> some(?s), Substitution.lookup(?s, "x") <=> some(?v), term_as_int(?v) = some(7)
  rule look8(1)     :- mk() <=> some(?s), Substitution.lookup(?s, "x") <=> some(?v), term_as_int(?v) = some(8)
  rule lookn(1)     :- mk() <=> some(?s), Substitution.lookup(?s, "x") <=> none()
  rule binds0(1)    :- mk() <=> some(?s), Substitution.bindings(?s) <=> []
end
"#;

/// A KB READER REDUCES AT A RULE-BODY OPERAND, and the negation over it is sound.
///
/// `ctors` / `fields` are the computation; `ctors_no` / `fields_no` are the wrong value, so
/// the positive rows cannot be passed by a reader answering anything at all; `ctors_neg` is
/// the soundness row — 1 DEFINITE before, a positive fact from a call that never ran. All
/// three polarities DECIDE (total == definite).
#[test]
fn a_kb_reader_reduces_at_a_rule_body_operand() {
    let mut kb = crate::common::load_kb_with(FIXTURE);
    for (row, want) in [
        ("ctors", 1),
        ("ctors_no", 0),
        ("ctors_neg", 0),
        ("fields", 1),
        ("fields_no", 0),
    ] {
        let goal = format!("wi9r5hn.rb.{row}(1)");
        assert_eq!(
            (answers(&mut kb, &goal), total(&mut kb, &goal)),
            (want, want),
            "{goal}: (definite, total) — the reader must REDUCE and decide. Before this \
             ticket every row answered 0 total, and `ctors_neg` 1 DEFINITE"
        );
    }
}

/// A BOOL-RETURNING ONE IS A RELATION: `can_be_sort` as a bare goal routes to `= true`
/// (`bare_bodied_bool_relation`, whose host leg reads `is_interpreter_mapped_op`). Before,
/// the goal had no clauses and was DECIDED FALSE, so `not(can_be_sort(…Color…))` answered 1.
#[test]
fn a_bool_reflect_op_is_a_rule_body_relation() {
    let mut kb = crate::common::load_kb_with(FIXTURE);
    for (row, want) in [("cbs", 1), ("cbs_lit", 0), ("cbs_neg", 0)] {
        let goal = format!("wi9r5hn.rb.{row}(1)");
        assert_eq!(
            (answers(&mut kb, &goal), total(&mut kb, &goal)),
            (want, want),
            "{goal}: (definite, total)"
        );
    }
}

/// A SUBSTITUTION CROSSES BRIDGE INTERPRETERS AND IS READ IN THE ARENA THAT MINTED IT.
///
/// `mk()` reduces in one scratch interpreter (its `unify` allocates the substitution
/// there), `Substitution.lookup` / `bindings` in another. `look7` reads the binding; `look8`
/// and `lookn` are its wrong values; `binds0` says the substitution is NOT empty. Before this
/// ticket all four suspended (`mk` refused its own `as_term` operand); with the
/// receiver-arena read restored the `lookup` rows panic.
#[test]
fn a_substitution_is_read_across_bridge_interpreters() {
    let mut kb = crate::common::load_kb_with(FIXTURE);
    for (row, want) in [("look7", 1), ("look8", 0), ("lookn", 0), ("binds0", 0)] {
        let goal = format!("wi9r5hn.rb.{row}(1)");
        assert_eq!(
            (answers(&mut kb, &goal), total(&mut kb, &goal)),
            (want, want),
            "{goal}: (definite, total)"
        );
    }
}

const FIXTURE_MORE: &str = r#"
namespace wi9r5hn.more
  import anthill.prelude.{Int64, String, Bool, Option, List}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{KB, Term, Substitution, SortInfo, TermRepr, LiteralRepr, unify, as_term, fresh_var, term_as_int, term_as_sort, sort_as_term, can_be_sort}
  import anthill.reflect.TermRepr.{ConstRepr}
  import anthill.reflect.LiteralRepr.{IntLiteral}

  sort Color
    entity red
  end

  rule refl(1)     :- term_as_int(KB.reflect(KB.kb(), ConstRepr(value: IntLiteral(value: 7)))) = some(7)
  rule refl_no(1)  :- term_as_int(KB.reflect(KB.kb(), ConstRepr(value: IntLiteral(value: 7)))) = some(8)
  rule reify(1)    :- KB.reify(KB.kb(), as_term(7)) <=> ConstRepr(value: IntLiteral(value: 7))
  rule reify_no(1) :- KB.reify(KB.kb(), as_term(7)) <=> ConstRepr(value: IntLiteral(value: 8))
  rule sorts(1)    :- KB.sorts(KB.kb(), some("wi9r5hn.more")) <=> [SortInfo(name: ?, definition: ?, kind: ?, constructors: ?, operations: ?, parameters: ?, requires: ?)]
  rule sorts_no(1) :- KB.sorts(KB.kb(), some("wi9r5hn.more")) <=> []
  rule tas(1)      :- term_as_sort(as_term(Color)) <=> some(?)
  rule tas_no(1)   :- term_as_sort(as_term(7)) <=> some(?)
  rule sat(1)      :- can_be_sort(sort_as_term(Color))
  operation mk() -> Option[T = Substitution] = unify(fresh_var("x"), as_term(7), KB.kb())
  rule comp(1)     :- mk() <=> some(?s), Substitution.lookup(Substitution.compose(?s, ?s, KB.kb()), "x") <=> some(?v), term_as_int(?v) = some(7)
  rule comp_no(1)  :- mk() <=> some(?s), Substitution.lookup(Substitution.compose(?s, ?s, KB.kb()), "x") <=> none()
end
"#;

/// THE REST OF THE SET at a rule-body operand, each against its wrong value: the
/// `TermRepr` bridge both ways, the namespace-filtered `KB.sorts`, the sort <-> term pair,
/// and a `compose` whose two operands are one handle (so the two reads nest). Before this
/// ticket every row answered 0 — `comp` / `comp_no` suspended, the rest decided false.
#[test]
fn the_rest_of_the_reflect_set_reduces_at_a_rule_body_operand() {
    let mut kb = crate::common::load_kb_with(FIXTURE_MORE);
    for (row, want) in [
        ("refl", 1),
        ("refl_no", 0),
        ("reify", 1),
        ("reify_no", 0),
        ("sorts", 1),
        ("sorts_no", 0),
        ("tas", 1),
        ("tas_no", 0),
        ("sat", 1),
        ("comp", 1),
        ("comp_no", 0),
    ] {
        let goal = format!("wi9r5hn.more.{row}(1)");
        assert_eq!(
            (answers(&mut kb, &goal), total(&mut kb, &goal)),
            (want, want),
            "{goal}: (definite, total)"
        );
    }
}

const FIXTURE_HANDLES: &str = r#"
namespace wi9r5hn.handles
  import anthill.prelude.{Int64, String, Bool, List, Map, Function}
  operation adder(n: Int64) -> Function[Int64, Int64] = lambda x -> x + n
  operation apply1(f: Function[Int64, Int64], v: Int64) -> Int64 = f(v)
  rule clo(1)    :- adder(10) <=> ?f, apply1(?f, 1) = 11
  rule clo_no(1) :- adder(10) <=> ?f, apply1(?f, 1) = 12
  rule map(1)    :- Map.put(Map.empty(), "a", 1) <=> ?m, Map.size(?m) = 1
  rule map_no(1) :- Map.put(Map.empty(), "a", 1) <=> ?m, Map.size(?m) = 2
end
"#;

/// A RUNTIME HANDLE BOUND BY ONE RULE-BODY CALL IS READ BY THE NEXT, whatever it is.
///
/// The `Substitution` rows above are one case of a general shape: the resolver binds
/// `?f` / `?m` to a closure or a map one scratch bridge interpreter minted, and the
/// next call reduces in another. Two things stood in the way, both MEASURED:
///   * the bound value reached the next call σ-applied into the goal as a SPLICED
///     occurrence, so `apply1` bound its parameter to a node rather than a closure
///     ("unknown operation: …apply1.f") and `Map.size` refused its receiver — both rows
///     SUSPENDED. The resolver→eval boundary (`Interpreter::call_op_bridged`) cancels
///     the wrapper now, leaving the resolver's own builtins the carrier the goal holds;
///   * with that fixed, the closure rows PANICKED — `enter_closure` read the closure
///     through `self.closures`, the READING interpreter's arena (index out of bounds).
///     Closure and stream reads are methods on their handles now, as `Map`, `Cell` and
///     `Substitution` reads are (`eval::closure` / `eval::stream` cross-arena tests).
///
/// NO STREAM ROW, and not for want of one: a stream pull (`splitFirst`) declares its
/// row (`effects s.E`), so it never reduces at a rule-body operand — the same gate that
/// keeps a σ-bound handle READ-only (`bridge_op_to_eval`'s "pure"). The stream handle's
/// own-arena read is driven by `eval::stream`'s unit test.
#[test]
fn a_runtime_handle_crosses_bridge_interpreters() {
    let mut kb = crate::common::load_kb_with(FIXTURE_HANDLES);
    for (row, want) in [("clo", 1), ("clo_no", 0), ("map", 1), ("map_no", 0)] {
        let goal = format!("wi9r5hn.handles.{row}(1)");
        assert_eq!(
            (answers(&mut kb, &goal), total(&mut kb, &goal)),
            (want, want),
            "{goal}: (definite, total)"
        );
    }
}

/// A REFLECT READ THE EXTENT REFUSES IS A REPORTED FAULT, NOT A CRASH. A program may
/// assert a BODIED rule under a reflect functor, and the extent seam refuses to read
/// such a relation as facts. The reader PANICKED on that — MEASURED, `KB.descriptions`
/// at a rule-body operand took the process down from inside resolution. It is
/// `EvalError::KbReadFailed` now: the goal suspends AND the search says why — a
/// `Schedule` classification would suspend it just the same and say nothing, which is
/// what the message row is here to tell apart — MEASURED, with `KbReadFailed` moved to
/// `Schedule` the message row fails (no error reported) while the suspension row passes.
#[test]
fn a_refused_reflect_read_suspends_the_goal() {
    let mut kb = crate::common::load_kb_with(
        r#"
namespace wi9r5hn.forged
  import anthill.prelude.{Int64, String, Bool, List, Option}
  import anthill.prelude.Option.{none}
  import anthill.reflect.{KB, MemberInfo, DescriptionInfo}
  rule DescriptionInfo(target: ?t, content: "forged", index: 0) :- MemberInfo(name: ?t, kind: ?, parent: ?)
  rule descs(1) :- KB.descriptions(KB.kb(), none()) <=> []
end
"#,
    );
    let goal = "wi9r5hn.forged.descs(1)";
    assert_eq!(
        (answers(&mut kb, goal), total(&mut kb, goal)),
        (0, 1),
        "{goal}: the refused read must SUSPEND the goal — not decide it, not panic"
    );
    let g = crate::common::query_pattern_term(&mut kb, goal);
    let (_, stats) = kb.resolve_with_stats(&[g], &ResolveConfig::default());
    assert!(
        stats
            .errors
            .iter()
            .any(|e| e.message.contains("KB.descriptions")
                && e.message.contains("reflect DescriptionInfo read")),
        "the refusal must be REPORTED as a fault naming the call and the read; got {:?}",
        stats.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
    );
}
