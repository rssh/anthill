//! WI-20261124-YFD7F, stages S1–S3 — a typed column is not checked again at a call whose
//! argument the caller has established at the column's type.
//!
//! THE CASE. `rule memT(?x: Int64, ?l: List[T = Int64]) :- (?l <=> cons(head: ?x, tail: ?)) |
//! (?l <=> cons(head: ?, tail: ?t), memT(?x, ?t))` checked and filled `?l` at EVERY call, its
//! own recursion on the tail included: the fill walks a ground list whole, so a membership of
//! the last element of `[1, …, n]` walked every tail once per level, and each level's fill was
//! still pending when the next opened. MEASURED (release CLI, the fewest `--max-steps` that
//! answer, n = 25 / 50 / 100): 2097 / 7322 / 27147, where `memX`, the same rule with `?l`
//! unannotated — its inferred type concrete, so unchecked — took 396 / 796 / 1596; and `memU`,
//! with neither column written — `?l` inferred `List[T = ?e]`, checked — 1997 / 7122 / 26747.
//! At n = 400 `memT` was 18.55 s / 7.67 GB.
//!
//! THE CHANGE. S1: every fillable typed column gets the `SortDomain` read a caller routes to —
//! a ground bound's too, its fill reading the dictionary built at load. S2: a rule-body goal
//! hands such a read `__trusted(d)` where the caller has ESTABLISHED the argument at the
//! column's bound (`typing::trusted_columns`, the evidence rule). S3: a clause opened with a
//! trusted read drops that column's guard and fill (`resolve::typed_column_goal_positions`).
//! MEASURED after, n = 100 / 200 / 400 (`memT` 0.76 s / 139 MB at 400): `memT` 1704 / 3404 /
//! 6804, `memU` 1700 / 3400 / 6800, `memX` 1200 / 2400 / 4800 — its `Int64` column is trusted
//! in the recursion too; `memT` is within 1.1 of the 1596 the unchecked `memX` took at n = 100
//! before the change.
//!
//! BACK-OUTS, each RUN (2026-11-27), on this file:
//!  * [T] no `__trusted` slot passed (`trusted_slot` answers `None`): the two linearity rows
//!    of `memT` and `memU` fail — quadratic again; every other row passes.
//!  * [D] the slot passed but nothing dropped at the open: the same two rows fail.
//!  * [S] the evidence read off the goal argument's typer stamp, not the check's type: three
//!    rows fail — `the_type_the_check_established_is_the_evidence` (`strs(["a"])` answers),
//!    `a_part_of_another_branch_is_not_trusted` (the right branch's `?t` is stamped
//!    `List[T = Bool]`, and trusted), and `memU`'s linearity (its tail's stamp names another
//!    variable than its bound).
//!  * [C] a clause holding a cut trusts as any other: `a_cut_keeps_the_callee_fill_before_it`
//!    fails — four answers where the callee's fill committed to one.
//!  * [P] every `<=>` of the body counted as on the path: `a_part_of_another_branch_is_not_
//!    trusted` fails — the right branch's `len1` leaves its cell open, not filled.
//! Passing under every axis BY DESIGN: the unchecked `memX`'s linearity (no list check to
//! skip), generation through a trusted call (the caller's fill fills), a query's argument
//! checked once where it enters, and the refusal of `[[]]` at `List[T = Int64]` (the caller's
//! check runs).

use crate::common::{load_kb_with, query_pattern_term};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

const PROGRAM: &str = r#"
namespace yfd7ft
  import anthill.prelude.{List, Int64, Bool, String, Float, Option}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}

  rule memT(?x: Int64, ?l: List[T = Int64]) :- (?l <=> cons(head: ?x, tail: ?)) | (?l <=> cons(head: ?, tail: ?t), memT(?x, ?t))
  rule memX(?x: Int64, ?l) :- (?l <=> cons(head: ?x, tail: ?)) | (?l <=> cons(head: ?, tail: ?t), memX(?x, ?t))
  rule memU(?x, ?l) :- (?l <=> cons(head: ?x, tail: ?)) | (?l <=> cons(head: ?, tail: ?t), memU(?x, ?t))

  rule ints(?m: List[T = Int64]) :- true
  rule strs(?l: List[T = ?e]) :- ints(?l)

  rule pair(?m: List[T = Bool]) :- ?m <=> [?, ?]
  rule outerPair(?l: List[T = Bool]) :- pair(?l)
  rule firstPair(?l: List[T = Bool]) :- pair(?l), !

  sort Pair[A]
    entity pr(a: A)
  end
  fact flt(2.5)
  rule inc(?x: Int64, ?y) :- add(?x, 1, ?y)
  rule viaBranch(?p: Pair[A = Int64], ?y) :- (?p <=> pr(a: ?v), flt(?v), inc(?v, ?y)) | ?y <=> 0
  rule anyBranch(?y) :- viaBranch(?, ?y)
  rule noBranch(?z) :- not(anyBranch(3.5)), ?z <=> 1

  sort Colour
    entity red
    entity green
  end
  sort Duo[A, B]
    entity duo(x: A, y: B)
  end
  sort Box[T = Colour]
    entity box(v: T)
  end
  sort Hue = Colour
  sort Hues = List[T = Hue]
  rule duos(?x: Duo[Colour, Colour]) :- true
  rule hues(?x: Option[Hue]) :- true
  rule hueList(?x: Hues) :- ?x <=> [?]
  rule tuples(?x: (Colour, Option[T = Colour])) :- true
  rule boxes(?x: Box[T = Colour]) :- true

  rule len1(?m: List[T = Bool]) :- ?m <=> [?]
  rule other(?l: List[T = Bool], ?n) :- (?l <=> cons(head: ?, tail: ?t), ?n <=> 2) | (len1(?t), ?t <=> cons(head: ?b, tail: ?), ?n <=> (if ?b then 1 else 0))
end
"#;

fn config() -> ResolveConfig {
    ResolveConfig {
        max_depth: 100_000,
        max_steps: 100_000_000,
        ..ResolveConfig::default()
    }
}

/// The answers of `pattern` and the steps the whole search took.
fn run(kb: &mut KnowledgeBase, pattern: &str) -> (usize, u64) {
    let goal = query_pattern_term(kb, pattern);
    let (solutions, stats) = kb.resolve_with_stats(&[goal], &config());
    assert!(!stats.truncated, "`{pattern}` ran to its end: {stats:?}");
    (solutions.len(), stats.steps)
}

/// The membership of `n`, the last element of `[1, …, n]`: one answer, and its steps.
fn last_member_steps(kb: &mut KnowledgeBase, rel: &str, n: usize) -> u64 {
    let list: Vec<String> = (1..=n).map(|i| i.to_string()).collect();
    let (answers, steps) = run(kb, &format!("yfd7ft.{rel}({n}, [{}])", list.join(", ")));
    assert_eq!(answers, 1, "`{n}` is a member of `[1, …, {n}]` once");
    steps
}

/// Do the steps of `rel` grow linearly from n = 50 to 100 to 200 — each doubling at most
/// doubling them, give or take a few steps of the query's own?
fn assert_linear(kb: &mut KnowledgeBase, rel: &str) -> [u64; 3] {
    let s = [50, 100, 200].map(|n| last_member_steps(kb, rel, n));
    let slack = 40;
    assert!(
        s[1] <= 2 * s[0] + slack && s[2] <= 2 * s[1] + slack,
        "`{rel}` walks its list once: steps at n = 50 / 100 / 200 are {s:?}",
    );
    s
}

/// THE TICKET'S ROW — the typed `memT` walks its list ONCE: the steps double with the list,
/// and stay within a small factor of the unchecked `memX`'s. FAILS under [T] and [D]: 7 322 /
/// 27 147 / … at n = 50 / 100, quadratic.
#[test]
fn a_typed_recursion_on_its_own_tail_is_linear() {
    let mut kb = load_kb_with(PROGRAM);
    let typed = assert_linear(&mut kb, "memT");
    let unchecked = assert_linear(&mut kb, "memX");
    assert!(
        typed[2] <= 2 * unchecked[2],
        "the typed walk is within twice the unchecked one: {typed:?} against {unchecked:?}",
    );
}

/// A column whose type the clause leaves open — `?l` inferred `List[T = ?e]`, checked — is
/// trusted in the clause's own recursion at its own variables: `memU` is linear too. FAILS
/// under [T] and [D].
#[test]
fn an_inferred_column_with_a_variable_is_linear() {
    let mut kb = load_kb_with(PROGRAM);
    assert_linear(&mut kb, "memU");
}

/// CONTROL — the unchecked `memX` is linear whatever is trusted: it has no list check to skip.
#[test]
fn an_unchecked_list_column_is_linear() {
    let mut kb = load_kb_with(PROGRAM);
    assert_linear(&mut kb, "memX");
}

/// THE EVIDENCE IS THE CHECK'S TYPE, never the typer's stamp at the goal. `strs`'s column is
/// `List[T = ?e]`, and its goal `ints(?l)` unifies `?e` with `Int64` in the clause's typing —
/// the call's own column, not anything the check established: `strs`'s check admits
/// `["a"]`, a `List[T = String]`. `ints` is handed a check, and refuses it. FAILS under [S]:
/// `ints` trusted, `strs(["a"])` answers.
#[test]
fn the_type_the_check_established_is_the_evidence() {
    let mut kb = load_kb_with(PROGRAM);
    assert_eq!(run(&mut kb, r#"yfd7ft.strs(["a"])"#).0, 0, "`[\"a\"]` is no `List[T = Int64]`");
    assert_eq!(run(&mut kb, "yfd7ft.strs([1, 2])").0, 1, "`[1, 2]` is one");
}

/// CONTROL — GENERATION IS OWNED UPSTREAM. `outerPair`'s column is established by its own
/// check and fill, so `pair` is trusted and fills nothing; `outerPair`'s fill fills the two
/// cells `pair`'s body leaves open: the four lists, as `pair` alone answers them.
#[test]
fn a_trusted_call_leaves_its_generation_to_the_caller() {
    let mut kb = load_kb_with(PROGRAM);
    assert_eq!(run(&mut kb, "yfd7ft.pair(?l)").0, 4, "two cells of `Bool`");
    assert_eq!(run(&mut kb, "yfd7ft.outerPair(?l)").0, 4, "the caller's fill fills them");
}

/// A CUT commits past what its clause left open. `firstPair`'s `!` follows `pair(?l)`, which
/// FILLED `?l` before it — the cut commits to the first list, `[true, true]`. Trusted, `pair`
/// would leave both cells open, the cut commit to that, and `firstPair`'s own fill, after the
/// cut, enumerate all four. A clause holding a cut trusts nothing. FAILS under [C]: four answers.
#[test]
fn a_cut_keeps_the_callee_fill_before_it() {
    let mut kb = load_kb_with(PROGRAM);
    assert_eq!(run(&mut kb, "yfd7ft.firstPair(?l)").0, 1, "the cut commits to the first list");
}

/// A PART OF ANOTHER BRANCH IS NOT TRUSTED (WI-20261124-C6VN0: a branch types on its own).
/// `?t` is the tail of `?l` in the left branch only; in the right one it is a variable no check
/// of the clause covers, so `len1(?t)` is handed a check and FILLS its cell, which `if` reads:
/// `2` from the left branch, `1` and `0` from the right, each definite. FAILS under [P]: `len1`
/// trusted leaves the cell open, and `if` waits on it.
#[test]
fn a_part_of_another_branch_is_not_trusted() {
    let mut kb = load_kb_with(PROGRAM);
    let goal = query_pattern_term(&mut kb, "yfd7ft.other([true], ?n)");
    let (solutions, _) = kb.resolve_with_stats(&[goal], &config());
    assert_eq!(solutions.len(), 3, "`2` from the left branch, `1` and `0` from the right");
    assert!(solutions.iter().all(|s| s.is_definite()), "each definite");
}

/// CONTROL — A VALUE FROM OUTSIDE IS CHECKED ONCE, where it enters: a query passes no trusted
/// slot, so `memT`'s own check refuses a list whose tail is no list, at the top, though every
/// recursive call is trusted.
#[test]
fn a_query_argument_is_checked_where_it_enters() {
    let mut kb = load_kb_with(PROGRAM);
    assert_eq!(run(&mut kb, r#"yfd7ft.memT(5, anthill.prelude.List.cons(head: 5, tail: "junk"))"#).0, 0, "the tail is no list");
    assert_eq!(
        run(&mut kb, r#"yfd7ft.memT(7, anthill.prelude.List.cons(head: 5, tail: anthill.prelude.List.cons(head: 7, tail: "junk")))"#).0,
        0,
        "the junk below the member is refused by the top call's fill",
    );
    assert_eq!(run(&mut kb, "yfd7ft.memT(7, [5, 7])").0, 1, "a list of `Int64` is a member");
    assert_eq!(
        run(&mut kb, "yfd7ft.memT(7, anthill.prelude.List.cons(head: 5, tail: [7]))").0,
        1,
        "and so is one written with its constructor",
    );
}

/// CONTROL — `[[]]` against `List[T = Int64]` is refused: the guard's closed reading cannot tell
/// it from `[]`, and the fill, which can, still runs at the top call.
#[test]
fn a_nested_empty_list_is_refused_at_a_list_of_int() {
    let mut kb = load_kb_with(PROGRAM);
    assert_eq!(run(&mut kb, "yfd7ft.ints([[]])").0, 0, "`[[]]` is no `List[T = Int64]`");
    assert_eq!(run(&mut kb, "yfd7ft.memT(1, [[]])").0, 0, "nor at `memT`");
}

/// CONTROL — A TRUSTED CALLEE'S PART BOUND TO ANOTHER TYPE IS STILL REFUTED, never faulted.
/// `flt(?v)` in a `|` branch puts a `Float` into `?v`, the `Int64` field of `?p` — the branch's
/// own typing reads `?v` there, and the clause loads. `inc` is trusted at `?v` and runs no guard,
/// and `add(2.5, 1, ?y)` would FAULT. It never runs: `viaBranch`'s own guard was waiting on
/// `?p`'s open cell, and refutes `pr(a: 2.5)` when `flt` binds it, before the next goal — the
/// topmost check of a value waits on every cell a trusted callee binds. So `not(anyBranch(3.5))`
/// is DEFINITE. Passes under every axis BY DESIGN; recorded because the review asked whether a
/// branch defeats the evidence rule (MEASURED 2026-11-27, the inlined `add` alike).
#[test]
fn a_part_a_branch_binds_to_another_type_is_refuted_by_the_waiting_guard() {
    let mut kb = load_kb_with(PROGRAM);
    assert_eq!(crate::common::one_definite_int(&mut kb, "yfd7ft.noBranch"), Some(1), "refuted, not faulted");
}

/// S1 CONTROL — a GROUND bound fills through the dictionary built at load in every spelling of
/// its type: parameters written by position, an alias inside, an alias of a list, a tuple, a
/// defaulted parameter — and a query's typed variable at the defaulted sort, written bare.
/// `ground_domain_dictionary` refuses to fall back to the type, so a spelling it could not build
/// fails the load here. Passes under every axis BY DESIGN (no answer moves with S1).
#[test]
fn a_ground_bound_builds_its_dictionary_in_every_spelling() {
    let mut kb = load_kb_with(PROGRAM);
    for (pattern, count) in [
        ("yfd7ft.duos(?x)", 4),
        ("yfd7ft.hues(?x)", 3),
        ("yfd7ft.hueList(?x)", 2),
        ("yfd7ft.tuples(?x)", 6),
        ("yfd7ft.boxes(?x)", 2),
        ("yfd7ft.boxes(?x: yfd7ft.Box)", 2),
    ] {
        assert_eq!(run(&mut kb, pattern).0, count, "`{pattern}`");
    }
}
