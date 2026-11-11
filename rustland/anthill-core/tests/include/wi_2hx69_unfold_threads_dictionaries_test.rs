//! WI-20261013-2HX69 — 068 D1c: THE WI-580 UNFOLD READS ITS OTHER OPERAND AS A VALUE AND
//! HANDS THE CALLS IT HOISTS THE DICTIONARIES THE UNFOLDED BODY GIVES THEM.
//!
//! `unfold_eq_operand` splits `f(?x) = OTHER` into one continuation per `match` arm of `f`'s
//! body: `unify(?x, patternᵢ), unify(residualᵢ, OTHER)`, each call in the residual hoisted to a
//! fresh variable and an `eq` goal of its own. Two things changed.
//!
//! OTHER IS EVALUATED FIRST (068 §1.1), as every other consumer reads an operand: a call in it
//! that can run is replaced by its value, and one that cannot — waiting on a variable,
//! unreduced — declines the split, so the builtin delays on it. It replaced WI-20260827-XBHX3's
//! gate, which declined every OTHER holding a bodied call: that cost `bodyNest` its answer,
//! and it was what kept `w` from a wrong refutation (P1TPE's decline cannot see an override
//! behind a call it has not evaluated).
//!
//! A HOISTED CALL CARRIES ITS DICTIONARIES (068 §8 step 4). It is the call the operation body
//! makes, with the typer's stamps on it — so a dictionary written at the call site in an arm is
//! honoured — and a call that reads the unfolded operation's own `requires` is woven with what
//! the unfolded call carries for it: the typer's dictionary at literals, a citation's through a
//! clause's condition. An operation with `requires` was declined outright before.
//!
//! BACK-OUTS, each part by a temporary switch, all in one build and measured against this module
//! alone: the gate restored, OTHER read unevaluated, hoisted calls built without the typer's
//! stamps, an operation with `requires` declined, the slot weave off. Each row says which it
//! fails under.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// `(total, definite)`: a suspension is `(n, 0)`, a refutation `(0, 0)`.
fn counts(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let def = sols.iter().filter(|s| s.is_definite()).count();
    (sols.len(), def)
}

/// The local names of a unary relation's definite answers, in order.
fn definite_names(kb: &mut KnowledgeBase, qn: &str) -> Vec<String> {
    crate::common::query_unary(kb, qn)
        .into_iter()
        .filter(|(_, d)| *d)
        .map(|(v, _)| match kb.value_head_symbol(&v) {
            Some(s) => kb.local_name_of(s).to_string(),
            None => format!("{v:?}"),
        })
        .collect()
}

/// `AE`'s `eq` reads `k` and ignores `tag` (WI-20260827-P1TPE's carrier): `mk(red())` is
/// declared-equal to `pick(red())` and structurally different. `Descending` is a rival
/// `Ord[T = Int64]`: its `compare(1, 5)` is 4, `Int64`'s own is -1.
const SRC: &str = r#"
namespace wi2hx69
  import anthill.prelude.{Int64, Bool, List, Error, EmptyStream, Ord, WeakOrd, PartialOrd, PartialEq, Eq}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.List.{append}

  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  sort AE
    entity ae(k: Int64, tag: Int64)
    operation aeq(a: AE, b: AE) -> Bool = eq(a.k, b.k)
    provides PartialEq[T = AE, eq = aeq]
    provides Eq[T = AE]
  end

  sort Box
    entity box(v: Int64)
  end

  sort C
    entity red
    entity green
    operation pick(c: C) -> AE =
      match c
        case red() -> ae(k: 1, tag: 8)
        case green() -> ae(k: 2, tag: 0)
    operation mk(c: C) -> AE = ae(k: C.tag(c), tag: 9)
    operation bpick(c: C) -> Box =
      match c
        case red() -> box(v: 1)
        case green() -> box(v: 2)
    operation tag(c: C) -> Int64 =
      match c
        case red() -> 1
        case green() -> 2
    operation code(c: C) -> Int64 =
      match c
        case red() -> 1
        case green() -> 2
  end

  sort Util
    operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
    -- a dictionary selected where the call is written, in an operation with no `requires`
    operation pickD(c: C, x: Int64, y: Int64) -> Int64 =
      match c
        case red() -> Util.sign[A = Int64, WeakOrd = Descending](x, y)
        case green() -> 7
    -- the operation's own `requires`, read through its slot
    operation pickBy[A](c: C, x: A, y: A) -> Int64 requires WeakOrd[T = A] =
      match c
        case red() -> WeakOrd.compare(x, y)
        case green() -> 4
    -- the slot handed on to a callee that requires it
    operation pickVia[A](c: C, x: A, y: A) -> Int64 requires WeakOrd[T = A] =
      match c
        case red() -> Util.sign(x, y)
        case green() -> 4
  end

  -- the sort's `requires`, read through its slot
  sort Holder
    sort A = ?
    requires WeakOrd[T = A]
    operation hpick(c: C, x: A, y: A) -> Int64 =
      match c
        case red() -> WeakOrd.compare(x, y)
        case green() -> 4
  end

  rule bodyNest(?c)      :- C.bpick(?c) = box(v: C.tag(red()))
  rule hostNest(?c)      :- C.bpick(?c) = box(v: Int64.add(0, 1))
  rule waitNest(?c, ?d)  :- C.bpick(?c) = box(v: C.tag(?d))
  rule plain(?c)         :- C.bpick(?c) = box(v: 1)
  rule w(?c)             :- C.pick(?c) = C.mk(red())
  rule wg(1)             :- C.pick(red()) = C.mk(red())
  rule w0()              :- C.pick(?c) = C.mk(red())
  rule w0Naf(1)          :- not(w0())
  rule app(?a, ?b)       :- append(?a, [3]) = append(?b, [4])
  rule app1(?a)          :- append(?a, [3]) = [1, 3]

  rule selDesc(?c)       :- Util.pickD(?c, 1, 5) = 4
  rule selOwn(?c)        :- Util.pickD(?c, 1, 5) = -1
  rule selDescG(1)       :- Util.pickD(red(), 1, 5) = 4
  rule selOwnG(1)        :- Util.pickD(red(), 1, 5) = -1

  rule litBy(?c)         :- Util.pickBy(?c, 1, 5) = -1
  rule litByG(1)         :- Util.pickBy(red(), 1, 5) = -1
  rule litVia(?c)        :- Util.pickVia(?c, 1, 5) = -1
  rule litHold(?c)       :- Holder.hpick(?c, 1, 5) = -1

  rule byOwn[A](?a: A, ?b: A, ?c)  :- WeakOrd[T = A], Util.pickBy(?c, ?a, ?b) = 4
  rule byVia[A](?a: A, ?b: A, ?c)  :- WeakOrd[T = A], Util.pickVia(?c, ?a, ?b) = 4
  rule byHold[A](?a: A, ?b: A, ?c) :- WeakOrd[A], Holder.hpick(?c, ?a, ?b) = 4

  sort Driver
    operation citeOwn[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = C.code(byOwn(x, y).head.c)
    operation descOwn() -> Int64 effects {Error, Error[EmptyStream]} =
      citeOwn[A = Int64, WeakOrd = Descending](1, 5)
    operation plainOwn() -> Int64 effects {Error, Error[EmptyStream]} = C.code(byOwn(1, 5).head.c)
    operation citeVia[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = C.code(byVia(x, y).head.c)
    operation descVia() -> Int64 effects {Error, Error[EmptyStream]} =
      citeVia[A = Int64, WeakOrd = Descending](1, 5)
    operation plainVia() -> Int64 effects {Error, Error[EmptyStream]} = C.code(byVia(1, 5).head.c)
    operation citeHold[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = C.code(byHold(x, y).head.c)
    operation descHold() -> Int64 effects {Error, Error[EmptyStream]} =
      citeHold[A = Int64, WeakOrd = Descending](1, 5)
    operation plainHold() -> Int64 effects {Error, Error[EmptyStream]} = C.code(byHold(1, 5).head.c)
  end
end
"#;

/// `(counts, definite answers)` of each unary relation in `rels`.
fn answered(kb: &mut KnowledgeBase, rels: &[&str]) -> Vec<((usize, usize), Vec<String>)> {
    rels.iter()
        .map(|rel| {
            (
                counts(kb, &format!("wi2hx69.{rel}(?c)")),
                definite_names(kb, &format!("wi2hx69.{rel}")),
            )
        })
        .collect()
}

/// `(cited with Descending, uncited)` of one driver pair — `1` is `red`, `2` is `green`.
fn cited(interp: &mut anthill_core::eval::Interpreter, which: &str) -> (i64, i64) {
    let mut run = |entry: String| match interp.call(&format!("wi2hx69.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    };
    (run(format!("desc{which}")), run(format!("plain{which}")))
}

/// THE ANSWER XBHX3'S GATE COST: OTHER holds a call that runs, so it is read as its value
/// and the split answers. `bodyNest`'s `C.tag(red())` is a bodied call, `hostNest`'s
/// `Int64.add(0, 1)` a host one; both are `box(v: 1)` when the arms meet them, and `?c = red`
/// is the one answer, as for `plain`, which writes `box(v: 1)`.
///
/// FAILS with the gate restored: both (1, 0). `plain` passes either way.
#[test]
fn an_other_operand_holding_a_call_that_runs_is_read_as_its_value() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        answered(&mut kb, &["plain", "bodyNest", "hostNest"]),
        vec![((1, 1), vec!["red".to_string()]); 3],
        "OTHER is `box(v: 1)` once its call has run"
    );
}

/// AN OVERRIDE BEHIND A CALL IS NEVER REFUTED: `C.mk(red())` is `ae(k: 1, tag: 9)`, which
/// `aeq` holds equal to the `red` arm's `ae(k: 1, tag: 8)` (`wg`), and which the per-arm
/// structural `unify` would refute. Read as its value, OTHER reaches `AE`, and P1TPE's decline
/// suspends the split. `w0Naf` is the polarity: NAF over the refutation would prove a false
/// `not`.
///
/// FAILS with OTHER read raw: `w` (0, 0), `w0Naf` (1, 1). Passes with the
/// gate restored, which declines it for an unrelated reason.
#[test]
fn an_override_behind_a_call_is_never_refuted() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(counts(&mut kb, "wi2hx69.wg(1)"), (1, 1), "CONTROL: `?c = red` is a witness");
    assert_eq!(counts(&mut kb, "wi2hx69.w(?c)"), (1, 0), "a suspension, never a refutation");
    assert_eq!(
        counts(&mut kb, "wi2hx69.w0Naf(1)"),
        (1, 0),
        "NAF over the suspension suspends; over a refutation it would hold"
    );
}

/// AN OTHER OPERAND HOLDING A CALL THAT WAITS DECLINES THE SPLIT: `append(?b, [4])` waits on
/// `?b`, so no arm can bind the hoisted variables against data and the recursion would run to
/// the depth cap; `C.tag(?d)` waits on `?d`. Each is one suspension. `app1`, against data, is
/// the control: it solves `?a = [1]`.
///
/// FAILS with OTHER read raw: `app` is 24 rows, a split per step until
/// the depth cap, and `waitNest` 2. Passes with the gate restored.
#[test]
fn an_other_operand_holding_a_call_that_waits_declines_the_split() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        [
            counts(&mut kb, "wi2hx69.app(?a, ?b)"),
            counts(&mut kb, "wi2hx69.waitNest(?c, ?d)"),
            counts(&mut kb, "wi2hx69.app1(?a)"),
        ],
        [(1, 0), (1, 0), (1, 1)],
        "`app` and `waitNest` one suspension each, and they end; `app1` narrows against data"
    );
}

/// A DICTIONARY SELECTED IN AN ARM IS THE ONE THE HOISTED CALL USES. `pickD`'s red arm calls
/// `Util.sign` with `Descending`, 4 at `(1, 5)`; the ground twins say so. The unfold hoisted the
/// call without the typer's stamps, so it ran with `Int64`'s own -1: `selDesc` was REFUTED and
/// `selOwn` answered `red`, definitely — both wrong, with no `requires` on `pickD` at all.
///
/// FAILS with hoisted calls unstamped: `selDesc` (0, 0), `selOwn` (1, 1).
#[test]
fn a_dictionary_selected_in_an_arm_is_the_one_the_hoisted_call_uses() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(counts(&mut kb, "wi2hx69.selDescG(1)"), (1, 1), "CONTROL: `Descending`'s 4");
    assert_eq!(counts(&mut kb, "wi2hx69.selOwnG(1)"), (0, 0), "CONTROL: not `Int64`'s -1");
    assert_eq!(definite_names(&mut kb, "wi2hx69.selDesc"), vec!["red".to_string()]);
    assert_eq!(counts(&mut kb, "wi2hx69.selOwn(?c)"), (0, 0));
}

/// AN OPERATION WITH `requires` IS UNFOLDED, AT LITERALS: the typer builds `Int64`'s
/// `WeakOrd` for the call, and the red arm's `WeakOrd.compare` is woven with it — through the
/// operation's own slot (`pickBy`), handed on to a callee (`pickVia` → `Util.sign`), and through
/// the sort's (`Holder.hpick`). Each answers `?c = red`, as `litByG` does ground.
///
/// FAILS with an operation with `requires` declined: `litBy` and
/// `litVia` are (1, 0). `litHold` passes either way: its `requires` is its sort's, which the
/// decline never read.
#[test]
fn an_operation_with_requires_is_unfolded_at_literals() {
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(counts(&mut kb, "wi2hx69.litByG(1)"), (1, 1), "CONTROL: `Int64`'s -1 at red");
    assert_eq!(
        answered(&mut kb, &["litBy", "litVia", "litHold"]),
        vec![((1, 1), vec!["red".to_string()]); 3]
    );
}

/// A CITED DICTIONARY REACHES THE ARMS. Cited with `Descending`, `compare(1, 5)` is 4, so both
/// arms hold `= 4` and the first row is `red` (1); uncited, the clause derives `Int64`'s own -1
/// and only `green` (2) holds. Through the operation's own slot (`Own`), handed on to a callee
/// (`Via`) and through the sort's (`Hold`).
///
/// FAILS with the slot weave off: each `desc*` is 2, the hoisted call run
/// with the value's own dictionary. With an operation with `requires` declined
/// `Own` and `Via` find no row and the driver traps.
#[test]
fn a_cited_dictionary_reaches_the_arms() {
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(
        ["Own", "Via", "Hold"].map(|which| cited(&mut interp, which)),
        [(1, 2); 3],
        "(cited, uncited) of `Own`, `Via`, `Hold`"
    );
}
