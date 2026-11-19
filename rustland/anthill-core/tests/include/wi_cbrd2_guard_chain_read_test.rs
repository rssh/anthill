//! A CALL REACHED THROUGH ITS GUARD'S CHAIN (WI-20261105-CBRD2). A requirement a clause
//! declares holds its spec's chain (kernel-language §5.3, §8.7): under `rule same[A](?x: A,
//! ?y: A) :- Eq[T = A], eq(?x, ?y)`, the `PartialEq[T = A]` that `eq` needs is the one `Eq`
//! provides, the guard's first sub-dictionary; under `WeakOrd[T = A]`, `gt`'s `PartialOrd[T =
//! A]` is the one `WeakOrd` requires. The clause's weave read the guard's chain only in a
//! guarded equation (part 5n). In any other clause the call took a read of its own that no
//! citation fills:
//!
//! * a query with no bracket left it unrouted, and it found the provider from the values of
//!   `?x` and `?y` when the call ran (`resolve::value_reads_by_this_thread`);
//! * a citation that chose the guard's instance (`cmpOrd[A = Int64, Ord = Descending]`)
//!   built the read at the citation's types alone, so `compare` ran `Int64`'s own order
//!   beside a guard holding `Descending`.
//!
//! The call now takes the guard's sub-dictionary, read by `Dictionary.sub` off the guard's
//! dictionary at load (`composed_from_guards`), as an equation's does: what the citation
//! chose, and nothing read from the values. The goal the chain is searched for fixes only the
//! spec's carrier, and leaves the rest open for the chain's entry to write: `isEmpty` under
//! `FiniteCollection[C = C]` is the `Iterable[C = C, Element = Element, E = E]` it requires.
//! And a guard whose chain holds the call's spec only at another instance supplies nothing,
//! where it was taken to supply any (`declared_guard_requires`, removed): the call is refused.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The equation-only weave restored: every row but the last fails.
//!   [`a_call_through_the_chain_reads_no_value`], [`the_chain_is_read_two_steps_down`] and
//!   [`a_chain_entry_writing_more_than_the_call_covers_it`] on the reads (one per query; two
//!   for the boxes), each verdict unchanged. [`the_citations_choice_reaches_a_call_through_the_chain`]
//!   on the answer: `cmpOrd[A = Int64, Ord = Descending](1, 5, ?c)` gives `-1`, `Int64`'s own,
//!   where `Descending` gives `4` (the query with no bracket gives `-1` either way: the
//!   control). [`an_operations_citation_hands_its_choice_through_the_chain`] fails to load:
//!   `viaOrd[A](x: A, y: A) requires Ord[T = A] = cmpOrd(x, y).head.c` is refused, `cmpOrd`'s
//!   own read of `WeakOrd[T = A]` open at the citation, which no caller passes; the spec admits
//!   it (§5.3: the declared `Ord` holds its chain).
//! * The chain's goal with nothing left open: [`a_chain_entry_writing_more_than_the_call_covers_it`]
//!   fails on the reads (two), no other row.
//! * [`an_operations_slot_is_filled_through_the_chain`] is refused at load with HEAD's source
//!   (both changes out): a slot at the guard's parameter was the clause's refusal.
//! * The guard's spec taken to supply any spec its chain holds:
//!   [`a_chain_holding_the_spec_at_another_instance_supplies_nothing`] fails, its program
//!   loading clean.

use anthill_core::kb::resolve::value_reads_by_this_thread;

use crate::common::{load_errors_of, load_kb_with, load_stdlib_kb, pattern_answer_counts, pattern_last_ints};

/// `f`'s result and the reads for a call it answered from a value, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = value_reads_by_this_thread();
    let r = f();
    (r, value_reads_by_this_thread() - before)
}

const CHAIN: &str = r#"
namespace test.cbrd2.chain
  import anthill.prelude.{Int64, Bool, String, List, Error, EmptyStream, Eq, Hash, WeakOrd, Ord, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  import anthill.prelude.Iterable.{isEmpty}
  import anthill.prelude.Numeric.{sub}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gt}
  sort Descending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Ascending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end
  -- `Eq provides PartialEq[T = T]`: a conversion in the chain.
  rule same[A](?x: A, ?y: A) :- Eq[T = A], eq(?x, ?y)
  -- `WeakOrd requires PartialOrd[T]`: a requirement in the chain.
  rule bigger[A](?a: A, ?b: A) :- WeakOrd[T = A], gt(?a, ?b)
  -- `Ord provides WeakOrd[T = T]`: the order the guard's provider writes.
  rule cmpOrd[A](?a: A, ?b: A, ?c) :- Ord[T = A], WeakOrd.compare(?a, ?b, ?c)
  -- `Hash provides Eq[T = T]`, which provides `PartialEq[T = T]`: two steps.
  rule sameH[A](?x: A, ?y: A) :- Hash[T = A], eq(?x, ?y)
  -- `FiniteCollection requires Iterable[C = C, Element = Element, E = E]`: the guard writes
  -- only the carrier, and the chain the rest.
  rule emp[C](?ls: C, ?b) :- FiniteCollection[C = C], isEmpty(?ls, ?b)
  sort Box
    entity Box(items: List[T = String])
  end
  fact Box(items: ["a", "b"])
  fact Box(items: [])
  rule emptyLen(?n) :- Box(items: ?ls), emp(?ls, true), size(?ls, ?n)
  rule fullLen(?n) :- Box(items: ?ls), emp(?ls, false), size(?ls, ?n)
end
"#;

/// Operations citing `cmpOrd`, a namespace of their own over [`CHAIN`].
const CITED: &str = r#"
namespace test.cbrd2.chain.cited
  import anthill.prelude.{Int64, Error, EmptyStream, Ord}
  import test.cbrd2.chain.{cmpOrd, Descending, Ascending}
  operation viaOrd[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
    requires Ord[T = A] = cmpOrd(x, y).head.c
  operation viaD() -> Int64 effects {Error, Error[EmptyStream]} =
    viaOrd[A = Int64, Ord = Descending](1, 5)
  operation viaA() -> Int64 effects {Error, Error[EmptyStream]} =
    viaOrd[A = Int64, Ord = Ascending](1, 5)
  operation direct() -> Int64 effects {Error, Error[EmptyStream]} =
    cmpOrd[A = Int64, Ord = Descending](1, 5).head.c
end
"#;

/// `same` and `bigger` give the verdicts the values do, and read nothing from them: the
/// dictionary `eq` and `gt` dispatch through is the guard's, which the query passes at `Int64`.
#[test]
fn a_call_through_the_chain_reads_no_value() {
    let mut kb = load_kb_with(CHAIN);
    for (query, holds) in [
        ("test.cbrd2.chain.same(1, 1)", true),
        ("test.cbrd2.chain.same(1, 2)", false),
        ("test.cbrd2.chain.bigger(3, 1)", true),
        ("test.cbrd2.chain.bigger(1, 3)", false),
    ] {
        let (answers, reads) = counting(|| pattern_answer_counts(&mut kb, query));
        let expected = if holds { (1, 1) } else { (0, 0) };
        assert_eq!(answers, expected, "{query}");
        assert_eq!(reads, 0, "{query}: a dictionary read off the values");
    }
}

/// The citation chooses `Descending` for the guard, and `compare` runs it: `4` at `(1, 5)`.
/// With no bracket the query passes `Int64`'s own, `-1` — the control.
#[test]
fn the_citations_choice_reaches_a_call_through_the_chain() {
    let mut kb = load_kb_with(CHAIN);
    let (chosen, reads) = counting(|| {
        pattern_last_ints(&mut kb, "test.cbrd2.chain.cmpOrd[A = Int64, Ord = test.cbrd2.chain.Descending](1, 5, ?c)")
    });
    assert_eq!(chosen, vec![4], "the guard's `Descending` orders the call");
    assert_eq!(reads, 0);
    let (own, reads) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.chain.cmpOrd(1, 5, ?c)"));
    assert_eq!(own, vec![-1], "CONTROL: `Int64`'s own");
    assert_eq!(reads, 0, "a dictionary read off the values");
}

/// `Hash provides Eq`, `Eq provides PartialEq`: `eq` under a `Hash` guard is two sub-reads
/// down, and nothing is read from the values.
#[test]
fn the_chain_is_read_two_steps_down() {
    let mut kb = load_kb_with(CHAIN);
    for (query, holds) in [("test.cbrd2.chain.sameH(4, 4)", true), ("test.cbrd2.chain.sameH(4, 5)", false)] {
        let (answers, reads) = counting(|| pattern_answer_counts(&mut kb, query));
        assert_eq!(answers, if holds { (1, 1) } else { (0, 0) }, "{query}");
        assert_eq!(reads, 0, "{query}: a dictionary read off the values");
    }
}

/// `isEmpty` is `Iterable`'s, which `FiniteCollection` requires at its carrier and at
/// parameters the guard leaves unwritten: the chain's entry writes them, and the call fixes
/// only the carrier. Each box answers by its own length, nothing read from the lists.
#[test]
fn a_chain_entry_writing_more_than_the_call_covers_it() {
    let mut kb = load_kb_with(CHAIN);
    for (query, lengths) in [("test.cbrd2.chain.emptyLen(?n)", vec![0]), ("test.cbrd2.chain.fullLen(?n)", vec![2])] {
        let (answers, reads) = counting(|| pattern_last_ints(&mut kb, query));
        assert_eq!(answers, lengths, "{query}");
        assert_eq!(reads, 0, "{query}: a dictionary read off the values");
    }
}

/// From typed code: an operation holding `Ord[T = A]` cites `cmpOrd` at its own `A`, the
/// bracket choosing the rival at `viaOrd`, and the bracket at the citation itself chooses it
/// too.
#[test]
fn an_operations_citation_hands_its_choice_through_the_chain() {
    let mut interp = crate::common::interp_for(&format!("{CHAIN}\n{CITED}"));
    let mut int = |op: &str| match interp
        .call(&format!("test.cbrd2.chain.cited.{op}"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
    {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("{op}: expected an Int64, got {other:?}"),
    };
    assert_eq!(int("viaD"), 4);
    assert_eq!(int("viaA"), -4);
    assert_eq!(int("direct"), 4);
}

/// `Derived` requires `Base` at `List[T = T]`, not at `T`: its chain holds no `Base[T = A]`,
/// and a call of `Base` at `A` under the guard is a call at a type the clause declares nothing
/// for — refused, naming `Base` (§5.3: "a call at another of the clause's type parameters does
/// not"). It loaded before: the guard's spec was taken to supply any `Base`, and the call took a
/// read of its own, which no citation fills and which reads the provider off the value.
#[test]
fn a_chain_holding_the_spec_at_another_instance_supplies_nothing() {
    let errors = load_errors_of(
        r#"
namespace test.cbrd2.chain.apart
  import anthill.prelude.{Int64, List}
  sort Base
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Derived
    sort T = ?
    requires Base[T = List[T = T]]
  end
  sort IntBase
    provides Base[T = Int64]
    operation tag(x: Int64) -> Int64 = 1
  end
  sort ListBase
    provides Base[T = List[T = Int64]]
    operation tag(x: List[T = Int64]) -> Int64 = 2
  end
  sort IntDerived
    provides Derived[T = Int64]
  end
  rule r[A](?x: A, ?t) :- Derived[T = A], Base.tag(?x, ?t)
end
"#,
    );
    assert!(
        errors.iter().any(|e| e.contains("Base") && e.contains("the clause declares none")),
        "refused, naming `Base`: {errors:?}"
    );
}

/// A SLOT of an operation's own `requires` at the guard's parameter is the guard's
/// sub-dictionary too: `Util.sign` requires `WeakOrd[T = A]`, which `Ord[T = A]` provides, and
/// `s[A = Int64, Ord = Descending](1, 5, ?r)` answers `Descending`'s `4`, nothing read from the
/// values. Refused at load with HEAD's source ("the clause declares none"), against §5.3.
#[test]
fn an_operations_slot_is_filled_through_the_chain() {
    let mut kb = load_kb_with(
        r#"
namespace test.cbrd2.chain.slot
  import anthill.prelude.{Int64, Ord, WeakOrd}
  import anthill.prelude.Numeric.{sub}
  sort Descending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Util
    operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
  end
  rule s[A](?x: A, ?y: A, ?r) :- Ord[T = A], Util.sign(?x, ?y, ?r)
end
"#,
    );
    let (chosen, reads) = counting(|| {
        pattern_last_ints(&mut kb, "test.cbrd2.chain.slot.s[A = Int64, Ord = test.cbrd2.chain.slot.Descending](1, 5, ?r)")
    });
    assert_eq!(chosen, vec![4], "the guard's `Descending` fills `sign`'s slot");
    assert_eq!(reads, 0);
    let (own, _) = counting(|| pattern_last_ints(&mut kb, "test.cbrd2.chain.slot.s(1, 5, ?r)"));
    assert_eq!(own, vec![-1], "CONTROL: `Int64`'s own");
}
