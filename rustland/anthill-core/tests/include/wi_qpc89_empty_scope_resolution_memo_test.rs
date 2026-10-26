//! WI-20260926-QPC89 — A RUN-TIME DICTIONARY IS DERIVED ONCE PER GOAL. A rule body's
//! requirement read and a bridged call's frame hold argument values and no caller
//! dictionary, so each resolves its goal in an empty scope; `rd(leaf(), ?n)` asks
//! `Desc[T = Leaf]` at every query, and the answer is read off the declarations and the
//! provisions alone. `typing::resolve_in_empty_scope` memoizes a ground goal's answer
//! (`KnowledgeBase::empty_scope_resolve_cache`), dropped at the start of a typer run and
//! wherever a provision row is filed or unfiled.
//!
//! ## Back-out
//!
//! Measured with each part backed out by a switch, in one build:
//!
//! * No memo at all: all four rows FAIL — the first two at "is held after the first
//!   query", the last two at "is held" before their later load. Their answers hold
//!   either way.
//! * The rule-body read resolving past the memo (`fetch_built_dictionary` calling
//!   `resolve_with_rung`): `a_rule_body_read_keeps_its_derivation` FAILS, and the two
//!   lifetime rows at "is held" — their goals are asked by a read.
//! * The bridge resolving past it: `a_bridged_calls_frame_keeps_its_derivation` FAILS,
//!   and only it.
//! * Not dropped where a provision row is filed: `a_provision_filed_after_the_
//!   derivation_answers` FAILS — `[]` for `[5]`, the kept `NoMatch` read again.
//! * Not dropped at a typer run's start: `a_default_declared_by_a_later_load_answers_a_
//!   kept_tie` FAILS — `[]` for `[7]`, the kept tie.
//!
//! The four pass under the three load recipes.

use anthill_core::kb::load::LoadOptions;
use anthill_core::kb::KnowledgeBase;

/// `Leaf` provides `Desc` itself; `rd` reads the dictionary in its body, and `tw` calls an
/// operation whose own `requires` the bridge fills from the values.
const READS: &str = r#"
namespace test.qpc89.reads
  import anthill.prelude.{Int64}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  sort Util
    operation twice[A](x: A) -> Int64 requires Desc[T = A] =
      Int64.add(Desc.describe(x), Desc.describe(x))
  end

  rule rd(?x, ?n) :- Desc.describe(?x, ?n)
  rule rdLeaf(?n) :- rd(leaf(), ?n)
  rule tw(?x, ?n) :- Util.twice(?x, ?n)
  rule twLeaf(?n) :- tw(leaf(), ?n)
end
"#;

/// Two witnesses of `Desc[T = Leaf]` and no default: the goal ties.
const TIE: &str = r#"
namespace test.qpc89.tie
  import anthill.prelude.{Int64}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  sort Other
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
  end

  rule rd(?x, ?n) :- Desc.describe(?x, ?n)
  rule rdLeaf(?n) :- rd(leaf(), ?n)
end
"#;

/// A later load that settles [`TIE`]'s tie, and files no provision row.
const TIE_SETTLED: &str = r#"
namespace test.qpc89.settled
  import anthill.reflect.typing.DefaultProvider
  import test.qpc89.tie.{Desc, Rival}

  fact DefaultProvider(spec: Desc, provider: Rival)
end
"#;

/// `Box` provides `Desc` where its element does, and nothing provides it at `Leaf`.
const CONDITIONED: &str = r#"
namespace test.qpc89.cond
  import anthill.prelude.{Int64}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort Box
    sort V = ?
    entity box(v: V)
    provides Desc[T = Box[V = V]] :- Desc[T = V]
    operation describe(x: Box[V = V]) -> Int64 = 5
  end

  rule rd(?x, ?n) :- Desc.describe(?x, ?n)
  rule rdBox(?n) :- rd(box(v: leaf()), ?n)
end
"#;

/// A later load that provides [`CONDITIONED`]'s missing condition.
const CONDITION_MET: &str = r#"
namespace test.qpc89.met
  import anthill.prelude.{Int64}
  import test.qpc89.cond.{Desc, Leaf}

  sort LeafDesc
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
end
"#;

/// The relation `qn`'s one column, asked as a query: the definite integer answers.
fn definite_ints(kb: &mut KnowledgeBase, qn: &str) -> Vec<i64> {
    let rows = crate::common::query_unary(kb, qn);
    rows.iter()
        .filter(|(_, definite)| *definite)
        .map(|(v, _)| {
            crate::common::scalar_int(kb, v)
                .unwrap_or_else(|| panic!("`{qn}` answers an integer; got {v:?}"))
        })
        .collect()
}

/// A rule body's read derives its dictionary at the first query, and the derivation is
/// kept: the second query answers the same with no new entry.
#[test]
fn a_rule_body_read_keeps_its_derivation() {
    let mut kb = crate::common::load_kb_with(READS);
    let before = kb.empty_scope_resolve_cache_len();
    assert_eq!(definite_ints(&mut kb, "test.qpc89.reads.rdLeaf"), [7]);
    assert_eq!(
        kb.empty_scope_resolve_cache_len(),
        before + 1,
        "`Desc[T = Leaf]` is held after the first query",
    );
    assert_eq!(definite_ints(&mut kb, "test.qpc89.reads.rdLeaf"), [7]);
    assert_eq!(kb.empty_scope_resolve_cache_len(), before + 1, "and asked again, not added");
}

/// The bridged call's frame, the same way: `twice`'s `requires Desc[T = A]` is derived
/// from `leaf()` once.
#[test]
fn a_bridged_calls_frame_keeps_its_derivation() {
    let mut kb = crate::common::load_kb_with(READS);
    let before = kb.empty_scope_resolve_cache_len();
    assert_eq!(definite_ints(&mut kb, "test.qpc89.reads.twLeaf"), [14]);
    assert_eq!(
        kb.empty_scope_resolve_cache_len(),
        before + 1,
        "`twice`'s slot is held after the first query",
    );
    assert_eq!(definite_ints(&mut kb, "test.qpc89.reads.twLeaf"), [14]);
    assert_eq!(kb.empty_scope_resolve_cache_len(), before + 1, "and asked again, not added");
}

/// A later load that declares a default changes what a tie resolves to without filing a
/// provision row, so a memoized tie is dropped where its typer starts.
#[test]
fn a_default_declared_by_a_later_load_answers_a_kept_tie() {
    let mut kb = crate::common::load_kb_with(TIE);
    assert_eq!(definite_ints(&mut kb, "test.qpc89.tie.rdLeaf"), Vec::<i64>::new(), "a tie");
    assert!(kb.empty_scope_resolve_cache_len() > 0, "the tie is held");
    crate::common::expect_loaded(crate::common::load_in_a_later_call(
        &mut kb,
        TIE_SETTLED,
        LoadOptions::default(),
    ));
    assert_eq!(definite_ints(&mut kb, "test.qpc89.tie.rdLeaf"), [7], "`Rival`, the default");
}

/// A provision filed after the memo filled — here by a load that stops before its typer —
/// drops it: the condition `NoMatch` kept from the first query is not the answer.
#[test]
fn a_provision_filed_after_the_derivation_answers() {
    let mut kb = crate::common::load_kb_with(CONDITIONED);
    assert_eq!(
        definite_ints(&mut kb, "test.qpc89.cond.rdBox"),
        Vec::<i64>::new(),
        "nothing provides `Desc[T = Leaf]`",
    );
    assert!(kb.empty_scope_resolve_cache_len() > 0, "the failed resolution is held");
    crate::common::expect_loaded(crate::common::load_in_a_later_call(
        &mut kb,
        CONDITION_MET,
        LoadOptions {
            run_typer: false,
            ..LoadOptions::default()
        },
    ));
    assert_eq!(definite_ints(&mut kb, "test.qpc89.cond.rdBox"), [5], "`Box`'s own `describe`");
}
