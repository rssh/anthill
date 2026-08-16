//! WI-1109 — the ordering tower split three ways: `PartialOrd` / `WeakOrd` / `Ord`.
//!
//! WHAT THIS FILE IS FOR. The migration re-pointed ~30 existing fixtures at `WeakOrd`,
//! and a re-pointed fixture measures the OLD capability under a new name. Nothing drove
//! the two things WI-1109 actually adds: that the weak floor is a floor a carrier can
//! stop at (and is REFUSED above it), and that `Ord provides WeakOrd` lets a carrier
//! write ONE provision where it used to write two. Both are driven here, each with the
//! control that says the assertion is not vacuous.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT — MEASURED, not predicted, and the
//! measurement corrected a first draft of this note that claimed one failure:
//!
//!   * comment out `derive_forwarded_provisions` (kb/load.rs) and SEVEN of the eight
//!     fail. Not just the forwarding test: `Int64`/`String`/`BigInt` write only
//!     `provides Ord`, so without the derived rows the stdlib's own carriers have no
//!     `WeakOrd` floor and every `SortedSet` program here loses its slot — including the
//!     quotient assertions, which do not otherwise depend on the derivation.
//!     `a_weakord_only_comparator_is_refused_where_ord_is_required` is the one that
//!     still passes, and it passes VACUOUSLY (it expects load errors and gets different
//!     ones), which is why its assertion below pins the refusal's own words rather than
//!     merely asking that something failed.
//!   * back out `Ord provides WeakOrd[T = T]` (ordered.anthill) and
//!     `an_ord_constrained_body_reaches_compare` fails — that clause is what puts a
//!     `WeakOrd` dictionary inside an `Ord` one, and without it every `Ord`-constrained
//!     generic that calls `compare` stops resolving.
//!
//!     WI-1110 CHANGED WHICH CLAUSE THAT IS, and the note is corrected rather than
//!     dropped because the correction is the finding. WI-1109 shipped `requires
//!     WeakOrd[T]` BESIDE the `provides`, and this line named the `requires` half as
//!     what the test measured. They were one edge written twice: a spec's `provides` is
//!     a CONVERSION and is a chain entry in its own right, so the `requires` was
//!     redundant — and, filed as a provider row, it also made `Ord` a candidate answer
//!     to every `WeakOrd` goal. One clause now does both jobs.
//!   * restore `compare` to `Ord` and the whole file fails to load.
//!
//! The quotient assertions (`the_class_collapses…`, `union_is_left_biased…`) pin
//! behaviour the split DECLARED rather than changed — sortedset.anthill's EQUALITY
//! section now states it as contract. They are here because that contract had no witness
//! at all before, not because WI-1109 moved them.

use anthill_core::eval::Value;

/// A genuinely COARSE comparator: `compare("zz","aa") = 0` while `eq("zz","aa")` is
/// false, so its kernel is strictly wider than `Eq`. It is a lawful `WeakOrd[String]`
/// and CANNOT be an `Ord[String]`.
const BY_LENGTH: &str = r#"
  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
"#;

/// A comparator whose kernel IS `Eq`, written with ONE provision — the forwarding under
/// test. Before WI-1109 a carrier had to write the lower floor as well.
const ASCENDING: &str = r#"
  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end
"#;

const READ: &str = r#"
  sort Read
    operation first(l: List[T = String]) -> String =
      match l
        case nil() -> "<empty>"
        case cons(h, t) -> h
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool, SortedSet}}\n  \
         import anthill.prelude.List.{{nil, cons}}\n\
         {BY_LENGTH}{ASCENDING}{READ}{body}\nend\n"
    )
}

/// `Value` is not `PartialEq`, so both readers PROJECT it — the `wi844` shape.
fn eval_str(src: &str, entry: &str) -> String {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Str(v)) => v,
        other => panic!("{entry} must answer a String; got {other:?}"),
    }
}

fn eval_int(src: &str, entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(v)) => v,
        other => panic!("{entry} must answer an Int64; got {other:?}"),
    }
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

// ── the weak floor is a floor a carrier can STOP at ──────────────────────────

/// A `WeakOrd`-only comparator SORTS. Not "loads" — the value is asserted, because a
/// declaration that resolves and never runs is exactly what this repo's rules call not
/// evidence.
#[test]
fn a_weakord_only_comparator_sorts() {
    let src = program(
        "wi1109.sorts",
        "  sort D\n    \
         operation go(n: Int64) -> String =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         Read.first(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, \"aaa\"), \"zz\")))\n  end",
    );
    assert_eq!(
        eval_str(&src, "wi1109.sorts.D.go"),
        "zz",
        "`ByLength` orders by length, so the 2-char `zz` precedes the 3-char `aaa` — \
         a comparator that never reached the set would answer `aaa` (insertion order) \
         or `<empty>`"
    );
}

/// …AND IS REFUSED ABOVE ITS FLOOR. The whole content of `Ord` is the extra law, so a
/// carrier that cannot discharge it must not be usable where `Ord` is demanded.
#[test]
fn a_weakord_only_comparator_is_refused_where_ord_is_required() {
    let src = program(
        "wi1109.refused",
        "  sort Strict\n    \
         sort T = ?\n    \
         requires SO: Ord[T]\n    \
         operation tag(x: T) -> Int64 = 0\n  end\n  \
         sort D\n    \
         operation go(n: Int64) -> Int64 = Strict.tag[SO = ByLength](\"zz\")\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("ByLength")
                && e.contains("does not provide anthill.prelude.Ord")
        }),
        "a `WeakOrd`-only witness named at an `Ord` slot must be refused IN THOSE WORDS \
         — pinned rather than merely asserting that something failed, because with the \
         derivation backed out this program fails for an unrelated reason and a loose \
         `any(|e| …)` would pass vacuously: {errs:?}"
    );
}

/// THE CONTROL for the refusal above: the identical program at the `WeakOrd` slot the
/// witness DOES reach loads and runs. Without this pair, the refusal could be a witness
/// that works nowhere rather than one that works below `Ord`.
#[test]
fn the_same_witness_is_accepted_at_the_weak_slot() {
    let src = program(
        "wi1109.accepted",
        "  sort Loose\n    \
         sort T = ?\n    \
         requires SO: WeakOrd[T]\n    \
         operation tag(x: T) -> Int64 = 1\n  end\n  \
         sort D\n    \
         operation go(n: Int64) -> Int64 = Loose.tag[SO = ByLength](\"zz\")\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi1109.accepted.D.go"),
        1,
        "the same witness at the floor it provides must be accepted AND run"
    );
}

// ── the forwarding: ONE provision, both floors ───────────────────────────────

/// `Ascending` writes `provides Ord[T = Int64]` and NOTHING else. `SortedSet`'s slot is
/// `O: WeakOrd[T]`. This runs only because `derive_forwarded_provisions` materialized
/// the `WeakOrd[Int64]` row from the `Ord` one — the point of the whole increment.
#[test]
fn one_provides_ord_answers_a_weakord_slot() {
    let src = program(
        "wi1109.forward",
        "  sort D\n    \
         operation go(n: Int64) -> Int64 =\n      \
         let s = SortedSet.empty[T = Int64, O = Ascending]()\n      \
         match SortedSet.toList(SortedSet.insert(SortedSet.insert(s, 7), 3))\n        \
         case nil() -> -1\n        \
         case cons(h, t) -> h\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi1109.forward.D.go"),
        3,
        "one `provides Ord` must satisfy a `WeakOrd` slot AND sort through it; -1 would \
         mean the set came back empty"
    );
}

/// An `Ord`-CONSTRAINED body reaches `compare`, which lives on `WeakOrd`. This is what
/// `Ord provides WeakOrd[T = T]` buys (WI-1110; it was `requires WeakOrd[T]` when this
/// test was written, and the two collapsed into one clause), and it is the shape of
/// every ordering-generic a downstream program writes.
#[test]
fn an_ord_constrained_body_reaches_compare() {
    let src = format!(
        "\nnamespace wi1109.constrained\n  \
         import anthill.prelude.{{Ord, WeakOrd, Int64}}\n\
{}",
        "  sort Holder\n    \
         sort T = ?\n    \
         requires Ord[T]\n    \
         operation cmp(a: T, b: T) -> Int64 = WeakOrd.compare(a, b)\n  end\n  \
         sort D\n    \
         operation go(n: Int64) -> Int64 = Holder.cmp(7, 3)\n  end\nend\n",
    );
    assert!(
        eval_int(&src, "wi1109.constrained.D.go") > 0,
        "`requires Ord[T]` must supply the `WeakOrd` dictionary its body dispatches \
         through — 7 vs 3 is positive under the carrier's own order. WI-1110: the \
         dictionary now arrives through `Ord`'s SELF-SUPPLIED chain entry rather than \
         through a `requires` clause, and the value is the same"
    );
}

// ── the quotient, now contract rather than discovery ─────────────────────────

/// A coarse kernel makes the set a set of CLASSES, and one member of each survives.
#[test]
fn the_class_collapses_and_the_incumbent_survives() {
    let size = program(
        "wi1109.collapse",
        "  sort D\n    \
         operation go(n: Int64) -> Int64 =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         List.length(SortedSet.toList(\n        \
         SortedSet.insert(SortedSet.insert(SortedSet.insert(s, \"zz\"), \"aa\"), \"b\")))\n  end",
    );
    assert_eq!(
        eval_int(&size, "wi1109.collapse.D.go"),
        2,
        "`zz` and `aa` are one ByLength class, so three inserts leave TWO elements"
    );

    let rep = program(
        "wi1109.rep",
        "  sort D\n    \
         operation go(n: Int64) -> String =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         Read.first(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, \"zz\"), \"aa\")))\n  end",
    );
    assert_eq!(
        eval_str(&rep, "wi1109.rep.D.go"),
        "zz",
        "`insert` keeps the INCUMBENT — the first of a class inserted is the one stored"
    );
}

/// …and `union` keeps the LEFT operand's representative, so it is NOT commutative under
/// a coarse kernel. Both directions, because one alone cannot show a bias.
#[test]
fn union_is_left_biased_in_both_directions() {
    let go = |ns: &str, order: &str| {
        let src = program(
            ns,
            &format!(
                "  sort D\n    \
                 operation go(n: Int64) -> String =\n      \
                 let a = SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\")\n      \
                 let b = SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"aa\")\n      \
                 Read.first(SortedSet.toList(SortedSet.union({order})))\n  end"
            ),
        );
        eval_str(&src, &format!("{ns}.D.go"))
    };
    assert_eq!(go("wi1109.uab", "a, b"), "zz");
    assert_eq!(go("wi1109.uba", "b, a"), "aa");
}

/// THE CONTROL for both quotient assertions: at a kernel that IS `Eq` — the carrier's
/// own `Ord[String]` — nothing collapses and operand order cannot matter. Without this,
/// the two above would be consistent with `SortedSet` simply being broken.
#[test]
fn a_fine_kernel_collapses_nothing() {
    let src = program(
        "wi1109.fine",
        "  sort D\n    \
         operation go(n: Int64) -> Int64 =\n      \
         let s = SortedSet.empty[T = String, O = String]()\n      \
         List.length(SortedSet.toList(\n        \
         SortedSet.insert(SortedSet.insert(SortedSet.insert(s, \"zz\"), \"aa\"), \"b\")))\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi1109.fine.D.go"),
        3,
        "under the host's own `Ord[String]` the three strings are three ELEMENTS — the \
         collapse above belongs to the comparator, not to `SortedSet`"
    );
}

// ── the forwarding discharge is BINDING-PRECISE ──────────────────────────────

/// `forwarded_to_requires` (kb/typing.rs) lets a spec-to-spec forwarding be discharged
/// by the PROVIDER's own `requires`. It must match the required spec AT THE GOAL'S
/// BINDINGS, not merely by spec name: with two parameters, a `requires Eq[A]` would
/// otherwise answer a goal asking `Eq[B]`, and the forwarding would be certified where
/// the equality it needs was never required.
///
/// BACK-OUT: drop the `bindings_cover` clause from `forwarded_to_requires` and this
/// loads clean — the `Eq` entry bound to `A` answers the `Eq[B]` goal by spec name
/// alone. That is the control; the sibling `self_provides_required` arm carries the
/// same precision for the same reason.
#[test]
fn a_forwarding_is_not_discharged_by_a_requires_at_other_bindings() {
    let src = "
namespace wi1109.bindprec
  import anthill.prelude.{Eq, Int64}
  sort Sp
    sort X = ?
    sort Y = ?
    requires Eq[Y]
    operation probe(x: X, y: Y) -> Int64
  end
  sort S
    sort A = ?
    sort B = ?
    requires Eq[A]
    provides Sp[X = A, Y = B]
    operation probe(x: A, y: B) -> Int64 = 0
  end
end
";
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("anthill.prelude.Eq")),
        "`S` requires `Eq[A]` and forwards `Sp` whose `Eq` requirement is on `Y = B`, \
         so nothing discharges `Eq[B]` and the provision must be refused naming `Eq`: \
         {errs:?}"
    );
}

// ── a DERIVED row must not be reported as the author's text ──────────────────

/// A derived row is held to every check a written one is — a concrete carrier owes the
/// operation however the row arrived, so exempting it (the `is_unbacked_derived_provision`
/// route `eq_derive` uses) would suppress a CORRECT refusal. What it must not do is
/// report that refusal against a `provides` clause the author never wrote.
///
/// The pair is what makes this discriminating: the two carriers differ ONLY in which
/// floor they name, and before the fix their refusals were word-for-word identical.
///
/// NOTE the shape: both carriers are CONCRETE (they declare an entity). A
/// constructor-less sort is skipped by `check_provider_operations` entirely
/// ("abstract carrier → sub-interface, ops may stay primitives"), so the review's own
/// failure scenario — which used one — does not reach this walk at all.
#[test]
fn a_derived_provision_names_the_clause_the_author_wrote() {
    let derived = load_errs(
        "\nnamespace wi1109.derived\n  import anthill.prelude.{Ord, WeakOrd, Int64}\n\
         \x20 enum MyBox\n    entity box(v: Int64)\n    provides Ord[T = MyBox]\n  end\nend\n",
    );
    assert!(
        derived.iter().any(|e| {
            e.contains("backs no operation 'anthill.prelude.WeakOrd.compare'")
                && e.contains("is not written on this carrier")
                && e.contains("DERIVED from its `provides anthill.prelude.Ord`")
        }),
        "the carrier wrote `provides Ord` and nothing else, so the `WeakOrd` refusal must \
         say where that row came from: {derived:?}"
    );

    let written = load_errs(
        "\nnamespace wi1109.written\n  import anthill.prelude.{Ord, WeakOrd, Int64}\n\
         \x20 enum MyBox2\n    entity box2(v: Int64)\n    provides WeakOrd[T = MyBox2]\n  end\nend\n",
    );
    assert!(
        written.iter().any(|e| {
            e.contains("backs no operation 'anthill.prelude.WeakOrd.compare'")
                && !e.contains("is not written on this carrier")
        }),
        "the CONTROL: a carrier that DID write `provides WeakOrd` must get the refusal \
         with no derived-row note — without this half the note could be unconditional \
         and the assertion above would not discriminate: {written:?}"
    );
}
