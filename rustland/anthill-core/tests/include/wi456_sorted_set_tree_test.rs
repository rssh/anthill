//! WI-456 — `SortedSet` is a WEIGHT-BALANCED tree (Adams; `Data.Set`'s δ = 3, ratio = 2),
//! where it was an ascending list: `insert` O(log n) instead of O(n), `union` by split and
//! link, `size` O(1).
//!
//! WHAT A TEST OF A DATA STRUCTURE HAS TO DRIVE. Every public operation answers the same
//! values a list would, so value assertions alone would stay green on an UNBALANCED tree
//! — or on the old list. The balance invariant is therefore asserted DIRECTLY, by a
//! checker written in the test program that walks the public `tip` / `bin` constructors:
//! every node's `n` is its element count, and neither subtree outweighs the other more
//! than threefold. Ascending insertion is the input that degenerates a tree that does not
//! rebalance into a list, so it is the one driven.
//!
//! CONTROLS, per test, as CLAUDE.md asks:
//!  * `ascending_inserts_stay_balanced` / `union_is_ordered_balanced_and_left_biased` —
//!    MEASURED with `balance` reduced to `node(x, l, r)` (no rotation): every value
//!    assertion still passed and only the two `balanced` ones failed. That is the whole
//!    reason the checker exists.
//!  * `equality_is_extensional_not_structural` carries its own control INSIDE it: the
//!    `===` row asserts the two builds really are different trees, without which the `=`
//!    row would prove nothing. Its element-eq row fails if `sameElements` compares
//!    structurally rather than through the element's `PartialEq`.
//!  * `insert_keeps_the_incumbent` PASSES either way by design — it held on the
//!    list-backed version too. It is here because the tree rewrites the survival rule's
//!    site (`insert`'s `else s`), not because it measures the tree.

use anthill_core::eval::Value;

/// The checker and a filler, over `Int64` with its own ordering, plus `ByLength` for the
/// representative-survival rows. `Int64` has ONE `WeakOrd` provider here, so the sets are
/// built with `O = Int64` and nothing ties.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{WeakOrd, PartialOrd, PartialEq, Eq, String, Int64, List, Bool, SortedSet}}
  import anthill.prelude.SortedSet.{{tip, bin}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.PartialOrd.{{lt, gt, lte}}
  import anthill.prelude.Additive.{{add}}
  import anthill.prelude.Multiplicative.{{mul}}

  sort ByLength
    import anthill.prelude.String.{{length}}
    import anthill.prelude.Additive.{{sub}}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  sort Check
    -- The weight invariant, at every node: `n` is the node's element count, and the
    -- two subtrees are within δ = 3 of each other unless together they hold at most one.
    operation balanced(s: SortedSet[T = Int64, O = Int64]) -> Bool =
      match s
        case tip() -> true
        case bin(n, _, l, r) ->
          let sl = SortedSet.size(l)
          let sr = SortedSet.size(r)
          if n != add(add(sl, sr), 1) then false
          else if weightOk(sl, sr) then both(l, r)
          else false

    operation weightOk(sl: Int64, sr: Int64) -> Bool =
      if lte(add(sl, sr), 1) then true
      else if gt(sl, mul(3, sr)) then false
      else if gt(sr, mul(3, sl)) then false
      else true

    operation both(l: SortedSet[T = Int64, O = Int64], r: SortedSet[T = Int64, O = Int64]) -> Bool =
      if balanced(l) then balanced(r) else false

    -- `{{from, …, to}}` inserted in ascending order into `s`.
    operation fill(s: SortedSet[T = Int64, O = Int64], from: Int64, to: Int64)
        -> SortedSet[T = Int64, O = Int64] =
      if gt(from, to) then s else fill(SortedSet.insert(s, from), add(from, 1), to)

    -- The same, descending.
    operation fillDown(s: SortedSet[T = Int64, O = Int64], from: Int64, to: Int64)
        -> SortedSet[T = Int64, O = Int64] =
      if gt(to, from) then s else fillDown(SortedSet.insert(s, from), add(from, -1), to)

    operation empty(n: Int64) -> SortedSet[T = Int64, O = Int64] =
      SortedSet.empty[T = Int64, O = Int64]()

    operation sum(l: List[T = Int64]) -> Int64 =
      match l
        case nil() -> 0
        case cons(h, t) -> add(h, sum(t))

    operation firstInt(l: List[T = Int64]) -> Int64 =
      match l
        case nil() -> -1
        case cons(h, _) -> h

    operation firstStr(l: List[T = String]) -> String =
      match l
        case nil() -> "<empty>"
        case cons(h, _) -> h

    -- The property `toList` promises and the weight checker cannot see: ASCENDING under
    -- `O`. A `link` / `below` / `above` bug that misplaces an interior element leaves the
    -- weights and the element count intact, so nothing else here would catch it.
    operation ascending(l: List[T = Int64]) -> Bool =
      match l
        case nil() -> true
        case cons(h, t) ->
          match t
            case nil() -> true
            case cons(h2, _) -> if gt(h, h2) then false else ascending(t)
  end

  -- An element type whose equality is NOT its structure: `word` compares by LENGTH, so
  -- `word("ab")` and `word("cd")` are two terms and one value. It is what makes
  -- `sameElements`' `PartialEq.eq` call observable — a structural comparison answers
  -- differently — and `WeakOrd` over the same key keeps it a lawful set element.
  sort Word
    import anthill.prelude.String.{{length}}
    entity word(s: String)
    provides PartialEq[T = Word]
    provides Eq[T = Word]
    operation eq(a: Word, b: Word) -> Bool = PartialEq.eq(len(a), len(b))
    operation len(w: Word) -> Int64 =
      match w
        case word(s) -> length(s)
  end

  -- The ordering is a WITNESS sort, not `Word` itself: a concrete provider's dispatch is
  -- directed by its values, so `[O = Word]` is refused at the construction site (§4.4).
  sort WordLen
    import anthill.prelude.Additive.{{sub}}
    -- `WeakOrd requires PartialOrd[T]`, and nothing else provides one for `Word`; its
    -- surface is derived from `compare` (WI-876), so the row is all this owes.
    provides PartialOrd[T = Word]
    provides WeakOrd[T = Word]
    operation compare(a: Word, b: Word) -> Int64 = sub(Word.len(a), Word.len(b))
  end
{body}
end
"#
    )
}

/// ONE interpreter per `#[test]`, not per entry: `interp_for` loads the whole stdlib, and
/// this file's fixtures build 100-element sets, so a fresh one per call paid that twice
/// over per assertion.
struct Driver {
    interp: anthill_core::eval::Interpreter,
    ns: String,
}

impl Driver {
    fn new(ns: &str, body: &str) -> Driver {
        let src = program(ns, body);
        Driver {
            interp: crate::common::interp_for(&src),
            ns: format!("{ns}.Driver"),
        }
    }

    fn call(&mut self, op: &str) -> Value {
        let entry = format!("{}.{op}", self.ns);
        self.interp
            .call(&entry, &[Value::Int(0)])
            .unwrap_or_else(|e| panic!("{entry} runs; got {e:?}"))
    }

    fn int(&mut self, op: &str) -> i64 {
        match self.call(op) {
            Value::Int(n) => n,
            other => panic!("{op}: expected an Int64; got {other:?}"),
        }
    }

    fn bool(&mut self, op: &str) -> bool {
        match self.call(op) {
            Value::Bool(b) => b,
            other => panic!("{op}: expected a Bool; got {other:?}"),
        }
    }

    fn str(&mut self, op: &str) -> String {
        match self.call(op) {
            Value::Str(s) => s,
            other => panic!("{op}: expected a String; got {other:?}"),
        }
    }
}

/// 1..100 inserted in ascending order — a list's worst case and an unbalanced tree's.
/// The set holds 100 elements, walks back in order (sum 5050, first 1), and every node
/// satisfies the weight invariant.
#[test]
fn ascending_inserts_stay_balanced() {
    let mut d = Driver::new(
        "wi456.tree.asc",
        "  sort Driver\n    \
         operation set(n: Int64) -> SortedSet[T = Int64, O = Int64] = Check.fill(Check.empty(0), 1, 100)\n    \
         operation size(n: Int64) -> Int64 = SortedSet.size(set(0))\n    \
         operation sum(n: Int64) -> Int64 = Check.sum(SortedSet.toList(set(0)))\n    \
         operation first(n: Int64) -> Int64 = Check.firstInt(SortedSet.toList(set(0)))\n    \
         operation ordered(n: Int64) -> Bool = Check.ascending(SortedSet.toList(set(0)))\n    \
         operation balanced(n: Int64) -> Bool = Check.balanced(set(0))\n    \
         operation downOrdered(n: Int64) -> Bool =\n      \
         Check.ascending(SortedSet.toList(Check.fillDown(Check.empty(0), 100, 1)))\n    \
         operation downBalanced(n: Int64) -> Bool = Check.balanced(Check.fillDown(Check.empty(0), 100, 1))\n  \
         end",
    );
    assert_eq!(d.int("size"), 100, "size of 1..100");
    assert_eq!(d.int("sum"), 5050, "in-order walk of 1..100");
    assert_eq!(d.int("first"), 1, "least element");
    assert!(d.bool("ordered"), "the ascending build does not read back in order");
    assert!(d.bool("balanced"), "ascending build is unbalanced");
    assert!(d.bool("downOrdered"), "the descending build does not read back in order");
    assert!(d.bool("downBalanced"), "descending build is unbalanced");
}

/// Re-inserting a present element returns the set unchanged, and under a COARSE
/// comparator the INCUMBENT of the class survives: `"zz"` then `"aa"` under `ByLength` is
/// the one-element set `{"zz"}`.
#[test]
fn insert_keeps_the_incumbent() {
    let mut d = Driver::new(
        "wi456.tree.inc",
        "  sort Driver\n    \
         operation dupSize(n: Int64) -> Int64 =\n      \
         SortedSet.size(SortedSet.insert(Check.fill(Check.empty(0), 1, 10), 5))\n    \
         operation classSize(n: Int64) -> Int64 =\n      \
         SortedSet.size(SortedSet.insert(SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\"), \"aa\"))\n    \
         operation survivor(n: Int64) -> String =\n      \
         Check.firstStr(SortedSet.toList(SortedSet.insert(SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\"), \"aa\")))\n  \
         end",
    );
    assert_eq!(d.int("dupSize"), 10, "re-insert of a member");
    assert_eq!(d.int("classSize"), 1, "one class under ByLength");
    assert_eq!(d.str("survivor"), "zz", "the incumbent survives");
}

/// `union` of the odd and the even numbers up to 100, overlapping on nothing, is 1..100 in
/// order and balanced; of two overlapping ranges it counts each element once. And it is
/// LEFT-BIASED under a coarse comparator: the left operand's `"zz"` survives against the
/// right's `"aa"`, and the other way round.
#[test]
fn union_is_ordered_balanced_and_left_biased() {
    let mut d = Driver::new(
        "wi456.tree.union",
        "  sort Driver\n    \
         operation odds(s: SortedSet[T = Int64, O = Int64], i: Int64) -> SortedSet[T = Int64, O = Int64] =\n      \
         if gt(i, 100) then s else odds(SortedSet.insert(s, i), add(i, 2))\n    \
         operation u(n: Int64) -> SortedSet[T = Int64, O = Int64] =\n      \
         SortedSet.union(odds(Check.empty(0), 1), odds(Check.empty(0), 2))\n    \
         operation ov(n: Int64) -> SortedSet[T = Int64, O = Int64] =\n      \
         SortedSet.union(Check.fill(Check.empty(0), 1, 60), Check.fill(Check.empty(0), 41, 100))\n    \
         operation size(n: Int64) -> Int64 = SortedSet.size(u(0))\n    \
         operation sum(n: Int64) -> Int64 = Check.sum(SortedSet.toList(u(0)))\n    \
         operation ordered(n: Int64) -> Bool = Check.ascending(SortedSet.toList(u(0)))\n    \
         operation balanced(n: Int64) -> Bool = Check.balanced(u(0))\n    \
         operation overlap(n: Int64) -> Int64 = SortedSet.size(ov(0))\n    \
         operation overlapOrdered(n: Int64) -> Bool = Check.ascending(SortedSet.toList(ov(0)))\n    \
         operation overlapBalanced(n: Int64) -> Bool = Check.balanced(ov(0))\n    \
         operation leftZz(n: Int64) -> String =\n      \
         Check.firstStr(SortedSet.toList(SortedSet.union(\n        \
         SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\"),\n        \
         SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"aa\"))))\n    \
         operation leftAa(n: Int64) -> String =\n      \
         Check.firstStr(SortedSet.toList(SortedSet.union(\n        \
         SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"aa\"),\n        \
         SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\"))))\n  \
         end",
    );
    assert_eq!(d.int("size"), 100, "odds ∪ evens");
    assert_eq!(d.int("sum"), 5050, "odds ∪ evens in order");
    assert!(d.bool("ordered"), "the union does not read back in order");
    assert!(d.bool("balanced"), "union is unbalanced");
    assert_eq!(d.int("overlap"), 100, "1..60 ∪ 41..100");
    assert!(d.bool("overlapOrdered"), "the overlapping union does not read back in order");
    assert!(d.bool("overlapBalanced"), "overlapping union is unbalanced");
    assert_eq!(d.str("leftZz"), "zz", "left bias");
    assert_eq!(d.str("leftAa"), "aa", "left bias, swapped");
}

/// The shape depends on insertion order, so equality cannot be structural: 1..20
/// ascending and descending are two TREES (`===` false) and one SET (`=` true). Two sets
/// of the SAME SIZE differing in one member are not `=` — the row that drives
/// `sameElements`' element comparison, which a length check alone never reaches. And the
/// comparison is the ELEMENT's own: `Word` compares by length, so `{word("ab")}` and
/// `{word("cd")}` are one set in two terms.
#[test]
fn equality_is_extensional_not_structural() {
    let mut d = Driver::new(
        "wi456.tree.eq",
        "  sort Driver\n    \
         import anthill.prelude.SortedSet.{empty, insert}\n    \
         operation up(n: Int64) -> SortedSet[T = Int64, O = Int64] = Check.fill(Check.empty(0), 1, 20)\n    \
         operation down(n: Int64) -> SortedSet[T = Int64, O = Int64] = Check.fillDown(Check.empty(0), 20, 1)\n    \
         operation sameSet(n: Int64) -> Bool = up(0) = down(0)\n    \
         operation sameShape(n: Int64) -> Bool = up(0) === down(0)\n    \
         operation fewer(n: Int64) -> Bool = up(0) = Check.fill(Check.empty(0), 1, 19)\n    \
         operation swapped(n: Int64) -> Bool =\n      \
         up(0) = SortedSet.insert(Check.fill(Check.empty(0), 1, 19), 21)\n    \
         operation wordSet(s: String) -> SortedSet[T = Word, O = WordLen] =\n      \
         SortedSet.insert(SortedSet.empty[T = Word, O = WordLen](), word(s: s))\n    \
         operation byElementEq(n: Int64) -> Bool = wordSet(\"ab\") = wordSet(\"cd\")\n    \
         operation byElementShape(n: Int64) -> Bool = wordSet(\"ab\") === wordSet(\"cd\")\n  \
         end",
    );
    assert!(d.bool("sameSet"), "equal sets must be `=`");
    assert!(
        !d.bool("sameShape"),
        "the two builds must be different trees, or the `=` row proves nothing about \
         extensional equality"
    );
    assert!(!d.bool("fewer"), "sets differing by one member must not be `=`");
    assert!(
        !d.bool("swapped"),
        "{{1..19, 21}} and {{1..20}} are the same SIZE and differ in one member: `=` must \
         compare the elements, not just the count"
    );
    assert!(
        d.bool("byElementEq"),
        "`=` must compare elements through the ELEMENT's `PartialEq` (`Word` compares by \
         length), not structurally"
    );
    assert!(
        !d.bool("byElementShape"),
        "the two word sets must be structurally different, or the row above proves nothing"
    );
}
