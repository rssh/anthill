//! WI-456 — `SortedSet` provides the generic collection surface (`Iterable` /
//! `FiniteCollection` / `PersistentCollection`), and a call through one of those specs
//! keeps the set's comparator.
//!
//! THE DEFECT THE PROVISIONS EXPOSED. `SortedSet requires O: WeakOrd[T]` is a NAMED slot,
//! so the ordering is part of the type, and a DIRECT call (`SortedSet.insert(s, x)`)
//! reads it back off `s` (WI-844's `selections_from_slot_bindings`). A call through the
//! SPEC (`PersistentCollection.insert(s, x)`) never reached that reader — the callee is
//! the spec's and names no slot — so the resolver chose `SortedSet`'s provision and then
//! SEARCHED the sub-goal `WeakOrd[String]` for its condition, tying among every provider
//! of it: *"ambiguous dispatch … 3 instances provide WeakOrd (ByLength, String,
//! Alphabetical) … The tie is in a SUB-GOAL"*. The carrier's type written out in full
//! did not help; the provision match had bound `O = ByLength` and nothing read it.
//!
//! THE FIX, IN TWO PLACES, because the ordering was lost on two routes:
//!
//!  * TYPER (`carried_slot`, `kb/typing.rs`): the chosen provider's named slots are read
//!    off the provision match. A witness becomes a slot pin for the sub-goal, beside the
//!    bracket pins WI-870 already threads; an unwritten slot gets WI-1094's direct-route
//!    reading (forwarded if the signature declares it, refused otherwise); a concrete
//!    provider whose head omits the slot is refused.
//!  * RUNTIME (`resolve_bridge_requirements`, `kb/typing.rs`): a spec's DEFAULT body
//!    calling a sibling spec op (`size`'s `collect(c)`, `isEmpty`'s `iterator(c)`)
//!    dispatches by VALUE, and the bridge rebuilt `SortedSet`'s dictionary from a
//!    `sorted_set(…)` entity that carries no `O` — a tie, raised as
//!    `AmbiguousRequirement` for a body (`toList(s)`) that never reads `O`. A tie at a
//!    NAMED sort slot is now the recorded absence `NamedSlotNotCarried`: nothing is
//!    built, and a body that does read the slot is refused naming why
//!    (`a_default_body_reading_the_slot_by_value_is_refused_naming_it`).
//!
//! BACKED-OUT CONTROLS, both measured:
//!  * typer fix out → `spec_insert_*`, `generic_consumer_*` and `finite_collection_*`
//!    FAIL (load error, the sub-goal tie quoted above);
//!  * runtime fix out → `finite_collection_*` FAILS (`AmbiguousRequirement` for
//!    `SortedSet.collect`) and so does the named-slot refusal test (the tie's wording);
//!    the other tests dispatch straight to `SortedSet`'s own ops;
//!  * `single_ordering_control_*` PASSES either way by design: with one `WeakOrd[Int64]`
//!    provider in scope the searched sub-goal has one answer.
//!  * the refusals (`an_erased_*`, `a_provision_head_*`) and the forward (`a_declared_*`)
//!    record their own controls at their sites.

use anthill_core::eval::Value;

const BY_LENGTH: &str = r#"
  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
"#;

const ALPHABETICAL: &str = r#"
  sort Alphabetical
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 =
      if lt(a, b) then -1 else if gt(a, b) then 1 else 0
  end
"#;

/// `ByLength` puts `"zz"` first and `Alphabetical` puts `"aaa"` first, so the first
/// element of `{"zz", "aaa"}` names the comparator that built the set.
fn program(ns: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool, SortedSet, \
         PersistentCollection, FiniteCollection, Iterable}}\n  \
         import anthill.prelude.PartialOrd.{{lt, gt}}\n\
         {BY_LENGTH}{ALPHABETICAL}\n  \
         sort Read\n    \
         import anthill.prelude.List.{{cons, nil}}\n    \
         operation first(l: List[T = String]) -> String =\n      \
         match l\n        \
         case nil() -> \"<empty>\"\n        \
         case cons(h, t) -> h\n  \
         end\n{body}\nend\n"
    )
}

fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

fn eval_str(src: &str, entry: &str, why: &str) -> String {
    match eval_fresh(src, entry) {
        Ok(Value::Str(s)) => s,
        other => panic!("{why}; got {other:?}"),
    }
}

fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    match eval_fresh(src, entry) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

/// THE ACCEPTANCE: `PersistentCollection.insert` on a set of each ordering, both
/// orderings in scope, answers by the ordering each set's TYPE names.
#[test]
fn spec_insert_keeps_the_carriers_ordering() {
    let src = program(
        "wi456.insert",
        "  sort Driver\n    \
         operation byLength(n: Int64) -> String =\n      \
         let s = SortedSet.empty[T = String, O = ByLength]()\n      \
         Read.first(SortedSet.toList(\n        \
         PersistentCollection.insert(PersistentCollection.insert(s, \"zz\"), \"aaa\")))\n    \
         operation alphabetical(n: Int64) -> String =\n      \
         let s = SortedSet.empty[T = String, O = Alphabetical]()\n      \
         Read.first(SortedSet.toList(\n        \
         PersistentCollection.insert(PersistentCollection.insert(s, \"zz\"), \"aaa\")))\n  \
         end",
    );
    assert_eq!(
        eval_str(&src, "wi456.insert.Driver.byLength", "ByLength set through the spec"),
        "zz"
    );
    assert_eq!(
        eval_str(&src, "wi456.insert.Driver.alphabetical", "Alphabetical set through the spec"),
        "aaa"
    );
}

/// A GENERIC consumer — written against `PersistentCollection` only, knowing nothing of
/// `SortedSet` — keeps the ordering of the set it is handed. The dictionary for `Grow`'s
/// `requires` is built at the call from the argument's type, one level further from any
/// slot the call could name.
#[test]
fn generic_consumer_keeps_the_carriers_ordering() {
    let src = program(
        "wi456.generic",
        "  sort Grow\n    \
         sort C = ?\n    \
         requires PersistentCollection[C = C, Element = String, Effect = {}]\n    \
         operation addBoth(c: C) -> C =\n      \
         PersistentCollection.insert(PersistentCollection.insert(c, \"zz\"), \"aaa\")\n  \
         end\n  \
         sort Driver\n    \
         operation byLength(n: Int64) -> String =\n      \
         Read.first(SortedSet.toList(Grow.addBoth(SortedSet.empty[T = String, O = ByLength]())))\n    \
         operation alphabetical(n: Int64) -> String =\n      \
         Read.first(SortedSet.toList(Grow.addBoth(SortedSet.empty[T = String, O = Alphabetical]())))\n  \
         end",
    );
    assert_eq!(
        eval_str(&src, "wi456.generic.Driver.byLength", "generic consumer, ByLength set"),
        "zz"
    );
    assert_eq!(
        eval_str(&src, "wi456.generic.Driver.alphabetical", "generic consumer, Alphabetical set"),
        "aaa"
    );
}

/// The READ side: `FiniteCollection.collect` walks in the set's order and
/// `FiniteCollection.size` counts classes under it — `"zz"` and `"aa"` are one class
/// under `ByLength` and two under `Alphabetical`, so the size names the comparator too.
#[test]
fn finite_collection_reads_in_the_carriers_ordering() {
    let src = program(
        "wi456.read",
        "  sort Driver\n    \
         operation firstByLength(n: Int64) -> String =\n      \
         let s = SortedSet.insert(SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\"), \"aaa\")\n      \
         Read.first(FiniteCollection.collect(s))\n    \
         operation sizeByLength(n: Int64) -> Int64 =\n      \
         FiniteCollection.size(SortedSet.insert(SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\"), \"aa\"))\n    \
         operation sizeAlphabetical(n: Int64) -> Int64 =\n      \
         FiniteCollection.size(SortedSet.insert(SortedSet.insert(SortedSet.empty[T = String, O = Alphabetical](), \"zz\"), \"aa\"))\n    \
         operation emptyByLength(n: Int64) -> Bool =\n      \
         Iterable.isEmpty(SortedSet.empty[T = String, O = ByLength]())\n  \
         end",
    );
    // `Iterable.isEmpty`'s default is `Stream.isEmpty(iterator(c))` — the same bare
    // sibling call as `size`'s `collect(c)`, through the other spec.
    assert!(
        matches!(
            eval_fresh(&src, "wi456.read.Driver.emptyByLength"),
            Ok(Value::Bool(true))
        ),
        "Iterable.isEmpty of an empty ByLength set; got {:?}",
        eval_fresh(&src, "wi456.read.Driver.emptyByLength")
    );
    assert_eq!(
        eval_str(&src, "wi456.read.Driver.firstByLength", "collect of a ByLength set"),
        "zz"
    );
    assert_eq!(
        eval_int(&src, "wi456.read.Driver.sizeByLength", "size under ByLength"),
        1
    );
    assert_eq!(
        eval_int(&src, "wi456.read.Driver.sizeAlphabetical", "size under Alphabetical"),
        2
    );
}

/// A set whose type LEAVES `O` UNWRITTEN is refused through the spec exactly as WI-1094
/// refuses it on the direct route: the value chose an ordering the type does not record,
/// so any provider supplied here answers for the signature and not for the value. The
/// refusal must not depend on how many providers are in scope — the `Int64` half has ONE
/// (its own), which is the case a search would silently answer: extending a `Descending`
/// set with the ascending comparator.
///
/// CONTROL, measured: with `carried_slot`'s `Erased` arm backed out (treated as
/// `Forwarded`), the `Int64` half LOADS — the silent wrong order — and the `String` half
/// ties instead, advising the bracket value `f[Spec = W[Slot = Chosen]]` that the next
/// check refuses for a concrete provider.
#[test]
fn an_erased_ordering_through_the_spec_is_refused_whatever_the_provider_count() {
    for (ns, elem, x) in [("wi456.erased.two", "String", "\"zz\""), ("wi456.erased.one", "Int64", "3")] {
        let src = program(
            ns,
            &format!(
                "  sort Use\n    \
                 operation add(s: SortedSet[T = {elem}], x: {elem}) -> SortedSet[T = {elem}] =\n      \
                 PersistentCollection.insert(s, {x})\n  \
                 end"
            ),
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| panic!("an erased ordering must not load:\n{src}"));
        assert!(
            errs.iter().any(|e| e.contains(
                "the carrier's type leaves named slot `O` of `anthill.prelude.SortedSet` \
                 universally quantified"
            )),
            "{elem}: the refusal must name the erased slot; got {errs:?}"
        );
    }
}

/// The ONE shape a quantified slot may take (058 §7.1, WI-1094): the signature DECLARES
/// it — `R requires OE: WeakOrd[E]` and `s: SortedSet[T = E, O = OE]` — so the caller's
/// slot supplies the value's own dictionary and the call through the spec runs on it.
/// Driven at both orderings, which disagree about the first element.
#[test]
fn a_declared_ordering_through_the_spec_is_forwarded_from_the_caller() {
    let src = program(
        "wi456.forwarded",
        "  sort R\n    \
         sort E = ?\n    \
         requires OE: WeakOrd[E]\n    \
         operation grow(s: SortedSet[T = E, O = OE], x: E) -> SortedSet[T = E, O = OE] =\n      \
         PersistentCollection.insert(s, x)\n  \
         end\n  \
         sort Driver\n    \
         operation byLength(n: Int64) -> String =\n      \
         let s = SortedSet.insert(SortedSet.empty[T = String, O = ByLength](), \"zz\")\n      \
         Read.first(SortedSet.toList(R.grow(s, \"aaa\")))\n    \
         operation alphabetical(n: Int64) -> String =\n      \
         let s = SortedSet.insert(SortedSet.empty[T = String, O = Alphabetical](), \"zz\")\n      \
         Read.first(SortedSet.toList(R.grow(s, \"aaa\")))\n  \
         end",
    );
    assert_eq!(
        eval_str(&src, "wi456.forwarded.Driver.byLength", "forwarded ByLength ordering"),
        "zz"
    );
    assert_eq!(
        eval_str(&src, "wi456.forwarded.Driver.alphabetical", "forwarded Alphabetical ordering"),
        "aaa"
    );
}

/// A CONCRETE provider whose provision head does not write its named slot (`provides
/// Pick[C = Tagged[T = T], …]`, no `O = O`) cannot carry the value's ordering to the slot,
/// and is refused naming the missing binding — rather than falling back to the search
/// this ticket replaced, which ties here or silently picks by specificity.
#[test]
fn a_provision_head_that_omits_the_slot_is_refused() {
    let src = program(
        "wi456.nohead",
        "  sort Pick\n    \
         sort C = ?\n    \
         sort Element = ?\n    \
         operation keepLeast(c: C, x: Element) -> C\n  \
         end\n  \
         enum Tagged\n    \
         sort T = ?\n    \
         requires O: WeakOrd[T]\n    \
         entity tagged(v: T)\n    \
         provides Pick[C = Tagged[T = T], Element = T]\n    \
         operation single(x: T) -> Tagged[T = T, O = O] = tagged(v: x)\n    \
         operation keepLeast(c: Tagged[T = T, O = O], x: T) -> Tagged[T = T, O = O] =\n      \
         match c\n        \
         case tagged(v) -> if lt(WeakOrd.compare(x, v), 0) then tagged(v: x) else tagged(v: v)\n  \
         end\n  \
         sort Driver\n    \
         operation go(n: Int64) -> Tagged[T = String, O = ByLength] =\n      \
         Pick.keepLeast(Tagged.single[T = String, O = ByLength](\"zz\"), \"a\")\n  \
         end",
    );
    let errs = crate::common::try_load_kb_with(&src)
        .err()
        .unwrap_or_else(|| panic!("a head omitting the slot must not load:\n{src}"));
    assert!(
        errs.iter().any(|e| e.contains("does not bind its named slot `O` in its head")
            && e.contains("write `O = O`")),
        "the refusal must name the missing head binding; got {errs:?}"
    );
}

/// THE LIMIT OF THE RUNTIME FIX, pinned so it stays loud. A spec default body reaches
/// its carrier's operations by VALUE, and a value carries no `O`; `SortedSet`'s
/// `collect` / `iterator` never read it, which is why the provided surface runs. An
/// operation that DOES compare, reached the same way, has no ordering to use — and must
/// be refused naming that, not run under a guessed one. `Tagged` is the smallest such
/// carrier: `keepLeast` compares through `O`, and `Pick.twice`'s default body calls it
/// by value.
#[test]
fn a_default_body_reading_the_slot_by_value_is_refused_naming_it() {
    let src = program(
        "wi456.byvalue",
        "  sort Pick\n    \
         sort C = ?\n    \
         sort Element = ?\n    \
         operation keepLeast(c: C, x: Element) -> C\n    \
         operation twice(c: C, x: Element) -> C = keepLeast(keepLeast(c, x), x)\n  \
         end\n  \
         enum Tagged\n    \
         sort T = ?\n    \
         requires O: WeakOrd[T]\n    \
         entity tagged(v: T)\n    \
         provides Pick[C = Tagged[T = T, O = O], Element = T]\n    \
         operation single(x: T) -> Tagged[T = T, O = O] = tagged(v: x)\n    \
         operation keepLeast(c: Tagged[T = T, O = O], x: T) -> Tagged[T = T, O = O] =\n      \
         match c\n        \
         case tagged(v) -> if lt(WeakOrd.compare(x, v), 0) then tagged(v: x) else tagged(v: v)\n  \
         end\n  \
         sort Driver\n    \
         operation direct(n: Int64) -> Int64 =\n      \
         match Pick.keepLeast(Tagged.single[T = String, O = ByLength](\"zz\"), \"a\")\n        \
         case tagged(v) -> String.length(v)\n    \
         operation byValue(n: Int64) -> Int64 =\n      \
         match Pick.twice(Tagged.single[T = String, O = ByLength](\"zz\"), \"a\")\n        \
         case tagged(v) -> String.length(v)\n  \
         end",
    );
    // The typer-dispatched call reads `O = ByLength` off the type and runs: "a" is
    // shorter than "zz".
    assert_eq!(
        eval_int(&src, "wi456.byvalue.Driver.direct", "the typer-dispatched compare"),
        1
    );
    let err = format!("{:?}", eval_fresh(&src, "wi456.byvalue.Driver.byValue"));
    assert!(
        err.contains("NAMED requirement slot") && err.contains("cannot be recovered"),
        "a by-value dispatch into an operation that reads the named slot must be refused \
         naming the slot's cause; got {err}"
    );
}

/// CONTROL — passes with the fix backed out, by design: `Int64` has ONE `WeakOrd`
/// provider here, so the searched sub-goal cannot tie. It pins that the provisions
/// themselves are sound independently of the resolver change.
#[test]
fn single_ordering_control_spec_insert_runs() {
    let src = "\nnamespace wi456.single\n  \
               import anthill.prelude.{Int64, List, SortedSet, PersistentCollection}\n  \
               sort Driver\n    \
               import anthill.prelude.List.{cons, nil}\n    \
               operation go(n: Int64) -> Int64 =\n      \
               let s = SortedSet.empty[T = Int64, O = Int64]()\n      \
               match SortedSet.toList(PersistentCollection.insert(PersistentCollection.insert(s, 7), 3))\n        \
               case nil() -> -1\n        \
               case cons(h, t) -> h\n  \
               end\nend\n";
    assert_eq!(eval_int(src, "wi456.single.Driver.go", "single-ordering control"), 3);
}
