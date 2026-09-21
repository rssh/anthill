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
//!    WI-20260921-R10KC INVERTED THAT ROW and renamed it
//!    `a_default_body_reads_the_named_slot_through_its_provisions_dictionary`: a spec
//!    default body is no longer ON the value route. It receives its provision's
//!    dictionary and resolves the body-less sibling BY PROJECTION out of it, so the
//!    slot is read rather than reconstructed. The runtime absence above survives for
//!    the routes with no static type to build a dictionary from — see that variant's
//!    doc at `UnavailableWhy::NamedSlotNotCarried`.
//!
//! BACKED-OUT CONTROLS, both measured:
//!  * typer fix out → `spec_insert_*`, `generic_consumer_*` and `finite_collection_*`
//!    FAIL (load error, the sub-goal tie quoted above);
//!  * runtime fix out → `finite_collection_*` FAILS (`AmbiguousRequirement` for
//!    `SortedSet.collect`). It used to also name the named-slot REFUSAL test here;
//!    WI-20260921-R10KC inverted that row and it is now
//!    `a_default_body_reads_the_named_slot_through_its_provisions_dictionary`, whose own
//!    back-out controls are R10KC's two edits and are recorded at its site;
//!    the other tests dispatch straight to `SortedSet`'s own ops. WHICH ROWS drive that
//!    bridge narrowed when `SortedSet` gained O(1) `size` and `isEmpty` members: those
//!    override the spec defaults (WI-444), so `sizeByLength` / `sizeAlphabetical` /
//!    `emptyByLength` now call them directly and `firstByLength`'s
//!    `FiniteCollection.collect` is the row left on the default-body route;
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
    program_with_rivals(ns, &format!("{BY_LENGTH}{ALPHABETICAL}"), body)
}

/// WI-456 — [`program`] with the rival orderings as a PARAMETER, so
/// `single_witness_provider_control_a_bare_witness_loads` can be the same program with
/// the rivals removed and nothing else. Hand-copying the preamble instead let the
/// control differ in imports too, and a control that differs in two things is evidence
/// for neither.
fn program_with_rivals(ns: &str, rivals: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool, SortedSet, \
         PersistentCollection, FiniteCollection, Iterable}}\n  \
         import anthill.prelude.PartialOrd.{{lt, gt}}\n\
         {rivals}\n  \
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

/// WI-20260921-R10KC — A SPEC DEFAULT BODY READS THE NAMED SLOT, AND THE SLOT DECIDES.
///
/// THIS TEST INVERTED. It was `a_default_body_reading_the_slot_by_value_is_refused_naming_it`
/// and it PINNED the refusal: a spec default body reached its carrier's operations by
/// VALUE, a value carries its sort and none of its type arguments, and the named slot
/// `O` — a SELECTION the construction site made, with no footprint in the data — could
/// not be recovered. `SortedSet`'s `collect` / `iterator` never read it, which is why the
/// provided surface ran; `Tagged.keepLeast` does, and it was refused.
///
/// It is no longer reached by value. `Pick.twice`'s frame now carries the `Pick[Tagged]`
/// INSTANCE (`Dictionary(<the WeakOrd slot>, impl: Tagged)`), and the sibling
/// `keepLeast` resolves BY PROJECTION out of it — `Dictionary.resolveOp`, spelled in eval
/// as `dispatch_via_sort_ops_table` + `expand_dispatching_dict`. Both routes find
/// `Tagged.keepLeast`; only this one brings the evidence it reads.
///
/// **BOTH ROWS SPLIT BY ORDERING, and the `direct` row FIRST.** It used to compare `"zz"`
/// against `"a"`, where `ByLength` and `Alphabetical` agree that `"a"` is least — so its
/// `1` proved the typed call RAN and not that the comparator DECIDED. `"aaa"` against
/// `"zz"` splits them: `ByLength` keeps `"zz"` (2 < 3) and `Alphabetical` keeps `"aaa"`
/// (a < z), so `String.length` reads back 2 or 3 and one answer twice fails the test.
/// That is what makes the `defaultByLength` / `defaultAlphabetical` rows evidence about WHICH dictionary
/// travelled rather than that some route answered.
///
/// BACKED OUT, MEASURED — the two edits are independent and each is necessary:
///  * `classify_pin_or_apply_within`'s `threads_instance` out → both default-body rows
///    fail with the `NAMED requirement slot … cannot be recovered` refusal this test
///    used to assert. The typer resolves the `Pick[Tagged]` instance either way; without
///    that clause it is dropped on the `PinNow` branch and the frame is empty.
///  * `Interpreter::spec_instance_for_sibling_call` out → the same two rows fail the same
///    way: the dictionary reaches `twice`'s frame and the sibling call's own channel is
///    still empty, so the dispatch falls to value-direction regardless.
/// The two `direct` rows pass either way BY DESIGN — a typed call at a written carrier
/// type was never on this route — which is what makes them the control for the split
/// itself: they prove `ByLength` and `Alphabetical` really do disagree here.
#[test]
fn a_default_body_reads_the_named_slot_through_its_provisions_dictionary() {
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
         operation directByLength(n: Int64) -> Int64 =\n      \
         match Pick.keepLeast(Tagged.single[T = String, O = ByLength](\"aaa\"), \"zz\")\n        \
         case tagged(v) -> String.length(v)\n    \
         operation directAlphabetical(n: Int64) -> Int64 =\n      \
         match Pick.keepLeast(Tagged.single[T = String, O = Alphabetical](\"aaa\"), \"zz\")\n        \
         case tagged(v) -> String.length(v)\n    \
         operation defaultByLength(n: Int64) -> Int64 =\n      \
         match Pick.twice(Tagged.single[T = String, O = ByLength](\"aaa\"), \"zz\")\n        \
         case tagged(v) -> String.length(v)\n    \
         operation defaultAlphabetical(n: Int64) -> Int64 =\n      \
         match Pick.twice(Tagged.single[T = String, O = Alphabetical](\"aaa\"), \"zz\")\n        \
         case tagged(v) -> String.length(v)\n  \
         end",
    );
    // THE CONTROL FOR THE SPLIT: a typed call at a written carrier type, which was never
    // on the value route. If these two ever agreed, the rows below would prove nothing.
    assert_eq!(
        eval_int(
            &src,
            "wi456.byvalue.Driver.directByLength",
            "the typer-dispatched compare under ByLength keeps \"zz\" (2 < 3)"
        ),
        2
    );
    assert_eq!(
        eval_int(
            &src,
            "wi456.byvalue.Driver.directAlphabetical",
            "the typer-dispatched compare under Alphabetical keeps \"aaa\" (a < z)"
        ),
        3
    );
    // THE ACCEPTANCE: ONE default body, two orderings, two answers.
    assert_eq!(
        eval_int(
            &src,
            "wi456.byvalue.Driver.defaultByLength",
            "`Pick.twice`'s default body must reach `Tagged.keepLeast` through the \
             `Pick[Tagged]` instance, whose slot is ByLength"
        ),
        2
    );
    assert_eq!(
        eval_int(
            &src,
            "wi456.byvalue.Driver.defaultAlphabetical",
            "…and the SAME body under Alphabetical must answer differently — one answer \
             twice would mean the comparator did not decide"
        ),
        3
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

// ─────────────────────────────────────────────────────────────────────────────
// (b) — THE SUB-GOAL TIE AT A **WITNESS SORT**'s OWN NAMED SLOT
//
// The 2026-08-15 note's (b), narrowed by the tree commit to "the provider is a WITNESS
// sort rather than a carrier". MEASURED for this ticket, and the finding is that the
// CHANNEL was never missing — `O = ByInner[OI = ByLength]` in the carrier's TYPE steers
// the witness's own slot and loads (`the_advised_repair_*` below drive it). What was
// missing is that neither diagnostic NAMED it, and the two disagreed:
//
//   * route 1, the call bracket (`WeakOrd.compare[WeakOrd = ByInner](…)`), printed
//     `TieRepair::SubGoal`'s SCHEMA — *"give the conditional provider a NAMED
//     requirement slot and bind it in the value position (`f[Spec = W[Slot = Chosen]]`)"*
//     — in front of a provider that already declares one, leaving the name to guess;
//   * route 2, the carrier's type (`SortedSet[T = Boxed[E = String], O = ByInner]`),
//     dropped `TieRepair` on the floor in `describe_resolution_failure` and fell through
//     to the generic tail *"select a witness that provides this requirement at these
//     bindings, or drop the selection and let it resolve"* — FALSE on both halves:
//     `ByInner` does provide at those bindings, and dropping the selection loses the
//     ordering the program is about.
//
// That is exactly the shape the same note caught at (4) — two checks disagreeing about
// what the author should do — one level down, and it is what (c) closed for the level
// above. `tie_repair_advice` is now the one owner of the sentence and both routes read
// it.
//
// THE FIXTURE is the file's own (`ByLength` / `String` / `Alphabetical`, the trio the
// header quotes) plus a WITNESS over a one-field wrapper: `ByInner` cannot be a witness
// for `String` directly, because a provider whose own sub-goal is the spec it provides
// resolves witness-locally (058 §3.8) and would not terminate.
//
// BACKED-OUT CONTROLS, one edit at a time:
//   * `InstanceTie::slot` + its stamp in `resolve_inner`'s `err` arm → the two
//     `names_the_slot` arms FAIL (the message reverts to the schema) and so does
//     wi870's sharpened control;
//   * `!err.is_forwarded()` (the stamp's OWNERSHIP test, `owns_the_tie = true`) →
//     `a_tie_below_a_named_slot_is_not_attributed_to_that_slot` ALONE;
//   * the `PinnedWitness::TiedInside` suppression → `route_2_does_not_also_advise_the_
//     opposite` ALONE;
//   * `describe_resolution_failure`'s repair append → `route_2_a_tie_under_a_carrier_
//     named_witness_names_the_slot` AND `a_tie_below_a_named_slot_is_not_attributed_to_
//     that_slot` fail: both read their verdict off route 2's message;
//   * `single_witness_provider_control_*` PASSES either way BY DESIGN — one provider,
//     no tie — which is what pins the refusal to the TIE and not to the shape.

/// `ByInner`, a witness whose element ordering is a NAMED slot, over a wrapper sort so
/// the witness never provides the spec its own sub-goal asks for.
const BY_INNER: &str = r#"
  enum Boxed
    import anthill.prelude.{PartialEq, Eq}
    sort E = ?
    requires Eq[T = E]
    entity boxed(v: E)
    provides PartialEq[T = Boxed]
    provides Eq[T = Boxed]
    operation eq(a: Boxed, b: Boxed) -> Bool =
      match a
        case boxed(av) ->
          match b
            case boxed(bv) -> PartialEq.eq(av, bv)
  end

  sort ByInner
    import anthill.prelude.{WeakOrd, PartialOrd}
    sort E = ?
    requires OI: WeakOrd[T = E]
    provides PartialOrd[T = Boxed[E = E]]
    provides WeakOrd[T = Boxed[E = E]]
    operation compare(a: Boxed[E = E], b: Boxed[E = E]) -> Int64 =
      match a
        case boxed(av) ->
          match b
            case boxed(bv) -> WeakOrd.compare(av, bv)
  end
"#;

/// A `SortedSet` of wrapped strings whose comparator is `ByInner` with `slot` written —
/// `""` for the bare witness that ties. Reads back the FIRST element, which names the
/// element ordering the witness's slot resolved to.
fn boxed_set(ns: &str, slot: &str) -> String {
    program(
        ns,
        &format!(
            "{BY_INNER}  sort Driver\n    \
             import anthill.prelude.List.{{cons, nil}}\n    \
             operation go(n: Int64) -> String =\n      \
             let s = SortedSet.empty[T = Boxed[E = String], O = ByInner{slot}]()\n      \
             firstInner(SortedSet.toList(\n        \
             PersistentCollection.insert(PersistentCollection.insert(s, boxed(v: \"zz\")), \
             boxed(v: \"aaa\"))))\n    \
             operation firstInner(l: List[T = Boxed[E = String]]) -> String =\n      \
             match l\n        \
             case nil() -> \"<empty>\"\n        \
             case cons(h, t) ->\n          \
             match h\n            \
             case boxed(v) -> v\n  \
             end",
        ),
    )
}

fn tie_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected the sub-goal tie, but this loaded clean:\n{src}"))
}

/// ROUTE 2 — the witness reached through the CARRIER'S TYPE. The message must name the
/// slot that ties, and the spelling that repairs it *in a type*, because that is the
/// only place this call could write it: there is no bracket on a `SortedSet.empty[…]`
/// that reaches `ByInner`'s own sub-goal (058 §3.3 — a key reaches one level).
#[test]
fn route_2_a_tie_under_a_carrier_named_witness_names_the_slot() {
    let errs = tie_errs(&boxed_set("wi456.route2", ""));
    let joined = errs.join("\n");
    assert!(
        joined.contains("named slot `OI` of") && joined.contains("wi456.route2.ByInner"),
        "the tie fills `ByInner`'s own `OI`, and the message has to say so — naming the \
         tied SPEC alone is what sent the author to the wrong repair: {errs:?}"
    );
    assert!(
        joined.contains("ByInner[OI = …]"),
        "…in the spelling that repairs it, which `the_advised_repair_*` then writes \
         verbatim: {errs:?}"
    );
    // (No "and not `SortedSet`'s own `O`" assertion here: for THIS fixture no arm can
    // emit that clause, so it would be a guard that cannot fire. The wrong attribution
    // is driven where it can actually happen —
    // `a_tie_below_a_named_slot_is_not_attributed_to_that_slot`.)
}

/// AND NOT THE OPPOSITE ADVICE IN THE SAME BREATH. This is the (4)-shaped half: the
/// generic tail told the author to select a different witness or drop the selection,
/// directly after the clause naming the slot they actually have to bind.
#[test]
fn route_2_does_not_also_advise_the_opposite() {
    let joined = tie_errs(&boxed_set("wi456.route2b", "")).join("\n");
    assert!(
        !joined.contains("drop the selection"),
        "`ByInner` DOES provide at these bindings and dropping it loses the ordering — \
         the two sentences cannot both be printed: {joined}"
    );
}

/// ROUTE 1 — the same tie reached through a CALL BRACKET, which used to print a schema
/// (`f[Spec = W[Slot = Chosen]]`) rather than the slot. One `tie_repair_advice` owns the
/// sentence, so the two routes agree by construction; this arm is what says so from the
/// outside.
#[test]
fn route_1_a_tie_under_a_bracket_named_witness_names_the_same_slot() {
    let src = program(
        "wi456.route1",
        &format!(
            "{BY_INNER}  sort Driver\n    \
             operation go(n: Int64) -> Int64 =\n      \
             WeakOrd.compare[WeakOrd = ByInner](boxed(v: \"zz\"), boxed(v: \"aaa\"))\n  \
             end",
        ),
    );
    let joined = tie_errs(&src).join("\n");
    assert!(
        joined.contains("named slot `OI` of") && joined.contains("wi456.route1.ByInner"),
        "route 1 names the slot too: {joined}"
    );
}

/// THE ADVICE, WRITTEN OUT, RUNS — and the slot DECIDES. The two arms differ in one
/// token, the binding the diagnostic told the author to write, and they disagree about
/// which element comes first: `ByLength` puts `"zz"` before `"aaa"` (2 < 3) and
/// `Alphabetical` the reverse. So this asserts more than "the repair compiles" — it
/// asserts the witness's named slot, read out of the CARRIER'S TYPE two levels from any
/// call that could name it, is what orders the set.
#[test]
fn the_advised_repair_loads_and_its_slot_decides_the_order() {
    assert_eq!(
        eval_str(
            &boxed_set("wi456.repairA", "[OI = ByLength]"),
            "wi456.repairA.Driver.go",
            "`ByInner[OI = ByLength]` written in the carrier's type",
        ),
        "zz",
        "by inner LENGTH, so the 2-character string sorts first",
    );
    assert_eq!(
        eval_str(
            &boxed_set("wi456.repairB", "[OI = Alphabetical]"),
            "wi456.repairB.Driver.go",
            "`ByInner[OI = Alphabetical]` written in the carrier's type",
        ),
        "aaa",
        "…and the other binding flips it. Same witness, same call, two orders decided \
         by the nested slot binding — which is the channel (b) asked whether existed.",
    );
    // AND IN THE SPELLING THE MESSAGE PRINTS, which is the QUALIFIED one (a short name
    // need not resolve where the author is editing). The arms above write `ByInner[…]`
    // because the fixture imports it; nothing pinned that a DOTTED witness name carrying
    // a slot bracket loads at all, so the claim "writes what the diagnostic told the
    // author to write" rested on a form no test had ever loaded.
    assert_eq!(
        eval_str(
            &boxed_set("wi456.repairQ", "[OI = ByLength]").replace(
                "O = ByInner[OI = ByLength]",
                "O = wi456.repairQ.ByInner[OI = wi456.repairQ.ByLength]",
            ),
            "wi456.repairQ.Driver.go",
            "the qualified spelling the diagnostic prints",
        ),
        "zz",
    );
}

/// THE OTHER `PinnedWitness` ARM, positively. `route_2_does_not_also_advise_the_opposite`
/// only asserts that `TiedInside` DROPS the generic tail; without this arm a change that
/// returned `""` for both — or classified every pinned refusal as `TiedInside`, which is
/// exactly the gap /code-review found between the two gates — would delete the advice for
/// a genuinely unusable witness and the suite would stay green.
///
/// `Blank` has no ordering at all, so `ByInner`'s `OI` has NO provider: the projection
/// fails by `NoMatch`, not by a tie, and naming a different witness IS the repair.
#[test]
fn an_unusable_pinned_witness_still_gets_the_generic_advice() {
    let src = program(
        "wi456.unusable",
        &format!(
            "{BY_INNER}  enum Blank\n    \
             import anthill.prelude.{{PartialEq, Eq}}\n    \
             entity blank(n: Int64)\n    \
             provides PartialEq[T = Blank]\n    \
             provides Eq[T = Blank]\n    \
             operation eq(a: Blank, b: Blank) -> Bool =\n      \
             match a\n        \
             case blank(x) ->\n          \
             match b\n            \
             case blank(y) -> PartialEq.eq(x, y)\n  \
             end\n  \
             sort Driver\n    \
             operation go(n: Int64) -> Int64 =\n      \
             let s = SortedSet.empty[T = Boxed[E = Blank], O = ByInner]()\n      \
             FiniteCollection.size(PersistentCollection.insert(s, boxed(v: blank(n: 1))))\n  \
             end",
        ),
    );
    let errs = tie_errs(&src);
    assert!(
        errs.iter()
            .any(|e| e.contains("select a witness that provides this requirement")),
        "a pinned witness that cannot be used at all keeps `PinnedWitness::Unusable`'s \
         advice — only a tie INSIDE it suppresses that sentence: {errs:?}"
    );
}

/// CONTROL — passes with every edit of this section backed out, BY DESIGN: with the two
/// rival orderings gone, `WeakOrd[T = String]` has one provider and `ByInner`'s
/// sub-goal cannot tie, so the bare witness loads. It pins the refusal above to the TIE
/// rather than to the bare-witness shape.
#[test]
fn single_witness_provider_control_a_bare_witness_loads() {
    // The SAME program `boxed_set` builds, with the rival orderings — and only those —
    // removed: `String`'s own provision is then the sole `WeakOrd[String]`.
    let src = program_with_rivals(
        "wi456.solo",
        "",
        &format!(
            "{BY_INNER}  sort Driver\n    \
             operation go(n: Int64) -> Int64 =\n      \
             let s = SortedSet.empty[T = Boxed[E = String], O = ByInner]()\n      \
             FiniteCollection.size(PersistentCollection.insert(s, boxed(v: \"zz\")))\n  \
             end",
        ),
    );
    assert_eq!(
        eval_int(&src, "wi456.solo.Driver.go", "sole `WeakOrd[String]` provider"),
        1,
        "one provider, no tie: the bare witness is not refused for being bare",
    );
}

/// THE DEEPEST ROUTE, and the one the ticket was about: a GENERIC consumer — written
/// against `PersistentCollection` alone, knowing neither `SortedSet` nor `ByInner` —
/// handed a set whose comparator is a WITNESS carrying its own slot binding. Three
/// levels separate the binding from the dispatch that reads it (`Grow`'s `requires`
/// built at the argument's type → `SortedSet`'s provision match → `ByInner`'s `OI`),
/// and no call on the way can name any of them.
///
/// `generic_consumer_keeps_the_carriers_ordering` above is this test's control: it is
/// the same consumer over a DIRECT comparator (`O = ByLength`), so it passes with
/// everything here backed out and pins the consumer plumbing independently of the
/// nesting.
#[test]
fn a_generic_consumer_keeps_a_nested_slot_binding() {
    let grow = "  sort Grow\n    \
                sort C = ?\n    \
                requires PersistentCollection[C = C, Element = Boxed[E = String], Effect = {}]\n    \
                operation addBoth(c: C) -> C =\n      \
                PersistentCollection.insert(\n        \
                PersistentCollection.insert(c, boxed(v: \"zz\")), boxed(v: \"aaa\"))\n  \
                end\n";
    let src = |ns: &str, slot: &str| {
        program(
            ns,
            &format!(
                "{BY_INNER}{grow}  sort Driver\n    \
                 import anthill.prelude.List.{{cons, nil}}\n    \
                 operation go(n: Int64) -> String =\n      \
                 firstInner(SortedSet.toList(Grow.addBoth(\n        \
                 SortedSet.empty[T = Boxed[E = String], O = ByInner{slot}]())))\n    \
                 operation firstInner(l: List[T = Boxed[E = String]]) -> String =\n      \
                 match l\n        \
                 case nil() -> \"<empty>\"\n        \
                 case cons(h, t) ->\n          \
                 match h\n            \
                 case boxed(v) -> v\n  \
                 end",
            ),
        )
    };
    assert_eq!(
        eval_str(
            &src("wi456.deepA", "[OI = ByLength]"),
            "wi456.deepA.Driver.go",
            "generic consumer over `ByInner[OI = ByLength]`",
        ),
        "zz",
    );
    assert_eq!(
        eval_str(
            &src("wi456.deepB", "[OI = Alphabetical]"),
            "wi456.deepB.Driver.go",
            "generic consumer over `ByInner[OI = Alphabetical]`",
        ),
        "aaa",
        "the nested binding survives three levels of indirection — which is the whole \
         claim (b) was asking after",
    );
}

/// THE SLOT IS STAMPED BY THE FRAME WHOSE SUB-GOAL TIED, NOT BY THE NEAREST ENCLOSING
/// PROVIDER THAT HAPPENS TO HAVE ONE — found by /code-review on this ticket's own first
/// draft, which stamped "the innermost owner" and got it wrong.
///
/// `named_requirement_slots` is empty for the overwhelmingly common all-anonymous owner,
/// so a tie raised under such a provider stamps nothing and keeps travelling. The first
/// draft let the next frame out claim it, and the message then asserted a FALSE fact:
///
/// > it fills named slot `OI` of `ma.ByInner`, so bind that slot in the VALUE position,
/// > as `ma.ByInner[OI = …]`
///
/// The tie is `Marked` among `MarkA`/`MarkB` — `TokVia`'s ANONYMOUS requires, one level
/// below `OI`. `OI` itself resolves fine (`TokVia` is the sole `WeakOrd[Tok]`), so
/// binding it re-selects `TokVia` and re-raises the identical tie: the "advertise a
/// repair the next compile rejects" failure `TieRepair` exists to prevent.
///
/// `!err.is_forwarded()` is the condition, and it is not a rephrasing of "innermost":
/// it is true only in the frame whose OWN sub-goal is the goal that tied. An unstamped
/// tie renders the SCHEMA wording, which is true of every shape — so this is also the
/// only driver of `TieRepair::SubGoal(None)`, the majority arm.
///
/// BACKED OUT (`owns_the_tie = true`), MEASURED: this test fails with the message quoted
/// above. Everything else in the file passes either way, which is what makes this arm
/// the guard's sole control.
#[test]
fn a_tie_below_a_named_slot_is_not_attributed_to_that_slot() {
    let src = "
namespace wi456.misattr
  import anthill.prelude.{Ord, WeakOrd, PartialOrd, PartialEq, Eq, Int64, Bool, SortedSet}

  enum Tok
    import anthill.prelude.{PartialEq, Eq, PartialOrd}
    import anthill.prelude.Numeric.{sub}
    entity tok(n: Int64)
    provides PartialEq[T = Tok]
    provides Eq[T = Tok]
    provides PartialOrd[T = Tok]
    operation eq(a: Tok, b: Tok) -> Bool =
      match a
        case tok(an) -> match b
          case tok(bn) -> PartialEq.eq(an, bn)
    operation compare(a: Tok, b: Tok) -> Int64 =
      match a
        case tok(an) -> match b
          case tok(bn) -> sub(an, bn)
  end

  sort Marked
    sort T = ?
    operation mark(x: T) -> Int64
  end
  sort MarkA
    provides Marked[T = Tok]
    operation mark(x: Tok) -> Int64 = 1
  end
  sort MarkB
    provides Marked[T = Tok]
    operation mark(x: Tok) -> Int64 = -1
  end

  sort TokVia
    import anthill.prelude.{WeakOrd, PartialOrd}
    requires Marked[T = Tok]
    provides WeakOrd[T = Tok]
    operation compare(a: Tok, b: Tok) -> Int64 = Marked.mark(a)
  end

  enum Boxed
    import anthill.prelude.{PartialEq, Eq}
    sort E = ?
    requires Eq[T = E]
    entity boxed(v: E)
    provides PartialEq[T = Boxed]
    provides Eq[T = Boxed]
    operation eq(a: Boxed, b: Boxed) -> Bool =
      match a
        case boxed(av) -> match b
          case boxed(bv) -> PartialEq.eq(av, bv)
  end

  sort ByInner
    import anthill.prelude.{WeakOrd, PartialOrd}
    sort E = ?
    requires OI: WeakOrd[T = E]
    provides PartialOrd[T = Boxed[E = E]]
    provides WeakOrd[T = Boxed[E = E]]
    operation compare(a: Boxed[E = E], b: Boxed[E = E]) -> Int64 =
      match a
        case boxed(av) -> match b
          case boxed(bv) -> WeakOrd.compare(av, bv)
  end

  sort Driver
    operation go(n: Int64) -> Int64 =
      let s = SortedSet.empty[T = Boxed[E = Tok], O = ByInner]()
      SortedSet.size(SortedSet.insert(s, boxed(v: tok(n: 1))))
  end
end
";
    let errs = tie_errs(src);
    // ONE message carries the whole verdict — the wi870 rule, applied here too: three
    // `contains` over the JOINED text would be satisfied by three different errors.
    assert!(
        errs.iter().any(|e| e.contains("wi456.misattr.Marked")
            && e.contains("MarkA")
            && e.contains("is ANONYMOUS, so there is no slot to bind")),
        "the tie reported is the one that happened — `Marked`, among its two rivals — \
         and with no binder to name, the anonymous-requirement wording is the honest \
         answer. This is also the only arm that drives `TieRepair::SubGoal(None)`: \
         {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("named slot `OI`")),
        "and it is NOT attributed to `ByInner`'s `OI`, which resolved fine: binding it \
         re-selects `TokVia` and re-raises this very tie: {errs:?}"
    );
}
