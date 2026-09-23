//! WI-20260921-R10KC — A SPEC DEFAULT BODY RECEIVES ITS PROVISION'S DICTIONARY, and
//! resolves a body-less sibling member by PROJECTION out of it.
//!
//! THE DEFECT, IN ONE SENTENCE: both routes find the same implementation, and only one
//! of them brings the evidence.
//!
//! WHAT RAN BEFORE. `Searchable.containsAny` is a spec's shared DEFAULT BODY; it calls
//! the body-less sibling `contains`, whose carrier `MySet requires O: WeakOrd[T]` reads
//! that slot through `WeakOrd.compare`. The dictionary was built THREE times on the way
//! in — at `MySet.empty[T = String, O = ByLength]()`, at `MySet.insert`, and at the
//! `containsAny` call site itself, where the typer resolved `Searchable` AT `MySet` — and
//! it reached the frame that reads it ZERO times:
//!
//!   * the typer's defaulted fall-through arm resolved the instance and
//!     `classify_pin_or_apply_within` DROPPED it, because its `needs_reqs` test counts
//!     only the SPEC half of [`dict_layout`] and `Searchable` declares no `requires`;
//!     the class became `PinNow`, which carries no requirements channel at all;
//!   * so `containsAny`'s frame was empty, the sibling call's channel was empty, and the
//!     dispatch fell to VALUE-DIRECTION — which rebuilt `MySet`'s chain from
//!     `node(elem: "zz", rest: nothing())`, a value that mentions no ordering.
//!
//! The rebuild SUCCEEDS wherever the reconstructed goal has a unique answer, which is
//! why most of the value-directed population works. It fails exactly where the
//! construction site made a SELECTION the data does not record — which is what a NAMED
//! requirement slot is (058 §4.7: a named slot is a type parameter, and a runtime value
//! carries none). The refusal was:
//!
//! > cannot dispatch `anthill.prelude.WeakOrd.compare`: … reached by dispatching on a
//! > VALUE, which carries its sort but none of its type parameters — so the provider the
//! > value's construction chose for the slot cannot be recovered here, and more than one
//! > could have been.
//!
//! THE FIX, IN TWO PLACES, and MEASURED to need both — backing out either one restores
//! that exact refusal on all four default-body rows (this file's
//! [`a_spec_default_body_reads_the_carriers_named_slot_and_the_slot_decides`] and
//! [`the_dictionary_survives_the_default_bodys_own_recursion`], plus
//! `wi456_sorted_set_collection_test`'s `defaultByLength` / `defaultAlphabetical`):
//!
//!   * TYPER (`classify_pin_or_apply_within`, kb/typing.rs): a resolved tree that pins a
//!     PROVIDER the callee's own parent is not makes the dictionary the callee's
//!     DISPATCH ENVIRONMENT, so it is threaded even when the callee reads no named slot
//!     of its own.
//!   * EVAL (`Interpreter::spec_instance_for_sibling_call`, eval/eval.rs): a call to a
//!     member of the running operation's OWN sort fills its empty channel from that
//!     frame's `__req_self`. That is `Dictionary.resolveOp` — the projection
//!     `stdlib/anthill/realization/runtime.anthill` already declares — spelled in eval as
//!     `dispatch_via_sort_ops_table` + `expand_dispatching_dict`, both of which already
//!     existed for the `DeferToRequirement` route.
//!
//! WHY THE ORDERING IS THE INSTRUMENT. A test that only asserts the program RUNS would
//! stay green on a fix that threaded any dictionary at all, and would have stayed green
//! before the fix on any carrier whose slot nothing reads. Every `contains` row below is
//! driven at BOTH orderings with ONE polymorphic body and ONE query, and they must
//! DISAGREE: `"aa"` is not in `{"zz"}`, but under `ByLength` it is the same CLASS as
//! `"zz"` (both length 2) and under `Alphabetical` it is not. One answer twice fails.
//!
//! Related: WI-456, where this was measured (058 §33 is the layout this reads);
//! WI-1091/WI-1093, which fixed the same defect for a spec that DOES declare `requires`
//! — the half `needs_reqs` could already see.

use anthill_core::eval::Value;

/// The two rival orderings, so nothing below is explained by there being one thing to
/// pick. `ByLength` makes `"zz"` and `"aa"` one class; `Alphabetical` separates them.
const RIVALS: &str = r#"
  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  sort Alphabetical
    import anthill.prelude.PartialOrd.{lt, gt}
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 =
      if lt(a, b) then -1 else if gt(a, b) then 1 else 0
  end
"#;

/// The spec and the carrier. `Searchable` declares NO `requires` of its own — that is
/// the whole point: its dictionary's SPEC half is empty, so the only content is the
/// PROVIDER half, which is `MySet`'s named `O` slot.
const TOWER: &str = r#"
  sort Searchable
    import anthill.prelude.List.{nil, cons}
    sort C = ?
    sort Element = ?
    -- BODY-LESS: a dictionary entry, projected out by `Dictionary.resolveOp`.
    operation contains(c: C, x: Element) -> Bool
    -- THE ONE SHARED DEFAULT BODY. It calls the body-less sibling above AND recurses
    -- into itself, so both sibling shapes are driven: a body-less member (eval step 3b)
    -- and a BODIED one (step 3, which enters the spec's own body again and must carry
    -- the dictionary a second time).
    operation containsAny(c: C, xs: List[T = Element]) -> Bool =
      match xs
        case nil() -> false
        case cons(h, t) -> if contains(c, h) then true else containsAny(c, t)
  end

  enum MySet
    import anthill.prelude.PartialOrd.{lt, gt}
    sort T = ?
    requires O: WeakOrd[T]

    entity nothing
    entity node(elem: T, rest: MySet[T = T, O = O])

    provides Searchable[C = MySet[T = T, O = O], Element = T]
    operation contains(s: MySet[T = T, O = O], x: T) -> Bool =
      match s
        case nothing() -> false
        case node(y, r) ->
          let c = WeakOrd.compare(x, y)
          if lt(c, 0) then false
          else if gt(c, 0) then contains(r, x)
          else true

    operation empty() -> MySet[T = T, O = O] = nothing()

    operation insert(s: MySet[T = T, O = O], x: T) -> MySet[T = T, O = O] =
      match s
        case nothing() -> node(x, nothing())
        case node(y, r) ->
          let c = WeakOrd.compare(x, y)
          if lt(c, 0) then node(x, s)
          else if gt(c, 0) then node(y, insert(r, x))
          else s
  end
"#;

fn program(ns: &str, rivals: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, Bool}}\n  \
         import anthill.prelude.List.{{nil, cons}}\n\
         {rivals}{TOWER}{body}\nend\n"
    )
}

fn eval_bool(src: &str, entry: &str, why: &str) -> bool {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{why}; got {other:?}"),
    }
}

/// THE DRIVER. One polymorphic default body, one query, two orderings, two answers.
///
/// `{"zz"}` does not contain `"aa"`. Under `ByLength` it contains its CLASS (2 == 2), so
/// `Searchable.containsAny(s, ["aa"])` is `true`; under `Alphabetical` it is `false`.
/// The comparator that decides is `MySet`'s named `O` slot, chosen at
/// `MySet.empty[T = String, O = …]()` — three call frames away from the `contains`
/// dispatch that reads it, and recorded nowhere in the set's data.
///
/// BACKED OUT, EACH ALONE, MEASURED: `threads_instance` (kb/typing.rs) or
/// `spec_instance_for_sibling_call` (eval/eval.rs) out → BOTH rows raise
/// `cannot dispatch anthill.prelude.WeakOrd.compare: … reached by dispatching on a
/// VALUE … the provider the value's construction chose for the slot cannot be recovered
/// here`. Neither half is sufficient: the typer's builds the dictionary into
/// `containsAny`'s frame and the sibling call's own channel is still empty; eval's has
/// nothing in the frame to read.
#[test]
fn a_spec_default_body_reads_the_carriers_named_slot_and_the_slot_decides() {
    let src = program(
        "r10kc.split",
        RIVALS,
        "  sort Driver\n    \
         operation byLength(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")\n      \
         Searchable.containsAny(s, cons(\"aa\", nil()))\n    \
         operation alphabetical(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = Alphabetical](), \"zz\")\n      \
         Searchable.containsAny(s, cons(\"aa\", nil()))\n  \
         end",
    );
    assert!(
        eval_bool(
            &src,
            "r10kc.split.Driver.byLength",
            "the default body must reach `MySet.contains` through the `Searchable[MySet]` \
             instance, whose slot is ByLength — under which \"aa\" IS \"zz\"'s class"
        ),
        "ByLength must answer yes"
    );
    assert!(
        !eval_bool(
            &src,
            "r10kc.split.Driver.alphabetical",
            "…and the SAME body under Alphabetical must answer differently"
        ),
        "Alphabetical must answer no — one answer twice would mean the comparator never \
         decided, only that some route answered"
    );
}

/// THE RECURSIVE HOP, which the row above does not drive: there the FIRST element
/// decides and `containsAny` never calls itself. Here `"q"` (length 1) matches under
/// neither ordering, so the answer comes from the SECOND element — reached through
/// `containsAny(c, t)`, a call to a BODIED sibling.
///
/// It is a different eval route and a different failure. A body-less sibling falls to
/// value-direction (step 3b); a bodied one is found by `cached_operation_body` at step 3
/// and entered with whatever channel the apply carried — EMPTY — so without the fix the
/// dictionary survives exactly one frame and the recursion loses it. Both are filled by
/// [`Interpreter::spec_instance_for_sibling_call`], which is why one function covers
/// both and why this row would not be redundant if it did not.
#[test]
fn the_dictionary_survives_the_default_bodys_own_recursion() {
    let src = program(
        "r10kc.recur",
        RIVALS,
        "  sort Driver\n    \
         operation byLength(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")\n      \
         Searchable.containsAny(s, cons(\"q\", cons(\"aa\", nil())))\n    \
         operation alphabetical(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = Alphabetical](), \"zz\")\n      \
         Searchable.containsAny(s, cons(\"q\", cons(\"aa\", nil())))\n  \
         end",
    );
    assert!(
        eval_bool(
            &src,
            "r10kc.recur.Driver.byLength",
            "the second element decides, so the dictionary had to cross the recursive \
             `containsAny(c, t)` as well as the `contains(c, h)`"
        ),
        "ByLength must answer yes at the second element"
    );
    assert!(
        !eval_bool(&src, "r10kc.recur.Driver.alphabetical", "the same, unordered"),
        "Alphabetical must answer no"
    );
}

/// CONTROL, GREEN EITHER WAY BY DESIGN — the DIRECT call, where the carrier type is
/// written at the call site and the typer pins the slot. This is the route that worked
/// before this ticket, and keeping it green says the fix did not reroute the typed call;
/// it is also what proves `ByLength` and `Alphabetical` genuinely disagree on this query,
/// without which the driver above would be measuring nothing.
#[test]
fn control_the_direct_typed_call_already_read_the_slot() {
    let src = program(
        "r10kc.direct",
        RIVALS,
        "  sort Driver\n    \
         operation byLength(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")\n      \
         MySet.contains(s, \"aa\")\n    \
         operation alphabetical(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = Alphabetical](), \"zz\")\n      \
         MySet.contains(s, \"aa\")\n  \
         end",
    );
    assert!(eval_bool(&src, "r10kc.direct.Driver.byLength", "direct, ByLength"));
    assert!(!eval_bool(&src, "r10kc.direct.Driver.alphabetical", "direct, Alphabetical"));
}

/// CONTROL, GREEN EITHER WAY BY DESIGN — the UNIQUE-ANSWER REBUILD, which is why most
/// of the value-directed population never noticed this defect.
///
/// At `T = Int64` there is ONE `WeakOrd[Int64]` in scope (`Int64`'s own), so the goal
/// value-direction reconstructs from `node(elem: 7, rest: nothing())` has a unique
/// answer and the rebuild lands on the right comparator — not because evidence
/// travelled, but because nothing else could have been chosen. That is the boundary this
/// ticket's blast radius is drawn at, and it is the same boundary
/// `wi456_sorted_set_collection_test::single_ordering_control_*` pins one spec over.
///
/// `Int64` AND NOT `String` WITH THE RIVALS REMOVED, which is what a first draft of this
/// control did — and the back-out measurement is what caught it: the draft FAILED with
/// the fix out, because the stdlib's own `String` provides `WeakOrd[String]`, so
/// dropping `Alphabetical` still leaves TWO providers (`ByLength` and `String`) and the
/// rebuild still ties. A control that fails on the back-out is not a control.
#[test]
fn control_a_single_provider_rebuilds_the_same_answer() {
    let src = program(
        "r10kc.single",
        RIVALS,
        "  sort Driver\n    \
         operation go(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = Int64, O = Int64](), 7)\n      \
         Searchable.containsAny(s, cons(7, nil()))\n  \
         end",
    );
    assert!(
        eval_bool(&src, "r10kc.single.Driver.go", "single-provider control"),
        "with one `WeakOrd[Int64]` in scope the rebuild cannot tie, so this row passes \
         with the fix backed out too"
    );
}

/// THE LIST QUESTION, asked during review and MEASURED here: a `List` of witnessed
/// carriers — does the list have to keep the element's witness?
///
/// NO, AND NOTHING NEEDS TO: the witness rides the ELEMENT TYPE. `Bulk` is written
/// against `Searchable` alone — it knows neither `MySet` nor any ordering — and its
/// `requires S: Searchable[C = C, Element = E]` is resolved at `C := MySet[T = String,
/// O = …]`, a type that already names the witness, so the dictionary for that C carries
/// `MySet`'s provider half. `List[T = C]` contributes nothing; it is a container over a
/// type that has already pinned the slot. Where a list DOES carry a dictionary of its own
/// (`Eq[List[T]] :- Eq[T]`) the same mechanism holds one level up — the condition slot is
/// resolved at the element type, so it transitively holds this witness.
///
/// WHAT WOULD NEED A VALUE-CARRIED DICTIONARY is the shape the type cannot express:
/// elements at DIFFERENT `O` in ONE list. [`a_list_holds_one_witness_for_every_element`]
/// measures why that is not a quantifier question — a list has one element type, so one
/// witness — and homogeneity is exactly what makes one type-level dictionary sufficient
/// here.
///
/// FOUR LEVELS separate the binding from the read: `MySet.empty[O = ByLength]` →
/// `Bulk`'s `S` slot at the call → the `Searchable[MySet]` instance → `MySet.contains`'s
/// own `__req_weakord`. The two rows must still disagree.
///
/// PASSES EITHER WAY BY DESIGN — stated because a review found this row presented as a
/// driver when it is not. `Bulk` DECLARES `requires S: Searchable[…]`, so
/// `Searchable.contains(h, x)` is a `DeferToRequirement` read of `Bulk`'s own slot
/// (`start_apply_deferred`): the channel is non-empty, it never reaches
/// [`Interpreter::spec_instance_for_sibling_call`], and `needs_reqs` is already true so
/// the typer's clause is never consulted. That is the route WI-1091/WI-1093 delivered.
/// What this row is FOR is the question a review asked of the design — whether a
/// CONTAINER of witnessed carriers needs a witness of its own — and the answer it
/// measures is that it does not: the element TYPE carries it, and the FORWARDED spelling
/// runs at four levels' remove. WI-20260921-EE0EP cites it as exactly that.
#[test]
fn a_generic_consumer_over_a_list_keeps_each_elements_ordering() {
    let src = program(
        "r10kc.list",
        RIVALS,
        "  sort Bulk\n    \
         sort C = ?\n    \
         sort E = ?\n    \
         requires S: Searchable[C = C, Element = E]\n    \
         operation anyHas(cs: List[T = C], x: E) -> Bool =\n      \
         match cs\n        \
         case nil() -> false\n        \
         case cons(h, t) -> if Searchable.contains(h, x) then true else anyHas(t, x)\n  \
         end\n  \
         sort Driver\n    \
         operation byLength(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")\n      \
         Bulk.anyHas[C = MySet[T = String, O = ByLength], E = String](cons(s, nil()), \"aa\")\n    \
         operation alphabetical(n: Int64) -> Bool =\n      \
         let s = MySet.insert(MySet.empty[T = String, O = Alphabetical](), \"zz\")\n      \
         Bulk.anyHas[C = MySet[T = String, O = Alphabetical], E = String](cons(s, nil()), \"aa\")\n  \
         end",
    );
    assert!(
        eval_bool(
            &src,
            "r10kc.list.Driver.byLength",
            "the element type names the witness, so the generic list consumer keeps it"
        ),
        "ByLength must answer yes"
    );
    assert!(
        !eval_bool(&src, "r10kc.list.Driver.alphabetical", "the same, unordered"),
        "Alphabetical must answer no"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// THE ROUTES WITH NO STATIC TYPE TO BUILD A DICTIONARY FROM
//
// This ticket was FILED as "may a requirement dictionary be stored in a VALUE", and the
// answer turned out to be that it need not be for the program above: the carrier's type
// is written or inferred at every site, so the dictionary can be BUILT — it was simply
// never handed to the frame that reads it. What survives of the original question is the
// population where there genuinely is no static type. The ticket named three; each is
// MEASURED here, and `UnavailableWhy::NamedSlotNotCarried`'s remaining job is what they
// add up to (its site in kb/typing.rs names this section back).
//
//  1. THE HOST ENTRY (`Interpreter::call` → `seed_entry_requirements`) — RUNS, AND ITS
//     ANSWER IS THE WRONG ONE. Driven by [`the_host_entry_route_answers_by_value_direction`].
//     Not a gap this ticket opened and not one it may close by itself: the sort half of a
//     host entry's frame is filled with self-rooted STAND-INS, and WI-868's doc at
//     `Interpreter::stand_in_requirement` records that as a decision with three
//     measurements behind it — a stand-in is "an invitation to the rescue, which is the
//     only reason `interp.call` works at all on a sort with a `requires`". The rescue is
//     value-direction, and for a NAMED slot it answers from the ARGUMENTS rather than
//     from the slot: `WeakOrd.compare("aa", "zz")` resolves to `String`'s own ordering,
//     so a `ByLength` set is searched alphabetically and nothing says so. What would
//     close it is named at that same site as the thing that "would re-open" WI-868: a
//     stand-in that keeps the provider's identity while carrying an absence — a change to
//     the dictionary VALUE, which is the half of this ticket's original framing that is
//     still live.
//
//     THE SORT HALF ONLY. The OP-half twin — EE0EP's `has(s: MySet[T = String], …)`,
//     whose slot `s.O` is op-scoped — was closed by WI-20260922-ATFGH without touching
//     the stand-in: that slot is a marker whose read is refused at `interp.call`, and
//     `Interpreter::call_with_witnesses` names its witness
//     (`wi_ee0ep_param_dictionary_test::the_host_entry_names_the_witness_or_is_refused`).
//     This row's slot is the SORT's own `O`, one of the dictionaries
//     `call_with_requirements` takes from a host, and WI-868's stand-in decision is what
//     keeps plain `interp.call` as it is.
//
//  2. THE SLD BRIDGE from a rule body (`call_op_bridged`) — SUSPENDS. It resolves the
//     callee's chain from the ARGUMENT TYPES and passes `NamedSlotTies::Raise`, so a
//     named-slot tie is an `Ambiguous` verdict rather than a recorded absence, and the
//     bridge residualizes instead of answering under a guessed ordering. That is the
//     right verdict for this route: a residual goal is a conditional answer the caller
//     can still discharge, where a `NoProvider` marker would be an answer that raises at
//     the read. Not driven here, because the rule shape that reaches it residualizes one
//     goal EARLIER — measured: `rule bridged(?r) :- ?s = Mk.set(0), ?r =
//     Searchable.contains(?s, "aa")` answers one conditional solution with `eq(?_,
//     set(0))` itself undischarged, with ONE provider in scope as well as with two. So an
//     assertion here would not be about the slot.
//
//  3. THE OPENED RIGID — REFUSED, and the ticket's framing of it was WRONG TWICE. It
//     said "a true existential …, which Anthill does not have"; Anthill HAS existentials
//     (`docs/kernel-language.md`, "In a RETURN the quantifier flips to ∃", WI-1063: a
//     return's unwritten slot IS existential — the body PACKS a witness, each USE OPENS a
//     fresh rigid skolem), and a rigid in a type projection is one of those openings. So
//     `operation mk() -> MySet[T = String]` over a body that builds at `O = ByLength` IS
//     the shape, it is spellable, and it is where this ticket's fix does not reach: the
//     skolem names no provider, so no dictionary can be built at the call site either.
//     [`the_existential_return_opens_a_skolem_that_names_no_provider`] drives both halves,
//     and the asymmetry is the finding: the DIRECT call is refused AT LOAD by WI-1094's
//     message, which names the slot and the repair, while the same value through the SPEC
//     loads clean and refuses one phase later with `NamedSlotNotCarried`.
//
//     THE SECOND ERROR was calling `List[T = MySet[T = String, O = ?]]` UNSPELLABLE. It
//     is spellable, and the consumer over it RUNS once it declares and forwards the slot
//     — [`a_generic_consumer_over_a_list_keeps_each_elements_ordering`] is that program.
//     What cannot be BUILT is a HETEROGENEOUS list, and the reason is not the quantifier
//     but arity: an unwritten nested slot takes ONE fresh rigid PER SLOT (WI-1061, "the
//     inner row of `List[T = Stream]` … takes a fresh rigid, one per slot"), and a list
//     has ONE element type, so one `O` for every element. Measured by
//     [`a_list_holds_one_witness_for_every_element`]. That — a witness quantified
//     PER DATUM rather than per type — is the only shape a value-carried dictionary
//     would be the sole answer for, and it is rank-1-ness that excludes it, not a
//     missing ∃.

/// ROUTE 1 — THE HOST ENTRY, PINNED AS IT IS RATHER THAN AS IT SHOULD BE.
///
/// `MySet.contains` is called from Rust with a `MySet` VALUE and a `String`: no call
/// site, no carrier type, and `seed_entry_requirements` fills the `O` slot with a
/// self-rooted stand-in. `dispatch_via_sort_ops_table` finds no `compare` at `MySet`, so
/// the read falls through to value-direction, which classifies `WeakOrd.compare("aa",
/// "zz")` from its STRING arguments and lands on `String`'s own alphabetical ordering.
/// The set was built at `ByLength`, under which `"aa"` IS `"zz"`'s class, so the right
/// answer is `true` and this route answers `false`.
///
/// PINNED, NOT ACCEPTED. This is the WI-868 stand-in-vs-marker decision seen from the one
/// side it is wrong on, and fixing it is the change that doc names as what "would
/// re-open" it. Pinning the wrong answer is what makes the fix VISIBLE when someone makes
/// it — the test fails, and its author reads this paragraph.
///
/// PASSES EITHER WAY BY DESIGN with respect to THIS ticket's two edits: a host entry's
/// channel is non-empty (the stand-ins), so `spec_instance_for_sibling_call` returns it
/// untouched, and no call site is classified. Measured with both edits backed out:
/// identical `false`.
#[test]
fn the_host_entry_route_answers_by_value_direction() {
    let src = program(
        "r10kc.host",
        RIVALS,
        "  sort Mk\n    \
         operation one(n: Int64) -> MySet[T = String, O = ByLength] =\n      \
         MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")\n  \
         end\n  \
         sort InSource\n    \
         operation go(n: Int64) -> Bool =\n      \
         MySet.contains(Mk.one(0), \"aa\")\n  \
         end",
    );
    // THE CONTROL, and it is what makes the row below a defect rather than a fact about
    // `ByLength`: the SAME call written IN ANTHILL, where the argument's type carries the
    // slot, answers `true`.
    assert!(
        eval_bool(
            &src,
            "r10kc.host.InSource.go",
            "in-source, the carrier type writes `O` and the typer pins it"
        ),
        "CONTROL: under ByLength, \"aa\" is \"zz\"'s class — the right answer is true",
    );

    let mut interp = crate::common::interp_for(&src);
    let one = interp
        .call("r10kc.host.Mk.one", &[Value::Int(0)])
        .expect("building the one-element set");
    assert!(
        matches!(
            interp.call(
                "r10kc.host.MySet.contains",
                &[one, Value::Str("aa".to_string())]
            ),
            Ok(Value::Bool(false))
        ),
        "the host entry has no carrier type, so the `O` slot is a stand-in and the read \
         falls to value-direction, which answers from the STRING arguments — `String`'s \
         alphabetical ordering, not the set's `ByLength`. Pinned as the wrong answer it \
         is; see this test's doc for what closes it",
    );
}

/// ROUTE 3 — THE EXISTENTIAL RETURN, both halves, and the asymmetry between them.
///
/// `Pack.mk` packs `O := ByLength` and elides the slot in its return, so each USE opens a
/// fresh rigid skolem (kernel-language.md, WI-1063). The skolem names no provider, so
/// there is no dictionary to build at the call site — which is the one remaining
/// population of `UnavailableWhy::NamedSlotNotCarried` after this ticket.
///
/// THE TWO HALVES REFUSE AT DIFFERENT PHASES, and that is the finding worth keeping:
///   * DIRECT (`MySet.contains(Pack.mk(0), …)`) — a LOAD error, WI-1094's, which names
///     the slot and the repair ("Write `O` in the parameter's type");
///   * THROUGH THE SPEC (`Searchable.containsAny(Pack.mk(0), …)`) — loads CLEAN and
///     refuses at run time with the value-directed `NamedSlotNotCarried` sentence.
/// One phase apart for one cause. Whether the spec route should reach WI-1094's load
/// refusal is not this ticket's to decide; it is recorded so the next reader has the
/// measurement rather than an assumption.
#[test]
fn the_existential_return_opens_a_skolem_that_names_no_provider() {
    const PACK: &str = "  sort Pack\n    \
         operation mk(n: Int64) -> MySet[T = String] =\n      \
         MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\")\n  \
         end\n";

    // THROUGH THE SPEC: loads, and refuses at the read.
    let via_spec = program(
        "r10kc.exists",
        RIVALS,
        &format!(
            "{PACK}  sort Driver\n    \
             operation go(n: Int64) -> Bool =\n      \
             Searchable.containsAny(Pack.mk(0), cons(\"aa\", nil()))\n  \
             end"
        ),
    );
    let mut interp = crate::common::interp_for(&via_spec);
    let err = format!("{:?}", interp.call("r10kc.exists.Driver.go", &[Value::Int(0)]));
    assert!(
        err.contains("NAMED requirement slot") && err.contains("cannot be recovered"),
        "an opened skolem names no provider, so the default body has no dictionary to \
         receive and the read must be refused naming the slot; got {err}"
    );

    // DIRECT: refused one phase earlier, at LOAD.
    let direct = program(
        "r10kc.exists2",
        RIVALS,
        &format!(
            "{PACK}  sort Driver\n    \
             operation go(n: Int64) -> Bool = MySet.contains(Pack.mk(0), \"aa\")\n  \
             end"
        ),
    );
    let errs = crate::common::try_load_kb_with(&direct)
        .err()
        .unwrap_or_else(|| panic!("the direct call at an opened skolem must not load"));
    assert!(
        errs.iter().any(|e| e.contains("universally quantified")
            && e.contains("named requirement slot `O")),
        "the direct route gets WI-1094's LOAD refusal naming the unwritten slot; got \
         {errs:?}"
    );
}

/// THE ARITY OF A WITNESS IN A CONTAINER, measured because a review asked the obvious
/// question — "we can have `List[SortedSet]` and run `head.insert`" — and the answer is
/// YES, with one caveat that is the whole of what a value-carried dictionary would buy.
///
/// TWO ROWS, and neither is about the witness:
///
///  1. `List[T = MySet]` IS SPELLABLE, and `head.insert` fails on the ELEMENT type: a
///     nested unwritten slot takes ONE FRESH RIGID PER SLOT (WI-1061, "the inner row of
///     `List[T = Stream]` … takes a fresh rigid, one per slot"), so `h : MySet[T = ρT,
///     O = ρO]` and a `String` does not fit `ρT`. Write the `T` and this goes away;
///     what is left is the witness, which is
///     [`an_unwritten_named_slot_has_no_channel_at_any_depth`]'s subject.
///  2. WHAT CANNOT BE BUILT is a list holding elements at two DIFFERENT witnesses, and
///     `cons` says so in the plainest possible terms. One list, one element type, one
///     `O`; the `?` is per SLOT, never per element.
///
/// Row 2 is the only shape that would need the witness in the DATUM, and it is RANK-1-ness
/// that excludes it, not a missing ∃ — Anthill has existentials (WI-1063), and
/// [`the_existential_return_opens_a_skolem_that_names_no_provider`] drives one.
#[test]
fn a_list_holds_one_witness_for_every_element() {
    // 1 — the element TYPE is rigid, so the value does not fit it.
    let errs = crate::common::try_load_kb_with(&program(
        "r10kc.arity",
        RIVALS,
        "  sort Bulk\n    \
         operation headHas(ss: List[T = MySet], x: String) -> Bool =\n      \
         match ss\n        \
         case nil() -> false\n        \
         case cons(h, t) -> MySet.contains(MySet.insert(h, x), x)\n  \
         end",
    ))
    .err()
    .expect("a bare nested carrier leaves T rigid");
    assert!(
        errs.iter()
            .any(|e| e.contains("insert.x") && e.contains("expected ?T, got String")),
        "an unwritten NESTED slot is a fresh rigid, so `insert`'s element does not \
         accept a String; got {errs:?}"
    );

    // 2 — THE ONE THAT CANNOT BE BUILT: two witnesses, one list.
    let errs = crate::common::try_load_kb_with(&program(
        "r10kc.hetero",
        RIVALS,
        "  sort Driver\n    \
         operation go(n: Int64) -> Bool =\n      \
         let byLen = MySet.empty[T = String, O = ByLength]()\n      \
         let alpha = MySet.empty[T = String, O = Alphabetical]()\n      \
         match cons(byLen, cons(alpha, nil()))\n        \
         case nil() -> false\n        \
         case cons(h, t) -> true\n  \
         end",
    ))
    .err()
    .expect("a list of two different orderings must not load");
    assert!(
        errs.iter().any(|e| e.contains("cons.tail")
            && e.contains("O = ByLength")
            && e.contains("O = Alphabetical")),
        "one list has one element type, so it has one witness — `cons` refuses the \
         second ordering by name; got {errs:?}"
    );
}

/// **DEPTH IS THE AXIS — SINCE WI-20260921-EE0EP, AND IT WAS NOT BEFORE.** This row used
/// to assert the opposite, and the inversion is the finding rather than an edit: a
/// TOP-LEVEL unwritten slot now has a channel and a NESTED one still has none.
///
/// WI-1059 and WI-1061 always said the two differ — a top-level unwritten slot IS the
/// projection off the value that carries it (`s: MySet[T = String]` is checked as
/// `s: MySet[T = String, O = s.O]`), where a nested one (`List[T = MySet[T = String]]`)
/// takes a fresh rigid with **no name at all**. What was true before EE0EP is that the
/// difference bought NOTHING: both got WI-1094's refusal, word for word, because a
/// signature that omits the slot had nowhere for a caller to put a dictionary.
///
/// EE0EP keys its channel on exactly that name. The synthesized slot
/// ([`SupplySource::FromParam`]) records WHICH PARAMETER to read the witness out of, so a
/// slot the language can spell as `s.O` is suppliable and a slot nothing spells is not.
/// The nested case is therefore not an oversight: there is no receiver to read, the
/// element is reached by a pattern match, and `List`'s own type says nothing about the
/// element's ordering. Writing the element's slot is the repair, and it works —
/// `wi_ee0ep_param_dictionary_test::a_list_element_keeps_its_own_ordering` drives it.
///
/// DRIVEN BY VALUE on the half that changed, not just by loading: the top arm must answer
/// the ARGUMENT's comparator, and one answer twice would mean the channel delivered some
/// other dictionary.
///
/// BACKED OUT: the top arm reverts to the refusal the nested arm still gets.
#[test]
fn the_channel_reaches_a_named_slot_and_not_a_nameless_one() {
    // TOP LEVEL — the slot is `s.O`, the language spells it, and the argument supplies it.
    let top = program(
        "r10kc.depth",
        RIVALS,
        "  sort Bulk\n    \
         operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)\n  \
         end\n  \
         sort Driver\n    \
         operation byLength(n: Int64) -> Bool =\n      \
         Bulk.has(MySet.insert(MySet.empty[T = String, O = ByLength](), \"zz\"), \"aa\")\n    \
         operation alphabetical(n: Int64) -> Bool =\n      \
         Bulk.has(MySet.insert(MySet.empty[T = String, O = Alphabetical](), \"zz\"), \"aa\")\n  \
         end",
    );
    assert!(
        eval_bool(&top, "r10kc.depth.Driver.byLength", "the top-level channel"),
        "a top-level unwritten slot is the projection `s.O`, which EE0EP supplies from \
         the argument — ByLength must answer yes"
    );
    assert!(
        !eval_bool(&top, "r10kc.depth.Driver.alphabetical", "the same body, the rival"),
        "…and the rival ordering must answer no through the SAME body; one answer twice \
         would mean the dictionary was re-derived rather than forwarded"
    );

    // NESTED — a fresh rigid nothing spells, so there is no receiver to read a witness
    // out of and the refusal stands.
    let nested = crate::common::try_load_kb_with(&program(
        "r10kc.depth.nested",
        RIVALS,
        "  sort Bulk\n    \
         operation headHas(ss: List[T = MySet[T = String]], x: String) -> Bool =\n      \
         match ss\n        \
         case nil() -> false\n        \
         case cons(h, t) -> MySet.contains(h, x)\n  \
         end",
    ))
    .err()
    .unwrap_or_else(|| panic!("a NESTED unwritten slot has no name and must not load"));
    // PINS THE NAMED-SLOT REFUSAL, not "some error happened". The first cut allowed
    // `expected ?T` as an alternative, which is the generic unification message and would
    // have kept this row green on any unrelated type error in the fixture — so it would
    // have stopped measuring the thing its own doc claims.
    assert!(
        nested
            .iter()
            .any(|e| e.contains("NOTHING HERE CAN SUPPLY IT")
                && e.contains("named requirement slot `O")),
        "a nested unwritten slot takes a fresh rigid (WI-1061) that nothing spells, so no \
         parameter can supply it — and the refusal must say so by name; got {nested:?}"
    );
}

/// **THE SIBLING ROUTE DISPATCHES ONLY WITHIN ITS OWN SPEC** — the gate a `/code-review`
/// of this ticket found missing, and which cost a SILENT WRONG ANSWER rather than a
/// missing one.
///
/// `dictionary_resolved_sibling` (step 3c) reads `__req_self` off the frame and hands it
/// to `resolve_op_target`, which keys on the target's SHORT NAME alone
/// (`sort_ops_lookup(provider, short)`). Nothing asked whether the dictionary was FOR the
/// spec the target belongs to. So a call to an unrelated spec's member, reached while the
/// frame happened to hold some instance dictionary, was redirected into that dictionary's
/// provider by name.
///
/// MEASURED before the gate: `Other.mark()` — body-less and receiver-less, so it reaches
/// 3c — called from `Marked`'s default body at a carrier `Box` that provides `Marked` and
/// NOT `Other`, answered **99** out of `Box.mark`. The trace read
/// `__req_self provider = Box` / `resolved to Box.mark`. Before WI-20260921-R10KC added
/// this route the same call was a loud `unrunnable_target_error`, so the ticket's own
/// "strictly additive" claim was true only about the PREVIOUS outcome.
///
/// The gate is [`spec_instance_for_sibling_call`]'s (2) and (3), unchanged: the target's
/// parent is a SORT, and the dictionary's provider PROVIDES it and is not it. Failing
/// either falls back to the loud error, so it can only restore a refusal and never break
/// a working call — which is why the four rows above still pass.
///
/// BACKED OUT: this row answers `99` instead of raising.
#[test]
fn the_sibling_route_does_not_dispatch_across_specs_by_short_name() {
    let src = r#"
namespace r10kc.crossspec
  import anthill.prelude.{Int64, String, Bool, List, WeakOrd, Ord}

  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  -- A spec the carrier does NOT provide, whose member is BODY-LESS and RECEIVER-LESS —
  -- the two properties that carry a call to step 3c.
  sort Other
    operation mark() -> Int64
  end

  -- The spec whose DEFAULT BODY runs with `__req_self` in its frame.
  sort Marked
    sort C = ?
    operation tag(c: C) -> Int64
    operation run(c: C) -> Int64 = Other.mark()
  end

  -- The carrier. Its `requires` is what puts a real dictionary in the frame; its `mark`
  -- is the short-name collision. It provides `Marked`, never `Other`.
  enum Box
    sort T = ?
    requires O: WeakOrd[T]
    entity box(v: T)
    provides Marked[C = Box[T = T, O = O]]
    operation tag(c: Box[T = T, O = O]) -> Int64 = 1
    operation mark() -> Int64 = 99
    operation make(v: T) -> Box[T = T, O = O] = box(v)
  end

  sort Driver
    operation go(n: Int64) -> Int64 =
      Marked.run(Box.make[T = String, O = ByLength]("z"))
  end
end
"#;
    let mut interp = crate::common::interp_for(src);
    let got = interp.call("r10kc.crossspec.Driver.go", &[Value::Int(0)]);
    assert!(
        got.is_err(),
        "`Other.mark` is not a member of anything `Box` provides, so the frame's `Box` \
         dictionary must not answer it — a short-name match is not a dispatch. Got {got:?}"
    );
}
