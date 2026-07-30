//! WI-844 (proposal 058 §5.3, §4.7, §7.1, §9 phase 4) — the `SortedSet` DRIVER: two
//! orderings of ONE carrier coexist, each is chosen at a CONSTRUCTION site, each is
//! threaded to the comparison that reads it, and merging one into the other is a TYPE
//! error.
//!
//! WHY THIS PHASE IS THE POINT OF THE ARC. Phases 0–3b moved a refusal (declarations →
//! the one ambiguous call) and gave the call a bracket to answer with. None of that is
//! worth having unless a real program can hold two witnesses of one `(spec, carrier)`
//! and keep them apart. `stdlib/anthill/prelude/sortedset.anthill` is that program:
//! `requires O: Ordered[T]` is a NAMED slot, so the ordering is a type PARAMETER and
//! `SortedSet[T = String, O = ByLength]` and `SortedSet[T = String, O = Alphabetical]`
//! are two types.
//!
//! WHAT THE TICKET ASSUMED AND WHAT WAS TRUE. §4.6 says the threading needs "nothing
//! new". Driven at HEAD before this ticket, HALF of it did:
//!
//!  * the construction site worked — `SortedSet.empty[T = String, O = ByLength]()`
//!    selects, via WI-841's sort-level seeding leg;
//!  * `union` of two differently-ordered sets was already the exact refusal §5.3
//!    promises, WI-836 having landed: `expected SortedSet[T = String, O = ByLength],
//!    got SortedSet[T = String, O = Alphabetical]`;
//!  * but the very next line of §5.3's own program, `SortedSet.insert(a, "zz")`,
//!    FAILED TO LOAD: *"constructing `Ordered[T = String]` is ambiguous among
//!    providers: String, ByLength, Alphabetical"*. And so did `union(a, b)` on two
//!    AGREEING sets — the program that must work. The pin was read only off the call's
//!    own BRACKET (WI-841), never off the type an argument already carried, so the
//!    driver was writable only by repeating `[T = String, O = ByLength]` at every
//!    call: the type parameter doing none of the work §4.7 gives it.
//!
//! WHAT LANDED is the READ half of §4.7's rule — `selections_from_slot_bindings`
//! (`kb/typing.rs`): a named slot's parameter is looked up in σ once argument
//! unification is complete, and a witness found there becomes an ordinary
//! `InstanceSelection`, judged by the same `check_selection_bindings` a written one is.
//! The bracket and the argument write the SAME variable; this reads it back. An
//! ABSTRACT binding derives nothing, which is what keeps §7.1's `report[T, O]` a
//! forward of the caller's dictionary rather than a wrong pin.
//!
//! WHERE THE TWO ORDERINGS LIVE, and why not in the stdlib. The ticket scopes phase 4
//! to `stdlib/anthill/prelude/`, and `SortedSet` is there. `ByLength` / `Alphabetical`
//! are NOT, and the reason is measured (`two_string_orderings_make_a_bare_compare_
//! ambiguous`): the Rust binding already declares `fact Ordered[T = String]`, so a
//! third and fourth provider in the PRELUDE would make every bracket-less
//! `Ordered.compare(a: String, b: String)` in every downstream program a load error.
//! Tier 3's coexistence is a per-program choice, not something a standard library may
//! impose on its consumers. So the driver declares them.
//!
//! Reference: docs/proposals/058-modular-instances.md §5.3, §4.7, §7.1, §9 phase 4;
//! stdlib/anthill/prelude/sortedset.anthill.

use anthill_core::eval::Value;

/// The two `Ordered[String]` witnesses of §5.3, declared separately so the
/// single-provider control can take one without a substring search into the other.
/// `ByLength` orders by `length`, `Alphabetical` by the host's string order — chosen so
/// that on `["zz", "aaa"]` they DISAGREE about the first element (`zz` is shorter,
/// `aaa` is earlier), which is what makes every value assertion below discriminating.
const BY_LENGTH: &str = r#"
  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Int64.{sub}
    fact Ordered[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end
"#;

const ALPHABETICAL: &str = r#"
  sort Alphabetical
    fact Ordered[T = String]
    operation compare(a: String, b: String) -> Int64 =
      if lt(a, b) then -1 else if gt(a, b) then 1 else 0
  end
"#;

/// `first`, so a `List[T = String]` result can be asserted as a plain `Value::Str`.
const FIRST: &str = r#"
    operation first(l: List[T = String]) -> String =
      match l
        case nil() -> "<empty>"
        case cons(h, t) -> h
"#;

fn program(ns: &str, body: &str) -> String {
    program_with(ns, &format!("{BY_LENGTH}{ALPHABETICAL}"), body)
}

/// The same preamble over a chosen set of ordering declarations — the single-provider
/// control takes `BY_LENGTH` alone, and spelling the imports twice to get it is how the
/// two drift.
fn program_with(ns: &str, orderings: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ordered, String, Int64, List, Bool, SortedSet}}\n  \
         import anthill.prelude.PartialOrd.{{lt, gt}}\n{orderings}{body}\nend\n"
    )
}

/// THE DRIVER PIPELINE, in one place: construct with `[T = String, O = <ordering>]`,
/// then insert `"zz"` and `"aaa"` and read the first element — every downstream call
/// BRACKET-LESS, which is the WI-844 mechanism under test. The two orderings disagree
/// about which of those two strings comes first, so the answer names the comparator:
/// `zz` under `ByLength`, `aaa` under `Alphabetical`.
///
/// A builder rather than seven hand-copies: several assertions below say "the SAME body
/// shape, differing only in the bracket", and with one producer that is structural
/// instead of something the reader has to verify by eye across the file.
fn string_pipeline(op: &str, ordering: &str) -> String {
    format!(
        "    operation {op}(n: Int64) -> String =\n      \
         let s = SortedSet.empty[T = String, O = {ordering}]()\n      \
         first(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, \"zz\"), \"aaa\")))\n"
    )
}

/// The `Int64` twin: `7` then `3`, so `3` is ascending's answer and `7` descending's.
fn int_pipeline(op: &str, ordering: &str) -> String {
    format!(
        "    operation {op}(n: Int64) -> Int64 =\n      \
         let s = SortedSet.empty[T = Int64, O = {ordering}]()\n      \
         match SortedSet.toList(SortedSet.insert(SortedSet.insert(s, 7), 3))\n        \
         case nil() -> -1\n        \
         case cons(h, t) -> h\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

fn loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got load errors: {errs:?}");
    }
}

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one. The load doubles as the clean-load gate (`interp_for` panics on a dirty
/// load), so a value assertion also asserts the program loads. Returning the `Result`
/// rather than a value is what lets the two WI-857 tests below assert a FAILURE through
/// the same runner every passing test uses. (`wi841_call_site_selection_test`'s shape.)
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

/// The dual of [`eval_int`] for the two tests that pin a KNOWN failure (WI-857): the
/// call must error, and with the expected text — "it errored" alone would pass on an
/// unrelated breakage of the same program.
fn eval_err(src: &str, entry: &str, needle: &str, why: &str) {
    let err = match eval_fresh(src, entry) {
        Err(e) => format!("{e:?}"),
        Ok(v) => panic!("{why}; expected a failure, got {v:?}"),
    };
    assert!(err.contains(needle), "{why}; expected {needle:?}, got: {err}");
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so every
/// `loads_clean` below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    // `load_errs` panics unless the load returned `Err`, so calling it IS the control.
    load_errs(&program(
        "wi844.control",
        "  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    ));
}

// ── §9 phase 4 acceptance ────────────────────────────────────────────

/// THE PRECONDITION, and it is not free: `String` already has an `Ordered` provider
/// (`fact Ordered[T = String]` in the Rust binding, `anthill-stl/anthill/string.anthill`).
/// So this loads THREE providers of one `(spec, carrier)` — the configuration tier 3
/// admits and every earlier phase refused at load.
#[test]
fn two_orderings_for_one_carrier_coexist() {
    loads_clean(
        &program("wi844.coexist", ""),
        "two witness sorts for `Ordered[String]` are NAMEABLE, so they coexist beside \
         the Rust binding's own provider (058 §4.1 tier 3)",
    );
}

/// …AND THAT IS WHY THEY ARE NOT IN THE PRELUDE. With them declared, a bracket-less
/// `Ordered.compare` on a `String` is an ambiguous dispatch naming all three. Pinning
/// this is what makes the placement decision a measurement rather than a preference:
/// putting these two witnesses in `stdlib/` would hand this error to every downstream
/// program that compares two strings.
#[test]
fn two_string_orderings_make_a_bare_compare_ambiguous() {
    let src = program(
        "wi844.bare",
        "  sort Use\n    operation cmp(a: String, b: String) -> Int64 = Ordered.compare(a, b)\n  end",
    );
    let errs = load_errs(&src);
    let tie: Vec<&String> = errs.iter().filter(|e| e.contains("ambiguous dispatch of")).collect();
    assert_eq!(tie.len(), 1, "one ambiguous call, one error; all errors: {errs:?}");
    let text = tie[0];
    assert!(
        text.contains("anthill.prelude.String")
            && text.contains("wi844.bare.ByLength")
            && text.contains("wi844.bare.Alphabetical"),
        "the diagnostic must name all three providers — the prelude's own included, \
         since it is the one a stdlib placement would collide with: {text}"
    );
}

/// THE HEADLINE (§5.3): `union` of a `ByLength` set and an `Alphabetical` one is a
/// TYPE error, in the words §5.3 wrote before the mechanism existed. This is WI-836's
/// acceptance surfacing on a real program — before that ticket the identical shape
/// loaded clean and merged sets ordered by different comparators.
#[test]
fn union_across_two_orderings_is_a_type_error() {
    let src = program(
        "wi844.merge",
        "  sort Driver\n    \
         operation mixed(n: Int64) -> List[T = String] =\n      \
         let a = SortedSet.empty[T = String, O = ByLength]()\n      \
         let b = SortedSet.empty[T = String, O = Alphabetical]()\n      \
         SortedSet.toList(SortedSet.union(a, b))\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("expected SortedSet[T = String, O = ByLength]")
                && e.contains("got SortedSet[T = String, O = Alphabetical]")
        }),
        "the merge hazard must be refused by ordinary parameter agreement, naming BOTH \
         orderings — that rendering IS §5.3's promised diagnostic: {errs:?}"
    );
}

/// …and the CONTROL that makes the refusal attributable to the ordering rather than to
/// `union` being unusable: the same call on two sets that AGREE loads. Without this,
/// deleting the ordering from `union`'s signature would leave the test above passing.
#[test]
fn union_within_one_ordering_loads() {
    loads_clean(
        &program(
            "wi844.agree",
            "  sort Driver\n    \
             operation same(n: Int64) -> List[T = String] =\n      \
             let a = SortedSet.empty[T = String, O = ByLength]()\n      \
             let b = SortedSet.empty[T = String, O = ByLength]()\n      \
             SortedSet.toList(SortedSet.union(a, b))\n  end",
        ),
        "two sets of the SAME ordering merge — MEASURED refused before WI-844 \
         (`constructing Ordered[T = String] is ambiguous`), which is why the mismatch \
         test above needs this control",
    );
}

/// …and it merges CORRECTLY. `union` is a single-pass merge over the two operands'
/// shared invariant (ascending under `O`, duplicate-free) rather than a fold of
/// `insert`, so its result is worth an assertion and not just a load: `{1,3,5} ∪
/// {2,3,4}` must be `{1,2,3,4,5}` — sorted, with the shared `3` appearing ONCE.
///
/// Four cases, because a merge has four ways to be wrong: the interleave, the duplicate
/// at the seam, and each empty operand (the base cases the recursion bottoms out on).
/// Commutativity is asserted too — a merge that dropped one side's tail would pass one
/// direction and fail the other.
#[test]
fn union_merges_ascending_and_deduplicates() {
    let src = program(
        "wi844.merge",
        "  sort Ascending\n    \
         import anthill.prelude.Numeric.{sub}\n    \
         fact Ordered[T = Int64]\n    \
         operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)\n  end\n  \
         sort Driver\n    \
         import anthill.prelude.String.{concat}\n    \
         import anthill.prelude.Int64.{to_string}\n    \
         operation render(l: List[T = Int64]) -> String =\n      \
         match l\n        \
         case nil() -> \"\"\n        \
         case cons(h, t) -> concat(to_string(h), render(t))\n    \
         operation a() -> SortedSet[T = Int64, O = Ascending] =\n      \
         let s = SortedSet.empty[T = Int64, O = Ascending]()\n      \
         SortedSet.insert(SortedSet.insert(SortedSet.insert(s, 5), 1), 3)\n    \
         operation b() -> SortedSet[T = Int64, O = Ascending] =\n      \
         let s = SortedSet.empty[T = Int64, O = Ascending]()\n      \
         SortedSet.insert(SortedSet.insert(SortedSet.insert(s, 4), 3), 2)\n    \
         operation ab(n: Int64) -> String = render(SortedSet.toList(SortedSet.union(a(), b())))\n    \
         operation ba(n: Int64) -> String = render(SortedSet.toList(SortedSet.union(b(), a())))\n    \
         operation aEmpty(n: Int64) -> String =\n      \
         render(SortedSet.toList(SortedSet.union(a(), SortedSet.empty[T = Int64, O = Ascending]())))\n    \
         operation emptyA(n: Int64) -> String =\n      \
         render(SortedSet.toList(SortedSet.union(SortedSet.empty[T = Int64, O = Ascending](), a())))\n  end",
    );
    assert_eq!(
        eval_str(&src, "wi844.merge.Driver.ab", "{1,3,5} u {2,3,4}"),
        "12345",
        "sorted, and the shared 3 appears ONCE — `123345` would mean the seam duplicated",
    );
    assert_eq!(
        eval_str(&src, "wi844.merge.Driver.ba", "the same union, operands swapped"),
        "12345",
        "a merge that dropped one side's tail passes one direction and fails the other",
    );
    assert_eq!(eval_str(&src, "wi844.merge.Driver.aEmpty", "x u {} = x"), "135");
    assert_eq!(eval_str(&src, "wi844.merge.Driver.emptyA", "{} u x = x"), "135");
}

/// THE WI-844 MECHANISM ITSELF, isolated: after ONE pinned construction, every
/// downstream call goes BRACKET-LESS. The choice is read out of the argument's type,
/// which is the whole content of "a named slot is a type parameter" (§4.7).
///
/// Measured before the fix, this exact program refused at the first `insert` with
/// *"constructing `Ordered[T = String]` is ambiguous among providers: String,
/// ByLength, Alphabetical"* — the argument's `O = ByLength` notwithstanding.
#[test]
fn the_ordering_is_read_from_the_argument_type_not_only_the_bracket() {
    let src = program(
        "wi844.read",
        &format!(
            "  sort Driver\n{FIRST}{}  end",
            string_pipeline("shortestFirst", "ByLength")
        ),
    );
    assert_eq!(
        eval_str(&src, "wi844.read.Driver.shortestFirst", "one pin, then no brackets"),
        "zz",
        "`zz` (2 chars) sorts before `aaa` (3) under ByLength — and the two `insert`s \
         and the `toList` carry no bracket at all",
    );
}

/// …AND EACH ORDERING IS ITS OWN ANSWER. Two sets over ONE carrier and ONE element
/// type, differing only in the bracket written at their CONSTRUCTION, fed to the same
/// bracket-less pipeline. One answer twice would mean the selection reached nothing.
#[test]
fn each_construction_site_selects_its_own_ordering() {
    let src = program(
        "wi844.thread",
        &format!(
            "  sort Driver\n{FIRST}{}{}  end",
            string_pipeline("byLength", "ByLength"),
            string_pipeline("alphabetical", "Alphabetical")
        ),
    );
    assert_eq!(
        eval_str(&src, "wi844.thread.Driver.byLength", "the length ordering, selected"),
        "zz",
    );
    assert_eq!(
        eval_str(&src, "wi844.thread.Driver.alphabetical", "the alphabetic ordering, selected"),
        "aaa",
        "the SAME body shape over the SAME two strings, differing only in the bracket \
         at `empty` — so `zz` twice would mean the construction-site selection decided \
         nothing",
    );
}

/// The discrimination control for the pair above, driven rather than assumed: SWAP the
/// two construction brackets and the two answers swap. Each answer is therefore
/// attributable to the bracket written at its own construction site, not to the order
/// of the declarations, the order of the `insert`s, or the entry name.
#[test]
fn swapping_the_construction_brackets_swaps_the_answers() {
    let src = program(
        "wi844.swap",
        &format!(
            "  sort Driver\n{FIRST}{}{}  end",
            string_pipeline("byLength", "Alphabetical"),
            string_pipeline("alphabetical", "ByLength")
        ),
    );
    // The entry NAMES are deliberately left as they were: only the brackets moved.
    assert_eq!(
        eval_str(&src, "wi844.swap.Driver.byLength", "the pin, swapped"),
        "aaa",
    );
    assert_eq!(
        eval_str(&src, "wi844.swap.Driver.alphabetical", "the pin, swapped"),
        "zz",
    );
}

/// THE SECOND σ PRODUCER: an ETA'd op reference. `attach_eta_dispatch_dict` pins the
/// op's parameters by unifying its eta arrow against the EXPECTED one, so an expected
/// arrow naming `O = ByLength` puts the witness in σ with no call and no bracket
/// anywhere. Found by review and measured: before the fix this exact program refused
/// with *"constructing `Ordered[T = String]` is ambiguous among providers"* — the
/// expected type's `O = ByLength` notwithstanding — because that site passed an empty
/// selection list on the (then-true, now half-true) grounds that "an eta carries no
/// call-site bracket".
///
/// Asserted by VALUE and in BOTH orderings, because "it loads" would also pass if the
/// pin were dropped and the search happened to answer.
#[test]
fn an_etad_op_takes_its_ordering_from_the_expected_arrow() {
    let src = program(
        "wi844.eta",
        &format!(
            "  import anthill.prelude.SortedSet.{{insert, empty, toList}}\n  \
             import anthill.prelude.Function\n  \
             sort Driver\n{FIRST}    \
             operation viaByLength(\n        \
             f: (SortedSet[T = String, O = ByLength], String) \
             -> SortedSet[T = String, O = ByLength]) -> String =\n      \
             first(toList(f(f(empty[T = String, O = ByLength](), \"zz\"), \"aaa\")))\n    \
             operation viaAlphabetical(\n        \
             f: (SortedSet[T = String, O = Alphabetical], String) \
             -> SortedSet[T = String, O = Alphabetical]) -> String =\n      \
             first(toList(f(f(empty[T = String, O = Alphabetical](), \"zz\"), \"aaa\")))\n    \
             operation byLength(n: Int64) -> String = viaByLength(insert)\n    \
             operation alphabetical(n: Int64) -> String = viaAlphabetical(insert)\n  end"
        ),
    );
    assert_eq!(eval_str(&src, "wi844.eta.Driver.byLength", "eta'd against a ByLength arrow"), "zz");
    assert_eq!(
        eval_str(&src, "wi844.eta.Driver.alphabetical", "eta'd against an Alphabetical arrow"),
        "aaa",
        "the SAME bare `insert` reference, differing only in the expected arrow's `O` — \
         so one answer twice would mean the eta's σ was not read",
    );
}

/// §7.1 — an ABSTRACT ordering parameter FORWARDS, it does not re-search. `Report` is
/// universally polymorphic in `O`: it can call through the order and can never name
/// which one it got. Both differently-ordered sets flow through the SAME body and each
/// keeps its own comparator, which is what "runtime choice = which statically pinned
/// branch executed" means in practice.
///
/// This is also the guard on the WI-844 read: an abstract slot must derive NO pin. Were
/// `is_type_param_value` dropped from `selections_from_slot_bindings`, the abstract `O`
/// would be read as a witness and universal polymorphism would become a wrong pin.
#[test]
fn an_abstract_ordering_parameter_forwards_the_callers_choice() {
    let src = program(
        "wi844.abstract",
        &format!(
            "  sort Report\n    \
             sort T = ?\n    \
             requires O: Ordered[T]\n    \
             operation first(s: SortedSet[T = T, O = O], dflt: T) -> T =\n      \
             match SortedSet.toList(s)\n        \
             case nil() -> dflt\n        \
             case cons(h, t) -> h\n  end\n  \
             sort Driver\n{FIRST}    \
             operation viaByLength(n: Int64) -> String =\n      \
             let a = SortedSet.empty[T = String, O = ByLength]()\n      \
             Report.first(SortedSet.insert(SortedSet.insert(a, \"zz\"), \"aaa\"), \"<none>\")\n    \
             operation viaAlphabetical(n: Int64) -> String =\n      \
             let b = SortedSet.empty[T = String, O = Alphabetical]()\n      \
             Report.first(SortedSet.insert(SortedSet.insert(b, \"zz\"), \"aaa\"), \"<none>\")\n  end"
        ),
    );
    assert_eq!(
        eval_str(&src, "wi844.abstract.Driver.viaByLength", "abstract O, ByLength argument"),
        "zz",
    );
    assert_eq!(
        eval_str(&src, "wi844.abstract.Driver.viaAlphabetical", "abstract O, Alphabetical argument"),
        "aaa",
        "ONE polymorphic body, two answers — the dictionary is forwarded from the \
         argument's type, not re-resolved against the carrier",
    );
}

/// TWO witnesses for ONE spec are REFUSED, not first-matched — and the refusal does not
/// care WHICH producer wrote each. An `InstanceSelection` is keyed by the SPEC, so a
/// sort with two same-spec named slots would pin one witness onto BOTH requirements if
/// the read took the first.
///
/// Three spellings, all refused with one message. The bracket-only one is WI-841's and
/// already worked. The type-only one is what WI-844's read made reachable: measured,
/// `Both.mk[T = String, A = ByLength, B = Alphabetical](…)` is refused at the bracket,
/// while the parameter ANNOTATION carrying the identical bindings LOADS.
///
/// THE MIXED ONE IS THE INTERESTING CASE, and a first cut got it wrong. That cut ranked
/// the producers — a derived witness colliding with a BRACKET-written one was exempted,
/// on the (true-for-one-slot, false-across-two) reasoning that they read one variable
/// and so cannot disagree. Measured: adding `[A = ByLength]` to the call DELETED the
/// refusal, leaving one pin serving both deps. Hence `[case_mixed]` below, and hence
/// `push_selection` compares unconditionally.
#[test]
fn two_witnesses_for_one_spec_are_refused_whoever_wrote_them() {
    let both = |ns: &str, call: &str| {
        program(
            ns,
            &format!(
                "  sort Both\n    \
                 sort T = ?\n    \
                 requires A: Ordered[T]\n    \
                 requires B: Ordered[T]\n    \
                 entity both(x: T)\n    \
                 operation cmp(s: Both[T = T, A = A, B = B], y: T) -> Int64 = \
                 Ordered.compare(y, y)\n  end\n  \
                 sort Take\n    \
                 operation take(s: Both[T = String, A = ByLength, B = Alphabetical]) \
                 -> Int64 =\n      {call}\n  end"
            ),
        )
    };
    // (namespace, the call, what wrote the two witnesses)
    let cases = [
        ("wi844.twoslot", "Both.cmp(s, \"q\")", "both read off the argument's TYPE"),
        (
            "wi844.twoslotmixed",
            "Both.cmp[A = ByLength](s, \"q\")",
            "MIXED: `A` written in the bracket, `B` read off the argument's type",
        ),
    ];
    for (ns, call, how) in cases {
        let errs = load_errs(&both(ns, call));
        assert!(
            errs.iter().any(|e| {
                e.contains("two providers are selected")
                    && e.contains(&format!("{ns}.Both.cmp"))
                    && e.contains(&format!("{ns}.ByLength"))
                    && e.contains(&format!("{ns}.Alphabetical"))
                    && e.contains("one spec, one witness per call")
            }),
            "{how}: two same-spec slots bound to two witnesses must be refused, naming \
             both: {errs:?}"
        );
    }
}

/// §4.7's scope statement, the accepting half: a signature that OMITS `O` erases the
/// distinction AT THAT BOUNDARY, deliberately. One `SortedSet[T = String]` parameter
/// takes both a `ByLength` and an `Alphabetical` set — this is how "I work for any
/// order" is written, and it is what keeps existing `SortedSet[T = …]` code loading.
#[test]
fn a_signature_omitting_the_ordering_accepts_both() {
    loads_clean(
        &program(
            "wi844.any",
            "  sort Any\n    \
             operation tag(s: SortedSet[T = String]) -> Int64 = 1\n  end\n  \
             sort Driver\n    \
             import anthill.prelude.Numeric.{add}\n    \
             operation both(n: Int64) -> Int64 =\n      \
             let a = SortedSet.empty[T = String, O = ByLength]()\n      \
             let b = SortedSet.empty[T = String, O = Alphabetical]()\n      \
             add(Any.tag(a), Any.tag(b))\n  end",
        ),
        "omission in TYPE position means ANY (058 §4.7), so ONE signature takes both \
         orderings — the merge safety is per-SIGNATURE, holding exactly where `O` is \
         written",
    );
}

/// …and the refusing half, which §4.7 does not state and this ticket measured: the
/// erasure is only free for a body that never DISPATCHES through the omitted slot. One
/// that does has no comparator to use, and says so — it does not pick.
///
/// The pair matters: "omitting is allowed" and "omitting is silently resolved" would
/// look identical from the accepting test alone.
#[test]
fn omitting_the_ordering_in_a_body_that_dispatches_is_loud() {
    let src = program(
        "wi844.underdetermined",
        "  sort Any\n    \
         operation size(s: SortedSet[T = String]) -> Int64 =\n      \
         SortedSet.toList(s).length()\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("anthill.prelude.Ordered[T = anthill.prelude.String]")
                && e.contains("ambiguous among providers")
                && e.contains("wi844.underdetermined.ByLength")
                && e.contains("wi844.underdetermined.Alphabetical")
        }),
        "a body that reads the order through an OMITTED slot is under-determined and \
         must name the candidates, never pick one: {errs:?}"
    );
}

/// §5.3's last paragraph — "omitting the binding keeps existing code working" — split
/// in two by what driving it found. It LOADS, and tier 2 resolves it: `SortedSet.empty
/// [T = Int64]()` names no ordering and the unique `Ordered[Int64]` provider answers,
/// which is the non-regression half and is what this asserts.
///
/// IT THEN DIES AT EVAL, on a defect that predates the whole arc and needs none of its
/// vocabulary — **WI-857**, pinned here (with its 058-free control below) so the
/// ticket has a live reproducer and so this file does not read as though the spelling
/// works. The producer of a requirement dictionary walks the PROVIDER's `requires`
/// chain (`candidate_sub_goals_owned`), the consumer names the frame's slots from the
/// SPEC's (`expand_dispatching_dict`); a carrier-keyed `fact Ordered[T = Int64]` has an
/// empty chain while `Ordered` itself declares two, so the dict arrives arity 0 where 2
/// are wanted. A WITNESS provider agrees by accident — dispatch then lands on the
/// witness's own member, whose parent chain is empty — which is why every other test in
/// this file runs.
///
/// "The same program you write today meaning the same thing" is therefore literally
/// true, and that is the point: today's spelling fails identically (see the control).
#[test]
fn omitting_the_ordering_is_resolved_but_dies_at_eval() {
    let src = program(
        "wi844.inferred",
        "  sort Driver\n    \
         operation smallest(n: Int64) -> Int64 =\n      \
         let a = SortedSet.empty[T = Int64]()\n      \
         match SortedSet.toList(SortedSet.insert(SortedSet.insert(a, 7), 3))\n        \
         case nil() -> -1\n        \
         case cons(h, t) -> h\n  end",
    );
    loads_clean(
        &src,
        "omission leaves `O` to inference and tier 2 answers with the unique \
         `Ordered[Int64]` provider — the LOAD half of §5.3's last paragraph",
    );
    eval_err(
        &src,
        "wi844.inferred.Driver.smallest",
        "has arity 0 but its requires chain has 2 entries",
        "WI-857: the inferred route dies at eval — flip this to `eval_int(…) == 3` when \
         that ticket lands",
    );
}

/// …and the control that keeps WI-857 out of 058's ledger: the identical failure with
/// no `SortedSet`, no named slot, no second provider and no bracket anywhere — a bare
/// `requires Eq[T]` sort calling `PartialEq.eq`. Beside it, the spec whose OWN chain is
/// empty (`PartialEq`) RUNS, which is what identifies the trigger as the spec's chain
/// depth rather than the shape.
#[test]
fn wi857_control_the_same_hole_with_no_058_vocabulary() {
    let src = program_with(
        "wi844.wi857",
        "", // no orderings: this has nothing to do with coexistence
        "  import anthill.prelude.{PartialEq, Eq}\n  \
         sort HolderPE\n    \
         sort T = ?\n    \
         requires PartialEq[T]\n    \
         operation same(a: T, b: T) -> Bool = PartialEq.eq(a, b)\n  end\n  \
         sort HolderEq\n    \
         sort T = ?\n    \
         requires Eq[T]\n    \
         operation same(a: T, b: T) -> Bool = PartialEq.eq(a, b)\n  end\n  \
         sort Driver\n    \
         operation viaPartialEq(n: Int64) -> Int64 =\n      \
         let b = HolderPE.same(7, 7)\n      1\n    \
         operation viaEq(n: Int64) -> Int64 =\n      \
         let b = HolderEq.same(7, 7)\n      1\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi844.wi857.Driver.viaPartialEq", "PartialEq has an EMPTY own chain"),
        1,
        "the control must PASS, else it proves nothing about what distinguishes the \
         failing case",
    );
    eval_err(
        &src,
        "wi844.wi857.Driver.viaEq",
        "bundles 0 sub-requirement(s)",
        "the 058-free twin of the failure above — `Eq` requires `PartialEq`, so its \
         dictionary wants one sub-entry and gets none; same producer/consumer \
         disagreement, one level shallower",
    );
}

/// The element type is untouched by all of this: a `String` set and an `Int64` set
/// coexist in one program, each with its own named comparator. Guards against a fix
/// that made the derived pin element-blind — the two slots would then cross-talk.
///
/// It also shows the driver is not a String curiosity: `Int64` already has a prelude
/// `Ordered` provider, so `Ascending` is a SECOND one for that carrier too, and the
/// bracket is what tells them apart.
#[test]
fn a_string_set_and_an_int_set_keep_their_own_orderings() {
    let src = program(
        "wi844.mixed",
        &format!(
            "  sort Ascending\n    \
             import anthill.prelude.Numeric.{{sub}}\n    \
             fact Ordered[T = Int64]\n    \
             operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)\n  end\n  \
             sort Descending\n    \
             import anthill.prelude.Numeric.{{sub}}\n    \
             fact Ordered[T = Int64]\n    \
             operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)\n  end\n  \
             sort Driver\n{FIRST}{}{}{}  end",
            string_pipeline("strings", "ByLength"),
            int_pipeline("ascending", "Ascending"),
            int_pipeline("descending", "Descending")
        ),
    );
    assert_eq!(eval_str(&src, "wi844.mixed.Driver.strings", "pinned String set"), "zz");
    assert_eq!(eval_int(&src, "wi844.mixed.Driver.ascending", "Int64, ascending"), 3);
    assert_eq!(
        eval_int(&src, "wi844.mixed.Driver.descending", "Int64, descending"),
        7,
        "the SAME two integers into the same pipeline — 3 twice would mean the \
         `Int64` orderings were not distinguished either",
    );
}

/// The SINGLE-PROVIDER control for the whole file: with `Alphabetical` deleted, the
/// pinned-then-bracket-less spelling still works. So nothing above is an artifact of
/// the two-provider configuration, and a program written against one ordering does not
/// change meaning when a second is declared elsewhere.
///
/// The OMITTED spelling is deliberately not exercised here: with one provider it is
/// `omitting_the_ordering_is_resolved_but_dies_at_eval`'s WI-857 case, which that test
/// owns.
#[test]
fn one_ordering_alone_behaves_the_same() {
    let src = program_with(
        "wi844.sole",
        BY_LENGTH,
        &format!("  sort Driver\n{FIRST}{}  end", string_pipeline("pinned", "ByLength")),
    );
    assert_eq!(
        eval_str(&src, "wi844.sole.Driver.pinned", "one witness beside the prelude's own"),
        "zz",
    );
}
