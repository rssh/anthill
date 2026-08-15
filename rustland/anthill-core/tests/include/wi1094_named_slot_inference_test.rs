//! WI-1094 (proposal 058 §3.4, §3.9; implementation notes §27) — **an omitted NAMED
//! requirement slot is inferred INTO THE TYPE, and an ERASED one is refused.**
//!
//! §3.4 has two halves and WI-861 delivered neither of them at a named slot. *"Omitting
//! a named slot in type position means ANY"* — the accepting half — was already true
//! (`wi844::a_signature_omitting_the_ordering_accepts_both`). *"Omitting it at a call
//! leaves it to inference (the ladder, §3.2)"* was not: rung 2a was deliberately WITHHELD
//! at a named slot, because a default fills a DICTIONARY and writes nothing into the
//! TYPE, and a value typed "any `O`" carrying a `Pair`-ordered dictionary is a mismatch,
//! not an answer.
//!
//! **ONE BINDING, THREE STATES — that is the whole mechanism.** A named slot IS a type
//! parameter, so what its binder resolves to at a call answers which half applies, and
//! every reader before this one asked a two-way question (`is_type_param_value`: abstract
//! or not):
//!
//!   * a still-FLEX variable — *nobody, at any site, has said*. `SortedSet.empty[T =
//!     Pair[…]]()` writes no `O` and no argument carries one, so this call CONSTRUCTS the
//!     value and the ladder answers. The answer is written into the BINDER, so it rides in
//!     the value's type and every later bracket-less call reads it back through σ as an
//!     ordinary tier-1 pin. That is what makes it COMPOSE, and it is what a
//!     dictionary-only default could not do.
//!   * a SKOLEM (a `Var::Rigid`, or the `s.O` projection a parameter's unwritten slot is
//!     filled with) — *the enclosing signature said ANY*. The value flowing in already
//!     chose; §3.9 leaves forwarding or refusal, and forwarding is unavailable by
//!     construction (a dictionary rides in a FRAME, never in a value). So: refused.
//!   * a witness sort — already decided, unchanged since WI-844.
//!
//! **THE REFUSAL IS COUNT-INDEPENDENT, AND THAT IS THE POINT OF `a_sole_provider_does_
//! not_excuse_the_erasure`.** Before this ticket the erasing shape was loud only when the
//! providers happened to TIE; with one provider it loaded clean and constructed silently
//! (WI-1094's own probe measurement). The tie was never the defect.
//!
//! **WHICH ARM MEASURES WHICH HALF**, so a back-out is attributable rather than a count.
//! Reverting the `Unspoken` bind fails `a_bracketless_set_takes_the_ladders_answer`,
//! `the_inferred_binding_is_in_the_type_not_just_the_dictionary`,
//! `two_inferred_sets_agree_and_merge`, `a_quantified_slot_the_caller_supplies_still_
//! forwards` (its second entry), `the_dot_spelling_reads_the_same_decision` and wi858's
//! headline — 6. Reverting the `Quantified` refusal fails
//! `an_erased_named_slot_is_refused_not_reconstructed`,
//! `a_sole_provider_does_not_excuse_the_erasure`,
//! `an_anonymous_caller_requirement_is_not_the_values_own_dictionary`,
//! `a_nested_frame_supply_does_not_excuse_the_erasure`,
//! `the_dot_spelling_reads_the_same_decision` and wi844's erased-slot arm — 6.
//! Reverting the DECLARED-binder skip (`param_rigids`) fails 1769 across 370 files:
//! §7.1's abstract form is everywhere and the stdlib itself stops loading.
//!
//! **AND WHICH PASS EITHER WAY BY DESIGN**: `positive_control_a_broken_program_is_refused`
//! (the harness check), `a_tie_the_ladder_cannot_break_is_still_reported` (the
//! pre-existing tier-3 refusal, which this ticket neither adds to nor removes — it is
//! here to say that inference CONSULTS the ladder rather than replacing it), and
//! `an_op_scoped_named_slot_keeps_its_own_reading` (which asserts a NON-change: both
//! spellings keep their pre-WI-1094 reading, and it fails only if the mechanism ever
//! widens past the sort level). `the_dot_spelling_reads_the_same_decision` moves with
//! whichever half is reverted, since it drives both.
//!
//! Reference: 058 §3.2, §3.4, §3.6, §3.9; `docs/design/058-implementation.md` §26, §27;
//! `wi858_pair_orderings_test` (the headline acceptance), `wi844_sorted_set_driver_test`
//! (the σ read this builds on), `stdlib/anthill/prelude/sortedset.anthill`.

use anthill_core::eval::Value;

/// TWO `Ord[Int64]` witnesses, declared separately so the single-provider control can
/// take one without a substring search into the other. They DISAGREE on `7` vs `3`,
/// which is what makes every value assertion below discriminating: ascending answers
/// `3`, descending `7`.
const DESCENDING: &str = r#"
  sort Descending
    import anthill.prelude.{Int64, Ord, WeakOrd}
    import anthill.prelude.Numeric.{sub}
    -- WI-1109: the WEAK floor. A chosen rival comparator is exactly what `WeakOrd` is
    -- for, and it is the floor `SortedSet`'s `O` slot names. Declaring `Ord[Int64]`
    -- here would ALSO put a second provider on the floor `Int64` itself occupies, so a
    -- bracket-less `Ord[Int64]` — which `Boxed requires Ord[BT]` below resolves — would
    -- be ambiguous between the carrier's own order and this rival.
    fact WeakOrd[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
"#;

const DOUBLED: &str = r#"
  sort Doubled
    import anthill.prelude.{Int64, Ord, WeakOrd}
    import anthill.prelude.Numeric.{sub}
    fact Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end
"#;

/// Read the first element of a set built by inserting `7` then `3`.
const HEAD: &str = r#"
    operation head(l: List[T = Int64]) -> Int64 =
      match l
        case nil() -> -1
        case cons(h, t) -> h
"#;

fn program(ns: &str, witnesses: &str, body: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         import anthill.prelude.{{Ord, WeakOrd, String, Int64, List, SortedSet}}\n\
         {witnesses}{body}\nend\n"
    )
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

/// Run `entry(0)` on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one, and `interp_for` panics on a dirty load, so a value assertion is also a
/// clean-load assertion.
fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}\n{src}"),
    }
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so every
/// clean-load assertion below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    load_errs(&program(
        "wi1094.control",
        DESCENDING,
        "  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    ));
}

// ── §3.4's second half: inference INTO THE TYPE ──────────────────────

/// THE MECHANISM, at its smallest. With TWO rival `Ord[Int64]` witnesses declared beside
/// the host's own, a bracket-less `SortedSet.empty[T = Int64]()` used to be a tier-3
/// refusal at the very next call. It now takes the ladder's answer — §3.6's inference
/// rule makes `Int64`'s own provision the default, so ascending — and the answer lands in
/// `s`'s TYPE, which is what carries it through the two bracket-less calls after it.
///
/// THE CONTROL IS THE SECOND ARM, and it is what separates "inferred" from "hard-wired":
/// the same pipeline with `O = Descending` written answers the other way. Without it this
/// test would pass on a tree that had simply stopped consulting the slot.
#[test]
fn a_bracketless_set_takes_the_ladders_answer() {
    let pipeline = |ns: &str, bracket: &str| {
        let src = program(
            ns,
            &format!("{DESCENDING}{DOUBLED}"),
            &format!(
                "  sort Driver\n{HEAD}    \
                 operation run(n: Int64) -> Int64 =\n      \
                 let s = SortedSet.empty[T = Int64{bracket}]()\n      \
                 head(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, 7), 3)))\n  end"
            ),
        );
        eval_int(&src, &format!("{ns}.Driver.run"), "the pipeline must run")
    };
    assert_eq!(
        pipeline("wi1094.infer", ""),
        3,
        "058 §3.4: an omitted named slot is left to inference, and §3.6 makes the \
         carrier's own provision the default — so silence takes `Int64`'s ascending \
         `Ord` even with two rivals declared. Before WI-1094 this did not load"
    );
    assert_eq!(
        pipeline("wi1094.infer.pinned", ", O = Descending"),
        7,
        "tier 1 outranks the inference: the SAME pipeline with the bracket written \
         answers descending"
    );
}

/// **THE COMPOSITION CLAIM, DRIVEN — this is why a dictionary-only default could not
/// have delivered the ticket.** The inference happens at ONE call (`empty`); the two
/// calls after it write no bracket and must read the choice back out of `s`'s type. If
/// the answer lived only in a dictionary, `insert` would face an unbound `O` again and
/// re-derive it independently — and a call that re-derives cannot disagree with itself
/// here, so the discriminating question is asked the other way round: does the
/// downstream call see a PIN?
///
/// It does, and the observable is that `union` — §3.4's merge check — now REFUSES to
/// merge the inferred set with a `Descending` one. Two differently-ordered sets have two
/// TYPES, and that check can only fire if the inferred `O` reached the type at all. A
/// value typed "any `O`" would merge silently, which is the exact mismatch WI-861 refused
/// to create.
#[test]
fn the_inferred_binding_is_in_the_type_not_just_the_dictionary() {
    let src = program(
        "wi1094.merge",
        &format!("{DESCENDING}{DOUBLED}"),
        "  sort Driver\n    \
         operation mixed(n: Int64) -> List[T = Int64] =\n      \
         let a = SortedSet.empty[T = Int64]()\n      \
         let b = SortedSet.empty[T = Int64, O = Descending]()\n      \
         SortedSet.toList(SortedSet.union(a, b))\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("expected SortedSet[T = Int64, O = Int64]")
                && e.contains("got SortedSet[T = Int64, O = Descending]")
        }),
        "the INFERRED `O` must be part of `a`'s type — the diagnostic names it as \
         `O = Int64`, the carrier's own provision — so merging it into a `Descending` \
         set is a type error naming both orderings. Had the inference only filled a \
         dictionary, `a` would be typed with an unbound `O`, both sets would be one \
         type, and this would load: {errs:?}"
    );
}

/// …and the same claim from the accepting side, so the arm above is not passing on a
/// `union` that refuses everything: two sets whose `O` was inferred the SAME way merge
/// fine, and the merged set is still ascending.
#[test]
fn two_inferred_sets_agree_and_merge() {
    let src = program(
        "wi1094.merge.ok",
        &format!("{DESCENDING}{DOUBLED}"),
        "  sort Driver\n\
         \x20   operation head(l: List[T = Int64]) -> Int64 =\n      \
         match l\n        \
         case nil() -> -1\n        \
         case cons(h, t) -> h\n    \
         operation run(n: Int64) -> Int64 =\n      \
         let a = SortedSet.insert(SortedSet.empty[T = Int64](), 7)\n      \
         let b = SortedSet.insert(SortedSet.empty[T = Int64](), 3)\n      \
         head(SortedSet.toList(SortedSet.union(a, b)))\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi1094.merge.ok.Driver.run", "the union must run"),
        3,
        "two independently-inferred sets take the same provider, so they have the SAME \
         type and merge — ascending, so `3` leads"
    );
}

// ── §3.9's half: the ERASED slot is refused ──────────────────────────

/// **THE `erase3` MEASUREMENT, as a refusal.** A `SortedSet[T = Int64, O = Descending]`
/// pushed through a signature that OMITS `O` used to have its dictionary rebuilt from
/// `Int64`'s own ascending `Ord` — measured at WI-861 as reading back `3` where the
/// slot-keeping route read `7`. The omission is not silence: §3.4 makes it mean ANY, so
/// the value flowing in already chose and its choice is not recoverable here.
///
/// §3.9 allows two answers — forward the value's own dictionary, or refuse — and
/// forwarding is unavailable BY CONSTRUCTION: a dictionary rides in a FRAME, never in a
/// value, so a signature that declares no slot for it has nothing to forward. Hence a
/// refusal, at the call inside the erasing body, naming the slot and the provider the
/// construction WOULD have taken.
///
/// The second arm is the control that keeps the first honest: the slot-KEEPING route
/// through the same two inserts runs and answers `7`, so what is refused is the erasure
/// and not the pipeline.
#[test]
fn an_erased_named_slot_is_refused_not_reconstructed() {
    let erasing = "  sort Any\n    \
                   operation add(s: SortedSet[T = Int64], x: Int64) -> SortedSet[T = Int64] =\n      \
                   SortedSet.insert(s, x)\n  end";
    let errs = load_errs(&program(
        "wi1094.erased",
        &format!("{DESCENDING}{DOUBLED}"),
        erasing,
    ));
    assert!(
        errs.iter().any(|e| {
            e.contains("universally quantified")
                && e.contains("`O: anthill.prelude.WeakOrd`")
                && e.contains("anthill.prelude.SortedSet.insert")
        }),
        "a signature that omits `O` and then dispatches through it must be refused at \
         that call — the value already chose and nothing here can recover the choice: \
         {errs:?}"
    );
    // THE CONTROL: the same two inserts with the slot KEPT read back descending.
    let kept = program(
        "wi1094.kept",
        &format!("{DESCENDING}{DOUBLED}"),
        &format!(
            "  sort Driver\n{HEAD}    \
             operation run(n: Int64) -> Int64 =\n      \
             let s = SortedSet.empty[T = Int64, O = Descending]()\n      \
             head(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, 7), 3)))\n  end"
        ),
    );
    assert_eq!(
        eval_int(&kept, "wi1094.kept.Driver.run", "the kept route must run"),
        7,
        "the slot-KEEPING route is what the erased one used to disagree with — WI-861 \
         measured 3 against this 7"
    );
}

/// **AND THE COUNT DOES NOT EXCUSE IT.** The identical erasing signature with exactly ONE
/// `Ord[Int64]` provider in scope (the host's own — no rival declared) LOADED CLEAN
/// before WI-1094 and built its dictionary silently. That is the same defect with the tie
/// removed: the refusal above is about the slot being universally quantified with no
/// dictionary in the frame, not about how many providers answer the goal.
///
/// This arm is the one that fails if the refusal is ever re-keyed on a candidate count.
#[test]
fn a_sole_provider_does_not_excuse_the_erasure() {
    let errs = load_errs(&program(
        "wi1094.sole",
        "",
        "  sort Any\n    \
         operation add(s: SortedSet[T = Int64], x: Int64) -> SortedSet[T = Int64] =\n      \
         SortedSet.insert(s, x)\n  end",
    ));
    assert!(
        errs.iter().any(|e| {
            e.contains("universally quantified") && e.contains("anthill.prelude.Int64")
        }),
        "with ONE provider the construction is right by luck, and the erasure is the \
         same defect — the refusal must name the provider it would have taken without \
         being conditional on there being two: {errs:?}"
    );
}

// ── The two things the refusal must NOT reach ────────────────────────

/// A QUANTIFIED slot WITH a dictionary in the frame is 058 §7.1's universally-polymorphic
/// form, and it must keep working: `Report` declares `requires O: Ord[T]`, so its `O` is
/// abstract at every call in its body AND the caller supplies the dictionary. The refusal
/// above must fire only where the frame supplies nothing.
///
/// Driven by VALUE and by DISAGREEMENT: one body, two differently-ordered sets, two
/// answers. One answer twice would mean the dictionary was re-derived rather than
/// forwarded — which is the very thing the refusal exists to stop, showing up as a wrong
/// number instead of a load error.
#[test]
fn a_quantified_slot_the_caller_supplies_still_forwards() {
    let src = program(
        "wi1094.forward",
        &format!("{DESCENDING}{DOUBLED}"),
        "  sort Report\n    \
         sort T = ?\n    \
         requires O: WeakOrd[T]\n    \
         operation first(s: SortedSet[T = T, O = O], dflt: T) -> T =\n      \
         match SortedSet.toList(s)\n        \
         case nil() -> dflt\n        \
         case cons(h, t) -> h\n  end\n  \
         sort Driver\n    \
         operation viaDesc(n: Int64) -> Int64 =\n      \
         let s = SortedSet.empty[T = Int64, O = Descending]()\n      \
         Report.first(SortedSet.insert(SortedSet.insert(s, 7), 3), -1)\n    \
         operation viaInferred(n: Int64) -> Int64 =\n      \
         let s = SortedSet.empty[T = Int64]()\n      \
         Report.first(SortedSet.insert(SortedSet.insert(s, 7), 3), -1)\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi1094.forward.Driver.viaDesc", "the pinned set"),
        7,
        "an abstract `O` FORWARDS the caller's dictionary — §7.1, and the refusal must \
         not reach it"
    );
    assert_eq!(
        eval_int(&src, "wi1094.forward.Driver.viaInferred", "the inferred set"),
        3,
        "…and the INFERRED choice travels through the same polymorphic body, so one \
         body answers two ways"
    );
}

/// The inference is a LADDER answer, not a construction that outranks the frame. Where
/// the caller's own named slot already supplies the goal, `resolve` answers `FromScope`,
/// which pins no impl — so nothing is written into the binder and the forward stands.
///
/// MEASURED BY DISAGREEMENT: `Wrap.build` constructs a `SortedSet[T = E]` with no bracket
/// inside a sort whose own `requires OE: Ord[E]` covers the goal. If the inference had
/// overridden the forward, both entries would answer with the carrier's own ascending
/// order; they answer differently, so each took its CALLER's choice.
#[test]
fn inference_does_not_override_a_dictionary_the_caller_supplies() {
    let src = program(
        "wi1094.frame",
        &format!("{DESCENDING}{DOUBLED}"),
        "  sort Wrap\n    \
         sort E = ?\n    \
         requires OE: WeakOrd[E]\n    \
         operation build(x: E, y: E) -> List[T = E] =\n      \
         SortedSet.toList(SortedSet.insert(SortedSet.insert(SortedSet.empty[T = E](), x), y))\n  \
         end\n  \
         sort Driver\n\
         \x20   operation head(l: List[T = Int64]) -> Int64 =\n      \
         match l\n        \
         case nil() -> -1\n        \
         case cons(h, t) -> h\n    \
         operation viaDesc(n: Int64) -> Int64 =\n      \
         head(Wrap.build[OE = Descending](7, 3))\n    \
         operation viaDoubled(n: Int64) -> Int64 =\n      \
         head(Wrap.build[OE = Doubled](7, 3))\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi1094.frame.Driver.viaDesc", "the descending caller"),
        7,
        "`SortedSet.empty[T = E]()` inside `Wrap` must FORWARD `Wrap`'s own `OE` slot, \
         not construct a rival — the ladder answers `FromScope` first and that pins no \
         impl"
    );
    assert_eq!(
        eval_int(&src, "wi1094.frame.Driver.viaDoubled", "the ascending caller"),
        3,
        "…and the OTHER caller gets the other order out of the SAME body, which is what \
         says the forward reached the construction site"
    );
}

// ── What the ladder still cannot answer ──────────────────────────────

/// A tie the ladder cannot break is still a tie. `Widget` provides `Ord` NOWHERE itself,
/// so §3.6's inference rule mints no default row for it and two witnesses leave rung 2a
/// with nothing to prefer. Nothing is written into the binder, and the refusal that
/// fires is the pre-existing dictionary-build one, naming both candidates and the
/// bracket to write.
///
/// The pair with `a_bracketless_set_takes_the_ladders_answer` is the point: inference
/// consults the ladder, it does not replace it — so "no answer" still means say which.
#[test]
fn a_tie_the_ladder_cannot_break_is_still_reported() {
    let src = program(
        "wi1094.tie",
        r#"
  sort Widget
    entity widget(v: Int64)
  end
  sort WidgetUp
    import anthill.prelude.{Int64, Ord, WeakOrd}
    import anthill.prelude.Numeric.{sub}
    import anthill.prelude.Widget.{widget}
    fact WeakOrd[T = Widget]
    operation compare(a: Widget, b: Widget) -> Int64 =
      match a
        case widget(x) ->
          match b
            case widget(y) -> sub(x, y)
  end
  sort WidgetDown
    import anthill.prelude.{Int64, Ord, WeakOrd}
    import anthill.prelude.Numeric.{sub}
    import anthill.prelude.Widget.{widget}
    fact WeakOrd[T = Widget]
    operation compare(a: Widget, b: Widget) -> Int64 =
      match a
        case widget(x) ->
          match b
            case widget(y) -> sub(y, x)
  end
"#,
        "  sort Driver\n    \
         operation run(n: Int64) -> List[T = Widget] =\n      \
         SortedSet.toList(SortedSet.empty[T = Widget]())\n  end",
    );
    let errs = load_errs(&src);
    assert!(
        errs.iter().any(|e| {
            e.contains("ambiguous among providers")
                && e.contains("wi1094.tie.WidgetUp")
                && e.contains("wi1094.tie.WidgetDown")
        }),
        "a carrier that provides nothing itself has no default, so the ladder answers \
         nothing and the tier-3 refusal stands — inference consults the ladder, it does \
         not replace it: {errs:?}"
    );
}


// ── "the frame supplies SOMETHING" is not "the value's own" ──────────

/// **THE SECOND FACE OF THE ERASURE, AND IT WAS A WRONG ANSWER RATHER THAN A REFUSAL.**
/// §3.9's lawful repair is "forward the value's own dictionary" — and a forward only
/// carries the VALUE's choice when the parameter's TYPE names the slot as one of this
/// signature's own declared parameters (`a_quantified_slot_the_caller_supplies_still_
/// forwards`). `Loose` does not: its `requires Ord[LT]` is ANONYMOUS, so it fixes nothing
/// about `s`'s type (§3.4 — an anonymous slot is a constraint, solved and recorded
/// nowhere), and forwarding it answers a constraint of `Loose`'s while the argument was
/// built with some other order.
///
/// MEASURED, on a first cut of this very ticket that gated the refusal on a provider
/// being CONSTRUCTIBLE: with `LT` abstract nothing can be constructed, so the gate
/// declined, the dictionary build forwarded `Loose`'s own `Ord[LT]`, and a `Descending`
/// set inserted into through this body read back **3** where its own order says **7**.
/// That is the `erase3` wrong answer reached through a forward instead of a search, which
/// is why the refusal is keyed on the SLOT being undeclared and not on what a rival would
/// have been.
///
/// The control below is the same body with the slot NAMED and written into the parameter
/// type — the one-word repair the diagnostic advertises — and it runs, answering the
/// value's own order.
#[test]
fn an_anonymous_caller_requirement_is_not_the_values_own_dictionary() {
    let errs = load_errs(&program(
        "wi1094.loose",
        DESCENDING,
        "  sort Loose\n    \
         sort LT = ?\n    \
         requires WeakOrd[LT]\n    \
         operation addAndCount(s: SortedSet[T = LT], x: LT) -> Int64 =\n      \
         SortedSet.toList(SortedSet.insert(s, x)).length()\n  end",
    ));
    assert!(
        errs.iter().any(|e| {
            e.contains("universally quantified")
                && e.contains("`O: anthill.prelude.WeakOrd`")
                && e.contains("anthill.prelude.SortedSet.insert")
        }),
        "an ANONYMOUS caller requirement records nothing about the argument's type, so \
         forwarding it answers for the signature and not for the value: {errs:?}"
    );
    // THE CONTROL, and it is the repair the message names: NAME the slot and WRITE it in
    // the parameter's type. Now the forward is the value's own, and the body reads the
    // order the construction site chose.
    let named = program(
        "wi1094.loose.named",
        DESCENDING,
        "  sort Tight\n    \
         sort LT = ?\n    \
         requires LO: WeakOrd[LT]\n    \
         operation addAndHead(s: SortedSet[T = LT, O = LO], x: LT, dflt: LT) -> LT =\n      \
         match SortedSet.toList(SortedSet.insert(s, x))\n        \
         case nil() -> dflt\n        \
         case cons(h, t) -> h\n  end\n  \
         sort Driver\n    \
         operation run(n: Int64) -> Int64 =\n      \
         let s = SortedSet.empty[T = Int64, O = Descending]()\n      \
         Tight.addAndHead(SortedSet.insert(s, 7), 3, -1)\n  end",
    );
    assert_eq!(
        eval_int(&named, "wi1094.loose.named.Driver.run", "the named-slot repair"),
        7,
        "with the slot NAMED and written into the parameter's type, the forward carries \
         the set's OWN descending order — inserting 3 into [7] keeps 7 in front. This is \
         the number the anonymous spelling got wrong (it answered 3)"
    );
}

/// …and neither is a dictionary the frame carries NESTED inside some other slot. `User`
/// requires `Boxed[BT = Int64]`, whose own `requires Ord[BT]` bundles an `Ord[Int64]` the
/// dictionary build's Strategy 2 will happily project — but it is `Boxed`'s evidence,
/// chosen wherever `User` was instantiated, and it has nothing to do with the order `s`
/// was built with.
///
/// This arm and the one above are the same rule seen at the two places a frame can answer
/// a goal without answering FOR THIS VALUE, which is why the refusal asks whether the
/// BINDER was declared rather than whether the frame has anything to offer. An early cut
/// consulted the frame first and let both through.
///
/// The second arm is the control that keeps this from being "any use of `Boxed` refuses":
/// a CONSTRUCTION in the very same frame still infers and runs.
#[test]
fn a_nested_frame_supply_does_not_excuse_the_erasure() {
    let boxed = "  sort Boxed\n    \
                 sort BT = ?\n    \
                 requires Ord[BT]\n    \
                 operation tag(x: BT) -> Int64 = 0\n  end\n  \
                 sort BoxedInt\n    \
                 fact Boxed[BT = Int64]\n    \
                 operation tag(x: Int64) -> Int64 = 1\n  end\n";
    let errs = load_errs(&program(
        "wi1094.nested",
        DESCENDING,
        &format!(
            "{boxed}  sort User\n    \
             requires Boxed[BT = Int64]\n    \
             operation size(s: SortedSet[T = Int64]) -> Int64 =\n      \
             SortedSet.toList(s).length()\n  end"
        ),
    ));
    assert!(
        errs.iter().any(|e| {
            e.contains("universally quantified") && e.contains("anthill.prelude.SortedSet.toList")
        }),
        "a nested `Ord[Int64]` bundled inside the frame's `Boxed` slot is `Boxed`'s \
         evidence, not the argument's order — Strategy 2 would project it silently: \
         {errs:?}"
    );
    // THE CONTROL: the same frame, a CONSTRUCTION instead of an erasure. Nothing about
    // holding a `Boxed` slot stops a bracket-less `empty` from inferring.
    let built = program(
        "wi1094.nested.built",
        DESCENDING,
        &format!(
            "{boxed}  sort User\n{HEAD}    \
             requires Boxed[BT = Int64]\n    \
             operation run(n: Int64) -> Int64 =\n      \
             let s = SortedSet.empty[T = Int64]()\n      \
             head(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, 7), 3)))\n  end\n  \
             sort Driver\n    \
             operation go(n: Int64) -> Int64 = User.run(0)\n  end"
        ),
    );
    assert_eq!(
        eval_int(&built, "wi1094.nested.built.Driver.go", "the construction control"),
        3,
        "a construction site in the same frame still takes the ladder's answer — the \
         refusal is about the slot being undeclared, not about the frame being non-empty"
    );
}

// ── one decision, two spellings ──────────────────────────────────────

/// **THE DOT READS THE SAME DECISION AS THE QUALIFIED CALL, both halves.** A dot is a
/// dispatch decision reached by its own path (WI-1035/1038/1039), and "one program, two
/// spellings, two answers" is the defect that arc exists to close — so this asks the
/// question rather than assuming the paths converged.
///
/// Both arms are the file's own programs re-spelled and nothing else: the inference
/// pipeline through `s.insert(7).insert(3).toList()` must give the same `3`
/// `a_bracketless_set_takes_the_ladders_answer` gets, and the erasure through
/// `s.toList()` must give the same refusal `an_erased_named_slot_is_refused_not_
/// reconstructed` gets. A silent divergence here would be a bracket-less pipeline that
/// computes one order written one way and another written the other.
#[test]
fn the_dot_spelling_reads_the_same_decision() {
    let inferred = program(
        "wi1094.dot",
        &format!("{DESCENDING}{DOUBLED}"),
        &format!(
            "  sort Driver\n{HEAD}    \
             operation run(n: Int64) -> Int64 =\n      \
             let s = SortedSet.empty[T = Int64]()\n      \
             head(s.insert(7).insert(3).toList())\n  end"
        ),
    );
    assert_eq!(
        eval_int(&inferred, "wi1094.dot.Driver.run", "the dotted pipeline"),
        3,
        "the inferred `O` rides in `s`'s type, so the DOT spelling reads it back exactly \
         as the qualified one does"
    );
    let errs = load_errs(&program(
        "wi1094.dot.erased",
        &format!("{DESCENDING}{DOUBLED}"),
        "  sort Any\n    \
         operation size(s: SortedSet[T = Int64]) -> Int64 = s.toList().length()\n  end",
    ));
    assert!(
        errs.iter().any(|e| {
            e.contains("universally quantified") && e.contains("anthill.prelude.SortedSet.toList")
        }),
        "…and the erasure is refused through the dot too — a spelling that escaped it \
         would be a silent wrong order for one of the two ways to write the call: {errs:?}"
    );
}

// ── the boundary of the mechanism ────────────────────────────────────

/// **AN OP-SCOPED NAMED SLOT IS OUT OF SCOPE FOR THE INFERENCE, and the exclusion is
/// pinned rather than left to the absence of a test.** This mechanism writes into a type
/// PARAMETER so the answer rides in a VALUE's type; 058 §3.9 says an op-scoped
/// requirement is "evidence about THIS CALL of THIS OPERATION, belonging to no
/// instance", so there is no value to carry it. Omitting the binder is therefore still
/// `UnconstrainedTypeParam` — an inference that had fired would have bound it from
/// `Widget`'s own provision and the program would load.
///
/// **THE SECOND HALF MOVED AT WI-1091, and the correction matters more than the row.**
/// This doc used to add: "WI-841 agrees from the other side: that route is served by
/// value-directed dispatch, which never sees a selection, so a bracket there is refused
/// outright once two providers answer" — and concluded that refusing the WRITTEN binder
/// is "WHY inferring it would buy nothing: the route cannot carry the answer to the
/// body". The premise was true when written and is now false. WI-1091 widened the
/// op-scoped placement, so a body call licensed by its enclosing operation's own
/// `requires` READS that dictionary, and the call-site supply has honoured the bracket
/// since WI-822 LEG 1. A written `[d = LoudDesc]` now DECIDES — 99, `LoudDesc`'s answer,
/// against the 1 that `Widget`'s own provision gives by default.
///
/// So the two halves no longer share a reason, and that is the honest reading: the route
/// CAN carry a selection, and this ticket still declines to INFER one because a type
/// parameter is the wrong place to put evidence that belongs to no instance. Which is a
/// narrower claim than the one this row used to make, and the one it can support.
///
/// The tie here is DEFAULT-ABLE on purpose — `Widget` provides `Desc` itself, so §3.6
/// mints a default row and the ladder WOULD have had an answer to give. Without that,
/// "nothing was inferred" would be indistinguishable from "there was nothing to infer";
/// it is also what makes 1-vs-99 name WHICH provider the bracket chose.
#[test]
fn an_op_scoped_named_slot_keeps_its_own_reading() {
    let fixtures = r#"
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Widget
    entity widget(v: Int64)
    provides Desc[T = Widget]
    operation describe(x: Widget) -> Int64 = 1
  end
  sort LoudDesc
    import anthill.prelude.{Int64}
    fact Desc[T = Widget]
    operation describe(x: Widget) -> Int64 = 99
  end
  sort Holder
    operation probe(x: Widget) -> Int64 requires d: Desc[T = Widget] = Desc.describe(x)
  end
"#;
    let driver = |ns: &str, bracket: &str| {
        program(
            ns,
            fixtures,
            &format!(
                "  sort Driver\n    \
                 import {ns}.Widget.{{widget}}\n    \
                 operation run(n: Int64) -> Int64 = Holder.probe{bracket}(widget(v: 5))\n  end"
            ),
        )
    };
    let bare = load_errs(&driver("wi1094.opslot.bare", ""));
    assert!(
        bare.iter()
            .any(|e| e.contains("unconstrained") && e.contains("'d'")),
        "an omitted op-scoped binder keeps `UnconstrainedTypeParam` — had the inference \
         reached it, the default (`Widget`'s own provision) would have bound it and this \
         would load: {bare:?}"
    );
    // …and WRITING it now DECIDES (WI-1091). Driven to the VALUE, not to a load verdict:
    // `LoudDesc`'s 99 against the 1 `Widget`'s own provision gives by default, so a
    // bracket that were accepted and dropped — WI-841's measured defect — would show as
    // the default's number rather than as an error.
    let mut interp = crate::common::interp_for(&driver("wi1094.opslot.pinned", "[d = LoudDesc]"));
    let got = interp.call("wi1094.opslot.pinned.Driver.run", &[Value::Int(0)]);
    assert!(
        matches!(got, Ok(Value::Int(99))),
        "the written binder must select `LoudDesc` — a 1 is `Widget`'s own provision, \
         i.e. the bracket accepted and dropped; got {got:?}"
    );
}

/// **THE INDEX DRIFT A FIRST CUT WALKED INTO, found by `/code-review` and pinned so it
/// cannot come back with the branch.** An op-scoped `requires` list is OVERLOADED
/// (WI-840): one comma list carries both spec requirements and VALUE preconditions
/// (WI-539). `NamedRequirementSlot::slot` counts over the WHOLE flattened list while the
/// dictionary chain is built with preconditions FILTERED OUT — so a precondition written
/// before the binder puts the two indexings one apart.
///
/// The first cut of this ticket decoded op-scoped slots and reported the internal
/// `SlotSelectionUnindexable` here instead of the author-facing
/// `UnconstrainedTypeParam` — and the review's note is the part worth keeping: a
/// SAME-SPEC variant would have passed the `same_sort_canonical` guard and silently
/// returned the WRONG GOAL. Skipping op-scoped slots wholesale is what removes the
/// question; this arm is the reason not to re-open it without the offset.
#[test]
fn a_value_precondition_before_an_op_scoped_binder_keeps_its_own_diagnostic() {
    let errs = load_errs(&program(
        "wi1094.precond",
        "",
        "  sort Holder\n    \
         import anthill.prelude.PartialEq.{neq}\n    \
         operation pick(a: Int64, b: Int64) -> Int64\n      \
         requires neq(a, 0), lo: WeakOrd[T = Int64]\n    \
         = WeakOrd.compare(a, b)\n  end\n  \
         sort Driver\n    \
         operation run(n: Int64) -> Int64 = Holder.pick(7, 3)\n  end",
    ));
    assert!(
        errs.iter()
            .any(|e| e.contains("unconstrained") && e.contains("'lo'")),
        "the author-facing diagnostic, not the internal `could not be established` one: \
         a precondition ahead of the binder offsets the two indexings, and this ticket's \
         answer is to not read that chain at all: {errs:?}"
    );
}
