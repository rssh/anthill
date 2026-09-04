//! WI-900 — THE MINT GUARD AND THE NAME LADDER MUST AGREE on which names a rule head
//! may introduce. The rule lives in `docs/kernel-language.md` §"A rule-introduced
//! functor is scoped where it is written"; the mechanism is
//! `load::rule_head_ladder_answer`. This file drives the two edges of *denotes* —
//! an implicit name whose target is NOT loaded, and an ambiguous one.
//!
//! STDLIB LOADS: THREE, one per stdlib-bearing `#[test]` (~0.5s each). The per-claim
//! naming is what forces them; see `wi894_rule_functor_scope_test`'s header.

use crate::common::load_kb_bare;

/// THE TICKET'S OWN MEASUREMENT. `and` names nothing in this KB — no scope and no ladder
/// rung gives it a meaning — which makes each sort's head an INTRODUCTION, one per sort.
///
/// IT NO LONGER MEASURES THE TIER RUNG, and saying so is the point (WI-20260826-XED22,
/// raised by `/code-review`). `and` WAS an implicit-prelude name whose target
/// (`anthill.prelude.Bool.and`) was the only one of the 22 absent from a bare KB, which
/// is what made this fixture able to separate "the ladder consulted the tier and the tier
/// had no target" from "the name means nothing at all". `and` is not a tier entry now, so
/// this row exercises an ordinary unknown name and is indistinguishable from one spelled
/// `zzz`. It still measures WI-900's actual defect — two sorts' same-named heads must not
/// collapse onto one global — and that is why it is kept rather than retired. NO NAME
/// REMAINS that could restore the sharper reading: every surviving tier target is
/// pre-declared in Rust and so present even with no stdlib.
const TWO_SORTS_ONE_IMPLICIT_NAME: &str = r#"
namespace wi900.probe
  sort A
    fact pa900(1)
    rule and(?x) :- pa900(?x)
  end
  sort B
    fact pb900(2)
    rule and(?x) :- pb900(?x)
  end
end
"#;

/// The CLAUSES are what the assertion is about, not just the symbols: a merge shows up as
/// two sorts' rules hanging off ONE functor, and `A`'s law then answers inside `B`.
///
/// PRE-FIX (measured): neither qualified name exists and the bare global `and` carries
/// BOTH clauses — on a program that loads clean.
#[test]
fn a_stdlib_less_kb_does_not_collapse_two_sorts_onto_one_global() {
    let mut kb = load_kb_bare(&[TWO_SORTS_ONE_IMPLICIT_NAME]);
    for (qn, why) in [
        (
            "wi900.probe.A.and",
            "`and` means nothing in this KB, so A's head INTRODUCES it",
        ),
        (
            "wi900.probe.B.and",
            "…and B's head introduces B's own, distinct from A's",
        ),
    ] {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("`{qn}` must be a scoped symbol of its own sort: {why}"));
        assert_eq!(
            kb.rules_by_functor_iter(sym).count(),
            1,
            "`{qn}` must carry exactly its OWN sort's one clause",
        );
    }
    // The bare global is the fallback both spellings used to land on. Interning it here
    // cannot create clauses — it only names the symbol the collapse would have used.
    let bare = kb.intern("and");
    assert_eq!(
        kb.rules_by_functor_iter(bare).count(),
        0,
        "no clause may hang off the bare global `and` — that is the collapse itself",
    );
}

/// The same two sorts on `cons`, for the OTHER direction below. It cannot share
/// [`TWO_SORTS_ONE_IMPLICIT_NAME`] any more, and the reason is worth stating because it
/// is the whole content of WI-20260826-XED22: the two directions need OPPOSITE things of
/// the name, and after that ticket no single name gives both.
///
///   * the stdlib-less direction needs the tier target ABSENT from a bare KB;
///   * this direction needs the name to be a TIER ENTRY at all.
///
/// `anthill.prelude.Bool.and` was the only entry in the whole table satisfying the first
/// — MEASURED across all 22, every other target is pre-declared in Rust
/// (`register_stdlib_scopes` / `register_builtin_tag`) and so present even with no stdlib.
/// That is why the fixture above uses `and`, and it is why removing `and` from the tier
/// strands THIS direction rather than that one. `cons` is an ordinary surviving entry and
/// serves here: the rule is about the TIER, and the name was never the subject.
/// NO MEMBER IMPORT, DELIBERATELY -- the second fixture in this ticket to be broken by
/// WI-909's mechanical sweep, after `wi521_prelude_test`'s. The pass added
/// `import anthill.prelude.List.{cons}` here because the fixture writes `cons`; but this
/// fixture writes it precisely to observe what an UNIMPORTED head does, so the import
/// made the heads resolve and the row below assert the opposite of what it ran. A sweep
/// cannot distinguish a negative fixture from an unmigrated one; only reading can.
const TWO_SORTS_ONE_TIER_NAME: &str = r#"
namespace wi900.loaded
  sort A
    fact pa900(1)
    rule cons(?x) :- pa900(?x)
  end
  sort B
    fact pb900(2)
    rule cons(?x) :- pb900(?x)
  end
end
"#;

/// THE OTHER DIRECTION OF THE SAME RULE — INVERTED IN WI-909's third pass, which took
/// the last four rows (the constructors) off `PRELUDE_QUALIFIED` and left it empty.
///
/// The row used to say: when the implicit target IS loaded, the name already means
/// something, so the head REFERENCES it and introduces nothing (WI-530's decision, which
/// kept a `[simp]` law about `List.cons` a law about `List.cons`). That decision is
/// unchanged; what changed is its PREMISE. A rule head is RESOLVED, not declared
/// (WI-896), and resolution no longer has a rung below scope — so an unimported `cons`
/// head in `wi900.loaded.A` reaches nothing and MINTS `wi900.loaded.A.cons`, exactly as
/// `cut` / `unify` / `struct_eq` did when they left the tier before it.
///
/// Kept and inverted rather than deleted: "a bare tier name in a head is a reference"
/// was the rule this file established, and this is where a reader looks for it. The
/// stdlib's own laws about `List.cons` are unaffected — `list.anthill` is inside the
/// sort that declares it, where scope resolution answers.
#[test]
fn a_loaded_implicit_target_is_now_introduced_not_referenced() {
    let kb = crate::common::load_kb_with(TWO_SORTS_ONE_TIER_NAME);
    for qn in ["wi900.loaded.A.cons", "wi900.loaded.B.cons"] {
        assert!(
            kb.has_qualified_name(qn),
            "`{qn}` must be minted: `cons` is off the tier, so an unimported head \
             spelled that way introduces a scope-local name instead of adding a clause \
             to `anthill.prelude.List.cons`",
        );
    }
    assert!(
        kb.has_qualified_name("anthill.prelude.List.cons"),
        "control, and it still discriminates after the inversion: the target IS present, \
         so the heads above mint because `cons` is off the TIER — not because the stdlib \
         failed to load and there was nothing to reference either way",
    );
}

/// WHY THE DEFECT WAS INVISIBLE, pinned as the invariant it is — see
/// `load::implicit_target_orphans` for what an orphan costs. It is also the measurement
/// behind "the fix changes nothing in a stdlib-full KB": the static and the loaded
/// reading of the tier differ on exactly the absent targets, and there are none.
///
/// COVERS THE PRELUDE ALONE since WI-20260825-5W3RJ, and the other half did not weaken
/// — it stopped existing. The kernel desugaring vocab used to be 28 more addresses in
/// this same table; the converter now names each target outright
/// (`parse::desugar_target`), so there is no second list to fall out of agreement with
/// the declarations. `wi040_reserved_vocab_test` is where that half is measured now.
///
/// AND SINCE WI-909's THIRD PASS THIS ROW IS VACUOUS, said plainly rather than left for
/// a reader to discover: `PRELUDE_QUALIFIED` is EMPTY, so `implicit_target_orphans`
/// walks nothing and cannot report. It is kept, and kept green, because the invariant it
/// states is a property of the TABLE rather than of any entry — a future row added
/// without a declaration is exactly what it would catch. If the table and its accessors
/// are deleted outright (the dead-code follow-on WI-909 leaves open), this row goes with
/// them; it should not be repaired into asserting something else.
#[test]
fn every_implicit_target_is_declared_by_the_standard_load() {
    let kb = crate::common::load_kb_with("namespace wi900.empty\n  fact anchor900(1)\nend\n");
    let orphans = anthill_core::kb::load::implicit_target_orphans(&kb);
    assert!(
        orphans.is_empty(),
        "these implicit targets resolve to nothing — a bare reference to each falls to \
         the WI-476 bare intern, and a rule head spelled that way now INTRODUCES the \
         name instead of referencing it: {orphans:?}",
    );
}

/// THE AMBIGUOUS RUNG, pinned because the conflict must never be buried under a
/// scope-local that outranks the candidates.
///
/// IT IS NOW REACHED BY TWO ROUTES, and both are driven below (WI-20260822-845G7). When
/// the two wildcard-imported `amb900`s are DECLARED, the head DENOTES — ambiguously,
/// which is still denoting — so it references them and the ambiguity is reported at the
/// reference, §"the same ladder, to the rung" (WI-900). When they are only rule HEADS,
/// nothing is minted yet, so the head denotes nothing and would introduce a scope-local:
/// that is exactly the burial this row exists to prevent, and it is refused one step
/// earlier by the visibility rule, which names all three scopes.
///
/// BEFORE 845G7 only the second program existed here, and it reached the AMBIGUITY
/// message — through `Ownership`'s overlay, which made the head yield to one of the two
/// candidates and left the finished table ambiguous. That route is gone with the
/// fixpoint; the declared arm below is what keeps the ambiguity message measured.
#[test]
fn an_ambiguous_head_is_a_reference_so_the_load_is_refused() {
    const SRC: &str = r#"
namespace wi900.seed
  fact seed900(1)
end
namespace wi900.one
  rule amb900(?x) :- wi900.seed.seed900(?x)
end
namespace wi900.two
  rule amb900(?x) :- wi900.seed.seed900(?x)
end
namespace wi900.user
  import wi900.one.*
  import wi900.two.*
  rule amb900(?x) :- wi900.seed.seed900(?x)
end
"#;
    let Err(errs) = crate::common::try_load_kb_with(SRC) else {
        panic!(
            "two wildcard-imported `amb900`s must refuse the load — if this now loads, \
             the head was minted and the conflict was silently resolved in the author's \
             favour",
        );
    };
    assert!(
        errs.iter().any(|e| e.contains("amb900")
            && e.contains("introduces that name at 3 scopes, each of which reaches")),
        "undeclared, the three scopes all introduce `amb900` and can see each other, so \
         the visibility rule refuses before any of them can shadow the others; got \
         {errs:?}",
    );

    // DECLARED — and now the head DENOTES, ambiguously, so it is a REFERENCE and the
    // ambiguity is reported where §"the same ladder, to the rung" says it should be.
    // This is the arm that keeps the ambiguity message itself measured.
    let declared = SRC
        .replace(
            "namespace wi900.one\n  rule amb900",
            "namespace wi900.one\n  rule amb900(?x)\n  rule amb900",
        )
        .replace(
            "namespace wi900.two\n  rule amb900",
            "namespace wi900.two\n  rule amb900(?x)\n  rule amb900",
        );
    let Err(errs) = crate::common::try_load_kb_with(&declared) else {
        panic!("two declared `amb900`s wildcard-imported together must still be ambiguous")
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("ambiguous") && e.contains("amb900")),
        "the refusal must be the AMBIGUITY, named — any other error here means the head \
         resolved (or minted) and this fixture stopped testing its claim; got {errs:?}",
    );
}
