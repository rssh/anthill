//! WI-776 — a one-column COMPUTED schema 1-collapses to its element type, and the mismatch
//! against a WRITTEN one-component tuple now NAMES that collapse.
//!
//! THE TICKET WAS A DECISION, and this is the "explain it" branch: the two sides are NOT
//! made to agree.
//!
//! WHY NOT — and the first version of this header got this WRONG, worth recording because
//! the wrong reason also reached the SPEC before a reviewer caught it. The rejected claim
//! was that a one-column schema keeping its column would be UNCONSTRUCTIBLE. It would not:
//! §4.5 says a one-component tuple type's inhabitants arrive by WIDTH SUBTYPING from a
//! wider tuple, and `narrow() -> (a: Int64) = wide()` over `wide() -> (a: Int64, b: String)`
//! loads clean today (asserted below, with a live negative control). The value side is just
//! as capable — `materialize_solution` builds the row as `(name, value)` pairs and then
//! throws the name away at arity one.
//!
//! The REAL reason is that the collapse is a PAIRED type-and-value convention whose value
//! half §6.8 fixes at the TERM level (`x.(f)` -> `x.f`; a single RENAME `rel.(years: age)`
//! collapses and drops the label, WI-639; `rel.name : Relation[String]`). Keeping the column
//! in the SCHEMA alone desynchronizes type from term across projection, relation drain and
//! `Without`/`Project`. That is a breaking change to a specified rule — a cost, not an
//! impossibility.
//!
//! WHAT THE NOTE HAS TO SAY: `(a: A)` is not a broken spelling of `A`, it is a real type
//! matching any tuple whose `a` column CONFORMS to `A` (§4.5's width rule is `S_n <: T_n` —
//! "has a column named `a`" alone is not enough, and the code gates on exactly this). It
//! must NOT be called an input-position type: width subtyping is general, and the note fires
//! at op-ARG positions too, where that phrasing contradicts itself.
//!
//! Owned in `render_mismatch_pair` (kb/typing.rs) as a second CAUSE beside WI-795's arity
//! qualification, for the same reason that one exists: the PAIR says something neither side
//! does. `expected (a: Int64), got Int64` is true, and useless — both types are right, they
//! are the two sides of a collapse the reader cannot see.

use crate::common::try_load_kb_with;

fn load_errs(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

/// The note, keyed on the two things it must get RIGHT: the label it tells the author to
/// drop, and the element type it tells them to write instead. Asserting only "some note
/// appeared" would pass on a note naming the wrong column — which is the whole failure mode
/// for the NESTED case below, where the outer type is not the one at fault.
fn assert_collapse_note(src: &str, label: &str, elem: &str) {
    let errs = load_errs(src);
    assert!(!errs.is_empty(), "expected a type mismatch, but it loaded clean:\n{src}");
    let joined = errs.join("\n");
    assert!(
        joined.contains("1-collapses to its element type"),
        "expected the mismatch to NAME the 1-collapse; got:\n{joined}"
    );
    assert!(
        joined.contains(&format!("never `({label}: {elem})`"))
            && joined.contains(&format!("write `{elem}` here")),
        "the note must name the dropped label `{label}` and the element type `{elem}`; \
         got:\n{joined}"
    );
}

fn assert_no_collapse_note(src: &str) {
    let joined = load_errs(src).join("\n");
    assert!(!joined.is_empty(), "expected a type mismatch, but it loaded clean:\n{src}");
    assert!(
        !joined.contains("1-collapses to its element type"),
        "the 1-collapse note must NOT fire here; got:\n{joined}"
    );
}

const REL: &str = r#"
  import anthill.prelude.{String, Int64, Relation, Project}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)
"#;

// ── The three cases the ticket MEASURED ────────────────────────────────────────────

#[test]
fn without_residual_of_one_column_names_the_collapse() {
    assert_collapse_note(
        "namespace test.w776a\n  import anthill.prelude.{String, Int64, Without}\n  \
         operation resid() -> Without[T = (a: Int64, b: String), Drop = (b: String)]\n  \
         operation as_tuple() -> (a: Int64) = resid()\nend\n",
        "a",
        "Int64",
    );
}

#[test]
fn one_entry_project_keep_spec_names_the_collapse() {
    assert_collapse_note(
        &format!(
            "namespace test.w776p\n{REL}\n  \
             operation kept(r: Relation[T = (name: String, age: Int64)])\n    \
             -> Project[T = (name: String, age: Int64), Keep = (who: \"name\")]\n  \
             operation use_kept(r: Relation[T = (name: String, age: Int64)]) \
             -> (who: String) = kept(r)\nend\n"
        ),
        "who",
        "String",
    );
}

/// The NESTED case, and the reason the detector descends through type ARGUMENTS at all.
/// `expected Relation[T = (name: String)], got Relation[T = String, E = {…}]` — the fault is
/// one level in, so the note must name `name`/`String` (the T argument), NOT the whole
/// `Relation[…]` on either side.
///
/// Two things had to be right for this to fire, both measured rather than assumed. The `E`
/// argument is present on the actual side only and is NOT part of the fault — the same
/// source with `Relation[T = String]` loads clean — so arguments missing from one side are
/// skipped rather than counted as a difference. And the two `T` keys are DIFFERENT
/// `Symbol`s that both resolve to "T" (WI-708 dual-keying, bare vs op-scoped), so the
/// arguments align by `same_label`, not by symbol identity; an identity compare silently
/// found no shared argument and dropped the note on exactly this case.
#[test]
fn collapse_inside_a_type_argument_names_the_inner_column() {
    assert_collapse_note(
        &format!(
            "namespace test.w776r\n{REL}\n  \
             rule adult(?name) :- person(name: ?name, age: ?a)\n  \
             operation who() -> Relation[T = (name: String)] = adult\nend\n"
        ),
        "name",
        "String",
    );
}

// ── The collapse itself is UNCHANGED — this branch explains, it does not fix ────────

#[test]
fn the_collapsed_spelling_still_loads_clean() {
    // The decision was to KEEP the collapse, so the element spelling the note recommends
    // must actually be the one that works. Without this, the note could be recommending a
    // type that also fails, and every test above would still pass.
    assert!(
        load_errs(
            "namespace test.w776ok\n  import anthill.prelude.{String, Int64, Without}\n  \
             operation resid() -> Without[T = (a: Int64, b: String), Drop = (b: String)]\n  \
             operation as_scalar() -> Int64 = resid()\nend\n"
        )
        .is_empty(),
        "the element spelling the note recommends must load clean"
    );
    // And the same at the nested site.
    assert!(
        load_errs(&format!(
            "namespace test.w776okr\n{REL}\n  \
             rule adult(?name) :- person(name: ?name, age: ?a)\n  \
             operation who() -> Relation[T = String] = adult\nend\n"
        ))
        .is_empty(),
        "`Relation[T = String]` must load clean against the collapsed schema"
    );
}

/// The counter-example to the reason this ticket was ALMOST decided on. A one-component
/// tuple type is INHABITED — §4.5's width subtyping supplies it from a wider tuple — and in
/// a RETURN position, not merely an argument one. Asserted because the first version of this
/// work claimed the opposite ("a type no term can construct") and wrote that into the spec;
/// this test is what makes the claim checkable instead of rhetorical.
///
/// So the decision does NOT rest on impossibility. It rests on the collapse being a paired
/// type-and-value convention that §6.8 fixes at the term level.
#[test]
fn a_one_component_tuple_type_is_inhabited_by_width_subtyping() {
    assert!(
        load_errs(
            "namespace test.w776w\n  import anthill.prelude.{String, Int64}\n  \
             operation wide() -> (a: Int64, b: String) = (a: 1, b: \"x\")\n  \
             operation narrow() -> (a: Int64) = wide()\nend\n"
        )
        .is_empty(),
        "a wider tuple must conform to `(a: Int64)` in a RETURN position"
    );
    // Live negative control: without this, the assertion above would also pass if the
    // op-return check were simply not running on these declarations.
    let errs = load_errs(
        "namespace test.w776w2\n  import anthill.prelude.{String, Int64}\n  \
         operation wide2() -> (a: Int64, b: String) = (a: 1, b: \"x\")\n  \
         operation narrow2() -> (a: String) = wide2()\nend\n",
    );
    assert!(
        errs.join("\n").contains("expected (a: String)"),
        "width subtyping must still require the column to CONFORM, not merely exist; \
         got: {errs:?}"
    );
}

// ── Over-firing controls ───────────────────────────────────────────────────────────

#[test]
fn an_unrelated_mismatch_gets_no_note() {
    assert_no_collapse_note(
        "namespace test.w776n\n  import anthill.prelude.{String, Int64}\n  \
         operation f() -> Int64 = \"hello\"\nend\n",
    );
}

#[test]
fn a_one_tuple_whose_element_does_not_match_gets_no_note() {
    // THE load-bearing control. The note claims "you wrote the 1-tuple of exactly this
    // type" — so it must be gated on the component matching the actual, not merely on the
    // expected side being a 1-tuple. Here `(a: Int64)` meets `String`: a real mismatch that
    // the collapse does not explain, and telling the author to "write `Int64`" would be
    // actively wrong.
    assert_no_collapse_note(
        "namespace test.w776n2\n  import anthill.prelude.{String, Int64}\n  \
         operation g() -> (a: Int64) = \"hello\"\nend\n",
    );
}

/// The note fires on a SHAPE, and the shape occurs without any schema — so the wording must
/// not assert a collapse happened. `= 42` has no projection, no `Without`, no relation
/// anywhere, yet expected `(a: Int64)` against actual `Int64` is exactly the pair.
///
/// The advice is still right here (`write Int64`), which is why the note is kept rather than
/// gated on provenance; what was wrong was stating a cause as fact. The first version opened
/// "a one-column schema 1-collapses…" as an assertion about THIS program.
#[test]
fn the_note_states_a_shape_not_an_unproven_cause() {
    let joined = load_errs(
        "namespace test.w776lit\n  import anthill.prelude.{Int64}\n  \
         operation g() -> (a: Int64) = 42\nend\n",
    )
    .join("\n");
    assert!(
        joined.contains("the expected type is a ONE-COMPONENT tuple"),
        "the note must lead with the shape it actually tested; got:\n{joined}"
    );
    assert!(
        joined.contains("usual source of this pair"),
        "the collapse must be offered as the USUAL cause, not asserted of a program with no \
         schema in it; got:\n{joined}"
    );
}

/// A fix that does not fix is worse than no note. When a second type ARGUMENT also differs,
/// correcting the collapse leaves the program broken — measured: `Vec[T = (a: Int64), N = 4]`
/// against `Vec[T = Int64, N = 3]` named the `T` fix, and applying it verbatim still failed
/// on `N`. So the note withdraws unless the collapse is the ONLY fault.
#[test]
fn a_second_differing_type_argument_withdraws_the_note() {
    assert_no_collapse_note(
        "namespace test.w776multi\n  import anthill.prelude.{Int64, String}\n  \
         sort Vec\n    sort T = ?\n    sort N = ?\n  end\n  \
         operation mk() -> Vec[T = Int64, N = 3]\n  \
         operation use() -> Vec[T = (a: Int64), N = 4] = mk()\nend\n",
    );
    // Control: the SAME shape with the other argument agreeing still gets the note, so the
    // gate above narrows the note rather than disabling the parameterized path wholesale.
    assert_collapse_note(
        "namespace test.w776multi2\n  import anthill.prelude.{Int64, String}\n  \
         sort Vec2\n    sort T = ?\n    sort N = ?\n  end\n  \
         operation mk2() -> Vec2[T = Int64, N = 3]\n  \
         operation use2() -> Vec2[T = (a: Int64), N = 3] = mk2()\nend\n",
        "a",
        "Int64",
    );
}

// ── The gap this branch does NOT close, pinned so it is not believed fixed ──────────

/// `Concat` and `Without` are still not inverses at arity one, and no diagnostic can make
/// them so: the collapse DESTROYS the column name, and at the `Concat` site nothing
/// supplies it — there is no expectation to recover `a` from. Measured, the type stalls
/// UNREDUCED as `Concat[A = Int64, B = (c: Bool)]`.
///
/// Asserted rather than left implicit so the limitation stays visible: WI-776 explains the
/// collapse at a mismatch, it does not close the type-level algebra. If a later change ever
/// makes this reduce, this test fails and someone re-reads the decision.
#[test]
fn concat_over_a_collapsed_without_still_stalls() {
    let errs = load_errs(
        "namespace test.w776e\n  \
         import anthill.prelude.{String, Int64, Bool, Concat, Without}\n  \
         operation roundtrip() -> Concat[A = Without[T = (a: Int64, b: String), \
         Drop = (b: String)], B = (c: Bool)]\n  \
         operation use_it() -> (a: Int64, c: Bool) = roundtrip()\nend\n",
    );
    let joined = errs.join("\n");
    assert!(
        joined.contains("Concat[A = Int64"),
        "the arity-1 residual must still reach Concat COLLAPSED (label destroyed), leaving \
         it unreduced; got:\n{joined}"
    );
    // Control on the same shape: at arity >= 2 nothing collapses and the residual is usable.
    assert!(
        load_errs(
            "namespace test.w776e2\n  \
             import anthill.prelude.{String, Int64, Bool, Without}\n  \
             operation resid2() -> Without[T = (a: Int64, b: String, z: Bool), \
             Drop = (z: Bool)]\n  \
             operation use2() -> (a: Int64, b: String) = resid2()\nend\n"
        )
        .is_empty(),
        "a 2-column residual must still load clean — the defect is specific to arity one"
    );
}
