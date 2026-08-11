//! WI-999 — proposal 059 R4 CLAUSE 3: a declaration in a sort scope may not
//! CAPTURE a short name that already resolves there.
//!
//! THE HAZARD. A name can already mean something in a sort's scope without being a
//! member of it. 059 measured a main-entry body calling a bare `f(…)` that resolved
//! through `import lib.f` and answered `1`; adding a declaration of `f` to the shared
//! sort scope made the SAME UNEDITED BODY answer `2`. Clause 1 (WI-1049) is keyed on
//! two declarations colliding and cannot see this, because nothing named `f` was ever
//! a member. Every row below drives the base VALUE first, because "it loads clean" is
//! exactly what the hazard does.
//!
//! OVER THE WHOLE SORT SCOPE, not over secondary entries: the flip is identical when
//! the capturing declaration sits in the main entry, so an entry-local rule would
//! patch the wrong object and split the one scope 059 R2 rests on.
//! [`main_entry_capture_is_refused`] is that half.
//!
//! OVER THREE DECLARATION CATEGORIES, because narrowing to operations or to members
//! is refuted by measurement: a `const` captures without ever joining the dispatch
//! surface, and a nested type captures the very type a receiver then dispatches
//! against. A binder and an entity variant are excluded by 059 (identity, not a
//! declaration that may be added) — [`entity_variant_is_not_a_capturer`] pins that.
//!
//! ── WHAT 059's CENSUS MISSED, AND WHAT THIS TICKET AMENDED ────────────────────
//!
//! 059 R4 states the clause over "a name that already resolves there" and reports,
//! from WI-981's 61-site census, ZERO no-override captures in the corpus. MEASURED
//! HERE, the unamended clause refuses THREE stdlib sites, of two shapes the census
//! never reached — its five classes sum to 61 and neither shape is among them:
//!
//!   * `prelude.SortedSet.merge` over `EffectExpression.merge`, and
//!     `reflect.Substitution.apply` over `Expr.apply` — a sibling type's entity
//!     CONSTRUCTOR, reached through §8.6's variant-exposure link.
//!   * `reflect.KB.reflect` over the NAMESPACE `anthill.reflect`.
//!
//! Both are excluded by the amended clause, each for its own reason, and
//! [`sibling_constructor_is_not_a_capture`] / [`enclosing_namespace_is_not_a_capture`]
//! drive them on the shapes the stdlib sites have. The residual corpus cost is zero —
//! which is what 059 claimed, now holding for stated reasons rather than by an
//! incomplete count.
//!
//! ── THE EXCLUSION IS A RELATION, NEVER A ROUTE ────────────────────────────────
//!
//! A capture is excused when the declaring sort PROVIDES or REQUIRES the sort that
//! owns the captured name. `provides` is how a sort implements what it provides.
//! `requires` is 059's second stated option for this clause ("or drop the narrow
//! exclusion"), taken over the narrow one because the narrow one is unimplementable
//! without false refusals: `requires_shadow_is_confusable` falls open to "confusable"
//! whenever the requirement binds the spec to a TYPE PARAMETER rather than to a
//! carrier, and falling open is right for a warning and wrong for a refusal.
//! [`requires_shadow_is_not_refused`] is that case, on the shape that forced it.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED by making each edit and re-running, not predicted.
//!
//! Delete the `check_name_captures(kb)` call in `load_phase_inner` — 4 fail, 9 pass:
//!
//!   * [`operation_capture_is_refused`], [`const_capture_is_refused`],
//!     [`nested_type_capture_is_refused`], [`main_entry_capture_is_refused`] — FAIL.
//!     Each loads clean with the check gone, which is the defect.
//!   * every `*_base_*` row, [`provider_override_is_not_refused`],
//!     [`requires_shadow_is_not_refused`], [`sibling_constructor_is_not_a_capture`],
//!     [`enclosing_namespace_is_not_a_capture`],
//!     [`entity_variant_is_not_a_capturer`], [`ordinary_namespace_is_untouched`] —
//!     PASS EITHER WAY, BY DESIGN. They are the controls: without them a check that
//!     refused everything would look correct.
//!
//! Remove EITHER amendment — the variant-exposure skip in `resolve_captured_name`, or
//! `captured_is_namespace_only` — and NINE of the rows fail, the same nine each time.
//! Not because those rows test the amendment: because the STDLIB ITSELF stops loading,
//! so every row whose fixture includes it dies before its assertion. That is the
//! amendments' cost as a number, and it is why 059's "zero corpus sites" claim had to
//! be restated rather than merely re-checked.
//!
//! The exposure skip's three narrowings each have their own failing row, measured the
//! same way. Drop the edge-local `parent_edge_is_imported` conjunct ⇒
//! [`plain_import_of_a_variant_bearing_sort_is_a_capture`] alone fails. Drop the
//! subtree flip that spends the skip after an imported edge ⇒
//! [`wildcard_import_of_the_leaked_into_namespace_is_a_capture`] alone fails. Ask only
//! for the capturing declaration's own file instead of every file with text at the
//! address ⇒ [`an_import_in_a_file_that_does_write_here_is_a_capture`] alone fails.
//! All three narrowings came from `/code-review`; the first cut had none of them.

use anthill_core::eval::{self, Interpreter, Value};

/// Load, then DRIVE — call the operation and assert the value. A base row that only
/// loaded would measure nothing: the whole hazard is a program that loads clean.
fn eval_int(src: &str, op: &str) -> i64 {
    let kb = crate::common::try_load_kb_with(src)
        .unwrap_or_else(|errs| panic!("base fixture must load clean; got {errs:#?}"));
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => n,
        Ok(other) => panic!("expected Int from {op}, got {}", other.type_name()),
        Err(e) => panic!("{op} failed to evaluate: {e}"),
    }
}

/// The load errors of a source that must be REFUSED. Panics on a clean load, which
/// is the failure this whole file exists to catch.
fn refusal(src: &str) -> String {
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("expected a capture refusal; the fixture loaded CLEAN"),
        Err(errs) => errs.join("\n"),
    }
}

/// Assert one capture refusal naming BOTH sites — the capturing declaration by
/// keyword and name, and what the name meant before, by qualified name. "Both sites
/// named" is the acceptance: the two declarations routinely sit in different files,
/// and the one the author has open is the one that did not change.
fn assert_names_both(errs: &str, capturing: &str, sort: &str, captured: &str) {
    for want in [capturing, sort, captured] {
        assert!(
            errs.contains(want),
            "capture refusal must name {want:?}; got:\n{errs}"
        );
    }
}

// ── the operation capture: 059's own measured hazard ────────────────────────

/// The base row. `use`'s body reads a bare `f` that resolves through the import.
const OP_BASE: &str = r#"
namespace wi999.lib
  operation f(x: Int64) -> Int64 = 1
end
namespace wi999.op
  import wi999.lib.f
  sort Rec
    entity rec(n: Int64)
    operation use(r: Rec) -> Int64 = f(r.n)
  end
  operation drive() -> Int64 = Rec.use(rec(n: 0))
end
"#;

#[test]
fn operation_capture_base_answers_the_import() {
    // PASSES EITHER WAY, BY DESIGN — it is the "before" the refusal protects, and
    // it is what makes the next test's refusal attributable to the added
    // declaration rather than to anything else in the fixture.
    assert_eq!(eval_int(OP_BASE, "wi999.op.drive"), 1);
}

#[test]
fn operation_capture_is_refused() {
    // The identical program plus a secondary entry declaring `f`. Nothing named `f`
    // was a member, so clause 1 is silent and the freshness/body rules admit it —
    // and `use`'s unedited body now answers 2.
    //
    // BACKED OUT: this test FAILS — the fixture loads clean.
    let errs = refusal(&format!(
        "{OP_BASE}\nnamespace wi999.op\n  namespace Rec\n    \
         operation f(x: Int64) -> Int64 = 2\n  end\nend\n"
    ));
    assert_names_both(&errs, "operation f", "wi999.op.Rec", "wi999.lib.f");
}

#[test]
fn main_entry_capture_is_refused() {
    // THE SAME CAPTURE, WRITTEN IN THE MAIN ENTRY. 059 measured the flip identically
    // for both spellings, which is why the clause is stated over the sort SCOPE and
    // not over secondary entries: an entry-local rule would patch the wrong object.
    //
    // BACKED OUT: this test FAILS — the fixture loads clean.
    let errs = refusal(
        r#"
namespace wi999.lib2
  operation f(x: Int64) -> Int64 = 1
end
namespace wi999.mainentry
  import wi999.lib2.f
  sort Rec
    entity rec(n: Int64)
    operation use(r: Rec) -> Int64 = f(r.n)
    operation f(x: Int64) -> Int64 = 2
  end
end
"#,
    );
    assert_names_both(&errs, "operation f", "wi999.mainentry.Rec", "wi999.lib2.f");
}

// ── the const capture: a member that never joins the dispatch surface ────────

const CONST_BASE: &str = r#"
namespace wi999.clib
  const LIMIT: Int64 = 1
end
namespace wi999.cns
  import wi999.clib.{LIMIT}
  sort Rec
    entity rec(n: Int64)
    operation use(r: Rec) -> Int64 = LIMIT
  end
  operation drive() -> Int64 = Rec.use(rec(n: 0))
end
"#;

#[test]
fn const_capture_base_answers_the_import() {
    // PASSES EITHER WAY, BY DESIGN — the base half of the const row.
    assert_eq!(eval_int(CONST_BASE, "wi999.cns.drive"), 1);
}

#[test]
fn const_capture_is_refused() {
    // A const is a member and is NOT on the dispatch surface (059 measured
    // `receiver.K` refused in either placement), so clause 1 cannot reach this even
    // in principle — which is why clause 3 is stated over LOOKUP rather than over
    // membership.
    //
    // BACKED OUT: this test FAILS — the fixture loads clean and `use` answers 2.
    let errs = refusal(&format!(
        "{CONST_BASE}\nnamespace wi999.cns\n  namespace Rec\n    \
         const LIMIT: Int64 = 2\n  end\nend\n"
    ));
    assert_names_both(&errs, "const LIMIT", "wi999.cns.Rec", "wi999.clib.LIMIT");
}

// ── the nested-type capture: dot dispatch routes straight THROUGH it ─────────

const TYPE_BASE: &str = r#"
namespace wi999.tlib
  sort Code
    entity code(v: Int64)
    operation tag(c: Code) -> Int64 = c.v
  end
end
namespace wi999.tns
  import wi999.tlib.{Code, code}
  sort Rec
    entity rec(n: Int64)
    operation use(r: Rec) -> Int64 = code(v: 100).tag()
  end
  operation drive() -> Int64 = Rec.use(rec(n: 0))
end
"#;

#[test]
fn nested_type_capture_base_answers_the_import() {
    // PASSES EITHER WAY, BY DESIGN. It also drives the point 059 makes about this
    // category: `.tag()` DISPATCHES on the captured type, so a type capture is not
    // excused by "dot dispatch never routes through it" — it routes through nothing
    // else.
    assert_eq!(eval_int(TYPE_BASE, "wi999.tns.drive"), 100);
}

#[test]
fn nested_type_capture_is_refused() {
    // Same-shape on purpose: give the two types different fields and the capture
    // surfaces as a loud field error — for the WRONG reason — while same-shape
    // nothing complains. A rule may not rest on the types happening to disagree.
    //
    // BACKED OUT: this test FAILS — the fixture loads clean, constructing and
    // dispatching on the NESTED `Code`.
    let errs = refusal(&format!(
        "{TYPE_BASE}\nnamespace wi999.tns\n  namespace Rec\n    \
         sort Code\n      entity code(v: Int64)\n      \
         operation tag(c: Code) -> Int64 = 200\n    end\n  end\nend\n"
    ));
    assert_names_both(&errs, "sort Code", "wi999.tns.Rec", "wi999.tlib.Code");
}

// ── the exclusions: a RELATION, never a route ────────────────────────────────

#[test]
fn provider_override_is_not_refused() {
    // `Impl` PROVIDES `Show` and supplies its own `show`, which is how a sort
    // implements what it provides — 23 of the corpus's 61 shadowing declarations.
    // DRIVEN, not merely loaded: the override has to be the operation that answers.
    //
    // PASSES EITHER WAY, BY DESIGN — the control that the check did not refuse
    // everything. It FAILS if `capture_is_excused` drops its `sort_provides` leg,
    // which is the refusal's most likely over-reach.
    let src = r#"
namespace wi999.prov
  import anthill.prelude.{Int64}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort Impl
    entity impl(n: Int64)
    requires Show[T = Impl]
    provides Show[T = Impl]
    operation show(x: Impl) -> Int64 = 42
  end
  operation drive() -> Int64 = Impl.show(impl(n: 0))
end
"#;
    assert_eq!(eval_int(src, "wi999.prov.drive"), 42);
}

#[test]
fn requires_shadow_is_not_refused() {
    // THE SHAPE THAT DECIDED THE EXCLUSION'S WIDTH, and it is `anthill-testcases/
    // ring-polynom` in miniature: the requirement binds the spec to a TYPE PARAMETER
    // (`Ring[R]`, the ELEMENT type), and the sort declares its own `add` for ITSELF.
    // Under the narrow reading this is refused — `requires_shadow_is_confusable`
    // cannot prove `R` and `Poly[R]` different, a type parameter being a wildcard, so
    // it falls open to "confusable". Falling open is right for WI-346's warning and
    // wrong for a refusal: it would reject the ordinary way to give a sort an
    // operator beside a requirement on its element type.
    //
    // PASSES EITHER WAY, BY DESIGN — under the narrow reading it would FAIL, which
    // is the measurement that chose 059's other stated option.
    let src = r#"
namespace wi999.req
  import anthill.prelude.{Int64}
  sort Ring
    sort T = ?
    operation add(a: T, b: T) -> T
  end
  sort Poly
    sort R = ?
    requires Ring[T = R]
    entity poly(c: R)
    operation add(p1: Poly[R = R], p2: Poly[R = R]) -> Int64 = 7
  end
  operation drive() -> Int64 = Poly.add(poly(c: 1), poly(c: 2))
end
"#;
    assert_eq!(eval_int(src, "wi999.req.drive"), 7);
}

// ── the two shapes 059's census missed ───────────────────────────────────────

#[test]
fn sibling_constructor_is_not_a_capture() {
    // `prelude.SortedSet.merge` over `EffectExpression.merge` in miniature. §8.6
    // leaks an enum's constructors to the ENCLOSING namespace so they can be written
    // unqualified THERE; that is not a statement that the bare name is in use at any
    // address inside it. Members and constructors are named PER TYPE — the
    // alternative makes every constructor name in a namespace a reserved word for
    // every sort in it.
    //
    // DRIVEN ON BOTH SIDES, which is the point: the sibling's constructor stays
    // reachable from the enclosing namespace (`driveCtor` = 3) while the sort's own
    // same-named member answers for the sort (`driveMember` = 9). The exclusion is
    // that these coexist, not that one wins.
    //
    // PASSES EITHER WAY, BY DESIGN. MEASURED with the variant-exposure skip removed
    // from `resolve_captured_name`: NINE of this file's thirteen rows fail, not one —
    // the STDLIB ITSELF is refused at `SortedSet.merge` and `Substitution.apply`, so
    // every row that loads it dies in the fixture rather than in its assertion. That
    // is the amendment's cost stated as a number: without it, no program that uses
    // the standard library loads.
    let src = r#"
namespace wi999.sib
  import anthill.prelude.{Int64}
  enum Other
    entity merge(left: Int64, right: Int64)
    entity leaf(v: Int64)
  end
  sort Box
    entity box(k: Int64)
    operation merge(a: Int64, b: Int64) -> Int64 = 9
  end
  operation driveCtor() -> Int64 =
    match merge(left: 1, right: 2)
      case merge(l, r) -> 3
      case leaf(v) -> 4
  operation driveMember() -> Int64 = Box.merge(1, 2)
end
"#;
    assert_eq!(eval_int(src, "wi999.sib.driveCtor"), 3);
    assert_eq!(eval_int(src, "wi999.sib.driveMember"), 9);
}

#[test]
fn enclosing_namespace_is_not_a_capture() {
    // `reflect.KB.reflect` over the namespace `anthill.reflect` in miniature. A
    // namespace denotes no value and no type — it can appear only as the head of a
    // qualified path, so there is no answer for a body to silently get a different
    // one of. What a capture does to a path is the DOTTED LADDER's, measured in
    // `captured_is_namespace_only`'s doc and tracked as its own ticket: the recovery
    // rung re-roots a shadowed head at the bare global twin instead of at the
    // enclosing chain.
    //
    // PASSES EITHER WAY, BY DESIGN. MEASURED with `captured_is_namespace_only`
    // removed from the check: NINE of thirteen rows fail, for the sibling-constructor
    // row's reason — the STDLIB ITSELF is refused, here at `reflect.KB.reflect` over
    // the namespace `anthill.reflect`, so every row that loads it dies in its fixture.
    // It would also fail if the predicate were widened to a symbol that is ALSO a sort
    // (059 R2's own `namespace X` + `sort X` shape, one symbol carrying both
    // categories), which is why the value/type kinds are named rather than negated.
    let src = r#"
namespace wi999.outer
  namespace inner
    import anthill.prelude.{Int64}
    operation g(x: Int64) -> Int64 = 5
    sort Box
      entity box(v: Int64)
      operation inner(b: Box) -> Int64 = b.v
    end
    operation drive() -> Int64 = Box.inner(box(v: 8))
  end
end
"#;
    assert_eq!(eval_int(src, "wi999.outer.inner.drive"), 8);
}

// ── an IMPORT spends the exposure exclusion ──────────────────────────────────
//
// All three rows below were found by `/code-review` on the first cut, which tested
// only the IMMEDIATE `scope → parent` edge. §8.6's leak is excused because it is
// AUTOMATIC; an import of the leaking type, or of the namespace it leaks into, is
// the author asking for those bare names, and a declaration taking one captures it.

#[test]
fn plain_import_of_a_variant_bearing_sort_is_a_capture() {
    // `import wi999.ilib.Colour` splices `Colour`'s scope in as a non-enclosing
    // parent, so `Red` is in view in `wi999.iplain` because THIS FILE asked. One hop:
    // the imported edge IS the exposure-looking edge.
    //
    // BACKED OUT (the `parent_edge_is_imported` conjunct): this test FAILS — the
    // fixture loads clean. This is the corpus-live shape, not a hypothetical: the
    // stdlib holds ~10 plain imports of variant-bearing sorts (`anthill.prelude.List`,
    // `.Option`, `.Stream`, `.Iteration`, `.Iterable`).
    let errs = refusal(
        r#"
namespace wi999.ilib
  enum Colour
    entity Red(x: Int64)
    entity Blue(x: Int64)
  end
end
namespace wi999.iplain
  import wi999.ilib.Colour
  sort Box
    entity box(v: Int64)
    operation Red(n: Int64) -> Int64 = 2
  end
end
"#,
    );
    assert_names_both(&errs, "operation Red", "wi999.iplain.Box", "wi999.ilib.Colour.Red");
}

#[test]
fn wildcard_import_of_the_leaked_into_namespace_is_a_capture() {
    // TWO HOPS, and the one the first cut missed. `import wi999.wlib.*` makes the
    // edge `wi999.wns → wi999.wlib` an imported one; the NEXT edge, `wlib → Colour`,
    // is §8.6's exposure edge with a `Declaration` origin. An edge-local test admits
    // the first and skips the second, so `Red` was invisible to the check although
    // the author's own import is what put it in view.
    //
    // BACKED OUT (the `below` flip in `resolve_in_scope_recursive_with_mode`): this
    // test FAILS — the fixture loads clean, and a body reading `Red(x: 7)` silently
    // rebinds to `Box.Red`.
    let errs = refusal(
        r#"
namespace wi999.wlib
  enum Colour
    entity Red(x: Int64)
    entity Blue(x: Int64)
  end
end
namespace wi999.wns
  import wi999.wlib.*
  sort Box
    entity box(v: Int64)
    operation Red(n: Int64) -> Int64 = 2
  end
end
"#,
    );
    assert_names_both(&errs, "operation Red", "wi999.wns.Box", "wi999.wlib.Colour.Red");
}

#[test]
fn same_namespace_exposure_without_an_import_is_still_not_a_capture() {
    // THE CONTROL for the two rows above, and the reason they are about the IMPORT
    // rather than about variants: identical shape, `Colour` and `Box` declared in ONE
    // namespace so no import is written at all. §8.6 leaks `Red` here automatically,
    // and the exclusion holds — this is `SortedSet.merge`'s shape.
    //
    // PASSES EITHER WAY, BY DESIGN. Without it, deleting the exclusion outright would
    // make the two rows above pass and look correct.
    let src = r#"
namespace wi999.noimport
  import anthill.prelude.{Int64}
  enum Colour
    entity Red(x: Int64)
    entity Blue(x: Int64)
  end
  sort Box
    entity box(v: Int64)
    operation Red(n: Int64) -> Int64 = 2
  end
  operation drive() -> Int64 = Box.Red(1)
end
"#;
    assert_eq!(eval_int(src, "wi999.noimport.drive"), 2);
}

// ── the capture question is asked PER FILE, not over their union ─────────────

#[test]
fn an_import_in_a_file_with_no_text_here_is_not_a_capture() {
    // WI-995: an import resolves ONLY in the file that wrote it. File A imports
    // `wi999.xlib.f` into `wi999.xns` and never mentions `Rec`; file B declares
    // `Rec.f`. No body anywhere reads a bare `f` in `Rec`'s scope, and A's text could
    // not have — so refusing B would reject a valid program whose only repair lives
    // in someone else's file.
    //
    // Found by `/code-review`: the first cut asked under `ImportVisibility::All` (the
    // union over every file) and refused this. PASSES EITHER WAY once the per-file
    // loop exists; under the union reading it FAILED.
    let kb = crate::common::try_load_kb_with_files(&[
        r#"
namespace wi999.xlib
  operation f(x: Int64) -> Int64 = 1
end
namespace wi999.xns
  import wi999.xlib.f
  operation elsewhere(n: Int64) -> Int64 = f(n)
end
"#,
        r#"
namespace wi999.xns
  sort Rec
    entity rec(n: Int64)
    operation f(r: Rec) -> Int64 = 2
  end
end
"#,
    ]);
    assert!(
        kb.is_ok(),
        "an import in a file with no text in `Rec`'s scope is not a capture of \
         `Rec.f`; got: {:#?}",
        kb.err()
    );
}

#[test]
fn an_import_in_a_file_that_does_write_here_is_a_capture() {
    // THE OTHER SIDE, and what makes the row above a narrowing rather than a hole:
    // file A's import is the same, but now A's text DOES enter `Rec`'s scope and
    // reads the bare `f`. File B's declaration repoints A's unedited body, and the
    // per-file loop asks on A's behalf and finds it — which the capturing
    // declaration's OWN file could never have answered, `f` resolving to nothing
    // there.
    //
    // BACKED OUT (asking only for the capturing declaration's file): this test FAILS
    // — the fixture loads clean, and it is 059's motivating case, a secondary entry
    // written by a third party.
    let errs = match crate::common::try_load_kb_with_files(&[
        r#"
namespace wi999.ylib
  operation f(x: Int64) -> Int64 = 1
end
namespace wi999.yns
  import wi999.ylib.f
  sort Rec
    entity rec(n: Int64)
    operation use(r: Rec) -> Int64 = f(r.n)
  end
end
"#,
        r#"
namespace wi999.yns
  namespace Rec
    operation f(x: Int64) -> Int64 = 2
  end
end
"#,
    ]) {
        Ok(_) => panic!("expected a capture refusal across files; the fixture loaded CLEAN"),
        Err(errs) => errs.join("\n"),
    };
    assert_names_both(&errs, "operation f", "wi999.yns.Rec", "wi999.ylib.f");
}

// ── the categories that may not CAPTURE ──────────────────────────────────────

#[test]
fn entity_variant_is_not_a_capturer() {
    // 059 excludes binders and entity variants by name: a constructor is IDENTITY,
    // which R1/R3 say is written once and never added. Its census counts 38 such
    // sites, every one legitimate — including `TypeExtractor.Error` over a `sort
    // Error` declared elsewhere, which is this shape exactly.
    //
    // DRIVEN FROM INSIDE `Holder`'s OWN SCOPE, which is where the capture is: there
    // the bare `Code` is the variant, and it would be the sibling `sort Code` if the
    // variant had not taken the name. Constructing it at namespace level instead
    // measures nothing about this rule — the name is contested between the sort and
    // the exposed variant there, and answers `unknown functor` (measured).
    //
    // PASSES EITHER WAY, BY DESIGN — it FAILS if `DeclCategory::can_capture` admits
    // `Entity`, which is the category list's own failure mode.
    let src = r#"
namespace wi999.var
  import anthill.prelude.{Int64}
  sort Code
    entity code(v: Int64)
  end
  sort Holder
    entity Code(w: Int64)
    operation make(w: Int64) -> Holder = Code(w: w)
    operation read(h: Holder) -> Int64 = h.w
  end
  operation drive() -> Int64 = Holder.read(Holder.make(6))
end
"#;
    assert_eq!(eval_int(src, "wi999.var.drive"), 6);
}

#[test]
fn ordinary_namespace_is_untouched() {
    // 059 is explicit that "nothing in R3 or R4 reaches" an ordinary namespace — one
    // at an address no type occupies. The same declaration that is refused inside a
    // sort scope is legal here, and the check's scope gate (`has_kind(owner, Sort)`)
    // is what keeps it so.
    //
    // PASSES EITHER WAY, BY DESIGN — it FAILS if the scope gate is dropped, which
    // would make the clause reach every namespace in the language.
    let src = r#"
namespace wi999.nslib
  operation f(x: Int64) -> Int64 = 1
end
namespace wi999.plain
  import wi999.nslib.f
  operation f(x: Int64) -> Int64 = 2
  operation drive() -> Int64 = f(0)
end
"#;
    assert_eq!(eval_int(src, "wi999.plain.drive"), 2);
}
