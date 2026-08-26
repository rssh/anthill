//! WI-20260826-NB88H — A MEMBER IMPORT DOES NOT WALK OUT OF THE SORT IT NAMES.
//!
//! `import a.b.C.{n}` resolves `n` by, among other strategies, asking the resolver for
//! the short name AT `C`'s scope (`load::process_imports`, selective strategy 2). That
//! call started an ORDINARY walk, so it left `C` through the enclosing link and answered
//! out of `a.b` — and out of the namespace above THAT. Measured on the delivered tree:
//!
//!   `import anthill.prelude.Numeric.{List}` -> bound `anthill.prelude.List`, a SIBLING
//!   `import anthill.prelude.Pair.{Pair}`    -> bound `Pair` ITSELF, one level out
//!
//! Both are lines that document a membership which does not exist, and both would
//! silently bind something else the day `anthill.prelude` gained a shadowing sibling.
//!
//! ## This is WI-1089's rule, at the one site that never applied it
//!
//! WI-1089 states it on [`crate::intern::EnclosingLinks`] — "`import a.b.C` puts `C` in
//! scope. `C`'s scope is enclosed by `a.b`, so a walk that re-enters the enclosing chain
//! answers with every name of `a.b` — and of the namespace above THAT — from a line that
//! named one sort" — and applied it to the edges the resolver CROSSES. Strategy 2
//! crosses no edge: it calls the resolver AT the base scope, so the walk began in
//! `EnclosingLinks::Followed` and the stop never engaged. `resolve_below_import` is that
//! same walk entered as if the import edge had already been taken.
//!
//! ## What is deliberately NOT narrowed, and why it is not an omission
//!
//! WI-1089's own sentence continues: "a `requires`, a variant exposure and the imported
//! scope's own imports are contents of the thing imported, and stay reachable". So
//! `Numeric.{lt}` and `Ord.{gte}` still resolve, through `requires` and through
//! `provides`+`requires` respectively — the second is the link WI-1110 calls
//! load-bearing, and it still is. Narrowing to OFFERS alone would make the import agree
//! with the qualified address (`load::dotted_by_provision`) and reverse that sentence;
//! measured, it refuses `Ord.{gt, gte, lt, lte}` at 55 sites. That is a decision on its
//! own terms, not a consequence of this one, and
//! `wi_x9rrn_provided_member_address_test::the_qualified_population_is_contained_in_the_member_imports`
//! is where the two populations are still compared.
//!
//! ## WHAT FAILS WHEN THIS IS BACKED OUT
//!
//! Put `resolve_in_scope` back in place of `resolve_below_import` (kb/load.rs,
//! `ImportKind::Selective`) and:
//!   * FOUR rows fail — `a_member_import_does_not_reach_a_sibling_of_the_sort`,
//!     `a_member_import_does_not_rebind_the_sort_itself`,
//!     `the_stop_survives_a_requires_hop` and
//!     `the_refusal_is_located_and_names_the_written_path`. Each fixture loads CLEAN,
//!     which is the defect: the name binds, and using it then works.
//!   * FIVE pass EITHER WAY by design — `an_offered_member_still_imports_and_runs`,
//!     `a_required_member_still_imports`, `an_exposed_constructor_still_imports`,
//!     `a_declared_member_still_imports` and
//!     `a_member_of_a_nested_sort_still_imports_through_the_namespace`. They are the
//!     over-reach controls: what fails if the stop is ever applied to an edge that is
//!     not the enclosing one.
//!
//! A SECOND back-out, measured, separates this fix from a weaker one: make the stop
//! apply at the ENTRY scope and resume below it. THREE rows fall —
//! `the_stop_survives_a_requires_hop`,
//! `a_member_import_does_not_rebind_the_sort_itself` and
//! `the_refusal_is_located_and_names_the_written_path` — because each reaches its target
//! one hop past the entry (`Host requires nb88h.far.Constrained` for the first,
//! `Numeric requires PartialOrd` for the other two, both landing in a namespace holding
//! the name). `a_member_import_does_not_reach_a_sibling_of_the_sort` PASSES under that
//! weaker rule, which is why it is not the row to read for this distinction: `Host`'s own
//! sibling sits in the namespace the entry stop already closes.

use crate::common::{interp_for, try_load_kb_with, try_load_kb_with_files};

/// A library whose sort has: its OWN member, a member it is OFFERED by `provides`, a
/// member it merely `requires`, and — next door, reachable only by walking out — a
/// SIBLING sort and a sibling operation.
const LIB: &str = r#"namespace nb88h.lib
  import anthill.prelude.{Int64}

  sort Sibling
    entity sibling(v: Int64)
  end

  operation sibling_op(x: Int64) -> Int64 = x

  sort Offered
    sort T = ?
    operation offered(x: T) -> T
  end

  sort Host
    sort T = ?
    provides Offered[T = T]
    requires nb88h.far.Constrained[T]
    operation own(x: T) -> T
  end
end
"#;

/// A SECOND namespace, reached from `Host` only by its `requires` clause. `Remote` is a
/// sibling of the CONSTRAINT, so no enclosing link of `Host`'s own leads to it: the sole
/// route is out through the `requires` target's container. That is what makes
/// [`the_stop_survives_a_requires_hop`] separate a PATH-property stop from one applied to
/// the entry scope alone.
const FAR: &str = r#"namespace nb88h.far
  import anthill.prelude.{Int64}

  sort Remote
    entity remote(v: Int64)
  end

  sort Constrained
    sort T = ?
    operation constrained(x: T) -> T
  end
end
"#;

fn import_errors(import_line: &str) -> Vec<String> {
    let src = format!(
        r#"namespace nb88h.use
  import anthill.prelude.{{Int64}}
  {import_line}
end
"#
    );
    match try_load_kb_with_files(&[LIB, FAR, &src]) {
        Ok(_) => Vec::new(),
        Err(errs) => errs,
    }
}

/// The unresolved-import errors the line produced, keyed by the path they name.
///
/// FOR THE NEGATIVE ROWS ONLY. A positive row must use [`import_errors`] and demand the
/// WHOLE load be clean: filtering to one message makes "no unresolved import" true of a
/// fixture that stopped loading for any other reason, which is the "it loads clean"
/// evidence this repo's own principles refuse (found by `/code-review`).
fn unresolved_imports(import_line: &str) -> Vec<String> {
    import_errors(import_line)
        .into_iter()
        .filter(|e| e.contains("unresolved import"))
        .collect()
}

/// A positive row's assertion: the fixture loads with NO error of any kind.
fn assert_imports_clean(import_line: &str, why: &str) {
    let errs = import_errors(import_line);
    assert!(errs.is_empty(), "`{import_line}` must load clean — {why}: {errs:#?}");
}

// ── THE DEFECT: three shapes, all refused ────────────────────────────────────

/// `Sibling` and `sibling_op` live in `nb88h.lib`, NOT in `Host`. A line naming `Host`
/// must not deliver them.
#[test]
fn a_member_import_does_not_reach_a_sibling_of_the_sort() {
    for name in ["Sibling", "sibling_op"] {
        let errs = unresolved_imports(&format!("import nb88h.lib.Host.{{{name}}}"));
        assert_eq!(
            errs.len(),
            1,
            "`Host.{{{name}}}` names a SIBLING of `Host` and must be refused at the \
             import line, loudly and once; got {errs:#?}"
        );
        assert!(
            errs[0].contains(&format!("nb88h.lib.Host.{name}")),
            "the refusal must name the path the AUTHOR WROTE, so the repair is visible \
             from the message: {}",
            errs[0]
        );
    }
}

/// The shape the corpus actually carried: `import anthill.prelude.Pair.{Pair}`, which
/// bound `Pair` by walking one level out of `Pair`'s own scope.
#[test]
fn a_member_import_does_not_rebind_the_sort_itself() {
    let errs = unresolved_imports("import nb88h.lib.Host.{Host}");
    assert_eq!(
        errs.len(),
        1,
        "`Host.{{Host}}` asks `Host` for a member named `Host`; it has none, and the \
         answer must not be `Host` itself from the namespace above: {errs:#?}"
    );

    // …and the live stdlib witnesses, which is what says the fixture is not a
    // shape only this test can build.
    for path in [
        "anthill.prelude.Pair.{Pair}",
        "anthill.prelude.Option.{Option}",
        "anthill.prelude.Numeric.{List}",
    ] {
        let errs = unresolved_imports(&format!("import {path}"));
        assert_eq!(errs.len(), 1, "`{path}` must be refused: {errs:#?}");
    }
}

/// THE STOP IS A PATH PROPERTY, not one hop — and this is the row that says so.
///
/// `Host requires nb88h.far.Constrained`, and `Remote` is a sibling of that CONSTRAINT,
/// in a namespace `Host` has no enclosing link to. So the only route from `Host` to
/// `Remote` leaves through the `requires` target's own container, one hop further on
/// than the entry scope. A `requires` edge is not itself a stopper
/// (`parent_edge_stops_enclosing` admits only `File` / `Invocation` / `Provision`), so
/// the refusal here comes from the mode being INHERITED down the walk rather than
/// tested at the edge.
///
/// MEASURED, both back-outs: swapping `resolve_below_import` for `resolve_in_scope`
/// fails this row, and so does a variant that stops the enclosing link at the entry
/// scope and resumes below it — under which `Remote` binds again while
/// `a_member_import_does_not_reach_a_sibling_of_the_sort` still passes. That asymmetry
/// is the whole content of this row: `Remote` is the only target in this file that no
/// enclosing link of `Host`'s own can reach.
#[test]
fn the_stop_survives_a_requires_hop() {
    let errs = unresolved_imports("import nb88h.lib.Host.{Remote}");
    assert_eq!(
        errs.len(),
        1,
        "`Remote` is reachable from `Host` ONLY out through the `requires` target's \
         namespace; the stop must still be in force there: {errs:#?}"
    );

    // The CONSTRAINT'S OWN MEMBER, beside it: what the `requires` edge legitimately
    // delivers, and the reason this row is not "a `requires` stopped reaching anything".
    assert_imports_clean(
        "import nb88h.lib.Host.{constrained}",
        "`Host requires Constrained`, so `constrained` is contents of what was imported",
    );
}

// ── THE CONTROLS: what an import still reaches (pass either way by design) ────

/// A member the sort DECLARES. Strategy 1 answers it off `by_qualified_name` and never
/// consults the walk at all — the row that says the refusals above are not "member
/// imports stopped working".
#[test]
fn a_declared_member_still_imports() {
    assert_imports_clean("import nb88h.lib.Host.{own}", "`Host` declares `own`");
}

/// A member reached by `provides` — the conversion edge. DRIVEN: the imported name is
/// called and its value asserted, so the row cannot pass on a name that denotes nothing.
#[test]
fn an_offered_member_still_imports_and_runs() {
    let src = r#"namespace nb88h.offered
  import anthill.prelude.{Int64}
  import anthill.prelude.Numeric.{add, sub, mul}
  operation t() -> Int64 = mul(add(2, 3), sub(10, 4))
end
"#;
    let mut interp = interp_for(src);
    let got = interp
        .call("nb88h.offered.t", &[])
        .expect("`add`/`sub`/`mul` come from `Numeric provides Additive/Multiplicative`");
    // The WHOLE rendering, not a substring: `contains("30")` also accepts `Int(300)`
    // (found by `/code-review`).
    assert_eq!(format!("{got:?}"), "Int(30)", "(2+3)*(10-4) = 30, got {got:?}");
}

/// A member reached by `requires`, and by `provides` THEN `requires` — the two edge
/// kinds this ticket deliberately leaves reachable. `Ord provides WeakOrd` and
/// `WeakOrd requires PartialOrd`, which is the link WI-1110 recorded as load-bearing
/// for exactly this import.
///
/// DRIVEN through `Ord.{gte}`; `Numeric.{lt}` is asserted as a load, since the point
/// there is only that the name binds.
#[test]
fn a_required_member_still_imports() {
    let src = r#"namespace nb88h.required
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Ord.{gte, lt}
  operation hi() -> Bool = gte(7, 3)
  operation lo() -> Bool = lt(7, 3)
end
"#;
    let mut interp = interp_for(src);
    let hi = interp.call("nb88h.required.hi", &[]).expect("`gte` must run");
    let lo = interp.call("nb88h.required.lo", &[]).expect("`lt` must run");
    assert!(
        format!("{hi:?}").contains("true") && format!("{lo:?}").contains("false"),
        "gte(7,3)=true, lt(7,3)=false; got {hi:?} / {lo:?}"
    );

    // `Numeric requires PartialOrd[T]` — one edge, no conversion in front of it.
    assert_imports_clean(
        "import anthill.prelude.Numeric.{lt}",
        "a `requires` is contents of the thing imported (WI-1089); narrowing THAT is a \
         separate decision with a 55-site migration",
    );
}

/// A constructor a sort leaks to its enclosing namespace by §8.6 variant exposure. The
/// base path here is the NAMESPACE, and the walk reaches the sort through the exposure
/// link — a non-enclosing edge, so the stop must not touch it.
#[test]
fn an_exposed_constructor_still_imports() {
    for line in [
        "import anthill.prelude.{some, none}",
        "import anthill.prelude.{cons, nil}",
    ] {
        assert_imports_clean(line, "the exposure edge is not the enclosing link");
    }
}

/// The base is a NAMESPACE and the name lives one level down inside a sort — strategy
/// 3's population (`find_in_nested_scope`), which reads the qualified index and never
/// walks. Eleven such rows were measured on the corpus; this is the shape.
#[test]
fn a_member_of_a_nested_sort_still_imports_through_the_namespace() {
    let src = r#"namespace nb88h.nested.lib
  import anthill.prelude.{Int64}
  enum Verdict
    entity yes
    entity no
  end
end
"#;
    let user = r#"namespace nb88h.nested.use
  import anthill.prelude.{Int64}
  import nb88h.nested.lib.{yes}
  fact yes
end
"#;
    let errs = match try_load_kb_with_files(&[src, user]) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    };
    assert!(
        !errs.iter().any(|e| e.contains("unresolved import")),
        "a nested entity is reached by the qualified index, not by the walk: {errs:#?}"
    );
}

/// THE MESSAGE. A refusal here is a MIGRATION, so it has to say enough to repair the
/// line without reading the loader — the path as written, and a source location.
#[test]
fn the_refusal_is_located_and_names_the_written_path() {
    let src = r#"namespace nb88h.located
  import anthill.prelude.{Int64}
  import anthill.prelude.Numeric.{List}
end
"#;
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("`Numeric.{{List}}` must not load"),
        Err(e) => e,
    };
    let hit = errs
        .iter()
        .find(|e| e.contains("unresolved import"))
        .unwrap_or_else(|| panic!("expected an unresolved-import error, got {errs:#?}"));
    assert!(
        hit.contains("anthill.prelude.Numeric.List"),
        "must name the path as written: {hit}"
    );
    assert!(
        hit.contains("3:"),
        "must carry the import line's location (line 3): {hit}"
    );
}
