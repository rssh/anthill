//! WI-20260826-XFTC7 — A NESTED SORT REACHED BY A `provides` CONVERSION IS NAMEABLE IN
//! TYPE POSITION.
//!
//! ## The asymmetry this closes
//!
//! WI-20260825-X9RRN gave the dotted ladder a rung that follows `provides`, so `Mid.f()`
//! and `Mid.rel` resolve through the conversion. The TYPE position did not move, and the
//! reason was not a policy: `load::try_rigid_type_projection` carries its OWN qualified-
//! child lookup —
//!
//!     let child_qn = format!("{sort_qn}.{member_name}");
//!     if let Some(&child) = kb.symbols.by_qualified_name.get(&child_qn) { … }
//!
//! — which is rung 1 of the ladder written a second time, and it had rung 1's gap. So
//! `x: Base.Inner` loaded while `x: Mid.Inner` fell past it into a RIGID PROJECTION and
//! the typer refused it as *"type 'Mid' has no member 'Inner'"*. One spelling, three
//! positions, two answers.
//!
//! ## Why this is a NAME question and not a type-inheritance claim
//!
//! The ticket framed the decision as "does a value-level conversion convey a nested
//! SORT", which would be a claim about what a type HAS. That is not the branch this sits
//! in. Its own comment says its job: deciding that `Outer.Inner` is a *legitimate
//! qualified CHILD reference, not a projection* — what a NAME denotes, which the ladder
//! already answers identically everywhere else. `project_type_member` is untouched, and a
//! member no head offers still reaches it and is still refused.
//!
//! ## The back-out these rows are stated against
//!
//! Delete the `dotted_by_provision` call in `try_rigid_type_projection`'s non-param arm.
//! Every positive row here fails with "has no member". `a_typo_is_still_loud_in_type_
//! position` and the declared-child controls pass either way BY DESIGN — they are what
//! says the arm was widened by exactly one edge kind rather than made permissive.

use crate::common::{interp_for, try_load_kb_with};

fn errs_of(src: &str) -> Vec<String> {
    try_load_kb_with(src)
        .map(|_| Vec::new())
        .unwrap_or_else(|e| e)
}

fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

/// A VALUE FLOWS THROUGH THE TYPE, which is the claim — not that the name loads.
///
/// `viaMid` takes `x: Mid.Inner` and reads `x.v`. If the parameter's type were anything
/// but `Base.Inner`, the argument would not check and the field read would not resolve;
/// 41 is what says the whole chain landed. The `Base.Inner` control carries a DIFFERENT
/// number so a failure names which spelling broke.
///
/// BACKED OUT: `type mismatch in Mid.Inner (entity-field): expected a well-formed type
/// projection, got type 'xf.lib.Mid' has no member 'Inner'` — the ticket's own repro.
#[test]
fn a_provided_nested_sort_types_a_parameter_and_a_value_flows_through_it() {
    let src = r#"
namespace test.xftc7.drive
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    sort Inner
      entity inner(v: Int64)
    end
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  operation viaMid(x: Mid.Inner) -> Int64 = x.v
  operation viaBase(x: Base.Inner) -> Int64 = x.v
  operation driveMid() -> Int64 = viaMid(Base.Inner.inner(v: 41))
  operation driveBase() -> Int64 = viaBase(Base.Inner.inner(v: 7))
end
"#;
    assert_eq!(
        drive(src, "test.xftc7.drive.driveMid"),
        "Int(41)",
        "`x: Mid.Inner` must denote `Base.Inner` — the sort `Mid` reaches by `provides` — \
         and a value of it must pass and project"
    );
    assert_eq!(
        drive(src, "test.xftc7.drive.driveBase"),
        "Int(7)",
        "THE CONTROL: the DECLARED spelling in the same position, so a failure above is \
         about the conversion and not about nested sorts being unnameable"
    );
}

/// AN ENUM CHILD TOO — the second member kind this branch names, and the row that says the
/// hop is about the qualified-child LOOKUP rather than about one shape of declaration.
///
/// The branch's own comment lists both cases it serves: "`Outer.Inner` for a nested alias
/// sort, `Enum.Entity`". Only `Inner` was measured when the fix was written; without this
/// row, an implementation that special-cased nested sorts would pass everything above.
#[test]
fn a_provided_enum_child_is_nameable_too() {
    let src = r#"
namespace test.xftc7.enumchild
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    enum Colour
      entity red(v: Int64)
      entity blue(v: Int64)
    end
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  operation viaMid(c: Mid.Colour) -> Int64 = 2
  operation drive() -> Int64 = viaMid(Base.Colour.red(v: 1))
end
"#;
    assert_eq!(
        drive(src, "test.xftc7.enumchild.drive"),
        "Int(2)",
        "an `enum` child reached by conversion must name the same sort the declared \
         spelling does"
    );
}

/// A TYPO IS STILL LOUD, on BOTH spellings — the row that keeps this from being a
/// permissive arm.
///
/// `Mid.Nonesuch` names nothing under either reading, so it must still fall to the
/// projection path and be refused there. Asserting the DECLARED twin beside it is what
/// says the refusal is about the member and not about the conversion: if only
/// `Mid.Nonesuch` were checked, an implementation that refused every converted name would
/// pass.
///
/// PASSES BOTH WAYS BY DESIGN. This is the row that fails if the arm is ever widened past
/// the provision edges.
#[test]
fn a_typo_is_still_loud_in_type_position() {
    let program = |head: &str| {
        format!(
            r#"
namespace test.xftc7.typo
  import anthill.prelude.{{Int64}}
  sort Base
    sort T = ?
    sort Inner
      entity inner(v: Int64)
    end
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  operation g(x: {head}.Nonesuch) -> Int64 = 2
end
"#
        )
    };
    for head in ["Mid", "Base"] {
        let errs = errs_of(&program(head));
        assert!(
            errs.iter()
                .any(|e| e.contains("has no member 'Nonesuch'")),
            "`{head}.Nonesuch` denotes nothing under any reading and must reach the \
             projection path's refusal; got {errs:?}"
        );
    }
}

/// THE HEAD'S OWN CHILD WINS, and the fixture is built so the number names the winner.
///
/// `Mid` declares `sort Inner { entity minner }` AND provides a `Base` whose `Inner`
/// declares `binner`. The hop sits BELOW the direct join, so `x: Mid.Inner` is `Mid`'s —
/// and `Mid.Inner.minner(…)` type-checks against it. Had it bound `Base.Inner`, the
/// argument would be a different sort and the load would fail; the two entity names are
/// distinct precisely so the two readings cannot both accept this program.
#[test]
fn the_heads_own_child_wins_over_the_provided_one() {
    let src = r#"
namespace test.xftc7.rung1
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    sort Inner
      entity binner(v: Int64)
    end
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
    sort Inner
      entity minner(v: Int64)
    end
  end
  operation viaMid(x: Mid.Inner) -> Int64 = x.v
  operation drive() -> Int64 = viaMid(Mid.Inner.minner(v: 42))
end
"#;
    assert_eq!(
        drive(src, "test.xftc7.rung1.drive"),
        "Int(42)",
        "a head that declares the child itself answers with its own — the provision hop \
         is consulted only where the direct join missed"
    );
}

/// TWO PROVIDED ROUTES TO ONE CHILD NAME ARE AN AMBIGUITY, in BOTH source orders — and
/// reported BY NAME rather than left to the projection path.
///
/// Falling through would report "type 'Mid' has no member 'Inner'", which is the OPPOSITE
/// verdict: it says the name denotes nothing where in fact it denotes two things. Both
/// clause orders are run for WI-20260825-EBMG8's reason — a same-named member reached
/// twice otherwise resolves by SOURCE ORDER, which is stable in tests and stable across
/// machines and is therefore worse than a coin flip.
#[test]
fn two_provided_routes_to_one_child_are_ambiguous_in_either_order() {
    let program = |first: &str, second: &str| {
        format!(
            r#"
namespace test.xftc7.amb
  import anthill.prelude.{{Int64}}
  sort L
    sort T = ?
    sort Inner
      entity linner(v: Int64)
    end
  end
  sort R
    sort T = ?
    sort Inner
      entity rinner(v: Int64)
    end
  end
  sort Mid
    sort T = ?
    provides {first}[T = T]
    provides {second}[T = T]
  end
  operation g(x: Mid.Inner) -> Int64 = 2
end
"#
        )
    };
    for (a, b) in [("L", "R"), ("R", "L")] {
        let errs = errs_of(&program(a, b));
        assert!(
            errs.iter().any(|e| e.contains("ambiguous symbol 'Mid.Inner'")
                && e.contains("test.xftc7.amb.L.Inner")
                && e.contains("test.xftc7.amb.R.Inner")),
            "with `provides {a}` first, `Mid.Inner` reaches two declarations and must SAY \
             so — not report the opposite verdict that it denotes nothing, and not pick by \
             clause order (WI-20260825-EBMG8); got {errs:?}"
        );
    }
}

/// A DIAMOND IS ONE ANSWER, driven to a value.
///
/// `Mid provides L` and `provides R`, and BOTH provide `Base`, whose `Inner` is declared
/// ONCE. The walk's `visited` set probes `Base` once, so this is not the ambiguity above —
/// and refusing it would refuse the shape `algebra.anthill` records as benign, which the
/// library is built on.
#[test]
fn a_diamond_over_one_child_is_one_answer() {
    let src = r#"
namespace test.xftc7.diamond
  import anthill.prelude.{Int64}
  sort Base
    sort T = ?
    sort Inner
      entity inner(v: Int64)
    end
  end
  sort L
    sort T = ?
    provides Base[T = T]
  end
  sort R
    sort T = ?
    provides Base[T = T]
  end
  sort Mid
    sort T = ?
    provides L[T = T]
    provides R[T = T]
  end
  operation viaMid(x: Mid.Inner) -> Int64 = x.v
  operation drive() -> Int64 = viaMid(Base.Inner.inner(v: 42))
end
"#;
    assert_eq!(
        drive(src, "test.xftc7.diamond.drive"),
        "Int(42)",
        "two routes to ONE declaration are one answer — the ambiguity must discriminate \
         on the declaration, not on the number of routes"
    );
}

/// A MEMBER THAT IS NOT A TYPE IS REFUSED AT THE DECLARATION — on BOTH readings, and it
/// was refused on neither. Found by `/code-review`.
///
/// What leaves this arm is `make_sort_ref(child)`, so the child has to be something that
/// can BE a type. Nothing asked: measured, `operation Zero()` on `Base` made `x: Base.Zero`
/// load clean and the nonsense type surfaced only if some call site happened to be checked
/// — *"expected Zero, got Int64"*, reported far from its cause. The conversion path
/// mirrored it exactly (`x: Mid.Zero`), so the hop widened a hole rather than opening one.
///
/// THE GATE IS POSITIVE, AND THAT IS THE FINDING RATHER THAN A STYLE CHOICE. The obvious
/// move is to reuse the ladder's `not_a_field`. It does not work, measured: the symbol a
/// two-segment name reaches from an operation's parameter list is `SymbolKind::Param`,
/// which `not_a_field` admits. `Sort | Entity` settles every case at once — `Field`,
/// `Param` and `Operation` are simply not types — and it is the TYPE position's own
/// question rather than a third copy of the ladder's.
///
/// THE THIRD ROW IS WI-751's SHAPE, and it is the one that shows the gate is worth having
/// on the DECLARED path too: with an eponymous `sort Foo` beside `operation Foo(X: Int64)`,
/// the operation's parameter registers at `probe.Foo.X`, so the sort-headed join lands on
/// it. That program used to load.
#[test]
fn a_member_that_is_not_a_type_is_refused_at_the_declaration() {
    let ops = |head: &str| {
        format!(
            r#"
namespace test.xftc7.kind
  import anthill.prelude.{{Int64}}
  import anthill.prelude.Option.{{some}}
  sort Base
    sort T = ?
    operation Zero() -> Int64 = 0
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  operation useIt(x: {head}.Zero) -> Int64 = 3
  operation drive() -> Int64 = useIt(7)
end
"#
        )
    };
    for head in ["Base", "Mid"] {
        let errs = errs_of(&ops(head));
        assert!(
            errs.iter().any(|e| e.contains("has no member 'Zero'")),
            "`{head}.Zero` names an OPERATION, which cannot be a type — it must be refused \
             where it is written, not minted into a type that fails at some call site; \
             got {errs:?}"
        );
    }
    // WI-751's eponymous shape, on the DECLARED join: the operation's parameter is
    // registered under the sort's qualified name, so the join lands on a `Param`.
    let eponymous = r#"
namespace test.xftc7.epo
  import anthill.prelude.{Int64}
  sort Foo
    entity mk(v: Int64)
  end
  operation Foo(X: Int64) -> Int64 = X
  operation useField(y: Foo.X) -> Int64 = 3
  operation drive() -> Int64 = useField(5)
end
"#;
    let errs = errs_of(eponymous);
    assert!(
        errs.iter().any(|e| e.contains("has no member 'X'")),
        "an operation PARAMETER reached by the sort-headed join is not a type either — \
         and `not_a_field` does not catch it, because its kind is `Param`; got {errs:?}"
    );
}

/// THE GATE DID NOT OVER-NARROW — the control for the row above, and the reason it is a
/// separate row is that "refuses non-types" and "still admits every type" are two claims.
///
/// Three shapes the arm must keep: a nested SORT, an `Enum.Entity` (the second case the
/// arm's own comment names — an ENTITY, which is why the gate is `Sort | Entity` and not
/// `Sort`), and a TYPE PARAMETER of the provided sort. The last is the subtle one: a
/// sort's parameters register as `SymbolKind::Sort`, so the gate admits them, and that is
/// deliberate — `Base.E` through the head's own declaration and `Mid.E` through the
/// conversion behave identically at a call site (measured: both load, both accept an
/// `Int64`), so refusing one would reintroduce the position-dependence this ticket removes.
#[test]
fn every_shape_that_is_a_type_still_passes_the_gate() {
    let src = r#"
namespace test.xftc7.kindok
  import anthill.prelude.{Int64}
  enum Colour
    entity red(v: Int64)
    entity blue(v: Int64)
  end
  sort Base
    sort T = ?
    sort E = ?
    sort Inner
      entity inner(v: Int64)
    end
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
  operation nested(x: Mid.Inner) -> Int64 = x.v
  operation variant(c: Colour.red) -> Int64 = c.v
  operation paramDeclared(x: Base.E) -> Int64 = 1
  operation paramProvided(x: Mid.E) -> Int64 = 2
  operation drive() -> Int64 = nested(Base.Inner.inner(v: 40)) + paramProvided(3)
end
"#;
    // LOADING covers all four spellings — `variant`'s parameter is typed `Colour.red`, and
    // a member the gate ate would be refused at that signature.
    assert!(
        errs_of(src).is_empty(),
        "a nested sort, an enum ENTITY (`Colour.red`) and a type PARAMETER through both \
         the head's own declaration and the conversion must all still be nameable as \
         types; got {:?}",
        errs_of(src)
    );
    // …and the two that can carry a value carry one, so the row is not resting on
    // loadability alone.
    //
    // `Colour.red` IS NOT AMONG THEM, AND THAT IS A DEFECT ELSEWHERE RATHER THAN A
    // PROPERTY OF THIS GATE — WI-20260826-JSFHG. §8.2 says "each constructor name is a
    // sort in its own right" and both halves of `red <: Colour` are implemented (a
    // `Colour.red` parameter passes where `Colour` is expected; the reverse is refused).
    // But every constructor application is typed at the PARENT sort — `red(v: 1)`,
    // `Colour.red(v: 1)`, a declared `-> Colour.red` return, and even a re-construction
    // inside a `match` arm that has already narrowed to `red`, all say "expected red, got
    // Colour" — so no expression has the variant type and a signature written with one is
    // unsatisfiable. This row therefore asserts that the NAME is admitted as a type, which
    // is this gate's whole claim, and leaves inhabiting it to that ticket.
    assert_eq!(
        drive(src, "test.xftc7.kindok.drive"),
        "Int(42)",
        "40 through the `Mid.Inner` parameter plus `paramProvided`'s own 2, reached \
         through a `Mid.E` parameter — so a failure names which shape stopped working"
    );
}

/// `internal` IS ASKED OF BOTH PATHS, AND OF NEITHER BEFORE — and the message says
/// FORBIDDEN rather than ABSENT.
///
/// The declared qualified-child join read `by_qualified_name` with no visibility gate at
/// all: measured on the tree this ticket started from, an `internal sort Inner` cited as
/// `Base.Inner` from another namespace LOADED CLEAN. That is the same bypass WI-369 closes
/// at `process_imports` and WI-752 at the dotted ladder, and it was found here only
/// because adding a gated conversion path beside an ungated declared one is an asymmetry
/// that has to be either justified or removed. Closing it cost the corpus nothing —
/// measured across the whole suite, the single failure was the row that had recorded the
/// hole.
///
/// THE MESSAGE IS THE OTHER HALF. A hidden child that merely fell through reached the
/// projection path and was reported as "type 'Base' has no member 'Inner'" — telling the
/// author their name denotes NOTHING when it denotes something they may not see. Both
/// paths now report the forbidden access by name, the conversion one through a second,
/// admitting read (`resolve_dotted_reported`'s own shape), because a candidate the scope
/// cannot see must not be COUNTED where the size of the set is the verdict.
///
/// THE CONTROL is the same program with the `internal` removed: both spellings load.
/// Without it the row passes on a tree where nested sorts are unnameable altogether.
#[test]
fn an_internal_child_is_forbidden_by_both_paths_and_named_as_such() {
    let program = |head: &str, modifier: &str| {
        format!(
            r#"
namespace test.xftc7.hidden
  import anthill.prelude.{{Int64}}
  sort Base
    sort T = ?
    {modifier}sort Inner
      entity inner(v: Int64)
    end
  end
  sort Mid
    sort T = ?
    provides Base[T = T]
  end
end
namespace test.xftc7.hidden.use
  import anthill.prelude.{{Int64}}
  import test.xftc7.hidden.{{Base, Mid}}
  sort U
    operation g(x: {head}.Inner) -> Int64 = 2
  end
end
"#
        )
    };
    // BOTH paths refuse, and BOTH name the forbidden access rather than an absent member.
    for head in ["Base", "Mid"] {
        let errs = errs_of(&program(head, "internal "));
        assert!(
            errs.iter()
                .any(|e| e.contains("internal") && e.contains(&format!("{head}.Inner"))),
            "`{head}.Inner` is `internal` to `test.xftc7.hidden.Base` — the citing scope \
             may not see it, and must be told THAT rather than that the member does not \
             exist; got {errs:?}"
        );
        assert!(
            !errs.iter().any(|e| e.contains("has no member")),
            "…and must NOT be reported as absent, which is the opposite verdict and what \
             the fall-through used to say; got {errs:?}"
        );
    }
    // THE CONTROL: without the modifier both spellings load.
    for head in ["Base", "Mid"] {
        assert!(
            errs_of(&program(head, "")).is_empty(),
            "a VISIBLE nested sort must be nameable by both spellings — otherwise the \
             refusals above measure nothing; got {:?}",
            errs_of(&program(head, ""))
        );
    }
}

/// WHAT A NAME MAY BE USED AS IS A SET, NOT THE KEYWORD THAT CAME FIRST.
///
/// `type_admissible` (kb/load.rs) is the positive gate this ticket added so that an
/// `operation Zero()` cannot mint a type. It asked `kb.kind_of`, which is
/// `SymbolDef::primary_kind` — and that method's own doc says it is "the keyword the
/// declaration opened with — for DISPLAY only … Not a test for what the name can be used
/// as: see `has_kind`". `define` / `add_kind` accumulate a category SET precisely so
/// source order stops deciding things (WI-926), and asking the first keyword put the
/// order back: a `Base` declaring BOTH `operation Inner()` and `sort Inner` refused the
/// projection when the operation was written first and accepted it when the sort was.
/// Byte-identical programs, two verdicts. Found by `/code-review`.
///
/// WHAT FAILS ON BACK-OUT (restore `matches!(kb.kind_of(sym), Some(Sort) | Some(Entity))`):
/// the `operation`-first row below — the sort-first row and both refusal controls pass
/// either way, and are what says the repair widened the gate by exactly the ordering and
/// not at all in what it admits.
#[test]
fn a_child_that_is_also_an_operation_is_a_type_in_either_declaration_order() {
    let program = |first: &str, second: &str| {
        format!(
            r#"
namespace test.xftc7.order
  import anthill.prelude.{{Int64}}
  sort Base
    {first}
    {second}
  end
  operation take(x: Base.Inner) -> Int64 = 1
end
"#
        )
    };
    let as_sort = "sort Inner\n      entity mk\n    end";
    let as_op = "operation Inner() -> Int64";

    // THE SUBJECT and its order-twin: the same declarations, swapped.
    for (a, b, which) in [
        (as_op, as_sort, "operation first"),
        (as_sort, as_op, "sort first"),
    ] {
        let errs = errs_of(&program(a, b));
        assert!(
            errs.is_empty(),
            "`Base.Inner` names a sort whichever keyword opened the name first \
             ({which}); got {errs:?}"
        );
    }

    // CONTROL 1 — a name that is ONLY an operation is still not a type. This is what the
    // gate exists for, and `has_kind` must not have given it away.
    let only_op = r#"
namespace test.xftc7.order2
  import anthill.prelude.{Int64}
  sort Base
    operation Zero() -> Int64
  end
  operation take(x: Base.Zero) -> Int64 = 1
end
"#;
    assert!(
        errs_of(only_op)
            .iter()
            .any(|e| e.contains("has no member") && e.contains("Zero")),
        "an operation-only member must not mint a type; got {:?}",
        errs_of(only_op)
    );

    // CONTROL 2 — the gate is a gate, not a pass-through: a member of neither category
    // is still refused, so CONTROL 1 is not passing merely because nothing is checked.
    let field = r#"
namespace test.xftc7.order3
  import anthill.prelude.{Int64}
  sort Base
    entity base(fld: Int64)
  end
  operation take(x: Base.fld) -> Int64 = 1
end
"#;
    assert!(
        !errs_of(field).is_empty(),
        "a FIELD is not a type either; got a clean load"
    );
}
