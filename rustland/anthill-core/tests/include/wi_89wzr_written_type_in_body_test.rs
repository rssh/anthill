//! WI-20261001-89WZR — A TYPE WRITTEN INSIDE A BODY NAMES THE BODY'S OWN PARAMETERS.
//!
//! A signature's types reach the body with each type parameter in scope made RIGID. A type
//! written inside the body — a `let` annotation, a lambda parameter's, a call's bracket — was
//! read as the loader lowered it: the parameter's canonical variable, or its bare name for
//! the enclosing sort's. So `let x: T = y` related a rigid to the variable it stands for and
//! was refused (`expected ?T, got ?T`), in four spellings; a `-R` written in a `let`
//! annotation was a row variable of its own, not the operation's `R`, so a callback that may
//! raise `R` was accepted as lacking it; and a bracket said nothing — `id[A = U](y)` with `y:
//! T` loaded, the argument pinning the `U` the author wrote.
//!
//! Each is now read through the substitution that rigidified the signature
//! (`written_type_at_body_rigids`): an annotation for the value's expected type, the
//! conformance check and the binding; a bracket's value — the callee's or a companion
//! receiver's — for what it binds. Never written back into the stored tree, a rigid being
//! pass-local.
//!
//! Every row that can RUNS and names its value; the rows asserting a LOAD verdict name the
//! refusal a back-out makes disappear.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-03), each part present but disabled, over this file's 16 rows and
//! `wi_80zv8_self_test`'s two `let` rows and its bracket row:
//!
//! 1. THE `let` ANNOTATION IS READ AT THE BODY'S RIGIDS (typing/visit.rs, the `Let` arm). 8
//!    FAIL: the five rows of the four spellings here — each refused as before — the `-R` row
//!    (it loads), and `wi_80zv8_self_test`'s `let same: Self` and its written twin.
//! 2. A LAMBDA PARAMETER'S ANNOTATION IS READ THE SAME WAY (typing/visit.rs, the `Lambda`
//!    arm). 1 FAILS: [`a_lambda_annotation_naming_the_parameter_holds_its_body_to_it`] — the
//!    pinning body loads.
//! 3. TWO ARROWS DIFFERING IN THEIR ROW ARE RENDERED WITH IT (typing/display.rs
//!    `arrow_rows_that_differ`). 1 FAILS:
//!    [`a_lacks_constraint_in_a_let_annotation_is_the_operations_own_row`] — refused, but as
//!    `expected Int64 -> Bool, got Int64 -> Bool`. (`typing_test`'s WI-795 row pins the same
//!    rendering on a hand-built pair, and the cause-agnostic note one level down.)
//! 4. ONE BINDER'S ANNOTATION IS COMPARED WHEN IT NAMES A PARAMETER — (a) read at the body's
//!    rigids (typing/pattern.rs `bind_and_label_pattern`), (b) compared at the DETERMINED
//!    reading, where a rigid counts (`binder_annotation_conflict`). 1 FAILS under each:
//!    [`a_binder_annotation_naming_a_parameter_is_held_to_it`] — the false `a: U` loads.
//! 5. A BRACKET'S VALUE IS READ AT THE BODY'S RIGIDS (typing/slots.rs
//!    `bracket_value_to_bind`, the one reader of the callee bracket, the receiver bracket and
//!    a rule citation's). 4 FAIL here:
//!    [`a_bracket_naming_the_callers_parameter_is_held_to_it`] (the false bracket loads),
//!    [`a_row_bracket_naming_the_callers_row_charges_it`] (it loads),
//!    [`a_bracket_at_another_instance_is_written_in_terms_of_this_one`] and
//!    [`a_receiver_bracket_types_a_bare_return_in_the_bodys_terms`] (both refused as cyclic).
//!    And 2 elsewhere: `wi_80zv8_self_test`'s `self_in_a_call_bracket_is_this_instance` (the
//!    bracket `[A = Self]` no longer holds its argument to this instance), and
//!    `wi_5g28a_citation_bracket_test`'s `a_rigid_in_the_bracket_is_that_rigid` — the
//!    citation's bracket had this reading already, from a substitution of its own, and now
//!    takes it from the shared reader.
//! 6. THE RECEIVER'S TYPE, WHERE IT TYPES A BARE RETURN, IS READ THE SAME WAY (typing/apply.rs,
//!    the WI-20260829-W6JH0 result arm). 1 FAILS:
//!    [`a_receiver_bracket_types_a_bare_return_in_the_bodys_terms`] — the result is typed at
//!    the callee's parameter, which the receiver's entry has just bound, one `Option` too deep.
//!
//! Every row fails under at least one part but four, which pass either way by design and
//! say so at their sites: [`a_let_annotation_naming_another_parameter_is_refused`],
//! [`a_lacks_constraint_on_a_parameter_refuses_the_same_callback`],
//! [`a_lambda_annotation_naming_the_sorts_parameter_is_this_instance`] (it ran before: the
//! body pins nothing, so the parameter's flexible variable did no harm there) and
//! [`a_recursive_call_writing_its_own_parameter_runs`].
//!
//! ROWS ELSEWHERE THAT MOVED WITH PART 5, each changed at its site: the arm rows of
//! `wi_7tn1q_occurs_check_sort_alias_test` (a bracket value mentioning the parameter it
//! binds) are written in a namespace nested in the sort, where the parameter is still not
//! the body's own and the binding still cyclic — in the sort's own operation the same text
//! is the call at another instance this file drives; and `wi_0rp29_nested_projection_value_
//! in_type_test`'s `[EffP = {R}]` case is refused by the bracket's own row, before the
//! argument that used to refuse it.
//!
//! NOT COVERED, measured and left — a gap of its own, and not about type parameters: a
//! MULTI-parameter lambda's per-binder annotations are not its binders' types when no
//! arrow is expected. `let f = lambda (a: Int64, b: String) -> a` followed by `f(1, 2)`
//! loads, as does `lambda (a: T, b: T) -> a` applied to a `T` and a `U`: each binder takes
//! its type from the context (an inference variable), and the annotation is only compared.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

// ── The four spellings ──────────────────────────────────────────────────────

/// AN OPERATION'S OWN TYPE PARAMETER: `same[T](y: T) -> T = let x: T = y  x`. It was
/// refused `expected ?T, got ?T` — the two rendering alike and not being one type.
#[test]
fn a_let_annotation_naming_the_operations_parameter_is_that_parameter() {
    let src = r#"
namespace wi89wzr.op1
  import anthill.prelude.{Int64}
  operation same[T](y: T) -> T =
    let x: T = y
    x
  operation go() -> Int64 = same(7)
end
"#;
    assert_eq!(run_src(src, "wi89wzr.op1.go"), Ok(7));
}

/// THE PARAMETER INSIDE A WRITTEN TYPE: `let xs: List[T = T] = cons(head: y, tail: nil)`.
/// It was refused `expected List[T = ?T], got List[T = ?T]`. (The list LITERAL `[y]` in the
/// same place loaded before the fix: the annotation is the literal's expected type and its
/// element then took the annotation's variable.)
#[test]
fn a_let_annotation_naming_the_parameter_inside_a_type_is_that_parameter() {
    let src = r#"
namespace wi89wzr.op2
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{cons, nil}
  operation single[T](y: T) -> List[T = T] =
    let xs: List[T = T] = cons(head: y, tail: nil)
    xs
  operation go() -> Int64 = List.length(single(5))
end
"#;
    assert_eq!(run_src(src, "wi89wzr.op2.go"), Ok(1));
}

/// AN OPERATION'S OWN PARAMETER INSIDE A SORT: `keep[U](b: Box, u: U) -> U`, where the
/// bridge holds the sort's parameter and the operation's.
#[test]
fn a_let_annotation_naming_an_operations_parameter_inside_a_sort_is_that_parameter() {
    let src = r#"
namespace wi89wzr.op3
  import anthill.prelude.{Int64, String}
  sort Box
    sort T = ?
    entity box(v: T)
    operation keep[U](b: Self, u: U) -> U =
      let x: U = u
      x
  end
  operation go() -> Int64 = Box.keep(box(v: "s"), 9)
end
"#;
    assert_eq!(run_src(src, "wi89wzr.op3.go"), Ok(9));
}

/// THE ENCLOSING SORT'S PARAMETER, WRITTEN BY ITS NAME: `get(b: Box) -> T = let x: T = b.v
/// x`. The loader lowers that name to a reference to the parameter, not to its variable, so
/// this spelling goes through the bridge's other half. It was refused `expected T, got ?T`.
#[test]
fn a_let_annotation_naming_the_sorts_parameter_is_that_parameter() {
    let src = r#"
namespace wi89wzr.sort1
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity box(v: T)
    operation get(b: Box[T = T]) -> T =
      let x: T = b.v
      x
  end
  operation go() -> Int64 = Box.get(box(v: 11))
end
"#;
    assert_eq!(run_src(src, "wi89wzr.sort1.go"), Ok(11));
}

/// …AND INSIDE A WRITTEN TYPE: `let same: Box[T = T] = b`, the form `Self` stands for
/// (proposal 070 §1.2; `wi_80zv8_self_test` drives the `Self` spelling).
#[test]
fn a_let_annotation_naming_the_sort_at_its_own_parameter_is_this_instance() {
    let src = r#"
namespace wi89wzr.sort2
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity box(v: T)
    operation get(b: Box[T = T]) -> T =
      let same: Box[T = T] = b
      same.v
  end
  operation go() -> Int64 = Box.get(box(v: 13))
end
"#;
    assert_eq!(run_src(src, "wi89wzr.sort2.go"), Ok(13));
}

// ── What stays refused ──────────────────────────────────────────────────────

/// A WRONG ANNOTATION IS STILL REFUSED, naming both parameters: `let x: T = u` with `u: U`.
/// CONTROL — passes with or without the change by design: both readings relate two
/// different parameters, and the renderings are the parameters' names either way.
#[test]
fn a_let_annotation_naming_another_parameter_is_refused() {
    let src = r#"
namespace wi89wzr.wrong1
  import anthill.prelude.{Int64}
  operation mixup[T, U](t: T, u: U) -> T =
    let x: T = u
    x
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["x.annotation (let-binding): expected ?T, got ?U"],
        "`let x: T = u` with `u: U`",
    );
}

/// The `-R` fixture: `g` may raise `Error[Foo]`, and `R` is the operation's own row, so
/// nothing shows that `g` lacks it. `use_body` is `use`'s body.
fn lacks_program(ns: &str, extra: &str, use_body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, Error}}
  sort Foo
    entity foo
  end
{extra}
  operation use[R](g: (x: Int64) -> Bool @ {{Error[Foo]}}, w: (x: Int64) -> Bool @ {{R}}) -> Bool effects {{Error[Foo], R}} =
{use_body}
end
"#
    )
}

/// A `-R` IN A `let` ANNOTATION IS THE OPERATION'S `R`: `let h: (x: Int64) -> Bool @
/// {Error[Foo], -R} = g` claims `g` lacks the operation's own row, which nothing shows — `R`
/// may be instantiated to `{Error[Foo]}`. It LOADED (MEASURED): the annotation's `R` was a
/// row variable of its own. The refusal prints both rows, which is the renderer's half of
/// this ticket: an arrow's row is not otherwise rendered, and the pair read `expected Int64
/// -> Bool, got Int64 -> Bool`.
#[test]
fn a_lacks_constraint_in_a_let_annotation_is_the_operations_own_row() {
    let src = lacks_program(
        "wi89wzr.lacks1",
        "",
        "    let h: (x: Int64) -> Bool @ {Error[Foo], -R} = g\n    h(1)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &[
            "h.annotation (let-binding)",
            "expected Int64 -> Bool @ {-?R, Error[T = Foo]}",
            "got Int64 -> Bool @ {Error[T = Foo]}",
        ],
        "`-R` in a let annotation",
    );
}

/// CONTROL — its PARAMETER twin, refused before and after: the same callback handed to a
/// parameter requiring `-R`. Passes with or without the change by design; it is what the
/// row above is now refused "as".
#[test]
fn a_lacks_constraint_on_a_parameter_refuses_the_same_callback() {
    let src = lacks_program(
        "wi89wzr.lacks2",
        "  operation needs[R](h: (x: Int64) -> Bool @ {Error[Foo], -R}, w: (x: Int64) -> Bool @ {R}) -> Bool effects {Error[Foo], R} = h(1)",
        "    needs(g, w)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["needs.h (op-arg)", "to lack the row `?R`"],
        "`-R` on a parameter",
    );
}

// ── One binder of a destructuring `let` ─────────────────────────────────────

fn binder_program(ns: &str, binder_ty: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  operation firstOf[T, U](y: T, z: U) -> T =
    let (a: {binder_ty}, b) = (y, 1)
    a
  operation go() -> Int64 = firstOf(8, "s")
end
"#
    )
}

/// ONE BINDER'S ANNOTATION NAMING A PARAMETER IS HELD TO IT: `let (a: T, b) = (y, 1)` with
/// `y: T` runs, and `a: U` there is refused naming both parameters. The per-binder check
/// compared only CONCRETE types, so the false `a: U` loaded (MEASURED); it now reads the
/// annotation at the body's rigids and compares two of the body's own parameters as it
/// compares two concrete types.
#[test]
fn a_binder_annotation_naming_a_parameter_is_held_to_it() {
    assert_eq!(
        run_src(&binder_program("wi89wzr.bind1", "T"), "wi89wzr.bind1.go"),
        Ok(8)
    );
    assert_refused_naming(
        &load_errors(&binder_program("wi89wzr.bind2", "U")),
        &["<binder>.a (binder-annotation): expected ?T, got ?U"],
        "`let (a: U, b) = (y, 1)` with `y: T`",
    );
}

// ── A binder typed by its annotation alone ──────────────────────────────────

/// A LAMBDA PARAMETER'S ANNOTATION IS THE PARAMETER TOO, and the body is held to it: `lambda
/// (x: T) -> x` is the identity at `T` and runs, while a body that pins `T` — `x + 1` — is
/// refused, as an operation body that pins its parameter is (§8.1). The annotation was the
/// parameter's FLEXIBLE variable, so the second lambda loaded, typed `(Int64) -> Int64`
/// under an annotation saying `T`.
#[test]
fn a_lambda_annotation_naming_the_parameter_holds_its_body_to_it() {
    let ok = r#"
namespace wi89wzr.lam1
  import anthill.prelude.{Int64}
  operation via[T](y: T) -> T =
    let f = lambda (x: T) -> x
    f(y)
  operation go() -> Int64 = via(21)
end
"#;
    assert_eq!(run_src(ok, "wi89wzr.lam1.go"), Ok(21));
    let pinned = r#"
namespace wi89wzr.lam2
  import anthill.prelude.{Int64}
  operation via[T](y: T) -> Int64 =
    let f = lambda (x: T) -> x + 1
    f(5)
end
"#;
    assert_refused_naming(
        &load_errors(pinned),
        &["add.b (op-arg): expected ?T, got Int64"],
        "`lambda (x: T) -> x + 1` pins the operation's own parameter",
    );
}

/// …AND SO IS ONE NAMING THE ENCLOSING SORT'S PARAMETER, by its name or through `Self`:
/// inside `sort Box`, `lambda (x: T) -> x` and `lambda (b: Self) -> b` are identities at
/// this instance.
#[test]
fn a_lambda_annotation_naming_the_sorts_parameter_is_this_instance() {
    let src = r#"
namespace wi89wzr.lam3
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity box(v: T)
    operation content(b: Self) -> T =
      let f = lambda (x: T) -> x
      let g = lambda (c: Self) -> c
      f(g(b).v)
  end
  operation go() -> Int64 = Box.content(box(v: 17))
end
"#;
    assert_eq!(run_src(src, "wi89wzr.lam3.go"), Ok(17));
}

// ── A call-site bracket ─────────────────────────────────────────────────────

fn bracket_program(ns: &str, bracket: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  operation id[A](x: A) -> A = x
  operation pick[T, U](y: T, z: U) -> T = id[A = {bracket}](y)
  operation go() -> Int64 = pick(7, "s")
end
"#
    )
}

/// A BRACKET NAMING THE CALLER'S PARAMETER IS HELD TO IT: `id[A = U](y)` with `y: T` is
/// refused naming both parameters. It LOADED (MEASURED): the bracket's `U` was the
/// parameter's flexible variable, which the argument then pinned to `T` — the bracket said
/// nothing. The true one, `id[A = T](y)`, runs; that half is a CONTROL and passes either way.
#[test]
fn a_bracket_naming_the_callers_parameter_is_held_to_it() {
    assert_eq!(
        run_src(&bracket_program("wi89wzr.br1", "T"), "wi89wzr.br1.go"),
        Ok(7)
    );
    assert_refused_naming(
        &load_errors(&bracket_program("wi89wzr.br2", "U")),
        &["id.x (op-arg): expected ?U, got ?T"],
        "`id[A = U](y)` with `y: T`",
    );
}

/// `Strm.each[EffP](s, f: … @ {EffP, -s.E})` called from `use[R]` over `s: Strm[E = {R}]` with
/// a pure callback; `call` is the call as written.
fn row_bracket_program(ns: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64}}
  sort Strm
    sort T = ?
    effects E = ?
    operation each[EffP](s: Self, f: (x: Int64) -> Bool @ {{EffP, -s.E}}) -> Bool effects {{EffP}} = true
  end
  operation pure1(x: Int64) -> Bool = true
  operation use[R](s: Strm[T = Int64, E = {{R}}]) -> Bool effects {{R}} = {call}
end
"#
    )
}

/// A ROW WRITTEN IN A BRACKET IS THE OPERATION'S OWN ROW: `Strm.each[EffP = {R}](s, pure1)`
/// makes the callback's row `{R, -R}` — it admits what `-s.E` says it lacks, which is
/// uninhabitable (WI-20260929-0RP29's row decision; its written twin is that file's
/// `a_row_holding_a_variable_it_lacks_is_uninhabitable`). It LOADED (MEASURED): the bracket's
/// `R` was a row variable of its own, which the pure callback then emptied, so the call
/// charged nothing where it was told to charge `R`. The bracket-less call — CONTROL, passes
/// either way — loads: nothing there says the callback raises `R`.
#[test]
fn a_row_bracket_naming_the_callers_row_charges_it() {
    assert_refused_naming(
        &load_errors(&row_bracket_program(
            "wi89wzr.br3",
            "Strm.each[EffP = {R}](s, pure1)",
        )),
        &["each.f (op-arg)", "both admit and lack `?R`"],
        "`[EffP = {R}]` over `s: Strm[E = {R}]`",
    );
    let errs = load_errors(&row_bracket_program("wi89wzr.br4", "Strm.each(s, pure1)"));
    assert!(errs.is_empty(), "the bracket-less call: {errs:#?}");
}

/// A CALL AT ANOTHER INSTANCE IS WRITTEN IN TERMS OF THIS ONE: inside `sort Box[T]`,
/// `Box.empty[T = Option[T = T]]()` and `Box[T = Option[T = T]].empty()` are `empty` at the
/// instance whose element is an `Option` of this body's `T`. Both were refused — the callee's
/// `T` and this instance's were one variable, so the binding was cyclic
/// (WI-20260911-7TN1Q's refusal, which a bracket written where `T` is not the body's own
/// parameter still gets: that file's arm rows).
#[test]
fn a_bracket_at_another_instance_is_written_in_terms_of_this_one() {
    let src = r#"
namespace wi89wzr.br5
  import anthill.prelude.{Int64, Option, none, some}
  sort Box[T]
    entity box(v: T)
    operation empty() -> Option[T = T] = none()
    operation viaCallee(b: Self) -> Option[T = Option[T = T]] = Box.empty[T = Option[T = T]]()
    operation viaReceiver(b: Self) -> Option[T = Option[T = T]] = Box[T = Option[T = T]].empty()
  end
  operation tag(o: Option[T = Option[T = Int64]]) -> Int64 =
    match o
      case none() -> 3
      case some(_) -> 4
  operation go() -> Int64 = tag(Box.viaCallee(box(v: 1))) + tag(Box.viaReceiver(box(v: 1)))
end
"#;
    assert_eq!(run_src(src, "wi89wzr.br5.go"), Ok(6));
}

/// … AND A RECEIVER'S OWN TYPE IS READ THE SAME WAY: `Bag[T = Option[T = T]].empty()` is
/// typed by what the receiver wrote (WI-20260829-W6JH0) — at this body's `T`, not at the
/// callee's, which the receiver's own entry has just bound to that `Option`.
///
/// `empty` returned the sort BARE when this row was written (`-> Bag`), and the receiver's
/// type typed that bare return. Since proposal 070 a bare return is a `Bag` the operation
/// picks, not this instance; `-> Self` is the instance the row is about, and it is the
/// receiver's bracket that fixes it.
#[test]
fn a_receiver_bracket_types_the_return_in_the_bodys_terms() {
    let src = r#"
namespace wi89wzr.br6
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.List.{cons, nil}
  sort Bag[T]
    entity bag(items: List[T = T])
    operation empty() -> Self = bag(items: nil)
    operation nested(b: Self) -> Bag[T = Option[T = T]] = Bag[T = Option[T = T]].empty()
  end
  operation count(b: Bag[T = Option[T = Int64]]) -> Int64 = List.length(b.items)
  operation go() -> Int64 = count(Bag.nested(bag(items: cons(head: 1, tail: nil)))) + 9
end
"#;
    assert_eq!(run_src(src, "wi89wzr.br6.go"), Ok(9));
}

/// CONTROL — a recursive call writing its own parameter in the bracket, `rec[T = T](y, n -
/// 1)`: the value IS the parameter. Passes with or without the change by design.
#[test]
fn a_recursive_call_writing_its_own_parameter_runs() {
    let src = r#"
namespace wi89wzr.br7
  import anthill.prelude.{Int64}
  operation rec[T](y: T, n: Int64) -> T =
    match n
      case 0 -> y
      case _ -> rec[T = T](y, n - 1)
  operation go() -> Int64 = rec(7, 3)
end
"#;
    assert_eq!(run_src(src, "wi89wzr.br7.go"), Ok(7));
}
