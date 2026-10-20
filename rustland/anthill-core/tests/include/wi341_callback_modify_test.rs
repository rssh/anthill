//! WI-341 (loader binder context) + WI-360 (end-to-end callback `Modify`
//! propagation). A callback parameter whose arrow effect modifies its OWN param
//! — `f: (a: Cell) -> Unit @ Modify[a]` — now LOADS: the binder `a` resolves to
//! the registered `CallbackParam` place `<op>.f.a` (it used to fail as
//! `UnresolvedName "a"`). Applied over a list element, that latent `Modify[f.a]`
//! flows to the op boundary, where the WI-353 classifier re-keys it via the
//! WI-352 flow facts and surfaces `Modify[l]` — the full pipeline, from source.

/// Load stdlib + user source together (the path the effect check runs on) and
/// surface load errors as strings rather than panicking.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    crate::common::try_load_kb_with(source).map(|_| ())
}

/// A `foreach` whose callback modifies the element it is handed. `?decl` is the
/// op-level effects clause (empty, or `effects Modify[l]`).
fn each_src(decl: &str) -> String {
    format!(
        r#"
namespace anthill.test.wi341
  import anthill.prelude.{{List, Unit, Cell}}
  import anthill.prelude.List.{{cons, nil}}

  operation each(l: List[T = Cell], f: (a: Cell) -> Unit @ Modify[a]) -> Unit{decl} =
    match l
      case nil() -> ()
      case cons(h, rest) -> f(h)
end
"#
    )
}

#[test]
fn callback_modify_arrow_param_loads() {
    // The headline WI-341 fix: a callback arrow effect referencing its OWN param
    // (`Modify[a]`) must LOAD — `a` resolves to the place `each.f.a`, not
    // `UnresolvedName "a"`. With the surfaced `Modify[l]` declared, it is clean.
    let errs = load_result(&each_src(" effects Modify[l]"));
    assert!(
        errs.is_ok(),
        "callback `Modify[a]` must load (binder `a` -> place each.f.a) and, with \
         `effects Modify[l]` declared, type clean; got: {:#?}",
        errs.err()
    );
}

#[test]
fn callback_element_modify_surfaces_on_list_from_source() {
    // The WI-360 acceptance, end-to-end: without the declaration, the modify on
    // the element callback must surface as `Modify[l]` at the boundary and be
    // reported undeclared — proving the full pipeline (binder->place ->
    // body row Modify[f.a] -> WI-352 flow -> WI-353 re-key -> Modify[l]) fired.
    let errs = load_result(&each_src(""))
        .expect_err("a foreach whose callback modifies its element must surface Modify[l]");
    assert!(
        errs.iter().any(|e| e.contains("Modify") && e.contains('l')),
        "expected an undeclared `Modify[l]` effect error (the surfaced, re-keyed \
         label); got: {:#?}",
        errs,
    );
}

#[test]
fn arrow_param_name_colliding_with_type_param_is_not_captured() {
    // WI-341 over-capture guard: the binder scope must apply ONLY to the arrow's
    // effect labels, not its param/return TYPE positions. Here the arrow param
    // `a` shares a name with the op type-param `a`; `(a: a) -> a` must type as the
    // type-param (so `f(v)` checks), not capture the type `a` to the place `f.a`.
    let src = r#"
namespace anthill.test.wi341collide
  import anthill.prelude.{Unit}

  operation apply_id[a](v: a, f: (a: a) -> a) -> a = f(v)
end
"#;
    load_result(src).expect(
        "an arrow param name colliding with a type-param must not corrupt the \
         arrow's param/return types",
    );
}

#[test]
fn non_modifying_callback_needs_no_effect() {
    // Control: a callback with no effect surfaces nothing — `each` stays pure and
    // needs no declaration. (Guards against the binder context spuriously
    // minting an effect.)
    let src = r#"
namespace anthill.test.wi341pure
  import anthill.prelude.{List, Unit, Cell}
  import anthill.prelude.List.{cons, nil}

  operation each(l: List[T = Cell], f: (a: Cell) -> Unit) -> Unit =
    match l
      case nil() -> ()
      case cons(h, rest) -> f(h)
end
"#;
    load_result(src).expect("a non-modifying callback must leave `each` pure");
}

// ── A feed the flow pass does not follow is KEPT, never dropped ────────────────
//
// The boundary classifier drops a callback parameter's `Modify` whose sources are
// all fresh and non-escaping. It used to read "the flow pass saw no feed" the same
// way, so each op below loaded typed PURE while it wrote a cell its caller holds
// (MEASURED on the tree before the change: `use_first` and `use_alias` loaded
// clean, `walk` reported `Modify[z]` and not `Modify[l]`, `mk_one` loaded clean).
// Now a place counts as fed only by what the pass followed when it carries a
// `traced` fact, and an untraced one is kept on every input and on the result.
// MEASURED back-outs: with the whole change out, each `*_is_kept` test and
// `an_untraced_feed_is_charged_only_to_inputs_a_modify_can_fire_on` FAIL; each
// `*_declared` test passes either way by design (the coarse answer is declarable).
// `a_thunks_output_that_stays_local_drops_while_it_counts_as_fresh` passes with the
// whole change out (that drop is old behaviour) and FAILS with only `traced` not
// asserted, or with only a `() -> T` callback not read as callable — it is the
// control that a traced place still drops. With only the fresh-output rule for an
// untraced result out, `a_fresh_output_returned_inside_a_constructor_is_kept` fails;
// with only the type gate out, the `…charged_only_to_inputs…` test does.

/// The labels a load reported as undeclared, as written (`Modify[T = l]`).
fn undeclared(src: &str) -> std::collections::BTreeSet<String> {
    let errs = load_result(src).expect_err("the op must be refused for an undeclared effect");
    let labels: std::collections::BTreeSet<String> = errs
        .iter()
        .filter_map(|e| e.split("got undeclared effect: ").nth(1))
        .map(|l| l.trim().to_string())
        .collect();
    assert!(!labels.is_empty(), "no undeclared-effect error among: {errs:#?}");
    labels
}

fn labels(names: &[&str]) -> std::collections::BTreeSet<String> {
    names.iter().map(|n| format!("Modify[T = {n}]")).collect()
}

/// The callback is handed what an ordinary call returned — here an element of
/// `l` or `d` itself. The pass does not follow a call's result, so `f.a` is
/// untraced and the label stays on both inputs.
fn use_first_src(decl: &str) -> String {
    format!(
        r#"
namespace anthill.test.wi341untraced.first
  import anthill.prelude.{{Int64, Unit, Cell, Modify, List}}
  operation first(l: List[T = Cell[V = Int64]], d: Cell[V = Int64]) -> Cell[V = Int64] =
    match l
      case cons(h, _) -> h
      case nil() -> d
  operation use_first(l: List[T = Cell[V = Int64]], d: Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Unit{decl} =
    f(first(l, d))
end
"#
    )
}

#[test]
fn a_callback_fed_a_call_result_is_kept() {
    assert_eq!(undeclared(&use_first_src("")), labels(&["d", "l"]));
}

#[test]
fn a_callback_fed_a_call_result_declared() {
    load_result(&use_first_src(" effects {Modify[l], Modify[d]}")).expect("declared, it loads");
}

/// The callback is applied through a `let` alias. The pass sees `k(h)` as no
/// application of `f`, and `f` read as a value escapes: all of its places are
/// untraced.
fn use_alias_src(decl: &str) -> String {
    format!(
        r#"
namespace anthill.test.wi341untraced.alias
  import anthill.prelude.{{Int64, Unit, Cell, Modify, List}}
  operation use_alias(l: List[T = Cell[V = Int64]], d: Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Unit{decl} =
    let k = f
    match l
      case cons(h, _) -> k(h)
      case nil() -> k(d)
end
"#
    )
}

#[test]
fn a_callback_applied_through_an_alias_is_kept() {
    assert_eq!(undeclared(&use_alias_src("")), labels(&["d", "l"]));
}

#[test]
fn a_callback_applied_through_an_alias_declared() {
    load_result(&use_alias_src(" effects {Modify[l], Modify[d]}")).expect("declared, it loads");
}

/// The coarse answer is charged only to inputs a `Modify` can fire on: a
/// modifiable sort (`d: Cell`), a type argument that is one (`l: List[T =
/// Cell]`), a data sort whose field is one (`w: Wrap`), a type parameter (`z:
/// Acc` — it may be a `Cell`). Never `n: Int64`, `ns: List[T = Int64]` or `k:
/// Function[…]`: charging those made an op declare `Modify[n]` on an `Int64`,
/// which then spread to every caller (MEASURED before the gate). FAILS with the
/// type gate backed out (the last three come back) and with the change backed
/// out (the op loads clean).
#[test]
fn an_untraced_feed_is_charged_only_to_inputs_a_modify_can_fire_on() {
    let src = r#"
namespace anthill.test.wi341untraced.gate
  import anthill.prelude.{Int64, Unit, Cell, Modify, List, Function}
  sort Wrap
    entity wrap(rep: Cell[V = Int64])
  end
  operation first(l: List[T = Cell[V = Int64]], d: Cell[V = Int64]) -> Cell[V = Int64] =
    match l
      case cons(h, _) -> h
      case nil() -> d
  operation gate[Acc](l: List[T = Cell[V = Int64]], d: Cell[V = Int64], z: Acc, n: Int64, ns: List[T = Int64], w: Wrap, k: Function[A = Int64, B = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Unit =
    f(first(l, d))
end
"#;
    assert_eq!(undeclared(src), labels(&["d", "l", "w", "z"]));
}

/// A result typed by a type variable may be a `Cell` at a call, so the escaping
/// accumulator's `Modify[result]` is kept beside the seed's `Modify[z]`. FAILS with
/// the type-variable arm of `result_type_admits_region` backed out: only `Modify[z]`
/// was reported (MEASURED, 2026-10-16) — the variable fell through to the functor
/// test and read as "cannot carry a region". (No `*_declared` twin: an op declaring
/// `Modify[z]` must be handed a place for `z` at its own recursive call, and a
/// `let`-bound step is then charged `Modify[acc]` — the same for a `Cell` fold, and
/// not this rule's.)
#[test]
fn a_type_variable_result_keeps_the_escaping_modify() {
    let src = r#"
namespace anthill.test.wi341untraced.generic
  import anthill.prelude.{Int64, Unit, Cell, Modify, List}
  operation fold_g[Acc](xs: List[T = Cell[V = Int64]], z: Acc, f: (a: Acc, t: Cell[V = Int64]) -> Acc @ Modify[a]) -> Acc =
    match xs
      case nil() -> z
      case cons(h, rest) -> fold_g(rest, f(z, h), f)
end
"#;
    assert_eq!(undeclared(src), labels(&["result", "z"]));
}

/// The recursion hands the accumulator `z` an ordinary call's result, so `z` is
/// untraced, and so is `f.a`, which `z` feeds: `Modify[l]` as well as `Modify[z]`.
#[test]
fn an_untraced_value_carried_by_the_recursion_is_kept() {
    let src = r#"
namespace anthill.test.wi341untraced.walk
  import anthill.prelude.{Int64, Unit, Cell, Modify, List}
  operation first(l: List[T = Cell[V = Int64]], d: Cell[V = Int64]) -> Cell[V = Int64] =
    match l
      case cons(h, _) -> h
      case nil() -> d
  operation walk(l: List[T = Cell[V = Int64]], z: Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Unit =
    match l
      case nil() -> f(z)
      case cons(_, t) -> walk(t, first(l, z), f)
end
"#;
    assert_eq!(undeclared(src), labels(&["l", "z"]));
}

/// A `() -> T` callback is a callback: `mk()` is its fresh output, which `f`
/// writes and the op returns — `Modify[result]`. It used to read as "not
/// callable" (its argument places are empty), so `c` had no origin at all.
fn mk_one_src(decl: &str) -> String {
    format!(
        r#"
namespace anthill.test.wi341untraced.thunk
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  operation mk_one(mk: () -> Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Cell[V = Int64]{decl} =
    let c = mk()
    let _ = f(c)
    c
end
"#
    )
}

#[test]
fn a_thunks_output_written_and_returned_is_kept() {
    assert_eq!(undeclared(&mk_one_src("")), labels(&["result"]));
}

#[test]
fn a_thunks_output_written_and_returned_declared() {
    load_result(&mk_one_src(" effects Modify[result]")).expect("declared, it loads");
}

/// The written fresh output leaves inside a constructed value. The pass does not
/// follow what a constructor holds, so `result` is untraced and the fresh output
/// may be in it.
#[test]
fn a_fresh_output_returned_inside_a_constructor_is_kept() {
    let src = r#"
namespace anthill.test.wi341untraced.cons
  import anthill.prelude.{Int64, Unit, Cell, Modify, List}
  import anthill.prelude.List.{cons, nil}
  operation mk_list(mk: () -> Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> List[T = Cell[V = Int64]] =
    let c = mk()
    let _ = f(c)
    cons(c, nil())
end
"#;
    assert_eq!(undeclared(src), labels(&["result"]));
}

/// What a traced drop still is: every feed traced, the result traced and holding
/// only `d`, and `f.a` fed only `mk`'s result — which counts as FRESH. That is an
/// assumption, not evidence (`flow_derive`'s module doc): a `mk` returning a cell
/// its closure holds makes this op write a caller's cell while typed pure. This
/// pins today's verdict under it; when a callback's result stops counting as
/// fresh, this op is refused and the test flips.
#[test]
fn a_thunks_output_that_stays_local_drops_while_it_counts_as_fresh() {
    let src = r#"
namespace anthill.test.wi341untraced.local
  import anthill.prelude.{Int64, Unit, Cell, Modify}
  operation use_fresh(d: Cell[V = Int64], mk: () -> Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Cell[V = Int64] =
    let c = mk()
    let _ = f(c)
    d
end
"#;
    load_result(src).expect("a written fresh value that does not escape owes no declaration");
}

/// A CONSTRUCTOR applied to nothing holds no value a callback wrote, in every spelling an
/// operation body gives it — `tok`, `tok()`, `Tok.tok`, an eponymous `Tok` — at the body's
/// tail and as a callback's argument. `holds_no_value` read a bare name off `Ref`/`Ident` by
/// `kind_of`; a body writes a bare name as `VarRef`, and an eponymous constructor's kind is its
/// sort's. So the bare tail was refused `undeclared effect: Modify[T = result]` where `tok()`
/// loaded, and `f(tok)` charged the callback's `Modify` to the unrelated input `c` (MEASURED).
///
/// BACK-OUT: the `VarRef` spelling dropped from `holds_no_value` fails the bare, the eponymous
/// and the callback-argument rows; reading the kind by `kind_of` again fails the eponymous one.
/// `tok()` passes either way by design: an applied constructor is a `Constructor` node.
#[test]
fn a_bare_constructor_holds_no_value_in_every_spelling() {
    for (ns, sort_body, tail) in [
        ("bare", "entity tok", "tok"),
        ("applied", "entity tok", "tok()"),
        ("qualified", "entity tok", "Tok.tok"),
        ("eponymous", "entity Tok", "Tok"),
    ] {
        let src = format!(
            r#"
namespace anthill.test.wi341noval.{ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify, Modifiable}}
  sort Tok
    provides Modifiable[T = Self]
    {sort_body}
  end
  operation use_fresh(mk: () -> Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Tok =
    let c = mk()
    let _ = f(c)
    {tail}
end
"#
        );
        if let Err(errs) = load_result(&src) {
            panic!("{ns}: a constructor at the tail holds no written value; got: {errs:#?}");
        }
    }
    let src = r#"
namespace anthill.test.wi341noval.cbarg
  import anthill.prelude.{Int64, Unit, Cell, Modify, Modifiable}
  sort Tok
    provides Modifiable[T = Self]
    entity tok
  end
  operation feed_tok(c: Cell[V = Int64], f: (a: Tok) -> Unit @ Modify[a]) -> Unit =
    f(tok)
end
"#;
    load_result(src).expect("a constructor handed to a callback is no input of the caller's");
}
