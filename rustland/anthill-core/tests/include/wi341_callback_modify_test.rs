//! WI-341 (loader binder context) + WI-360 (end-to-end callback `Modify`
//! propagation). A callback parameter whose arrow effect modifies its OWN param
//! — `f: (a: Cell) -> Unit @ Modify[a]` — now LOADS: the binder `a` resolves to
//! the registered `CallbackParam` place `<op>.f.a` (it used to fail as
//! `UnresolvedName "a"`). Applied to a list element `h`, the write is `h`'s, read
//! at the application as a named call's parameter is read at its argument (050.1
//! §5.2, WI-20261014-7EZS6), and charged `Modify[l]` where `h`'s scope ends.

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
    // reported undeclared — proving the full pipeline (binder->place -> row
    // Modify[f.a] -> `Modify[h]` at `f(h)` -> `Modify[l]` at the arm's end) fired.
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

// ── A callback's write is read at its argument, as a named call's is ───────────
//
// Applying `f` reads its row's own parameters at the arguments (050.1 §5.2,
// WI-20261014-7EZS6): `f(y)` is `Modify[y]`, charged where `y`'s scope ends, as
// `put(y, 5)` is over `put(c: Cell[V = Int64], n: Int64) effects Modify[c]`. Each
// program below is run beside that twin, the named call where it applies `f`, and the
// two give one verdict. Before, `Modify[f.a]` stayed in the row to the boundary, where
// the flow facts (WI-352/353) charged it: onto every modifiable input where their pass
// had not followed a feed. Since no application leaves the label there, the rows of
// that arm's own rules are `kb::region::wi353_tests`, moved from here.
//
// Where the twin's verdict is not the program's meaning — a call's or a thunk's result
// may be a cell of the caller's, and nothing says so — both are WI-20261016-HE2J6's,
// and the row says so; it flips with that ticket.
//
// BACK-OUT (each part of WI-20261014-7EZS6 alone, by a temporary switch, MEASURED): the
// application's re-key off fails the two `HE2J6` rows, `walk`'s, `fold_g`'s and the
// constant's (its `let` spelling charged `Modify[c]` again) — the flow facts' old
// answers; a written callback arrow's binders not read off its places fails those five
// and `a_callback_fed_a_call_result_names_no_place`; the refusal of an argument naming
// no place off fails that row and the constant's (`f(tok)` loads). The alias rows and
// the fresh local's drop pass either way by design: the flow facts answered them alike.

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

fn put_src() -> &'static str {
    "  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =\n    let _ = Cell.set(c, n)\n    n\n"
}

/// `first` returns an element of `l` or `d` itself, and declares no memory clause.
fn first_src() -> &'static str {
    "  operation first(l: List[T = Cell[V = Int64]], d: Cell[V = Int64]) -> Cell[V = Int64] =\n    match l\n      case cons(h, _) -> h\n      case nil() -> d\n"
}

/// A program over `put` and `first`: `ops` is the rest of the namespace.
fn program(ns: &str, ops: &str) -> String {
    format!(
        "namespace anthill.test.wi341app.{ns}\n  import anthill.prelude.{{Int64, Unit, Cell, Modify, List}}\n  import anthill.prelude.List.{{cons, nil}}\n{}{}{ops}end\n",
        put_src(),
        first_src(),
    )
}

/// The errors of a load that must be refused.
fn refusal(src: &str) -> Vec<String> {
    load_result(src).expect_err("the program must be refused")
}

/// An argument that names no place is refused at a parameter the callback's row writes,
/// whatever the operation declares, as at a named call's: there is no name to charge.
#[test]
fn a_callback_fed_a_call_result_names_no_place() {
    let callback = "(a: Cell[V = Int64]) -> Unit @ Modify[a]";
    for decl in ["", " effects {Modify[l], Modify[d]}"] {
        for (spelling, op) in [
            (
                "callback",
                format!("  operation use(l: List[T = Cell[V = Int64]], d: Cell[V = Int64], f: {callback}) -> Unit{decl} =\n    f(first(l, d))\n"),
            ),
            (
                "named",
                format!("  operation use(l: List[T = Cell[V = Int64]], d: Cell[V = Int64]) -> Int64{decl} =\n    put(first(l, d), 5)\n"),
            ),
        ] {
            let errs = refusal(&program("noplace", &op));
            assert!(
                errs.iter().any(|e| e.contains("expected an argument naming a PLACE")
                    && e.contains("Bind it first")),
                "{spelling}, declares `{decl}`: a call's result names no place; got: {errs:#?}"
            );
        }
    }
}

/// Bound by a `let`, the call's result is a name, and its write is charged as `put(y,
/// 5)`'s: `first` declares no memory clause, so its result is connected with nothing the
/// caller holds, and the write is to fresh memory. At run time it writes an element of
/// `l` or `d`: WI-20261016-HE2J6 (its program (1) is the named twin).
#[test]
fn a_callback_fed_a_bound_call_result_writes_what_its_twin_does() {
    for op in [
        "  operation use(l: List[T = Cell[V = Int64]], d: Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Unit =\n    let y = first(l, d)\n    f(y)\n",
        "  operation use(l: List[T = Cell[V = Int64]], d: Cell[V = Int64]) -> Int64 =\n    let y = first(l, d)\n    put(y, 5)\n",
    ] {
        load_result(&program("bound", op))
            .unwrap_or_else(|errs| panic!("HE2J6's verdict, today: loads; got: {errs:#?}\n{op}"));
    }
}

/// The callback applied through a `let` alias is applied: `k(h)` writes `h`, a binder of
/// `l`'s match, and `k(d)` writes `d`.
fn use_alias_src(decl: &str) -> String {
    program(
        "alias",
        &format!(
            "  operation use_alias(l: List[T = Cell[V = Int64]], d: Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Unit{decl} =\n    let k = f\n    match l\n      case cons(h, _) -> k(h)\n      case nil() -> k(d)\n"
        ),
    )
}

#[test]
fn a_callback_applied_through_an_alias_writes_each_argument() {
    assert_eq!(undeclared(&use_alias_src("")), labels(&["d", "l"]));
}

#[test]
fn a_callback_applied_through_an_alias_declared() {
    load_result(&use_alias_src(" effects {Modify[l], Modify[d]}")).expect("declared, it loads");
}

/// The recursion hands `z` what `first` returned. `walk` declares nothing, so its own
/// call incurs nothing, and `f(z)` is `Modify[z]` alone, as `put(z, 5)` is. Declared,
/// the recursive call writes its argument, bound by a `let`, and that is the
/// `bound_call_result` row's case (HE2J6).
#[test]
fn a_callback_carried_by_the_recursion_writes_its_argument() {
    let callback = "(a: Cell[V = Int64]) -> Unit @ Modify[a]";
    let callback_walk = |decl: &str, step: &str| {
        format!(
            "  operation walk(l: List[T = Cell[V = Int64]], z: Cell[V = Int64], f: {callback}) -> Unit{decl} =\n    match l\n      case nil() -> f(z)\n      case cons(_, t) -> {step}\n"
        )
    };
    let named_walk = |decl: &str, step: &str| {
        format!(
            "  operation walk(l: List[T = Cell[V = Int64]], z: Cell[V = Int64]) -> Int64{decl} =\n    match l\n      case nil() -> put(z, 5)\n      case cons(_, t) -> {step}\n"
        )
    };
    for op in [
        callback_walk("", "walk(t, first(l, z), f)"),
        named_walk("", "walk(t, first(l, z))"),
    ] {
        assert_eq!(undeclared(&program("walk", &op)), labels(&["z"]), "{op}");
    }
    for op in [
        callback_walk(" effects Modify[z]", "\n        let y = first(l, z)\n        walk(t, y, f)"),
        named_walk(" effects Modify[z]", "\n        let y = first(l, z)\n        walk(t, y)"),
    ] {
        load_result(&program("walkdecl", &op))
            .unwrap_or_else(|errs| panic!("HE2J6's verdict, today: loads; got: {errs:#?}\n{op}"));
    }
}

/// `f(z, h)` writes the seed. The accumulators after it are `f`'s results, connected with
/// nothing `f` was handed (its arrow writes no memory clause), so their writes are to
/// fresh memory and `result` is not charged — as over a named `step` with `Modify[a]`.
/// A step returning `t` makes the accumulator an element of `xs`: HE2J6's fold step.
#[test]
fn a_callback_fed_its_own_result_writes_only_the_seed() {
    for op in [
        "  operation fold_g[Acc](xs: List[T = Cell[V = Int64]], z: Acc, f: (a: Acc, t: Cell[V = Int64]) -> Acc @ Modify[a]) -> Acc =\n    match xs\n      case nil() -> z\n      case cons(h, rest) -> fold_g(rest, f(z, h), f)\n",
        "  operation step[Acc](a: Acc, t: Cell[V = Int64]) -> Acc effects Modify[a] = a\n  operation fold_g[Acc](xs: List[T = Cell[V = Int64]], z: Acc) -> Acc =\n    match xs\n      case nil() -> z\n      case cons(h, rest) -> fold_g(rest, step(z, h))\n",
    ] {
        assert_eq!(undeclared(&program("fold", op)), labels(&["z"]), "{op}");
    }
}

/// A thunk's output, written and returned — alone, or inside a constructed value. The
/// thunk's row is empty, so it allocates nothing: what it returns is a cell its closure
/// holds, which the operation writes with nothing declared. The regions read a call's
/// result as fresh memory, which the allocation's own `Modify[result]` covers, and the
/// named twin loads as the callback does: HE2J6's program (2).
#[test]
fn a_thunks_output_written_and_returned_writes_what_its_twin_does() {
    for tail in ["c", "cons(c, nil())"] {
        let result = if tail == "c" { "Cell[V = Int64]" } else { "List[T = Cell[V = Int64]]" };
        for write in ["f(c)", "put(c, 5)"] {
            let op = format!(
                "  operation mk(mk: () -> Cell[V = Int64], f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> {result} =\n    let c = mk()\n    let _ = {write}\n    {tail}\n"
            );
            load_result(&program("thunk", &op))
                .unwrap_or_else(|errs| panic!("HE2J6's verdict, today: loads; got: {errs:#?}\n{op}"));
        }
    }
}

/// What a write to a fresh local is: `f(c)` writes `c`, which holds `mk()`'s result —
/// fresh memory, by the same reading — and `c` is not returned, so nothing is charged.
/// That is an assumption, not evidence: a `mk` returning a cell its closure holds makes
/// this op write a caller's cell while typed pure. This pins today's verdict under it;
/// when a callback's result stops counting as fresh (WI-20261016-HE2J6), this op is
/// refused and the test flips. Passes with either part of WI-20261014-7EZS6 backed out:
/// the flow facts dropped it too.
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

/// A constructor applied to nothing is a constant and names no resource, so handing it to
/// a callback whose row writes the parameter is refused, as handing it to `touch` is. Bound
/// by a `let`, the write is the local's, which holds no memory of the caller's: it loads,
/// as `touch(t)` does. Before, the flow facts read `f(tok)` as holding no value and loaded
/// it, and charged `let t = tok; f(t)` to the unrelated input `c` (MEASURED on 29613621).
#[test]
fn a_constant_handed_to_a_callback_is_read_as_at_a_named_call() {
    let decls = "  import anthill.prelude.{Int64, Unit, Cell, Modify, Modifiable}\n  sort Tok\n    provides Modifiable[T = Self]\n    entity tok\n  end\n  operation touch(a: Tok) -> Unit effects Modify[a] = ()\n";
    let callback = "f: (a: Tok) -> Unit @ Modify[a]";
    let src = |ns: &str, param: &str, body: &str| {
        format!("namespace anthill.test.wi341noval.{ns}\n{decls}  operation feed_tok(c: Cell[V = Int64]{param}) -> Unit =\n{body}end\n")
    };
    for (spelling, param, call) in [("callback", format!(", {callback}"), "f"), ("named", String::new(), "touch")] {
        let errs = refusal(&src("bare", &param, &format!("    {call}(tok)\n")));
        assert!(
            errs.iter().any(|e| e.contains("expected an argument naming a PLACE") && e.contains("a constant")),
            "{spelling}: a constant names no resource; got: {errs:#?}"
        );
        load_result(&src("bound", &param, &format!("    let t = tok\n    {call}(t)\n")))
            .unwrap_or_else(|errs| panic!("{spelling}: a local holding a constant is no input of the caller's; got: {errs:#?}"));
    }
}
