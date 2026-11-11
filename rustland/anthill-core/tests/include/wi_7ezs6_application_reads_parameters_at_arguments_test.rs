//! WI-20261014-7EZS6 — proposal 050.1 §5.2: applying a function value reads its own parameters
//! at the arguments, as a call of an operation by name reads its parameters. `w(q)` over
//! `(z: Cell[V = Int64]) -> Int64 @ {Modify[z]}` writes `Modify[q]`, for a lambda held in a
//! `let` and for a callback parameter applied directly or through a `let` alias alike.
//!
//! Before, the application returned the function's row as its arrow writes it: a lambda's
//! `Modify[z]` reached the operation's boundary naming the lambda's binder, undeclared; a
//! callback's `Modify[w.z]` reached it naming the callback's place, where the flow facts charged
//! it to every modifiable input when `w` was read as a value. Each row drives the program: an
//! admitted one runs and its value says which cell was written; a refusal is asserted by the
//! words that name it, beside the program that differs in one thing and runs.
//!
//! BACK-OUT, each part alone, by a temporary switch over this file and the 52 suites that apply
//! a function value writing a cell (1385 rows; MEASURED):
//! - the labels over the binders re-keyed onto the arguments' places — off, every row here
//!   fails, and so do the rows those suites changed with it (review 9's two, EDPF6's, N2YEK's
//!   applied case, 809JN's lambda-parameter row) and wi341's;
//! - a written callback arrow's binders read off its places (`callback_of_place`) — off, the
//!   callback rows fail: the two alias rows, `a_callback_applied_to_a_local_cell_…`, the
//!   guarded row and the placeless row;
//! - the refusal of an argument naming no place — off, the placeless row and the whole-tuple
//!   row (`w(Cell.new(1), 5)`) fail;
//! - the guarded row's labels held as the application incurs them — off, the guarded row fails;
//! - the binder taking the whole tuple charged onto its components — off, the whole-tuple row.
//!
//! The family `e-applied-arrow` moved with the change: its 7EZS6 exceptions are gone, and the
//! verdict lines it moved are the writes now read at `q`.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

const PUT: &str = r#"
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace test.e7ezs6.{ns}\n  import anthill.prelude.{{Int64, Bool, Cell, List, Unit, String, Error}}\n  import anthill.prelude.PartialEq.{{eq}}\n{PUT}{body}\nend\n"
    )
}

fn entry(ns: &str) -> String {
    format!("test.e7ezs6.{ns}.go")
}

/// The ticket's program: a lambda writing its own parameter, held in a `let` and applied to a
/// cell `go` allocated. The write is to `r`, `go`'s own memory, which it owes nothing for.
#[test]
fn a_let_held_lambda_applied_to_a_local_cell_runs() {
    let src = program(
        "ticket",
        r#"
  operation go() -> Int64 effects {Error[String]} =
    let r: Cell[V = Int64] = Cell.new(1)
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    let n = w(r)
    n * 10 + Cell.get(r)
"#,
    );
    assert_eq!(run_int64(&src, &entry("ticket")), Ok(55));
}

/// Applied to a parameter, the lambda's write is the parameter's: refused naming `p` where
/// nothing is declared, and running where `Modify[p]` is.
#[test]
fn a_let_held_lambda_applied_to_a_parameter_writes_the_parameter() {
    let undeclared = program(
        "lambda_param",
        r#"
  operation f(p: Cell[V = Int64]) -> Int64 =
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    w(p)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&undeclared),
        &["f.effects", "undeclared effect: Modify[T = p]"],
        "the lambda's write to its parameter is a write to `p`",
    );
    let declared = program(
        "lambda_param_ok",
        r#"
  operation f(p: Cell[V = Int64]) -> Int64 effects Modify[p] =
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    w(p)
  operation go() -> Int64 =
    let c = Cell.new(1)
    let n = f(c)
    n * 10 + Cell.get(c)
"#,
    );
    assert_eq!(run_int64(&declared, &entry("lambda_param_ok")), Ok(55));
}

/// The ticket's addendum: a callback parameter applied through a `let` alias writes the cell it
/// is applied to, `q`, and not `r` beside it.
#[test]
fn a_callback_applied_through_an_alias_writes_its_argument_alone() {
    let header = r#"
  operation use[R](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {R}, w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64"#;
    let undeclared = program(
        "alias_none",
        &format!("{header} =\n    let v = w\n    v(q)\n"),
    );
    let errors = load_errors_of(&undeclared);
    assert_refused_naming(
        &errors,
        &["use.effects", "undeclared effect: Modify[T = q]"],
        "`v(q)` writes `q`",
    );
    assert!(
        !errors.join(" | ").contains("Modify[T = r]"),
        "`v(q)` writes nothing of `r`: {errors:?}"
    );
    let declared = program(
        "alias_q",
        &format!(
            "{header} effects Modify[q] =\n    let v = w\n    v(q)\n{}",
            r#"
  operation go() -> Int64 =
    let c = Cell.new(1)
    let d = Cell.new(2)
    let x = use(c, d, lambda (n: Int64) -> n, lambda (z: Cell[V = Int64]) -> put(z, 5))
    x * 100 + Cell.get(c) * 10 + Cell.get(d)
"#
        ),
    );
    assert_eq!(run_int64(&declared, &entry("alias_q")), Ok(552));
}

/// Through an alias, a callback applied to a list element writes the list, a field path's
/// argument its head, and a named argument meets the binder its label names — none of them `r`
/// beside it.
#[test]
fn a_callback_applied_through_an_alias_reads_each_argument_shape() {
    let element = program(
        "element",
        r#"
  operation use(l: List[T = Cell[V = Int64]], r: Cell[V = Int64], w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 effects Modify[l] =
    let v = w
    match l
      case nil() -> 0
      case cons(h, rest) -> v(h)
  operation go() -> Int64 =
    let c = Cell.new(1)
    let d = Cell.new(2)
    let lc = [c]
    let x = use(lc, d, lambda (z: Cell[V = Int64]) -> put(z, 5))
    x * 100 + Cell.get(c) * 10 + Cell.get(d)
"#,
    );
    assert_eq!(run_int64(&element, &entry("element")), Ok(552));
    let field = program(
        "field",
        r#"
  entity holder(c: Cell[V = Int64])
  operation use(p: holder, r: Cell[V = Int64], w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 effects Modify[p] =
    let v = w
    v(p.c)
  operation go() -> Int64 =
    let c = Cell.new(1)
    let d = Cell.new(2)
    let hc = holder(c: c)
    let x = use(hc, d, lambda (z: Cell[V = Int64]) -> put(z, 5))
    x * 100 + Cell.get(c) * 10 + Cell.get(d)
"#,
    );
    assert_eq!(run_int64(&field, &entry("field")), Ok(552));
    let named = program(
        "named",
        r#"
  operation use(p: Cell[V = Int64], r: Cell[V = Int64], w: (a: Cell[V = Int64], n: Int64) -> Int64 @ {Modify[a]}) -> Int64 effects Modify[p] =
    let v = w
    v(n: 5, a: p)
  operation go() -> Int64 =
    let c = Cell.new(1)
    let d = Cell.new(2)
    let x = use(c, d, lambda (a: Cell[V = Int64], n: Int64) -> put(a, n))
    x * 100 + Cell.get(c) * 10 + Cell.get(d)
"#,
    );
    assert_eq!(run_int64(&named, &entry("named")), Ok(552));
}

/// A callback applied to a cell its operation allocated writes the operation's own memory,
/// which it owes nothing for.
#[test]
fn a_callback_applied_to_a_local_cell_writes_nothing_of_the_callers() {
    let src = program(
        "local",
        r#"
  operation use(q: Cell[V = Int64], w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 =
    let c = Cell.new(1)
    let n = w(c)
    n * 10 + Cell.get(c) + Cell.get(q)
  operation go() -> Int64 =
    let d = Cell.new(2)
    use(d, lambda (z: Cell[V = Int64]) -> put(z, 5))
"#,
    );
    assert_eq!(run_int64(&src, &entry("local")), Ok(57));
}

/// An argument that names no place, where the function writes its parameter, is refused as a
/// call of an operation by name refuses it — for a lambda and a callback alike; the same value
/// bound by a `let` first and passed by name runs.
#[test]
fn an_argument_naming_no_place_is_refused_at_a_written_parameter() {
    for (ns, body) in [
        (
            "fresh_lambda",
            "  operation go() -> Int64 =\n    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)\n    w(Cell.new(1))\n",
        ),
        (
            "fresh_callback",
            "  operation use(w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 =\n    w(Cell.new(1))\n",
        ),
    ] {
        assert_refused_naming(
            &load_errors_of(&program(ns, body)),
            &["(op-arg)", "an argument naming a PLACE", "declares `Modify[", "Bind it first"],
            "a fresh cell handed to a parameter the function writes names no place",
        );
    }
    let bound = program(
        "fresh_bound",
        r#"
  operation go() -> Int64 =
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    let c = Cell.new(1)
    let n = w(c)
    n * 10 + Cell.get(c)
"#,
    );
    assert_eq!(run_int64(&bound, &entry("fresh_bound")), Ok(55));
}

/// A row that admits a write only under a guard holds an application to it, as it holds a call
/// of an operation by name: `w(q)` with nothing showing `b` is refused, and the same call in
/// the branch `if b` runs.
#[test]
fn a_guarded_row_holds_an_application_to_its_guard() {
    let header = r#"
  operation use(q: Cell[V = Int64], b: Bool, w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 effects {Modify[q] :- eq(b, true)} ="#;
    let unguarded = program("guard_none", &format!("{header}\n    w(q)\n"));
    assert_refused_naming(
        &load_errors_of(&unguarded),
        &["use.effects", "only where `eq(b, true)` holds", "the call of `w` incurs `Modify[T = q]`"],
        "`w(q)` writes `q` where nothing shows `b`",
    );
    let lambda_unguarded = program(
        "guard_lambda",
        r#"
  operation use(q: Cell[V = Int64], b: Bool) -> Int64 effects {Modify[q] :- eq(b, true)} =
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    w(q)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&lambda_unguarded),
        &["use.effects", "only where `eq(b, true)` holds", "the call of `w` incurs `Modify[T = q]`"],
        "the lambda's `w(q)` writes `q` where nothing shows `b`",
    );
    let guarded = program(
        "guard_if",
        &format!(
            "{header}\n    if b then w(q) else 0\n{}",
            r#"
  operation go() -> Int64 =
    let c = Cell.new(1)
    let x = use(c, true, lambda (z: Cell[V = Int64]) -> put(z, 5))
    x * 10 + Cell.get(c)
"#
        ),
    );
    assert_eq!(run_int64(&guarded, &entry("guard_if")), Ok(55));
}

/// A lambda of one binder taking the whole tuple of the application's arguments holds the
/// tuple the application builds, which lies in its components' memory: its write is `p`'s,
/// whether the components are written at the call or held in a `let`; and a component naming
/// no place is refused as an argument naming none is.
#[test]
fn a_binder_taking_the_whole_tuple_writes_its_components() {
    let lambda = "    let w = lambda (t: (Cell[V = Int64], Int64)) -> put(t._1, t._2)\n";
    let undeclared = program(
        "whole_none",
        &format!("  operation f(p: Cell[V = Int64], r: Cell[V = Int64]) -> Int64 =\n{lambda}    w(p, 5)\n"),
    );
    let errors = load_errors_of(&undeclared);
    assert_refused_naming(
        &errors,
        &["f.effects", "undeclared effect: Modify[T = p]"],
        "the whole-tuple binder's write is `p`'s",
    );
    assert!(!errors.join(" | ").contains("Modify[T = r]"), "nothing of `r`: {errors:?}");
    for (ns, call) in [("whole_args", "    w(p, 5)\n"), ("whole_let", "    let pr = (p, 5)\n    w(pr)\n")] {
        let declared = program(
            ns,
            &format!(
                "  operation f(p: Cell[V = Int64]) -> Int64 effects Modify[p] =\n{lambda}{call}{}",
                r#"
  operation go() -> Int64 =
    let c = Cell.new(1)
    let n = f(c)
    n * 10 + Cell.get(c)
"#
            ),
        );
        assert_eq!(run_int64(&declared, &entry(ns)), Ok(55), "{ns}");
    }
    let fresh = program(
        "whole_fresh",
        &format!("  operation f() -> Int64 =\n{lambda}    w(Cell.new(1), 5)\n"),
    );
    assert_refused_naming(
        &load_errors_of(&fresh),
        &["(op-arg)", "an argument naming a PLACE", "Bind it first"],
        "a fresh cell as a component of the whole tuple names no place",
    );
}

/// A join of two callbacks, applied: whichever is taken writes the cell it is applied to, `q`,
/// and nothing of `r`; where the second also writes `r`, the join owes it. Before, the flow
/// facts read `k` as two callbacks used as values and charged every input (`{q, r}`).
#[test]
fn a_join_of_two_callbacks_applied_writes_its_argument() {
    let header = |g_row: &str| {
        format!(
            "  operation use(b: Bool, q: Cell[V = Int64], r: Cell[V = Int64], f: (a: Cell[V = Int64]) -> Int64 @ {{Modify[a]}}, g: (c: Cell[V = Int64]) -> Int64 @ {{{g_row}}}) -> Int64"
        )
    };
    let body = "    let k = if b then f else g\n    k(q)\n";
    let errors = load_errors_of(&program("join_none", &format!("{} =\n{body}", header("Modify[c]"))));
    assert_refused_naming(&errors, &["use.effects", "undeclared effect: Modify[T = q]"], "`k(q)` writes `q`");
    assert!(!errors.join(" | ").contains("Modify[T = r]"), "`k(q)` writes nothing of `r`: {errors:?}");
    let errors = load_errors_of(&program(
        "join_r",
        &format!("{} effects Modify[q] =\n{body}", header("Modify[c], Modify[r]")),
    ));
    assert_refused_naming(&errors, &["use.effects", "undeclared effect: Modify[T = r]"], "`g` writes `r` too");
    let go = r#"
  operation go() -> Int64 =
    let c = Cell.new(1)
    let d = Cell.new(2)
    let x = use(false, c, d, lambda (a: Cell[V = Int64]) -> put(a, 4), lambda (z: Cell[V = Int64]) -> put(z, 5))
    x * 100 + Cell.get(c) * 10 + Cell.get(d)
"#;
    let declared = program("join_q", &format!("{} effects Modify[q] =\n{body}{go}", header("Modify[c]")));
    assert_eq!(run_int64(&declared, &entry("join_q")), Ok(552));
}
