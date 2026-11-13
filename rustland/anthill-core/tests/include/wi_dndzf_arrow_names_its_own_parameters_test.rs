//! WI-20261002-DNDZF part 1, with WI-20261014-6T5C6 — an arrow names its own parameters wherever
//! it is written, and two arrows that differ only in those names are one type
//! (kernel-language §4.4).
//!
//! `app2(q, f: (x: Cell[V = Int64]) -> Unit @ {Modify[x]})` lets its callback write the cell it
//! is handed; `appD[EffP](q, f: (x: …) -> Unit @ {EffP, -Modify[x]})` denies it. The callback is
//! `lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)`, whose row is `{Modify[k]}`.
//!
//! MEASURED before (d7ac9630): a list of that lambda and its twin over `j` was refused at its
//! second element, and so was the `if` choosing one ("expected … @ {Modify[T = k]}, got … @
//! {Modify[T = j]}"); the arrow `(x: Cell[V = Int64]) -> Unit @ {Modify[x]}` written as an
//! operation's result, an entity's field, an alias or a `let` annotation was refused
//! "unresolved name 'x'", where in an operation's parameter list it loads. Now each runs to 42
//! through `app2` and is refused through `appD` naming the absence, as the lambda written at
//! the call is.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! Each part backed out by a temporary switch, in one build, over this file's rows and the
//! suites beside it (`wi_edpf6`, `wi_1tjqh`, the four `wi_0rp29_*` files, `wi424`, `wi440`,
//! `wi441`, `wi469`, `wi698`, `wi_41yye`, `wi_450ka`, `wi_xzmgc`, `wi347`, `wi_f3fyj`: 633 rows).
//!
//! 1. A WRITTEN ARROW'S PARAMETER HAS A PLACE OUTSIDE AN OPERATION'S PARAMETER LIST
//!    (`Loader::written_arrow_places`) — none. 7 FAIL, all here: an arrow written anywhere and
//!    its refusal twin, the alias slot, the field beside a row parameter, the member and its
//!    spec, the arrow in a callback's result, the arrow nested in a callback parameter.
//! 2. … AND THE ARROW RECORDS ITS PARAMETERS (`ArrowBinderFrame::named`) — records none. 18
//!    FAIL: the same 7, and 11 beside — `wi_edpf6` 3, `wi_0rp29` 6, `wi_1tjqh` 2 — whose
//!    callback parameter's arrow is now read by the parameters it records (below).
//! 3. TWO ARROWS ARE COMPARED WITH THEIR PARAMETERS MATCHED BY POSITION
//!    (`function_parts_at_one_binders`, in unify and in subtyping) — compared as written. 8
//!    FAIL, all here: both rows of the twins, both of an arrow written anywhere, the alias slot,
//!    the member and its spec, the arrow in a callback's result, the nested arrow.
//! 4. A SLOT'S POSITIONS ARE READ OFF ITS TYPE (`declared_arrow_places`) — off the callback
//!    parameter's registered places only. 2 FAIL: the alias slot and the field beside a row
//!    parameter.
//! 5. A CALLBACK PARAMETER NAMED `result` IS REFUSED — loads. 1 FAILS:
//!    [`an_arrow_in_a_callback_result_names_its_own_parameter`].
//!
//! PASSES EITHER WAY, BY DESIGN: [`a_label_naming_a_value_in_scope_is_compared_as_it_stands`].
//!
//! DELETED, with the written arrow recording its parameters: the readers that took a callback
//! parameter's place as saying its position where the type records none (the slot check's
//! place map and its own-parameter test, and an application's re-key). Each was armed to panic
//! where it would still decide, over `anthill-core`'s suites and the families: none was reached.
//! KEPT: the same positional reading in `unify_denoted_view`, which a lacks set held in σ still
//! reaches (two `wi_1tjqh` rows: a member's callback label against its spec's).
//!
//! NOT KEPT, measured: an arrow nested in a callback parameter's arrow taking the places
//! `register_callback_places` registers for it (`<op>.f.g.y`) rather than fresh ones. Built and
//! backed out: no row here or beside, and no probe (a member fitted to its spec with a row
//! parameter on the nested arrow), had another verdict.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS and its value says which cell was
//! written; a refusal is asserted by the words that name it, beside the program that differs in
//! one thing and runs.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

const SLOTS: &str = "  operation app2(q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {Modify[x]}) -> Unit effects {Modify[q]} = f(q)
  operation appD[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, -Modify[x]}) -> Unit effects {EffP} = f(q)";

/// `go()` hands `body` two fresh cells, `c` holding 1 and `d` holding 2, and reads both back:
/// `Cell.get(c) * 10 + Cell.get(d)`. `CALL` in `body` is the slot the callback is passed to.
fn program(ns: &str, above: &str, body: &str, call: &str) -> String {
    let body = body.replace("CALL", call);
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, String, List, Cell, Modify}}
{SLOTS}
{above}
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
{body}
    Cell.get(c) * 10 + Cell.get(d)
end
"#
    )
}

const ALLOWS: &str = "app2";
const DENIES: &str = "appD[EffP = {}]";
const DENIED: &[&str] = &["appD.f (op-arg)", "to lack `Modify[T = f.x]` (its `-…` lacks-constraint)"];

/// The two lambdas over `k` and over `j`, each written once, in a list and in an `if`; the
/// first one is passed on.
fn renamed_twins() -> Vec<(&'static str, String)> {
    let k = "lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)";
    let j = "lambda (j: Cell[V = Int64]) -> Cell.set(j, 43)";
    vec![
        (
            "list",
            format!(
                "    let fs = [{k}, {j}]\n    let _ = match fs\n      case cons(g, _) -> CALL(c, g)\n      case nil() -> Cell.set(c, 0)"
            ),
        ),
        (
            "if",
            format!("    let g = if Cell.get(c) > 0 then {k} else {j}\n    let _ = CALL(c, g)"),
        ),
    ]
}

/// TWO LAMBDAS DIFFERING ONLY IN THEIR PARAMETER'S NAME ARE ONE TYPE: the list and the `if`
/// load, and the callback taken out of them writes the cell `app2` hands it — 42 * 10 + 2.
#[test]
fn two_arrows_differing_only_in_their_parameters_names_are_one_type() {
    for (spelling, body) in renamed_twins() {
        let ns = format!("wi_dndzf.twins_{spelling}");
        let src = program(&ns, "", &body, ALLOWS);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(422), "{spelling}");
    }
}

/// … AND THE ONE TAKEN OUT OF THEM IS REFUSED WHERE THE SLOT DENIES THE WRITE, by the absence it
/// violates. The twins are the rows above.
#[test]
fn the_callback_taken_out_of_them_is_refused_where_the_slot_denies_the_write() {
    for (spelling, body) in renamed_twins() {
        let ns = format!("wi_dndzf.twins_denied_{spelling}");
        let src = program(&ns, "", &body, DENIES);
        assert_refused_naming(&load_errors_of(&src), DENIED, spelling);
    }
}

/// A LABEL NAMING A VALUE IN SCOPE IS NO PARAMETER: a lambda writing `d` and one writing its own
/// parameter are two types, in a list and in an `if`, while two writing `d` are one, and the one
/// chosen writes `d` whatever cell it is handed: 1 * 10 + 42. Passes before and after by design:
/// the renaming reaches only the arrows' own parameters.
#[test]
fn a_label_naming_a_value_in_scope_is_compared_as_it_stands() {
    let scope = "lambda (k: Cell[V = Int64]) -> Cell.set(d, 42)";
    let own = "lambda (j: Cell[V = Int64]) -> Cell.set(j, 43)";
    let scope2 = "lambda (j: Cell[V = Int64]) -> Cell.set(d, 43)";
    for (spelling, body, at) in [
        ("list", format!("    let fs = [{scope}, {own}]"), "list.element 2"),
        ("if", format!("    let g = if Cell.get(c) > 0 then {scope} else {own}"), "if.rule"),
    ] {
        let ns = format!("wi_dndzf.scope_{spelling}");
        let src = program(&ns, "", &body, ALLOWS);
        assert_refused_naming(&load_errors_of(&src), &[at, "Modify[T = d]"], spelling);
    }
    let ns = "wi_dndzf.scope_same";
    let body = format!("    let g = if Cell.get(c) > 0 then {scope} else {scope2}\n    let _ = g(c)");
    assert_eq!(run_int64(&program(ns, "", &body, ALLOWS), &format!("{ns}.go")), Ok(52));
}

/// The arrow `(x: Cell[V = Int64]) -> Unit @ {Modify[x]}` written where no parameter list
/// registers its parameter, and a callback of that type passed to the slot.
fn written_anywhere() -> Vec<(&'static str, &'static str, &'static str)> {
    vec![
        (
            "result",
            "  operation mk() -> (x: Cell[V = Int64]) -> Unit @ {Modify[x]} = lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)",
            "    let _ = CALL(c, mk())",
        ),
        (
            "field",
            "  sort Holder\n    entity holder(f: (x: Cell[V = Int64]) -> Unit @ {Modify[x]})\n  end",
            "    let h = holder(f: lambda (k: Cell[V = Int64]) -> Cell.set(k, 42))\n    let _ = CALL(c, h.f)",
        ),
        (
            "alias",
            "  sort Setter = (x: Cell[V = Int64]) -> Unit @ {Modify[x]}\n  operation mkS() -> Setter = lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)",
            "    let _ = CALL(c, mkS())",
        ),
        (
            "annotation",
            "",
            "    let h: (x: Cell[V = Int64]) -> Unit @ {Modify[x]} = lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)\n    let _ = CALL(c, h)",
        ),
    ]
}

/// AN ARROW WRITTEN ANYWHERE NAMES ITS OWN PARAMETER: an operation's result, an entity's field,
/// an alias and a `let` annotation each load, and the callback of that type writes the cell
/// `app2` hands it. Each was refused "unresolved name 'x'" (MEASURED).
#[test]
fn an_arrow_written_anywhere_names_its_own_parameter() {
    for (spelling, above, body) in written_anywhere() {
        let ns = format!("wi_dndzf.written_{spelling}");
        let src = program(&ns, above, body, ALLOWS);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(422), "{spelling}");
    }
}

/// … AND IS REFUSED WHERE THE SLOT DENIES THE WRITE. The twins are the rows above.
#[test]
fn an_arrow_written_anywhere_is_refused_where_the_slot_denies_the_write() {
    for (spelling, above, body) in written_anywhere() {
        let ns = format!("wi_dndzf.written_denied_{spelling}");
        let src = program(&ns, above, body, DENIES);
        assert_refused_naming(&load_errors_of(&src), DENIED, spelling);
    }
}

/// A SLOT TYPED BY AN ALIAS NAMING ITS PARAMETER IS READ AT ITS PARAMETER: applied to `q`, the
/// alias's `Modify[x]` is a write to `q`, which `viaAlias` declares — and a lambda written there
/// writing the cell it is handed runs. Declaring nothing, `viaAlias` is refused for the write it
/// does not declare.
#[test]
fn a_slot_typed_by_an_alias_is_read_at_its_parameter() {
    let alias = "  sort Setter = (x: Cell[V = Int64]) -> Unit @ {Modify[x]}";
    let body = "    let _ = viaAlias(c, lambda (k: Cell[V = Int64]) -> Cell.set(k, 42))";
    let declares = format!("{alias}\n  operation viaAlias(q: Cell[V = Int64], f: Setter) -> Unit effects {{Modify[q]}} = f(q)");
    let ns = "wi_dndzf.alias_slot";
    assert_eq!(run_int64(&program(ns, &declares, body, ALLOWS), &format!("{ns}.go")), Ok(422));
    let silent = format!("{alias}\n  operation viaAlias(q: Cell[V = Int64], f: Setter) -> Unit = f(q)");
    let ns = "wi_dndzf.alias_slot_silent";
    assert_refused_naming(
        &load_errors_of(&program(ns, &silent, body, ALLOWS)),
        &["viaAlias.effects (op-effects)", "Modify[T = q]"],
        "undeclared",
    );
}

/// WI-20261014-6T5C6's PROGRAM: an entity field's arrow names its own parameter beside the
/// sort's row parameter. The construction is admitted, and the write is to the cell the field's
/// function is applied to: `use(c)` puts 5 into `c`, 5 * 10 + 5. Refused "unresolved name 'k' in
/// scope 'Box'" (MEASURED).
#[test]
fn a_field_arrow_beside_a_row_parameter_names_its_own_parameter() {
    let ns = "wi_dndzf.boxed";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Box
    effects EB = ?
    entity box(g: (k: Cell[V = Int64]) -> Int64 @ {{Modify[k], EB}})
  end
  operation use(q: Cell[V = Int64]) -> Int64 effects {{Modify[q]}} =
    let b = box(g: lambda (k: Cell[V = Int64]) -> put(k, 5))
    match b
      case box(g) -> g(q)
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let n = use(c)
    n * 10 + Cell.get(c)
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(55));
}

/// AN ARROW NESTED IN A CALLBACK PARAMETER'S ARROW NAMES ITS OWN PARAMETER: `f`'s parameter `g`
/// writes the cell it is handed, and `drive`'s callback hands it `f`'s own cell, which `f`'s row
/// names — `hof` writes 7 into `q`. Refused "unresolved name 'y'" (MEASURED). Handing `g` a cell
/// `f`'s row does not name is refused.
#[test]
fn an_arrow_nested_in_a_callback_parameter_names_its_own_parameter() {
    let program = |ns: &str, inner: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  operation hof(q: Cell[V = Int64], f: (c: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Unit @ {{Modify[y]}}) -> Unit @ {{Modify[c]}}) -> Unit effects {{Modify[q]}} =
    f(q, lambda (z: Cell[V = Int64]) -> Cell.set(z, 7))
  operation drive(q: Cell[V = Int64], r: Cell[V = Int64]) -> Unit effects {{Modify[q], Modify[r]}} =
    hof(q, lambda (c: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Unit @ {{Modify[y]}}) -> g({inner}))
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let _ = drive(c, d)
    Cell.get(c) * 10 + Cell.get(d)
end
"#
        )
    };
    let ns = "wi_dndzf.nested";
    assert_eq!(run_int64(&program(ns, "c"), &format!("{ns}.go")), Ok(72));
    let ns = "wi_dndzf.nested_other";
    assert_refused_naming(
        &load_errors_of(&program(ns, "r")),
        &["hof.f (op-arg)", "Modify[T = r]"],
        "a cell f's row does not name",
    );
}

/// A SPEC OPERATION AND ITS MEMBER EACH WRITE THE ARROW IN THEIR RESULT: the member fits the
/// spec whether it names the parameter as the spec does or otherwise, and the callback the call
/// returns writes the cell `app2` hands it.
#[test]
fn a_member_and_its_spec_each_write_the_arrow_in_their_result() {
    for (spelling, member) in [("same", "x"), ("renamed", "y")] {
        let ns = format!("wi_dndzf.member_{spelling}");
        let above = format!(
            "  sort Mk\n    sort C = ?\n    operation mk(c: C) -> (x: Cell[V = Int64]) -> Unit @ {{Modify[x]}}\n  end\n  sort Tag\n    entity tag(n: Int64)\n    provides Mk[C = Tag]\n    operation mk(c: Tag) -> ({member}: Cell[V = Int64]) -> Unit @ {{Modify[{member}]}} = lambda (k: Cell[V = Int64]) -> Cell.set(k, 42)\n  end"
        );
        let body = "    let _ = CALL(c, Mk.mk(tag(n: 1)))";
        let src = program(&ns, &above, body, ALLOWS);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(422), "{spelling}");
        let ns = format!("wi_dndzf.member_denied_{spelling}");
        let src = program(&ns, &above, body, DENIES);
        assert_refused_naming(&load_errors_of(&src), DENIED, spelling);
    }
}

/// AN ARROW IN A CALLBACK'S RESULT NAMES ITS OWN PARAMETER: `f` returns a setter, and `curry`
/// applies it to its own cell. A callback parameter named `result` is refused: `<f>.result` is
/// the callback's return value, and a row naming it read the enclosing operation's result
/// (MEASURED: it loaded under `effects {Modify[q], Modify[result]}`).
#[test]
fn an_arrow_in_a_callback_result_names_its_own_parameter() {
    let ns = "wi_dndzf.curried";
    let above = "  operation curry(q: Cell[V = Int64], f: (n: Int64) -> (y: Cell[V = Int64]) -> Unit @ {Modify[y]}) -> Unit effects {Modify[q]} =\n    let s = f(42)\n    s(q)";
    let body = "    let _ = curry(c, lambda (n: Int64) -> lambda (k: Cell[V = Int64]) -> Cell.set(k, n))";
    assert_eq!(run_int64(&program(ns, above, body, ALLOWS), &format!("{ns}.go")), Ok(422));
    let ns = "wi_dndzf.result_named";
    let above = "  operation named(q: Cell[V = Int64], f: (result: Cell[V = Int64]) -> Unit @ {Modify[result]}) -> Cell[V = Int64] effects {Modify[q], Modify[result]} =\n    let _ = f(q)\n    q";
    assert_refused_naming(
        &load_errors_of(&program(ns, above, "", ALLOWS)),
        &["parameter name 'result' of the callback `f` is reserved"],
        "a callback parameter named result",
    );
}
