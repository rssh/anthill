//! WI-20261015-809JN — proposal 050.1, stage 1: a write through a `let`- or pattern-bound
//! name is charged to the memory the name reaches, where the name's scope ends, instead of
//! being dropped because the binder is a `let` or a pattern (kernel-language.md §5.6).
//!
//! Each row drives the program: a refusal names the label the write was charged as, and its
//! declared twin runs to the value the write leaves. Which part of `typing/memory.rs` each
//! row needs is said at the row, as the parts that fail it when backed out alone (measured
//! with one switch per part, in one build). Backing out the charge itself — the labels over
//! local names dropped, as before — fails every row but the fresh-memory control, the
//! relations, the alias, the capture and the sibling-branch rows. The one part no row fails
//! is a callee's memory clause being left out of Γ's facts (`assume_call_ensures`): the
//! record answers the same, so that passes either way by design — it keeps one source for
//! the two relations. Two more are design rather than verdict: a `match` arm's end keeping a
//! pool write's label in the row (a reader that never refuses one still sees the write), and
//! the walk skipping a value whose type holds no memory (cost). A binder over a constructor
//! constant holding no memory is driven by `wi_9wvt7_review7_test`'s variant-place row, which
//! failed with it read as an alias of the constructor.

use crate::common::{assert_refused_naming, load_errors_of, run_int64, try_load_kb_with};

const PUT: &str = r#"
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace test.n809.{ns}\n  import anthill.prelude.{{Int64, Bool, Cell, List, Unit}}\n  import anthill.memory.{{memory_alias, memory_maybe_connected}}\n{PUT}{body}\nend\n"
    )
}

/// `let x = p` aliases `p`, so a write through `x` is `Modify[p]` (§3). Fails with the charge
/// backed out (`charge`): the write was dropped and `f` loaded declaring nothing.
#[test]
fn a_write_through_a_let_alias_of_a_parameter_is_the_parameters() {
    let undeclared = program(
        "let_alias",
        r#"
  operation f(p: Cell[V = Int64]) -> Int64 =
    let x = p
    put(x, 7)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&undeclared),
        &["f.effects", "undeclared effect: Modify[T = p]"],
        "a write through `let x = p` is p's",
    );
    let declared = program(
        "let_alias_ok",
        r#"
  operation f(p: Cell[V = Int64]) -> Int64 effects Modify[p] =
    let x = p
    put(x, 7)
  operation go() -> Int64 =
    let c = Cell.new(1)
    let _ = f(c)
    Cell.get(c)
"#,
    );
    assert_eq!(run_int64(&declared, "test.n809.let_alias_ok.go"), Ok(7));
}

/// A binder inside a constructor pattern reads a field of the scrutinee, so a write through
/// it is the scrutinee's (§2, a pattern). Fails with the charge backed out (`charge`).
#[test]
fn a_write_through_a_list_element_is_the_lists() {
    let undeclared = program(
        "element",
        r#"
  operation g(l: List[T = Cell[V = Int64]]) -> Int64 =
    match l
      case nil() -> 0
      case cons(h, rest) -> put(h, 8)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&undeclared),
        &["g.effects", "undeclared effect: Modify[T = l]"],
        "a write through a list element is the list's",
    );
    let declared = program(
        "element_ok",
        r#"
  operation g(l: List[T = Cell[V = Int64]]) -> Int64 effects Modify[l] =
    match l
      case nil() -> 0
      case cons(h, rest) -> put(h, 8)
  operation go() -> Int64 =
    let d = Cell.new(1)
    let ld = [d]
    let _ = g(ld)
    Cell.get(d)
"#,
    );
    assert_eq!(run_int64(&declared, "test.n809.element_ok.go"), Ok(8));
}

/// A binder that is the whole scrutinee aliases it. Fails with the charge backed out
/// (`charge`).
#[test]
fn a_whole_scrutinee_binder_aliases_it() {
    let undeclared = program(
        "whole",
        r#"
  operation m(p: Cell[V = Int64]) -> Int64 =
    match p
      case x -> put(x, 1)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&undeclared),
        &["m.effects", "undeclared effect: Modify[T = p]"],
        "a write through `case x` over p is p's",
    );
}

/// A construction lies in its parts' memory (§2), so a write through a field taken back out
/// of it is the part's. Fails with the construction's regions backed out (`construct`): the
/// write was charged to nothing; and with the charge (`charge`).
#[test]
fn a_write_through_a_constructed_value_is_its_parts() {
    let undeclared = program(
        "boxed",
        r#"
  entity box(c: Cell[V = Int64])
  operation viaBox(p: Cell[V = Int64]) -> Int64 =
    let b = box(c: p)
    match b
      case box(c) -> put(c, 6)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&undeclared),
        &["viaBox.effects", "undeclared effect: Modify[T = p]"],
        "a write through a field of `box(c: p)` is p's",
    );
    let declared = program(
        "boxed_ok",
        r#"
  entity box(c: Cell[V = Int64])
  operation viaBox(p: Cell[V = Int64]) -> Int64 effects Modify[p] =
    let b = box(c: p)
    match b
      case box(c) -> put(c, 6)
  operation go() -> Int64 =
    let e = Cell.new(1)
    let _ = viaBox(e)
    Cell.get(e)
"#,
    );
    assert_eq!(run_int64(&declared, "test.n809.boxed_ok.go"), Ok(6));
}

/// `let y = if b then p else q` aliases neither and lies in both, so a write through `y` is
/// charged to both (§2, a join). Fails with the branches' regions backed out (`join`): the
/// write was charged to nothing and `pick` loaded declaring `Modify[p]` alone; and with the
/// charge (`charge`).
#[test]
fn a_branch_value_lies_in_both_branches_memory() {
    let one = program(
        "pick",
        r#"
  operation pick(p: Cell[V = Int64], q: Cell[V = Int64], b: Bool) -> Int64 effects Modify[p] =
    let y = if b then p else q
    put(y, 3)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&one),
        &["pick.effects", "undeclared effect: Modify[T = q]"],
        "a write through a branch value is charged to both branches",
    );
    let both = program(
        "pick_ok",
        r#"
  operation pick(p: Cell[V = Int64], q: Cell[V = Int64], b: Bool) -> Int64
    effects {Modify[p], Modify[q]} =
    let y = if b then p else q
    put(y, 3)
  operation go() -> Int64 =
    let k = Cell.new(1)
    let q = Cell.new(1)
    let _ = pick(k, q, false)
    Cell.get(k) * 10 + Cell.get(q)
"#,
    );
    assert_eq!(run_int64(&both, "test.n809.pick_ok.go"), Ok(13));
}

/// CONTROL, the WI-314 rows' reading: a write to memory the body allocated and does not
/// return adds nothing, through an alias too. Passes with every part backed out by design.
#[test]
fn a_write_to_fresh_memory_adds_nothing() {
    let src = program(
        "fresh",
        r#"
  operation local(n: Int64) -> Int64 =
    let c = Cell.new(n)
    let d = c
    let _ = put(d, 5)
    Cell.get(c)
  operation go() -> Int64 = local(2)
"#,
    );
    assert_eq!(run_int64(&src, "test.n809.fresh.go"), Ok(5));
}

/// `kb()` and `KB.loaded` hand out values connected to `kb_storage`, state outside the
/// process no row can name, so a write through one is refused, in every spelling that binds
/// the value. Fails with the pool's region backed out (`pool`): every one loaded declaring
/// nothing; with the charge (`charge`); with a construction's regions (`construct`, the
/// `boxed` spelling) and a branch's (`join`, `viaIf`). The inline `KB.assert(kb(), …)` stays
/// refused by the place rule, either way.
#[test]
fn a_write_through_a_knowledge_base_value_is_refused() {
    let src = r#"
namespace test.n809.kb
  import anthill.prelude.{Int64, Bool, Unit, Option, List, String}
  import anthill.reflect.{KB, Term}
  import anthill.reflect.KB.{kb, loaded}
  entity Thing(n: Int64)
  entity holder(k: KB)
  operation w(k: KB, t: Term) -> Int64 effects Modify[k] =
    let _ = KB.assert(k, t, Thing[])
    1
  operation direct(t: Term) -> Int64 =
    let k = kb()
    let _ = KB.assert(k, t, Thing[])
    1
  operation alias2(t: Term) -> Int64 =
    let k = kb()
    let j = k
    w(j, t)
  operation boxed(t: Term) -> Int64 =
    let h = holder(k: kb())
    match h
      case holder(j) -> w(j, t)
  operation viaIf(t: Term, b: Bool) -> Int64 =
    let k = if b then kb() else kb()
    w(k, t)
  operation layer(t: Term, srcs: List[T = String]) -> Int64 effects Error[anthill.reflect.LoadFailed] =
    let k = loaded(srcs)
    w(k, t)
end
"#;
    let errs = load_errors_of(src);
    for op in ["direct", "alias2", "boxed", "viaIf", "layer"] {
        assert!(
            errs.iter().any(|e| e.contains(&format!("{op}.effects"))
                && e.contains("anthill.reflect.KBStorage.kb_storage")
                && e.contains("cannot be declared")),
            "a write through a knowledge-base value in `{op}` must be refused naming \
             kb_storage; got:\n{errs:#?}"
        );
    }
    let inline = r#"
namespace test.n809.kb_inline
  import anthill.prelude.{Int64}
  import anthill.reflect.{KB, Term}
  import anthill.reflect.KB.{kb}
  entity Thing(n: Int64)
  operation add(t: Term) -> Int64 =
    let _ = KB.assert(kb(), t, Thing[])
    1
end
"#;
    assert_refused_naming(
        &load_errors_of(inline),
        &["assert.kb", "names no resource"],
        "the inline call stays refused by the place rule",
    );
}

/// A lambda's parameter's memory is its caller's: a write through it keeps naming it, so an
/// application that writes the operation's own cell is refused where nothing declares it.
/// Fails with that kept label backed out (`supplied`): the label was dropped and `use` ran,
/// writing `q` (family `e-applied-arrow`'s `writes-own` programs, which moved to `runs`);
/// and with the charge (`charge`), which drops it too.
#[test]
fn a_write_through_a_lambdas_parameter_keeps_naming_it() {
    let src = program(
        "lambda_param",
        r#"
  operation use(q: Cell[V = Int64]) -> Int64 =
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    w(q)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["use.effects", "undeclared effect: Modify[T = z]"],
        "a lambda's write through its own parameter is not dropped",
    );
}

/// A `let` inside a lambda's body aliases what it binds, as one in the operation's body
/// does. Fails with the charge backed out (`charge`).
#[test]
fn a_write_through_a_let_inside_a_lambda_is_the_parameters() {
    let src = program(
        "in_lambda",
        r#"
  operation viaLambda(p: Cell[V = Int64]) -> Int64 =
    let w = lambda (t: Int64) -> (let j = p
                                  put(j, t))
    w(1)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["viaLambda.effects", "undeclared effect: Modify[T = p]"],
        "a write through a let inside a lambda is the parameter's",
    );
}

/// The ticket's `readOnly`: the slot forbids a write to its argument, and `f`, whose write
/// through `let x = p` is now declared, is refused there. Fails with the charge backed out
/// (`charge`): `f` declared nothing and passed the slot.
#[test]
fn a_read_only_slot_refuses_a_callback_writing_through_an_alias() {
    let src = program(
        "read_only",
        r#"
  operation f(p: Cell[V = Int64]) -> Int64 effects Modify[p] =
    let x = p
    put(x, 7)
  operation fUndeclared(p: Cell[V = Int64]) -> Int64 =
    let x = p
    put(x, 7)
  operation readOnly[Eff](c: Cell[V = Int64], w: (x: Cell[V = Int64]) -> Int64 @ {Eff, -Modify[x]}) -> Int64
    effects {Eff} =
    let _ = w(c)
    Cell.get(c)
  operation go() -> Int64 =
    let k = Cell.new(1)
    readOnly(k, f)
"#,
    );
    let errs = load_errors_of(&src);
    assert_refused_naming(&errs, &["readOnly.w", "lack"], "the slot refuses f");
    assert_refused_naming(
        &errs,
        &["fUndeclared.effects", "Modify[T = p]"],
        "the undeclared twin is refused for its own write",
    );
}

const APART: &str = r#"
  entity box(c: Cell[V = Int64])
  operation apart(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64
    requires not memory_maybe_connected(p, q) = 1
  operation same(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64
    requires memory_alias(p, q) = 2
  -- connects s's memory with x's and writes nothing: an upper bound a clause may state
  operation tie(s: Cell[V = Int64], x: Cell[V = Int64]) -> Int64
    ensures memory_maybe_connected(s, x) = 0
"#;

fn with_apart(ns: &str, body: &str) -> String {
    program(ns, &format!("{APART}{body}"))
}

/// The memory relations at a call's `requires`, answered by the body's record (050.1 §1):
/// two cells the body allocated are separate, one cell twice and a field taken out of a box
/// holding it are not; two parameters are unknown, and so unproved, unless the caller
/// requires it; a parameter and a fresh cell are separate; an alias is the cell. Fails with
/// the record's answer backed out (`view`): `useFresh`, `useFreshParam` and `useAlias` were
/// refused as unproved; and with a construction's regions (`construct`): `useBoxed` loaded.
#[test]
fn the_memory_relations_are_answered_from_the_record() {
    let ok = with_apart(
        "relations_ok",
        r#"
  operation useFresh(n: Int64) -> Int64 =
    let a = Cell.new(n)
    let b = Cell.new(n)
    apart(a, b)
  operation useDeclared(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64
    requires not memory_maybe_connected(p, q) =
    apart(p, q)
  operation useFreshParam(p: Cell[V = Int64]) -> Int64 =
    let a = Cell.new(1)
    apart(p, a)
  operation useAlias(p: Cell[V = Int64]) -> Int64 =
    let x = p
    same(x, p)
"#,
    );
    if let Err(errs) = try_load_kb_with(&ok) {
        panic!("the separate and aliased places must be proved; got:\n{errs:#?}");
    }
    for (op, call, goal) in [
        ("useSame", "let a = Cell.new(n)\n    apart(a, a)", "not(memory_maybe_connected(a, a))"),
        (
            "useBoxed",
            "let a = Cell.new(n)\n    let bx = box(c: a)\n    match bx\n      case box(c) -> apart(a, c)",
            "not(memory_maybe_connected(a, c))",
        ),
    ] {
        let src = with_apart(
            &format!("rel_{op}"),
            &format!("  operation {op}(n: Int64) -> Int64 =\n    {call}\n"),
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &["apart.requires", goal],
            "connected places are not separate",
        );
    }
    let params = with_apart(
        "rel_params",
        r#"
  operation useParams(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64 =
    apart(p, q)
  operation useNotAlias(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64 =
    same(p, q)
"#,
    );
    let errs = load_errors_of(&params);
    assert_refused_naming(&errs, &["apart.requires", "memory_maybe_connected(p, q)"], "unknown");
    assert_refused_naming(&errs, &["same.requires", "memory_alias(p, q)"], "unknown");
}

/// A callee clause connecting two of its arguments unites their memory (§2, a call that
/// stores), so a later write through one is charged to the other — `tie` writes nothing
/// itself, so the label comes from the connection alone. Fails with stores backed out
/// (`stores`): `afterTie` loaded declaring nothing; and with the charge (`charge`).
#[test]
fn a_store_connects_its_arguments_memory() {
    let src = with_apart(
        "store",
        r#"
  operation afterTie(s: Cell[V = Int64]) -> Int64 =
    let c = Cell.new(0)
    let _ = tie(s, c)
    put(c, 2)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["afterTie.effects", "undeclared effect: Modify[T = s]"],
        "a write after a store is charged to the container",
    );
    let after_join = with_apart(
        "store_join",
        r#"
  operation afterJoin(s: Cell[V = Int64], b: Bool) -> Int64 =
    let c = Cell.new(0)
    let _ = if b then tie(s, c) else 0
    apart(s, c)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&after_join),
        &["apart.requires", "memory_maybe_connected(s, c)"],
        "a connection made in one branch is kept after the join",
    );
}

/// A connection a store makes in one branch is not seen in the other (050.1 §2, a join): the
/// `else` branch of `sibling` is where `tie` did not run, so `s` and `c` are separate there.
/// Fails with every connection read in every branch (`branch`), and with the record's answer
/// backed out (`view`).
#[test]
fn a_connection_is_not_seen_in_a_sibling_branch() {
    let src = with_apart(
        "sibling",
        r#"
  operation sibling(s: Cell[V = Int64], b: Bool) -> Int64 =
    let c = Cell.new(0)
    if b then tie(s, c) else apart(s, c)
"#,
    );
    if let Err(errs) = try_load_kb_with(&src) {
        panic!("the else branch has no connection; got:\n{errs:#?}");
    }
}

/// An alias of a parameter is that parameter alone (§3): after `tie(p, q)` the two may share,
/// and still a write through `let x = p` is `Modify[p]` and not `Modify[q]`. Fails with the
/// alias read as regions (`alias`): `viaAlias` was refused naming `Modify[q]`.
#[test]
fn an_alias_of_a_parameter_is_that_parameter_alone() {
    let src = with_apart(
        "alias_alone",
        r#"
  operation viaAlias(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64 effects Modify[p] =
    let _ = tie(p, q)
    let x = p
    put(x, 1)
"#,
    );
    if let Err(errs) = try_load_kb_with(&src) {
        panic!("a write through an alias of p is p's alone; got:\n{errs:#?}");
    }
}

/// A lambda reaches every name it captures (§2), so a lambda over `c` is not separate from
/// `c` — whatever it returns: `writer` returns an `Int64` and writes `c` when applied. Fails
/// with captures backed out (`captures`): both loaded; and `writer` with a function value
/// filtered by its result type, as a row reads one.
#[test]
fn a_lambda_lies_in_what_it_captures() {
    for (op, lambda) in [("capture", "lambda () -> c"), ("writer", "lambda () -> put(c, 1)")] {
        let src = program(
            op,
            &format!(
                r#"
  operation sep[A](a: A, b: Cell[V = Int64]) -> Int64
    requires not memory_maybe_connected(a, b) = 1
  operation {op}(n: Int64) -> Int64 =
    let c = Cell.new(n)
    let f = {lambda}
    sep(f, c)
"#
            ),
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &["sep.requires", "memory_maybe_connected(f, c)"],
            "a lambda capturing c may share c's memory",
        );
    }
}

/// A binder taking a field out of a value is in that value's memory but is not the value:
/// `memory_alias(b, c)` over `case box(c)` of `b` is unproved, while `let x = p` is `p`
/// (`the_memory_relations_are_answered_from_the_record`). FAILS with a field binder read as
/// an alias of its holder: the call was accepted, a promise that the box and the cell it
/// holds are one resource.
#[test]
fn a_field_binder_is_not_its_holder() {
    let src = program(
        "field_alias",
        r#"
  entity box(c: Cell[V = Int64])
  operation sameB(p: box, q: Cell[V = Int64]) -> Int64 requires memory_alias(p, q) = 2
  operation fieldNotAlias(b: box) -> Int64 =
    match b
      case box(c) -> sameB(b, c)
"#,
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["sameB.requires", "memory_alias(b, c)"],
        "a field is not its holder",
    );
}

/// A lambda's body is a scope: a write through a name bound inside it is charged where the
/// name's memory lies before the lambda's row is formed, so the row names only what is in
/// scope where the lambda is written (§3). Without it the row named the body's own `j`, and
/// a slot refused it as naming a value out of scope even where the write was declared.
/// FAILS with the lambda body's end not charged: both programs refused naming `j`.
#[test]
fn a_lambdas_row_names_no_binder_of_its_body() {
    let body = |row: &str| {
        format!(
            r#"
  operation applyOwn[EA](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {{Modify[k], EA}}) -> Int64
    effects {{Modify[p], EA}} = f(p)
  operation viaRow(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64 effects {row} =
    applyOwn(p, lambda (k: Cell[V = Int64]) -> (let j = q
                                                  let _ = put(j, 2)
                                                  put(k, 1)))
"#
        )
    };
    assert_refused_naming(
        &load_errors_of(&program("lambda_end", &body("Modify[p]"))),
        &["viaRow.effects", "undeclared effect: Modify[T = q]"],
        "the lambda's write through `let j = q` is q's",
    );
    if let Err(errs) = try_load_kb_with(&program("lambda_end_ok", &body("{Modify[p], Modify[q]}"))) {
        panic!("declared, the lambda's row is admitted; got:\n{errs:#?}");
    }
}

/// A body writing through one knowledge-base value twice, another between, is refused once
/// per name. Passes either way by design: the boundary reads a row whose labels are already
/// one per name, and only that reader records a write to a pool — an arm's end keeps the
/// label in the row instead ([`ScopeEnd`]), so no second record of it can form.
#[test]
fn a_pool_write_is_refused_once_per_name() {
    let src = r#"
namespace test.n809.kb_twice
  import anthill.prelude.{Int64}
  import anthill.reflect.{KB, Term}
  import anthill.reflect.KB.{kb}
  entity Thing(n: Int64)
  operation twice(t: Term) -> Int64 =
    let k = kb()
    let j = kb()
    let _ = KB.assert(k, t, Thing[])
    let _ = KB.assert(j, t, Thing[])
    let _ = KB.assert(k, t, Thing[])
    1
end
"#;
    let errs = load_errors_of(src);
    let through = |name: &str| {
        errs.iter()
            .filter(|e| e.contains(&format!("through `{name}` reaches")))
            .count()
    };
    assert_eq!((through("k"), through("j")), (1, 1), "{errs:#?}");
}

/// A rule body has no memory record: a memory relation asked there is refused as unaskable,
/// so a `not(…)` over it proves nothing. FAILS with the relation failing there instead: the
/// negation held, and `ask` answered definitely.
#[test]
fn a_memory_relation_in_a_rule_body_proves_nothing() {
    let src = r#"
namespace test.n809.rule_body
  import anthill.prelude.{Int64}
  import anthill.memory.{memory_alias}
  rule ask(?r) :- ?r <=> 1, not(memory_alias(?r, ?r))
  rule control(?r) :- ?r <=> 1
end
"#;
    let mut kb = try_load_kb_with(src).unwrap_or_else(|e| panic!("{e:#?}"));
    let answers = crate::common::query_unary(&mut kb, "test.n809.rule_body.ask");
    assert!(
        answers.iter().all(|(_, definite)| !definite),
        "a negated memory relation in a rule body must not hold; got {answers:?}"
    );
    let control = crate::common::query_unary(&mut kb, "test.n809.rule_body.control");
    assert!(control.iter().any(|(_, definite)| *definite), "{control:?}");
}

/// A scope's end charges only the names bound within it (§3: a label is resolved where its
/// name's scope ends). A lambda writing `k`, a cell its enclosing body allocated, keeps
/// `Modify[k]` in its row — at an arm's end inside the lambda and at the lambda's end alike —
/// because the lambda is applied elsewhere and the write is not to its own memory: a slot
/// admitting no effect refuses it. FAILS with each scope end charging every name of the body
/// (the arm's mark, or the lambda's, taken as the body's start): `k`'s fresh memory read as
/// the scope's own and the write dropped, so `inArm` loaded — as it did before this stage,
/// where the arm's end dropped every `let` in scope — and so did `atEnd`, with
/// `wi_41yye_enclosing_place_type_test::let_local_cell_is_checked`'s box over such a lambda.
#[test]
fn a_scope_end_charges_only_its_own_names() {
    let src = program(
        "own_names",
        r#"
  operation pure1(f: (x: Int64) -> Int64 @ {}) -> Int64 = f(1)
  operation inArm(n: Int64) -> Int64 =
    let k = Cell.new(n)
    pure1(lambda (x: Int64) -> match x
                                 case _ -> put(k, x))
  operation atEnd(n: Int64) -> Int64 =
    let k = Cell.new(n)
    pure1(lambda (x: Int64) -> put(k, x))
"#,
    );
    let errs = load_errors_of(&src);
    let refused = errs
        .iter()
        .filter(|e| e.contains("pure1.f") && e.contains("Modify[T = k]"))
        .count();
    assert_eq!(
        refused, 2,
        "both lambdas write the enclosing body's cell and are refused at a pure slot; got:\n{errs:#?}"
    );
}

/// `memory_disconnected`, defined in `anthill.memory` by the Horn clause
/// `memory_disconnected(?a, ?b) :- not(memory_maybe_connected(?a, ?b))`: two cells the body
/// allocated are disconnected, one cell twice and two parameters are not proved so, and a
/// caller requiring `not memory_maybe_connected(p, q)` discharges a callee requiring
/// `memory_disconnected(p, q)` — the clause runs left to right. The other way round is not
/// derived (`callerDtoN`): its Γ holds `memory_disconnected(p, q)`, and nothing derives the
/// negation from it. FAILS with the clause removed: `freshD` and `callerNtoD` refused, the
/// name declaring nothing.
#[test]
fn memory_disconnected_is_the_negation_of_maybe_connected() {
    let src = program(
        "disconnected",
        r#"
  operation apartN(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64
    requires not memory_maybe_connected(p, q) = 1
  operation apartD(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64
    requires memory_disconnected(p, q) = 2
  operation freshD(n: Int64) -> Int64 =
    let a = Cell.new(n)
    let b = Cell.new(n)
    apartD(a, b)
  operation sameD(n: Int64) -> Int64 =
    let a = Cell.new(n)
    apartD(a, a)
  operation paramsD(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64 = apartD(p, q)
  operation callerNtoD(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64
    requires not memory_maybe_connected(p, q) = apartD(p, q)
  operation callerDtoN(p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64
    requires memory_disconnected(p, q) = apartN(p, q)
"#,
    )
    .replace(
        "import anthill.memory.{memory_alias, memory_maybe_connected}",
        "import anthill.memory.{memory_alias, memory_maybe_connected, memory_disconnected}",
    );
    let errs = load_errors_of(&src);
    let refused = |goal: &str| errs.iter().any(|e| e.contains(goal));
    assert!(!refused("memory_disconnected(a, b)"), "freshD: {errs:#?}");
    assert!(refused("memory_disconnected(a, a)"), "sameD: {errs:#?}");
    assert!(refused("memory_disconnected(p, q)"), "paramsD: {errs:#?}");
    assert!(refused("not(memory_maybe_connected(p, q))"), "callerDtoN: {errs:#?}");
    assert_eq!(
        errs.iter().filter(|e| e.contains("apartD.requires")).count(),
        2,
        "sameD and paramsD only — callerNtoD's own requirement discharges apartD's: {errs:#?}"
    );
}
