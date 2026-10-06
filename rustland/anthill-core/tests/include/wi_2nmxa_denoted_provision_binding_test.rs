//! WI-20260829-2NMXA — what a provision binds its spec's parameters to is read at a
//! receiver whose type argument HOLDS A VALUE.
//!
//! A type argument that holds a value rides an occurrence and not a hash-consed term:
//! `MappedStream[…, TransformEffects = {Modify[k]}]`, the type of a mapped stream whose
//! transform writes the cell `k`. The reader of "what is `FiniteCollection` at this
//! receiver" kept a receiver's argument only where it was a term, so that argument read as
//! one the receiver had not written; the witness's `E = {SourceEffects, TransformEffects}`
//! then stayed open, and the spec's row at that receiver was not read at all. Three
//! spellings of one program asked for it and each was refused:
//!
//!   total(c: FiniteCollection.C) effects FiniteCollection.E     "expected a type for
//!     — the member sugar                                          'FiniteCollection.E',
//!                                                                 got unconstrained"
//!   total[P, R](c: P) effects R                                  "expected a type for 'R',
//!     requires FiniteCollection[C = P, E = R]                     got unconstrained"
//!   m.size() / FiniteCollection.size(m)                          "got undeclared effect: ?_"
//!     — a spec operation the provider does not override
//!
//! while the same three over `TransformEffects = {}` loaded. A spec operation the provider
//! OVERRIDES was never in the gap — its row comes from unifying the argument with the
//! override's own signature — which is why the gap looked narrower than it was; those rows
//! are the controls below.
//!
//! THE READING IS CARRIER-NEUTRAL NOW. The receiver's arguments are read on the carrier
//! each rides (`typing::parameterized_vid_bindings`), the provision's binding is
//! instantiated with them by a rewrite whose replacements may be occurrences
//! (`typing::rewrite_type_leaves`, under `substitute_carrier_params` and the witness
//! instantiation), and a parameter is bound to the result as it stands. Where every
//! argument is a term the result is the hash-consed term it always was.
//!
//! A ROW THAT RUNS ASSERTS A VALUE: the count the consumer answers and the sum the
//! transform wrote into the cell, so the row was read AND the dictionary the call owes was
//! built at that receiver. A row that is refused asserts the effect or the type named — the
//! row is read as `{Modify[k]}`, not dropped to `{}`. FOUR ROWS ASSERT A LOAD VERDICT AND
//! RUN NOTHING, each for the reason at its site: the member returning another row, the
//! denial and the key are refusals, and the cited column's bound is suspended at run time
//! on either twin.
//!
//! BACK-OUTS, MEASURED. Each entry is ONE part of the change put back as it was — present
//! and wrong, not deleted — and run over the unit tests and `wi_tests` (666 + 6218 rows);
//! the rows it names are all that fail. A row with no module is this file's, by the first
//! words of its name.
//!
//!  * A receiver's arguments kept only where they are terms (`parameterized_vid_bindings`)
//!    — 13: the unit row `wi470_parameterized_vid_bindings_reads_both_carriers`,
//!    `n01py…::a_row_that_names_a_cell_is_read_like_a_ground_one`, and eleven here:
//!    `a_members_row…`, `a_bracket_parameter_a_clause_binds…`, `a_defaulted_spec_operation…`,
//!    `the_row_read_names…`, `the_row_read_is…`, `a_clauses_row…`, `a_defaulted_operation…`,
//!    `a_self_receiving…`, `a_cell_named…`, `a_stream_mapped_twice…`,
//!    `a_witness_that_reorders…`.
//!  * A witness's binding at the receiver kept only where a term
//!    (`bind_spec_params_from_carrier_param`) — 11: those thirteen less the unit row and
//!    `a_self_receiving…`.
//!  * A clause's parameter bound only at a CLOSED type (`bind_clause_params_at_carrier`)
//!    — 9: the `n01py` row, `a_members_row…`, `a_bracket_parameter_a_clause_binds…`,
//!    `the_row_read_names…`, `the_row_read_is…`, `a_clauses_row…`, `a_cell_named…`,
//!    `a_stream_mapped_twice…`, `a_witness_that_reorders…`.
//!  * A carrier's own binding at the receiver kept only where a term (the same function's
//!    other arm) — 3: `a_clauses_row…`, `a_defaulted_operation…`, `a_cell_named…`.
//!  * A self-receiver's binding kept only where a term (`bind_spec_params_from_carrier`)
//!    — 1: `a_self_receiving…`.
//!  * A lent member grounded only at a CLOSED type (`lent_member`) — 1: `a_projected_row…`.
//!  * A spec view's bindings dropped where no term (`unwrap_spec_view_value`) — 26: seven
//!    here (`a_members_row…`, both `a_bracket_parameter…` rows, `a_clauses_row…`,
//!    `a_cell_named…`, `a_stream_mapped_twice…`, `a_witness_that_reorders…`) and nineteen
//!    rows of the tickets that put a value in a requirement:
//!    `wi_020th_two_hop_chain_test` (6), `wi_jn09w_holder_gate_test` (4),
//!    `wi_0rp29_nested_projection_value_in_type_test` (3), `wi_kssa4_spec_typed_value_test`
//!    (2), `wi_wbhtm_value_in_type_call_test` (2), `wi_2kv4y_unfixed_carrier_test` (1),
//!    `typer_capability_matrix_test` (1).
//!  * A provider's view instantiated by the term walk (`parameterized_compatible_view`) —
//!    1: `a_member_returning_another_row…`.
//!  * No witness leg on the view arm (`types_compatible_view_structural`) — 2:
//!    `a_denial…` and `a_bounded_column…`.
//!  * A written argument read into a field's projection only where a term
//!    (`bare_spec_arg_provision_projection`) — 1: `a_spec_typed_field…`.
//!  * A key checked only where its type is a term (`check_use_site_requires_eq`) — 1:
//!    `a_key_whose_type…`.
//!  * A child widened by `ViewItem::to_value`, and `type_is_ground` as the plain view walk
//!    — 1 each, the unit rows of `wi_2nmxa_value_holding_type_reader_tests`.
//!
//! PASS EITHER WAY, and not by design — these parts of the change no row drives, each for
//! the reason given; the reading left in is the one that answers a type the same on every
//! carrier:
//!
//!   the rewrite kept out of a value's expression — what it walks (a provision's binding, a
//!     clause, a declared type) names no place a join could take for a parameter;
//!   a σ link followed on any carrier (`sigma_class_terminal`) — no σ a test builds holds
//!     one there that is no term (not one of the reads);
//!   an eliminated spec view left on its children's carriers, and a spec's binding read on
//!     its own — a stored clause is a term, and the readers answer alike on either;
//!   two provision bindings compared structurally, and a default's row against a goal's
//!     argument — every pair compared is two stored terms, a literal in a goal being
//!     re-grounded as the term a row stores;
//!   a `require[…]` bracket's arguments composed into the chain it holds — the demand a
//!     clause's goal makes of a bracket says none of the spec's type parameters;
//!   an unwritten slot of an application that holds a value opened like its term twin's —
//!     the relation reads an unwritten slot as any instantiation, opened or not;
//!   a bare applied entry and a carried type with no sort head read as their term twins,
//!     and a route's pin kept where it holds a value — no entry, carried type or citation
//!     in the suite has the shape.

use crate::common::{assert_refused_naming, load_errors_of, try_load_kb_with};
use anthill_core::eval::{self, Interpreter};

/// Load `src` and call `entry` with the `Modify` handler installed: its `Int64`, or why it
/// did not load or run.
fn run(src: &str, entry: &str) -> Result<i64, String> {
    let kb = try_load_kb_with(src).map_err(|errs| errs.join("\n"))?;
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    crate::common::register_modify_handler(&mut interp);
    match interp.call(entry, &[]) {
        Ok(eval::Value::Int(v)) => Ok(v),
        other => Err(format!("`{entry}` did not run to an Int64: {other:?}")),
    }
}

// ── the stdlib's mapped stream: the ticket's own program ─────────────────────

/// `f` takes a mapped stream over a list whose transform writes `k`, and consumes it by
/// `body`; `g` builds one — the transform adds each element to `k` — and `main` answers
/// `f`'s answer × 100 + the cell. `f_effects` is the row `f` declares.
///
/// THE TRANSFORM'S ROW IS WRITTEN AT `map`, not inferred from the lambda: a row variable is
/// not bound from a label that holds a value yet (`typing::bind_row_tail`), which is another
/// reader than the one these rows are for.
fn mapped(ns: &str, decl: &str, f_effects: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{List, Int64, Unit, FiniteCollection, MappedStream, Cell, Modify}}
  {decl}
  operation f(k: Cell[V = Int64],
              m: MappedStream[Source = List[T = Int64], SourceElement = Int64, T = Int64,
                              SourceEffects = {{}}, TransformEffects = {{Modify[k]}}]) -> Int64 {f_effects} =
    {body}
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation g(k: Cell[V = Int64]) -> Int64 effects {{Modify[k]}} =
    f(k, FiniteCollection.map[EffP = {{Modify[k]}}](rows(), lambda (x: Int64) -> bump(k, x)))
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = g(k)
    n * 100 + Cell.get(k)
end
"#
    )
}

const MEMBER: &str = "operation total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E = FiniteCollection.size(c)";
const BRACKET: &str = "operation total[P, R](c: P) -> Int64 effects R requires FiniteCollection[C = P, E = R] = FiniteCollection.size(c)";
const WRITES_K: &str = "effects {Modify[k]}";

/// THE TICKET'S PROGRAM. `total`'s row is `FiniteCollection.E`, a member's parameter, which
/// a call fixes by the provision at the carrier it passes: the witness's `E =
/// {SourceEffects, TransformEffects}` at this receiver is `{Modify[k]}`. Four elements, and
/// the transform ran over each: 4 × 100 + (1 + 2 + 3 + 4).
#[test]
fn a_members_row_is_read_off_a_witness_at_a_receiver_that_names_a_cell() {
    let ns = "wi2nmxa.member";
    assert_eq!(
        run(&mapped(ns, MEMBER, WRITES_K, "total(m)"), &format!("{ns}.main")),
        Ok(410)
    );
}

/// The same requirement with the row a parameter of the operation's own bracket, which the
/// call leaves to the provision as it leaves the member.
#[test]
fn a_bracket_parameter_a_clause_binds_is_read_off_the_witness_too() {
    let ns = "wi2nmxa.bracket";
    assert_eq!(
        run(&mapped(ns, BRACKET, WRITES_K, "total(m)"), &format!("{ns}.main")),
        Ok(410)
    );
}

/// CONTROL FOR THE PROVISION'S READING — it passes with each reader of the receiver backed
/// out, by design: the parameter is written at the call, so nothing is read off the
/// provision for it. It is no control for the requirement itself, whose own binding holds
/// the value: where a spec view drops such a binding it fails with the rest.
#[test]
fn a_bracket_parameter_written_at_the_call_is_the_control() {
    let ns = "wi2nmxa.bracketwritten";
    assert_eq!(
        run(
            &mapped(ns, BRACKET, WRITES_K, "total[R = {Modify[k]}](m)"),
            &format!("{ns}.main")
        ),
        Ok(410)
    );
}

/// A SPEC OPERATION THE WITNESS DOES NOT OVERRIDE, by the dot and by name: `size` is
/// `FiniteCollection`'s own default over `collect`, so its row is the spec's `E`, read off
/// the provision at the receiver. `collect`, which the witness does define, and `foldLeft`,
/// which adds a row of its own, beside it.
#[test]
fn a_defaulted_spec_operation_reads_its_row_off_the_witness() {
    for (tag, body, answer) in [
        ("dot", "m.size()", 410),
        ("named", "FiniteCollection.size(m)", 410),
        ("collect", "FiniteCollection.collect(m).length()", 410),
        (
            "fold",
            "FiniteCollection.foldLeft(m, 0, lambda (acc: Int64, x: Int64) -> acc + x)",
            1010,
        ),
    ] {
        let ns = format!("wi2nmxa.specop.{tag}");
        assert_eq!(
            run(&mapped(&ns, "", WRITES_K, body), &format!("{ns}.main")),
            Ok(answer),
            "`{body}`"
        );
    }
}

/// THE ROW IS READ AS WHAT IT IS, NOT AS NOTHING. `f` declared pure and consuming the
/// stream is refused for the cell the transform writes — by each spelling. A reader that
/// answered `{}` for the argument it could not carry would load these.
#[test]
fn the_row_read_names_the_cell() {
    for (tag, decl, body) in [
        ("member", MEMBER, "total(m)"),
        ("bracket", BRACKET, "total(m)"),
        ("dot", "", "m.size()"),
    ] {
        let ns = format!("wi2nmxa.pure.{tag}");
        assert_refused_naming(
            &load_errors_of(&mapped(&ns, decl, "", body)),
            &["f.effects (op-effects)", "got undeclared effect: Modify[T = k]"],
            &format!("`{body}` in an operation declared pure"),
        );
    }
}

/// …AND IT NAMES THE CELL THE RECEIVER'S TYPE NAMES. A stream whose transform writes `j`,
/// consumed in an operation that declares `Modify[k]`.
#[test]
fn the_row_read_is_the_receivers_cell_and_no_other() {
    let src = r#"
namespace wi2nmxa.othercell
  import anthill.prelude.{List, Int64, FiniteCollection, MappedStream, Cell, Modify}
  operation total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E = FiniteCollection.size(c)
  operation f(k: Cell[V = Int64], j: Cell[V = Int64],
              m: MappedStream[Source = List[T = Int64], SourceElement = Int64, T = Int64,
                              SourceEffects = {}, TransformEffects = {Modify[j]}]) -> Int64 effects {Modify[k]} =
    total(m)
end
"#;
    assert_refused_naming(
        &load_errors_of(src),
        &["f.effects (op-effects)", "got undeclared effect: Modify[T = j]"],
        "the stream writes `j`, the operation declares `k`",
    );
}

/// CONTROL — PASSES EITHER WAY BY DESIGN: the same consumer over a stream whose transform
/// is pure, every argument of whose type is a term.
#[test]
fn a_ground_row_is_the_control() {
    let src = r#"
namespace wi2nmxa.ground
  import anthill.prelude.{List, Int64, FiniteCollection, MappedStream}
  operation total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E = FiniteCollection.size(c)
  operation f(m: MappedStream[Source = List[T = Int64], SourceElement = Int64, T = Int64,
                              SourceEffects = {}, TransformEffects = {}]) -> Int64 = total(m)
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation inc(x: Int64) -> Int64 = x + 1
  operation main() -> Int64 = f(rows().map(inc))
end
"#;
    assert_eq!(run(src, "wi2nmxa.ground.main"), Ok(4));
}

// ── a spec of the program's own: each way a provision binds the row ──────────

/// `Walk` over a carrier parameter, with a row `E`: `run` a provider defines, `twice` the
/// spec's own default over it. Three carriers, one per way a provision says the row:
///
///  * `Box` — its OWN provision, the row its own parameter (`E = BE`);
///  * `Duo` — its own provision, the row a COMPOUND over two parameters (`E = {A, B}`);
///  * `Crate` — a WITNESS's provision, the row the witness's parameter (`E = WE`), which
///    the witness's head ties to the carrier's (`C = Crate[CE = WE]`).
///
/// `use` consumes a `v` of type `ty` by `body`; `build` makes one from `make` and `main`
/// answers `use`'s answer × 100 + the cell.
fn walk(ns: &str, ty: &str, body: &str, make: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}

  sort Walk
    sort C = ?
    effects E = ?
    operation run(c: C, x: Int64) -> Int64 effects E
    operation twice(c: C, x: Int64) -> Int64 effects E = run(c, x) + run(c, x)
  end

  sort Box
    import anthill.prelude.{{Int64}}
    import {ns}.{{Walk}}
    effects BE = ?
    entity box(f: (x: Int64) -> Int64 @ {{BE}})
    provides Walk[C = Self, E = BE]
    operation run(b: Self, x: Int64) -> Int64 effects BE = match b case box(f) -> f(x)
  end

  sort Duo
    import anthill.prelude.{{Int64}}
    import {ns}.{{Walk}}
    effects A = ?
    effects B = ?
    entity duo(f: (x: Int64) -> Int64 @ {{A}}, g: (x: Int64) -> Int64 @ {{B}})
    provides Walk[C = Self, E = {{A, B}}]
    operation run(d: Self, x: Int64) -> Int64 effects {{A, B}} = match d case duo(f, g) -> f(x) + g(x)
  end

  sort Crate
    import anthill.prelude.{{Int64}}
    effects CE = ?
    entity crate(f: (x: Int64) -> Int64 @ {{CE}})
  end

  sort CrateWalk
    import anthill.prelude.{{Int64}}
    import {ns}.{{Walk, Crate}}
    import {ns}.Crate.{{crate}}
    effects WE = ?
    provides Walk[C = Crate[CE = WE], E = WE]
    operation run(c: Crate[CE = WE], x: Int64) -> Int64 effects WE = match c case crate(f) -> f(x)
  end

  import {ns}.Box.{{box}}
  import {ns}.Duo.{{duo}}
  import {ns}.Crate.{{crate}}

  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation inc(x: Int64) -> Int64 = x + 1
  operation via(c: Walk.C) -> Int64 effects Walk.E = Walk.run(c, 5)
  operation viaBr[P, R](c: P) -> Int64 effects R requires Walk[C = P, E = R] = Walk.run(c, 5)

  operation use(k: Cell[V = Int64], v: {ty}) -> Int64 effects {{Modify[k]}} = {body}
  operation build(k: Cell[V = Int64]) -> Int64 effects {{Modify[k]}} =
    let v: {ty} = {make}
    use(k, v)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = build(k)
    n * 100 + Cell.get(k)
end
"#
    )
}

const WRITES: &str = "lambda (x: Int64) -> bump(k, x)";

/// The three carriers, each as its type at a transform that writes `k`, the expression that
/// makes one, and what `Walk.run(v, 5)` and `Walk.twice(v, 5)` answer × 100 + the cell: `Duo`
/// runs both of its functions, the second of them `inc` (5 + 6, the cell 5; twice, 22 and
/// the cell 10).
fn carriers() -> [(&'static str, &'static str, String, i64, i64); 3] {
    [
        ("own", "Box[BE = {Modify[k]}]", format!("box({WRITES})"), 505, 1010),
        (
            "compound",
            "Duo[A = {Modify[k]}, B = {}]",
            format!("duo({WRITES}, inc)"),
            1105,
            2210,
        ),
        ("witness", "Crate[CE = {Modify[k]}]", format!("crate({WRITES})"), 505, 1010),
    ]
}

/// THE MEMBER SUGAR AND THE BRACKET CLAUSE over each carrier: the row is the carrier's
/// provision's, read at the receiver.
#[test]
fn a_clauses_row_is_read_off_each_kind_of_provision() {
    for (kind, ty, make, answer, _) in carriers() {
        for (spelling, body) in [("member", "via(v)"), ("bracket", "viaBr(v)")] {
            let ns = format!("wi2nmxa.walk.{kind}.{spelling}");
            assert_eq!(
                run(&walk(&ns, ty, body, &make), &format!("{ns}.main")),
                Ok(answer),
                "`{body}` over `{ty}`"
            );
        }
    }
}

/// THE SPEC'S OWN DEFAULT over each carrier: all three define `run` and leave `twice` to the
/// spec, whose row at the receiver is the provision's — for `Duo` the compound `{A, B}` at
/// `A = {Modify[k]}`. The function runs twice.
#[test]
fn a_defaulted_operation_reads_its_row_off_each_kind_of_provision() {
    for (kind, ty, make, _, answer) in carriers() {
        let ns = format!("wi2nmxa.walk.{kind}.defaulted");
        assert_eq!(
            run(&walk(&ns, ty, "Walk.twice(v, 5)", &make), &format!("{ns}.main")),
            Ok(answer),
            "`Walk.twice(v, 5)` over `{ty}`"
        );
    }
}

/// CONTROL — PASSES EITHER WAY BY DESIGN. The operation each provider DEFINES: its row is
/// the override's own, fixed by unifying the argument with the override's signature, and no
/// provision is read for it. It is what says the gap was the reading and not the receiver.
#[test]
fn an_overridden_operation_is_the_control() {
    for (kind, ty, make, answer, _) in carriers() {
        let ns = format!("wi2nmxa.walk.{kind}.overridden");
        assert_eq!(
            run(&walk(&ns, ty, "Walk.run(v, 5)", &make), &format!("{ns}.main")),
            Ok(answer),
            "`Walk.run(v, 5)` over `{ty}`"
        );
    }
}

/// CONTROL — PASSES EITHER WAY BY DESIGN: the compound provision at rows that are terms.
#[test]
fn a_compound_provision_at_ground_rows_is_the_control() {
    let ns = "wi2nmxa.walk.compound.ground";
    assert_eq!(
        run(
            &walk(ns, "Duo[A = {}, B = {}]", "via(v)", "duo(inc, inc)"),
            &format!("{ns}.main")
        ),
        Ok(1200)
    );
}

// ── a spec that receives on itself ───────────────────────────────────────────

/// `Sp` receives on itself, with a row `E`: `run` a provider defines and `twice` the spec's
/// own default. `Box` provides it at its own row parameter, `E = BE`. `viaSelf` writes the
/// row as a projection of its receiver. `use` consumes a box whose function writes `k` by
/// `body`, declaring `declared`; `main` answers `use`'s answer × 100 + the cell.
fn receiving_on_itself(ns: &str, declared: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  sort Sp
    import anthill.prelude.{{Int64}}
    effects E = ?
    operation run(s: Self, x: Int64) -> Int64 effects E
    operation twice(s: Self, x: Int64) -> Int64 effects E = run(s, x) + run(s, x)
  end
  sort Box
    import anthill.prelude.{{Int64}}
    import {ns}.{{Sp}}
    effects BE = ?
    entity box(f: (x: Int64) -> Int64 @ {{BE}})
    provides Sp[E = BE]
    operation run(b: Self, x: Int64) -> Int64 effects BE = match b case box(f) -> f(x)
  end
  import {ns}.Box.{{box}}
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation viaSelf(s: Sp) -> Int64 effects s.E = Sp.run(s, 5)
  operation use(k: Cell[V = Int64], v: Box[BE = {{Modify[k]}}]) -> Int64 effects {{{declared}}} = {body}
  operation build(k: Cell[V = Int64]) -> Int64 effects {{Modify[k]}} =
    let v: Box[BE = {{Modify[k]}}] = box(lambda (x: Int64) -> bump(k, x))
    use(k, v)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = build(k)
    n * 100 + Cell.get(k)
end
"#
    )
}

/// THE SPEC'S OWN DEFAULT ON A SPEC THAT RECEIVES ON ITSELF: `Sp.twice(v, 5)`'s row is the
/// spec's `E`, which the provision binds to the receiver's own parameter — a row naming a
/// cell. In an operation declared PURE it loaded and ran, writing the cell twice: the
/// receiver's argument read as one it had not written, `E` stayed open, and an open row was
/// no effect at all. Its twin at a row that holds no value, `Box[BE = {Error[String]}]`, was
/// refused.
///
/// CONTROL — PASSES EITHER WAY BY DESIGN: the same call where the cell is declared, which
/// loaded before for the wrong reason and answers 5 + 5 with 10 written.
#[test]
fn a_self_receiving_specs_default_reads_its_row_at_a_receiver_that_names_a_cell() {
    assert_refused_naming(
        &load_errors_of(&receiving_on_itself("wi2nmxa.selfrecv.pure", "", "Sp.twice(v, 5)")),
        &["use.effects (op-effects)", "got undeclared effect: Modify[T = k]"],
        "`Sp.twice(v, 5)` in an operation declared pure",
    );
    let ns = "wi2nmxa.selfrecv.declared";
    assert_eq!(
        run(
            &receiving_on_itself(ns, "Modify[k]", "Sp.twice(v, 5)"),
            &format!("{ns}.main")
        ),
        Ok(1010)
    );
}

/// THE ROW WRITTEN AS A PROJECTION OF THE RECEIVER: `viaSelf(s: Sp) effects s.E`, called on
/// the box, incurs what the provision says `E` is there. A row naming the caller's cell is
/// that answer as much as `{}` is, and the projection reader held it to the argument check's
/// closedness instead — so `s.E` stayed a projection, and the call was refused "undeclared
/// effect: v.E" in a caller that declares the cell (its twin at `{Error[String]}` loaded).
/// Declared pure, the refusal names the cell.
#[test]
fn a_projected_row_is_read_at_a_receiver_that_names_a_cell() {
    let ns = "wi2nmxa.projected.declared";
    assert_eq!(
        run(
            &receiving_on_itself(ns, "Modify[k]", "viaSelf(v)"),
            &format!("{ns}.main")
        ),
        Ok(505)
    );
    assert_refused_naming(
        &load_errors_of(&receiving_on_itself("wi2nmxa.projected.pure", "", "viaSelf(v)")),
        &["use.effects (op-effects)", "got undeclared effect: Modify[T = k]"],
        "`viaSelf(v)` in an operation declared pure",
    );
}

// ── a cell named like a type parameter ───────────────────────────────────────

/// A VALUE IN A ROW IS NOT A TYPE PARAMETER, WHATEVER IT IS CALLED. The receiver's row is
/// spliced into the provision's binding where a parameter of the carrier stood, and the cell
/// it names is a value of the caller's: a cell called `A`, `B`, `CE`, `WE` or `E` — the
/// names of the carriers', the witness's and the spec's own parameters — is the cell, as one
/// called `k` is. A parameter is named by a type's reference and a place by an expression's,
/// and that is what keeps the two apart: the rewrite that puts a receiver's arguments in also
/// declines to enter a type that holds a value, and NO ROW MEASURES THAT (backed out, this
/// row and every other answer the same — the first of the parts the module doc lists as
/// undriven).
///
/// `Duo` runs both functions over 5, the first adding it to the cell (11, cell 5); `Crate`
/// runs once over 5 and twice over 1 (7, cell 12): 18 × 100 + 12.
#[test]
fn a_cell_named_like_a_type_parameter_is_still_the_cell() {
    for cell in ["k", "A", "B", "CE", "WE", "E"] {
        let ns = format!("wi2nmxa.named.{}", cell.to_lowercase());
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  sort Walk
    sort C = ?
    effects E = ?
    operation run(c: C, x: Int64) -> Int64 effects E
    operation twice(c: C, x: Int64) -> Int64 effects E = run(c, x) + run(c, x)
  end
  sort Duo
    import anthill.prelude.{{Int64}}
    import {ns}.{{Walk}}
    effects A = ?
    effects B = ?
    entity duo(f: (x: Int64) -> Int64 @ {{A}}, g: (x: Int64) -> Int64 @ {{B}})
    provides Walk[C = Self, E = {{A, B}}]
    operation run(d: Self, x: Int64) -> Int64 effects {{A, B}} = match d case duo(f, g) -> f(x) + g(x)
  end
  sort Crate
    import anthill.prelude.{{Int64}}
    effects CE = ?
    entity crate(f: (x: Int64) -> Int64 @ {{CE}})
  end
  sort CrateWalk
    import anthill.prelude.{{Int64}}
    import {ns}.{{Walk, Crate}}
    import {ns}.Crate.{{crate}}
    effects WE = ?
    provides Walk[C = Crate[CE = WE], E = WE]
    operation run(c: Crate[CE = WE], x: Int64) -> Int64 effects WE = match c case crate(f) -> f(x)
  end
  import {ns}.Duo.{{duo}}
  import {ns}.Crate.{{crate}}
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation inc(x: Int64) -> Int64 = x + 1
  operation via(c: Walk.C) -> Int64 effects Walk.E = Walk.run(c, 5)
  operation useDuo({cell}: Cell[V = Int64], v: Duo[A = {{Modify[{cell}]}}, B = {{}}]) -> Int64
    effects {{Modify[{cell}]}} = via(v)
  operation useCrate({cell}: Cell[V = Int64], v: Crate[CE = {{Modify[{cell}]}}]) -> Int64
    effects {{Modify[{cell}]}} = via(v) + Walk.twice(v, 1)
  operation build({cell}: Cell[V = Int64]) -> Int64 effects {{Modify[{cell}]}} =
    let d: Duo[A = {{Modify[{cell}]}}, B = {{}}] = duo(lambda (x: Int64) -> bump({cell}, x), inc)
    let c: Crate[CE = {{Modify[{cell}]}}] = crate(lambda (x: Int64) -> bump({cell}, x))
    useDuo({cell}, d) + useCrate({cell}, c)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = build(k)
    n * 100 + Cell.get(k)
end
"#
        );
        assert_eq!(run(&src, &format!("{ns}.main")), Ok(1812), "a cell called `{cell}`");
    }
}

// ── two cells, and a witness that names its carrier's parameters in another order ──

/// A STREAM MAPPED TWICE, each transform writing its own cell: the outer stream's source is
/// the inner stream, itself a type that holds a value, and the witness's row at the outer is
/// the two together. Four elements; the inner transform adds each to `a`, the outer adds
/// each + 10 to `b`. The control declares one cell and is refused for the other.
#[test]
fn a_stream_mapped_twice_carries_both_cells() {
    let program = |ns: &str, declared: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{List, Int64, Unit, FiniteCollection, MappedStream, Cell, Modify}}
  operation total(c: FiniteCollection.C) -> Int64 effects FiniteCollection.E = FiniteCollection.size(c)
  operation rows() -> List[T = Int64] = [1, 2, 3, 4]
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation g(a: Cell[V = Int64], b: Cell[V = Int64]) -> Int64 effects {{{declared}}} =
    let inner = FiniteCollection.map[EffP = {{Modify[a]}}](rows(), lambda (x: Int64) -> bump(a, x))
    let outer = FiniteCollection.map[EffP = {{Modify[b]}}](inner, lambda (x: Int64) -> bump(b, x + 10))
    total(outer)
  operation main() -> Int64 =
    let a: Cell[V = Int64] = Cell.new(0)
    let b: Cell[V = Int64] = Cell.new(0)
    let n = g(a, b)
    n * 10000 + Cell.get(a) * 100 + Cell.get(b)
end
"#
        )
    };
    let ns = "wi2nmxa.twice";
    assert_eq!(
        run(&program(ns, "Modify[a], Modify[b]"), &format!("{ns}.main")),
        Ok(41050)
    );
    assert_refused_naming(
        &load_errors_of(&program("wi2nmxa.twice_one", "Modify[a]")),
        &["g.effects (op-effects)", "got undeclared effect: Modify[T = b]"],
        "the outer transform's cell is in the row too",
    );
}

/// A WITNESS WHOSE PARAMETERS ARE THE CARRIER'S IN ANOTHER ORDER: `TwoWalk provides Walk[C =
/// Two[A = B, B = A], E = A]` — the witness's `A` is the carrier's `B`, and the spec's row is
/// that one. Over a `Two[A = {Modify[k]}, B = {Modify[j]}]` the row is `{Modify[j]}`: the
/// receiver's arguments go to the witness's parameters by what the head says, not by name.
/// `run` walks by the carrier's second function, which adds its argument + 1 to `j`. The
/// control declares `k` and is refused for `j`.
#[test]
fn a_witness_that_reorders_its_carriers_parameters_reads_the_one_it_names() {
    let program = |ns: &str, declared: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  sort Walk
    sort C = ?
    effects E = ?
    operation run(c: C, x: Int64) -> Int64 effects E
  end
  sort Two
    import anthill.prelude.{{Int64}}
    effects A = ?
    effects B = ?
    entity two(f: (x: Int64) -> Int64 @ {{A}}, g: (x: Int64) -> Int64 @ {{B}})
  end
  sort TwoWalk
    import anthill.prelude.{{Int64}}
    import {ns}.{{Walk, Two}}
    import {ns}.Two.{{two}}
    effects A = ?
    effects B = ?
    provides Walk[C = Two[A = B, B = A], E = A]
    operation run(c: Two[A = B, B = A], x: Int64) -> Int64 effects A = match c case two(f, g) -> g(x)
  end
  import {ns}.Two.{{two}}
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation via(c: Walk.C) -> Int64 effects Walk.E = Walk.run(c, 5)
  operation use(k: Cell[V = Int64], j: Cell[V = Int64],
                v: Two[A = {{Modify[k]}}, B = {{Modify[j]}}]) -> Int64 effects {{{declared}}} = via(v)
  operation build(k: Cell[V = Int64], j: Cell[V = Int64]) -> Int64 effects {{Modify[k], Modify[j]}} =
    let v: Two[A = {{Modify[k]}}, B = {{Modify[j]}}] =
      two(lambda (x: Int64) -> bump(k, x), lambda (x: Int64) -> bump(j, x + 1))
    use(k, j, v)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let j: Cell[V = Int64] = Cell.new(0)
    let n = build(k, j)
    n * 10000 + Cell.get(k) * 100 + Cell.get(j)
end
"#
        )
    };
    let ns = "wi2nmxa.reorder";
    assert_eq!(run(&program(ns, "Modify[j]"), &format!("{ns}.main")), Ok(60006));
    assert_refused_naming(
        &load_errors_of(&program("wi2nmxa.reorder_k", "Modify[k]")),
        &["use.effects (op-effects)", "got undeclared effect: Modify[T = j]"],
        "the witness's row is the carrier's second parameter",
    );
}

// ── the subtype relation's reading of a provider at an argument that holds a value ──

/// `Cnt` provides `Stream` at its own row, `E = {EC}`; its `splitFirst` returns the rest as a
/// `Cnt` at `rest_row`.
fn rest_at(ns: &str, rest_row: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Option, Pair, Stream, Modify, Error}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}
  sort Cnt
    sort T = ?
    effects EC = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = {{EC}}]
    operation splitFirst(c: Self) -> Option[Pair[A = T, B = Cnt[T = T, EC = {rest_row}]]] effects {{EC}} =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end
end
"#
    )
}

/// A MEMBER RETURNS WHAT ITS SPEC PROMISES, WHATEVER CARRIER THE TYPE RIDES. `Stream`'s
/// `splitFirst` returns the rest as a stream at the receiver's row, which at this provision
/// is `{EC}`. A member returning the rest at ANOTHER row does not fit: at `{Error[String]}`
/// it was refused, and at `{Modify[c]}` — a row that names the member's own parameter, so a
/// type that holds a value — it loaded. The subtype relation reads `Cnt`'s `Stream` view at
/// the returned type's arguments, and an argument that is no term was not read into it: the
/// view's `{EC}` stood as the parameter it was written with, which the spec's side also is.
///
/// CONTROLS — PASS EITHER WAY BY DESIGN: the ground twin is refused, and the rest returned at
/// the receiver's own row loads.
#[test]
fn a_member_returning_another_row_is_refused_as_its_ground_twin_is() {
    for (tag, rest_row) in [("cell", "{Modify[c]}"), ("ground", "{Error[String]}")] {
        assert_refused_naming(
            &load_errors_of(&rest_at(&format!("wi2nmxa.rest.{tag}"), rest_row)),
            &[
                "its own member 'splitFirst' does not fit 'anthill.prelude.Stream.splitFirst'",
                "which is not a subtype of the spec's",
            ],
            &format!("the rest returned at `{rest_row}`"),
        );
    }
    let errs = load_errors_of(&rest_at("wi2nmxa.rest.same", "EC"));
    assert!(errs.is_empty(), "the rest at the receiver's own row: {errs:#?}");
}

// ── a spec standing for its providers, at a type that holds a value ──────────

/// `Cap`, a spec over a parameter, provided for `Buf` by a WITNESS; `Other` is a sort
/// nothing provides it for. `body` follows inside the namespace.
fn witnessed(ns: &str, imports: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Unit}}
{imports}
  sort Cap
    sort C = ?
    operation weight(c: C) -> Int64
  end
  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end
  sort Other
    sort T = ?
    sort N = ?
    entity other(v: T)
  end
  sort BufCap
    import anthill.prelude.{{Int64}}
    import {ns}.{{Cap, Buf}}
    sort T = ?
    sort N = ?
    provides Cap[C = Buf[T = T, N = N]]
    operation weight(c: Buf[T = T, N = N]) -> Int64 = 7
  end
{body}
end
"#
    )
}

/// A DENIAL IS NOT EVADED BY A TYPE THAT HOLDS A VALUE. `-Permission[Cap]` denies the
/// permission for every provider of `Cap` — a provision relates the two capabilities — and
/// `Buf` is one through its witness. `Permission[Buf[T = Int64, N = Bool]]` under that denial
/// was refused, and `Permission[Buf[T = Int64, N = 3]]` loaded: a type that holds a value
/// reaches the subtype relation's other dispatch, whose arm for a parameterized type against
/// a bare spec did not ask the witness.
///
/// CONTROLS — PASS EITHER WAY BY DESIGN: the twin whose type holds no value is refused, and
/// the permission for a sort nothing provides `Cap` for loads under the denial.
#[test]
fn a_denial_is_not_evaded_by_a_type_that_holds_a_value() {
    let program = |ns: &str, capability: &str| {
        witnessed(
            ns,
            "  import anthill.prelude.{Permission}",
            &format!(
                "  operation guarded[Rho](f: () -> Unit @ {{Rho, -Permission[Cap]}}) -> Unit\n  \
                 operation mints() -> Unit\n    effects {{Permission[{capability}]}}\n  \
                 operation call() -> Unit = guarded[Rho = {{Permission[{capability}]}}](mints)"
            ),
        )
    };
    for (tag, capability) in [
        ("value", "Buf[T = Int64, N = 3]"),
        ("type", "Buf[T = Int64, N = Bool]"),
    ] {
        assert_refused_naming(
            &load_errors_of(&program(&format!("wi2nmxa.deny.{tag}"), capability)),
            &["violates its `-Permission[T = Cap]` lacks-constraint"],
            &format!("`Permission[{capability}]` under `-Permission[Cap]`"),
        );
    }
    let errs = load_errors_of(&program("wi2nmxa.deny.other", "Other[T = Int64, N = 3]"));
    assert!(errs.is_empty(), "no provision relates `Other` to `Cap`: {errs:#?}");
}

/// A COLUMN BOUNDED BY A WITNESSED SPEC IS CITED WITH AN ARGUMENT WHOSE TYPE HOLDS A VALUE.
/// `keep(?x: Cap.C, ?y)` stores the requirement `Cap` of its first column, and `keep(b)`
/// applies the relation from an operation body: the argument's type is checked against that
/// bound, which a `Buf` meets through its witness. With `b: Buf[T = Int64, N = Bool]` the
/// citation loaded, and with `b: Buf[T = Int64, N = 3]` it was refused, "argument binding
/// column `x` has an incompatible type".
///
/// A LOAD VERDICT. The citation is what the typer decides here; run, the bound is asked of
/// the matched value, whose `N` no field determines, and that goal is suspended on either
/// twin.
///
/// CONTROLS — PASS EITHER WAY BY DESIGN: the twin whose type holds no value loads, and an
/// argument of a sort nothing provides `Cap` for is refused.
#[test]
fn a_bounded_column_is_cited_with_an_argument_whose_type_holds_a_value() {
    let program = |ns: &str, arg_type: &str| {
        witnessed(
            ns,
            "  import anthill.prelude.{List, Error}\n  import anthill.prelude.List.{length}",
            &format!(
                "  import {ns}.Buf.{{buf}}\n  \
                 fact src(buf(v: 1), 10)\n  \
                 rule keep(?x: Cap.C, ?y) :- src(?x, ?y)\n  \
                 operation cited(b: {arg_type}) -> Int64 effects Error = length(keep(b).takeN(5))"
            ),
        )
    };
    for (tag, arg_type) in [
        ("value", "Buf[T = Int64, N = 3]"),
        ("type", "Buf[T = Int64, N = Bool]"),
    ] {
        let errs = load_errors_of(&program(&format!("wi2nmxa.cite.{tag}"), arg_type));
        assert!(errs.is_empty(), "`keep(b)` over `b: {arg_type}`: {errs:#?}");
    }
    assert_refused_naming(
        &load_errors_of(&program("wi2nmxa.cite.other", "Other[T = Int64, N = 3]")),
        &["argument binding column `x` has an incompatible type"],
        "an argument of a sort nothing provides `Cap` for",
    );
}

// ── a constructor's field typed at a spec ─────────────────────────────────────

/// `Src`, a spec that receives on itself, with a row: `Cnt` provides it at its own row
/// parameter, and `Wrap` holds a `Src` in a field. `use` takes a `c` of type `ty`, wraps it
/// and pulls through the wrapper, under the row `declared`; `main` answers `use`'s answer
/// × 100 + the cell.
fn wrapped(ns: &str, ty: &str, declared: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  sort Src
    import anthill.prelude.{{Int64}}
    effects E = ?
    operation pull(s: Self) -> Int64 effects E
  end
  sort Cnt
    import anthill.prelude.{{Int64}}
    effects EC = ?
    entity cnt(f: (x: Int64) -> Int64 @ {{EC}})
    provides Src[E = EC]
    operation pull(c: Self) -> Int64 effects EC = match c case cnt(f) -> f(1)
  end
  sort Wrap
    import anthill.prelude.{{Int64}}
    effects WE = ?
    entity wrap(source: Src[E = WE])
    provides Src[E = WE]
    operation pull(w: Self) -> Int64 effects WE = match w case wrap(s) -> Src.pull(s)
  end
  import {ns}.Cnt.{{cnt}}
  import {ns}.Wrap.{{wrap}}
  operation bump(k: Cell[V = Int64], x: Int64) -> Int64 effects {{Modify[k]}} =
    let u = Cell.set(k, Cell.get(k) + x)
    x
  operation use(k: Cell[V = Int64], c: {ty}) -> Int64 {declared} = Src.pull(wrap(c))
  operation build(k: Cell[V = Int64]) -> Int64 effects {{Modify[k]}} =
    let c: {ty} = cnt(lambda (x: Int64) -> bump(k, x))
    use(k, c)
  operation main() -> Int64 =
    let k: Cell[V = Int64] = Cell.new(0)
    let n = build(k)
    n * 100 + Cell.get(k)
end
"#
    )
}

/// A FIELD TYPED AT A SPEC TAKES A PROVIDER'S VALUE AT THE ROW THE PROVIDER HAS THERE.
/// `wrap(source: Src[E = WE])` given a `Cnt[EC = {Modify[k]}]` is a `Wrap` at the row `Cnt
/// provides Src[E = EC]` says at that receiver. The receiver's written argument was read
/// only where it was a term, so the field's row stayed the projection `c.EC`, which `use`
/// does not declare: "got undeclared effect: c.EC". The function runs once over 1 and adds
/// it to the cell: 1 × 100 + 1.
///
/// The label written without braces is the row holding it, and answers the same. The pure
/// declaration is refused naming the cell, where it named the projection.
#[test]
fn a_spec_typed_field_takes_a_providers_row_that_names_a_cell() {
    for (tag, ty) in [
        ("braced", "Cnt[EC = {Modify[k]}]"),
        ("bare", "Cnt[EC = Modify[k]]"),
    ] {
        let ns = format!("wi2nmxa.field.{tag}");
        assert_eq!(
            run(&wrapped(&ns, ty, "effects {Modify[k]}"), &format!("{ns}.main")),
            Ok(101),
            "`wrap(c)` over `c: {ty}`"
        );
    }
    assert_refused_naming(
        &load_errors_of(&wrapped("wi2nmxa.field.pure", "Cnt[EC = {Modify[k]}]", "")),
        &["undeclared effect: Modify[T = k]"],
        "the pure declaration",
    );
}

// ── a key that holds a value ──────────────────────────────────────────────────

/// A KEY THAT HOLDS A VALUE IS STILL A KEY. `Map` and `Set` require a lawful `Eq` of what
/// they are keyed by, and a key whose equality is not reflexive is refused where the type is
/// written. `Vec[T = Float, N = Bool]` was, and `Vec[T = Float, N = 3]` loaded: the check
/// took the bindings of a written type that were hash-consed terms, on the reading that the
/// others were values in a type position, and a type that holds one somewhere inside is not
/// a term either. Only a value at the root is no key.
///
/// CONTROLS — PASS EITHER WAY BY DESIGN: the twin whose key holds no value is refused, a key
/// with a lawful element loads, and so does the unlawful type where `Map` does not key by it.
#[test]
fn a_key_whose_type_holds_a_value_is_checked_for_a_lawful_equality() {
    let program = |ns: &str, written: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Float, Bool, Set, Map, List}}
  sort Vec
    sort T = ?
    sort N = ?
    entity vec(items: List[T])
  end
  operation k(s: {written}) -> Int64 = 1
end
"#
        )
    };
    for (tag, written, key) in [
        ("map", "Map[K = Vec[T = Float, N = 3], V = Int64]", "Vec[T = anthill.prelude.Float, N = 3]"),
        ("set", "Set[T = Vec[T = Float, N = 3]]", "Vec[T = anthill.prelude.Float, N = 3]"),
        (
            "nested",
            "Map[K = List[T = Vec[T = Float, N = 3]], V = Int64]",
            "Vec[T = anthill.prelude.Float, N = 3]]",
        ),
        (
            "type",
            "Map[K = Vec[T = Float, N = Bool], V = Int64]",
            "Vec[T = anthill.prelude.Float, N = anthill.prelude.Bool]",
        ),
    ] {
        assert_refused_naming(
            &load_errors_of(&program(&format!("wi2nmxa.key.{tag}"), written)),
            &["requires `anthill.prelude.Eq` at its parameter", key, "provides `NonEq`"],
            &format!("`{written}`"),
        );
    }
    for (tag, written) in [
        ("lawful", "Map[K = Vec[T = Int64, N = 3], V = Int64]"),
        ("unkeyed", "Map[K = Int64, V = Vec[T = Float, N = 3]]"),
    ] {
        let errs = load_errors_of(&program(&format!("wi2nmxa.key.{tag}"), written));
        assert!(errs.is_empty(), "`{written}`: {errs:#?}");
    }
}
